# Range-conditioned circuit reduction

## Decision

The active Flean research direction is a concrete range-conditioned circuit reduction.

The first target is not another general error-bound framework and not a continuation of the
canonical modular-addition table. It is a fixed tiny ReLU network whose actual floating-point
execution is proved equivalent, on its stated input domain, to a simpler integer and Boolean
circuit.

The initial network computes XOR on two Boolean inputs:

```text
h₁ = ReLU(x + y)
h₂ = ReLU(x + y - 1)
out = h₁ - 2 h₂
```

For `x,y ∈ {0,1}`, `h₁ = x+y` and `h₂ = x∧y`, hence

```text
out = x + y - 2(x∧y) = x xor y.
```

The theorem should concern the specified floating-point operation trace, not merely the real
function denoted by the same formula.

## Why this is the right first network

This example is deliberately small, but it exercises the important boundaries of the reduction
stack:

- the input domain is structural (`x,y` are exactly encoded bits), not just a loose norm bound;
- all affine operations reduce to small integer arithmetic under an explicit representability
  condition;
- the second hidden unit crosses a genuine ReLU boundary at `x+y=1`;
- the negative bias and final subtraction exercise sign reasoning and exact cancellation to zero;
- ReLU reduces operationally to the existing sign-bit masked select;
- the final result has a Boolean interpretation, so the endpoint is a circuit theorem rather than
  another real-valued approximation theorem.

It also avoids premature infrastructure. Length-two dot products already exist, so the first result
does not depend on building a generic `dotN` or matvec layer.

## Intended theorem ladder

### 1. Concrete operation trace

Define one small executable object for the network, using Flean's floating-point add, subtract,
multiply, and `Fp.fpRelu` operations in the actual evaluation order. Fix the weights and biases to
the exact integers `0`, `1`, `-1`, and `2`.

The public definition should not quantify over arbitrary weights. Generalization can follow after
the concrete proof exposes the right reusable boundary.

### 2. Range certificate

For bit inputs, prove the exact intermediate ranges:

```text
x + y       ∈ {0,1,2}
x + y - 1   ∈ {-1,0,1}
h₁          ∈ {0,1,2}
h₂          ∈ {0,1}
out         ∈ {0,1}
```

Use those ranges to discharge finiteness and exact-representability obligations. The relevant
condition should be stated once at the network boundary—for example, a precision/exponent
condition strong enough to represent every integer in `[-2,2]`—rather than repeated at each op.

### 3. Integer reduction

Prove that projecting every intermediate floating-point result through the exact-integer shadow
gives the corresponding integer computation. This is the numerical reduction:

```text
floating-point network = bounded integer network.
```

The proof should reuse `ExactInt`, `ExactIntB`, and their zero-admitting operations. It should not
reprove individual rounding facts.

### 4. ReLU-to-logic reduction

On the Boolean input domain, prove

```text
ReLU(x + y)     = x + y
ReLU(x + y - 1) = x AND y.
```

Connect the second statement to the sign-bit/masked-select implementation of ReLU, rather than
treating ReLU as an opaque real `max`.

### 5. Headline theorem

The endpoint should have the shape

```text
x,y are finite encodings of Boolean bits
-----------------------------------------
the concrete FP network returns their XOR bit
```

Ideally a second theorem exposes the decoded output word and shows that the whole computation can
be replaced extensionally by a Boolean XOR circuit on the admitted inputs.

## What would make the result genuinely useful

The XOR theorem is the first calibration point, not the research destination. While proving it,
record which hypotheses and proof objects are truly necessary. A good implementation should leave
behind only small reusable pieces:

- a Boolean-to-`ExactIntB` input constructor;
- a compact bundle for a finite computation whose exact-integer bound is propagated internally;
- a bridge from a Boolean threshold predicate to the ReLU sign-bit selection;
- an extensional circuit-equivalence theorem schema, if the concrete proof reveals one naturally.

Do not build these abstractions speculatively. Extract them from the finished XOR proof.

## Follow-up network

Once the XOR calibration is complete, the next serious target is a small fixed binary-weight ReLU
classifier. For inputs and weights in `{−1,+1}`, its dot product reduces to

```text
n - 2 * HammingDistance(input, weight),
```

so a floating-point neuron can potentially be replaced by XNOR, popcount, an integer threshold,
and a final mask. That is the more representative circuit-synthesis result; XOR first tells us
whether Flean can express the reduction cleanly end to end.

## Relationship to modular addition and Wick

The modular-addition work remains a valuable later consumer. Wick now supplies a detailed
real-valued theory of Fourier solutions, mode capture, phase alignment, local grokking, and kernel
rotation. Flean's distinct contribution would be to reduce a learned finite-precision realization
or identify where precision changes that mechanism.

Three modular-addition continuations remain worth preserving:

1. **Finite-precision phase diagram.** Vary modulus, frequency support, storage precision, and
   accumulation precision; prove both collision-based impossibility results and margin-based
   correctness results.
2. **Range-conditioned reduction of a learned checkpoint.** Use observed activation ranges to
   replace parts of its floating-point computation by integer, bit-level, or affine pieces.
3. **Finite-precision kernel-rotation certificates.** Import checkpoint snapshots and certify that
   the computed kernel-target observable still exhibits Wick's predicted rotation, or locate the
   precision at which it ceases to do so.

These should begin with an experiment or an actual checkpoint. Do not extend the canonical trig
table, prove more ideal margin identities, or freeze a large approximate-cyclic-code API in
advance of that evidence.

## First implementation increment

Create a dedicated module, tentatively
`Flean/Operations/RangeReduction/XorNet.lean`, containing:

1. the concrete FP evaluation trace;
2. bit-input constructors and exact intermediate bounds;
3. a theorem identifying the final exact integer with Boolean XOR.

The first increment is complete only when it proves the concrete end-to-end result. A generic
network interface, `dotN`, the binary-weight follow-up, and theorem automation are explicitly later
work.

## Landed implementation (2026-07-21)

The first increment is implemented in:

- `Flean/Operations/RangeReduction/XorNet.lean` — generic range-conditioned reduction;
- `Flean/Operations/RangeReduction/XorNetBinary32.lean` — concrete Binary32/RNE endpoint.

The generic file adds two small operations extracted from the concrete proof:

- `ExactIntB.withBound`, which tightens a proved semantic bound without changing the carried FP
  value or integer;
- `ExactIntB.relu`, whose FP field is literally `Fp.fpRelu` and whose integer shadow is
  `max 0 n`.

The network carries the actual add, subtract, multiply, and sign-bit ReLU operations through
`ExactIntB`. One contract,

```text
4 < 2^prec
prec - 1 ≤ max_exp,
```

licenses the complete trace. `eval_n_eq_arithmetic_xor` reduces it to `x+y-2xy`, and
`eval_n_eq_xor` identifies that integer with Boolean XOR. `eval_fp_eq_trace` proves that erasing the
certificates yields the displayed literal FP program; `fpEval_toVal_eq_xor` transfers the result
back to its decoded FP value.

For Binary32/RNE, `Binary32.fpEval_toVal_eq_xor` discharges the format contract and
`Binary32.fpEval_eq_fpBit` proves the strongest concrete endpoint: the literal FP trace returns the
canonical finite encoding of the XOR bit, including its exact zero/one representation.

No generic network interface or n-ary fold was required. The next research step is therefore the
fixed binary-weight XNOR + popcount + threshold reduction, using the XOR result as the API
calibration point.
