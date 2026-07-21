# Representation-first modular addition

## Decision

The next modular-addition layer should not be a completed literal sine/cosine table.

The existing table development is a valid reference implementation and proves useful floating-point
facts, but it chose the wrong object as the public semantic boundary. `FpClockTables` asks an
implementation to approximate one canonical coordinate vector entry by entry. This turns a choice
of basis and a storage layout into part of the theorem statement.

That is too rigid for the actual goal: explaining and certifying a learned modular-addition model.
A trained model can implement the same mechanism after frequency permutation, phase rotation,
rescaling, mixing within a two-dimensional frequency plane, or a paired change of basis between its
features and readout. Such a model need not be close entrywise to our preferred ordering of cosine
and sine coordinates.

Literal words remain important at the artifact boundary. They should not define the mathematical
mechanism.

## What was wrong with the table-first method

The full `p = 113` table has 113 rows and 224 coordinates, but those entries are not independent
data. They are repeated evaluations of a cyclic group representation:

```text
chi_k(a + b) = chi_k(a) * chi_k(b).
```

Writing every evaluation into a table discards that structure and then asks Lean to reconstruct it
through thousands of local approximation obligations. Exact certification of every canonical RNE
trigonometric word would establish provenance for a synthetic reference table, but it would not
show that a trained network uses the same basis or even the same coordinate normalization.

The method therefore has three mismatches:

1. **Structural duplication.** A small family of characters is expanded into a large table.
2. **Gauge dependence.** Entrywise closeness distinguishes implementations that compute identical
   logits after an invertible change of coordinates.
3. **Wrong validation target.** The important claim is that the realized computation composes
   residues and separates the correct class, not that its weights equal canonical trig constants.

The committed literal bridge is still useful: it proves that imported bit patterns decode exactly
to Flean values. Its role is generic artifact ingestion for reference or learned weights.

## The mathematical object we actually want

At the exact level, modular addition should be presented as a representation of the cyclic group,
not as a table of samples.

For the familiar Fourier instance, each nonzero frequency contributes a real two-dimensional plane.
In a chosen basis the group action is rotation by the corresponding phase, and composition is
complex multiplication:

```text
(c_a, s_a) * (c_b, s_b)
  = (c_a*c_b - s_a*s_b, s_a*c_b + c_a*s_b).
```

The basis is not essential. A frequency plane may be rotated or rescaled if the composition and
readout maps transform with it. A clean exact API should expose laws such as:

```text
encode 0 = identity
combine (encode a) (encode b) = encode (a + b)
score (encode s) c = kernel (s - c)
score (encode s) s > score (encode s) c       when c != s
```

The canonical sine/cosine clock is then one instance. A recurrence, a generated phase evaluator, a
lookup table, and a learned embedding/readout pair are other possible realizations.

There are two useful abstraction levels.

### Representation-specific layer

An exact `CyclicCharacterSystem` can describe a finite family of two-dimensional representations of
`ZMod p`, their composition laws, and a compatible dual readout. This is where Fourier identities,
frequency support, orthogonality, and redundancy belong.

This layer should avoid committing consumers to a global cosine-then-sine coordinate ordering.
Coordinates may exist inside a concrete instance, but the public theorems should be invariant under
the allowed changes of basis in each frequency plane.

### Operational layer

An `ApproxCyclicCode` should state only what correctness consumes:

- an encoded state for each residue;
- a realized combination operation for separate inputs;
- a realized score for every candidate class;
- a bound on the composition defect;
- a bound transferring state error into score error;
- a class-separation margin or a comparison with an exact separating kernel;
- floating-point execution error for the actual operation trace.

Its headline theorem should say that margin greater than structural defect plus arithmetic error
implies the correct argmax. It should not mention trigonometric coordinates or tables.

## How real weights should enter

The weights-into-Lean bridge should ingest literal tensors and certify an invariant mechanism, not
entrywise agreement with a hand-selected Fourier gauge.

Two different goals should remain separate.

### Extensional verification

For `p = 113` there are only `113^2 = 12769` input pairs. Once the actual finite weights and the
precise floating-point forward pass are imported, correctness or empirical accuracy can be checked
directly over the finite domain. An untrusted evaluator may produce logits, argmax witnesses, or a
compact execution certificate; Lean checks the bit-level inputs, the forward-pass relation, and the
claimed result.

This is the shortest honest route to a statement about a particular trained artifact. It requires
no canonical trig table and no claim that the learned weights look Fourier-like. Exhaustive checking
proves *what the network does*.

### Intensional explanation

A separate structural certificate should explain *why it does it*. That certificate can identify
learned frequency planes and show that the network approximately realizes cyclic composition and a
separating readout. It should support robustness arguments, comparisons across training runs, and
predictions about lower precision. It need not be in the trusted path of the finite correctness
check.

A useful certificate for a trained model could contain:

1. a set of detected frequency subspaces obtained from the learned embeddings/readout;
2. change-of-basis maps identifying those subspaces with abstract character planes;
3. residual bounds outside the selected subspaces;
4. composition-defect bounds for the learned upstream computation;
5. readout/kernel error bounds and the resulting per-input margin;
6. floating-point forward-error bounds for the concrete execution trace.

The certificate may be generated by untrusted Python. Lean should check the imported bit patterns,
rational matrices, residual inequalities, and final margin theorem. The generator is then a search
and compression tool rather than part of the trusted base.

This approach naturally tolerates:

- permutation of frequencies;
- rotations and reflections within a real frequency plane;
- paired feature/readout scaling;
- sparse learned frequency support;
- extra components whose contribution is bounded as a residual;
- models that realize the group law approximately rather than matching analytic trig values.

## What to do with the existing modules

The existing development should remain:

- `ModAddClock.lean` supplies the exact score, margins, and perturbation theorem.
- `ModAddClockFp.lean` is a valid table-backed realization and contains reusable dot-product error
  results.
- `ModAddClockBinary32*.lean` is a verified reference backend and regression test for the numerical
  machinery.
- `ModAddClockBinary32Literal.lean` is the beginning of a generic literal artifact boundary.

But new core results should not extend `FpClockTables` by adding more table-specific fields. The
representation-first API should be a new module, with a bridge showing that the current Fourier
clock is one instance. API changes across this repository are allowed, so downstream code can later
move to the cleaner interface rather than preserving the table abstraction indefinitely.

## Recommended next increment

1. Identify one actual trained checkpoint and pin down its tensor shapes, bit formats, and precise
   forward-pass semantics.
2. Build the smallest literal tensor importer and reflected/executable certificate needed to verify
   its finite-domain accuracy directly.
3. Inspect that checkpoint's embedding, intermediate activations, and readout spectra up to changes
   of basis.
4. Only then define the small approximate cyclic-code interface justified by the observed mechanism;
   its theorem should depend on composition defect, score defect, arithmetic error, and margin.
5. Bridge the existing exact Fourier clock into that interface as a reference instance.

Bulk generation of the remaining canonical Binary32 trig table is deliberately not on this path.
The exact full-bank margin theorem is useful only if a later representation-level argument needs
it; it is not a prerequisite for importing or understanding a learned model.
