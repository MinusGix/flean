# Clock representation analysis of the grokked mod-113 network

*Measured 2026-07-22 on the seed-0 checkpoint (`references/large_files/full_run_data.pth`),
script `references/analyze_clock.py`, float64 throughout.*

This is the **mechanism** half of the capstone (#2g). The verified checker
(`Flean/Checker/ModAddFull.lean`) already proves *that* the network computes
`(a+b) mod 113` in spec-Binary32, by recomputing every input. This document asks
*why*: how much of that behaviour is explained by the Fourier "clock", and what
is left over.

## The decomposition

Write the realized readout logits as a cube `L[a,b,c]` over the `p³` triples and
split it:

```
L[a,b,c]  =  junk[a,b]                    -- independent of c: cannot affect any argmax
          +  clock[(a+b-c) mod p]         -- the mechanism
          +  defect[a,b,c]                -- everything else
```

`clock` is obtained by projecting onto functions of `a+b` (stage 1), then onto
functions of `s-c` (stage 2), then truncating to the top `K` Fourier modes
(stage 3). Each projection is the L²-optimal one, so each reported defect is a
genuine lower bound on what that structural assumption costs.

## Results

| quantity | value |
|---|---|
| realized margin (fp64 readout) | **9.605165** |
| ideal K=5 clock margin `g(0) − max_{t≠0} g(t)` | **18.3012** |
| composition defect `‖L₀ − M[a+b]‖_∞` (stage 1) | 12.0085 |
| shift defect `‖M − g[s−c]‖_∞` (stage 2) | 5.1414 |
| total defect `ε = ‖L₀ − clock‖_∞` at K=5 | 12.4082 |
| c-independent part removed at stage 0 | 0.0678 |

Frequency content of `g` (power, DC excluded):

| k | \|G_k\| | cumulative |
|---|---|---|
| 42 | 4.7867 | 33.05% |
| 52 | 4.4831 | 62.04% |
| 35 | 2.9878 | 74.91% |
| 41 | 2.9675 | 87.61% |
| 14 | 2.9305 | **100.00%** |
| 29 | 0.0210 | 100.00% |

## Three findings

**1. The sparse-frequency picture reproduces exactly.** The five frequencies
`{14, 35, 41, 42, 52}` carry 100.00% of the non-DC power, matching the set
recorded from the earlier checkpoint inspection. Going to K=6 or K=8 moves the
total defect by 0.026 (12.408 → 12.434): there is nothing spectral left to find.

**2. The defect consumes ~47% of the ideal margin.** A pure 5-frequency clock
would decide with margin 18.30; the network delivers 9.605. The loss is almost
entirely the *composition* defect (12.01) — the logits are not a function of
`a+b` alone — and essentially none of it is missing frequencies. This is the
main new quantitative statement about the network.

**3. A global sup-norm certificate provably cannot work.** With `ε = 12.41`
against a clock margin of 18.30,

```
margin − 2ε = −6.52      (K=1: −68.9,  K=3: −36.7,  K=6: −6.46,  K=8: −6.44)
```

so the global form of `failureSet_subset_smallMargin` is unusable at *every* K.
Only the per-input form survives:

| bound | certified |
|---|---|
| per-input symmetric, `m_clock > 2·d(a,b)` where `d(a,b) = max_c \|defect\|` | 12584/12769 (**98.55%**) |
| sharp, `m_clock + d[a,b,s] − max_{c≠s} d[a,b,c] > 0` | 12769/12769 (**100%**), min slack **+0.1616** |

This is exactly the margin-versus-error discipline the project is built on:
global correctness is the wrong shape of claim, per-input margin is the right
one, and here the data *forces* that rather than merely permitting it.

## Caveat on the 100% figure

The sharp bound uses the realized per-input defects, so it is a **decomposition,
not a compression** — obtaining those defects costs as much as obtaining the
logits. Its value is structural: it shows the clock accounts for the margin and
localizes precisely what does not. A self-contained certificate needs defect
bounds derived independently of the readout (e.g. from the weights), which is
the real open problem for #2g.

## Proposed Lean shape

Parametric, in a new `ModAddRepresentation.lean`, bridging to the existing
`Flean/Operations/ModAddClock.lean`:

- `clockApprox K G : ℕ → R` — the trig polynomial with amplitudes/phases `G`;
- `defect L K G a b c := L a b c − clockApprox …` ;
- `correct_of_defect_lt_margin` — per-input: `m_clock + d_s − max_{c≠s} d_c > 0`
  implies the true sum is the strict argmax of `L a b ·`;
- accuracy bound `1 − |{(a,b) : 2·d(a,b) ≥ m_clock}| / p²`, instantiated at the
  98.55% figure, with the exact clock instance (`clockLogit`) as the reference
  case where all defects vanish and the bound degenerates to `correct_everywhere`.
