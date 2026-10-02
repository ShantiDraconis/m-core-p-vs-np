# T02 / P02 consolidated frontier — dac7a413

## Anchor

- Source commit: `dac7a41398ba2ad18d810b1b719f207f31a56126`
- Audit anchor: `audit/p02-odd-semantic-recurrence-dac7a413`
- Structural file: `lean/MCore/Real/P02OddSemanticRecurrence.lean`
- Status: `SOURCE | STRUCTURAL_TARGET=FORMALIZED | BUILD_PENDING | MATERIAL_GAPS=1`
- Scientific promotion: **none**
- Current OPEN_MATH: `TotalOddSemanticRecurrence`

This document records the current frontier only. It does not certify a successful Lean build and must not be used as a GREEN/FROZEN certificate until a build log is attached.

## Canonical material chain

For a deterministic polynomial-time candidate `M` with declared total clock, define

`R_M(x) := (complementSemanticReduction M hTotal).reduce x`.

The current Cook–Levin implementation is definitionally

`R_M(x) = encodeCircuit (boundedExecCircuit_NTM (complementToNTMCandidate M) x (M.timeBound x.length))`.

The already formalized semantic bridge is

`CanonicalSAT (R_M x) ↔ ¬ DeclaredAccepts M x`.

The exact producer retained by the P02 frontier is

```lean
structure TotalCandidateInvariantProducer where
  witness :
    ∀ M : PolyDTMCandidate,
      DeclaredClockTotal M → BitString
  invariant :
    ∀ (M : PolyDTMCandidate)
      (hTotal : DeclaredClockTotal M),
      DeclaredAccepts M
          ((complementSemanticReduction M hTotal).reduce
            (witness M hTotal)) ↔
        DeclaredAccepts M (witness M hTotal)
```

An inhabitant mechanically yields

`UniversalCounterexampleProducer → UniversalFailure CanonicalSAT ↔ ¬ InP CanonicalSAT → PneqNP`

using the frozen P01 SAT-in-NP result for the final separation step.

## Odd semantic recurrence reduction

The branch now contains:

- `Orbit R x0`
- `ObsEquiv M u v := DeclaredAccepts M u ↔ DeclaredAccepts M v`
- `OddGap i j := ∃ d, j = i + (2*d+1)`
- `OddSemanticRecurrence M R`

and proves, without a new open assumption,

`OddSemanticRecurrence → adjacent ObsEquiv → TotalCandidateInvariantProducer`.

Hence the remaining material target can be written as

```lean
def TotalOddSemanticRecurrence : Prop :=
  ∀ (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M),
    OddSemanticRecurrence M
      (complementSemanticReduction M hTotal).reduce
```

This is not currently proven.

## Anti-circularity / FlipState

`FlipState` gives a total alternating dynamics where every step negates the observation. The audit proves that odd-separated orbit points cannot be observationally equivalent.

Therefore the following kinds of properties are insufficient by themselves:

- growth of the reduction output,
- injectivity,
- source recoverability / decodability,
- computability / polynomial-time construction,
- the semantic flip `SAT(R_M x) ↔ ¬M(x)`.

Any future candidate property that is also satisfied by the abstract alternating model cannot decrease `MATERIAL_GAPS`.

## Exact tableau implementation

The real tableau decomposes as

```lean
boundedExecTableauCNF_NTM M x t :=
  ntmInitialCNF M x t ++
  ntmTransitionsCNF M x t ++
  ntmFinalAcceptanceCNF M t

boundedExecCircuit_NTM M x t :=
  ntmCNFCircuit (boundedExecTableauCNF_NTM M x t)
```

The input enters the tableau through `inputTape x` in `ntmInitialCNF`, which fixes:

- the initial state,
- the initial head symbol,
- the initial left tape cells,
- the initial right tape cells.

Thus the source bitstring is not present as a single literal AST subcircuit `encodeInput x`; it is represented by initial-configuration constraints.

`encodeCircuit` has an already-proved inverse-on-range theorem:

`decodeCircuit (encodeCircuit c) = some c`.

A first technical theorem worth extracting is therefore:

```lean
decodeCircuit (R_M x)
  =
some
  (boundedExecCircuit_NTM
    (complementToNTMCandidate M)
    x
    (M.timeBound x.length))
```

This is expected to be definitional/simp-level plumbing, not OPEN_MATH.

## Next technical frontier: source recovery and tableau factorization

The next non-circular technical work is:

1. characterize the initial-configuration clauses generated from `inputTape x`;
2. prove uniqueness/recovery of the source from those initial constraints when the relevant length/radius metadata is retained;
3. define a source decoder for the range of the real reduction;
4. factor the tableau into a machine/time/length template plus an input instantiation.

Target shape:

```text
Tableau(M,x,t)
  = Instantiate(Template(M, |x|, t), x)
```

These results would expose structure that the abstract `FlipState` does not model.

## R_M² frontier

The next genuine dynamics object is

`R_M²(x) = R_M(R_M(x))`,

i.e.

```text
encodeCircuit(
  tableau(
    complement M,
    encodeCircuit(tableau(complement M, x, t(|x|))),
    t(|R_M(x)|)
  )
)
```

The research task is to find a syntactic or semantic invariant of repeated tableau instantiation that:

1. is provable from the concrete `boundedExecCircuit_NTM` implementation;
2. is false in the abstract alternating `FlipState`;
3. forces an odd-distance observational collision.

## Sigma warning

A finite syntactic signature `Sigma` is not enough merely because it classifies tableau skeletons.

For arbitrary `M : PolyDTMCandidate`, the implication

`Sigma u = Sigma v → (DeclaredAccepts M u ↔ DeclaredAccepts M v)`

does not follow from Cook–Levin semantics: an arbitrary deterministic machine may distinguish the encodings by raw bitstring features.

Therefore a useful `Sigma` must come with an independently proved observer-refinement theorem from specific real-tableau structure; defining `Sigma := M` or embedding the target equivalence into `Sigma` is circular and forbidden.

## Current exact status

```text
P02
├── non-total candidates → timeout witness                     GREEN/previous
├── complement NTM realization                                FORMALIZED
├── Cook–Levin semantic bridge                                FORMALIZED
├── semantic failure ↔ behavioral invariance                  FORMALIZED
├── odd recurrence → invariant producer                       FORMALIZED
├── FlipState anti-model                                      FORMALIZED
├── source-recovery / template factorization                  NEXT_TECHNICAL
└── TotalOddSemanticRecurrence for the real R_M               OPEN_MATH
```

No theorem in this document should be interpreted as a proof of `P ≠ NP`. The material gap count remains exactly one until a genuine inhabitant of the terminal producer is constructed without assuming an equivalent separation statement.
