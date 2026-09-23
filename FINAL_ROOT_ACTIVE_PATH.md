# FINAL_ROOT — Active Path

This file is the single operational source of truth for the active branch.

## Active gaps

### P01
Target:
- `MCore.Real.P01FinalCertificate.P01ConstructionGap`

Shortest implementation path:
- `PhysicalMachineCore.FixedPhysicalVerifierRefinement`
- `P01FullVerifierPhysical.PhysicalVerifierRealization`
- `P01FinalCertificate.P01MachineConstruction`
- `P01ConstructionGap`
- `SATInNPGap circuitBitEncoding`

Already reusable:
- parser simulation
- witness-preserving nondeterministic preparation
- semantic verifier
- physical stack V2
- push/pop primitive machine
- witness shuttle
- uniform cost bounds
- fixed 47-state integrated layout

Do not reopen parser/leaf/macro work unless this path proves a concrete dependency is broken.

### P02
Preferred minimal target:
- `MCore.Real.P02FastPathAttack.TotalCandidateSemanticFailure`

Promotion:
- `TotalCandidateSemanticFailure`
- `TotalityOrSemanticCounterexample`
- `G21Pointwise`
- `P02Target`

The older `UniformSemanticStabilityProducer` remains a sufficient but stronger route, not the preferred target.

## Frozen negative routes

### Exact same-input
- state: RED / FROZEN / CLOSED_BY_FALSIFICATION
- anchor: `11dd4ff2beb436f6682b4a16f504a48e55a3cc86`
- reopen: FORBIDDEN

### Bounded same-input
- state: RED / FROZEN / CLOSED_BY_FALSIFICATION
- source: `49b2ba3cf73e4d1d201e9b12bb26f4ecbfc63ad6`
- certificate commit: `e78e171ecf17a7da39ff52e7bfb8f720e5e467e5`
- kernel run: `35930277832` SUCCESS
- frozen ref: `frozen/p02-bounded-same-input-falsified-e78e171e`
- reopen: FORBIDDEN

## Final promotion

Only this chain matters:

```text
P01ConstructionGap
  -> SATInNPGap

TotalCandidateSemanticFailure
  -> P02Target

SATInNPGap + P02Target + existing G3
  -> FinalExternalInputs
  -> final_external_certificate
  -> FINAL_ROOT
```

## Current normative state

- P01: OPEN
- P02 positive producer: OPEN_MATH
- G3: reuse existing certified contract
- FINAL_ROOT: NULL

No conditional theorem, falsified route, historical GREEN support artifact, or CI success may be promoted as an inhabitant of either active gap.
