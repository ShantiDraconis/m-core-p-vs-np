# FINAL_PROOF clean lane — 2026-09-23

## Rule

Do not edit, replace, or reinterpret previously certified artifacts.
The clean lane is additive and imports certified/established components only as dependencies.

## Critical live path

### P01
P01MachineConstruction
-> P01FinalProofProducer.Producer
-> P01ConstructionGap / SATInNPGap

Required fields:
- stateCount
- machine
- blank_none
- timeBound
- time_poly
- halts
- accepts_iff

### P02
EffectiveDiagonalCompiler
+ Carrier(circuitOf, selfInput)
+ cook_levin_correct
+ same_input_of_fixed
-> P02FinalProofProducer.Producer
-> flips_of_fixed
-> CanonicalSATFixedPointRealizer
-> DiagonalCounterexampleWitness
-> DiagonalFamily
-> G21Pointwise
-> P02Target

There is no separate OPEN_MATH obligation after cook_levin_correct and same_input_of_fixed.

### G3
Use existing:
- CookNormalizedG3Contract.cookNormalizedExternalContract

No new G3 mathematics is required in the clean lane.

### External
P01 producer
+ P02 producer
+ existing G3 contract
-> FinalExternalInputs
-> final_external_certificate
-> OfficialPneqNP for the normalized official model selection.

## Excluded from the critical build

The following may remain in the repository but are not required to build the clean lane:
- residual/research rotation route;
- literal semantic fixed-point route;
- Prime2 research transfer;
- broad gap-discovery/audit generators;
- historical alternative P02 semantic-self-embedding routes;
- old two-gap wrappers that only repackage the same blockers.

They can be audited separately and do not gate the clean-lane build.

## Fail-closed

No:
- sorry
- admit
- new axioms/constants
- fabricated state counts or time bounds
- endpoint assumptions
- literal BitString fixed-point assumption
- fake FINAL_ROOT
