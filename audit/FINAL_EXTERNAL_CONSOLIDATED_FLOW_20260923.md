# FINAL_EXTERNAL consolidated flow — 2026-09-23

This audit consolidates all currently reusable GREEN/CERTIFIED work into one
fail-closed route to the repository's existing FinalExternalCertificate.

## P01 line

P01 parser/leaf certified components
→ T1-A GlobalParserSimulation
→ T1-B ParserWitnessComposition
→ T1-C VerifierComposition
→ T1-D physical/full verifier
→ P01WitnessIndexedRead*
→ P01MachineConstruction
→ P01ConstructionGap
→ SATInNPGap.

Remaining exact requirement: inhabit P01ConstructionGap from the integrated
physical machine without new assumptions.

## P02 line

P02BoundedComputation*
→ P02KleeneE1 / P02KleeneBridgeAudit
→ EffectiveDiagonalCompiler
→ Kleene fixed point
→ CookLevinSameInputData
→ cook_levin_correct
+ same_input_of_fixed
→ flips_of_fixed
→ CanonicalSATFixedPointRealizer
→ DiagonalCounterexampleWitness
→ DiagonalFamily
→ UniversalWitnessExists
→ G21Pointwise
→ P02Target.

Residual research insertion:
ResidualRotationAlgebra
→ ResidualSameInputInvariant
→ same_input_of_fixed.

P02SemanticMismatchAlgebra is reusable downstream algebra only; it does not
replace the missing same-input/Cook-Levin theorem.

Remaining exact mathematical requirements:
- cook_levin_correct
- same_input_of_fixed
Therefore flips_of_fixed remains OPEN_MATH.

## G3 line

Existing certified source/provenance/model/DTM/NTM/four-way/external-contract
infrastructure
→ G3ExternalContract.

## Final merge

P01ConstructionGap
+ P02Target
+ G3ExternalContract
→ FinalExternalInputs / FinalExternalLiveTwoProducer
→ FinalExternalCertificate
→ FINAL_EXTERNAL
→ FINAL_ROOT
→ FINAL_PROOF.

## Current blockers to an actual external certificate

1. P01ConstructionGap exact producer not yet certified in the active lane.
2. P02Target exact producer not yet available because cook_levin_correct and
   same_input_of_fixed remain OPEN_MATH.
3. G3 external contract must be present at the exact active commit used for
   final merge.
4. Only after all three producers coexist on one kernel-checked commit may
   FinalExternalCertificate be promoted.
5. FINAL_ROOT remains null until that promotion succeeds.
