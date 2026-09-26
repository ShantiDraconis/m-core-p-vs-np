# FINAL_PROOF critical closure ledger — 2026-09-23

## 1. P01ConstructionGap

Target file:
- lean/MCore/Real/P01ConstructionGapClosure.lean

Exact terminal object:
- P01MachineConstruction

Must provide:
1. real stateCount from composed control;
2. one concrete integrated NTM;
3. blank_none;
4. real timeBound;
5. PolynomialTimeBound proof;
6. universal halting proof;
7. accepts_iff SATBits proof.

Reusable inputs:
- parser simulation/composition;
- witness generator/read machinery;
- verifier composition/full verifier.

Closure:
P01MachineConstruction -> P01ConstructionGap -> CanonicalSATMachineClosure / SATInNPGap.

## 2. cook_levin_correct

Target file:
- lean/MCore/Real/P02CookLevinSameInputClosure.lean

Exact proposition:
- CookLevinCorrect carrier

Must provide:
1. concrete circuitOf c;
2. concrete selfInput c;
3. bounded-computation/tableau encoding of M on selfInput c;
4. proof canonical SAT of encodeCircuit(circuitOf c) iff the intended negated
   bounded acceptance statement;
5. encoder/decoder correctness;
6. size/time bounds needed by the construction.

Must not use P02Target, G21 or flips_of_fixed as assumptions.

## 3. same_input_of_fixed

Target file:
- lean/MCore/Real/P02CookLevinSameInputClosure.lean

Exact proposition:
- SameInputOfFixed carrier

Must provide:
1. same carrier used by cook_levin_correct;
2. relation between compiler code semantics and selfInput;
3. transport of Nat.Partrec.Code.eval c = K.f c;
4. equality selfInput c = encodeCircuit(circuitOf c).

Must not assume a literal BitString fixed point.

ResidualRotation earns proof credit only if it constructs the existing
ResidualSameInputInvariant from real compiler/execution data.

## 4. flips_of_fixed

Already derived once 2 and 3 hold.

No independent OPEN_MATH theorem remains here:
CookLevinCorrect + SameInputOfFixed -> CookLevinSameInputData.flips_of_fixed.

## 5. P02Target

Target file:
- lean/MCore/Real/P02TargetClosure.lean

Need one uniform P02ClosureData:
1. compiler for every PolyDTMCandidate;
2. shared carrier for every candidate;
3. cook_correct for every candidate;
4. same_input for every candidate.

Then mechanically:
P02ClosureData
-> UniformCookLevinSameInputBridge
-> CanonicalSATFixedPointRealizer
-> DiagonalCounterexampleWitness
-> DiagonalFamily
-> G21Pointwise
-> P02Target.

No additional mathematical producer exists after P02ClosureData.

## 6. Final external merge

Target aggregator:
- lean/MCore/Real/FinalProofCriticalClosures.lean

Need:
- P01ClosureData;
- P02ClosureData;
- G3ExternalContract.

Then:
CriticalClosureData
-> ConsolidatedExternalInputs
-> existing FinalExternal certificate path
-> FINAL_EXTERNAL
-> FINAL_ROOT
-> FINAL_PROOF.

Fail-closed:
- no sorry/admit;
- no new axioms;
- no literal semantic fixed-point route;
- no fabricated state count, time bound, certificate, or root.
