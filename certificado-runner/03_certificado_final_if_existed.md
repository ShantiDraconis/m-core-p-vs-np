# CERTIFICADO FINAL — IF IT EXISTED

This document is a fail-closed target description, not a present certificate.

## Current P01 boundary

The accepted machine model is fixed by the repository:

- state: `Fin (stateCount + 1)`
- tape alphabet: `Option Bool`
- canonical bitstring input tape
- blank symbol: `none`
- polynomial time bound
- exact halting and soundness/completeness

The historical `SATRealization.lean` shortcut is not admissible because it stores arbitrary formula data in machine state and uses an input-dependent rich tape alphabet.

## Required P01 closure

A future file

`lean/MCore/Real/P01FinalCertificate.lean`

must kernel-check a theorem named:

`p01_final_certificate : CanonicalSATMachineClosure`

without `sorry`, `admit`, new axioms, hidden oracles, semantic weakening, or a parallel machine model.

That theorem must arise from a genuine finite-control implementation of:

verified SAT relation
→ recursive canonical parser/stack
→ nondeterministic witness generation
→ deterministic verification
→ `PolyNTMRealization (SATBits circuitBitEncoding)`.

## What P01 GREEN would not mean

P01 GREEN would establish SAT in NP in this hardened internal machine model.
It would **not** establish P != NP.

P02 remains the independent open mathematical obligation:

`¬ InP (SATBits circuitBitEncoding)`

or equivalently the repository's universal deterministic failure object for the same language, together with the required official-model transfer.

## Full final state, if it existed

Only after the exact terminal producers of all seven problem chains were closed,
and the independent M-Core formulation gates were also closed, could the hub report:

`7 FINAL PROOFS + 1 M-CORE FORMULATION = 8/8 GREEN_CLOSED`.

That would still be an internal formal-validation state. External prize requirements remain separate.
