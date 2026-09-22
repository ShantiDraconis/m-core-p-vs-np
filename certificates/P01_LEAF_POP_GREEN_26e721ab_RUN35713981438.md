# P01 Leaf-Pop Certificate

Status: GREEN / FROZEN / CERTIFIED SUBGATE

Source SHA: 26e721ab25425d62312945200baa9c127910d320
Frozen branch: frozen/p01-leaf-pop-green-26e721ab
ATK P01 clean run: 35713981438 — SUCCESS

Certified scope:
- state-13 rightmost-active pop search;
- false-tombstone scan invariant;
- transition on the rightmost active true into state 14;
- exact connection from afterEndMoveLeft to leaf pop scan;
- decomposed logical popSlot suffix realization;
- source hygiene, Lean build, and axiom audit for macro/return/leaf chain.

Explicitly NOT certified:
- complete state-14/state-15 source-check return;
- complete leaf accept/reject/rewind semantics;
- SlotParserMachineSimulationCertificate;
- CanonicalRecursiveParserOperationalGap;
- CanonicalSATMachineClosure;
- P01 final;
- P02 or P != NP.

P01 endpoint remains OPEN.
