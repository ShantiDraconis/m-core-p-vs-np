# P01 LEAF POP / CLEAN OPERATIONAL PREFIX — GREEN

Repository: ShantiDraconis/m-core-p-vs-np
Source SHA: 26e721ab25425d62312945200baa9c127910d320
Chain: P01 HARD
Gate: leaf rightmost-active pop macro + clean operational regression
Classification: GREEN SUBGATE / P01 HARD REMAINS OPEN

Verified runs:
- P01 parser macro: 35713976753 — SUCCESS
- P01 clean operational SAT: 35713981438 — SUCCESS
- P01 HARD regression: 35713976909 — SUCCESS
- P02 regression: 35713976797 — SUCCESS
- G3 source/model regression: 35713976730 — SUCCESS
- External regression: 35713976744 — SUCCESS
- certificate: 35713976806 — SUCCESS

Formal payload includes:
- replicate_option_false_rotate
- leafPop_run_false_prefix
- afterEndMoveLeft_leaf_eq_popScan
- leaf_pop_decomposed
- previously certified binary return / rewind macro

Boundary:
This closes the state-13 rightmost-active-slot pop subgate and validates the recovered P01 operational prefix.
It does NOT inhabit SlotParserMachineSimulationCertificate, CanonicalRecursiveParserOperationalGap,
CanonicalSATMachineClosure, or P01 HARD.

Promotion:
P01 leaf-pop operational prefix: GREEN → FROZEN → CERTIFIED
P01 HARD: OPEN / ATTACK
