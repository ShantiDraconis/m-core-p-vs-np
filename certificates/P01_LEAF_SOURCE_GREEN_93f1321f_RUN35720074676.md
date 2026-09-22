# P01 LEAF SOURCE-CHECK / REWIND MACRO — GREEN

Repository: ShantiDraconis/m-core-p-vs-np
Source SHA: 93f1321f53aa93e18c7dcbf8a8a04e2844a15cbe
Chain: P01 canonical SAT NTM realization
Gate: leaf source classification + state-17 rewind return
Classification: GREEN SUBGATE / P01 HARD REMAINS OPEN

Verified runs at source SHA:
- ATK P01 parser macro: 35720074676 — SUCCESS
- certificate workflow: 35720074584 — SUCCESS

Objects:
- MCore.Real.CanonicalSATParserLeafSourceProof.leaf16_exhausted_accepts
- MCore.Real.CanonicalSATParserLeafSourceProof.leaf17_exhausted_rejects
- MCore.Real.CanonicalSATParserLeafSourceProof.leaf17_step_to_rewind
- MCore.Real.CanonicalSATParserLeafSourceProof.leaf17_roundtrip_to_phase

Predecessors reused:
- P01 parser macro — GREEN/FROZEN/CERTIFIED
- P01 binary return/rewind — GREEN/FROZEN/CERTIFIED
- P01 leaf-pop — GREEN/FROZEN/CERTIFIED
- P01 state14/15 return scan — GREEN/FROZEN/CERTIFIED

Boundary:
This closes the local source-check/rewind macro after a successful leaf pop.
It does not yet construct the full SlotParserMachineSimulationCertificate and
does not close CanonicalSATMachineClosure.

Promotion:
P01 leaf source-check/rewind: GREEN → FROZEN → CERTIFIED
P01 HARD: OPEN
FINAL_EXTERNAL: BLOCKED
