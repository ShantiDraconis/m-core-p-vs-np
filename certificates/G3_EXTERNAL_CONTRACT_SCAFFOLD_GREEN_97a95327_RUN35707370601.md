# G3 EXTERNAL CONTRACT SCAFFOLD — GREEN

Repository: ShantiDraconis/m-core-p-vs-np
Source SHA: 97a95327360c3d4fc29dae1453330974e5f30519
Classification: GREEN scaffold / external-contract hardening only

Verified runs:
- ATK External scaffold: 35707370601 — SUCCESS
- P01 regression: 35707370588 — SUCCESS
- P02 normalization frontier regression: 35707370614 — SUCCESS
- certificate: 35707370623 — SUCCESS

Formal payload:
- OfficialModelSource
- OfficialModelSelection
- G3ModelBridge
- G3ExternalContract
- FinalExternalInputs requiring sourced G3 contract

Boundary:
This certificate validates the fail-closed interface and provenance requirements for G3.
It does NOT construct an external model equivalence, does NOT inhabit G3Gap, and does NOT issue FINAL_EXTERNAL.

Status:
G3 scaffold/source contract: GREEN → FROZEN → CERTIFIED
G3 construction: OPEN
FINAL_EXTERNAL: BLOCKED G1+G2+G3
FINAL_PROOF: 0/7
