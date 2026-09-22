# P01 BINARY-HEAD PARSER DELTA — GREEN / FROZEN / CERTIFIED

Repository: ShantiDraconis/m-core-p-vs-np
Source SHA: 0ff71d49edd9457025377fe6eaf041bea8bd2171
Frozen branch: frozen/p01-binary-head-green-0ff71d49
Certificate branch: cert/p01-binary-head-0ff71d49-run35731861724
Verified run: 35731861724 — ATK P01 parser macro — SUCCESS

Classification:
- P01_BINARY_HEAD = GREEN / FROZEN / CERTIFIED
- P01_HARD = OPEN
- T1.A global parser simulation = OPEN / IN_PROCESS

Scope:
This certificate freezes only the binary-head parser delta at source SHA 0ff71d49.
It does not promote P01ConstructionGap, does not close SlotParserMachineSimulationCertificate,
and is not merged into the clean final-proof lane because its history diverges from 9d987dc8 at 614f88fe.

Kernel/CI evidence:
- parser macro run 35731861724 SUCCESS
- certificate run 35731861789 SUCCESS
- subsequent certificate runs 35731957632 and 35731961204 SUCCESS
- PR parser macro regression 35731866819 SUCCESS
- P01 HARD scaffold regression 35731861786 SUCCESS

Endpoint:
P01ConstructionGap remains OPEN_IMPLEMENTATION.
