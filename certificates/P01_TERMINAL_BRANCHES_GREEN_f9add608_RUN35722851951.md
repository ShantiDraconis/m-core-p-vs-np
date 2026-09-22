# P01 TERMINAL BRANCHES — GREEN / FROZEN / CERTIFIED

Repository: ShantiDraconis/m-core-p-vs-np
Validated source SHA: f9add60881d709ce8320cb54a4d52f26d829b8f5
Source theorem commit: 18c12c40545b41e63b75b1c8e99e27c6ff527335
Workflow integration commit: f9add60881d709ce8320cb54a4d52f26d829b8f5
Verified run: 35722851951 — ATK P01 parser macro — SUCCESS

Classification:
- P01_LEAF_SOURCE_RETURN = GREEN
- P01_TERMINAL_BRANCHES = GREEN
- P01_HARD = OPEN

Formal payload:
- leaf16_residual_rejects
- leafResidualRejectConfig_halted
- binary_exhausted_rejects

Scope:
This certificate freezes only the residual-source rejection and exhausted-binary
terminal parser branches together with their successful parser-macro CI audit.

It does not construct the complete SlotParserMachineSimulationCertificate.
It does not construct P01MachineConstruction.
It does not close P01 HARD, FINAL_INTERNAL, or FINAL_EXTERNAL.
