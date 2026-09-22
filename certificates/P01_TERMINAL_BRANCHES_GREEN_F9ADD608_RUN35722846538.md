# P01 TERMINAL BRANCHES — GREEN / FROZEN / CERTIFIED

Repository: ShantiDraconis/m-core-p-vs-np
Source SHA: f9add60881d709ce8320cb54a4d52f26d829b8f5
Verified run: 35722846538 — ATK P01 parser macro — SUCCESS

Classification:
- P01_TERMINAL_BRANCHES = GREEN
- P01_HARD = OPEN

Formal payload:
- leaf16_residual_rejects
- leafResidualRejectConfig_halted
- binary_exhausted_rejects

Scope:
Closes the residual-source rejection branch for a completed leaf and the
source-exhausted rejection branch for binary constructors. It does not close
the global parser simulation or P01 HARD.
