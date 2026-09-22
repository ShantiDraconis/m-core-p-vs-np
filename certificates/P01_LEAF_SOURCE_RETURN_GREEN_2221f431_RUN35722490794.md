# P01 LEAF SOURCE RETURN — GREEN / FROZEN / CERTIFIED

Repository: ShantiDraconis/m-core-p-vs-np
Source SHA: 2221f4318dbc73d0900b623e324127d19482758c
Verified run: 35722490794 — ATK P01 parser macro — SUCCESS

Classification:
- P01_PARSER_MACRO = GREEN
- P01_LEAF_SOURCE_RETURN = GREEN
- P01_HARD = OPEN

Formal payload:
- leaf16_exhausted_accepts
- leaf17_exhausted_rejects
- leaf17_step_to_rewind
- leaf17_roundtrip_to_phase

Scope:
This freezes the certified leaf pop/source-return/phase-boundary behavior only.
It does not construct P01MachineConstruction and does not close P01 HARD.
