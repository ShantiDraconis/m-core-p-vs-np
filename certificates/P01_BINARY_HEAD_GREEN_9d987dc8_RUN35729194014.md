# P01 BINARY-HEAD PARSER DELTA — GREEN / FROZEN / CERTIFIED

Repository: ShantiDraconis/m-core-p-vs-np
Source SHA: 9d987dc8161bfc7bcb371d4624532356fe32a89f
Source branch: attack/p01-binary-head-clean-20260922
Primary verified run: 35729194014 — ATK P01 parser macro — SUCCESS
Generic certificate run: 35729193992 — certificate — SUCCESS

Classification:
- P01_BINARY_HEAD = GREEN
- P01 parser macro chain = GREEN at this source
- P01_HARD = OPEN

Verified payload includes:
- MCore.Real.CanonicalSATParserBinaryHeadProof.and_head_roundtrip_nonempty
- MCore.Real.CanonicalSATParserBinaryHeadProof.or_head_roundtrip_nonempty
- MCore.Real.CanonicalSATParserBinaryHeadProof.and_head_exhausted_rejects
- MCore.Real.CanonicalSATParserBinaryHeadProof.or_head_exhausted_rejects
- MCore.Real.CanonicalSATParserGlobalSpec.logParseCore_eq_slotParseCore
- MCore.Real.CanonicalSATParserGlobalSpec.logAccept_iff_slotAccept

CI result:
- CanonicalSATParserBinaryHeadProof built successfully
- axiom audit passed with no sorryAx in the audited parser chain
- endpoint firewall printed P01_BINARY_HEAD=GREEN_IF_JOB_SUCCEEDS
- endpoint firewall preserved P01_HARD=OPEN

Scope:
This certificate freezes only the clean binary-head/global-slotlog parser delta.
It does not construct P01MachineConstruction, does not close P01ConstructionGap,
and does not issue FINAL_EXTERNAL.
