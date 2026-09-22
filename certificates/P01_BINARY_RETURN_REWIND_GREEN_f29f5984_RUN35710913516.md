# P01 BINARY RETURN / REWIND MACRO — GREEN

Repository: ShantiDraconis/m-core-p-vs-np
Source SHA: f29f5984a92d7681887801e50ec2b6143d9f7ee4
Chain: P01 HARD
Gate: binary work-log return + delimiter crossing + unread-source rewind
Classification: GREEN SUBGATE / P01 HARD REMAINS OPEN

Verified runs at source SHA:
- P01 parser macro: 35710913516 — SUCCESS
- P01 HARD regression: 35710913421 — SUCCESS
- P02 regression: 35710913464 — SUCCESS
- G3 source provenance: 35710913408 — SUCCESS
- External regression: 35710913448 — SUCCESS
- certificate: 35710913462 — SUCCESS

Formal payload includes:
- binaryReturnConfig
- binaryReturn_step_cons
- binaryReturn_run
- afterEndMoveLeft_binary_eq_return
- binary_afterEnd_to_delimiter
- binaryCheckConfig
- binaryReturn_step_delimiter_nonempty
- binaryCheck_step_to_rewind
- binary_delimiter_enters_rewind
- binary_afterEnd_roundtrip

Lineage:
- ac5f76f3e83319fe4e3d189c8863cf1854824c84 — binary return reverse-log shape GREEN
- 2f3b246030641993e755e3976afcd4d9a4c9ac05 — post-head return/rewind attempt, parser macro RED
- 5f0c4b7337d65de1f3713b15b5b72750702ca60d — explicit delimiter/rewind attempt, parser macro RED
- e6447622016cf9e22a3a71807504d1f6294501f6 — source-left invariant repair, parser macro RED
- f29f5984a92d7681887801e50ec2b6143d9f7ee4 — zero-fuel tail repair, all relevant workflows SUCCESS

Boundary:
This certificate closes only the binary parser macro subgate.
It does NOT inhabit SlotParserMachineSimulationCertificate and does NOT close
CanonicalRecursiveParserOperationalGap, CanonicalSATMachineClosure, P01 HARD,
FINAL_INTERNAL, or FINAL_EXTERNAL.

Promotion:
P01 binary return/rewind: GREEN → FROZEN → CERTIFIED
P01 HARD: OPEN / ATTACK
