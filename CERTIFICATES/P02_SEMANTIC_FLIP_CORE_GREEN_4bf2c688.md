# P02 SEMANTIC FLIP CORE — GREEN FROZEN CERTIFICATE

Status: **GREEN_FROZEN_CERTIFIED**
Scope: **STRUCTURAL / SEMANTIC REDUCTION**
Does not certify: **UniversalFailure**, **SAT not in P**, or **P != NP**

Frozen source:
- SHA: `4bf2c6885c088392e0d19c7f464df07ab285305e`
- Frozen ref: `frozen/p02-semantic-flip-core-green-4bf2c688`
- Gate: `P02 Universal Failure Min-Cut`
- Run: `36868230303` — SUCCESS
- Parallel `fail-proof-all-gaps`: `36868230308` — SUCCESS

Certified kernel content:
- `P02UniversalFailureMinCut`
- `P02FailureNormalForms`
- `P02ExplicitClockNormalForm`
- `P02TotalCandidateSemanticCore`
- `P02SemanticFlipCore`

Key exact equivalences:
- candidate failure = timeout or semantic disagreement;
- universal failure = total-candidate semantic core;
- total-candidate semantic core = total-candidate semantic flip core.

Material open core after this checkpoint:
for every deterministic polynomial-time candidate which halts within its declared clock on every input, produce an input witnessing the exact semantic SAT flip.

No literal fixed-point existence is certified or assumed.
