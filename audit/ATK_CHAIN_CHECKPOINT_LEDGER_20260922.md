# ATK chain checkpoint ledger — 2026-09-22

Canonical working snapshot before this ledger:
`f29f5984a92d7681887801e50ec2b6143d9f7ee4`

This ledger records recent source SHAs that were not individually frozen, their disposition, and the canonical GREEN checkpoints that supersede them. A RED or superseded SHA is documented but is not promoted.

## P01 HARD chain

Existing certified anchors:
- `f4e2215b65aab2bef2f16b131e3dad7105994aee` — clean source GREEN/FROZEN/CERTIFIED.
- `ada18eeddb72490e44a9c6033d63690a416a7f0b` — parser TM→NTM integration prefix GREEN/FROZEN/CERTIFIED.
- `db716cec19ddbba552f5b91f865089abd4eea9e5` — parser seek/work-log macro GREEN/FROZEN/CERTIFIED.

Recent return/rewind lineage:
- `7cd8ecc8f413e5c112a2146044faa182488ef4bc` — source for binary return proof; superseded.
- `d860ead4ae57f7032c9479242c3914eec4ca2bea` — dedicated macro audit introduced; parser macro RED.
- `ac5f76f3e83319fe4e3d189c8863cf1854824c84` — reverse-log shape fixed; parser macro SUCCESS; superseded by stronger checkpoint.
- `2f3b246030641993e755e3976afcd4d9a4c9ac05` — post-head roundtrip extension; parser macro RED.
- `5f0c4b7337d65de1f3713b15b5b72750702ca60d` — explicit delimiter/rewind steps; parser macro RED.
- `e6447622016cf9e22a3a71807504d1f6294501f6` — source-left invariant repair; parser macro RED.
- `f29f5984a92d7681887801e50ec2b6143d9f7ee4` — zero-fuel tail closed; all relevant workflows SUCCESS.

Canonical new checkpoint:
- `frozen/p01-binary-return-rewind-green-f29f5984`
- `cert/p01-binary-return-rewind-f29f5984-run35710913516`
- scope: binary work-log return, delimiter crossing, unread-source rewind and roundtrip.
- P01 HARD remains OPEN.

## P02 / G2 chain

Existing certified anchor:
- `77ed82750762fa3057c96f340254f522681ccdee` — G2.0 canonical normalization GREEN/FROZEN/CERTIFIED.

Diagonal-frontier lineage:
- `b87a8c5bf9e614920eba85bf691a35b320093ce8` — fail-closed diagonal frontier formalized.
- `9a0c899004c74749bbeff4b8fb7ccd411fe4339f` — semantic diagonal transformer source introduced.
- `e7d699d6532940eaed9b1c933de49264e3a61de6` — dedicated transformer audit; P02 RED.
- `dd0411e0eca5e4f40494e5f2ed413847272ebecf` — encoding/fixed-point rewrite repaired; P02 SUCCESS.
- `f29f5984a92d7681887801e50ec2b6143d9f7ee4` — current all-regression GREEN snapshot.

Canonical new checkpoint:
- `frozen/p02-semantic-diagonal-transformer-green-f29f5984`
- `cert/p02-semantic-diagonal-transformer-f29f5984-run35710913464`
- scope: validity, exact length, semantic flip, and conditional fixed-point-to-failure wiring.
- G2.1 fixed-point existence remains OPEN_MATH.
- G2.2/G2.3 remain CONDITIONAL.
- P02 FINAL remains OPEN.

## G3 / FINAL_EXTERNAL chain

Existing certified anchor:
- `97a95327360c3d4fc29dae1453330974e5f30519` — sourced external-contract scaffold GREEN/FROZEN/CERTIFIED.

Scaffold/provenance lineage:
- `0ee39ab9a1d25e785868c635ea73c21d5a0f855f` — OfficialModel scaffold.
- `3beec2f1f235f35cb24aba8f2820efcc984d3450` — EncodingNormalization scaffold.
- `6a8a9a44976ea07f726744fe43dbfb34d81d3cf5` — G3ModelMatch scaffold.
- `20f4cf30ce0687012f8d568795e3d21a7b8d8f67` — FinalExternalCertificate fail-closed scaffold.
- `58d84bc8c2e1a45583afc7dfe31c7d5f34768385` — four simulation directions hardened with polynomial-overhead payloads.
- `1091d8632d6a3186bd724f63980ed7cf45f522cc` — external provenance required.
- `121cb7bb75443ca9664dd5860cdbc743e393fe75` — model bridge bound to explicit source contract.
- `97a95327360c3d4fc29dae1453330974e5f30519` — sourced external contract checkpoint frozen/certified.
- `067ed9f14eca60499b67130512efa1b0391247df` — Cook/CMI source record added.
- `f1a4f9d4dfb558a7f6f7efe2090794bcd8aeddba` — dedicated source-provenance workflow added and G3 source job SUCCESS.
- `f29f5984a92d7681887801e50ec2b6143d9f7ee4` — current all-regression GREEN snapshot.

Canonical new checkpoint:
- `frozen/g3-cook-cmi-provenance-green-f29f5984`
- `cert/g3-cook-cmi-provenance-f29f5984-run35710913408`
- scope: populated Cook/CMI source provenance and fail-closed source validation.
- concrete external model remains OPEN_CONSTRUCTION.
- four two-way simulations remain OPEN_CONSTRUCTION.
- G3 endpoint remains OPEN.
- FINAL_EXTERNAL remains BLOCKED G1+G2+G3.

## Current fail-closed status

- P01 HARD: OPEN / ATTACK.
- G2.0: GREEN/FROZEN/CERTIFIED.
- G2.1: OPEN_MATH.
- G2.2/G2.3: CONDITIONAL.
- G3 source provenance: GREEN/FROZEN/CERTIFIED.
- G3 model match endpoint: OPEN_CONSTRUCTION.
- FINAL_INTERNAL: BLOCKED G1+G2.
- FINAL_EXTERNAL: BLOCKED G1+G2+G3.
- FINAL_EXTERNAL_ISSUED: false.
- FINAL_ROOT: null.

No RED or merely conditional source SHA is promoted as a terminal proof.
