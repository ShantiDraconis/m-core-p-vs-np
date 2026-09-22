# ATK STOP / FREEZE MANIFEST — USER REQUESTED STOP

Repository: ShantiDraconis/m-core-p-vs-np
Stop baseline: f9add60881d709ce8320cb54a4d52f26d829b8f5
Policy: no further attack work after this snapshot; preserve only validated GREEN artifacts.

Frozen and certified artifacts produced in this session:

1. G2.1 literal fixed-point falsification
   - source: 17c04b62d03946aab4573894833f087ade25bc33
   - run: 35721158651 SUCCESS
   - freeze: frozen/p02-g2-1-literal-fixed-point-falsified-17c04b62
   - cert branch: cert/p02-g2-1-literal-fixed-point-falsified-17c04b62-run35721158651
   - cert tip: 3b2fb5e392c7006830d8730578dead24b30d75b6

2. P01 HARD scaffold
   - source: 9d6dd9575a61782c70137abff348356f805bc654
   - run: 35721236027 SUCCESS
   - freeze: frozen/p01-hard-scaffold-green-9d6dd957
   - cert branch: cert/p01-hard-scaffold-9d6dd957-run35721236027
   - cert tip: 44b9787d6c7c8ec02366849424cc09183931f825
   - endpoint P01_HARD remains OPEN

3. G2.2 terminal wiring
   - validated source: 38db71b416906e5b7138774842e91d3e367aad09
   - run: 35722282451 SUCCESS
   - freeze: frozen/p02-g2-2-wiring-green-38db71b4
   - cert branch: cert/p02-g2-2-wiring-38db71b4-run35722282451
   - checksum completion commit: 3eefb7e2b42955303f028cadcffe266aade2ae2a
   - G2_1_POINTWISE and P02_FINAL remain OPEN

4. P01 leaf source return
   - source: 2221f4318dbc73d0900b623e324127d19482758c
   - run: 35722490794 SUCCESS
   - freeze: frozen/p01-leaf-source-return-green-2221f431
   - cert branch: cert/p01-leaf-source-return-2221f431-run35722490794
   - checksum completion commit: 8e927cfde49b2d3a49d38baab010dd0e584c3753

5. P01 terminal branches
   - theorem source: 18c12c40545b41e63b75b1c8e99e27c6ff527335
   - validated source: f9add60881d709ce8320cb54a4d52f26d829b8f5
   - run: 35722851951 SUCCESS
   - freeze: frozen/p01-terminal-branches-green-f9add608
   - cert branch: cert/p01-terminal-branches-f9add608-run35722851951
   - cert tip: 24f5c2b966b90efb5e63a9a850319396cf73bd61
   - P01_HARD remains OPEN

6. GREEN-only audit ledger
   - source: cebe0ecd7d6178a584b6e1fc01ff82dad5988e8b
   - freeze: frozen/atk-green-freeze-ledger-cebe0ecd
   - cert branch: cert/atk-green-freeze-ledger-cebe0ecd
   - cert tip: c32144335fb2b5b1459a109575a708401811ccdd

Explicitly not promoted/frozen as solved endpoints:
- P01_HARD
- G2_1_POINTWISE
- P02_FINAL
- G3_SOURCE_FIDELITY
- G3_MODEL_MATCH official/source-fidelity endpoint
- FINAL_EXTERNAL

This manifest is a preservation record, not a proof of P != NP.
