# ATK GREEN FREEZE LEDGER — 2026-09-22

Policy: CLOSE/FREEZE ONLY VERIFIED GREEN SUBGATES.
No OPEN, OPEN_MATH, OPEN_SOURCE_FIDELITY, or OPEN final endpoint is promoted.

Checkpoint before this ledger:
- attack SHA: 9d6dd9575a61782c70137abff348356f805bc654

## P01

### GREEN / reused frozen
- parser macro
  - frozen/p01-parser-macro-green-db716cec
  - cert/p01-parser-macro-db716cec-run35709328356
  - regression at 9d6dd957: run 35721311881 SUCCESS
- leaf-pop
  - frozen/p01-leaf-pop-green-eb492843
  - cert/p01-leaf-pop-eb492843-run35720014541
  - regression at 9d6dd957: run 35721311903 SUCCESS
- clean operational SAT
  - existing certified P01 operational chain retained
  - regression at 9d6dd957: run 35721312030 SUCCESS

### GREEN / newly frozen
- P01 HARD scaffold only
  - source: 9d6dd9575a61782c70137abff348356f805bc654
  - run: 35721236027 SUCCESS
  - frozen/p01-hard-scaffold-green-9d6dd957
  - cert/p01-hard-scaffold-9d6dd957-run35721236027
  - certificate commit: 44b9787d6c7c8ec02366849424cc09183931f825

### NOT FROZEN AS ENDPOINT
- P01_HARD = OPEN
- exact remaining payload: inhabit P01MachineConstruction and discharge the no-input final promotion.

## P02 / G2

### GREEN / frozen / certified
- G2.0 normalization
  - frozen/p02-g2-0-normalization-green-d72e53bc
  - cert/p02-g2-0-normalization-d72e53bc-run35707286302
- semantic diagonal transformer
  - frozen/p02-semantic-diagonal-transformer-green-f29f5984
  - cert/p02-semantic-diagonal-transformer-f29f5984-run35710913464
- literal fixed-point firewall
  - frozen/p02-literal-fixed-point-firewall-green-26e721ab
  - cert/p02-literal-fixed-point-firewall-26e721ab-run35713976797
- literal fixed-point countermodel
  - source: 9d6dd9575a61782c70137abff348356f805bc654
  - run: 35721311898 SUCCESS
  - frozen/p02-literal-fixed-point-countermodel-green-9d6dd957
  - cert/p02-literal-fixed-point-countermodel-9d6dd957-run35721311898
  - cert commit: cb1e30ec759f6ccb6f9f813693164fb945a287cb
- route-level falsification certificate retained
  - source: 17c04b62d03946aab4573894833f087ade25bc33
  - run: 35721158651 SUCCESS
  - frozen/p02-g2-1-literal-fixed-point-falsified-17c04b62
  - cert/p02-g2-1-literal-fixed-point-falsified-17c04b62-run35721158651
  - cert commit: 3b2fb5e392c7006830d8730578dead24b30d75b6

### NOT FROZEN AS FINAL P02
Current P02 normalization-frontier run 35721236038 succeeded as a build/audit,
but its boundary still declares:
- G2_1 = OPEN_MATH
- P02_FINAL = OPEN

Therefore no P02 FINAL freeze is issued.

## G3

### GREEN / reused frozen
Current regression: run 35721236017 SUCCESS.

- source provenance
  - frozen/g3-cook-cmi-provenance-green-f29f5984
  - cert/g3-cook-cmi-provenance-f29f5984-run35710913408
- normalized DTM two-way
  - frozen/g3-normalized-dtm-two-way-green-26e721ab
  - cert/g3-normalized-dtm-two-way-26e721ab-run35713976730
- normalized NTM two-way
  - frozen/g3-normalized-ntm-two-way-green-77070515
  - cert/g3-normalized-ntm-two-way-77070515-run35715054272
- normalized four-way/model bridge
  - frozen/g3-normalized-four-way-green-3f04da00
  - cert/g3-normalized-four-way-3f04da00-run35715387641
- normalized external contract
  - frozen/g3-normalized-external-contract-green-f2cafea7
  - cert/g3-normalized-external-contract-f2cafea7-run35719428075

### NOT FROZEN AS OFFICIAL MATCH
The successful G3 run explicitly preserves:
- G3_SOURCE_FIDELITY = OPEN
- G3_MODEL_MATCH = OPEN_SOURCE_FIDELITY

No official/source-fidelity endpoint freeze is issued.

## External

### GREEN scaffold / reused frozen
Current external scaffold regression: run 35721236073 SUCCESS.
- frozen/g3-external-contract-scaffold-green-97a95327
- cert/g3-external-contract-scaffold-97a95327-run35707370601

### NOT FROZEN
- FINAL_EXTERNAL = OPEN

## Freeze invariant

A branch named frozen/* or cert/* in this ledger means only the named subgate is frozen.
It must not be interpreted as closing a parent endpoint whose own CI boundary remains OPEN.
