# FINAL_EXTERNAL chain ledger — c511da2c

Date: 2026-09-23

This ledger preserves the currently formalized terminal chain and the already frozen/certified anchors that feed it. It is fail-closed: no item is marked GREEN unless an existing frozen/cert branch with a recorded successful run exists.

## Terminal chain

`UniformCompilerValueComputable`
→ `D3SemanticSelfReference`
→ `P02Target`
→ `PneqNP`
→ `FinalExternalInputs`
→ `FINAL_EXTERNAL`

Source theorem file:
- `lean/MCore/Real/P02CompilerTerminalPromotion.lean`
- source commit: `c511da2c0e88bf858a698404e281914752f10e46`
- source freeze ref: `frozen/p02-compiler-terminal-promotion-source-c511da2c`
- state: `SOURCE / FROZEN_SOURCE`
- CI: `BUILD_PENDING`
- mathematical terminal: `UniformCompilerValueComputable = OPEN_MATH`

## Theorems introduced at c511da2c

- `compilerComputable_to_D3`
- `compilerComputable_P01_to_internal_final`
- `compilerComputable_to_FinalExternalInputs`
- `compilerComputable_P01_G3_to_external_final`
- `compilerComputable_P01_G3_to_FinalExternalGap`

These theorems introduce no replacement axiom for the open terminal; they consume `UniformCompilerValueComputable` explicitly.

## Frozen/certified anchors reused by the chain

| Role | Source SHA | Frozen ref | Certificate ref / run |
|---|---|---|---|
| P01 physical realization | `058f574bd2ad1349eb17717549ca5ad378666336` | `frozen/p01-physical-realization-green-058f574b` | `cert/p01-physical-realization-058f574b-run35785607933` |
| P01 phase bridge | `bd067a3988d70b80d154b5c532dae92384100229` | `frozen/t1-a-phase-bridge-green-bd067a39` | `cert/t1-a-phase-bridge-bd067a39-run35795773383` |
| P01 polynomial bound | `921170b335f31cfdf5b8fa120b7fd90907872990` | `frozen/t1-c-poly-bound-green-921170b3` | `cert/t1-c-poly-bound-921170b3-run35791659492` |
| P01 terminal construction checkpoint | `41f31f40a1c0e224a72f92d2b2140e0174396a16` | `frozen/atk-41f31f40` | `cert/atk-41f31f40-run35886054258` |
| G3 normalized external contract | `f2cafea7a74f3ef8ad4140943515622545c9f1d8` | `frozen/g3-normalized-external-contract-green-f2cafea7` | `cert/g3-normalized-external-contract-f2cafea7-run35719428100` |
| P02 Kleene bridge | `5f8a0aa2c6ca41d77515e3bf97bd1fa53138679d` | `frozen/p02-kleene-green-5f8a0aa2` | `cert/p02-kleene-5f8a0aa2-run35784099753` |
| P02 E1 | `0f6bcd5243ee499dc3e182b81ea98459858b6883` | `frozen/p02-e1-green-0f6bcd52` | `cert/p02-e1-0f6bcd52-run35785227242` |
| P02 E2 audit | `b6b6821b337ae70ef958d461a44156d2345d3336` | `frozen/p02-e2-audit-green-b6b6821b` | `cert/p02-e2-audit-b6b6821b-run35785134353` |
| P02 E2 math checkpoint | `8218207dd3258860cdb9859a99ab677c36880d23` | `frozen/p02-e2-math-checkpoint-green-8218207d` | `cert/p02-e2-math-checkpoint-8218207d-run35788500754` |
| Semantic mismatch algebra | `f3dc5354a6f8a652fbcda941b4f0a0e6213ddd30` | `frozen/t5-c-semantic-mismatch-green-f3dc5354` | `cert/t5-c-semantic-mismatch-f3dc5354-run35791665694` |
| Candidate coding | `a5635895dee4d7736778ce0104dfbe7016f6487a` | `frozen/t5-d-candidate-coding-green-a5635895` | `cert/t5-d-candidate-coding-a5635895-run35795602565` |
| Diagonal compiler | `8fff59efc44d1c8d5ee37190eca56ed9a5278d6f` | `frozen/t5-e-diagonal-compiler-green-8fff59ef` | `cert/t5-e-diagonal-compiler-8fff59ef-run35791673222` |
| P02 integration | `270282a55e18588dce3e7a8a9a72db2cda277d98` | `frozen/p02-integration-green-270282a5` | `cert/p02-integration-270282a5-run35787562294` |
| FINAL_EXTERNAL integration | `c102d9d482d708a7a865803e94f294c6da82ed9a` | `frozen/final-external-integration-green-c102d9d4` | `cert/final-external-integration-c102d9d4-run35722252805` |
| FINAL_EXTERNAL two-gap harness | `b406b806da58ebe6bc1f85863ee44054ad42edb2` | `frozen/final-external-two-gap-green-b406b806` | `cert/final-external-two-gap-b406b806-run35722743845` |
| Final fail-external harness | `815dfb08e719b80e82cc35a5e01988064a0b3496` | `frozen/final-fail-external-green-815dfb08` | `cert/final-fail-external-815dfb08-run35722796449` |

## Fail-closed state

- P01: READY from frozen/certified construction anchors above.
- G3: READY from normalized external contract.
- P02 compiler terminal promotion: SOURCE / FROZEN_SOURCE.
- `UniformCompilerValueComputable`: OPEN_MATH.
- `FINAL_EXTERNAL`: READY_CONDITIONAL.
- `FINAL_ROOT`: NULL.
- No FINAL_EXTERNAL issuance is asserted by this ledger.
