# ATK STOP / RECOVERY CHAIN — 2026-09-22

## Stop point

Attack branch:
`attack/p01-hard-realization-20260922`

Stopped HEAD:
`bb65456b7198d71c127d07e47de288a902654033`

No GitHub Actions runs were active when this recovery snapshot was created.

Current blocking RED:
- workflow: `ATK P02 normalization frontier`
- run: `35715538906`
- SHA: `bb65456b7198d71c127d07e47de288a902654033`
- file: `lean/MCore/Real/P02LiteralFixedPointCountermodel.lean`
- failure: Lean could not synthesize `Decidable` for the concrete `HaltsWithin` propositions at the falseBits and trueBits correctness proofs.
- downstream printed `sorryAx` only because the file failed to elaborate; this SHA is RED and is not promoted.

The recovery chain stops here. No RED source is frozen or certified.

---

## P01 chain recovered

Certified/frozen anchors already present:

1. Clean source
   - frozen: `frozen/p01-clean-source-green-f4e2215b`
   - source SHA: `f4e2215b65aab2bef2f16b131e3dad7105994aee`
   - cert: `cert/p01-clean-source-f4e2215b-run35669003760`
   - cert commit: `ab4ffd1a98d92af38447db24854a9d9ac0f9df5a`

2. Component fail-proof
   - frozen: `frozen/p01-component-failproof-green-9e21b631`
   - source SHA: `9e21b631cd56bf49376b9e4a391b3cde45af60da`
   - cert: `cert/p01-component-failproof-9e21b631-run35586024302`
   - cert commit: `8062b709d7d3c2b7ab046794afde99de1c03c2e4`

3. Verified relation
   - frozen: `frozen/p01-verified-relation-green-1453539c`
   - source SHA: `1453539c13ba5224d1b84198f162075741a12a98`
   - cert: `cert/p01-verified-relation-1453539c-run35587134807`
   - cert commit: `a568bad3492e8042a1f70fe666f0ce1a2a1ecaed`

4. Operational prefix
   - frozen: `frozen/p01-operational-prefix-green-50859a9f`
   - source SHA: `50859a9fe3b4b4ef77ad212cd2bb570453200e0a`
   - cert: `cert/p01-operational-prefix-50859a9f`

5. Parser components
   - frozen: `frozen/p01-parser-components-green-fc20887e`
   - source SHA: `fc20887e556091a4775080ab23ee1ff61917040e`
   - cert: `cert/p01-parser-components-fc20887e-run35700922856`
   - cert commit: `2043a76bc04157c4c6c74ef5fc82ad28c1852f45`

6. TM→NTM integration prefix
   - frozen: `frozen/p01-integration-prefix-green-ada18eed`
   - source SHA: `ada18eeddb72490e44a9c6033d63690a416a7f0b`
   - cert: `cert/p01-integration-prefix-ada18eed-run35699864579`
   - cert commit: `d909103f75087f41711c697aca400e53df4a4b82`

7. Parser macro
   - frozen: `frozen/p01-parser-macro-green-db716cec`
   - source SHA: `db716cec19ddbba552f5b91f865089abd4eea9e5`
   - cert: `cert/p01-parser-macro-db716cec-run35709328356`
   - cert commit: `b0ff13266c2615dd38e38b722a0485911a6f32a2`

8. Binary return / rewind
   - frozen: `frozen/p01-binary-return-rewind-green-f29f5984`
   - source SHA: `f29f5984a92d7681887801e50ec2b6143d9f7ee4`
   - cert: `cert/p01-binary-return-rewind-f29f5984-run35710913516`
   - cert commit: `cab90e15d5347163b5bbc5536ec2bb28e9efff06`

9. Leaf-pop
   - frozen: `frozen/p01-leaf-pop-green-26e721ab`
   - source SHA: `26e721ab25425d62312945200baa9c127910d320`
   - cert: `cert/p01-leaf-pop-26e721ab-run35713981438`
   - cert commit: `11682c2313ba69b7c090460690b96fb85412d8f2`

10. Leaf-pop operational
    - frozen: `frozen/p01-leaf-pop-operational-green-26e721ab`
    - source SHA: `26e721ab25425d62312945200baa9c127910d320`
    - cert: `cert/p01-leaf-pop-operational-26e721ab-run35713981438`
    - cert commit: `8510823d9544abec032d540b57b0762c4d468cc8`

Validated later P01 work that was not separately frozen/certified before the stop:
- `a2c42957f7553b8269f403eb374ec43692dd8215` — leaf post-pop state14/15 return scan source.
- `72aa7be339ddcde8ffd83527a3bf0b932879cd45` — dedicated P01 parser-macro audit SUCCESS (`35714475319`) and P01 clean operational SAT SUCCESS (`35714480250`); no dedicated frozen/cert ref recovered for this subgate.
- `bb65456b...` — P01 parser macro SUCCESS `35715539111`, P01 HARD scaffold SUCCESS `35715538926`, P01 clean operational SAT SUCCESS `35715544699`. P01 HARD endpoint is still OPEN.

P01 endpoint status at stop:
`OPEN / ATTACK`

---

## P02 / G2 chain recovered

1. G2.0 canonical normalization
   - frozen: `frozen/g2-0-canonical-normalization-green-77ed8275`
   - source SHA: `77ed82750762fa3057c96f340254f522681ccdee`
   - cert: `cert/g2-0-canonical-normalization-77ed8275-run35704042568`
   - cert commit: `649806b2e9849b255fb8eb0d576930878d27219a`

2. G2.0 later normalized checkpoint
   - frozen: `frozen/p02-g2-0-normalization-green-d72e53bc`
   - source SHA: `d72e53bc7f667c75a432226a23adc59a255c5652`
   - cert: `cert/p02-g2-0-normalization-d72e53bc-run35707286302`
   - cert commit: `3c244256a4cf46b9e43b0934495eb7298fdbfda8`

3. Semantic diagonal transformer
   - frozen: `frozen/p02-semantic-diagonal-transformer-green-f29f5984`
   - source SHA: `f29f5984a92d7681887801e50ec2b6143d9f7ee4`
   - cert: `cert/p02-semantic-diagonal-transformer-f29f5984-run35710913464`
   - cert commit: `321a1ad6f0205eb2795939655ed802a9114de480`

4. Literal fixed-point firewall
   - frozen: `frozen/p02-literal-fixed-point-firewall-green-26e721ab`
   - source SHA: `26e721ab25425d62312945200baa9c127910d320`
   - cert: `cert/p02-literal-fixed-point-firewall-26e721ab-run35713976797`
   - cert commit: `01de3cf83d79338db8b9d4740c37719d3b9cca4c`

Countermodel attempt:
- `29c70bb1de8b64b3ef3df44b4fa6a79cb1e0d739` — source added; all pre-existing workflows were SUCCESS, but the new countermodel file was not yet included in the P02 build gate at this SHA.
- `bb65456b7198d71c127d07e47de288a902654033` — CI was extended to audit the countermodel; P02 run `35715538906` RED on missing `Decidable` instances. This is the exact current stop.

Therefore the last certified P02 mathematical checkpoint remains:
`26e721ab25425d62312945200baa9c127910d320`

G2.1 fixed-point existence remains:
`OPEN_MATH`

G2.2/G2.3 remain:
`CONDITIONAL`

P02 FINAL:
`OPEN`

---

## G3 / external chain recovered

1. External contract scaffold
   - frozen: `frozen/g3-external-contract-scaffold-green-97a95327`
   - source SHA: `97a95327360c3d4fc29dae1453330974e5f30519`
   - cert: `cert/g3-external-contract-scaffold-97a95327-run35707370601`
   - cert commit: `8a0ecfcad1fd3806f16abb481010ce5631a5055d`

2. Cook/CMI provenance
   - frozen: `frozen/g3-cook-cmi-provenance-green-f29f5984`
   - source SHA: `f29f5984a92d7681887801e50ec2b6143d9f7ee4`
   - cert: `cert/g3-cook-cmi-provenance-f29f5984-run35710913408`
   - cert commit: `81a8ce7ee18bce83a6f5048f5e5f0dc62edfd45f`

3. Normalized deterministic two-way bridge
   - frozen: `frozen/g3-normalized-dtm-two-way-green-26e721ab`
   - source SHA: `26e721ab25425d62312945200baa9c127910d320`
   - cert: `cert/g3-normalized-dtm-two-way-26e721ab-run35713976730`
   - cert commit: `ffadd26536e73d9b58f63cba5e2d3b381693e595`

Later validated G3 source progression not recovered as dedicated frozen refs:
- `1784a3bd040b5cef544d9025047a49705b4b18b3` — nondeterministic two-way bridge source.
- `8d55490c0b2d0759bbc6e0de81d0a209f2c08e73` — first dedicated NTM audit; G3 source job RED.
- `170a6350c4e0e1099dbb75393d0f36a841dff58a` — NTM simulation repair.
- `7707051580cd4e4685e30c8206cfdc060ae1b1ab` — successor/runBranches rewrite repair.
- `e5f68f93dae3e454ded57e22c4f0285740f4b57b` — assembled normalized four-way bridge source.
- `f9e7ed4eb5037d67376191ad2f0381795078be51` — assembled bridge audit; G3 source job RED.
- `3f04da0076dc9cf7e244a62fa729d98f0a21e612` — identity-cost tail fixed; G3 source provenance run `35715387641` SUCCESS, External scaffold `35715387657` SUCCESS, all parallel regressions SUCCESS.
- no dedicated frozen/cert ref for the assembled four-way bridge was present at stop.

G3 endpoint status at stop:
- DTM two-way bridge: FROZEN/CERTIFIED.
- later NTM/four-way source: VALIDATED at `3f04da00...` but not recovered as a dedicated frozen/cert ref.
- official/source-fidelity endpoint: OPEN_CONSTRUCTION.
- FINAL_EXTERNAL: BLOCKED.

---

## Supporting canonical SAT certified foundations recovered

- `frozen/canonical-sat-frame-encoding-green-16c86a4c`
  / `cert/canonical-sat-frame-encoding-16c86a4c-run35534708302`
- `frozen/canonical-sat-ntm-scanner-green-20572d56`
  / `cert/canonical-sat-ntm-scanner-20572d56-run35534056088`
- `frozen/canonical-sat-tag-parser-green-b26a7639`
  / `cert/canonical-sat-tag-parser-b26a7639-run35534504881`
- `frozen/canonical-sat-unary-parser-green-006dbbae`
  / `cert/canonical-sat-unary-parser-006dbbae-run35534601547`
- `frozen/frame-tape-gate-hardened-green-8c1e22c`
  / `cert/frame-tape-gate-hardened-8c1e22c-run35539620103`
- `frozen/sat-machine-interface-green-de1200d3`
  / `cert/sat-machine-interface-de1200d3-run35508745285`
- `frozen/sat-machine-hardened-green-7ab06d04`
  / `cert/sat-machine-hardened-7ab06d04-run35508933565`
- `frozen/sat-semantics-green-5b483a7f`
  / `cert/sat-semantics-5b483a7f-run35508513530`

---

## Exact chain at stop

```text
P01 foundations
  → parser components
  → TM→NTM integration
  → parser macro
  → binary return/rewind
  → leaf-pop / leaf-pop operational
  → state14/15 return scan [VALIDATED_UNFROZEN]
  → P01 HARD [OPEN]

P02
  G2.0 normalization [FROZEN/CERTIFIED]
  → semantic diagonal transformer [FROZEN/CERTIFIED]
  → literal fixed-point firewall [FROZEN/CERTIFIED]
  → literal fixed-point countermodel [RED at bb65456b / run 35715538906]
  → G2.1 [OPEN_MATH]
  → G2.2/G2.3 [CONDITIONAL]
  → P02 FINAL [OPEN]

G3
  external contract [FROZEN/CERTIFIED]
  → Cook/CMI provenance [FROZEN/CERTIFIED]
  → normalized DTM two-way [FROZEN/CERTIFIED]
  → NTM/four-way bridge [VALIDATED_UNFROZEN at 3f04da00]
  → source fidelity/model-match endpoint [OPEN_CONSTRUCTION]

FINAL_INTERNAL = BLOCKED G1+G2
FINAL_EXTERNAL = BLOCKED G1+G2+G3
FINAL_EXTERNAL_ISSUED = false
```

## Restart rule

If work resumes, do not restart from old RED attempts and do not rerun frozen gates without a compatibility reason.

Resume points:
- P01: after leaf-pop operational / state14-15 return scan.
- P02: repair only `P02LiteralFixedPointCountermodel.lean` from the RED `bb65456b...`; certified fallback remains `26e721ab...`.
- G3: resume from validated `3f04da00...`, while keeping `26e721ab...` as the last dedicated frozen/certified DTM bridge checkpoint.

No final proof is claimed by this recovery ledger.


---

## Missing certificates recovered after stop

All GREEN subgates that had dedicated successful validation but lacked a dedicated freeze/certificate ref have now been promoted.

### P01 state14/15 return scan
- source SHA: `72aa7be339ddcde8ffd83527a3bf0b932879cd45`
- frozen: `frozen/p01-leaf-state14-15-return-green-72aa7be3`
- cert: `cert/p01-leaf-state14-15-return-72aa7be3-run35714475319`
- cert tip: `8b6360e9f334e4a11084f6ddd833123975b02190`
- certificate SHA256: `75a688b7fd150d803fa2c9b698970aa7206a3c3fd839fff940d9e9cae79da62b`

### G3 normalized NTM two-way bridge
- source SHA: `7707051580cd4e4685e30c8206cfdc060ae1b1ab`
- frozen: `frozen/g3-normalized-ntm-two-way-green-77070515`
- cert: `cert/g3-normalized-ntm-two-way-77070515-run35715054272`
- cert tip: `0320de1f6993adcc5a06e5d3ba1da2963ed9aed5`
- certificate SHA256: `6895a971bf3ca273817b1b8b8c8ff59036e6c613f093b28db6a2bc5c1e9172be`

### G3 normalized four-way bridge
- source SHA: `3f04da0076dc9cf7e244a62fa729d98f0a21e612`
- frozen: `frozen/g3-normalized-four-way-green-3f04da00`
- cert: `cert/g3-normalized-four-way-3f04da00-run35715387641`
- cert tip: `0fda1584b6a2ed22610c6dbd7140f004423dbc30`
- certificate SHA256: `9c93b698badd1eebc2ca0370f0df7f9d86a6dd38c8a052b4fdd84896cea8d284`

### Remaining non-certifiable frontier

- P01 HARD: OPEN.
- P02 literal fixed-point countermodel: RED at `bb65456b7198d71c127d07e47de288a902654033`, run `35715538906`; skipped as requested.
- G2.1 diagonal fixed-point existence: OPEN_MATH.
- G2.2/G2.3: CONDITIONAL.
- G3 source-fidelity/model-identification endpoint: OPEN_CONSTRUCTION.
- FINAL_INTERNAL: BLOCKED.
- FINAL_EXTERNAL: BLOCKED.

No remaining `VALIDATED_UNFROZEN` subgate from the recovered stop set is left without a dedicated freeze/certificate ref.
