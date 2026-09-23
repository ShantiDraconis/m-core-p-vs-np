# ATK FINAL_PROOF endpoint audit — 2026-09-23

Policy: record only observed endpoint state. GREEN wiring does not imply the parent mathematical endpoint is proved. RED and OPEN_MATH remain fail-closed.

Current branch HEAD at insertion: `2650177c73798ec1db7675d099799e3ad6952173`.

## Advanced endpoints retained in the audit

### P01 / T1

- P01 parser macro — GREEN/FROZEN/CERTIFIED anchor retained from the existing GREEN freeze ledger.
- P01 leaf-pop — GREEN/FROZEN/CERTIFIED anchor retained.
- P01 parser/leaf operational chain — GREEN/FROZEN/CERTIFIED anchor retained.
- T1-A Global Parser Simulation — GREEN producer already incorporated in the P01 construction line.
- T1-B ParserWitnessComposition — GREEN producer already incorporated.
- T1-C VerifierComposition — GREEN producer already incorporated.
- T1-D terminal integration — RED at HEAD `2650177c`, run `35853047067`; not promoted.
- P01 terminal endpoint / `P01ConstructionGap` — not promoted until T1-D closes.

### P02 / G2 / T5

- G2.0 canonical normalization — GREEN/FROZEN/CERTIFIED anchor retained.
- Semantic diagonal transformer — GREEN/FROZEN/CERTIFIED anchor retained.
- Literal fixed-point firewall/countermodel — GREEN/FROZEN/CERTIFIED as a negative result.
- Literal `SemanticFixedPointExistence` route — CLOSED_BY_FALSIFICATION; it must not be reused as a producer.
- T5 terminal bridges — GREEN at HEAD `2650177c`, run `35853046977`.
- Kleene fixed-point theorem — GREEN infrastructure.
- UniversalWitness/G21/P02 implication/equivalence wiring — GREEN infrastructure.
- Prime2 conservative research transfer — GREEN at HEAD `2650177c`, run `35853046949`; RESEARCH_ONLY / ZERO_PROOF_CREDIT unless an exact standard witness is produced.
- `flips_of_fixed` / same-input Kleene-to-canonical-SAT semantic transport — OPEN_MATH.
- `G21Pointwise` / `P02Target` terminal mathematical producer — remains OPEN_MATH until `flips_of_fixed` is inhabited without an oracle, sorry, axiom, literal string fixed point, or nucleusTag semantics.

### G3 / external infrastructure

- Existing G3 source-provenance, simulation, model/encoding and external-contract certified subgates remain retained exactly at their previously certified scopes.
- FinalExternal integration/certificate code is retained as downstream consumer infrastructure only.
- No external terminal issue is promoted while P01 or P02 exact producers are absent.

### Audit / certificate machinery

- Certificate workflow — SUCCESS on `3f537cb940552a117da50031def44cf66222d41f`, run `35853041938`.
- Earlier certificate on `4b2eed73b8e731e9800cdc4d5e66828ba03d789d` — SUCCESS, run `35851659981`.
- FINAL_PROOF gap discovery at HEAD `2650177c` — RED, run `35853047008`; not promoted.
- The gap-discovery workflow was repaired to build `MCore.Research.PatternCalculator` before generated formalizations.
- The T5 terminal bridge workflow is GREEN at the same HEAD.

## Exact remaining terminal blockers

1. T1-D must become GREEN so the exact P01 construction producer can be promoted.
2. `flips_of_fixed` must be proved kernel-valid. This is the remaining mathematical core of the Kleene-to-canonical-SAT route.
3. FINAL_PROOF audit must return GREEN after the current CI/audit repairs.

## Promotion path once the exact producers exist

`P01ConstructionGap + flips_of_fixed`
→ `DiagonalFamily`
→ `UniversalWitnessExists`
→ `G21Pointwise`
→ `P02Target`
→ existing FinalExternal integration
→ `FINAL_ROOT`
→ `FINAL_PROOF`.

## Fail-closed invariant

- A GREEN workflow for wiring, research, or certificate infrastructure is not proof of `G21Pointwise` or `P02Target`.
- Prime2 metadata, including `nucleusTag`, may not contribute SAT truth or CorrectAt failure.
- The falsified literal fixed-point route remains permanently excluded.
- `FINAL_ROOT` remains null until all exact terminal producers are kernel-valid.
