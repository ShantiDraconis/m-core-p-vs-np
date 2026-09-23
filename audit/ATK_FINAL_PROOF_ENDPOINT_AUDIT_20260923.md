# ATK FINAL_PROOF endpoint audit — 2026-09-23

Policy: record only observed endpoint state. GREEN wiring does not imply the parent mathematical endpoint is proved. RED and OPEN_MATH remain fail-closed.

Current branch HEAD at latest audit update: `573dbd65f0c049bcd649a573ea93b3fa2a58543f`.

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

Certified/checkpoint family now registered:
- `19c7c5ea93d627d8db48fbdac870360b17e4d151` — GREEN/FROZEN/CERTIFIED checkpoint family; runs `35851683381`, `35851686239`, `35851690967`, `35851700184`.
- `3f3afb71708e597ba269b92ba7fc942428512ab6` — GREEN/CERTIFIED repair checkpoint; run `35851714159`.
- `c4627e6a313a4bbcf331c8e05864c37889369867` — GREEN/CERTIFIED progress snapshot; run `35851730333`.
- `8922bdb4bbdbb0c84e4565eea9ee8c3f2e138dd3` — certificate workflow SUCCESS; run `35853038311`.
- `3f537cb940552a117da50031def44cf66222d41f` — certificate workflow SUCCESS; run `35853041938`.
- `2650177c73798ec1db7675d099799e3ad6952173` — certificate workflow SUCCESS; run `35853046993`.
- `4b2eed73b8e731e9800cdc4d5e66828ba03d789d` — certificate workflow SUCCESS; run `35851659981`.
- HEAD `573dbd65f0c049bcd649a573ea93b3fa2a58543f`: T5 terminal bridges GREEN, run `35853271391`; certificate run `35853271430` was still running at the time this audit entry was written.

Audit state:
- FINAL_PROOF gap discovery at HEAD `573dbd65` — RED, run `35853271408`; not promoted.
- The gap-discovery workflow was repaired to build `MCore.Research.PatternCalculator` before generated formalizations.
- T5 terminal bridge workflow is GREEN at HEAD `573dbd65`.

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


## Canonical endpoint links and dependency flow

The endpoint graph below is the only promotion route accepted by this audit. An arrow means the downstream theorem/producer may consume the upstream result; it does not mean the upstream obligation is solved.

### P01 branch

`P01 parser macro`
→ `P01 leaf-pop`
→ `P01 parser/leaf operational chain`
→ `T1-A Global Parser Simulation`
→ `T1-B ParserWitnessComposition`
→ `T1-C VerifierComposition`
→ `T1-D terminal integration`
→ `P01MachineConstruction`
→ `P01ConstructionGap`
→ `SATInNPGap circuitBitEncoding`.

Current terminal state: T1-D is RED; therefore `P01ConstructionGap` is not promoted.

### P02 / Kleene branch

`EffectiveDiagonalCompiler M`
+ `Nat.Partrec.Code.fixed_point₂` (GREEN)
→ code fixed point `c*` with `eval c* = K.f c*`
→ `CanonicalSATFixedPointRealizer.bitsOf c*`
→ `valid`
+ `flips_of_fixed`
→ `DiagonalCounterexampleWitness M`
→ `DiagonalFamily`
→ `UniversalWitnessExists`
→ `G21Pointwise`
→ `P02Target`
→ `¬ InP SATTarget`.

Current terminal state:
- Kleene fixed-point theorem: GREEN.
- T5 terminal implication/equivalence bridges: GREEN.
- `flips_of_fixed`: OPEN_MATH.
- Therefore `G21Pointwise`, `P02Target`, and `¬ InP SATTarget` are not promoted.

### Forbidden P02 route

`SemanticFixedPointExistence`
→ CLOSED_BY_FALSIFICATION via `no_universal_literal_fixed_point`
→ never re-enter the promotion graph.

### Prime2 research side-channel

`Prime2 Conservative Interpretation`
→ `PatternCalculator q=3,5,7,11`
→ research-only `bitsOfCandidate.raw`
→ only if an exact standard semantic failure theorem is proved
→ may feed the P02/Kleene branch above.

Invariant: `nucleusTag` has no SAT or CorrectAt semantics. Prime2 remains RESEARCH_ONLY / ZERO_PROOF_CREDIT until an exact raw standard witness is kernel-proved.

### G3 branch

Certified source/provenance
→ certified simulation/model/encoding subgates
→ external contract infrastructure
→ `G3ExternalContract`.

Only the exact certified scope of each G3 subgate is reusable.

### Final merge

`P01ConstructionGap`
+ `G21Pointwise / P02Target`
+ `G3ExternalContract`
→ existing `FinalExternalInputs`
→ `FinalExternalCertificate`
→ `FINAL_EXTERNAL`
→ `FINAL_ROOT`
→ `FINAL_PROOF`.

### Current cut set

The minimal blockers that disconnect the graph from `FINAL_PROOF` are:

1. `T1-D terminal integration` — RED.
2. `flips_of_fixed` — OPEN_MATH.
3. `FINAL_PROOF gap discovery` — RED CI/audit gate.

Everything downstream remains READY_CONDITIONAL until these exact blockers are discharged.
