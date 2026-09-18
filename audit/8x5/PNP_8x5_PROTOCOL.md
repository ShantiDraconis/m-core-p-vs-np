# P versus NP 8⊃5 certification — phase 0

WRITE_BRANCH: `audit/multistate-proof-refutation-v1`

## L1 HEAD_EXATO

`8527ea7d5a3a5939a9bf0d60bf954762ef6e29c0`

## L2 FROZEN_S1

`ShantiDraconis/m-core-p-vs-np@8527ea7d5a3a5939a9bf0d60bf954762ef6e29c0/lean/MCore/C12/Families.lean::c12_classical_endpoint_not_promoted`

## L3 ENDPOINT_DEFINITION

`audit/FinalEndpoint.lean::FINAL_STATEMENT`

Literal endpoint shape:

`¬ ∀ L, officialP L ↔ officialNP L`.

## L4 COMPRESSION

`audit/EndpointCompression.lean::endpoint_compression`

The endpoint follows conditionally from:
- F1 official-model match;
- F2 fixed K10 witness existence.

The C12 route additionally exposes `OPEN_BRIDGE`.

## L5 initial Sigma

Existing semantic audit evidence gives:

[
Sigma_{PNP,0}=(BLOCKING,BLOCKING,BLOCKING,BLOCKING,PENDING).
]

- HC: official model match and fixed witness bridge missing.
- Q: abstract/existential language universes do not yet match the fixed
  official language/model quantifiers.
- S: internal cost proxies are not proved equivalent to polynomial-time
  machine complexity/lower bounds.
- K: alpha=beta=1 finite experiments have no robustness theorem sufficient for
  the universal bridge.
- A: pending this new L8 audit.

## L6 residues

Primary frontiers are the existing:
- `F1_OFFICIAL_MODEL_MATCH`;
- `F2_FIXED_K10_WITNESS_EXISTENCE`;
- `OPEN_BRIDGE_C12_TO_FIXED_K10`.

No FECHADO-FECHADO-FECHADO emission is permitted.
