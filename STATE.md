# Current integration and proof status

The root Lean 4.19 package builds the P01 parser components restored from
`e2d24a050e5b1411fa4f604b5afe2bd7fe6d2954` and the P02 literal countermodel
from `9d6dd9575a61782c70137abff348356f805bc654`. See the generated
[proof inventory](inventory/PROOF_INVENTORY.md) for per-module coverage.
The six concatenated source archives are listed separately from the executable audits.

The historical HARD gate remains open. Its original two declaration checks are
preserved in [the probe](probe/ATK_HARD_PNP_NEXT.lean). After `lake build MCore`,
run `lake env lean probe/ATK_HARD_PNP_NEXT.lean` to reproduce the missing
identifiers. A successful library build does not execute or close that gate.

The P01 integrated SAT machine still requires a construction with halting and
acceptance correctness. P02 still requires a universal failure witness for the
same encoded language. The literal countermodel rules out one restricted
approach. The two diagnostics in `probe/*ExpectedFailure.lean` pin the types
of the remaining goals. They do not establish mathematical impossibility.

## Historical certification record

## C1

Status: RED_RECORDED / FIX_IN_PROGRESS

Latest audited RED:
- SHA: `b57468caa3fad70764206ea5d3d7513dad7ce28c`
- run: `35168094355`
- job: `105033608151`
- failed gate: semantic axiom closure
- cause: the CI required an empty axiom set, while the structural proofs implemented with `simp` report the standard Lean axiom `propext`.
- mathematical build: PASS
- historical chain preservation: PASS
- epistemic promotion: NONE

Earlier C1 RED class:
- `Option Bool` input split was implicit in `size_restrict` / `depth_restrict`; corrected by explicit case analysis.
- an intermediate `restrict_or` regression was corrected before certification and is now required to have a named adversarial regression.

Freeze policy: no C1 SHA is frozen until the complete hardened gate is GREEN.
Next transition: hardened C1 candidate -> CI -> GREEN then immutable freeze and individual certificate; otherwise record next RED fingerprint and repair forward only.
