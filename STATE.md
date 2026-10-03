# Certification state

## C1

Status: FIX_APPLIED / BUILD_PENDING

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
Applied fix: `certificate.yml` now audits the exact C1 axiom set, allowing only Lean's standard `propext` (or no axioms if future proof terms simplify further) and rejecting any unexpected dependency or `sorryAx`.
Fix commit: `9a39ed5c89e97768bf6124d2df36fa6e93c0631f`.
Next transition: run the hardened C1 gate -> if PASS, GREEN then immutable freeze and individual certificate; otherwise record the next RED fingerprint and repair forward only.
