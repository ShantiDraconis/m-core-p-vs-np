# Certification state

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
