# P01 BOUNDED NEGATION CERTIFICATE — GREEN

Status: GREEN_FROZEN_SUBGATE
Source SHA: ea576ccfd161e3ec759d344c510eb5d48d3b2167
certificate run: 36789159392 — SUCCESS
fail-proof-all-gaps run: 36789159390 — SUCCESS

Certified declaration:
- MCore.Real.P01CheckedEvalRunBoundedCertificate.neg_bounded_certificate

Dependencies already kernelized:
- bounded input/constant leaves
- checked negation tag prefix
- bounded child execution
- physical negation-frame return
- checked outcome normalization
- CheckedLayoutBound propagation
- checkedCircuitBudget arithmetic

DOES_NOT_CERTIFY:
- bounded AND/OR recursion
- full bounded circuit recursion
- whole-verifier HaltsWithin
- whole-verifier AcceptsWithin iff SATBits
- Nonempty P01MachineConstruction
- P01ConstructionGap
- G21Pointwise
- P != NP

Next material law required by binary recursion:
- exact source-consumption conservation across a bounded child run.
