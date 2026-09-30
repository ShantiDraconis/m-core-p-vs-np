# P01 BOUNDED INPUT CERTIFICATE — GREEN

Status: GREEN_FROZEN_SUBGATE
Scientific status: P01 OPEN_IMPLEMENTATION
P-vs-NP status: OPEN_MATH

Frozen source:
- SHA: 97792f5ee0db5cdcfca1acaceb7444d7fded695f
- Branch: frozen/p01-bounded-input-certificate-green-97792f5e
- certificate run: 36788631872 — SUCCESS
- fail-proof-all-gaps run: 36788631672 — SUCCESS

Kernelized content:
- preserving unary-index witness read for arbitrary valid index;
- full-layout input-node read preserving witness, consumed gap, unread source tail,
  frame stack and padding;
- checked 000 input route under the common checked-loop envelope;
- explicit CheckedLayoutBound propagation through the input route;
- bounded input leaf certificate;
- bounded constant leaf certificate;
- no source-level sorry/admit/closure axiom introduced by this subgate.

Primary declarations:
- MCore.Real.P01WitnessIndexedReadPreserving.preservingRead_forall_value
- MCore.Real.P01EvalInputNodePhysicalRefinement.inputNode000_full_layout_read
- MCore.Real.P01EvalInputNodePhysicalRefinement.inputNode000_full_layout_value
- MCore.Real.P01CheckedEvalRunBoundedInput.inputTag_checked_reaches_within_loopEnvelope
- MCore.Real.P01CheckedEvalRunBoundedCertificate.input_bounded_certificate
- MCore.Real.P01CheckedEvalRunBoundedCertificate.const_bounded_certificate

This closes the former local input-tag material obstruction.

DOES_NOT_CERTIFY:
- the recursive bounded certificate for NOT/AND/OR;
- the complete checked circuit bounded certificate;
- a whole-verifier HaltsWithin theorem;
- whole-verifier AcceptsWithin iff SATBits;
- one integrated parser + witness + verifier NTM;
- Nonempty P01MachineConstruction;
- P01ConstructionGap;
- G21Pointwise;
- P != NP.

Next exact frontier:
1. extend BoundedCheckedCircuitRunCertificate recursively through NOT/AND/OR;
2. derive the complete bounded circuit certificate;
3. convert bounded checked circuit execution into whole-verifier HaltsWithin and acceptance;
4. compose parser + witness guesser + checked verifier into one Fin-indexed NTM;
5. instantiate every field of P01MachineConstruction.
