# P01 Integration Prefix — GREEN Certificate

source_sha: ada18eeddb72490e44a9c6033d63690a416a7f0b
frozen_ref: frozen/p01-integration-prefix-green-ada18eed
certificate_ref: cert/p01-integration-prefix-ada18eed-run35699864579
workflow: ATK P01 HARD scaffold
run_id: 35699864579
conclusion: SUCCESS

classification: SOURCE_GREEN_PREFIX
promotion_scope: parser TM-to-NTM embedding + finite-control witness guesser only

verified:
- P01FinalCertificate scaffold build: PASS
- fail-closed hygiene: PASS
- generic TM -> singleton-branch NTM step simulation: PASS
- Fin 25 parser NTM successor/run/halting/acceptance bridge: PASS
- finite-control witness guesser NTM: PASS
- witness guesser fixed alphabet Option Bool: PASS
- witness guesser polynomial linear bound: PASS
- audited source sorryAx: ABSENT in promoted prefix

boundary:
- P01 HARD remains OPEN.
- ParserSimulationGap is not inhabited by this certificate.
- The integrated parse -> witness -> verifier -> accept/reject NTM is not yet constructed.
- CanonicalSATMachineClosure is not established.
- P02 remains blocked behind P01 HARD.
- This certificate does not establish P != NP.
