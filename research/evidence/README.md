# FINAL_PROOF Research Evidence Registry

Status: RESEARCH_EVIDENCE_ONLY / ZERO_PROOF_CREDIT_BY_DEFAULT

This registry stores observations discovered while FINAL_PROOF is being built,
tested, frozen, and certified. Evidence is classified here for later analysis.
Nothing in this directory is a proof producer merely because it is recorded.

## Evidence lanes

1. PRIME2
   Experimental alternative-prime structures, conservative-transfer candidates,
   failure witnesses, model comparisons, and boundary counterexamples.

2. HORIZON_PRIME
   Prime-horizon observations: threshold/boundary phenomena, first/last valid
   states under a chosen constraint, gap growth, shell transitions, parity
   effects, asymptotic candidate laws, and counterexamples.

3. G21_SEMANTIC
   Same-input witnesses, semantic mismatch candidates, self-embedding evidence,
   candidate-specific failures, and failed routes.

4. P01_PHYSICAL
   Physical-machine traces, state-count evidence, local refinement lemmas,
   halting bounds, stack/shuttle invariants, and implementation counterexamples.

5. COMPLEXITY_BOUNDS
   Polynomial bounds, domination inequalities, encoding-size estimates,
   simulation overhead, lower/upper-bound candidates, and failed asymptotics.

6. ENCODING_INVARIANTS
   Injectivity, decode/encode equalities, same-input preservation,
   canonicalization, normalization, and model-match evidence.

7. NEGATIVE_RESULTS
   Falsified routes, impossible fixed-point claims, countermodels, failed
   conjectures, and minimal obstruction statements.

8. GEOMETRIC_P012
   Compression/reflection/expansion structures, kernel shells, topology or
   geometry embeddings, and invariants under shape changes. Research only.

9. CERTIFICATE_PROVENANCE
   Commit SHA, workflow/run id, source path, dependency SHA, kernel version,
   hygiene result, freeze/certificate identifier, and hashes.

10. EXTERNAL_SOURCE
    Papers, datasets, external calculations, or independently produced
    certificates. Must include provenance and cannot promote automatically.

## Promotion rule

Evidence can enter FINAL_PROOF only through an explicit, kernel-checked theorem
whose conclusion is an existing real producer/obligation. Examples:

- Prime2 evidence -> ConservativePrime2Interpretation
- Prime2 failure evidence -> MappedPrime2UniversalFailure
- research route -> G21Pointwise
- P01 implementation evidence -> P01ConstructionGap

Absent such a theorem, classification remains RESEARCH_ONLY.

## Required fields per evidence item

- evidence_id
- lane
- status
- claim
- exact_scope
- source_repository
- source_sha
- source_path
- workflow_run
- created_at
- evidence_kind
- assumptions
- observed_result
- counterexample_if_any
- transfer_target
- transfer_status
- proof_credit
- notes


## M-Core first indeterminate constant (conditional lane)

The current conditional M-Core lane designates a first indeterminate constant
`I₀`, intended to correspond to the project's `0/0` state and to the
historical fingerprint `phi_11dd4ff2`. In the present repository HEAD there is
no concrete Lean declaration named `phi_11dd4ff2`, so this identification is
carried as explicit conditional data rather than asserted as an existing code.

The semantic bottom state is represented by `c.eval 0 = ⊥ : Part Nat`. The
bounded evaluator `c.evaln fuel 0 : Option Nat` is kept separate: if semantic
evaluation is bottom, `evaln_sound` prevents any finite fuel from producing a
value. Therefore the M-Core L'Hospital rule is not encoded as
`⊥ -> eventually some v`; it is an explicit hypothesis package whose
substantive field is the bounded diagonal witness producer required by P02.

Current fail-closed status:

- `MCORE_LHOSPITAL: ASSUMED / UNPROVED`
- `FINAL_EXTERNAL: CONDITIONAL [MCoreLHospitalBound]`
- `FINAL_PROOF: NOT_UNCONDITIONAL`

The intended M-Core interpretation is that the remaining indeterminate forms
are reduced to the first indeterminate constant `I₀`. That reduction is not
yet a theorem in this HEAD and must be formalized separately before it can be
used as an unconditional dependency.
