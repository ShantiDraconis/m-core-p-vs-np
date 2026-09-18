# PUBLIC_AUDIT_MIGRATION_MANIFEST

STATUS: SOURCE_CATALOG_ONLY / NO_MATHEMATICAL_PROMOTION

## Source lock

- REPOSITORY: `ShantiDraconis/m-core-p-vs-np`
- BASE: `6f310228a57984b33503a458f952207561c34c60`
- HEAD_SOURCE_LOCK: `6f310228a57984b33503a458f952207561c34c60`
- SOURCE_CERTIFICATE: C12
- SOURCE_RUN: `35300196456` / job `105461036544` = GREEN
- MAIN_REPRO_RUN_AT_LOCK: `35300295285` / job `105461320557` = GREEN
- LOCK_POLICY: audit commits may add files under `audit/` and one dense CI reproduction gate, but MUST NOT modify the locked mathematical source under `lean/MCore/`.

## Official endpoint source

Stephen Cook, *The P versus NP Problem*, Clay Mathematics Institute official problem description:
- §1, pp. 1–2: formal definitions of P and NP and the problem statement “Does P = NP?”
- §1, p. 2: P ⊆ NP.
- §2, p. 4: Satisfiability and 3-SAT are identified as NP-complete.

Canonical source:
https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf

## Audit interpretation

The repository currently formalizes an abstract `ClassicalComplexityInterface`, not the official Turing-machine definitions themselves. Therefore no theorem in this audit may identify the abstract predicates with the official P and NP classes without an explicit fixed-model matching hypothesis.

The existing K10 proposition
`∃ (Language α Value : Type), Nonempty (SeparationWitnessData Language α Value)`
quantifies over arbitrary types. It is NOT, by itself, the classical P-vs-NP endpoint and MUST NOT be promoted as one.

C11/C12 quantitative data are source evidence only. Finite family regressions and `PaysOff` measurements do not imply an asymptotic algorithm, a circuit lower bound, or a classical separation without an explicit transfer theorem.

## Files produced by the backward-dense pass

- `audit/FinalEndpoint.lean`
- `audit/EndpointCompression.lean`
- `audit/PNP_FRONTIERS_SEMANTIC_AUDIT.json`
- `audit/repro_PNP.lean`
- `audit/PNP_RESIDUE.md`

No `TARGET_CERTIFICATE` is emitted unless the real frontiers are discharged without new `sorry` or axioms.
