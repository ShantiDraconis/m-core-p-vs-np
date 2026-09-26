# FINAL_PROOF Evidence Map

## Evidence to collect while certification progresses

### Mathematical
- exact theorem statements proved by the kernel;
- minimal hypotheses and axiom printout;
- failed lemmas and countermodels;
- witness/counterexample objects;
- quantitative inequalities and their valid domains;
- same-input and quantifier-order preservation.

### Computational
- machine traces at boundary cases;
- halting/non-halting observations;
- state-count and transition-count data;
- input-size/runtime pairs;
- parser/verifier/stack/shuttle failure cases;
- regression datasets and outliers.

### Encoding/model
- encode/decode round trips;
- injectivity and collision searches;
- normalization/canonicalization behavior;
- model-match failures;
- transformations that do or do not preserve SAT semantics.

### Prime2 / Horizon Prime
- shell/core/gap measurements;
- first admissible states under each restriction;
- gap changes when 2 is included/excluded;
- counterexamples to proposed prime laws;
- candidate conservative maps back to standard arithmetic;
- experimental failures that survive that map.

### Certification/provenance
- repository and exact SHA;
- source file and theorem name;
- workflow/run id and conclusion;
- Lean/toolchain version;
- hygiene/sorry/axiom audit;
- dependency SHAs;
- freeze/certificate/root hashes;
- superseded or falsified certificates.

### External
- papers/results used as inspiration;
- exact theorem or dataset extracted;
- version/date/source;
- whether independently verified locally;
- transfer theorem required before formal use.

## Do not merge

Research evidence, finite experiments, metamodel labels, and external claims
must remain distinct from kernel proof evidence. They may be cross-linked but
never counted as FINAL_PROOF producers without explicit promotion theorems.
