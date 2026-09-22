# P02 G2.0 Candidate Normalization Certificate

Status: GREEN / FROZEN / CERTIFIED FORMAL_INFRA

Source SHA: d72e53bc7f667c75a432226a23adc59a255c5652
Frozen branch: frozen/p02-g2-0-normalization-green-d72e53bc
ATK clean run: 35707286302 — SUCCESS
Repository certificate run: 35707286255 — SUCCESS

Certified scope:
- extracts explicit polynomial coefficient/exponent bounds from PolyDTMCandidate.time_poly;
- defines a canonical normalized candidate with the same underlying deterministic machine data;
- proves HaltsWithin monotonicity reuse through existing MachineRunLemmas;
- proves CorrectAt preservation under a dominating explicit monomial bound;
- packages a noncomputable witness using Classical.choice only;
- passes source hygiene, build, and the dedicated P02 candidate-normalization axiom audit.

Explicitly NOT certified:
- effective enumerability of PolyDTMCandidate;
- G2.1 diagonal fixed point;
- any SAT lower bound;
- G2.2 contradiction;
- G2.3 FailureGenerator;
- SAT ∉ P;
- P ≠ NP.

G2.1 remains OPEN_MATH and is the terminal producer.
