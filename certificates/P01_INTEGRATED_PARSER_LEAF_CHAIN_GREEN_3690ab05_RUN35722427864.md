# P01 Integrated Parser/Leaf Chain — GREEN / FROZEN / CERTIFIED

Repository: ShantiDraconis/m-core-p-vs-np
Source SHA: 3690ab0593358d065930b36ec1e7a67852a88fa0
Frozen branch: frozen/p01-integrated-parser-leaf-chain-green-3690ab05
Certificate branch: cert/p01-integrated-parser-leaf-chain-3690ab05-run35722427864
Classification: GREEN_FROZEN_CERTIFIED_SUBGATE

Verified runs at source SHA:
- ATK P01 parser macro: 35722427864 — SUCCESS
- ATK P01 HARD scaffold: 35722427842 — SUCCESS
- ATK P02 normalization frontier: 35722427859 — SUCCESS
- ATK G3 source provenance: 35722427863 — SUCCESS
- ATK External scaffold: 35722427865 — SUCCESS
- certificate: 35722427901 — SUCCESS
- ATK P01 parser macro regression: 35722431275 — SUCCESS
- ATK P01 leaf-pop PR audit: 35722431242 — SUCCESS
- ATK P01 clean operational SAT: 35722431316 — SUCCESS
- ATK P02 literal countermodel PR audit: 35722431278 — SUCCESS
- certificate regression: 35722431762 — SUCCESS

Certified scope:
- certified parser macro chain;
- binary return/rewind chain;
- leaf-pop chain;
- leaf state14/15 return chain;
- certified leaf-source return/accept/reject chain;
- source hygiene, build, and axiom audit for the integrated reused source set.

Reuse provenance:
- leaf-source proof imported unchanged from frozen/p01-leaf-source-green-93f1321f;
- no frozen dependency was modified;
- the G2.1 literal fixed-point countermodel remains preserved and independently certified.

Explicitly NOT certified:
- a no-hypothesis inhabitant of SlotParserMachineSimulationCertificate;
- CanonicalRecursiveParserOperationalGap;
- integrated witness-guess + verifier NTM;
- CanonicalSATMachineClosure / SATInNPGap;
- P01 HARD final endpoint;
- SAT ∉ P or P ≠ NP.

Promotion:
P01 integrated parser/leaf reusable chain: GREEN → FROZEN → CERTIFIED
P01 full simulation: OPEN
P01 integrated SAT NTM: OPEN
P01 HARD: OPEN
