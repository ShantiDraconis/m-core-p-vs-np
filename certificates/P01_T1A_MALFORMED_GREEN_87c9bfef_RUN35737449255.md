# P01 T1.A Malformed-Head Prefix — GREEN / FROZEN / CERTIFIED

Repository: ShantiDraconis/m-core-p-vs-np
Source SHA: 87c9bfef31e5772a3a675a6285e5efa1c8b9ce1a
Frozen branch: frozen/p01-t1a-malformed-green-87c9bfef
Certificate branch: cert/p01-t1a-malformed-87c9bfef-run35737449255
Verified run: 35737449255 — FINAL_PROOF P01 T1A kernel — SUCCESS

Certified scope:
- direct build and axiom audit of P01GlobalParserSimulation
- malformed-head rejection path
- unary INPUT missing-terminator rejection
- previously certified blank-bisimulation and leaf terminal/source-return prefixes

Explicitly NOT certified:
- no-hypothesis SlotParserMachineSimulationCertificate
- P01ConstructionGap
- integrated parser/witness/verifier NTM
- SATInNPGap

State:
T1.A = IN_PROCESS
