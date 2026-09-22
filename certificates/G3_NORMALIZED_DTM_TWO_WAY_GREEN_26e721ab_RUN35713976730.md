# G3 NORMALIZED EXTERNAL DTM TWO-WAY BRIDGE — GREEN

Repository: ShantiDraconis/m-core-p-vs-np
Source SHA: 26e721ab25425d62312945200baa9c127910d320
Chain: G3 external model match
Gate: independent normalized machine model + deterministic two-way bridge
Classification: GREEN SUBGATE / G3 ENDPOINT REMAINS OPEN_CONSTRUCTION

Verified runs:
- G3 source provenance/model bridge: 35713976730 — SUCCESS
- External scaffold regression: 35713976744 — SUCCESS
- P01 HARD regression: 35713976909 — SUCCESS
- P02 regression: 35713976797 — SUCCESS
- P01 parser macro regression: 35713976753 — SUCCESS
- certificate: 35713976806 — SUCCESS

Formal payload includes:
- CookDTM / CookNTM independent normalized machine syntax
- CookDTM.run / CookNTM.runBranches external semantics
- CookPolyDTMCandidate / CookPolyNTMCandidate
- CookPRealization / CookNPRealization
- cookNormalizedModel
- cookNormalizedSelection
- internalDTM_to_cook
- cookDTM_to_internal
- deterministic run and CorrectAt equivalence lemmas

Boundary:
Only the deterministic two-way bridge is closed.
The nondeterministic two-way bridge remains OPEN.
Source-fidelity beyond the pinned Cook/CMI provenance remains an audit obligation.
G3ModelBridge is not yet inhabited; FINAL_EXTERNAL remains blocked.

Promotion:
G3 normalized external model + DTM two-way bridge: GREEN → FROZEN → CERTIFIED
G3 NTM two-way bridge: OPEN
G3 endpoint: OPEN_CONSTRUCTION
