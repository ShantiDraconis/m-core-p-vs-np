# G3 NORMALIZED EXTERNAL CONTRACT — GREEN

Repository: ShantiDraconis/m-core-p-vs-np
Source SHA: f2cafea7a74f3ef8ad4140943515622545c9f1d8
Chain: G3 external model match
Gate: normalized OfficialModelSelection + G3ExternalContract instantiation
Classification: GREEN SUBGATE / EXTERNAL SOURCE-FIDELITY ENDPOINT REMAINS OPEN

Verified runs at source SHA:
- G3 source provenance / normalized contract: 35719428075 — SUCCESS
- certificate workflow: 35719428100 — SUCCESS

Objects:
- MCore.Real.CookNormalizedG3Contract.cookNormalizedSelection
- MCore.Real.CookNormalizedG3Contract.cookNormalizedExternalContract
- MCore.Real.CookNormalizedG3Contract.cook_normalized_g3_contract_closed
- MCore.Real.CookNormalizedG3Contract.cook_normalized_contract_p_match
- MCore.Real.CookNormalizedG3Contract.cook_normalized_contract_np_match

Predecessors reused:
- G3 Cook/CMI provenance — GREEN/FROZEN/CERTIFIED
- normalized DTM two-way bridge — GREEN/FROZEN/CERTIFIED
- normalized NTM two-way bridge — GREEN/FROZEN/CERTIFIED
- normalized four-way bridge — GREEN/FROZEN/CERTIFIED

Boundary:
This closes the typed normalized G3ExternalContract subgate for the selected
normalized Cook-style formal model and populated source provenance record.
It does not prove that the normalized formal model is a complete formalization
of every convention in the Cook/CMI prose source. Source-fidelity/model
identification remains open and FINAL_EXTERNAL is not claimed closed.

Promotion:
G3 normalized contract: GREEN → FROZEN → CERTIFIED
G3 source fidelity: OPEN_CONSTRUCTION
FINAL_EXTERNAL: BLOCKED
