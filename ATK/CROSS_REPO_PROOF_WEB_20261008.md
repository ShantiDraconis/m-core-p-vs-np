# ATK — Cross-repository proof reuse graph (2026-10-08)

Repository: ShantiDraconis/m-core-p-vs-np
Branch: atk/global-material-audit-20261008
State: SOURCE / NOT KERNEL VERIFIED / NO TERMINAL PROMOTION

## Verified source paths and logical edges
- ShantiDraconis/M-Core :: `final-proof/pnp_prior_formalization_reuse.json` — Historical PNP reuse map: conditional, not an inhabitant
- ShantiDraconis/M-Core :: `evidence/endpoint_states.json` — References and declarations; REFERENCED_ONLY is not proved
- ShantiDraconis/axiomatic-millenium :: `AxiomaticMillenium.lean` — Seven-lane aggregation import root
- ShantiDraconis/axiomatic-millenium :: `AxiomaticMillenium/SevenLaneClosureKernel.lean` — 7 structural lanes, 9 material atoms, green=false
- ShantiDraconis/m-core-p-vs-np :: `lean/MCore/Real/P01FinalCertificate.lean` — Concrete P01MachineConstruction structure; construction_closes_p01 requires hypothesis

### PNP dependency edge
`P01MachineConstruction` -> `Nonempty P01MachineConstruction` (`P01ConstructionGap`) -> `CanonicalSATMachineClosure`.
`FinalExternalTwoGap := P01ConstructionGap ∧ G21Pointwise` (M-Core imported snapshot).
The theorem `construction_closes_p01` has an explicit `h : P01ConstructionGap` hypothesis. It is NOT a proof of that hypothesis.

### Structural seven-lane edge
`SevenLaneClosedMath` + `SevenLaneClosedBridge` + `SevenLaneExactFrontier` -> `SevenLaneClosureKernel` -> `GlobalExternalClosedMathReport` -> global M-Core audit.
The catalog reports seven lanes and nine material atoms; this is not terminal mathematical closure.

### Transfer rules
1. Match fully elaborated theorem types, universe parameters, hypotheses, and imports.
2. Pin source repository, commit SHA, Lean/toolchain version and blob SHA before copying.
3. Import existing modules where compatible; otherwise copy only into a versioned namespace with source attribution.
4. Execute `lake build`, `#check`, and `#print axioms` in a reproducible environment.
5. Never promote OPEN_MATH, terminalCertified, kernelVerified or FINAL_EXTERNAL_ISSUED from an unverified mapping.
6. Preserve main and frozen branches; forward-only integration.

### Next checks
- [ ] Inspect exact G21Pointwise declaration and compare with historical fixed-witness bridges.
- [ ] Locate an actual term inhabiting P01MachineConstruction (not only a structure declaration).
- [ ] Reconcile PNP two-gap view with seven-lane nine-atom accounting.
- [ ] Resolve project dependency and kernel build for this repository.
