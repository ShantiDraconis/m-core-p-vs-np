# P02 LANE4 PREKERNEL HARDENED V2

Branch: `atk/p02-lane4-reuse-t10-audit-20261003`

Source snapshot: `29e5fde392bc953eb69c8028be4fedf0a9be0d79`

Status: SOURCE_COMPLETE / PREKERNEL_HARDENED_V2 / KERNEL_PENDING / FAIL_CLOSED

Preventive fixes before kernel:
- standalone AUX gate now performs topological MCore build before direct Lean checks;
- preflight reuses successful L2 build in L3 instead of rebuilding MCore;
- stale lake-manifest is detected and verified after lake update;
- shell scripts are checked with bash -n at L0;
- bundle import DAG is checked before Lean;
- R5_PAIR, StructureBundle, AdvancedCertificateReuse and CompleteBundle are root-wired;
- polynomial bounds use explicit Nat monotonicity/ring composition instead of nlinarith/positivity;
- canonical interface adapters are explicit for CanonicalNotInPWitness;
- terminal equivalences use explicit Iff.trans rather than fragile rw chains;
- OpenProducerInventory has explicit fields and constructor;
- direct bundle checks follow StructureBundle -> AdvancedCertificateReuse -> CompleteBundle;
- no nlinarith/positivity/sorry/admit/opaque remains in the audited LANE4/tableau target path.

Not certified:
- kernel success;
- AUX_GREEN_CANDIDATE;
- T10 inhabitant;
- G21 inhabitant;
- UniversalFailure;
- SAT not in P;
- P != NP;
- FROZEN_HARD AUX/FULL.
