/-
RULE_IMMUTABLE_GLOBAL: NO_LOOP_ROUTE

This module is data-only. It introduces no axiom, theorem, producer, bridge,
certificate, or inhabitant.

The following route is prohibited in every external-certificate research lane:
  * DeficitBridge / ImmutableNoLoopRule / NoLoopRule
  * RestrictionProgressNorm -> RestrictionProgress bridge
  * cnfCircuitNorm -> cnfCircuit bridge
  * synthetic final_root_from_45bf2597
  * any construction whose only purpose is to turn the seven Lane-4 evidence
    checkpoints into a FinalExternalGap inhabitant by bypassing the missing
    mathematical implication.

The evidence commits may remain available for audit/history. They are not,
by themselves, producers of FinalExternalInputs.
-/

namespace MCore
namespace Real
namespace GlobalProhibition

def ruleId : String := "RULE_IMMUTABLE_GLOBAL_NO_LOOP_ROUTE"

def prohibitedSymbols : List String :=
  [ "MCore.Real.DeficitBridge"
  , "DeficitBridge"
  , "ImmutableNoLoopRule"
  , "NoLoopRule"
  , "noLoopBridgeImmutable"
  , "restrictionProgressNorm_to_raw"
  , "cnfCircuitNorm_to_circuit"
  , "final_root_from_45bf2597"
  , "finalExternalGapImm"
  , "externalCertificateImm"
  ]

def evidenceOnlyCheckpoints : List String :=
  [ "1b7ce6f8"
  , "24464291"
  , "f0a9fcd1"
  , "519e6868"
  , "003dd377"
  , "7732c120"
  , "45bf2597"
  ]

def policy : String :=
  "Evidence may be audited, but the prohibited Norm-to-Raw/no-loop route must not inhabit FinalExternalGap."

end GlobalProhibition
end Real
end MCore
