namespace MCore
namespace Real
namespace GlobalProhibition

def ruleId : String := "RULE_IMMUTABLE_GLOBAL_NO_LOOP_ROUTE"

def blockedNames : List String :=
  [ "DeficitBridge"
  , "ImmutableNoLoopRule"
  , "NoLoopRule"
  , "restrictionProgressNorm_to_raw"
  , "cnfCircuitNorm_to_circuit"
  , "final_root_from_45bf2597"
  ]

def evidenceOnly : List String :=
  [ "1b7ce6f8", "24464291", "f0a9fcd1", "519e6868"
  , "003dd377", "7732c120", "45bf2597" ]

end GlobalProhibition
end Real
end MCore
