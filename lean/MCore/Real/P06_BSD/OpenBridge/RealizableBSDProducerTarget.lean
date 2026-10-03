import MCore.Real.P06_BSD.SourceBinding

namespace MCore.Real.P06_BSD.OpenBridge.RealizableBSDProducerTarget

open P06_BSD.SourceBinding

def targetName : String :=
  "realizable elliptic-curve domain + universal rank equality + refined leading-coefficient identity on the same domain"

def rejectedAbstractTarget : String :=
  "∀ d : BSDArithmeticAnalyticData, BSDRankPart d"

def sourceRepo : String := canonicalBSDRepo
def sourceRef : String := canonicalFirewallRef
def sourcePath : String := "GATE_LEDGER.json"
def frontierState : String := "MODEL_BINDING_OPEN_MATH"

theorem source_ref_fixed :
    sourceRef = "c1e7b245726c4c65f5f9f878acefb86460746f4a" := rfl

#print axioms MCore.Real.P06_BSD.OpenBridge.RealizableBSDProducerTarget.source_ref_fixed

end MCore.Real.P06_BSD.OpenBridge.RealizableBSDProducerTarget
