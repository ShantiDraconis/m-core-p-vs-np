import MCore.Real.P01PreservingUnaryWitnessMachine

namespace MCore.Real.P01PreservingUnaryWitnessDiagnostic2

open CanonicalFinalProof
open CanonicalCircuitBits
open P01PreservingUnaryWitnessMachine

def diagCfg2 (k : Nat) :=
  preservingUnaryReadMachine.run k
    (indexSomeConfig [false, true] (false :: []) 1)

#eval (List.range 25).map (fun k =>
  (k,
   (diagCfg2 k).state,
   (diagCfg2 k).tape.left,
   (diagCfg2 k).tape.head,
   (diagCfg2 k).tape.right))

end MCore.Real.P01PreservingUnaryWitnessDiagnostic2
