import MCore.Real.P01PreservingUnaryWitnessMachine

namespace MCore.Real.P01PreservingUnaryWitnessDiagnostic

open CanonicalFinalProof
open CanonicalCircuitBits
open P01PreservingUnaryWitnessMachine

def diagCfg (k : Nat) :=
  preservingUnaryReadMachine.run k
    (indexSomeConfig [false] (false :: []) 1)

#eval (List.range 17).map (fun k =>
  (k,
   (diagCfg k).state,
   (diagCfg k).tape.left,
   (diagCfg k).tape.head,
   (diagCfg k).tape.right))

end MCore.Real.P01PreservingUnaryWitnessDiagnostic
