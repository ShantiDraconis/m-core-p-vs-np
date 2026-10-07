namespace MCore.NewRoutes
structure ProofComplexityObstruction where
  ProofSystem : Type
  lowerBound : ProofSystem → Prop
  universal : ∀ P, lowerBound P
structure AlgorithmsToLB where
  CircuitClass : Type
  satSpeedup : CircuitClass → Prop
  circuitLB : CircuitClass → Prop
structure DescriptiveSeparation where
  Structure : Type
  inPLogic inNPLogic separator : Structure → Prop
structure GCTMultiplicityObstruction where
  Representation : Type
  multiplicityObstruction : Representation → Prop
end MCore.NewRoutes
