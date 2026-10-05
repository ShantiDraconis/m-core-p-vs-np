import MCore.Real.P01PreservingUnaryReaderResiduals

namespace MCore.Real.P01PreservingUnaryTruncationLawV2

open CanonicalFinalProof
open P01WitnessIndexedRead
open P01PreservingUnaryWitnessMachine
open P01PreservingUnaryReaderCertificate

abbrev ConcreteClosureWitness := PreservingUnaryReaderCertificate

structure ReaderInput where
  witness : BitString
  index : Nat
  valid : index < witness.length

def ReaderInput.size (x : ReaderInput) : Nat :=
  x.witness.length + (encodeNat x.index).length

def ReaderInput.initialConfig (x : ReaderInput) :
    Configuration PreservingReadState (Option Bool) :=
  { state := preservingUnaryReadMachine.initial
    tape := witnessReadTape x.witness x.index }

def budget (x : ReaderInput) : Nat :=
  preservingUnaryTimeBound x.size

structure ExhaustionCertificate where
  halts :
    ∀ x : ReaderInput,
      preservingUnaryReadMachine.HaltsWithin (budget x) x.initialConfig

structure CorrectnessCertificate where
  correct :
    ∀ x : ReaderInput,
      preservingReadAccepting
        (preservingUnaryReadMachine.run (budget x) x.initialConfig).state =
      x.witness.getD x.index false

structure PreservationCertificate where
  preserves :
    ∀ x : ReaderInput,
      ∃ left right : List (Option Bool),
        (preservingUnaryReadMachine.run (budget x) x.initialConfig).tape =
          { left := left ++ x.witness.map some
            head := none
            right := right }

structure ConcreteSearchClosure where
  exhaustion : ExhaustionCertificate
  correctness : CorrectnessCertificate
  preservation : PreservationCertificate

def ConcreteSearchClosure.toReaderCertificate
    (C : ConcreteSearchClosure) : ConcreteClosureWitness :=
  residuals_close_preserving_unary_reader
    (by
      intro witness i hi
      exact C.exhaustion.halts ⟨witness, i, hi⟩)
    (by
      intro witness i hi
      exact C.correctness.correct ⟨witness, i, hi⟩)
    (by
      intro witness i hi
      exact C.preservation.preserves ⟨witness, i, hi⟩)

structure LoopInvariant where
  input : ReaderInput
  first second : Nat
  first_lt_second : first < second
  second_le_budget : second ≤ budget input
  repeated_config :
    preservingUnaryReadMachine.run first input.initialConfig =
    preservingUnaryReadMachine.run second input.initialConfig

inductive SearchResult
  | found : ConcreteSearchClosure → SearchResult
  | exhausted : ExhaustionCertificate → SearchResult
  | loopDetected : LoopInvariant → SearchResult
  | open : SearchResult

structure TruncationLaw where
  exhaustionProducesClosure :
    ExhaustionCertificate → ConcreteSearchClosure
  loopProducesClosure :
    LoopInvariant → ConcreteSearchClosure

def SearchResult.close?
    (L : TruncationLaw) :
    SearchResult → Option ConcreteClosureWitness
  | .found C => some C.toReaderCertificate
  | .exhausted E => some (L.exhaustionProducesClosure E).toReaderCertificate
  | .loopDetected I => some (L.loopProducesClosure I).toReaderCertificate
  | .open => none

theorem open_does_not_close (L : TruncationLaw) :
    SearchResult.open.close? L = none := by rfl

theorem exhaustion_closes
    (L : TruncationLaw) (E : ExhaustionCertificate) :
    PreservingUnaryReaderGap :=
  ⟨(L.exhaustionProducesClosure E).toReaderCertificate⟩

theorem loop_closes
    (L : TruncationLaw) (I : LoopInvariant) :
    PreservingUnaryReaderGap :=
  ⟨(L.loopProducesClosure I).toReaderCertificate⟩

#print axioms MCore.Real.P01PreservingUnaryTruncationLawV2.ConcreteSearchClosure.toReaderCertificate
#print axioms MCore.Real.P01PreservingUnaryTruncationLawV2.open_does_not_close
#print axioms MCore.Real.P01PreservingUnaryTruncationLawV2.exhaustion_closes
#print axioms MCore.Real.P01PreservingUnaryTruncationLawV2.loop_closes

end MCore.Real.P01PreservingUnaryTruncationLawV2
