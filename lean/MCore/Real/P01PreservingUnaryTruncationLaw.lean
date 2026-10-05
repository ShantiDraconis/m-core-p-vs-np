import MCore.Real.P01PreservingUnaryReaderCertificate
import MCore.Real.P01PreservingMarkerIteration

namespace MCore
namespace Real
namespace P01PreservingUnaryTruncationLaw

open CanonicalFinalProof
open P01WitnessIndexedRead
open P01PreservingUnaryWitnessMachine
open P01PreservingUnaryReaderCertificate
open P01PreservingMarkerIteration

abbrev ConcreteClosureWitness := PreservingUnaryReaderCertificate

structure ReaderSearchState where
  witness : BitString
  index : Nat
  index_valid : index < witness.length
  config : Configuration PreservingReadState (Option Bool)

def initialSearchState
    (witness : BitString) (index : Nat)
    (h : index < witness.length) : ReaderSearchState :=
  { witness := witness
    index := index
    index_valid := h
    config :=
      { state := preservingUnaryReadMachine.initial
        tape := witnessReadTape witness index } }

abbrev IsBlocking := ReaderSearchState → Prop

structure CompleteSearchSpace
    (Reachable : ReaderSearchState → Prop) where
  states : List ReaderSearchState
  complete : ∀ s, Reachable s → s ∈ states
  nodup : states.Nodup

structure LoopMeasure
    (LoopEdge : ReaderSearchState → ReaderSearchState → Prop) where
  measure : ReaderSearchState → Nat
  decreases :
    ∀ {a b}, LoopEdge a b → measure b < measure a

theorem loopEdge_wellFounded
    {LoopEdge : ReaderSearchState → ReaderSearchState → Prop}
    (M : LoopMeasure LoopEdge) :
    WellFounded (fun b a => LoopEdge a b) := by
  exact WellFounded.onFun M.measure Nat.lt_wfRel.wf

structure LoopInvariant
    (LoopEdge : ReaderSearchState → ReaderSearchState → Prop)
    (M : LoopMeasure LoopEdge) where
  state : ReaderSearchState
  repeats : Prop
  repeats_proof : repeats
  closure : ConcreteClosureWitness

inductive SearchResult
    (IsBlocking : ReaderSearchState → Prop)
    (LoopEdge : ReaderSearchState → ReaderSearchState → Prop)
    (M : LoopMeasure LoopEdge) where
  | found :
      (s : ReaderSearchState) →
      IsBlocking s →
      ConcreteClosureWitness →
      SearchResult IsBlocking LoopEdge M
  | exhausted :
      (∀ s, ¬ IsBlocking s) →
      ConcreteClosureWitness →
      SearchResult IsBlocking LoopEdge M
  | loopDetected :
      LoopInvariant LoopEdge M →
      SearchResult IsBlocking LoopEdge M

def SearchResult.toClosure
    {IsBlocking : ReaderSearchState → Prop}
    {LoopEdge : ReaderSearchState → ReaderSearchState → Prop}
    {M : LoopMeasure LoopEdge} :
    SearchResult IsBlocking LoopEdge M → ConcreteClosureWitness
  | .found _ _ h => h
  | .exhausted _ h => h
  | .loopDetected h => h.closure

theorem searchResult_closes_reader
    {IsBlocking : ReaderSearchState → Prop}
    {LoopEdge : ReaderSearchState → ReaderSearchState → Prop}
    {M : LoopMeasure LoopEdge}
    (r : SearchResult IsBlocking LoopEdge M) :
    PreservingUnaryReaderGap :=
  ⟨r.toClosure⟩

structure TruncationLaw
    (Reachable : ReaderSearchState → Prop)
    (IsBlocking : ReaderSearchState → Prop)
    (LoopEdge : ReaderSearchState → ReaderSearchState → Prop) where
  blockingDecidable : DecidablePred IsBlocking
  completeSpace : CompleteSearchSpace Reachable
  loopMeasure : LoopMeasure LoopEdge
  runSearch : SearchResult IsBlocking LoopEdge loopMeasure

theorem truncationLaw_closes_reader
    {Reachable : ReaderSearchState → Prop}
    {IsBlocking : ReaderSearchState → Prop}
    {LoopEdge : ReaderSearchState → ReaderSearchState → Prop}
    (L : TruncationLaw Reachable IsBlocking LoopEdge) :
    PreservingUnaryReaderGap :=
  searchResult_closes_reader L.runSearch

def ExactTruncationProducer : Prop :=
  ∃ (Reachable IsBlocking : ReaderSearchState → Prop)
    (LoopEdge : ReaderSearchState → ReaderSearchState → Prop),
    Nonempty (TruncationLaw Reachable IsBlocking LoopEdge)

theorem exact_truncation_producer_closes
    (h : ExactTruncationProducer) :
    PreservingUnaryReaderGap := by
  rcases h with ⟨Reachable, IsBlocking, LoopEdge, L⟩
  rcases L with ⟨law⟩
  exact truncationLaw_closes_reader law

#print axioms MCore.Real.P01PreservingUnaryTruncationLaw.loopEdge_wellFounded
#print axioms MCore.Real.P01PreservingUnaryTruncationLaw.searchResult_closes_reader
#print axioms MCore.Real.P01PreservingUnaryTruncationLaw.truncationLaw_closes_reader
#print axioms MCore.Real.P01PreservingUnaryTruncationLaw.exact_truncation_producer_closes

end P01PreservingUnaryTruncationLaw
end Real
end MCore
