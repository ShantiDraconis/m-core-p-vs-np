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

/-- Finite complete search space for all reachable reader states. -/
structure CompleteSearchSpace
    (Reachable : ReaderSearchState → Prop) where
  states : List ReaderSearchState
  complete : ∀ s, Reachable s → s ∈ states
  nodup : states.Nodup

/-- A strict natural-valued descent certificate for every declared loop edge. -/
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

/-- A detected repetition carries only the structural loop evidence.
It deliberately does NOT contain a closure witness. -/
structure LoopInvariant
    (LoopEdge : ReaderSearchState → ReaderSearchState → Prop)
    (M : LoopMeasure LoopEdge) where
  state : ReaderSearchState
  repeats : Prop
  repeats_proof : repeats

/-- A found blocker is evidence that search did not close. -/
structure MinimalBlock
    (IsBlocking : ReaderSearchState → Prop) where
  state : ReaderSearchState
  blocking : IsBlocking state

/-- Exhaustion is a proof over the entire candidate space, not search = none. -/
structure ExhaustionCertificate
    (IsBlocking : ReaderSearchState → Prop) where
  exhausted : ∀ s, ¬ IsBlocking s

/-- Total search result. None of the constructors smuggles in the theorem witness. -/
inductive SearchResult
    (IsBlocking : ReaderSearchState → Prop)
    (LoopEdge : ReaderSearchState → ReaderSearchState → Prop)
    (M : LoopMeasure LoopEdge) where
  | found :
      MinimalBlock IsBlocking →
      SearchResult IsBlocking LoopEdge M
  | exhausted :
      ExhaustionCertificate IsBlocking →
      SearchResult IsBlocking LoopEdge M
  | loopDetected :
      LoopInvariant LoopEdge M →
      SearchResult IsBlocking LoopEdge M

/-- The truncation law only proves total decidable classification.
It does not claim that a classified outcome proves the reader. -/
structure TruncationLaw
    (Reachable : ReaderSearchState → Prop)
    (IsBlocking : ReaderSearchState → Prop)
    (LoopEdge : ReaderSearchState → ReaderSearchState → Prop) where
  blockingDecidable : DecidablePred IsBlocking
  completeSpace : CompleteSearchSpace Reachable
  loopMeasure : LoopMeasure LoopEdge
  runSearch : SearchResult IsBlocking LoopEdge loopMeasure

/-- Material producer needed to resolve a genuine minimal blocker. -/
def FoundBlockClosureProducer
    {IsBlocking : ReaderSearchState → Prop} : Prop :=
  ∀ _m : MinimalBlock IsBlocking, ConcreteClosureWitness

/-- Material theorem required before proven exhaustion may close the reader. -/
def ExhaustionClosureProducer
    {IsBlocking : ReaderSearchState → Prop} : Prop :=
  ∀ _e : ExhaustionCertificate IsBlocking, ConcreteClosureWitness

/-- Material theorem required before loop detection may close the reader.
This is the exact fail-closed replacement for "loop means proved". -/
def LoopClosureProducer
    {LoopEdge : ReaderSearchState → ReaderSearchState → Prop}
    {M : LoopMeasure LoopEdge} : Prop :=
  ∀ _l : LoopInvariant LoopEdge M, ConcreteClosureWitness

/-- Exact producer package for turning a total search classification into closure.
All three branches must be materially discharged. -/
structure SearchClosureProducers
    {IsBlocking : ReaderSearchState → Prop}
    {LoopEdge : ReaderSearchState → ReaderSearchState → Prop}
    (M : LoopMeasure LoopEdge) where
  found : FoundBlockClosureProducer (IsBlocking := IsBlocking)
  exhausted : ExhaustionClosureProducer (IsBlocking := IsBlocking)
  loopDetected : LoopClosureProducer (LoopEdge := LoopEdge) (M := M)

def SearchResult.toClosure
    {IsBlocking : ReaderSearchState → Prop}
    {LoopEdge : ReaderSearchState → ReaderSearchState → Prop}
    {M : LoopMeasure LoopEdge}
    (P : SearchClosureProducers (IsBlocking := IsBlocking)
      (LoopEdge := LoopEdge) M) :
    SearchResult IsBlocking LoopEdge M → ConcreteClosureWitness
  | .found m => P.found m
  | .exhausted e => P.exhausted e
  | .loopDetected l => P.loopDetected l

theorem searchResult_closes_reader
    {IsBlocking : ReaderSearchState → Prop}
    {LoopEdge : ReaderSearchState → ReaderSearchState → Prop}
    {M : LoopMeasure LoopEdge}
    (P : SearchClosureProducers (IsBlocking := IsBlocking)
      (LoopEdge := LoopEdge) M)
    (r : SearchResult IsBlocking LoopEdge M) :
    PreservingUnaryReaderGap :=
  ⟨r.toClosure P⟩

theorem truncationLaw_closes_reader
    {Reachable : ReaderSearchState → Prop}
    {IsBlocking : ReaderSearchState → Prop}
    {LoopEdge : ReaderSearchState → ReaderSearchState → Prop}
    (L : TruncationLaw Reachable IsBlocking LoopEdge)
    (P : SearchClosureProducers (IsBlocking := IsBlocking)
      (LoopEdge := LoopEdge) L.loopMeasure) :
    PreservingUnaryReaderGap :=
  searchResult_closes_reader P L.runSearch

/-- Structural truncation producer: total search only. This does NOT close the gap. -/
def ExactTruncationProducer : Prop :=
  ∃ (Reachable IsBlocking : ReaderSearchState → Prop)
    (LoopEdge : ReaderSearchState → ReaderSearchState → Prop),
    Nonempty (TruncationLaw Reachable IsBlocking LoopEdge)

/-- Exact material producer still required after truncation is constructed. -/
def ExactTruncationClosureProducer : Prop :=
  ∃ (Reachable IsBlocking : ReaderSearchState → Prop)
    (LoopEdge : ReaderSearchState → ReaderSearchState → Prop)
    (L : TruncationLaw Reachable IsBlocking LoopEdge),
    Nonempty
      (SearchClosureProducers (IsBlocking := IsBlocking)
        (LoopEdge := LoopEdge) L.loopMeasure)

theorem exact_truncation_closure_producer_closes
    (h : ExactTruncationClosureProducer) :
    PreservingUnaryReaderGap := by
  rcases h with ⟨Reachable, IsBlocking, LoopEdge, L, P⟩
  rcases P with ⟨producers⟩
  exact truncationLaw_closes_reader L producers

#print axioms MCore.Real.P01PreservingUnaryTruncationLaw.loopEdge_wellFounded
#print axioms MCore.Real.P01PreservingUnaryTruncationLaw.searchResult_closes_reader
#print axioms MCore.Real.P01PreservingUnaryTruncationLaw.truncationLaw_closes_reader
#print axioms MCore.Real.P01PreservingUnaryTruncationLaw.exact_truncation_closure_producer_closes

end P01PreservingUnaryTruncationLaw
end Real
end MCore
