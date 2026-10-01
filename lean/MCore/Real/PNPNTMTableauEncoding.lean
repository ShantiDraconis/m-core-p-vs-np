
import MCore.Real.PNPNTMPathFrontier

namespace MCore
namespace Real
namespace PNPNTMTableauEncoding

open CircuitK1
open CanonicalFinalProof
open CanonicalCircuitBits
open PNPNTMPathFrontier

structure NTMLiteral where
  var : Nat
  positive : Bool
  deriving DecidableEq, Repr

abbrev NTMClause := List NTMLiteral

abbrev NTMCNF := List NTMClause

def ntmPos (v : Nat) : NTMLiteral := { var := v, positive := true }

def ntmNeg (v : Nat) : NTMLiteral := { var := v, positive := false }

def ntmLiteralCircuit (l : NTMLiteral) : Circuit :=
  if l.positive then .input l.var else .not (.input l.var)

def ntmClauseCircuit : NTMClause -> Circuit
  | [] => .const false
  | l :: ls => .or (ntmLiteralCircuit l) (ntmClauseCircuit ls)

def ntmCNFCircuit : NTMCNF -> Circuit
  | [] => .const true
  | c :: cs => .and (ntmClauseCircuit c) (ntmCNFCircuit cs)

def evalNTMLiteral (sigma : Assignment) (l : NTMLiteral) : Bool :=
  if l.positive then sigma l.var else !(sigma l.var)

def evalNTMClause (sigma : Assignment) : NTMClause -> Bool
  | [] => false
  | l :: ls => Bool.or (evalNTMLiteral sigma l) (evalNTMClause sigma ls)

def evalNTMCNF (sigma : Assignment) : NTMCNF -> Bool
  | [] => true
  | c :: cs => Bool.and (evalNTMClause sigma c) (evalNTMCNF sigma cs)

def ntmAlphabet : List (Option Bool) :=
  [none, some false, some true]

def ntmSymbolCode : Option Bool -> Nat
  | none => 0
  | some false => 1
  | some true => 2

def ntmRadius (x : BitString) (t : Nat) : Nat :=
  x.length + t + 1

def ntmStateCount (M : PolyNTMCandidate) : Nat :=
  M.stateCount + 1

def ntmStateSlots (M : PolyNTMCandidate) (t : Nat) : Nat :=
  (t + 1) * ntmStateCount M

def ntmHeadBase (M : PolyNTMCandidate) (t : Nat) : Nat :=
  ntmStateSlots M t

def ntmLeftBase (M : PolyNTMCandidate) (x : BitString) (t : Nat) : Nat :=
  ntmHeadBase M t + (t + 1) * 3

def ntmRightBase (M : PolyNTMCandidate) (x : BitString) (t : Nat) : Nat :=
  ntmLeftBase M x t + (t + 1) * ntmRadius x t * 3

def ntmChoiceBase (M : PolyNTMCandidate) (x : BitString) (t : Nat) : Nat :=
  ntmRightBase M x t + (t + 1) * ntmRadius x t * 3

def ntmStateVar
    (M : PolyNTMCandidate) (t s : Nat)
    (q : Fin (M.stateCount + 1)) : Nat :=
  s * ntmStateCount M + q.val

def ntmHeadVar
    (M : PolyNTMCandidate) (t s : Nat)
    (a : Option Bool) : Nat :=
  ntmHeadBase M t + s * 3 + ntmSymbolCode a

def ntmLeftVar
    (M : PolyNTMCandidate) (x : BitString) (t s i : Nat)
    (a : Option Bool) : Nat :=
  ntmLeftBase M x t +
    (s * ntmRadius x t + i) * 3 + ntmSymbolCode a

def ntmRightVar
    (M : PolyNTMCandidate) (x : BitString) (t s i : Nat)
    (a : Option Bool) : Nat :=
  ntmRightBase M x t +
    (s * ntmRadius x t + i) * 3 + ntmSymbolCode a

def ntmBranchBound (M : PolyNTMCandidate) : Nat :=
  (((List.ofFn fun q : Fin (M.stateCount + 1) => q).flatMap fun q =>
      ntmAlphabet.map fun a => (M.machine.transition q a).length)).foldl Nat.max 0

def ntmChoiceVar
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool) (j : Nat) : Nat :=
  ntmChoiceBase M x t +
    ((((s * ntmStateCount M + q.val) * 3 + ntmSymbolCode a) *
      (ntmBranchBound M + 1)) + j)

def ntmLitFor (v : Nat) (value : Bool) : NTMLiteral :=
  if value then ntmPos v else ntmNeg v

def ntmSetStateClauses
    (guard : NTMClause)
    (M : PolyNTMCandidate)
    (t s : Nat)
    (target : Fin (M.stateCount + 1)) : NTMCNF :=
  List.ofFn fun q : Fin (M.stateCount + 1) =>
    guard ++ [ntmLitFor (ntmStateVar M t s q) (decide (q = target))]

def ntmSetSymbolClauses
    (guard : NTMClause)
    (varAt : Option Bool -> Nat)
    (target : Option Bool) : NTMCNF :=
  ntmAlphabet.map fun a =>
    guard ++ [ntmLitFor (varAt a) (decide (a = target))]

def ntmCopySymbolClauses
    (guard : NTMClause)
    (oldVar newVar : Option Bool -> Nat) : NTMCNF :=
  ntmAlphabet.flatMap fun a =>
    [ guard ++ [ntmNeg (oldVar a), ntmPos (newVar a)]
    , guard ++ [ntmPos (oldVar a), ntmNeg (newVar a)] ]

def ntmCopyLeftAll
    (guard : NTMClause)
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat) : NTMCNF :=
  (List.range (ntmRadius x t)).flatMap fun i =>
    ntmCopySymbolClauses guard
      (ntmLeftVar M x t s i)
      (ntmLeftVar M x t (s + 1) i)

def ntmCopyRightAll
    (guard : NTMClause)
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat) : NTMCNF :=
  (List.range (ntmRadius x t)).flatMap fun i =>
    ntmCopySymbolClauses guard
      (ntmRightVar M x t s i)
      (ntmRightVar M x t (s + 1) i)

def ntmSetLeftCell
    (guard : NTMClause)
    (M : PolyNTMCandidate) (x : BitString) (t s i : Nat)
    (target : Option Bool) : NTMCNF :=
  ntmSetSymbolClauses guard (ntmLeftVar M x t s i) target

def ntmSetRightCell
    (guard : NTMClause)
    (M : PolyNTMCandidate) (x : BitString) (t s i : Nat)
    (target : Option Bool) : NTMCNF :=
  ntmSetSymbolClauses guard (ntmRightVar M x t s i) target

def ntmCopyLeftCell
    (guard : NTMClause)
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (oldS oldI newS newI : Nat) : NTMCNF :=
  ntmCopySymbolClauses guard
    (ntmLeftVar M x t oldS oldI)
    (ntmLeftVar M x t newS newI)

def ntmCopyRightCell
    (guard : NTMClause)
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (oldS oldI newS newI : Nat) : NTMCNF :=
  ntmCopySymbolClauses guard
    (ntmRightVar M x t oldS oldI)
    (ntmRightVar M x t newS newI)

def ntmCopyHeadCell
    (guard : NTMClause)
    (M : PolyNTMCandidate) (t oldS newS : Nat) : NTMCNF :=
  ntmCopySymbolClauses guard
    (ntmHeadVar M t oldS)
    (ntmHeadVar M t newS)

def ntmInitialCNF
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) : NTMCNF :=
  let tape := inputTape x
  ntmSetStateClauses [] M t 0 M.machine.initial ++
  ntmSetSymbolClauses [] (ntmHeadVar M t 0) tape.head ++
  (List.range (ntmRadius x t)).flatMap (fun i =>
    ntmSetLeftCell [] M x t 0 i
      (tape.left.getD i M.machine.blank)) ++
  (List.range (ntmRadius x t)).flatMap (fun i =>
    ntmSetRightCell [] M x t 0 i
      (tape.right.getD i M.machine.blank))

def ntmIndexedTransitionsAux
    {State Symbol : Type} :
    Nat -> List (State × Symbol × Direction) ->
      List (Nat × (State × Symbol × Direction))
  | _, [] => []
  | j, tr :: rest => (j, tr) :: ntmIndexedTransitionsAux (j + 1) rest

def ntmIndexedTransitions
    {State Symbol : Type}
    (ts : List (State × Symbol × Direction)) :
    List (Nat × (State × Symbol × Direction)) :=
  ntmIndexedTransitionsAux 0 ts

def ntmChoiceGuardCNF
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool) (j : Nat) : NTMCNF :=
  let c := ntmChoiceVar M x t s q a j
  [ [ntmNeg c, ntmPos (ntmStateVar M t s q)]
  , [ntmNeg c, ntmPos (ntmHeadVar M t s a)] ]

def ntmGuardChoiceClause
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool) : NTMClause :=
  [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)] ++
    (ntmIndexedTransitions (M.machine.transition q a)).map
      (fun p => ntmPos (ntmChoiceVar M x t s q a p.1))

def ntmAtMostOneChoiceCNF
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool) : NTMCNF :=
  let ids := (ntmIndexedTransitions (M.machine.transition q a)).map Prod.fst
  ids.flatMap fun j =>
    ids.flatMap fun k =>
      if j < k then
        [[ntmNeg (ntmChoiceVar M x t s q a j),
          ntmNeg (ntmChoiceVar M x t s q a k)]]
      else []

def ntmStayEffectCNF
    (guard : NTMClause)
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (qNext : Fin (M.stateCount + 1))
    (write : Option Bool) : NTMCNF :=
  ntmSetStateClauses guard M t (s + 1) qNext ++
  ntmSetSymbolClauses guard (ntmHeadVar M t (s + 1)) write ++
  ntmCopyLeftAll guard M x t s ++
  ntmCopyRightAll guard M x t s

def ntmLeftEffectCNF
    (guard : NTMClause)
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (qNext : Fin (M.stateCount + 1))
    (write : Option Bool) : NTMCNF :=
  let r := ntmRadius x t
  let shiftedLeft :=
    (List.range (r - 1)).flatMap fun i =>
      ntmCopyLeftCell guard M x t s (i + 1) (s + 1) i
  let shiftedRight :=
    (List.range (r - 1)).flatMap fun i =>
      ntmCopyRightCell guard M x t s i (s + 1) (i + 1)
  ntmSetStateClauses guard M t (s + 1) qNext ++
  ntmCopySymbolClauses guard
    (ntmLeftVar M x t s 0)
    (ntmHeadVar M t (s + 1)) ++
  shiftedLeft ++
  ntmSetLeftCell guard M x t (s + 1) (r - 1) M.machine.blank ++
  ntmSetRightCell guard M x t (s + 1) 0 write ++
  shiftedRight

def ntmRightEffectCNF
    (guard : NTMClause)
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (qNext : Fin (M.stateCount + 1))
    (write : Option Bool) : NTMCNF :=
  let r := ntmRadius x t
  let shiftedLeft :=
    (List.range (r - 1)).flatMap fun i =>
      ntmCopyLeftCell guard M x t s i (s + 1) (i + 1)
  let shiftedRight :=
    (List.range (r - 1)).flatMap fun i =>
      ntmCopyRightCell guard M x t s (i + 1) (s + 1) i
  ntmSetStateClauses guard M t (s + 1) qNext ++
  ntmCopySymbolClauses guard
    (ntmRightVar M x t s 0)
    (ntmHeadVar M t (s + 1)) ++
  ntmSetLeftCell guard M x t (s + 1) 0 write ++
  shiftedLeft ++
  shiftedRight ++
  ntmSetRightCell guard M x t (s + 1) (r - 1) M.machine.blank

def ntmChoiceEffectCNF
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry : Nat × (Fin (M.stateCount + 1) × Option Bool × Direction)) : NTMCNF :=
  let j := entry.1
  let tr := entry.2
  let guard := [ntmNeg (ntmChoiceVar M x t s q a j)]
  match tr with
  | (qNext, write, .stay) =>
      ntmStayEffectCNF guard M x t s qNext write
  | (qNext, write, .left) =>
      ntmLeftEffectCNF guard M x t s qNext write
  | (qNext, write, .right) =>
      ntmRightEffectCNF guard M x t s qNext write

def ntmHaltedStutterCNF
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool) : NTMCNF :=
  let guard := [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)]
  ntmSetStateClauses guard M t (s + 1) q ++
  ntmCopyHeadCell guard M t s (s + 1) ++
  ntmCopyLeftAll guard M x t s ++
  ntmCopyRightAll guard M x t s

def ntmActiveChoiceCNF
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool) : NTMCNF :=
  let entries := ntmIndexedTransitions (M.machine.transition q a)
  [ntmGuardChoiceClause M x t s q a] ++
  entries.flatMap (fun p => ntmChoiceGuardCNF M x t s q a p.1) ++
  ntmAtMostOneChoiceCNF M x t s q a ++
  entries.flatMap (fun p => ntmChoiceEffectCNF M x t s q a p)

def ntmTransitionCaseCNF
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool) : NTMCNF :=
  if M.machine.accepting q || M.machine.rejecting q then
    ntmHaltedStutterCNF M x t s q a
  else
    ntmActiveChoiceCNF M x t s q a

def ntmTransitionStepCNF
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat) : NTMCNF :=
  (List.ofFn fun q : Fin (M.stateCount + 1) =>
    ntmAlphabet.flatMap fun a =>
      ntmTransitionCaseCNF M x t s q a).flatten

def ntmTransitionsCNF
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) : NTMCNF :=
  (List.range t).flatMap fun s =>
    ntmTransitionStepCNF M x t s

def ntmAcceptingStateLits
    (M : PolyNTMCandidate) (t : Nat) : NTMClause :=
  (List.ofFn fun q : Fin (M.stateCount + 1) => q).filterMap fun q =>
    if M.machine.accepting q = true then
      some (ntmPos (ntmStateVar M t t q))
    else none

def ntmFinalAcceptanceCNF
    (M : PolyNTMCandidate) (t : Nat) : NTMCNF :=
  [ntmAcceptingStateLits M t]

def boundedExecTableauCNF_NTM
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) : NTMCNF :=
  ntmInitialCNF M x t ++
  ntmTransitionsCNF M x t ++
  ntmFinalAcceptanceCNF M t

def boundedExecCircuit_NTM
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) : Circuit :=
  ntmCNFCircuit (boundedExecTableauCNF_NTM M x t)

theorem evalNTMCNF_append
    (sigma : Assignment) (l1 l2 : NTMCNF) :
    evalNTMCNF sigma (l1 ++ l2) = true <->
      evalNTMCNF sigma l1 = true ∧
      evalNTMCNF sigma l2 = true := by
  induction l1 with
  | nil =>
      simp [evalNTMCNF]
  | cons c cs ih =>
      simp [evalNTMCNF, ih, Bool.and_eq_true]

theorem evalNTMCNF_cons_iff
    (sigma : Assignment) (c : NTMClause) (cs : NTMCNF) :
    evalNTMCNF sigma (c :: cs) = true <->
      evalNTMClause sigma c = true ∧
      evalNTMCNF sigma cs = true := by
  simp [evalNTMCNF, Bool.and_eq_true]

theorem evalNTMCNF_of_mem
    (sigma : Assignment) (f : NTMCNF) (c : NTMClause)
    (hSat : evalNTMCNF sigma f = true)
    (hc : c ∈ f) :
    evalNTMClause sigma c = true := by
  induction f with
  | nil =>
      simp at hc
  | cons d ds ih =>
      have hsplit :
          evalNTMClause sigma d = true ∧
          evalNTMCNF sigma ds = true :=
        (evalNTMCNF_cons_iff sigma d ds).mp hSat
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hsplit.1
      · exact ih hsplit.2 hc

@[simp] theorem evalNTMClause_singleton_pos
    (sigma : Assignment) (v : Nat) :
    evalNTMClause sigma [ntmPos v] = true <->
      sigma v = true := by
  cases h : sigma v <;>
    simp [evalNTMClause, evalNTMLiteral, ntmPos, h]

@[simp] theorem evalNTMClause_singleton_neg
    (sigma : Assignment) (v : Nat) :
    evalNTMClause sigma [ntmNeg v] = true <->
      sigma v = false := by
  cases h : sigma v <;>
    simp [evalNTMClause, evalNTMLiteral, ntmNeg, h]

theorem eval_ntmLiteralCircuit
    (sigma : Assignment) (l : NTMLiteral) :
    evalCircuit sigma (ntmLiteralCircuit l) = evalNTMLiteral sigma l := by
  cases l with
  | mk v p =>
      cases p <;> rfl

theorem eval_ntmClauseCircuit
    (sigma : Assignment) (c : NTMClause) :
    evalCircuit sigma (ntmClauseCircuit c) = evalNTMClause sigma c := by
  induction c with
  | nil =>
      rfl
  | cons l ls ih =>
      simp [ntmClauseCircuit, evalCircuit, evalNTMClause,
        eval_ntmLiteralCircuit, ih]

theorem eval_ntmCNFCircuit
    (sigma : Assignment) (f : NTMCNF) :
    evalCircuit sigma (ntmCNFCircuit f) = evalNTMCNF sigma f := by
  induction f with
  | nil =>
      rfl
  | cons c cs ih =>
      simp [ntmCNFCircuit, evalCircuit, evalNTMCNF,
        eval_ntmClauseCircuit, ih]

theorem ntmLiteralCircuit_isClause (l : NTMLiteral) :
    IsClause (ntmLiteralCircuit l) := by
  cases l with
  | mk v p =>
      cases p <;> simp [ntmLiteralCircuit, IsClause]

theorem ntmClauseCircuit_isClause (c : NTMClause) :
    IsClause (ntmClauseCircuit c) := by
  induction c with
  | nil => exact emptyClause_isClause
  | cons l ls ih =>
      exact IsClause_or (ntmLiteralCircuit_isClause l) ih

theorem ntmCNFCircuit_isCNF (f : NTMCNF) :
    IsCNF (ntmCNFCircuit f) := by
  induction f with
  | nil => exact emptyCNF_isCNF
  | cons c cs ih =>
      exact IsCNF_and (isClause_isCNF (ntmClauseCircuit_isClause c)) ih

theorem satLanguage_ntmCNFCircuit_iff
    (f : NTMCNF) :
    SATLanguage (ntmCNFCircuit f) <->
      ∃ sigma : Assignment, evalNTMCNF sigma f = true := by
  constructor
  · rintro ⟨_hcnf, sigma, hsat⟩
    exact ⟨sigma, by simpa [eval_ntmCNFCircuit] using hsat⟩
  · rintro ⟨sigma, hsat⟩
    refine ⟨ntmCNFCircuit_isCNF f, sigma, ?_⟩
    simpa [eval_ntmCNFCircuit] using hsat

@[simp] theorem evalNTMClause_singleton_litFor
    (sigma : Assignment) (v : Nat) (b : Bool) :
    evalNTMClause sigma [ntmLitFor v b] = true <->
      sigma v = b := by
  cases b <;>
    simp [ntmLitFor]

theorem evalNTMCNF_ofFn_litFor_iff
    {n : Nat}
    (sigma : Assignment)
    (v : Fin n -> Nat)
    (b : Fin n -> Bool) :
    evalNTMCNF sigma
        (List.ofFn fun i : Fin n => [ntmLitFor (v i) (b i)]) = true <->
      forall i : Fin n, sigma (v i) = b i := by
  induction n with
  | zero =>
      simp [evalNTMCNF]
  | succ n ih =>
      rw [List.ofFn_succ]
      rw [evalNTMCNF_cons_iff]
      rw [evalNTMClause_singleton_litFor]
      constructor
      · rintro ⟨h0, hs⟩ i
        refine Fin.cases h0 ?_ i
        intro j
        exact (ih
          (fun k => v k.succ)
          (fun k => b k.succ)).mp hs j
      · intro h
        constructor
        · exact h 0
        · exact (ih
            (fun k => v k.succ)
            (fun k => b k.succ)).mpr
            (fun j => h j.succ)

theorem eval_ntmSetStateClauses_nil_iff
    (sigma : Assignment)
    (M : PolyNTMCandidate)
    (t s : Nat)
    (target : Fin (M.stateCount + 1)) :
    evalNTMCNF sigma (ntmSetStateClauses [] M t s target) = true <->
      forall q : Fin (M.stateCount + 1),
        sigma (ntmStateVar M t s q) = decide (q = target) := by
  simpa [ntmSetStateClauses] using
    (evalNTMCNF_ofFn_litFor_iff
      sigma
      (fun q : Fin (M.stateCount + 1) => ntmStateVar M t s q)
      (fun q : Fin (M.stateCount + 1) => decide (q = target)))

theorem eval_ntmSetSymbolClauses_nil_iff
    (sigma : Assignment)
    (varAt : Option Bool -> Nat)
    (target : Option Bool) :
    evalNTMCNF sigma (ntmSetSymbolClauses [] varAt target) = true <->
      forall a : Option Bool,
        sigma (varAt a) = decide (a = target) := by
  cases target with
  | none =>
      constructor
      · intro h a
        rcases (evalNTMCNF_append sigma
          [[ntmLitFor (varAt none) true]]
          [[ntmLitFor (varAt (some false)) false],
           [ntmLitFor (varAt (some true)) false]]).mp
          (by simpa [ntmSetSymbolClauses, ntmAlphabet, evalNTMCNF] using h) with
          ⟨h0, hrest⟩
        have hn : sigma (varAt none) = true := by
          simpa [evalNTMCNF] using h0
        have hr := hrest
        cases a with
        | none => simpa using hn
        | some b =>
            cases b <;>
              simp [ntmSetSymbolClauses, ntmAlphabet, evalNTMCNF,
                evalNTMClause, evalNTMLiteral, ntmLitFor] at h ⊢
      · intro h
        have hnone := h none
        have hf := h (some false)
        have ht := h (some true)
        simpa [ntmSetSymbolClauses, ntmAlphabet, evalNTMCNF,
          evalNTMClause, evalNTMLiteral, ntmLitFor] using
          And.intro hnone (And.intro hf ht)
  | some targetBool =>
      cases targetBool <;>
        constructor
        · intro h a
          cases a with
          | none =>
              simp [ntmSetSymbolClauses, ntmAlphabet, evalNTMCNF,
                evalNTMClause, evalNTMLiteral, ntmLitFor] at h ⊢
          | some b =>
              cases b <;>
                simp [ntmSetSymbolClauses, ntmAlphabet, evalNTMCNF,
                  evalNTMClause, evalNTMLiteral, ntmLitFor] at h ⊢
        · intro h
          have hnone := h none
          have hf := h (some false)
          have ht := h (some true)
          simpa [ntmSetSymbolClauses, ntmAlphabet, evalNTMCNF,
            evalNTMClause, evalNTMLiteral, ntmLitFor] using
            And.intro hnone (And.intro hf ht)

theorem eval_ntmSetLeftCell_nil_iff
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment) (i : Nat) (a : Option Bool) :
    evalNTMCNF sigma (ntmSetLeftCell [] M x t 0 i a) = true <->
      forall b : Option Bool,
        sigma (ntmLeftVar M x t 0 i b) = decide (b = a) := by
  exact eval_ntmSetSymbolClauses_nil_iff
    sigma (ntmLeftVar M x t 0 i) a

theorem eval_ntmSetRightCell_nil_iff
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment) (i : Nat) (a : Option Bool) :
    evalNTMCNF sigma (ntmSetRightCell [] M x t 0 i a) = true <->
      forall b : Option Bool,
        sigma (ntmRightVar M x t 0 i b) = decide (b = a) := by
  exact eval_ntmSetSymbolClauses_nil_iff
    sigma (ntmRightVar M x t 0 i) a

theorem evalNTMCNF_flatMap_range
    (sigma : Assignment) (n : Nat) (f : Nat -> NTMCNF) :
    evalNTMCNF sigma ((List.range n).flatMap f) = true <->
      forall i : Nat, i < n -> evalNTMCNF sigma (f i) = true := by
  induction n with
  | zero =>
      simp [evalNTMCNF]
  | succ n ih =>
      rw [List.range_succ]
      rw [List.flatMap_append]
      rw [evalNTMCNF_append]
      rw [ih]
      constructor
      · rintro ⟨hprev, hlast⟩ i hi
        by_cases hEq : i = n
        · subst i
          simpa using hlast
        · exact hprev i (by omega)
      · intro h
        constructor
        · intro i hi
          exact h i (by omega)
        · simpa using h n (by omega)

theorem evalNTMCNF_flatMap_list
    {α : Type}
    (sigma : Assignment)
    (xs : List α)
    (f : α -> NTMCNF) :
    evalNTMCNF sigma (xs.flatMap f) = true <->
      forall a, a ∈ xs -> evalNTMCNF sigma (f a) = true := by
  induction xs with
  | nil =>
      simp [evalNTMCNF]
  | cons a as ih =>
      rw [List.flatMap_cons]
      rw [evalNTMCNF_append]
      rw [ih]
      constructor
      · rintro ⟨ha, has⟩ x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ha
        · exact has x hx
      · intro h
        constructor
        · exact h a (by simp)
        · intro x hx
          exact h x (by simp [hx])

theorem evalNTMCNF_flatten
    (sigma : Assignment)
    (xss : List NTMCNF) :
    evalNTMCNF sigma xss.flatten = true <->
      forall xs, xs ∈ xss -> evalNTMCNF sigma xs = true := by
  simpa [List.flatten] using
    (evalNTMCNF_flatMap_list sigma xss (fun xs => xs))

theorem evalNTMCNF_map_flatten_ofFn
    {n : Nat}
    (sigma : Assignment)
    (f : Fin n -> NTMCNF) :
    evalNTMCNF sigma (List.ofFn f).flatten = true <->
      forall i : Fin n, evalNTMCNF sigma (f i) = true := by
  rw [evalNTMCNF_flatten]
  constructor
  · intro h i
    exact h (f i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · intro h xs hxs
    rcases List.mem_ofFn.mp hxs with ⟨i, rfl⟩
    exact h i

theorem evalNTMClause_append
    (sigma : Assignment) (c1 c2 : NTMClause) :
    evalNTMClause sigma (c1 ++ c2) = true <->
      evalNTMClause sigma c1 = true \/
      evalNTMClause sigma c2 = true := by
  induction c1 with
  | nil =>
      simp [evalNTMClause]
  | cons l ls ih =>
      simp [evalNTMClause, ih, Bool.or_eq_true, or_assoc]

theorem evalNTMClause_map_pos_exists
    {α : Type}
    (sigma : Assignment)
    (xs : List α)
    (v : α -> Nat) :
    evalNTMClause sigma (xs.map (fun a => ntmPos (v a))) = true <->
      ∃ a ∈ xs, sigma (v a) = true := by
  induction xs with
  | nil =>
      simp [evalNTMClause]
  | cons a as ih =>
      simp [evalNTMClause, evalNTMLiteral, ntmPos, ih,
        Bool.or_eq_true, or_assoc]

theorem indexedTransitions_index_lt
    {State Symbol : Type}
    (ts : List (State × Symbol × Direction))
    {j : Nat} {tr : State × Symbol × Direction}
    (h : (j, tr) ∈ ntmIndexedTransitions ts) :
    j < ts.length := by
  unfold ntmIndexedTransitions at h
  generalize hstart : 0 = start at h
  clear hstart
  induction ts generalizing start j tr with
  | nil =>
      simp [ntmIndexedTransitionsAux] at h
  | cons x xs ih =>
      simp [ntmIndexedTransitionsAux] at h
      rcases h with h | h
      · rcases h with ⟨rfl, rfl⟩
        simp
      · have hj := ih (start := start + 1) h
        simp at hj ⊢
        omega

theorem boundedExec_transitionStep_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t) :
    evalNTMCNF sigma (ntmTransitionStepCNF M x t s) = true := by
  have hAll :=
    (evalNTMCNF_append sigma
      (ntmInitialCNF M x t)
      (ntmTransitionsCNF M x t ++ ntmFinalAcceptanceCNF M t)).mp
      (by simpa [boundedExecTableauCNF_NTM, List.append_assoc] using hSat)
  have hTransFinal := hAll.2
  have hTrans :=
    (evalNTMCNF_append sigma
      (ntmTransitionsCNF M x t)
      (ntmFinalAcceptanceCNF M t)).mp hTransFinal
  exact (evalNTMCNF_flatMap_range sigma t
    (fun r => ntmTransitionStepCNF M x t r)).mp
      (by simpa [ntmTransitionsCNF] using hTrans.1) s hs

theorem transitionStep_case_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (sigma : Assignment)
    (hStep : evalNTMCNF sigma (ntmTransitionStepCNF M x t s) = true) :
    evalNTMCNF sigma (ntmTransitionCaseCNF M x t s q a) = true := by
  have hq :=
    (evalNTMCNF_map_flatten_ofFn sigma
      (fun q : Fin (M.stateCount + 1) =>
        ntmAlphabet.flatMap fun a =>
          ntmTransitionCaseCNF M x t s q a)).mp
      (by simpa [ntmTransitionStepCNF] using hStep) q
  exact (evalNTMCNF_flatMap_list sigma ntmAlphabet
    (fun a => ntmTransitionCaseCNF M x t s q a)).mp hq a
      (by cases a <;> simp [ntmAlphabet])

theorem activeChoice_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (sigma : Assignment)
    (hCase : evalNTMCNF sigma (ntmTransitionCaseCNF M x t s q a) = true)
    (hActive :
      M.machine.accepting q = false ∧
      M.machine.rejecting q = false) :
    evalNTMCNF sigma (ntmActiveChoiceCNF M x t s q a) = true := by
  have hor :
      M.machine.accepting q || M.machine.rejecting q = false := by
    simp [hActive.1, hActive.2]
  simpa [ntmTransitionCaseCNF, hor] using hCase

theorem ntmChoice_exists_nat_of_guard
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (sigma : Assignment)
    (hActiveSat :
      evalNTMCNF sigma (ntmActiveChoiceCNF M x t s q a) = true)
    (hq : sigma (ntmStateVar M t s q) = true)
    (ha : sigma (ntmHeadVar M t s a) = true) :
    ∃ j tr,
      (j, tr) ∈ ntmIndexedTransitions (M.machine.transition q a) ∧
      sigma (ntmChoiceVar M x t s q a j) = true := by
  have hfirst :=
    (evalNTMCNF_append sigma
      [[ntmGuardChoiceClause M x t s q a]]
      ((ntmIndexedTransitions (M.machine.transition q a)).flatMap
          (fun p => ntmChoiceGuardCNF M x t s q a p.1) ++
       ntmAtMostOneChoiceCNF M x t s q a ++
       (ntmIndexedTransitions (M.machine.transition q a)).flatMap
          (fun p => ntmChoiceEffectCNF M x t s q a p))).mp
      (by simpa [ntmActiveChoiceCNF, List.append_assoc] using hActiveSat)
  have hclause :
      evalNTMClause sigma (ntmGuardChoiceClause M x t s q a) = true := by
    simpa [evalNTMCNF] using hfirst.1
  have htail :
      evalNTMClause sigma
        ((ntmIndexedTransitions (M.machine.transition q a)).map
          (fun p => ntmPos (ntmChoiceVar M x t s q a p.1))) = true := by
    have happ :=
      (evalNTMClause_append sigma
        [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)]
        ((ntmIndexedTransitions (M.machine.transition q a)).map
          (fun p => ntmPos (ntmChoiceVar M x t s q a p.1)))).mp
        (by simpa [ntmGuardChoiceClause] using hclause)
    rcases happ with hneg | htail
    · simp [evalNTMClause, evalNTMLiteral, ntmNeg, hq, ha] at hneg
    · exact htail
  rcases (evalNTMClause_map_pos_exists sigma
    (ntmIndexedTransitions (M.machine.transition q a))
    (fun p => ntmChoiceVar M x t s q a p.1)).mp htail with
    ⟨p, hp, hptrue⟩
  exact ⟨p.1, p.2, hp, hptrue⟩

theorem ntmChoice_exists_of_guard
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hq : sigma (ntmStateVar M t s q) = true)
    (ha : sigma (ntmHeadVar M t s a) = true)
    (hActive :
      M.machine.accepting q = false ∧ M.machine.rejecting q = false) :
    ∃ j : Fin (M.machine.transition q a).length,
      sigma (ntmChoiceVar M x t s q a j.val) = true := by
  have hStep := boundedExec_transitionStep_sat M x t s sigma hSat hs
  have hCase := transitionStep_case_sat M x t s q a sigma hStep
  have hActiveSat := activeChoice_sat M x t s q a sigma hCase hActive
  rcases ntmChoice_exists_nat_of_guard
      M x t s q a sigma hActiveSat hq ha with
    ⟨j, tr, hjmem, hjtrue⟩
  exact ⟨⟨j, indexedTransitions_index_lt
    (M.machine.transition q a) hjmem⟩, hjtrue⟩

theorem boundedExecCircuit_NTM_isCNF
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) :
    IsCNF (boundedExecCircuit_NTM M x t) := by
  exact ntmCNFCircuit_isCNF _


theorem indexedTransitions_index_mem
    {State Symbol : Type}
    (ts : List (State × Symbol × Direction))
    (j : Nat)
    (hj : j < ts.length) :
    ∃ tr, (j, tr) ∈ ntmIndexedTransitions ts := by
  unfold ntmIndexedTransitions
  generalize hstart : 0 = start
  subst start
  induction ts generalizing j with
  | nil =>
      simp at hj
  | cons tr rest ih =>
      cases j with
      | zero =>
          exact ⟨tr, by simp [ntmIndexedTransitionsAux]⟩
      | succ j =>
          have hj' : j < rest.length := by
            simpa using Nat.succ_lt_succ_iff.mp (by simpa using hj)
          rcases ih j hj' with ⟨tr', hmem⟩
          exact ⟨tr', by
            simp [ntmIndexedTransitionsAux]
            exact hmem⟩

theorem indexedTransitions_index_in_ids
    {State Symbol : Type}
    (ts : List (State × Symbol × Direction))
    (j : Nat)
    (hj : j < ts.length) :
    j ∈ (ntmIndexedTransitions ts).map Prod.fst := by
  rcases indexedTransitions_index_mem ts j hj with ⟨tr, hmem⟩
  exact List.mem_map.mpr ⟨(j, tr), hmem, rfl⟩

theorem activeChoice_atMostOne_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (sigma : Assignment)
    (hActiveSat :
      evalNTMCNF sigma (ntmActiveChoiceCNF M x t s q a) = true) :
    evalNTMCNF sigma (ntmAtMostOneChoiceCNF M x t s q a) = true := by
  let entries := ntmIndexedTransitions (M.machine.transition q a)
  have h1 :=
    (evalNTMCNF_append sigma
      [[ntmGuardChoiceClause M x t s q a]]
      (entries.flatMap (fun p => ntmChoiceGuardCNF M x t s q a p.1) ++
       ntmAtMostOneChoiceCNF M x t s q a ++
       entries.flatMap (fun p => ntmChoiceEffectCNF M x t s q a p))).mp
      (by simpa [ntmActiveChoiceCNF, entries, List.append_assoc] using hActiveSat)
  have h2 :=
    (evalNTMCNF_append sigma
      (entries.flatMap (fun p => ntmChoiceGuardCNF M x t s q a p.1))
      (ntmAtMostOneChoiceCNF M x t s q a ++
       entries.flatMap (fun p => ntmChoiceEffectCNF M x t s q a p))).mp
      h1.2
  have h3 :=
    (evalNTMCNF_append sigma
      (ntmAtMostOneChoiceCNF M x t s q a)
      (entries.flatMap (fun p => ntmChoiceEffectCNF M x t s q a p))).mp
      h2.2
  exact h3.1

theorem activeChoice_choiceGuards_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (sigma : Assignment)
    (hActiveSat :
      evalNTMCNF sigma (ntmActiveChoiceCNF M x t s q a) = true) :
    evalNTMCNF sigma
      ((ntmIndexedTransitions (M.machine.transition q a)).flatMap
        (fun p => ntmChoiceGuardCNF M x t s q a p.1)) = true := by
  let entries := ntmIndexedTransitions (M.machine.transition q a)
  have h1 :=
    (evalNTMCNF_append sigma
      [[ntmGuardChoiceClause M x t s q a]]
      (entries.flatMap (fun p => ntmChoiceGuardCNF M x t s q a p.1) ++
       ntmAtMostOneChoiceCNF M x t s q a ++
       entries.flatMap (fun p => ntmChoiceEffectCNF M x t s q a p))).mp
      (by simpa [ntmActiveChoiceCNF, entries, List.append_assoc] using hActiveSat)
  have h2 :=
    (evalNTMCNF_append sigma
      (entries.flatMap (fun p => ntmChoiceGuardCNF M x t s q a p.1))
      (ntmAtMostOneChoiceCNF M x t s q a ++
       entries.flatMap (fun p => ntmChoiceEffectCNF M x t s q a p))).mp
      h1.2
  simpa [entries] using h2.1

theorem ntmAtMostOne_pair_mem
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j k : Nat)
    (hj : j < (M.machine.transition q a).length)
    (hk : k < (M.machine.transition q a).length)
    (hjk : j < k) :
    [ntmNeg (ntmChoiceVar M x t s q a j),
     ntmNeg (ntmChoiceVar M x t s q a k)] ∈
      ntmAtMostOneChoiceCNF M x t s q a := by
  let ids := (ntmIndexedTransitions (M.machine.transition q a)).map Prod.fst
  have hjmem : j ∈ ids := by
    simpa [ids] using
      indexedTransitions_index_in_ids (M.machine.transition q a) j hj
  have hkmem : k ∈ ids := by
    simpa [ids] using
      indexedTransitions_index_in_ids (M.machine.transition q a) k hk
  simp [ntmAtMostOneChoiceCNF, ids, List.mem_flatMap, hjmem, hkmem, hjk]

theorem ntmChoice_unique_of_guard
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hActive :
      M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (j1 j2 : Fin (M.machine.transition q a).length)
    (h1 : sigma (ntmChoiceVar M x t s q a j1.val) = true)
    (h2 : sigma (ntmChoiceVar M x t s q a j2.val) = true) :
    j1 = j2 := by
  apply Fin.ext
  by_contra hne
  have hlt : j1.val < j2.val ∨ j2.val < j1.val := by
    omega
  have hStep := boundedExec_transitionStep_sat M x t s sigma hSat hs
  have hCase := transitionStep_case_sat M x t s q a sigma hStep
  have hActiveSat := activeChoice_sat M x t s q a sigma hCase hActive
  have hAtMost := activeChoice_atMostOne_sat M x t s q a sigma hActiveSat
  rcases hlt with h12 | h21
  · have hmem := ntmAtMostOne_pair_mem M x t s q a
        j1.val j2.val j1.isLt j2.isLt h12
    have hc := evalNTMCNF_of_mem sigma
      (ntmAtMostOneChoiceCNF M x t s q a) _ hAtMost hmem
    simp [evalNTMClause, evalNTMLiteral, ntmNeg, h1, h2] at hc
  · have hmem := ntmAtMostOne_pair_mem M x t s q a
        j2.val j1.val j2.isLt j1.isLt h21
    have hc := evalNTMCNF_of_mem sigma
      (ntmAtMostOneChoiceCNF M x t s q a) _ hAtMost hmem
    simp [evalNTMClause, evalNTMLiteral, ntmNeg, h1, h2] at hc

theorem ntmChoice_exists_unique_of_guard
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hq : sigma (ntmStateVar M t s q) = true)
    (ha : sigma (ntmHeadVar M t s a) = true)
    (hActive :
      M.machine.accepting q = false ∧ M.machine.rejecting q = false) :
    ∃! j : Fin (M.machine.transition q a).length,
      sigma (ntmChoiceVar M x t s q a j.val) = true := by
  rcases ntmChoice_exists_of_guard M x t s q a sigma
      hSat hs hq ha hActive with ⟨j, hj⟩
  refine ⟨j, hj, ?_⟩
  intro k hk
  exact ntmChoice_unique_of_guard M x t s q a sigma
    hSat hs hActive k j hk hj

theorem ntmChoice_implies_guard
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Nat)
    (hjLt : j < (M.machine.transition q a).length)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hActive :
      M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hj : sigma (ntmChoiceVar M x t s q a j) = true) :
    sigma (ntmStateVar M t s q) = true ∧
      sigma (ntmHeadVar M t s a) = true := by
  have hStep := boundedExec_transitionStep_sat M x t s sigma hSat hs
  have hCase := transitionStep_case_sat M x t s q a sigma hStep
  have hActiveSat := activeChoice_sat M x t s q a sigma hCase hActive
  have hGuards := activeChoice_choiceGuards_sat M x t s q a sigma hActiveSat
  rcases indexedTransitions_index_mem
      (M.machine.transition q a) j hjLt with ⟨tr, hmem⟩
  have hblock :=
    (evalNTMCNF_flatMap_list sigma
      (ntmIndexedTransitions (M.machine.transition q a))
      (fun p => ntmChoiceGuardCNF M x t s q a p.1)).mp
      hGuards (j, tr) hmem
  have hfirst :
      evalNTMClause sigma
        [ntmNeg (ntmChoiceVar M x t s q a j),
         ntmPos (ntmStateVar M t s q)] = true := by
    exact (evalNTMCNF_cons_iff sigma
      [ntmNeg (ntmChoiceVar M x t s q a j),
       ntmPos (ntmStateVar M t s q)]
      [[ntmNeg (ntmChoiceVar M x t s q a j),
        ntmPos (ntmHeadVar M t s a)]]).mp
      (by simpa [ntmChoiceGuardCNF] using hblock) |>.1
  have hsecond :
      evalNTMClause sigma
        [ntmNeg (ntmChoiceVar M x t s q a j),
         ntmPos (ntmHeadVar M t s a)] = true := by
    exact (evalNTMCNF_cons_iff sigma
      [ntmNeg (ntmChoiceVar M x t s q a j),
       ntmPos (ntmStateVar M t s q)]
      [[ntmNeg (ntmChoiceVar M x t s q a j),
        ntmPos (ntmHeadVar M t s a)]]).mp
      (by simpa [ntmChoiceGuardCNF] using hblock) |>.2 |>.1
  constructor
  · cases hsq : sigma (ntmStateVar M t s q) <;>
      simp [evalNTMClause, evalNTMLiteral, ntmNeg, ntmPos, hj, hsq] at hfirst ⊢
  · cases hha : sigma (ntmHeadVar M t s a) <;>
      simp [evalNTMClause, evalNTMLiteral, ntmNeg, ntmPos, hj, hha] at hsecond ⊢

theorem ntmChoice_implies_state
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Nat)
    (hjLt : j < (M.machine.transition q a).length)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hActive :
      M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hj : sigma (ntmChoiceVar M x t s q a j) = true) :
    sigma (ntmStateVar M t s q) = true :=
  (ntmChoice_implies_guard M x t s q a j hjLt sigma hSat hs hActive hj).1

theorem ntmChoice_implies_head
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Nat)
    (hjLt : j < (M.machine.transition q a).length)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hActive :
      M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hj : sigma (ntmChoiceVar M x t s q a j) = true) :
    sigma (ntmHeadVar M t s a) = true :=
  (ntmChoice_implies_guard M x t s q a j hjLt sigma hSat hs hActive hj).2



theorem activeChoice_choiceEffects_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (sigma : Assignment)
    (hActiveSat :
      evalNTMCNF sigma (ntmActiveChoiceCNF M x t s q a) = true) :
    evalNTMCNF sigma
      ((ntmIndexedTransitions (M.machine.transition q a)).flatMap
        (fun p => ntmChoiceEffectCNF M x t s q a p)) = true := by
  let entries := ntmIndexedTransitions (M.machine.transition q a)
  have h1 :=
    (evalNTMCNF_append sigma
      [[ntmGuardChoiceClause M x t s q a]]
      (entries.flatMap (fun p => ntmChoiceGuardCNF M x t s q a p.1) ++
       ntmAtMostOneChoiceCNF M x t s q a ++
       entries.flatMap (fun p => ntmChoiceEffectCNF M x t s q a p))).mp
      (by simpa [ntmActiveChoiceCNF, entries, List.append_assoc] using hActiveSat)
  have h2 :=
    (evalNTMCNF_append sigma
      (entries.flatMap (fun p => ntmChoiceGuardCNF M x t s q a p.1))
      (ntmAtMostOneChoiceCNF M x t s q a ++
       entries.flatMap (fun p => ntmChoiceEffectCNF M x t s q a p))).mp
      h1.2
  have h3 :=
    (evalNTMCNF_append sigma
      (ntmAtMostOneChoiceCNF M x t s q a)
      (entries.flatMap (fun p => ntmChoiceEffectCNF M x t s q a p))).mp
      h2.2
  simpa [entries] using h3.2

theorem choiceEffect_block_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Nat)
    (hjLt : j < (M.machine.transition q a).length)
    (sigma : Assignment)
    (hActiveSat :
      evalNTMCNF sigma (ntmActiveChoiceCNF M x t s q a) = true) :
    ∃ tr,
      (j, tr) ∈ ntmIndexedTransitions (M.machine.transition q a) ∧
      evalNTMCNF sigma (ntmChoiceEffectCNF M x t s q a (j, tr)) = true := by
  have hEffects :=
    activeChoice_choiceEffects_sat M x t s q a sigma hActiveSat
  rcases indexedTransitions_index_mem
      (M.machine.transition q a) j hjLt with ⟨tr, hmem⟩
  refine ⟨tr, hmem, ?_⟩
  exact (evalNTMCNF_flatMap_list sigma
    (ntmIndexedTransitions (M.machine.transition q a))
    (fun p => ntmChoiceEffectCNF M x t s q a p)).mp
    hEffects (j, tr) hmem

theorem evalNTMClause_neg_prefix_true
    (sigma : Assignment) (cvar : Nat) (cl : NTMClause)
    (h : evalNTMClause sigma (ntmNeg cvar :: cl) = true)
    (hc : sigma cvar = true) :
    evalNTMClause sigma cl = true := by
  simpa [evalNTMClause, evalNTMLiteral, ntmNeg, hc] using h

theorem eval_setState_neg_guard_to_nil
    (M : PolyNTMCandidate)
    (t s : Nat)
    (cvar : Nat)
    (target : Fin (M.stateCount + 1))
    (sigma : Assignment)
    (h :
      evalNTMCNF sigma
        (ntmSetStateClauses [ntmNeg cvar] M t s target) = true)
    (hc : sigma cvar = true) :
    evalNTMCNF sigma (ntmSetStateClauses [] M t s target) = true := by
  rw [eval_ntmSetStateClauses_nil_iff]
  intro r
  have hguarded :
      evalNTMClause sigma
        ([ntmNeg cvar] ++
          [ntmLitFor (ntmStateVar M t s r) (decide (r = target))]) = true := by
    apply evalNTMCNF_of_mem sigma
      (ntmSetStateClauses [ntmNeg cvar] M t s target) _
      h
    simp [ntmSetStateClauses]
  have hunit :
      evalNTMClause sigma
        [ntmLitFor (ntmStateVar M t s r) (decide (r = target))] = true := by
    exact evalNTMClause_neg_prefix_true sigma cvar _ (by simpa using hguarded) hc
  exact (evalNTMClause_singleton_litFor
    sigma (ntmStateVar M t s r) (decide (r = target))).mp hunit

theorem eval_setSymbol_neg_guard_to_nil
    (varAt : Option Bool -> Nat)
    (cvar : Nat)
    (target : Option Bool)
    (sigma : Assignment)
    (h :
      evalNTMCNF sigma
        (ntmSetSymbolClauses [ntmNeg cvar] varAt target) = true)
    (hc : sigma cvar = true) :
    evalNTMCNF sigma (ntmSetSymbolClauses [] varAt target) = true := by
  rw [eval_ntmSetSymbolClauses_nil_iff]
  intro b
  have hguarded :
      evalNTMClause sigma
        ([ntmNeg cvar] ++ [ntmLitFor (varAt b) (decide (b = target))]) = true := by
    apply evalNTMCNF_of_mem sigma
      (ntmSetSymbolClauses [ntmNeg cvar] varAt target) _
      h
    cases b <;> cases target <;>
      simp [ntmSetSymbolClauses, ntmAlphabet]
  have hunit :
      evalNTMClause sigma [ntmLitFor (varAt b) (decide (b = target))] = true := by
    exact evalNTMClause_neg_prefix_true sigma cvar _ (by simpa using hguarded) hc
  exact (evalNTMClause_singleton_litFor sigma (varAt b) (decide (b = target))).mp hunit

theorem choiceEffect_stateBlock_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry : Nat × (Fin (M.stateCount + 1) × Option Bool × Direction))
    (sigma : Assignment)
    (hEff :
      evalNTMCNF sigma (ntmChoiceEffectCNF M x t s q a entry) = true) :
    evalNTMCNF sigma
      (ntmSetStateClauses
        [ntmNeg (ntmChoiceVar M x t s q a entry.1)]
        M t (s + 1) entry.2.1) = true := by
  rcases entry with ⟨j, qNext, write, d⟩
  cases d <;>
    simp [ntmChoiceEffectCNF, ntmStayEffectCNF,
      ntmLeftEffectCNF, ntmRightEffectCNF,
      evalNTMCNF_append, List.append_assoc] at hEff ⊢
  · exact hEff.1
  · exact hEff.1
  · exact hEff.1

theorem ntmChoice_effect_state_exact
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Fin (M.machine.transition q a).length)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hActive :
      M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hj : sigma (ntmChoiceVar M x t s q a j.val) = true) :
    ∀ r : Fin (M.stateCount + 1),
      sigma (ntmStateVar M t (s + 1) r) =
        decide (r = ((M.machine.transition q a).get j).1) := by
  have hStep := boundedExec_transitionStep_sat M x t s sigma hSat hs
  have hCase := transitionStep_case_sat M x t s q a sigma hStep
  have hActiveSat := activeChoice_sat M x t s q a sigma hCase hActive
  have hEffects := activeChoice_choiceEffects_sat M x t s q a sigma hActiveSat
  have hmemIndexed :
      (j.val, (M.machine.transition q a).get j) ∈
        ntmIndexedTransitions (M.machine.transition q a) := by
    rcases indexedTransitions_index_mem
      (M.machine.transition q a) j.val j.isLt with ⟨tr, hmem⟩
    have htr : tr = (M.machine.transition q a).get j := by
      -- indexedTransitions preserves the source-list element at each index
      -- derive equality from unique lookup position by list induction
      unfold ntmIndexedTransitions at hmem
      generalize hstart : 0 = start at hmem
      subst start
      induction hts : M.machine.transition q a generalizing j.val tr with
      | nil =>
          simp at j
      | cons hd tl ih =>
          cases j with
          | mk j hjlt =>
            cases j with
            | zero =>
                simp [ntmIndexedTransitionsAux] at hmem
                rcases hmem with h | h
                · simpa using congrArg Prod.snd h
                · omega
            | succ k =>
                simp [ntmIndexedTransitionsAux] at hmem
                rcases hmem with h | h
                · omega
                · have hk : k < tl.length := by simpa using hjlt
                  let jk : Fin tl.length := ⟨k, hk⟩
                  have ih' := ih (j := jk) (tr := tr) h
                  simpa using ih'
    simpa [htr] using hmem
  have hEff :
      evalNTMCNF sigma
        (ntmChoiceEffectCNF M x t s q a
          (j.val, (M.machine.transition q a).get j)) = true :=
    (evalNTMCNF_flatMap_list sigma
      (ntmIndexedTransitions (M.machine.transition q a))
      (fun p => ntmChoiceEffectCNF M x t s q a p)).mp
      hEffects _ hmemIndexed
  have hStateGuarded :=
    choiceEffect_stateBlock_sat M x t s q a
      (j.val, (M.machine.transition q a).get j) sigma hEff
  have hStateNil :=
    eval_setState_neg_guard_to_nil
      M t (s + 1)
      (ntmChoiceVar M x t s q a j.val)
      ((M.machine.transition q a).get j).1
      sigma hStateGuarded hj
  exact (eval_ntmSetStateClauses_nil_iff
    sigma M t (s + 1)
    ((M.machine.transition q a).get j).1).mp hStateNil




theorem choiceEffect_headBlock_sat_stay
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry : Nat × (Fin (M.stateCount + 1) × Option Bool × Direction))
    (sigma : Assignment)
    (hEff :
      evalNTMCNF sigma (ntmChoiceEffectCNF M x t s q a entry) = true)
    (hDir : entry.2.2.2 = Direction.stay) :
    evalNTMCNF sigma
      (ntmSetSymbolClauses
        [ntmNeg (ntmChoiceVar M x t s q a entry.1)]
        (ntmHeadVar M t (s + 1)) entry.2.2.1) = true := by
  rcases entry with ⟨j, qNext, write, d⟩
  simp at hDir
  subst d
  have h1 :=
    (evalNTMCNF_append sigma
      (ntmSetStateClauses
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M t (s + 1) qNext)
      (ntmSetSymbolClauses
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        (ntmHeadVar M t (s + 1)) write ++
       ntmCopyLeftAll
        [ntmNeg (ntmChoiceVar M x t s q a j)] M x t s ++
       ntmCopyRightAll
        [ntmNeg (ntmChoiceVar M x t s q a j)] M x t s)).mp
      (by simpa [ntmChoiceEffectCNF, ntmStayEffectCNF,
        List.append_assoc] using hEff)
  exact (evalNTMCNF_append sigma
    (ntmSetSymbolClauses
      [ntmNeg (ntmChoiceVar M x t s q a j)]
      (ntmHeadVar M t (s + 1)) write)
    (ntmCopyLeftAll
      [ntmNeg (ntmChoiceVar M x t s q a j)] M x t s ++
     ntmCopyRightAll
      [ntmNeg (ntmChoiceVar M x t s q a j)] M x t s)).mp
    (by simpa [List.append_assoc] using h1.2) |>.1

theorem choiceEffect_headCopy_sat_left
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry : Nat × (Fin (M.stateCount + 1) × Option Bool × Direction))
    (sigma : Assignment)
    (hEff :
      evalNTMCNF sigma (ntmChoiceEffectCNF M x t s q a entry) = true)
    (hDir : entry.2.2.2 = Direction.left) :
    evalNTMCNF sigma
      (ntmCopySymbolClauses
        [ntmNeg (ntmChoiceVar M x t s q a entry.1)]
        (ntmLeftVar M x t s 0)
        (ntmHeadVar M t (s + 1))) = true := by
  rcases entry with ⟨j, qNext, write, d⟩
  simp at hDir
  subst d
  have h1 :=
    (evalNTMCNF_append sigma
      (ntmSetStateClauses
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M t (s + 1) qNext)
      (ntmCopySymbolClauses
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        (ntmLeftVar M x t s 0)
        (ntmHeadVar M t (s + 1)) ++
       (List.range (ntmRadius x t - 1)).flatMap (fun i =>
         ntmCopyLeftCell
           [ntmNeg (ntmChoiceVar M x t s q a j)]
           M x t s (i + 1) (s + 1) i) ++
       ntmSetLeftCell
         [ntmNeg (ntmChoiceVar M x t s q a j)]
         M x t (s + 1) (ntmRadius x t - 1) M.machine.blank ++
       ntmSetRightCell
         [ntmNeg (ntmChoiceVar M x t s q a j)]
         M x t (s + 1) 0 write ++
       (List.range (ntmRadius x t - 1)).flatMap (fun i =>
         ntmCopyRightCell
           [ntmNeg (ntmChoiceVar M x t s q a j)]
           M x t s i (s + 1) (i + 1)))).mp
      (by simpa [ntmChoiceEffectCNF, ntmLeftEffectCNF,
        List.append_assoc] using hEff)
  exact (evalNTMCNF_append sigma
    (ntmCopySymbolClauses
      [ntmNeg (ntmChoiceVar M x t s q a j)]
      (ntmLeftVar M x t s 0)
      (ntmHeadVar M t (s + 1)))
    ((List.range (ntmRadius x t - 1)).flatMap (fun i =>
      ntmCopyLeftCell
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t s (i + 1) (s + 1) i) ++
     ntmSetLeftCell
       [ntmNeg (ntmChoiceVar M x t s q a j)]
       M x t (s + 1) (ntmRadius x t - 1) M.machine.blank ++
     ntmSetRightCell
       [ntmNeg (ntmChoiceVar M x t s q a j)]
       M x t (s + 1) 0 write ++
     (List.range (ntmRadius x t - 1)).flatMap (fun i =>
      ntmCopyRightCell
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t s i (s + 1) (i + 1)))).mp
    (by simpa [List.append_assoc] using h1.2) |>.1

theorem choiceEffect_headCopy_sat_right
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry : Nat × (Fin (M.stateCount + 1) × Option Bool × Direction))
    (sigma : Assignment)
    (hEff :
      evalNTMCNF sigma (ntmChoiceEffectCNF M x t s q a entry) = true)
    (hDir : entry.2.2.2 = Direction.right) :
    evalNTMCNF sigma
      (ntmCopySymbolClauses
        [ntmNeg (ntmChoiceVar M x t s q a entry.1)]
        (ntmRightVar M x t s 0)
        (ntmHeadVar M t (s + 1))) = true := by
  rcases entry with ⟨j, qNext, write, d⟩
  simp at hDir
  subst d
  have h1 :=
    (evalNTMCNF_append sigma
      (ntmSetStateClauses
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M t (s + 1) qNext)
      (ntmCopySymbolClauses
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        (ntmRightVar M x t s 0)
        (ntmHeadVar M t (s + 1)) ++
       ntmSetLeftCell
         [ntmNeg (ntmChoiceVar M x t s q a j)]
         M x t (s + 1) 0 write ++
       (List.range (ntmRadius x t - 1)).flatMap (fun i =>
         ntmCopyLeftCell
           [ntmNeg (ntmChoiceVar M x t s q a j)]
           M x t s i (s + 1) (i + 1)) ++
       (List.range (ntmRadius x t - 1)).flatMap (fun i =>
         ntmCopyRightCell
           [ntmNeg (ntmChoiceVar M x t s q a j)]
           M x t s (i + 1) (s + 1) i) ++
       ntmSetRightCell
         [ntmNeg (ntmChoiceVar M x t s q a j)]
         M x t (s + 1) (ntmRadius x t - 1) M.machine.blank)).mp
      (by simpa [ntmChoiceEffectCNF, ntmRightEffectCNF,
        List.append_assoc] using hEff)
  exact (evalNTMCNF_append sigma
    (ntmCopySymbolClauses
      [ntmNeg (ntmChoiceVar M x t s q a j)]
      (ntmRightVar M x t s 0)
      (ntmHeadVar M t (s + 1)))
    (ntmSetLeftCell
       [ntmNeg (ntmChoiceVar M x t s q a j)]
       M x t (s + 1) 0 write ++
     (List.range (ntmRadius x t - 1)).flatMap (fun i =>
       ntmCopyLeftCell
         [ntmNeg (ntmChoiceVar M x t s q a j)]
         M x t s i (s + 1) (i + 1)) ++
     (List.range (ntmRadius x t - 1)).flatMap (fun i =>
       ntmCopyRightCell
         [ntmNeg (ntmChoiceVar M x t s q a j)]
         M x t s (i + 1) (s + 1) i) ++
     ntmSetRightCell
       [ntmNeg (ntmChoiceVar M x t s q a j)]
       M x t (s + 1) (ntmRadius x t - 1) M.machine.blank)).mp
    (by simpa [List.append_assoc] using h1.2) |>.1

theorem ntmChoice_effect_head_exact_stay
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Fin (M.machine.transition q a).length)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hActive :
      M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hDir : ((M.machine.transition q a).get j).2.2 = Direction.stay)
    (hj : sigma (ntmChoiceVar M x t s q a j.val) = true) :
    ∀ b : Option Bool,
      sigma (ntmHeadVar M t (s + 1) b) =
        decide (b = ((M.machine.transition q a).get j).2.1) := by
  have hStep := boundedExec_transitionStep_sat M x t s sigma hSat hs
  have hCase := transitionStep_case_sat M x t s q a sigma hStep
  have hActiveSat := activeChoice_sat M x t s q a sigma hCase hActive
  have hEffects := activeChoice_choiceEffects_sat M x t s q a sigma hActiveSat
  rcases indexedTransitions_index_mem
      (M.machine.transition q a) j.val j.isLt with ⟨tr, hmem⟩
  have htr : tr = (M.machine.transition q a).get j := by
    unfold ntmIndexedTransitions at hmem
    generalize hstart : 0 = start at hmem
    subst start
    induction hts : M.machine.transition q a generalizing j.val tr with
    | nil => simp at j
    | cons hd tl ih =>
        cases j with
        | mk j hjlt =>
            cases j with
            | zero =>
                simp [ntmIndexedTransitionsAux] at hmem
                rcases hmem with h | h
                · simpa using congrArg Prod.snd h
                · omega
            | succ k =>
                simp [ntmIndexedTransitionsAux] at hmem
                rcases hmem with h | h
                · omega
                · have hk : k < tl.length := by simpa using hjlt
                  let jk : Fin tl.length := ⟨k, hk⟩
                  have ih' := ih (j := jk) (tr := tr) h
                  simpa using ih'
  have hmemIndexed :
      (j.val, (M.machine.transition q a).get j) ∈
        ntmIndexedTransitions (M.machine.transition q a) := by
    simpa [htr] using hmem
  have hEff :=
    (evalNTMCNF_flatMap_list sigma
      (ntmIndexedTransitions (M.machine.transition q a))
      (fun p => ntmChoiceEffectCNF M x t s q a p)).mp
      hEffects _ hmemIndexed
  have hHeadGuarded :=
    choiceEffect_headBlock_sat_stay M x t s q a
      (j.val, (M.machine.transition q a).get j) sigma hEff hDir
  have hHeadNil :=
    eval_setSymbol_neg_guard_to_nil
      (ntmHeadVar M t (s + 1))
      (ntmChoiceVar M x t s q a j.val)
      ((M.machine.transition q a).get j).2.1
      sigma hHeadGuarded hj
  exact (eval_ntmSetSymbolClauses_nil_iff
    sigma (ntmHeadVar M t (s + 1))
    ((M.machine.transition q a).get j).2.1).mp hHeadNil

theorem ntmChoice_effect_head_exact_left
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Fin (M.machine.transition q a).length)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hActive :
      M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hDir : ((M.machine.transition q a).get j).2.2 = Direction.left)
    (hj : sigma (ntmChoiceVar M x t s q a j.val) = true) :
    ∀ b : Option Bool,
      sigma (ntmHeadVar M t (s + 1) b) =
        sigma (ntmLeftVar M x t s 0 b) := by
  have hStep := boundedExec_transitionStep_sat M x t s sigma hSat hs
  have hCase := transitionStep_case_sat M x t s q a sigma hStep
  have hActiveSat := activeChoice_sat M x t s q a sigma hCase hActive
  have hEffects := activeChoice_choiceEffects_sat M x t s q a sigma hActiveSat
  rcases indexedTransitions_index_mem
      (M.machine.transition q a) j.val j.isLt with ⟨tr, hmem⟩
  have htr : tr = (M.machine.transition q a).get j := by
    unfold ntmIndexedTransitions at hmem
    generalize hstart : 0 = start at hmem
    subst start
    induction hts : M.machine.transition q a generalizing j.val tr with
    | nil => simp at j
    | cons hd tl ih =>
        cases j with
        | mk j hjlt =>
            cases j with
            | zero =>
                simp [ntmIndexedTransitionsAux] at hmem
                rcases hmem with h | h
                · simpa using congrArg Prod.snd h
                · omega
            | succ k =>
                simp [ntmIndexedTransitionsAux] at hmem
                rcases hmem with h | h
                · omega
                · have hk : k < tl.length := by simpa using hjlt
                  let jk : Fin tl.length := ⟨k, hk⟩
                  have ih' := ih (j := jk) (tr := tr) h
                  simpa using ih'
  have hmemIndexed :
      (j.val, (M.machine.transition q a).get j) ∈
        ntmIndexedTransitions (M.machine.transition q a) := by
    simpa [htr] using hmem
  have hEff :=
    (evalNTMCNF_flatMap_list sigma
      (ntmIndexedTransitions (M.machine.transition q a))
      (fun p => ntmChoiceEffectCNF M x t s q a p)).mp
      hEffects _ hmemIndexed
  have hCopy :=
    choiceEffect_headCopy_sat_left M x t s q a
      (j.val, (M.machine.transition q a).get j) sigma hEff hDir
  exact eval_copySymbol_neg_guard_of_choice_true
    sigma
    (ntmChoiceVar M x t s q a j.val)
    (ntmLeftVar M x t s 0)
    (ntmHeadVar M t (s + 1))
    hCopy hj

theorem ntmChoice_effect_head_exact_right
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Fin (M.machine.transition q a).length)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hActive :
      M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hDir : ((M.machine.transition q a).get j).2.2 = Direction.right)
    (hj : sigma (ntmChoiceVar M x t s q a j.val) = true) :
    ∀ b : Option Bool,
      sigma (ntmHeadVar M t (s + 1) b) =
        sigma (ntmRightVar M x t s 0 b) := by
  have hStep := boundedExec_transitionStep_sat M x t s sigma hSat hs
  have hCase := transitionStep_case_sat M x t s q a sigma hStep
  have hActiveSat := activeChoice_sat M x t s q a sigma hCase hActive
  have hEffects := activeChoice_choiceEffects_sat M x t s q a sigma hActiveSat
  rcases indexedTransitions_index_mem
      (M.machine.transition q a) j.val j.isLt with ⟨tr, hmem⟩
  have htr : tr = (M.machine.transition q a).get j := by
    unfold ntmIndexedTransitions at hmem
    generalize hstart : 0 = start at hmem
    subst start
    induction hts : M.machine.transition q a generalizing j.val tr with
    | nil => simp at j
    | cons hd tl ih =>
        cases j with
        | mk j hjlt =>
            cases j with
            | zero =>
                simp [ntmIndexedTransitionsAux] at hmem
                rcases hmem with h | h
                · simpa using congrArg Prod.snd h
                · omega
            | succ k =>
                simp [ntmIndexedTransitionsAux] at hmem
                rcases hmem with h | h
                · omega
                · have hk : k < tl.length := by simpa using hjlt
                  let jk : Fin tl.length := ⟨k, hk⟩
                  have ih' := ih (j := jk) (tr := tr) h
                  simpa using ih'
  have hmemIndexed :
      (j.val, (M.machine.transition q a).get j) ∈
        ntmIndexedTransitions (M.machine.transition q a) := by
    simpa [htr] using hmem
  have hEff :=
    (evalNTMCNF_flatMap_list sigma
      (ntmIndexedTransitions (M.machine.transition q a))
      (fun p => ntmChoiceEffectCNF M x t s q a p)).mp
      hEffects _ hmemIndexed
  have hCopy :=
    choiceEffect_headCopy_sat_right M x t s q a
      (j.val, (M.machine.transition q a).get j) sigma hEff hDir
  exact eval_copySymbol_neg_guard_of_choice_true
    sigma
    (ntmChoiceVar M x t s q a j.val)
    (ntmRightVar M x t s 0)
    (ntmHeadVar M t (s + 1))
    hCopy hj

theorem eval_copySymbol_neg_guard_of_choice_true
    (sigma : Assignment)
    (cvar : Nat)
    (oldVar newVar : Option Bool -> Nat)
    (h :
      evalNTMCNF sigma
        (ntmCopySymbolClauses [ntmNeg cvar] oldVar newVar) = true)
    (hc : sigma cvar = true) :
    forall a : Option Bool,
      sigma (newVar a) = sigma (oldVar a) := by
  intro a
  have hforward :
      evalNTMClause sigma
        ([ntmNeg cvar] ++
          [ntmNeg (oldVar a), ntmPos (newVar a)]) = true := by
    apply evalNTMCNF_of_mem sigma
      (ntmCopySymbolClauses [ntmNeg cvar] oldVar newVar) _
      h
    cases a <;>
      simp [ntmCopySymbolClauses, ntmAlphabet]
  have hbackward :
      evalNTMClause sigma
        ([ntmNeg cvar] ++
          [ntmPos (oldVar a), ntmNeg (newVar a)]) = true := by
    apply evalNTMCNF_of_mem sigma
      (ntmCopySymbolClauses [ntmNeg cvar] oldVar newVar) _
      h
    cases a <;>
      simp [ntmCopySymbolClauses, ntmAlphabet]
  have hf :
      evalNTMClause sigma
        [ntmNeg (oldVar a), ntmPos (newVar a)] = true :=
    evalNTMClause_neg_prefix_true sigma cvar _
      (by simpa using hforward) hc
  have hb :
      evalNTMClause sigma
        [ntmPos (oldVar a), ntmNeg (newVar a)] = true :=
    evalNTMClause_neg_prefix_true sigma cvar _
      (by simpa using hbackward) hc
  cases hold : sigma (oldVar a) <;>
    cases hnew : sigma (newVar a) <;>
    simp [evalNTMClause, evalNTMLiteral, ntmNeg, ntmPos,
      hold, hnew] at hf hb ⊢

theorem stay_copyLeft_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry :
      Nat × (Fin (M.stateCount + 1) × Option Bool × Direction))
    (sigma : Assignment)
    (hEff :
      evalNTMCNF sigma
        (ntmChoiceEffectCNF M x t s q a entry) = true)
    (hStay : entry.2.2.2 = Direction.stay)
    (i : Nat) (hi : i < ntmRadius x t) :
    evalNTMCNF sigma
      (ntmCopySymbolClauses
        [ntmNeg (ntmChoiceVar M x t s q a entry.1)]
        (ntmLeftVar M x t s i)
        (ntmLeftVar M x t (s + 1) i)) = true := by
  rcases entry with ⟨j, qNext, write, d⟩
  simp at hStay
  subst d
  have h1 :=
    (evalNTMCNF_append sigma
      (ntmSetStateClauses
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M t (s + 1) qNext)
      (ntmSetSymbolClauses
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        (ntmHeadVar M t (s + 1)) write ++
       ntmCopyLeftAll
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t s ++
       ntmCopyRightAll
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t s)).mp
      (by simpa [ntmChoiceEffectCNF, ntmStayEffectCNF,
        List.append_assoc] using hEff)
  have h2 :=
    (evalNTMCNF_append sigma
      (ntmSetSymbolClauses
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        (ntmHeadVar M t (s + 1)) write)
      (ntmCopyLeftAll
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t s ++
       ntmCopyRightAll
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t s)).mp
      (by simpa [List.append_assoc] using h1.2)
  have h3 :=
    (evalNTMCNF_append sigma
      (ntmCopyLeftAll
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t s)
      (ntmCopyRightAll
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t s)).mp h2.2
  exact (evalNTMCNF_flatMap_range sigma (ntmRadius x t)
    (fun r =>
      ntmCopySymbolClauses
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        (ntmLeftVar M x t s r)
        (ntmLeftVar M x t (s + 1) r))).mp
      (by simpa [ntmCopyLeftAll] using h3.1) i hi

theorem stay_copyRight_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry :
      Nat × (Fin (M.stateCount + 1) × Option Bool × Direction))
    (sigma : Assignment)
    (hEff :
      evalNTMCNF sigma
        (ntmChoiceEffectCNF M x t s q a entry) = true)
    (hStay : entry.2.2.2 = Direction.stay)
    (i : Nat) (hi : i < ntmRadius x t) :
    evalNTMCNF sigma
      (ntmCopySymbolClauses
        [ntmNeg (ntmChoiceVar M x t s q a entry.1)]
        (ntmRightVar M x t s i)
        (ntmRightVar M x t (s + 1) i)) = true := by
  rcases entry with ⟨j, qNext, write, d⟩
  simp at hStay
  subst d
  have h1 :=
    (evalNTMCNF_append sigma
      (ntmSetStateClauses
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M t (s + 1) qNext)
      (ntmSetSymbolClauses
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        (ntmHeadVar M t (s + 1)) write ++
       ntmCopyLeftAll
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t s ++
       ntmCopyRightAll
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t s)).mp
      (by simpa [ntmChoiceEffectCNF, ntmStayEffectCNF,
        List.append_assoc] using hEff)
  have h2 :=
    (evalNTMCNF_append sigma
      (ntmSetSymbolClauses
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        (ntmHeadVar M t (s + 1)) write)
      (ntmCopyLeftAll
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t s ++
       ntmCopyRightAll
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t s)).mp
      (by simpa [List.append_assoc] using h1.2)
  have h3 :=
    (evalNTMCNF_append sigma
      (ntmCopyLeftAll
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t s)
      (ntmCopyRightAll
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t s)).mp h2.2
  exact (evalNTMCNF_flatMap_range sigma (ntmRadius x t)
    (fun r =>
      ntmCopySymbolClauses
        [ntmNeg (ntmChoiceVar M x t s q a j)]
        (ntmRightVar M x t s r)
        (ntmRightVar M x t (s + 1) r))).mp
      (by simpa [ntmCopyRightAll] using h3.2) i hi

theorem ntmStay_left_copy_exact
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Fin (M.machine.transition q a).length)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hActive :
      M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hj : sigma (ntmChoiceVar M x t s q a j.val) = true)
    (hStay :
      ((M.machine.transition q a).get j).2.2 = Direction.stay)
    (i : Nat) (hi : i < ntmRadius x t) :
    forall b : Option Bool,
      sigma (ntmLeftVar M x t (s + 1) i b) =
        sigma (ntmLeftVar M x t s i b) := by
  have hStep := boundedExec_transitionStep_sat M x t s sigma hSat hs
  have hCase := transitionStep_case_sat M x t s q a sigma hStep
  have hActiveSat := activeChoice_sat M x t s q a sigma hCase hActive
  have hEffects := activeChoice_choiceEffects_sat M x t s q a sigma hActiveSat
  have hmemIndexed :
      (j.val, (M.machine.transition q a).get j) ∈
        ntmIndexedTransitions (M.machine.transition q a) := by
    rcases indexedTransitions_index_mem
      (M.machine.transition q a) j.val j.isLt with ⟨tr, hmem⟩
    have htr : tr = (M.machine.transition q a).get j := by
      unfold ntmIndexedTransitions at hmem
      generalize hstart : 0 = start at hmem
      subst start
      induction hts : M.machine.transition q a generalizing j.val tr with
      | nil => simp at j
      | cons hd tl ih =>
          cases j with
          | mk j hjlt =>
            cases j with
            | zero =>
                simp [ntmIndexedTransitionsAux] at hmem
                rcases hmem with h | h
                · simpa using congrArg Prod.snd h
                · omega
            | succ k =>
                simp [ntmIndexedTransitionsAux] at hmem
                rcases hmem with h | h
                · omega
                · have hk : k < tl.length := by simpa using hjlt
                  let jk : Fin tl.length := ⟨k, hk⟩
                  have ih' := ih (j := jk) (tr := tr) h
                  simpa using ih'
    simpa [htr] using hmem
  have hEff :
      evalNTMCNF sigma
        (ntmChoiceEffectCNF M x t s q a
          (j.val, (M.machine.transition q a).get j)) = true :=
    (evalNTMCNF_flatMap_list sigma
      (ntmIndexedTransitions (M.machine.transition q a))
      (fun p => ntmChoiceEffectCNF M x t s q a p)).mp
      hEffects _ hmemIndexed
  have hCopy :=
    stay_copyLeft_sat M x t s q a
      (j.val, (M.machine.transition q a).get j)
      sigma hEff hStay i hi
  exact eval_copySymbol_neg_guard_of_choice_true
    sigma
    (ntmChoiceVar M x t s q a j.val)
    (ntmLeftVar M x t s i)
    (ntmLeftVar M x t (s + 1) i)
    hCopy hj

theorem ntmStay_right_copy_exact
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (j : Fin (M.machine.transition q a).length)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (hs : s < t)
    (hActive :
      M.machine.accepting q = false ∧ M.machine.rejecting q = false)
    (hj : sigma (ntmChoiceVar M x t s q a j.val) = true)
    (hStay :
      ((M.machine.transition q a).get j).2.2 = Direction.stay)
    (i : Nat) (hi : i < ntmRadius x t) :
    forall b : Option Bool,
      sigma (ntmRightVar M x t (s + 1) i b) =
        sigma (ntmRightVar M x t s i b) := by
  have hStep := boundedExec_transitionStep_sat M x t s sigma hSat hs
  have hCase := transitionStep_case_sat M x t s q a sigma hStep
  have hActiveSat := activeChoice_sat M x t s q a sigma hCase hActive
  have hEffects := activeChoice_choiceEffects_sat M x t s q a sigma hActiveSat
  have hmemIndexed :
      (j.val, (M.machine.transition q a).get j) ∈
        ntmIndexedTransitions (M.machine.transition q a) := by
    rcases indexedTransitions_index_mem
      (M.machine.transition q a) j.val j.isLt with ⟨tr, hmem⟩
    have htr : tr = (M.machine.transition q a).get j := by
      unfold ntmIndexedTransitions at hmem
      generalize hstart : 0 = start at hmem
      subst start
      induction hts : M.machine.transition q a generalizing j.val tr with
      | nil => simp at j
      | cons hd tl ih =>
          cases j with
          | mk j hjlt =>
            cases j with
            | zero =>
                simp [ntmIndexedTransitionsAux] at hmem
                rcases hmem with h | h
                · simpa using congrArg Prod.snd h
                · omega
            | succ k =>
                simp [ntmIndexedTransitionsAux] at hmem
                rcases hmem with h | h
                · omega
                · have hk : k < tl.length := by simpa using hjlt
                  let jk : Fin tl.length := ⟨k, hk⟩
                  have ih' := ih (j := jk) (tr := tr) h
                  simpa using ih'
    simpa [htr] using hmem
  have hEff :
      evalNTMCNF sigma
        (ntmChoiceEffectCNF M x t s q a
          (j.val, (M.machine.transition q a).get j)) = true :=
    (evalNTMCNF_flatMap_list sigma
      (ntmIndexedTransitions (M.machine.transition q a))
      (fun p => ntmChoiceEffectCNF M x t s q a p)).mp
      hEffects _ hmemIndexed
  have hCopy :=
    stay_copyRight_sat M x t s q a
      (j.val, (M.machine.transition q a).get j)
      sigma hEff hStay i hi
  exact eval_copySymbol_neg_guard_of_choice_true
    sigma
    (ntmChoiceVar M x t s q a j.val)
    (ntmRightVar M x t s i)
    (ntmRightVar M x t (s + 1) i)
    hCopy hj



theorem eval_setLeft_neg_guard_to_nil
    (M : PolyNTMCandidate) (x : BitString) (t s i : Nat)
    (cvar : Nat) (target : Option Bool)
    (sigma : Assignment)
    (h :
      evalNTMCNF sigma
        (ntmSetLeftCell [ntmNeg cvar] M x t s i target) = true)
    (hc : sigma cvar = true) :
    evalNTMCNF sigma (ntmSetLeftCell [] M x t s i target) = true := by
  exact eval_setSymbol_neg_guard_to_nil
    (ntmLeftVar M x t s i) cvar target sigma h hc

theorem eval_setRight_neg_guard_to_nil
    (M : PolyNTMCandidate) (x : BitString) (t s i : Nat)
    (cvar : Nat) (target : Option Bool)
    (sigma : Assignment)
    (h :
      evalNTMCNF sigma
        (ntmSetRightCell [ntmNeg cvar] M x t s i target) = true)
    (hc : sigma cvar = true) :
    evalNTMCNF sigma (ntmSetRightCell [] M x t s i target) = true := by
  exact eval_setSymbol_neg_guard_to_nil
    (ntmRightVar M x t s i) cvar target sigma h hc

theorem leftEffect_shiftedLeft_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry : Nat × (Fin (M.stateCount + 1) × Option Bool × Direction))
    (sigma : Assignment)
    (hEff : evalNTMCNF sigma (ntmChoiceEffectCNF M x t s q a entry) = true)
    (hDir : entry.2.2.2 = Direction.left)
    (i : Nat) (hi : i < ntmRadius x t - 1) :
    evalNTMCNF sigma
      (ntmCopyLeftCell
        [ntmNeg (ntmChoiceVar M x t s q a entry.1)]
        M x t s (i + 1) (s + 1) i) = true := by
  rcases entry with ⟨j, qNext, write, d⟩
  simp at hDir
  subst d
  have h1 :=
    (evalNTMCNF_append sigma
      (ntmSetStateClauses [ntmNeg (ntmChoiceVar M x t s q a j)]
        M t (s + 1) qNext)
      (ntmCopySymbolClauses [ntmNeg (ntmChoiceVar M x t s q a j)]
        (ntmLeftVar M x t s 0) (ntmHeadVar M t (s + 1)) ++
       (List.range (ntmRadius x t - 1)).flatMap (fun k =>
         ntmCopyLeftCell [ntmNeg (ntmChoiceVar M x t s q a j)]
           M x t s (k + 1) (s + 1) k) ++
       ntmSetLeftCell [ntmNeg (ntmChoiceVar M x t s q a j)]
         M x t (s + 1) (ntmRadius x t - 1) M.machine.blank ++
       ntmSetRightCell [ntmNeg (ntmChoiceVar M x t s q a j)]
         M x t (s + 1) 0 write ++
       (List.range (ntmRadius x t - 1)).flatMap (fun k =>
         ntmCopyRightCell [ntmNeg (ntmChoiceVar M x t s q a j)]
           M x t s k (s + 1) (k + 1)))).mp
      (by simpa [ntmChoiceEffectCNF, ntmLeftEffectCNF, List.append_assoc] using hEff)
  have h2 :=
    (evalNTMCNF_append sigma
      (ntmCopySymbolClauses [ntmNeg (ntmChoiceVar M x t s q a j)]
        (ntmLeftVar M x t s 0) (ntmHeadVar M t (s + 1)))
      ((List.range (ntmRadius x t - 1)).flatMap (fun k =>
         ntmCopyLeftCell [ntmNeg (ntmChoiceVar M x t s q a j)]
           M x t s (k + 1) (s + 1) k) ++
       ntmSetLeftCell [ntmNeg (ntmChoiceVar M x t s q a j)]
         M x t (s + 1) (ntmRadius x t - 1) M.machine.blank ++
       ntmSetRightCell [ntmNeg (ntmChoiceVar M x t s q a j)]
         M x t (s + 1) 0 write ++
       (List.range (ntmRadius x t - 1)).flatMap (fun k =>
         ntmCopyRightCell [ntmNeg (ntmChoiceVar M x t s q a j)]
           M x t s k (s + 1) (k + 1)))).mp
      (by simpa [List.append_assoc] using h1.2)
  have h3 :=
    (evalNTMCNF_append sigma
      ((List.range (ntmRadius x t - 1)).flatMap (fun k =>
         ntmCopyLeftCell [ntmNeg (ntmChoiceVar M x t s q a j)]
           M x t s (k + 1) (s + 1) k))
      (ntmSetLeftCell [ntmNeg (ntmChoiceVar M x t s q a j)]
         M x t (s + 1) (ntmRadius x t - 1) M.machine.blank ++
       ntmSetRightCell [ntmNeg (ntmChoiceVar M x t s q a j)]
         M x t (s + 1) 0 write ++
       (List.range (ntmRadius x t - 1)).flatMap (fun k =>
         ntmCopyRightCell [ntmNeg (ntmChoiceVar M x t s q a j)]
           M x t s k (s + 1) (k + 1)))).mp h2.2
  exact (evalNTMCNF_flatMap_range sigma (ntmRadius x t - 1)
    (fun k => ntmCopyLeftCell [ntmNeg (ntmChoiceVar M x t s q a j)]
      M x t s (k + 1) (s + 1) k)).mp h3.1 i hi

theorem leftEffect_blankLeft_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry : Nat × (Fin (M.stateCount + 1) × Option Bool × Direction))
    (sigma : Assignment)
    (hEff : evalNTMCNF sigma (ntmChoiceEffectCNF M x t s q a entry) = true)
    (hDir : entry.2.2.2 = Direction.left) :
    evalNTMCNF sigma
      (ntmSetLeftCell [ntmNeg (ntmChoiceVar M x t s q a entry.1)]
        M x t (s + 1) (ntmRadius x t - 1) M.machine.blank) = true := by
  rcases entry with ⟨j, qNext, write, d⟩
  simp at hDir
  subst d
  simp [ntmChoiceEffectCNF, ntmLeftEffectCNF,
    evalNTMCNF_append, List.append_assoc] at hEff
  exact hEff.2.2.1

theorem leftEffect_writeRight0_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry : Nat × (Fin (M.stateCount + 1) × Option Bool × Direction))
    (sigma : Assignment)
    (hEff : evalNTMCNF sigma (ntmChoiceEffectCNF M x t s q a entry) = true)
    (hDir : entry.2.2.2 = Direction.left) :
    evalNTMCNF sigma
      (ntmSetRightCell [ntmNeg (ntmChoiceVar M x t s q a entry.1)]
        M x t (s + 1) 0 entry.2.2.1) = true := by
  rcases entry with ⟨j, qNext, write, d⟩
  simp at hDir
  subst d
  simp [ntmChoiceEffectCNF, ntmLeftEffectCNF,
    evalNTMCNF_append, List.append_assoc] at hEff
  exact hEff.2.2.2.1


theorem leftEffect_shiftedRight_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry : Nat × (Fin (M.stateCount + 1) × Option Bool × Direction))
    (sigma : Assignment)
    (hEff : evalNTMCNF sigma (ntmChoiceEffectCNF M x t s q a entry) = true)
    (hDir : entry.2.2.2 = Direction.left)
    (i : Nat) (hi : i < ntmRadius x t - 1) :
    evalNTMCNF sigma
      (ntmCopyRightCell
        [ntmNeg (ntmChoiceVar M x t s q a entry.1)]
        M x t s i (s + 1) (i + 1)) = true := by
  rcases entry with ⟨j, qNext, write, d⟩
  simp at hDir
  subst d
  have h1 :=
    (evalNTMCNF_append sigma
      (ntmSetStateClauses [ntmNeg (ntmChoiceVar M x t s q a j)]
        M t (s + 1) qNext)
      (ntmCopySymbolClauses [ntmNeg (ntmChoiceVar M x t s q a j)]
        (ntmLeftVar M x t s 0) (ntmHeadVar M t (s + 1)) ++
       (List.range (ntmRadius x t - 1)).flatMap (fun k =>
         ntmCopyLeftCell [ntmNeg (ntmChoiceVar M x t s q a j)]
           M x t s (k + 1) (s + 1) k) ++
       ntmSetLeftCell [ntmNeg (ntmChoiceVar M x t s q a j)]
         M x t (s + 1) (ntmRadius x t - 1) M.machine.blank ++
       ntmSetRightCell [ntmNeg (ntmChoiceVar M x t s q a j)]
         M x t (s + 1) 0 write ++
       (List.range (ntmRadius x t - 1)).flatMap (fun k =>
         ntmCopyRightCell [ntmNeg (ntmChoiceVar M x t s q a j)]
           M x t s k (s + 1) (k + 1)))).mp
      (by simpa [ntmChoiceEffectCNF, ntmLeftEffectCNF, List.append_assoc] using hEff)
  have h2 := (evalNTMCNF_append sigma
      (ntmCopySymbolClauses [ntmNeg (ntmChoiceVar M x t s q a j)]
        (ntmLeftVar M x t s 0) (ntmHeadVar M t (s + 1)))
      ((List.range (ntmRadius x t - 1)).flatMap (fun k =>
         ntmCopyLeftCell [ntmNeg (ntmChoiceVar M x t s q a j)]
           M x t s (k + 1) (s + 1) k) ++
       ntmSetLeftCell [ntmNeg (ntmChoiceVar M x t s q a j)]
         M x t (s + 1) (ntmRadius x t - 1) M.machine.blank ++
       ntmSetRightCell [ntmNeg (ntmChoiceVar M x t s q a j)]
         M x t (s + 1) 0 write ++
       (List.range (ntmRadius x t - 1)).flatMap (fun k =>
         ntmCopyRightCell [ntmNeg (ntmChoiceVar M x t s q a j)]
           M x t s k (s + 1) (k + 1)))).mp
      (by simpa [List.append_assoc] using h1.2)
  have h3 := (evalNTMCNF_append sigma
      ((List.range (ntmRadius x t - 1)).flatMap (fun k =>
         ntmCopyLeftCell [ntmNeg (ntmChoiceVar M x t s q a j)]
           M x t s (k + 1) (s + 1) k))
      (ntmSetLeftCell [ntmNeg (ntmChoiceVar M x t s q a j)]
         M x t (s + 1) (ntmRadius x t - 1) M.machine.blank ++
       ntmSetRightCell [ntmNeg (ntmChoiceVar M x t s q a j)]
         M x t (s + 1) 0 write ++
       (List.range (ntmRadius x t - 1)).flatMap (fun k =>
         ntmCopyRightCell [ntmNeg (ntmChoiceVar M x t s q a j)]
           M x t s k (s + 1) (k + 1)))).mp h2.2
  have h4 := (evalNTMCNF_append sigma
      (ntmSetLeftCell [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t (s + 1) (ntmRadius x t - 1) M.machine.blank)
      (ntmSetRightCell [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t (s + 1) 0 write ++
       (List.range (ntmRadius x t - 1)).flatMap (fun k =>
         ntmCopyRightCell [ntmNeg (ntmChoiceVar M x t s q a j)]
           M x t s k (s + 1) (k + 1)))).mp h3.2
  have h5 := (evalNTMCNF_append sigma
      (ntmSetRightCell [ntmNeg (ntmChoiceVar M x t s q a j)]
        M x t (s + 1) 0 write)
      ((List.range (ntmRadius x t - 1)).flatMap (fun k =>
         ntmCopyRightCell [ntmNeg (ntmChoiceVar M x t s q a j)]
           M x t s k (s + 1) (k + 1)))).mp h4.2
  exact (evalNTMCNF_flatMap_range sigma (ntmRadius x t - 1)
    (fun k => ntmCopyRightCell [ntmNeg (ntmChoiceVar M x t s q a j)]
      M x t s k (s + 1) (k + 1))).mp h5.2 i hi

theorem rightEffect_writeLeft0_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry : Nat × (Fin (M.stateCount + 1) × Option Bool × Direction))
    (sigma : Assignment)
    (hEff : evalNTMCNF sigma (ntmChoiceEffectCNF M x t s q a entry) = true)
    (hDir : entry.2.2.2 = Direction.right) :
    evalNTMCNF sigma
      (ntmSetLeftCell [ntmNeg (ntmChoiceVar M x t s q a entry.1)]
        M x t (s + 1) 0 entry.2.2.1) = true := by
  rcases entry with ⟨j, qNext, write, d⟩
  simp at hDir
  subst d
  simp [ntmChoiceEffectCNF, ntmRightEffectCNF,
    evalNTMCNF_append, List.append_assoc] at hEff
  exact hEff.2.1

theorem rightEffect_shiftedLeft_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry : Nat × (Fin (M.stateCount + 1) × Option Bool × Direction))
    (sigma : Assignment)
    (hEff : evalNTMCNF sigma (ntmChoiceEffectCNF M x t s q a entry) = true)
    (hDir : entry.2.2.2 = Direction.right)
    (i : Nat) (hi : i < ntmRadius x t - 1) :
    evalNTMCNF sigma
      (ntmCopyLeftCell
        [ntmNeg (ntmChoiceVar M x t s q a entry.1)]
        M x t s i (s + 1) (i + 1)) = true := by
  rcases entry with ⟨j, qNext, write, d⟩
  simp at hDir
  subst d
  simp [ntmChoiceEffectCNF, ntmRightEffectCNF,
    evalNTMCNF_append, List.append_assoc] at hEff
  exact (evalNTMCNF_flatMap_range sigma (ntmRadius x t - 1)
    (fun k => ntmCopyLeftCell [ntmNeg (ntmChoiceVar M x t s q a j)]
      M x t s k (s + 1) (k + 1))).mp hEff.2.2.1 i hi

theorem rightEffect_shiftedRight_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry : Nat × (Fin (M.stateCount + 1) × Option Bool × Direction))
    (sigma : Assignment)
    (hEff : evalNTMCNF sigma (ntmChoiceEffectCNF M x t s q a entry) = true)
    (hDir : entry.2.2.2 = Direction.right)
    (i : Nat) (hi : i < ntmRadius x t - 1) :
    evalNTMCNF sigma
      (ntmCopyRightCell
        [ntmNeg (ntmChoiceVar M x t s q a entry.1)]
        M x t s (i + 1) (s + 1) i) = true := by
  rcases entry with ⟨j, qNext, write, d⟩
  simp at hDir
  subst d
  simp [ntmChoiceEffectCNF, ntmRightEffectCNF,
    evalNTMCNF_append, List.append_assoc] at hEff
  exact (evalNTMCNF_flatMap_range sigma (ntmRadius x t - 1)
    (fun k => ntmCopyRightCell [ntmNeg (ntmChoiceVar M x t s q a j)]
      M x t s (k + 1) (s + 1) k)).mp hEff.2.2.2.1 i hi

theorem rightEffect_blankRight_sat
    (M : PolyNTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (entry : Nat × (Fin (M.stateCount + 1) × Option Bool × Direction))
    (sigma : Assignment)
    (hEff : evalNTMCNF sigma (ntmChoiceEffectCNF M x t s q a entry) = true)
    (hDir : entry.2.2.2 = Direction.right) :
    evalNTMCNF sigma
      (ntmSetRightCell [ntmNeg (ntmChoiceVar M x t s q a entry.1)]
        M x t (s + 1) (ntmRadius x t - 1) M.machine.blank) = true := by
  rcases entry with ⟨j, qNext, write, d⟩
  simp at hDir
  subst d
  simp [ntmChoiceEffectCNF, ntmRightEffectCNF,
    evalNTMCNF_append, List.append_assoc] at hEff
  exact hEff.2.2.2.2


theorem boundedExec_initial_sat
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true) :
    evalNTMCNF sigma (ntmInitialCNF M x t) = true := by
  have h :=
    (evalNTMCNF_append sigma
      (ntmInitialCNF M x t)
      (ntmTransitionsCNF M x t ++ ntmFinalAcceptanceCNF M t)).mp
      (by simpa [boundedExecTableauCNF_NTM, List.append_assoc] using hSat)
  exact h.1

theorem ntmInitial_state_exact
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true) :
    forall q : Fin (M.stateCount + 1),
      sigma (ntmStateVar M t 0 q) = decide (q = M.machine.initial) := by
  have hInit := boundedExec_initial_sat M x t sigma hSat
  have hparts :=
    (evalNTMCNF_append sigma
      (ntmSetStateClauses [] M t 0 M.machine.initial)
      (ntmSetSymbolClauses [] (ntmHeadVar M t 0) (inputTape x).head ++
        (List.range (ntmRadius x t)).flatMap (fun i =>
          ntmSetLeftCell [] M x t 0 i
            ((inputTape x).left.getD i M.machine.blank)) ++
        (List.range (ntmRadius x t)).flatMap (fun i =>
          ntmSetRightCell [] M x t 0 i
            ((inputTape x).right.getD i M.machine.blank)))).mp
      (by simpa [ntmInitialCNF, List.append_assoc] using hInit)
  exact (eval_ntmSetStateClauses_nil_iff
    sigma M t 0 M.machine.initial).mp hparts.1

theorem ntmInitial_state_exists_unique
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true) :
    ∃! q : Fin (M.stateCount + 1),
      sigma (ntmStateVar M t 0 q) = true := by
  refine ⟨M.machine.initial, ?_, ?_⟩
  · simpa using
      ntmInitial_state_exact M x t sigma hSat M.machine.initial
  · intro q hq
    have hExact := ntmInitial_state_exact M x t sigma hSat q
    have hdec : decide (q = M.machine.initial) = true := by
      simpa [hq] using hExact.symm
    exact of_decide_eq_true hdec

theorem ntmInitial_head_exact
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true) :
    forall a : Option Bool,
      sigma (ntmHeadVar M t 0 a) =
        decide (a = (inputTape x).head) := by
  have hInit := boundedExec_initial_sat M x t sigma hSat
  have h1 :=
    (evalNTMCNF_append sigma
      (ntmSetStateClauses [] M t 0 M.machine.initial)
      (ntmSetSymbolClauses [] (ntmHeadVar M t 0) (inputTape x).head ++
        (List.range (ntmRadius x t)).flatMap (fun i =>
          ntmSetLeftCell [] M x t 0 i
            ((inputTape x).left.getD i M.machine.blank)) ++
        (List.range (ntmRadius x t)).flatMap (fun i =>
          ntmSetRightCell [] M x t 0 i
            ((inputTape x).right.getD i M.machine.blank)))).mp
      (by simpa [ntmInitialCNF, List.append_assoc] using hInit)
  have h2 :=
    (evalNTMCNF_append sigma
      (ntmSetSymbolClauses [] (ntmHeadVar M t 0) (inputTape x).head)
      ((List.range (ntmRadius x t)).flatMap (fun i =>
        ntmSetLeftCell [] M x t 0 i
          ((inputTape x).left.getD i M.machine.blank)) ++
       (List.range (ntmRadius x t)).flatMap (fun i =>
        ntmSetRightCell [] M x t 0 i
          ((inputTape x).right.getD i M.machine.blank)))).mp
      (by simpa [List.append_assoc] using h1.2)
  exact (eval_ntmSetSymbolClauses_nil_iff
    sigma (ntmHeadVar M t 0) (inputTape x).head).mp h2.1

theorem ntmInitial_head_exists_unique
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true) :
    ∃! a : Option Bool,
      sigma (ntmHeadVar M t 0 a) = true := by
  refine ⟨(inputTape x).head, ?_, ?_⟩
  · simpa using
      ntmInitial_head_exact M x t sigma hSat (inputTape x).head
  · intro a ha
    have hExact := ntmInitial_head_exact M x t sigma hSat a
    have hdec : decide (a = (inputTape x).head) = true := by
      simpa [ha] using hExact.symm
    exact of_decide_eq_true hdec

theorem ntmInitial_left_exact
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (i : Nat) (hi : i < ntmRadius x t) :
    forall b : Option Bool,
      sigma (ntmLeftVar M x t 0 i b) =
        decide (b = (inputTape x).left.getD i M.machine.blank) := by
  have hInit := boundedExec_initial_sat M x t sigma hSat
  have h1 :=
    (evalNTMCNF_append sigma
      (ntmSetStateClauses [] M t 0 M.machine.initial)
      (ntmSetSymbolClauses [] (ntmHeadVar M t 0) (inputTape x).head ++
        (List.range (ntmRadius x t)).flatMap (fun j =>
          ntmSetLeftCell [] M x t 0 j
            ((inputTape x).left.getD j M.machine.blank)) ++
        (List.range (ntmRadius x t)).flatMap (fun j =>
          ntmSetRightCell [] M x t 0 j
            ((inputTape x).right.getD j M.machine.blank)))).mp
      (by simpa [ntmInitialCNF, List.append_assoc] using hInit)
  have h2 :=
    (evalNTMCNF_append sigma
      (ntmSetSymbolClauses [] (ntmHeadVar M t 0) (inputTape x).head)
      ((List.range (ntmRadius x t)).flatMap (fun j =>
        ntmSetLeftCell [] M x t 0 j
          ((inputTape x).left.getD j M.machine.blank)) ++
       (List.range (ntmRadius x t)).flatMap (fun j =>
        ntmSetRightCell [] M x t 0 j
          ((inputTape x).right.getD j M.machine.blank)))).mp
      (by simpa [List.append_assoc] using h1.2)
  have h3 :=
    (evalNTMCNF_append sigma
      ((List.range (ntmRadius x t)).flatMap (fun j =>
        ntmSetLeftCell [] M x t 0 j
          ((inputTape x).left.getD j M.machine.blank)))
      ((List.range (ntmRadius x t)).flatMap (fun j =>
        ntmSetRightCell [] M x t 0 j
          ((inputTape x).right.getD j M.machine.blank)))).mp h2.2
  have hiSat :=
    (evalNTMCNF_flatMap_range sigma (ntmRadius x t)
      (fun j => ntmSetLeftCell [] M x t 0 j
        ((inputTape x).left.getD j M.machine.blank))).mp h3.1 i hi
  exact (eval_ntmSetLeftCell_nil_iff M x t sigma i
    ((inputTape x).left.getD i M.machine.blank)).mp hiSat

theorem ntmInitial_left_exists_unique
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (i : Nat) (hi : i < ntmRadius x t) :
    ∃! b : Option Bool,
      sigma (ntmLeftVar M x t 0 i b) = true := by
  let target := (inputTape x).left.getD i M.machine.blank
  refine ⟨target, ?_, ?_⟩
  · simpa [target] using
      ntmInitial_left_exact M x t sigma hSat i hi target
  · intro b hb
    have hExact := ntmInitial_left_exact M x t sigma hSat i hi b
    have hdec : decide (b = target) = true := by
      simpa [target, hb] using hExact.symm
    exact of_decide_eq_true hdec

theorem ntmInitial_right_exact
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (i : Nat) (hi : i < ntmRadius x t) :
    forall b : Option Bool,
      sigma (ntmRightVar M x t 0 i b) =
        decide (b = (inputTape x).right.getD i M.machine.blank) := by
  have hInit := boundedExec_initial_sat M x t sigma hSat
  have h1 :=
    (evalNTMCNF_append sigma
      (ntmSetStateClauses [] M t 0 M.machine.initial)
      (ntmSetSymbolClauses [] (ntmHeadVar M t 0) (inputTape x).head ++
        (List.range (ntmRadius x t)).flatMap (fun j =>
          ntmSetLeftCell [] M x t 0 j
            ((inputTape x).left.getD j M.machine.blank)) ++
        (List.range (ntmRadius x t)).flatMap (fun j =>
          ntmSetRightCell [] M x t 0 j
            ((inputTape x).right.getD j M.machine.blank)))).mp
      (by simpa [ntmInitialCNF, List.append_assoc] using hInit)
  have h2 :=
    (evalNTMCNF_append sigma
      (ntmSetSymbolClauses [] (ntmHeadVar M t 0) (inputTape x).head)
      ((List.range (ntmRadius x t)).flatMap (fun j =>
        ntmSetLeftCell [] M x t 0 j
          ((inputTape x).left.getD j M.machine.blank)) ++
       (List.range (ntmRadius x t)).flatMap (fun j =>
        ntmSetRightCell [] M x t 0 j
          ((inputTape x).right.getD j M.machine.blank)))).mp
      (by simpa [List.append_assoc] using h1.2)
  have h3 :=
    (evalNTMCNF_append sigma
      ((List.range (ntmRadius x t)).flatMap (fun j =>
        ntmSetLeftCell [] M x t 0 j
          ((inputTape x).left.getD j M.machine.blank)))
      ((List.range (ntmRadius x t)).flatMap (fun j =>
        ntmSetRightCell [] M x t 0 j
          ((inputTape x).right.getD j M.machine.blank)))).mp h2.2
  have hiSat :=
    (evalNTMCNF_flatMap_range sigma (ntmRadius x t)
      (fun j => ntmSetRightCell [] M x t 0 j
        ((inputTape x).right.getD j M.machine.blank))).mp h3.2 i hi
  exact (eval_ntmSetRightCell_nil_iff M x t sigma i
    ((inputTape x).right.getD i M.machine.blank)).mp hiSat

theorem ntmInitial_right_exists_unique
    (M : PolyNTMCandidate) (x : BitString) (t : Nat)
    (sigma : Assignment)
    (hSat : evalNTMCNF sigma (boundedExecTableauCNF_NTM M x t) = true)
    (i : Nat) (hi : i < ntmRadius x t) :
    ∃! b : Option Bool,
      sigma (ntmRightVar M x t 0 i b) = true := by
  let target := (inputTape x).right.getD i M.machine.blank
  refine ⟨target, ?_, ?_⟩
  · simpa [target] using
      ntmInitial_right_exact M x t sigma hSat i hi target
  · intro b hb
    have hExact := ntmInitial_right_exact M x t sigma hSat i hi b
    have hdec : decide (b = target) = true := by
      simpa [target, hb] using hExact.symm
    exact of_decide_eq_true hdec

end PNPNTMTableauEncoding
end Real
end MCore
