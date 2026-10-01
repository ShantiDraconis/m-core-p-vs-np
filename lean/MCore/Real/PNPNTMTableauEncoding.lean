
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

theorem boundedExecCircuit_NTM_isCNF
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) :
    IsCNF (boundedExecCircuit_NTM M x t) := by
  exact ntmCNFCircuit_isCNF _

end PNPNTMTableauEncoding
end Real
end MCore
