import MCore.C12.Families

namespace MCore
namespace Real

open CircuitK1
open C12

/-- A propositional literal in the existing Circuit AST. -/
def IsLiteral : Circuit → Prop
  | .input _ => True
  | .not (.input _) => True
  | _ => False

/-- A clause is a literal, an OR-tree of clauses, or the empty clause `false`. -/
def IsClause : Circuit → Prop
  | .const false => True
  | .input _ => True
  | .not (.input _) => True
  | .or a b => IsClause a ∧ IsClause b
  | _ => False

/-- CNF is a clause, an AND-tree of CNFs, or an empty conjunction/empty clause. -/
def IsCNF : Circuit → Prop
  | .const true => True
  | .const false => True
  | .input _ => True
  | .not (.input _) => True
  | .or a b => IsClause (.or a b)
  | .and a b => IsCNF a ∧ IsCNF b
  | _ => False

@[simp] theorem isLiteral_input (i : Nat) :
    IsLiteral (.input i) := trivial

@[simp] theorem isLiteral_not_input (i : Nat) :
    IsLiteral (.not (.input i)) := trivial

@[simp] theorem emptyClause_isClause :
    IsClause (.const false) := trivial

@[simp] theorem emptyCNF_isCNF :
    IsCNF (.const true) := trivial

@[simp] theorem emptyClause_isCNF :
    IsCNF (.const false) := trivial

/-- Structural closure of clauses under disjunction. -/
theorem IsClause_or {a b : Circuit} (ha : IsClause a) (hb : IsClause b) :
    IsClause (.or a b) :=
  ⟨ha, hb⟩

/-- Structural closure of CNFs under conjunction. -/
theorem IsCNF_and {a b : Circuit} (ha : IsCNF a) (hb : IsCNF b) :
    IsCNF (.and a b) :=
  ⟨ha, hb⟩

/-- Every structural literal is also a clause. -/
theorem isLiteral_isClause {c : Circuit} (h : IsLiteral c) : IsClause c := by
  cases c with
  | input i => exact True.intro
  | const b => cases h
  | not c =>
      cases c with
      | input i => exact True.intro
      | const b => cases h
      | not c => cases h
      | and a b => cases h
      | or a b => cases h
  | and a b => cases h
  | or a b => cases h

/-- Every literal produced by C12.literalAt has literal shape. -/
theorem literalAt_isLiteral
    (nVars seed clauseIdx pos : Nat) :
    IsLiteral (C12.literalAt nVars seed clauseIdx pos) := by
  unfold C12.literalAt
  refine Decidable.byCases
    (p := (seed + clauseIdx + pos) % 2 = 0) ?_ ?_
  · intro h
    rw [if_pos h]
    exact True.intro
  · intro h
    rw [if_neg h]
    exact True.intro

/-- Every literal produced by C12.literalAt is structurally a clause. -/
theorem literalAt_isClause
    (nVars seed clauseIdx pos : Nat) :
    IsClause (C12.literalAt nVars seed clauseIdx pos) :=
  isLiteral_isClause (literalAt_isLiteral nVars seed clauseIdx pos)


/-- Folding disjunction over clauses preserves clause shape from a clause accumulator. -/
theorem foldl_or_preserves_isClause
    (xs : List Circuit) (acc : Circuit)
    (hacc : IsClause acc)
    (hxs : ∀ c ∈ xs, IsClause c) :
    IsClause (xs.foldl (fun a c => .or a c) acc) := by
  induction xs generalizing acc with
  | nil =>
      exact hacc
  | cons x xs ih =>
      have hx : IsClause x :=
        hxs x (List.Mem.head xs)
      have htail : ∀ c ∈ xs, IsClause c := by
        intro c hc
        exact hxs c (List.Mem.tail x hc)
      exact ih (.or acc x) (IsClause_or hacc hx) htail

/-- Every nonempty randomClause has clause shape. -/
theorem randomClause_isClause
    (nVars seed clauseIdx width : Nat)
    (hwidth : 0 < width) :
    IsClause (C12.randomClause nVars seed clauseIdx width) := by
  unfold C12.randomClause
  cases width with
  | zero =>
      cases Nat.not_lt_zero 0 hwidth
  | succ width =>
      have range_eq_zero_cons_map_succ :
          ∀ n : Nat,
            List.range n =
              match n with
              | 0 => []
              | Nat.succ m => 0 :: List.map Nat.succ (List.range m) := by
        intro n
        induction n with
        | zero => rfl
        | succ m ih =>
            unfold List.range
            unfold List.range.loop
            change
              List.reverse (List.range.loop m [m]) =
                0 :: List.map Nat.succ
                  (List.reverse (List.range.loop m []))
            induction m generalizing ih with
            | zero => rfl
            | succ k hm =>
                unfold List.range.loop
                rw [List.reverse_cons, List.reverse_cons]
                change
                  List.reverse (List.range.loop k [k, Nat.succ k]) =
                    0 :: List.map Nat.succ
                      (List.reverse (List.range.loop k [k]))
                exact hm ih
      have h_range :
          List.range (Nat.succ width) =
            0 :: List.map Nat.succ (List.range width) := by
        exact range_eq_zero_cons_map_succ (Nat.succ width)
      have h_tail :
          List.map (C12.literalAt nVars seed clauseIdx)
              (List.map Nat.succ (List.range width)) =
            List.map
              (fun i => C12.literalAt nVars seed clauseIdx (Nat.succ i))
              (List.range width) := by
        induction List.range width with
        | nil => rfl
        | cons i is ih_tail =>
            rw [List.map_cons, List.map_cons, List.map_cons]
            rw [ih_tail]
      have h_map :
          List.map (C12.literalAt nVars seed clauseIdx)
              (List.range (Nat.succ width)) =
            C12.literalAt nVars seed clauseIdx 0 ::
              List.map
                (fun i => C12.literalAt nVars seed clauseIdx (Nat.succ i))
                (List.range width) := by
        rw [h_range]
        have h_cons :
            List.map (C12.literalAt nVars seed clauseIdx)
                (0 :: List.map Nat.succ (List.range width)) =
              C12.literalAt nVars seed clauseIdx 0 ::
                List.map (C12.literalAt nVars seed clauseIdx)
                  (List.map Nat.succ (List.range width)) := rfl
        rw [h_cons, h_tail]
      rw [h_map]
      have h_mem_tail :
          ∀ c ∈
            List.map
              (fun i => C12.literalAt nVars seed clauseIdx (Nat.succ i))
              (List.range width),
            IsClause c := by
        induction List.range width with
        | nil =>
            intro c hc
            cases hc
        | cons i is ih =>
            intro c hc
            cases hc with
            | head =>
                exact literalAt_isClause nVars seed clauseIdx (Nat.succ i)
            | tail _ hmem =>
                exact ih _ hmem
      exact foldl_or_preserves_isClause
        _ _
        (literalAt_isClause nVars seed clauseIdx 0)
        h_mem_tail

end Real
end MCore
