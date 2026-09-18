namespace Audit.SAT

def encodeNat : Nat → BitStr
  | 0 => [false]
  | n + 1 => true :: encodeNat n

def decodeNat : BitStr → Option (Nat × BitStr)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => do
      let (n, tail) ← decodeNat rest
      some (n + 1, tail)

theorem decodeNat_encodeNat_append (n : Nat) (tail : BitStr) :
    decodeNat (encodeNat n ++ tail) = some (n, tail) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [encodeNat, decodeNat, ih]

def encodeLiteral {n : Nat} (l : Literal n) : BitStr :=
  l.negated :: encodeNat l.var.val

def decodeLiteral (n : Nat) : BitStr → Option (Literal n × BitStr)
  | [] => none
  | neg :: rest => do
      let (k, tail) ← decodeNat rest
      if h : k < n then
        some ({ var := ⟨k, h⟩, negated := neg }, tail)
      else
        none

theorem decodeLiteral_encodeLiteral_append
    {n : Nat} (l : Literal n) (tail : BitStr) :
    decodeLiteral n (encodeLiteral l ++ tail) = some (l, tail) := by
  rcases l with ⟨v, neg⟩
  simp [encodeLiteral, decodeLiteral, decodeNat_encodeNat_append, v.isLt]

def encodeNList {α : Type} (enc : α → BitStr) : List α → BitStr
  | [] => []
  | x :: xs => enc x ++ encodeNList enc xs

def decodeN {α : Type}
    (dec : BitStr → Option (α × BitStr)) :
    Nat → BitStr → Option (List α × BitStr)
  | 0, bits => some ([], bits)
  | n + 1, bits => do
      let (x, rest) ← dec bits
      let (xs, tail) ← decodeN dec n rest
      some (x :: xs, tail)

theorem decodeN_encodeNList_append
    {α : Type}
    (enc : α → BitStr)
    (dec : BitStr → Option (α × BitStr))
    (hround : ∀ x tail, dec (enc x ++ tail) = some (x, tail))
    (xs : List α) (tail : BitStr) :
    decodeN dec xs.length (encodeNList enc xs ++ tail) =
      some (xs, tail) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [encodeNList, decodeN, List.append_assoc,
        hround x (encodeNList enc xs ++ tail), ih]

def encodeList {α : Type} (enc : α → BitStr) (xs : List α) : BitStr :=
  encodeNat xs.length ++ encodeNList enc xs

def decodeList {α : Type}
    (dec : BitStr → Option (α × BitStr))
    (bits : BitStr) : Option (List α × BitStr) := do
  let (n, rest) ← decodeNat bits
  decodeN dec n rest

theorem decodeList_encodeList_append
    {α : Type}
    (enc : α → BitStr)
    (dec : BitStr → Option (α × BitStr))
    (hround : ∀ x tail, dec (enc x ++ tail) = some (x, tail))
    (xs : List α) (tail : BitStr) :
    decodeList dec (encodeList enc xs ++ tail) =
      some (xs, tail) := by
  simp [encodeList, decodeList, List.append_assoc,
    decodeNat_encodeNat_append,
    decodeN_encodeNList_append enc dec hround xs tail]

def encodeClause {n : Nat} (c : Clause n) : BitStr :=
  encodeList encodeLiteral c

def decodeClause (n : Nat) (bits : BitStr) :
    Option (Clause n × BitStr) :=
  decodeList (decodeLiteral n) bits

theorem decodeClause_encodeClause_append
    {n : Nat} (c : Clause n) (tail : BitStr) :
    decodeClause n (encodeClause c ++ tail) = some (c, tail) := by
  exact decodeList_encodeList_append
    encodeLiteral (decodeLiteral n)
    (fun l t => decodeLiteral_encodeLiteral_append l t) c tail

def encodeCNF (φ : CNF) : BitStr :=
  encodeNat φ.nvars ++ encodeList encodeClause φ.clauses

def decodeCNF (bits : BitStr) : Option CNF := do
  let (n, rest) ← decodeNat bits
  let (clauses, tail) ← decodeList (decodeClause n) rest
  if tail.isEmpty then
    some { nvars := n, clauses := clauses }
  else
    none

theorem decodeCNF_encodeCNF (φ : CNF) :
    decodeCNF (encodeCNF φ) = some φ := by
  rcases φ with ⟨n, clauses⟩
  unfold encodeCNF decodeCNF
  rw [decodeNat_encodeNat_append]
  have hClause :
      ∀ c : Clause n, ∀ tail : BitStr,
        decodeClause n (encodeClause c ++ tail) = some (c, tail) := by
    intro c tail
    exact decodeClause_encodeClause_append c tail
  have hList :
      decodeList (decodeClause n) (encodeList encodeClause clauses) =
        some (clauses, []) := by
    unfold decodeList encodeList
    rw [decodeNat_encodeNat_append]
    exact
      decodeN_encodeNList_append
        (enc := encodeClause)
        (dec := decodeClause n)
        hClause clauses ([] : BitStr)
  rw [hList]
  simp

def concreteBitEncoding : BitEncoding :=
  { encode := encodeCNF
    decode := decodeCNF
    decode_encode := decodeCNF_encodeCNF }

theorem SATEncodingExistence_closed :
    SATEncodingExistence := by
  exact ⟨concreteBitEncoding⟩

def SATEncodingStatusClosed : String := "PROVED_INTERNAL"

#print axioms Audit.SAT.decodeNat_encodeNat_append
#print axioms Audit.SAT.decodeLiteral_encodeLiteral_append
#print axioms Audit.SAT.decodeN_encodeNList_append
#print axioms Audit.SAT.decodeCNF_encodeCNF
#print axioms Audit.SAT.SATEncodingExistence_closed

end Audit.SAT
