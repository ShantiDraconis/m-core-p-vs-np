import MCore.Real.P02SameInputOnlyFrontier
import MCore.Real.P02CookLevinFromBoundedExec
import MCore.Real.P02BoundedComputationEncoding
import MCore.Real.P02CompilerHaltingCounterexample
import MCore.Real.P02ExtensionalCoreAfterCookLevin

namespace MCore
namespace Real
namespace P02SameInputLengthFirewall

open CanonicalFinalProof
open CanonicalCircuitBits
open P02BoundedComputationEncoding
open P02CookLevinFromBoundedExec
open P02KleeneBridge
open P02SameInputOnlyFrontier
open P02ExtensionalSameInputBridge
open P02ExtensionalCoreAfterCookLevin

/-- Every canonical circuit encoding contains at least its three-bit root tag. -/
theorem encodeCircuit_length_ge_three
    (phi : CircuitK1.Circuit) :
    3 <= (encodeCircuit phi).length := by
  cases phi <;> simp [encodeCircuit]
  all_goals omega

/-- CNF-to-circuit encoding grows at least linearly with the number of clauses. -/
theorem cnfCircuit_encoding_length_ge
    (f : CNF) :
    3 * (f.length + 1) <=
      (encodeCircuit (cnfCircuit f)).length := by
  induction f with
  | nil =>
      simp [cnfCircuit, encodeCircuit]
  | cons c cs ih =>
      have hc : 3 <= (encodeCircuit (clauseCircuit c)).length :=
        encodeCircuit_length_ge_three (clauseCircuit c)
      simp [cnfCircuit, encodeCircuit]
      omega

/-- The initial tableau already contains at least one left-cell block per
radius position, hence at least radius-many clauses. -/
theorem radius_le_initialCNF_length
    (M : PolyDTMCandidate)
    (x : BitString)
    (t : Nat) :
    radius x t <= (initialCNF M x t).length := by
  unfold initialCNF
  dsimp
  simp [setLeftCell, setSymbolClauses, alphabet]
  omega

/-- The complete tableau contains the initial tableau as a prefix. -/
theorem initialCNF_length_le_tableau
    (M : PolyDTMCandidate)
    (x : BitString)
    (t : Nat) :
    (initialCNF M x t).length <=
      (boundedExecTableauCNF M x t).length := by
  simp [boundedExecTableauCNF]

/-- A bounded-execution circuit encoding is strictly longer than the raw input
whose execution it encodes. -/
theorem boundedExecBits_strictly_longer
    (M : PolyDTMCandidate)
    (x : BitString)
    (t : Nat) :
    x.length < (boundedExecBits M x t).length := by
  have hr : x.length < radius x t := by
    simp [radius]
  have hi : radius x t <= (initialCNF M x t).length :=
    radius_le_initialCNF_length M x t
  have ht :
      (initialCNF M x t).length <=
        (boundedExecTableauCNF M x t).length :=
    initialCNF_length_le_tableau M x t
  have henc :=
    cnfCircuit_encoding_length_ge (boundedExecTableauCNF M x t)
  unfold boundedExecBits boundedExecCircuit
  omega

/-- The rejection Cook-Levin instance can therefore never be literally the
same bitstring as its own source input. -/
theorem rejectCircuit_no_literal_same_input
    (M : PolyDTMCandidate)
    (x : BitString) :
    x ≠ encodeCircuit (rejectCircuit M x) := by
  intro h
  have hlen :
      x.length =
        (encodeCircuit (rejectCircuit M x)).length :=
    congrArg List.length h
  have hstrict :
      x.length <
        (encodeCircuit (rejectCircuit M x)).length := by
    unfold rejectCircuit
    exact boundedExecBits_strictly_longer
      (complementCandidate M) x (M.timeBound x.length)
  omega

/-- The current SameInputTransport contract has no inhabitant for any
effective compiler: Kleene supplies a semantic fixed point, but the demanded
literal SAT bitstring equality contradicts the strict encoding-length bound. -/
theorem no_sameInputTransport
    (M : PolyDTMCandidate)
    (K : EffectiveDiagonalCompiler M) :
    ¬ (Nonempty (SameInputTransport M K)) := by
  intro hS
  rcases hS with ⟨S⟩
  rcases kleene_fixed_point K with ⟨c, hfixed⟩
  have hsame :=
    S.same_input_of_fixed c hfixed
  exact rejectCircuit_no_literal_same_input M (S.selfInput c) hsame

/-- Consequently the current SameInputCore route is formally empty. -/
theorem sameInputCoreGap_false :
    ¬ SameInputCoreGap := by
  intro h
  rcases h with ⟨S⟩
  let M : PolyDTMCandidate := P02CompilerHaltingCounterexample.barrierCandidate
  exact
    no_sameInputTransport M (S.compiler M)
      ⟨S.transport M⟩


/-- The post-Cook-Levin extensional core is also impossible for the current
rejectCircuit carrier.  At an extensional fixed point, selfInput_ext and
compile_realizes force the forbidden literal equation
x = encodeCircuit (rejectCircuit M x). -/
theorem no_extensionalRejectCompilerCore
    (M : PolyDTMCandidate) :
    ¬ Nonempty (ExtensionalRejectCompilerCore M) := by
  intro h
  rcases h with ⟨E⟩
  let C : ExtensionalSameInputCompiler M := E.toCompiler
  rcases extensional_fixed_point C with ⟨c, hfixed⟩
  have hsame :
      E.selfInput c =
        encodeCircuit (rejectCircuit M (E.selfInput c)) := by
    have h := same_input_at_fixed_point C c hfixed
    simpa [C, ExtensionalRejectCompilerCore.toCompiler] using h
  exact rejectCircuit_no_literal_same_input M (E.selfInput c) hsame

/-- Therefore the uniform extensional core gap is empty, independently of the
compiler-halting barrier.  Any live G21 route must avoid literal equality
between the candidate input and the strictly larger Cook-Levin encoding. -/
theorem uniformExtensionalRejectCompilerCoreGap_false :
    ¬ UniformExtensionalRejectCompilerCoreGap := by
  intro h
  rcases h with ⟨U⟩
  exact no_extensionalRejectCompilerCore
    P02CompilerHaltingCounterexample.barrierCandidate
    ⟨U.core P02CompilerHaltingCounterexample.barrierCandidate⟩

#print axioms MCore.Real.P02SameInputLengthFirewall.encodeCircuit_length_ge_three
#print axioms MCore.Real.P02SameInputLengthFirewall.cnfCircuit_encoding_length_ge
#print axioms MCore.Real.P02SameInputLengthFirewall.radius_le_initialCNF_length
#print axioms MCore.Real.P02SameInputLengthFirewall.boundedExecBits_strictly_longer
#print axioms MCore.Real.P02SameInputLengthFirewall.rejectCircuit_no_literal_same_input
#print axioms MCore.Real.P02SameInputLengthFirewall.no_sameInputTransport
#print axioms MCore.Real.P02SameInputLengthFirewall.sameInputCoreGap_false

end P02SameInputLengthFirewall
end Real
end MCore
