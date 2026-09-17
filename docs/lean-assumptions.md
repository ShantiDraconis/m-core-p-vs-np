# Lean assumptions and proof-engineering rules

This file records elaborator/tactic assumptions discovered by RED runs. It is a proof-engineering audit log, not a list of mathematical axioms.

## C1 — `Option Bool` restrictions

For `ρ : Nat → Option Bool`, simplification of an expression containing `ρ i` must not be assumed to split the `Option` automatically. Proofs whose result depends on whether an input is fixed must explicitly perform `cases h : ρ i` (or use a helper that performs the equivalent split).

Adversarial regression: both `none` and `some b` input cases must compile for every structural restriction theorem.

## C1 — `simp` and `propext`

Lean proofs implemented with `simp` may report dependency on the standard `propext` axiom under `#print axioms`. Therefore CI must distinguish:

- forbidden project axioms / `sorry` / `admit`: fail closed;
- standard Lean `propext` introduced by simplification: explicitly allowed and recorded;
- unexpected additional axioms: fail.

An axiom audit must compare the exact reported set rather than assuming that every proved theorem has an empty `#print axioms` set.

## Rule for future C gates

Every new RED caused by elaboration, tactic behavior, coercion, case splitting, simplifier behavior, or axiom-audit semantics must add a reusable entry here and a named regression whenever practical.
