# Automatic Pattern Formalization Pipeline

Status: FAIL_CLOSED / NO_SORRY

Purpose: whenever a detector reports a previously unknown mathematical pattern,
create a Lean file immediately and classify it by kernel verification.

Pipeline:

DISCOVERY
-> canonical pattern JSON
-> stable pattern_id
-> Lean source generation
-> proof attempt
-> lake/Lean kernel check
-> FORMALIZED or OPEN_MATH
-> evidence registry
-> optional explicit transfer theorem
-> FINAL_PROOF producer

## Two legal outcomes

### FORMALIZED

A theorem is emitted only when the generated proposition is in a supported,
decidable fragment and Lean accepts the proof with no sorry/admit/new axiom.

### OPEN_MATH

The same mathematical statement is still translated into Lean as a named
definition of type Prop, but no theorem claiming the proposition is emitted.
This is a complete formalization of the conjecture, not a proof.

## Never allowed

- generate `axiom pattern : P`;
- generate `theorem pattern : P := by sorry`;
- infer an asymptotic theorem from finite samples;
- promote a geometric/P012 label into G21/P01;
- let nucleusTag affect standard SAT or CorrectAt semantics;
- mark a theorem FORMALIZED only from a numerical fit.

## Supported auto-proof fragment

The first implementation accepts finite exact arithmetic claims:
- natural/integer equality;
- natural/integer inequalities;
- primality of a concrete natural;
- concrete divisibility/non-divisibility;
- concrete Horizon-Prime boundary/gap facts already reducible by computation.

General quantified conjectures are emitted as OPEN_MATH unless a separately
registered proof strategy proves them.

## Promotion

Even a FORMALIZED research theorem has proof_credit=0 by default.
It receives FINAL_PROOF credit only through a kernel-checked bridge into an
existing producer such as G21Pointwise or P01ConstructionGap.
