# Closed Cores — P versus NP Research Agenda

Status: SOURCE_CATALOG_ONLY / NO_MATHEMATICAL_PROMOTION  
Branch: audit/multistate-proof-refutation-v1  
P_NE_NP_PROVED = false  
P_EQ_NP_PROVED = false

## 1. Boolean discriminant

Define the structural proposition

D := NP ⊆ P.

Since P ⊆ NP, D is equivalent to P=NP. Under classical logic:

D ∨ ¬D

and D ∧ ¬D is impossible.

This is a dichotomy encoding, not a solution.

## 2. Gaussian two-channel encoding

Introduce Boolean channels R,I ∈ {0,1} and encode

z = R + i I,
N(z)=R²+I².

Then N(z)∈{0,1,2}.

If R and I are declared to encode mutually exclusive orientations, then
N(z)=2 is a semantic contradiction flag. The raw arithmetic identity
N(1+i)=2 alone is not a proof of inconsistency.

The Gaussian arithmetic side additionally gives:
3 is not representable as a²+b² with a,b∈Z.

Candidate article:
"The 0,1,2 Encoding for Complexity Dichotomies"

Classification:
DEFINITIONAL_FRAMEWORK + ELEMENTARY_ARITHMETIC.

## 3. Gaussian contradiction detector

Proposed machine-checkable invariant:

Exclusive(R,I) := ¬(R ∧ I).

Detector(R,I) := (R²+I² = 2).

Target theorem:

Exclusive(R,I) → ¬Detector(R,I).

Conversely, for Boolean R,I:

Detector(R,I) ↔ (R=true ∧ I=true).

This can be formalized in Lean without touching the actual P-vs-NP frontier.

## 4. Prime-indexed certificate layer

For finite-support d_p∈{0,1}, define

C(d)=∏_p p^(d_p).

This is a Gödel-style multiplicative encoding of the active coordinates.

Potential weighted form:

C_w(d)=∏_p p^(w_p d_p),

so 27=3³ can encode weight 3 at the p=3 coordinate.

This is encoding theory only. It does not prove a computational separation.

## 5. Quadratic-ring research

Candidate comparisons:

- Gaussian: a²+b²
- Eisenstein: a²-ab+b²
- cyclotomic: norm maps in Z[ζ_n]

Research question:
which ring/norm best preserves the desired finite status algebra while keeping
the encoding injective and machine-checkable?

No claim is made that Z[ζ_12] automatically realizes any prescribed prime
signature. That requires a theorem.

## 6. Real oriented closure A — polySAT witness

This is a genuine P=NP route.

Required object:
an algorithm A for SAT or 3-SAT such that

1. A is total on valid inputs;
2. A returns the correct satisfiability answer;
3. runtime(A,x) ≤ c |x|^k for fixed c,k;
4. correctness and time bound are formalized without hidden oracle assumptions.

Classification:
OPEN_CORE / CLAY_LEVEL.

No Boolean or number-theoretic encoding substitutes for these obligations.

## 7. Real oriented closure B — superpolynomial lower bound

This is a genuine P≠NP route.

Required object:
a language L∈NP and a proof L∉P, or an equivalent unconditional separation.

Any proposed proof must be audited against at least:
- relativization,
- natural-proofs style barriers where relevant,
- algebrization,
- uniform/nonuniform mismatch,
- hidden advice/oracle assumptions,
- quantifier mismatch in lower-bound statements.

Classification:
OPEN_CORE / CLAY_LEVEL.

## 8. Riemann bridge

Proposed bridge:

RH ⇒ P ≠ NP.

Status:
OPEN_BRIDGE / NO KNOWN PROOF IN THIS REPOSITORY.

A valid route would require a theorem converting arithmetic information about
zeta zeros into a lower bound for a specified computational model. Mere
correlation, spectral analogy, or zero statistics are insufficient.

## 9. Lean certificate library

Safe formalization targets now:

- Boolean dichotomy identities;
- exclusive-channel contradiction detector;
- Gaussian norm image for Boolean coordinates;
- finite prime-indexed Gödel encodings;
- injectivity under finite-support hypotheses;
- theorem-status enums and audit metadata;
- explicit statements of polySAT and lower-bound frontiers.

Unsafe promotion targets:

- declaring polySAT without an algorithm;
- encoding P≠NP as an axiom;
- using a norm calculation as a lower bound;
- turning empirical branching factors into asymptotic complexity theorems.

## 10. Publication roadmap

Draft titles:

1. The Boolean Discriminant for P versus NP — framework note
2. The 0,1,2 Encoding — elementary formal layer
3. Gaussian Contradiction Detection in Proof-State Encodings
4. Prime-Indexed Complexity Certificate Codes
5. Oriented Closure I: polySAT Witness — OPEN
6. Oriented Closure II: Lower Bounds Beyond Known Barriers — OPEN
7. Lean4 Certificate Library for Complexity Cores

Only 1–4 and parts of 7 are presently framework/formalization projects.
5–6 are the actual unresolved mathematical frontiers.
