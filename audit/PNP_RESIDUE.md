# P-vs-NP backward-dense residue

STATUS: **RESIDUE / NO TARGET_CERTIFICATE / NO MATHEMATICAL PROMOTION**

SOURCE LOCK: `6f310228a57984b33503a458f952207561c34c60`

## HYPOTHESIS_RESIDUE

1. The repository has only an abstract `ClassicalComplexityInterface`. It does not formalize the official Turing-machine definitions of P and NP or prove a semantics-preserving adapter from those definitions to `inP`/`inNP`.
2. `SeparationWitnessData` is a valid conditional interface, but existence of witness data for the fixed official model is not proved.
3. The C12 finite distribution does not prove the universal/asymptotic `C12QuantitativeFrontier` and does not provide a transfer theorem to fixed K10 witness data.

## QUANTIFIER_RESIDUE

The current K10 open proposition is

`∃ (Language α Value : Type), Nonempty (SeparationWitnessData Language α Value)`.

That existential choice of `Language` is weaker than what the official endpoint requires. The classical problem fixes the computational model/language universe first; witness existence must then be proved inside that fixed model.

C12 tests finitely many sizes (`n=1..12`), finite seeds, and explicit restrictions. This cannot replace a universal or asymptotic quantifier.

## SCALING_RESIDUE

`costBits`, `BranchingCost = 2^costBits`, `stateRank`, and `Potential` are internally certified quantities. There is currently no theorem identifying the resulting recurrence/payoff with deterministic polynomial-time complexity, a superpolynomial lower bound, or a standard circuit complexity measure for the official endpoint.

## CONSTANT_RESIDUE

The certified C12 dataset uses `alpha = beta = 1`. There is no theorem showing robustness under weights, constants, encoding overhead, or polynomial simulation constants. No constant may be silently absorbed into an asymptotic claim.

## AXIOM_AUDIT

- Locked-source hygiene: GREEN in C12 run `35300196456` and main reproduction `35300295285`.
- No new `sorry`, `admit`, source-level `axiom`, or `constant` is permitted by the dense audit gate.
- `audit/repro_PNP.lean` prints axioms for the key K9/K10 wiring and the conditional endpoint compression.
- Any `sorryAx` in that reproduction is a hard failure.

## EXACT COMPRESSION

The endpoint can be reached conditionally from only:

`F1_OFFICIAL_MODEL_MATCH + F2_FIXED_K10_WITNESS_EXISTENCE -> FINAL_STATEMENT`.

The C12 research route factors as:

`F1_OFFICIAL_MODEL_MATCH + C12QuantitativeFrontier + OPEN_BRIDGE_C12_TO_FIXED_K10 -> FINAL_STATEMENT`.

Neither real frontier is discharged at the locked source SHA. Therefore the correct result of this backward pass is **RESIDUE**, not `TARGET_CERTIFICATE`.
