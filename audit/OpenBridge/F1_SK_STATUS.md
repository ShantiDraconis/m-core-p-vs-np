# P vs NP — F1 + C12 S/K research receipt

U-REF source: `ShantiDraconis/m-core-p-vs-np@0cc830beae500b5bfd20faa736eb6d749522b77f`

- Open-bridge run: `35393301371` / job `105756338481` — SUCCESS.
- 8⊃5 regression: `35393301349` — SUCCESS.
- No historical S1 file was modified.

## F1

The audit branch now contains an explicit Boolean-tape operational DTM/NTM model,
polynomial time bounds, the deterministic embedding into the nondeterministic
model, and a canonical `ClassicalComplexityInterface`.

Internal status: **PROVED_INTERNAL_CANONICAL_MODEL**.

External status: **EXTERNAL_CLASSICAL_PENDING_MATCH**.  No theorem currently
identifies this exact operational model with a separately formalized Cook/CMI
machine model.  Therefore this receipt does not promote the Clay endpoint.

Kernel footprints are restricted to `propext` and `Quot.sound`; no
`Classical.choice`, `sorryAx`, project axiom, `sorry`, or `admit`.

## C12 S/K calibration

The generated C12 + C13 matrix contains 1,774 rows. Re-evaluating the exact
payoff inequality with rational weights 1/2:1/2, 1:2, 2:1, 1/10:10,
10:1/10, and 1:1 produced **zero classification flips**.

This is finite robustness evidence only. It does not prove uniform robustness
or an asymptotic theorem.

S remains **OPEN_BRIDGE** because no theorem yet identifies the internal
`Potential` / `costBits` quantities with official polynomial-time TM
complexity or unrestricted circuit-size lower bounds.
