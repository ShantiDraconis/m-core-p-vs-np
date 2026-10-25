# P03 closure repair — 2026-10-25

Base: `19d2fb6bca6264ed3f8195810ef87f1d6ff2281d` (via `atk/winwin-missing-half-audit-20261024`).
Mathlib: `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

Rule: only proof bodies change. No `theorem`/`def` statement, import, or axiom is added, removed or edited.
Each repair below lists file, original lines, the Lean error, and the replacement.

| # | File | Original lines | Error (run) | Repair |
|---|---|---|---|---|
| 1 | `lean/MCore/Real/P02ComplementRunRealization.lean` | 233–234 | `rewrite failed, did not find instance of the pattern` (run 40137729328) | `DeclaredAccepts` is a definition; the accepting-state equation is exposed by type ascription, then rewritten |
| 2 | `lean/MCore/Real/P02ComplementRunRealization.lean` | 312–313 | `type mismatch` (run 40137729328) | `rw [← hx]` rewrote every `x`, including the one in `DeclaredAccepts candidate x`; the equation is now rewritten only inside the hypothesis from `complement_reduce_correct` |

## Result of run 40146581310 (commit `6aa11640`)

`P02ComplementRunRealization` and `P02ExactDiagonalFrontier` now compile. They are the modules that
`P02BehavioralAlignment` imports, and that module reached elaboration. The build of the full P03 closure then
stops at two modules that have never compiled on any branch:

| Module | Versions on all branches | Errors | Kind |
|---|---|---|---|
| `MCore.Real.SourceRecovery` (722 lines) | one (blob `7aaa5bd2`, 9 branches) | 17 | list-API drift (`List.drop_append_of_le` does not exist; each use needs a different core lemma), unsolved arithmetic goals, failed `apply` unifications |
| `MCore.Real.P02BehavioralAlignment` | one (blob `293072c1`, 11 branches) | 1 | ill-typed `def`: `DeclaredClockTotal M → BehavioralSelfAlignment M` omits the `hTotal` argument |

Downstream of them, still not compiled: `TableauTemplate`, `P03Lemmas`, `P02InvariantCore`, `P02OddSemanticRecurrence`,
`P02TableauDynamics` (which defines `R_M`), `P03RangeFailureFrontier`, `P03PerfectFlipDichotomy`.

## Decision

The repair of the module named in the request is complete and certified by the `certify` job. Repairing the
rest of the P03 closure is **not** continued. The P03 law `RangeFailureLaw` asks every total polynomial candidate
`M` to fail SAT somewhere on the range of its own complemented tableau map `R_M`. A candidate that knows its own
code (Kleene recursion) can read `x` back from the initial-configuration clauses of `R_M x`, check the
encoding, simulate itself on the shorter input `x`, and answer `¬ M(x)`. That is exactly `SAT(R_M x)`. Such a
candidate is a perfect flip, so `RangeFailureLaw` is expected to be **false**, independently of P vs NP. This
is a mathematical sketch, not a kernel proof. It needs a recursion theorem for the hardened machine model,
which the repository does not have. Under the instruction not to reopen old routes, the P03 route is recorded
as closed, not repaired further.
