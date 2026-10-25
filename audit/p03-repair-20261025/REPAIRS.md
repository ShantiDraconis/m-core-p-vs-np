# P03 closure repair — 2026-10-25

Base: `19d2fb6bca6264ed3f8195810ef87f1d6ff2281d` (via `atk/winwin-missing-half-audit-20261024`).
Mathlib: `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

Rule: only proof bodies change. No `theorem`/`def` statement, import, or axiom is added, removed or edited.
Each repair below lists file, original lines, the Lean error, and the replacement.

| # | File | Original lines | Error (run) | Repair |
|---|---|---|---|---|
| 1 | `lean/MCore/Real/P02ComplementRunRealization.lean` | 233–234 | `rewrite failed, did not find instance of the pattern` (run 40137729328) | `DeclaredAccepts` is a definition; the accepting-state equation is exposed by type ascription, then rewritten |
| 2 | `lean/MCore/Real/P02ComplementRunRealization.lean` | 312–313 | `type mismatch` (run 40137729328) | `rw [← hx]` rewrote every `x`, including the one in `DeclaredAccepts candidate x`; the equation is now rewritten only inside the hypothesis from `complement_reduce_correct` |
