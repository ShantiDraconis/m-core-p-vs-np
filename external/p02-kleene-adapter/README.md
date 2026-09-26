# P02 Kleene adapter experiment

Isolated external lane for testing whether Mathlib's formalized recursion
theorems can reduce the P02 semantic self-embedding frontier.

Upstream:
- repository: https://github.com/leanprover-community/mathlib4
- module: Mathlib/Computability/PartrecCode.lean
- pin: v4.19.0
- license: Apache-2.0

This directory is deliberately outside the root MCore build. It does not alter
or certify the existing GREEN P01/P02 artifacts. Promotion requires a separate
adapter into MCore's PolyDTMCandidate/BitString model plus its own kernel gate.

No claim of P != NP is made by this experiment.
