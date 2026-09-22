# P01 HARD SCAFFOLD — GREEN / FROZEN / CERTIFIED

Repository: ShantiDraconis/m-core-p-vs-np
Source SHA: 9d6dd9575a61782c70137abff348356f805bc654
Branch source: attack/p01-hard-realization-20260922
Verified run: 35721236027 — ATK P01 HARD scaffold — SUCCESS

Classification:
- P01_HARD_SCAFFOLD = GREEN
- P01_HARD = OPEN

Scope:
This certificate freezes only the scaffold/interface layer that isolates the exact
P01MachineConstruction payload and its promotion theorem.

It does not assert an inhabitant of P01MachineConstruction.
It does not assert CanonicalSATMachineClosure without an input construction.
It does not promote P01 HARD to closed.
It does not promote FINAL_INTERNAL or FINAL_EXTERNAL.

Verified gate behavior:
- build succeeded
- source hygiene succeeded
- axiom audit gate succeeded
- endpoint firewall explicitly printed P01_HARD=OPEN

Freeze rule:
Only the GREEN scaffold is frozen and certified.
The OPEN endpoint is not frozen as a mathematical closure.
