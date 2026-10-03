# Fail-Closed GREEN Gate

Configuration: `audit/green_gate_config.json`.

A lane may be promoted from `GREEN=false` to `GREEN=true` only when **all** gates below pass.

1. Frozen source provenance
   - Every SOURCE_BOUND_EXTERNAL_CLOSED dependency is pinned to an exact repository and commit SHA.
   - Any SHA change requires full re-audit.

2. Static Lean scan
   - No `axiom`, `sorry`, `admit`, or `opaque` in the lane's Lean files.
   - Administrative frontier names forbidden by the config must not appear as replacements for real material producers.

3. Explicit terminal certificate
   - The lane must contain `GreenCertificate.lean`.
   - It must expose `terminal_endpoint_closed`.
   - The theorem must close the actual terminal endpoint, not an architectural proxy.

4. Architecture audit
   - `lake env lean <lane>/ArchitectureAudit.lean` must succeed.
   - The audit must include the material bridge and downstream closure chain used by the terminal certificate.

5. Full build
   - `lake build MCore` must succeed.
   - Static source closure alone is not BUILD_VERIFIED.

6. Manifest promotion
   - Only after steps 1-5 pass:
     - `green = true`
     - `build = "VERIFIED"`
     - `materialGaps = 0`
     - record exact terminal theorem, proof commit, build commit/log, and frozen source refs.

7. External mathematical status
   - GREEN is a repository certification state only.
   - It does not by itself imply community acceptance, publication, or eligibility for a Clay prize.

## Current expected outcome

For P01-P06, RED `GreenCertificate.lean` templates now exist, but the gate must still fail because `terminal_endpoint_certified` is absent and `terminal_endpoint_closed = false`.

This failure is intentional and preserves the fail-closed invariant.
