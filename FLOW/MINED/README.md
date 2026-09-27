# MINED flow

Normalized observations extracted from repository evidence.

Every record should use:
`repo | sha | run_id | theorem | exact_type | state | error_class | error_signature | axioms | sorryAx | dependencies | hypothetical | terminal_effect`.

Deduplication key:
`error_class + error_signature + exact_type`.

Only repeated REAL patterns may become production rules. HYPOTHETICAL evidence may propose experiments, never proof rules.
