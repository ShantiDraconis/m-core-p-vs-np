# ATK MASTER — Consolidação literal das fontes verificadas

> Snapshot documental: inclui os conteúdos integrais das sete fontes abaixo. Não é um arquivo Lean compilável; arquivos JSON e Lean permanecem identificados por seção. A prova terminal não está certificada.

## ShantiDraconis/m-core-p-vs-np / GATE_LEDGER.json

Blob SHA: `dce43595b91271551d921e34af6dd5b798f88760`

```json
{
  "schema": "ATK_GATE_LEDGER_V2",
  "repo": "m-core-p-vs-np",
  "queue": "PNP",
  "hard_composite_remaining": 2,
  "hard_atomic_remaining": 2,
  "current_gate": "P01",
  "current_head": "969408f2d84121667319da04680893dd2978e9a6",
  "canonical_hard_base": {
    "state": "GREEN_FROZEN_REUSED",
    "branch": "frozen/material-orientation-green-969408f2",
    "sha": "969408f2d84121667319da04680893dd2978e9a6",
    "certificate_commit": "f14c2e1854d6b62dc3e5b567a6769a04075f76d5",
    "certified_scope": "material orientation kernel: genuine PolySAT route or LowerBoundWitness required"
  },
  "state_ci": "GREEN_PREFIX_REUSED",
  "state_math": "OPEN_MATH",
  "next": "P01: construct a fixed preserving unary-index witness reader for the sole remaining local evalStep input case; then lift the complete one-step refinement to global evalRun and compose parser+witness+verifier. G21Pointwise remains independently OPEN_MATH.",
  "progress_metric": "FROZEN_HARD/TOTAL_HARD",
  "tests_are_progress_metric": false,
  "frozen_prefix_decrements_hard": false,
  "direct_producer": {
    "state": "GREEN_TYPED_OPEN_MATH",
    "exactness": "EXACT_TWO_PRODUCER_CUT",
    "target": "P01ConstructionGap ∧ G21Pointwise",
    "source_repository": "ShantiDraconis/M-Core",
    "source_files": [
      "imports/pnp/b406b806/lean/MCore/Real/FinalExternalTwoGap.lean",
      "imports/pnp/c102d9d4/lean/MCore/Real/P02G21G22Attack.lean"
    ],
    "equivalences": [
      "G21Pointwise ↔ P02Target",
      "G21Pointwise ↔ G22Contradiction",
      "G22Contradiction ↔ ¬ InP SATTarget"
    ],
    "note": "G3 is already supplied by the normalized external contract; G2.2 is not an independent producer.",
    "inhabitant_state": "OPEN_MATH",
    "p01_internal_frontier": {
      "state": "GREEN_SUBGATES_OPEN_TERMINAL",
      "exact_target": "Nonempty P01MachineConstruction",
      "terminal_structure_fields": [
        "one fixed NTM over Option Bool",
        "blank_none",
        "polynomial time bound",
        "total HaltsWithin on every BitString",
        "AcceptsWithin ↔ SATBits circuitBitEncoding"
      ],
      "certified_reuse": {
        "parser": {
          "state": "GREEN_FROZEN_REUSE",
          "theorem": "slot_parser_machine_simulation_certificate"
        },
        "witness_guess": {
          "state": "GREEN",
          "branch": "atk/next-pnp-physical-verifier-20260929",
          "sha": "9ebd51f530786b146700e4c288ef30612ef34d5c",
          "run": 36499549795,
          "theorems": [
            "witnessGuess_complete",
            "witnessGuess_halts"
          ]
        },
        "indexed_witness_read": {
          "state": "GREEN",
          "branch": "atk/next-p01-integrated-machine-20260929",
          "sha": "575cd996e16eda4d9bc33bebd25df6b01f50aaa4",
          "runs": [
            36497448606,
            36497644415
          ],
          "theorem": "witnessIndexedReadGap_closed"
        },
        "one_machine_verifier_kernel": {
          "state": "GREEN_FRONTIER",
          "branch": "atk/next-pnp-one-machine-verifier-20260929",
          "sha": "3532d7af492eb2dfe50eb287d58abfa3b2dbb449",
          "run": 36500623426,
          "proved": [
            "fixed stack primitive TM push/pop",
            "source rewind / input shuttle infrastructure",
            "indexed witness read",
            "local physical const/neg/and/or refinements",
            "uniform polynomial cost envelopes"
          ]
        },
        "streaming_encoded_evaluator": {
          "state": "GREEN_FROZEN_REDUCTION",
          "branch": "frozen/p01-encoded-evaluator-green-62956cc7",
          "sha": "62956cc7760834d80bae27e5b928d06d92334a62",
          "run": 36508360906,
          "certificate": "CERTIFICATES/P01_ENCODED_EVALUATOR_GREEN_62956cc7.md",
          "theorems": [
            "evalEncodedCore_encode_append",
            "evalEncoded_encode",
            "evalEncoded_witness"
          ],
          "content": "direct evaluation of canonical prefix encoding with exact tail preservation; no Circuit value reconstructed in control"
        },
        "finite_frame_encoded_evaluator": {
          "state": "GREEN_FROZEN_REDUCTION",
          "branch": "frozen/p01-encoded-stack-evaluator-green-f70ab88b",
          "sha": "f70ab88b3ac8cb1bd37c5e6f3115e26184b39b2b",
          "run": 36508950379,
          "certificate": "CERTIFICATES/P01_ENCODED_STACK_EVALUATOR_GREEN_f70ab88b.md",
          "theorems": [
            "evalRun_encode_append",
            "evalStepCount_le_three_mul_encoding",
            "evalRun_encode_bounded"
          ],
          "content": "finite-frame small-step evaluator for canonical prefix bits; no Circuit AST in finite control; ≤3*encoding-length semantic control steps"
        },
        "eval_frame_tape": {
          "state": "GREEN_FROZEN_REDUCTION",
          "branch": "frozen/p01-frame-tape-green-eb5713e4",
          "sha": "eb5713e48e84a8adbb0850d1f2c60b46a738b4f6",
          "run": 36509233942,
          "certificate": "CERTIFICATES/P01_FRAME_TAPE_GREEN_eb5713e4.md",
          "content": "seven EvalFrame variants encoded injectively in fixed three-bit blocks; stack round-trip and 3*depth space bound kernel-checked"
        },
        "frame_push": {
          "state": "GREEN_FROZEN_PHYSICAL_SUBROUTINE",
          "branch": "frozen/p01-frame-push-green-12380362",
          "sha": "123803627c2157d41686471dc8c2c5c96eb408ae",
          "run": 36509879658,
          "certificate": "CERTIFICATES/P01_FRAME_PUSH_GREEN_12380362.md",
          "content": "one fixed TM writes exactly one three-bit EvalFrame code and preserves the V2 stack layout"
        },
        "frame_pop_read": {
          "state": "GREEN_FROZEN_PHYSICAL_SUBROUTINE",
          "branch": "frozen/p01-frame-pop-read-green-7f6597a1",
          "sha": "7f6597a14f0fcdfd7ee53edb880dd797748d5646",
          "run": 36540846559,
          "certificate": "CERTIFICATES/P01_FRAME_POP_READ_GREEN_7f6597a1.md",
          "content": "one fixed TM decodes/removes one three-bit EvalFrame in four physical steps, preserving canonical V2 layout and rejecting 111"
        },
        "evalstep_frame_refinement": {
          "state": "GREEN_FROZEN_PHYSICAL_REFINEMENT",
          "branch": "frozen/p01-evalstep-frame-refinement-green-8e3abccc",
          "sha": "8e3abccc052e631346f9decbf4db0c601080fde6",
          "run": 36542400193,
          "certificate": "CERTIFICATES/P01_EVALSTEP_FRAME_REFINEMENT_GREEN_8e3abccc.md",
          "proved": [
            "frame push refinement",
            "frame pop/read refinement",
            "NOT/AND/OR tag frame effects",
            "NOT return",
            "AND-left/OR-left pop→push continuation replacement",
            "AND-right/OR-right return"
          ]
        },
        "deterministic_tm_ntm_transport": {
          "state": "GREEN_FROZEN_REDUCTION",
          "branch": "frozen/p01-tm-ntm-transport-green-833fe0de",
          "sha": "833fe0ded9676bfd19d226b8bf1dfd0aeb070bf5",
          "runs": [
            36547692311,
            36547692227
          ],
          "theorems": [
            "tmAsNTM_successors_of_not_halted",
            "tmAsNTM_terminal_iff_halted",
            "runBranches_tmAsNTM_singleton",
            "tmHaltsWithin_iff_ntmHaltsWithin",
            "tmAsNTM_acceptsWithin_iff"
          ],
          "content": "deterministic TM phases embed as singleton-branch NTMs with full run, halting, and acceptance preservation"
        },
        "eval_cursor_roundtrip": {
          "state": "GREEN_FROZEN_PHYSICAL_REDUCTION",
          "branch": "atk/p01-eval-cursor-roundtrip-20260929",
          "sha": "1054b6bac5962d81f5c33a2b87d68f21b00d5ce0",
          "runs": [
            36544552231,
            36544552207
          ],
          "content": "fixed cursor seek+return roundtrip preserves witness/frame data and advances consumed cursor physically"
        },
        "source_to_stack": {
          "state": "GREEN_PHYSICAL_REFINEMENT",
          "branch": "atk/next-p01-source-consumption-20260929",
          "sha": "adb6db8d1943778655f63d651ed93f23f425ed47",
          "runs": [
            36545146201,
            36545146259
          ],
          "content": "source-to-stack tape refinement and cursor return kernel are GREEN"
        },
        "tag_input_consumption": {
          "state": "GREEN_PHYSICAL_REFINEMENT",
          "branch": "atk/next-p01-tag-input-consumption-20260929",
          "sha": "4eb4051ff330368627a3f30f2e080a00bd96f37d",
          "runs": [
            36547475406,
            36547475211
          ],
          "theorems": [
            "consumeOneTape_correct",
            "consumeThreeTape_correct"
          ],
          "content": "fixed cursor macros consume exactly one or three unread source bits while preserving witness and frame stack"
        },
        "frame_pop_v2": {
          "state": "GREEN_PHYSICAL_SUBROUTINE",
          "branch": "atk/next-p01-integrated-machine-v2-20260929",
          "sha": "8c40d7fa129d045810123886ed6c0bb96e034300",
          "runs": [
            36548367025,
            36548367093,
            36548367026
          ],
          "theorem": "framePop_run_six",
          "content": "six-step physical frame-pop decodes exact EvalFrame and fails closed on empty/truncated stack"
        },
        "five_tag_cursor_refinement": {
          "state": "GREEN_FROZEN_PHYSICAL_REFINEMENT",
          "branch": "frozen/p01-five-tag-cursor-refinement-green-6707aa0e",
          "sha": "6707aa0e65781e9d5674414bbf6c930443531bba",
          "run": 36552792426,
          "certificate": "CERTIFICATES/P01_FIVE_TAG_CURSOR_REFINEMENT_GREEN_6707aa0e.md",
          "theorems": [
            "evalStep_const_false_cursor_refined",
            "evalStep_const_true_cursor_refined",
            "evalStep_not_tag_cursor_refined",
            "evalStep_and_tag_cursor_refined",
            "evalStep_or_tag_cursor_refined"
          ],
          "content": "all five finite three-bit eval tags consume source physically; NOT/AND/OR also push the exact continuation frame"
        }
      },
      "exact_remaining": [
        "construct fixed-control preserving unary indexed witness read for input tag 000; existing destructive reader is insufficient for repeated variable queries",
        "lift complete physical evalStep refinement to one global physical verifier run theorem against frozen evalRun semantics",
        "construct one fixed finite-control NTM composing parser + witness phase + physical verifier",
        "prove global HaltsWithin under one polynomial timeBound",
        "prove AcceptsWithin iff SATBits circuitBitEncoding for every bitstring"
      ],
      "rejected_substitutes": [
        "IntegratedPhaseBridgeCertificate state-disjointness",
        "DecoderEvaluatorLocalCertificate nonterminal-control shell",
        "component shells without one-machine global execution theorem"
      ]
    }
  },
  "p01_direct_frontier": {
    "state": "OPEN_IMPLEMENTATION_SINGLE_INTEGRATION_OBJECT",
    "exact_target": "Nonempty P01FinalCertificate.P01MachineConstruction",
    "already_closed": [
      "global canonical parser simulation",
      "witnessGuess_halts and witnessGuess_complete",
      "verified SAT witness relation",
      "physical const/neg/and/or stack transforms",
      "fixed-control indexed witness reader with polynomial halting/correctness",
      "fixed-control eval-frame push/pop machines",
      "polynomial physical-verifier budget",
      "deterministic parser/verifier TM phases embed into NTM with full run/halting/acceptance preservation",
      "physical eval cursor seek/return roundtrip",
      "physical one/three-bit source consumption preserving witness/frame layout",
      "cursor-aware frame push and V2 frame pop",
      "physical cursor refinement of all five finite three-bit tags: constants, NOT, AND, OR"
    ],
    "not_counted_as_closure": [
      "state-only phase bridges",
      "PhysicalStackRep reconstruction without machine execution",
      "branch frozen/p01-exact-integrated-producer-green-661e43e4 because it still contains P01MachineConstructionExpectedFailure.lean"
    ],
    "exact_remaining": [
      "close the sole remaining local evalStep input-node case with a preserving unary-index witness reader",
      "prove one global physical verifier execution theorem refining frozen evalRun",
      "construct one fixed finite-control NTM composing parser + witness phase + verifier",
      "prove global HaltsWithin under one polynomial timeBound",
      "prove AcceptsWithin iff SATBits circuitBitEncoding for every bitstring"
    ],
    "consequence": "closing this object closes P01ConstructionGap; G21Pointwise remains independently OPEN_MATH"
  }
}

```

## ShantiDraconis/m-core-p-vs-np / audit/ATK_P01_MATERIAL_FRONTIER_V1.json

Blob SHA: `5b2df940f0bdff90726c865ae2cb079ca1a5c0d5`

```json
{
  "schema": "ATK_P01_MATERIAL_FRONTIER_V1",
  "canonical_target": "Nonempty P01MachineConstruction",
  "provenance": {
    "parser": {
      "status": "MATERIAL_GREEN_FROZEN_REUSE",
      "branch": "frozen/p01-global-parser-simulation-prefix-green-eaf1a3af",
      "theorem": "MCore.Real.P01GlobalParserBound.slot_parser_machine_simulation_certificate",
      "content": "no-hypothesis global Fin-25 parser simulation; polynomial halting and exact slotAccept semantics"
    },
    "witness_preserving_prep": {
      "status": "PARTIAL_CONCRETE",
      "branch": "attack/t1d-global-physical-20260922",
      "object": "MCore.Real.P01WitnessPreservingPrep.witnessPreservingPrep",
      "proved": [
        "fixed Fin 12 NTM",
        "blank_none",
        "polynomial cubic time-bound function",
        "local transition/branching lemmas",
        "never rejects"
      ],
      "open": [
        "global HaltsWithin theorem for every source",
        "global reached-layout theorem preserving source and producing witness"
      ]
    },
    "verifier": {
      "status": "PARTIAL_CONCRETE",
      "branch": "attack/t1d-global-physical-20260922",
      "proved": [
        "source-end scan",
        "physical move sequences",
        "witness shuttles",
        "physicalWitnessRead_correct",
        "local neg/and/or semantics",
        "functional reverse decoder"
      ],
      "open": [
        "Nonempty PhysicalVerifierRealization",
        "single fixed finite-control TM with polynomial halting and physical_eq_logical for every circuit/witness"
      ]
    },
    "integration": {
      "status": "OPEN_MATERIAL",
      "type": "MCore.Real.P01FinalCertificate.P01MachineConstruction",
      "open": [
        "single integrated NTM",
        "blank_none",
        "polynomial bound",
        "total halting",
        "accepts_iff SATBits circuitBitEncoding"
      ]
    },
    "witness_guess": {
      "status": "MATERIAL_GREEN_CI_CONFIRMED",
      "source_branch": "atk/p01-terminal-sprint-v1",
      "object": "MCore.Real.CanonicalSATWitnessGuessNTM.witnessGuessMachine",
      "theorems": [
        "MCore.Real.P01WitnessGuessExecution.witnessGuess_complete",
        "MCore.Real.P01WitnessGuessExecution.witnessGuess_halts"
      ],
      "content": "fixed finite-control NTM; every source-length Boolean witness is reachable; every branch halts within source.length+1",
      "verified_run": 36499549795,
      "verified_conclusion": "success",
      "scope_note": "Certified component; global P01MachineConstruction remains OPEN_MATH."
    },
    "source_rewind": {
      "status": "SOURCE_THEOREM_PRESENT_KERNEL_REVALIDATION_PENDING",
      "theorem": "MCore.Real.P01FullVerifierSourceRewind.sourceRewind_halts_linear",
      "content": "real three-state TM halts from canonical source-end tape in source.length + 2",
      "source_file": "lean/MCore/Real/P01FullVerifierSourceRewind.lean",
      "source_blob_sha": "30d21ee3d2ba4e65f8a388c2b92635fc179b908f",
      "proved_in_source": [
        "sourceRewindTimeBound_poly",
        "sourceRewind_enter_step",
        "sourceRewind_separator_step",
        "rewind_scan_run",
        "sourceRewind_halts_linear"
      ],
      "audit_note": "Exact theorem body and #print axioms found; dedicated successful kernel run for this file not independently verified. Do not label CI_GREEN until verified."
    },
    "indexed_witness_read": {
      "status": "MATERIAL_GREEN_CI_CONFIRMED",
      "machine": "MCore.Real.P01WitnessIndexedReadMachine.witnessIndexedReadMachine",
      "theorems": [
        "MCore.Real.P01WitnessIndexedReadMachine.read_zero_false",
        "MCore.Real.P01WitnessIndexedReadMachine.read_zero_true",
        "MCore.Real.P01WitnessIndexedReadProof.witnessSeek_run_state",
        "MCore.Real.P01WitnessIndexedReadProof.witnessSeek_run_halts"
      ],
      "content": "fixed Fin-6 TM reads selected witness cell without storing i in finite control; arbitrary blank seek padding halts and classifies bit",
      "verified_runs": [
        36497448606,
        36497644415
      ],
      "verified_conclusions": [
        "success",
        "success"
      ],
      "scope_note": "Historical indexed witness read only; does not establish the remaining preserving unary-index input-node case or global P01MachineConstruction."
    }
  },
  "permanent_fences": [
    "DecoderEvaluatorLocalCertificate: under-specified; nonterminal transition fields do not prove decode/eval semantics",
    "legacy ParserMachineCertificate/WitnessGuessMachineCertificate/VerifierMachineCertificate: trivially inhabitable component shells",
    "abstract LowerBoundWitness.not_in_p",
    "alternate language/model substitution",
    "IntegratedPhaseBridgeCertificate: state-disjointness only; no tape/config transition or semantic preservation; not material integration"
  ],
  "next_exact_attack": [
    "complete full indexed-read certificate from unary index consumption plus witnessSeek_run_halts",
    "construct one fixed physical verifier TM that composes indexed read with stack primitives and source rewind",
    "compose certified parser + guess + verifier into P01MachineConstruction"
  ],
  "lower_bound_after_np": "UniversalFailure (SATBits circuitBitEncoding)",
  "material_status": "OPEN_MATH",
  "reconciliation_20261008": {
    "source": "GATE_LEDGER.json",
    "policy": "forward-only, historical run confirmation; no terminal mathematical promotion",
    "terminal_status": "OPEN_MATH"
  }
}

```

## ShantiDraconis/m-core-p-vs-np / audit/ATK_RUN_DATA_20261009.json

Blob SHA: `568685a0afe250d37d22fce173c9827bd7f2a96f`

```json
{
  "schema": "atk.run_data.v1",
  "generated_date": "2026-10-09",
  "repo": "ShantiDraconis/m-core-p-vs-np",
  "audited_head": "3500283a67802d0f7d687285f53752446322c2a3",
  "new_kernel_run": {
    "started": false,
    "reason": "Available GitHub connector does not expose workflow_dispatch; no local Lean repository/toolchain mounted."
  },
  "commit_checks": {
    "statuses": [],
    "pull_request_workflow_runs": [],
    "note": "No checks returned is not proof of failure or success."
  },
  "historical_verified_runs": [
    {
      "id": 36499549795,
      "conclusion": "success",
      "scope": "witness guess"
    },
    {
      "id": 36497448606,
      "conclusion": "success",
      "scope": "indexed witness reader"
    },
    {
      "id": 36497644415,
      "conclusion": "success",
      "scope": "indexed witness reader"
    },
    {
      "id": 37848515115,
      "conclusion": "success",
      "head_sha": "c0a83c28242bc9415a5657b3add970f1132b3cbc",
      "scope": "recovery integration, audits"
    }
  ],
  "historical_artifact": {
    "run_id": 37848515115,
    "name": "pnp-recovery-integration-logs",
    "id": 11581900221,
    "digest": "sha256:9f3983423e67cd73bec48867bf9ce534adb6a512e4fc7f6b2779539ad8b4703f"
  },
  "frontier_statuses": {
    "parser": "MATERIAL_GREEN_FROZEN_REUSE",
    "witness_preserving_prep": "PARTIAL_CONCRETE",
    "verifier": "PARTIAL_CONCRETE",
    "integration": "OPEN_MATERIAL",
    "witness_guess": "MATERIAL_GREEN_CI_CONFIRMED",
    "source_rewind": "SOURCE_THEOREM_PRESENT_KERNEL_REVALIDATION_PENDING",
    "indexed_witness_read": "MATERIAL_GREEN_CI_CONFIRMED"
  },
  "remaining_math": [
    "P01ConstructionGap",
    "G21Pointwise"
  ],
  "final_math_certified": false
}

```

## ShantiDraconis/m-core-p-vs-np / lean/MCore/Real/P01FullVerifierSourceRewind.lean

Blob SHA: `30d21ee3d2ba4e65f8a388c2b92635fc179b908f`

```lean
import MCore.Real.P01FullVerifierPhysicalShuttles
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01FullVerifierSourceRewind

open CanonicalFinalProof
open P01FullVerifierPhysicalShuttles

/-- Three-state local macro:
0 enters the source from the source-end blank;
1 scans left across source bits until the witness/source separator blank;
2 halts after moving right to the first source cell (or source-end blank if empty).
-/
abbrev RewindState := Fin 3

def enterSource : RewindState := 0
def scanLeft : RewindState := 1
def rewindHalt : RewindState := 2

def sourceRewindMachine : TM RewindState (Option Bool) :=
  { initial := enterSource
    blank := none
    transition := fun q symbol =>
      if q = enterSource then
        (scanLeft, symbol, .left)
      else if q = scanLeft then
        match symbol with
        | some b => (scanLeft, some b, .left)
        | none => (rewindHalt, none, .right)
      else
        (rewindHalt, symbol, .stay)
    halting := fun q => q == rewindHalt }

@[simp] theorem sourceRewindMachine_blank :
    sourceRewindMachine.blank = none := rfl

@[simp] theorem enterSource_not_halted :
    sourceRewindMachine.halting enterSource = false := by decide

@[simp] theorem scanLeft_not_halted :
    sourceRewindMachine.halting scanLeft = false := by decide

@[simp] theorem rewindHalt_halted :
    sourceRewindMachine.halting rewindHalt = true := by decide

def sourceRewindTimeBound : TimeBound :=
  fun n => n + 2

theorem sourceRewindTimeBound_poly :
    PolynomialTimeBound sourceRewindTimeBound := by
  refine ⟨2, 1, ?_⟩
  intro n
  simp [sourceRewindTimeBound]
  omega

/-- First physical step from source-end enters the last source cell, or the
separator itself when the source is empty. -/
theorem sourceRewind_enter_step
    (witness source : BitString) :
    sourceRewindMachine.step
      { state := enterSource, tape := sourceEndTape witness source } =
      { state := scanLeft,
        tape := Tape.move none .left (sourceEndTape witness source) } := by
  simp [sourceRewindMachine, enterSource, scanLeft, TM.step, Tape.write]

/-- Once the separator blank is under the head, one legal right move reaches
the source-start side and enters the halting state. -/
theorem sourceRewind_separator_step
    (t : Tape (Option Bool))
    (hhead : t.head = none) :
    sourceRewindMachine.step { state := scanLeft, tape := t } =
      { state := rewindHalt, tape := Tape.move none .right t } := by
  cases t with
  | mk left head right =>
      cases head with
      | none =>
          simp [sourceRewindMachine, scanLeft, rewindHalt, enterSource,
            TM.step, Tape.write]
      | some b =>
          simp at hhead

#print axioms MCore.Real.P01FullVerifierSourceRewind.sourceRewindTimeBound_poly
#print axioms MCore.Real.P01FullVerifierSourceRewind.sourceRewind_enter_step
#print axioms MCore.Real.P01FullVerifierSourceRewind.sourceRewind_separator_step


/-- Exact scan configuration for the unread reversed source. -/
def rewindScanConfig
    (witness : BitString)
    (remaining : BitString)
    (right : List (Option Bool)) :
    Configuration RewindState (Option Bool) :=
  match remaining with
  | [] =>
      { state := scanLeft,
        tape := { left := witness.map some, head := none, right := right } }
  | b :: bs =>
      { state := scanLeft,
        tape := { left := bs.map some ++ none :: witness.map some,
                  head := some b,
                  right := right } }

@[simp] theorem rewindScanConfig_state
    (witness remaining : BitString)
    (right : List (Option Bool)) :
    (rewindScanConfig witness remaining right).state = scanLeft := by
  cases remaining <;> rfl

theorem rewindScan_step_cons
    (witness : BitString)
    (b : Bool) (bs : BitString)
    (right : List (Option Bool)) :
    sourceRewindMachine.step
      (rewindScanConfig witness (b :: bs) right) =
    rewindScanConfig witness bs (some b :: right) := by
  cases bs <;>
    simp [rewindScanConfig, sourceRewindMachine, enterSource, scanLeft,
      rewindHalt, TM.step, Tape.write, Tape.move, List.append_assoc]

theorem rewind_scan_run
    (witness remaining : BitString)
    (right : List (Option Bool)) :
    sourceRewindMachine.run remaining.length
      (rewindScanConfig witness remaining right) =
    rewindScanConfig witness []
      (remaining.reverse.map some ++ right) := by
  induction remaining generalizing right with
  | nil =>
      rfl
  | cons b bs ih =>
      rw [List.length_cons]
      simp only [TM.run, rewindScanConfig_state, scanLeft_not_halted,
        Bool.false_eq_true, if_false]
      rw [rewindScan_step_cons]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem sourceRewind_enter_to_scan
    (witness source : BitString) :
    sourceRewindMachine.step
      { state := enterSource, tape := sourceEndTape witness source } =
    rewindScanConfig witness source.reverse [none] := by
  cases h : source.reverse with
  | nil =>
      simp [sourceEndTape, rewindScanConfig, sourceRewindMachine,
        enterSource, scanLeft, TM.step, Tape.write, Tape.move, h]
  | cons b bs =>
      simp [sourceEndTape, rewindScanConfig, sourceRewindMachine,
        enterSource, scanLeft, TM.step, Tape.write, Tape.move, h,
        List.append_assoc]

theorem sourceRewind_run_one_enter
    (witness source : BitString) :
    sourceRewindMachine.run 1
      { state := enterSource, tape := sourceEndTape witness source } =
    rewindScanConfig witness source.reverse [none] := by
  rw [TM.run]
  simp only [enterSource_not_halted, Bool.false_eq_true, if_false]
  exact sourceRewind_enter_to_scan witness source

/-- From a canonical source-end tape, the real rewind TM halts within the
linear bound n+2. -/
theorem sourceRewind_halts_linear
    (witness source : BitString) :
    sourceRewindMachine.HaltsWithin
      (source.length + 2)
      { state := enterSource, tape := sourceEndTape witness source } := by
  unfold TM.HaltsWithin
  rw [show source.length + 2 = 1 + (source.length + 1) by omega]
  rw [MachineRunLemmas.run_add]
  rw [sourceRewind_run_one_enter]
  rw [show source.length + 1 = source.reverse.length + 1 by simp]
  rw [MachineRunLemmas.run_add]
  rw [rewind_scan_run]
  simp [rewindScanConfig, sourceRewindMachine, enterSource, scanLeft,
    rewindHalt, TM.run, TM.step, Tape.write, Tape.move]

#print axioms MCore.Real.P01FullVerifierSourceRewind.sourceRewind_halts_linear

end P01FullVerifierSourceRewind
end Real
end MCore

```

## ShantiDraconis/M-Core / evidence/endpoint_states.json

Blob SHA: `7292b65ff291b364e3ca8300c2cd57e6a163c828`

```json
{
  "ExternalModelMatch": {
    "declarations": [],
    "references": [
      "final-proof/endpoints.json",
      "final-proof/pnp_prior_formalization_reuse.json",
      "final-proof/premio_final_crosswalk_20260923.json"
    ],
    "state": "REFERENCED_ONLY",
    "unsafe_reference": false
  },
  "FINAL_EXTERNAL_ISSUED": {
    "declarations": [],
    "references": [
      "final-proof/endpoints.json",
      ".github/workflows/elyon-final-external-preparatory-freeze.yml",
      "certs/final_external/FINAL_PROOF_REUSE_LINKS_20260923.json",
      "certs/final_external/v1/manifest.json",
      "certs/final_external/v1/MATH_TERMINAL_BOUNDARY_20260922.json",
      "certs/final_external/v1/status.json",
      "certs/final_external/v1/README.md",
      "certs/final_external/v1/reproducibility.md"
    ],
    "state": "REFERENCED_ONLY",
    "unsafe_reference": true
  },
  "FINAL_PROOF": {
    "declarations": [],
    "references": [
      "ATK_HARD_CHAIN_INDEX.md",
      "FINAL_CLOSURE_REPORT.md",
      "FINAL_FAIL_MATHEMATICS.md",
      "final-proof/pnp_reuse_chain.json",
      "final-proof/endpoints.json",
      "final-proof/global_sources.json",
      "final-proof/premio_final_crosswalk_20260923.json",
      "final-proof/all_relevant_files.json",
      "EXPORTS/README.md",
      "certificado-runner/03_certificado_final_if_existed.md",
      "lean/MCore/FinalFail/ExactGapLedger.lean",
      ".github/workflows/final-proof-miner.yml",
      ".github/workflows/mcore-full-chain-archive-audit.yml",
      ".github/workflows/mcore-final-proof-integrated.yml",
      "certs/semantic_frontier/ATK_SEMANTIC_FRONTIER_0OF7_GREEN_299eeda5.md",
      "certs/final_external/FINAL_PROOF_REUSE_LINKS_20260923.json",
      "certs/final_external/v1/MATH_TERMINAL_BOUNDARY_20260922.json",
      "certs/final_external/v1/status.json",
      "certs/final_external/v1/gate_ledger.json",
      "imports/pnp/current/agents/00-orchestrator.md",
      "imports/pnp/current/agents/08-final-external-integrator.md"
    ],
    "state": "REFERENCED_ONLY",
    "unsafe_reference": true
  },
  "FINAL_ROOT": {
    "declarations": [],
    "references": [
      "MCCS_STATUS.json",
      "final-proof/endpoints.json",
      ".github/workflows/elyon-final-external-preparatory-freeze.yml",
      "certs/final_external/FINAL_PROOF_REUSE_LINKS_20260923.json",
      "certs/final_external/v1/manifest.json",
      "certs/final_external/v1/provenance.json",
      "certs/final_external/v1/MATH_TERMINAL_BOUNDARY_20260922.json",
      "certs/final_external/v1/status.json",
      "certs/final_external/v1/README.md",
      "certs/final_external/v1/reproducibility.md",
      "imports/pnp/current/agents/00-orchestrator.md",
      "imports/pnp/current/agents/08-final-external-integrator.md"
    ],
    "state": "REFERENCED_ONLY",
    "unsafe_reference": true
  },
  "FinalExternalCertificate": {
    "declarations": [],
    "references": [
      "final-proof/pnp_reuse_chain.json",
      "final-proof/endpoints.json",
      "final-proof/pnp_prior_formalization_reuse.json",
      "final-proof/all_relevant_files.json",
      "certs/final_external/FINAL_PROOF_REUSE_LINKS_20260923.json",
      "imports/pnp/current/agents/08-final-external-integrator.md",
      "imports/pnp/c102d9d4/lean/MCore/Real/FinalExternalCertificate.lean",
      "imports/pnp/b406b806/lean/MCore/Real/FinalExternalTwoGap.lean"
    ],
    "state": "REFERENCED_ONLY",
    "unsafe_reference": false
  },
  "FinalExternalGap": {
    "declarations": [
      {
        "file": "imports/pnp/c102d9d4/lean/MCore/Real/FinalExternalCertificate.lean",
        "kind": "def"
      }
    ],
    "references": [
      "final-proof/pnp_reuse_chain.json",
      "final-proof/endpoints.json",
      "final-proof/premio_final_crosswalk_20260923.json",
      "imports/pnp/c102d9d4/lean/MCore/Real/FinalExternalCertificate.lean",
      "imports/pnp/b406b806/lean/MCore/Real/FinalExternalTwoGap.lean"
    ],
    "state": "FOUND",
    "unsafe_reference": false
  },
  "FinalExternalLiveTwoProducer": {
    "declarations": [],
    "references": [
      "final-proof/endpoints.json",
      "imports/pnp/current/agents/08-final-external-integrator.md"
    ],
    "state": "REFERENCED_ONLY",
    "unsafe_reference": false
  },
  "G21Pointwise": {
    "declarations": [
      {
        "file": "imports/pnp/c102d9d4/lean/MCore/Real/P02G21G22Attack.lean",
        "kind": "def"
      }
    ],
    "references": [
      "MCCS_STATUS.json",
      "final-proof/pnp_reuse_chain.json",
      "final-proof/endpoints.json",
      "final-proof/global_sources.json",
      "final-proof/pnp_prior_formalization_reuse.json",
      "final-proof/premio_final_crosswalk_20260923.json",
      "final-proof/all_relevant_files.json",
      "lean/MCore/FinalProofRegistry.lean",
      "certs/final_external/FINAL_PROOF_REUSE_LINKS_20260923.json",
      "certs/final_external/v1/manifest.json",
      "certs/final_external/v1/MATH_TERMINAL_BOUNDARY_20260922.json",
      "certs/final_external/v1/status.json",
      "imports/pnp/c102d9d4/lean/MCore/Real/P02G21G22Attack.lean",
      "imports/pnp/b406b806/lean/MCore/Real/FinalExternalTwoGap.lean"
    ],
    "state": "REFERENCED_ONLY",
    "unsafe_reference": true
  },
  "OfficialPneqNP": {
    "declarations": [],
    "references": [
      "final-proof/pnp_reuse_chain.json",
      "final-proof/endpoints.json",
      "final-proof/premio_final_crosswalk_20260923.json",
      "imports/pnp/c102d9d4/lean/MCore/Real/FinalExternalCertificate.lean",
      "imports/pnp/b406b806/lean/MCore/Real/FinalExternalTwoGap.lean"
    ],
    "state": "REFERENCED_ONLY",
    "unsafe_reference": false
  },
  "P01ConstructionGap": {
    "declarations": [],
    "references": [
      "MCCS_STATUS.json",
      "final-proof/pnp_reuse_chain.json",
      "final-proof/endpoints.json",
      "final-proof/global_sources.json",
      "final-proof/premio_final_crosswalk_20260923.json",
      "final-proof/all_relevant_files.json",
      "lean/MCore/FinalProofRegistry.lean",
      "certs/final_external/FINAL_PROOF_REUSE_LINKS_20260923.json",
      "certs/final_external/v1/manifest.json",
      "certs/final_external/v1/MATH_TERMINAL_BOUNDARY_20260922.json",
      "certs/final_external/v1/status.json",
      "imports/pnp/b406b806/lean/MCore/Real/FinalExternalTwoGap.lean"
    ],
    "state": "REFERENCED_ONLY",
    "unsafe_reference": true
  },
  "P01MachineConstruction": {
    "declarations": [],
    "references": [
      "MCCS_STATUS.json",
      "final-proof/pnp_reuse_chain.json",
      "final-proof/endpoints.json",
      "final-proof/premio_final_crosswalk_20260923.json",
      "certs/final_external/v1/manifest.json",
      "certs/final_external/v1/MATH_TERMINAL_BOUNDARY_20260922.json",
      "imports/pnp/44e3327a/lean/MCore/Real/P01ConstructionClose.lean",
      "imports/pnp/current/agents/02-t1-machine-construction.md"
    ],
    "state": "REFERENCED_ONLY",
    "unsafe_reference": true
  },
  "P02SelfCodeExistence": {
    "declarations": [],
    "references": [
      "final-proof/endpoints.json",
      "imports/pnp/current/agents/06-self-code-universal-witness.md"
    ],
    "state": "REFERENCED_ONLY",
    "unsafe_reference": false
  },
  "P02Target": {
    "declarations": [],
    "references": [
      "final-proof/endpoints.json",
      "final-proof/pnp_prior_formalization_reuse.json",
      "final-proof/premio_final_crosswalk_20260923.json",
      "certs/final_external/v1/manifest.json",
      "certs/final_external/v1/MATH_TERMINAL_BOUNDARY_20260922.json",
      "imports/pnp/current/agents/07-g21-p02-target.md",
      "imports/pnp/c102d9d4/lean/MCore/Real/P02G21G22Attack.lean",
      "imports/pnp/b406b806/lean/MCore/Real/FinalExternalTwoGap.lean"
    ],
    "state": "REFERENCED_ONLY",
    "unsafe_reference": true
  },
  "SameInputClosure": {
    "declarations": [],
    "references": [
      "final-proof/endpoints.json"
    ],
    "state": "REFERENCED_ONLY",
    "unsafe_reference": false
  },
  "diagonalCompilerV2": {
    "declarations": [],
    "references": [
      "final-proof/endpoints.json"
    ],
    "state": "REFERENCED_ONLY",
    "unsafe_reference": false
  },
  "final_external_certificate": {
    "declarations": [
      {
        "file": "imports/pnp/c102d9d4/lean/MCore/Real/FinalExternalCertificate.lean",
        "kind": "theorem"
      }
    ],
    "references": [
      "final-proof/pnp_reuse_chain.json",
      "final-proof/endpoints.json",
      "imports/pnp/c102d9d4/lean/MCore/Real/FinalExternalCertificate.lean"
    ],
    "state": "FOUND",
    "unsafe_reference": false
  },
  "final_external_live_two_producer_closed": {
    "declarations": [],
    "references": [
      "final-proof/endpoints.json"
    ],
    "state": "REFERENCED_ONLY",
    "unsafe_reference": false
  },
  "p01_closed_no_hypothesis": {
    "declarations": [],
    "references": [
      "final-proof/endpoints.json",
      "imports/pnp/current/agents/02-t1-machine-construction.md"
    ],
    "state": "REFERENCED_ONLY",
    "unsafe_reference": false
  },
  "universal_witness_exists_no_hypothesis": {
    "declarations": [],
    "references": [
      "final-proof/endpoints.json",
      "imports/pnp/current/agents/06-self-code-universal-witness.md"
    ],
    "state": "REFERENCED_ONLY",
    "unsafe_reference": false
  }
}

```

## ShantiDraconis/M-Core / certs/final_external/v1/status.json

Blob SHA: `a9313ad2d22dfe9fc6b2c98d53da15ab7b8b11e6`

```json
{
  "schema": "elyon.final-external.v1.0.0",
  "certificate": "ELYON_FINAL_EXTERNAL",
  "version": "v1.0.0",
  "issuance": {
    "FINAL_EXTERNAL_ISSUED": false,
    "reason": "Fail-closed: the mathematical pipeline is now GREEN/FROZEN/CERTIFIED through the FinalExternalTwoGap reduction, so only two mathematical producers remain: P01ConstructionGap and G21Pointwise (equivalent to SAT not in P). G3 and G2.2 wiring are closed. Product/human issuance gates remain governed separately.",
    "infra_state": "READY_FOR_FREEZE",
    "math_state": "OPEN_MATH_TWO_EXACT_PRODUCERS",
    "release_state": "SEALED_CLOSED",
    "max_machine_state": "REVIEW_PENDING",
    "public_status": "PREPARATORY_NOT_ISSUED",
    "next_possible_without_human": [
      "PREPARATORY_PACKAGE",
      "HASHED",
      "REPRODUCIBILITY_AUDITED",
      "FROZEN_PREPARATORY"
    ],
    "not_possible": "FINAL_EXTERNAL_ISSUED"
  },
  "human_review": {
    "authority": "UNSET",
    "quorum": "UNSET",
    "evidence_policy": "UNSET"
  },
  "production": {
    "app": "UNSET",
    "crypto": "UNSET",
    "hardware": "UNSET"
  },
  "G3": "FORMAL_CONTRACT_CLOSED_GREEN_FROZEN_CERTIFIED",
  "final_proof": "0/7",
  "note": "This artifact can exist now as preparatory schema/manifest, but must NOT receive FINAL_EXTERNAL=ISSUED until release gates satisfied",
  "package_state": "PREPARATORY",
  "public_status": "PREPARATORY_NOT_ISSUED",
  "public_label": "PREPARATORY / non-issued infrastructure record",
  "hash_levels": {
    "PACKAGE_SHA256SUMS": "CALCULABLE_NOW_over_preparatory_files",
    "PREPARATORY_ROOT": "SEE_PREPARATORY_ROOT_FILE",
    "FINAL_ROOT": "NULL_MUST_REMAIN_NULL_until_P01ConstructionGap_and_G21Pointwise_and_all_release_gates_close"
  },
  "normative_state": {
    "ELYON_FINAL_EXTERNAL": "v1.0.0",
    "package_state": "PREPARATORY",
    "infra_state": "READY_FOR_FREEZE",
    "math_state": "OPEN_MATH",
    "final_proof": "0/7",
    "release_state": "SEALED_CLOSED",
    "maximum_auto_state": "REVIEW_PENDING",
    "FINAL_EXTERNAL_ISSUED": false,
    "P01_PREFIX": "GREEN_FROZEN_CERTIFIED_THROUGH_TERMINAL_BRANCHES_AND_GLOBAL_SLOTLOG",
    "P01_ENDPOINT": "OPEN_IMPLEMENTATION_P01_CONSTRUCTION",
    "P02_FRONTIER": "G2_1_LITERAL_CLOSED_BY_FALSIFICATION__G2_2_WIRING_GREEN_FROZEN_CERTIFIED",
    "P02_ENDPOINT": "OPEN_MATH_G21_POINTWISE_EQ_FAILURE_GENERATOR_EQ_SAT_NOT_IN_P",
    "P03..P07": "OPEN_MATH",
    "G3": "CLOSED_GREEN_FROZEN_CERTIFIED",
    "FINAL_EXTERNAL_MATH_INPUTS": "EXACT_TWO_PRODUCERS_REMAIN_P01ConstructionGap_AND_G21Pointwise",
    "FINAL_EXTERNAL_TWO_GAP_PIPELINE": "GREEN_FROZEN_CERTIFIED",
    "FINAL_EXTERNAL_TWO_GAP_PROGRESS": "0/2",
    "P_VS_NP_ENDPOINT": "OPEN",
    "P_VS_NP_EXTERNAL_MATH_CERTIFIED": false,
    "FINAL_ROOT_MATH": null,
    "GLOBAL_7_PROBLEMS_FINAL_PROOF": "0/7"
  },
  "package_revision": "v1.3.1-preparatory",
  "freeze_state": "FROZEN_PREPARATORY",
  "math_terminal_boundary": {
    "record": "MATH_TERMINAL_BOUNDARY_20260922.json",
    "frozen_branch": "frozen/final-external-math-boundary-442d11aa",
    "p01": "OPEN_IMPLEMENTATION_P01_CONSTRUCTION",
    "p02": "OPEN_MATH_G21_POINTWISE_EQ_SAT_NOT_IN_P",
    "g3": "CLOSED_GREEN_FROZEN_CERTIFIED",
    "latest_main_record_commit": "2df65e9c2e10ba8f920751b1202b161322425925",
    "g2_wiring": "CLOSED_GREEN_FROZEN_CERTIFIED",
    "two_gap_reduction": "CLOSED_GREEN_FROZEN_CERTIFIED",
    "exact_remaining_producers": [
      "P01ConstructionGap",
      "G21Pointwise"
    ],
    "certified_delta": {
      "p01_terminal_branches": {
        "source_sha": "f9add60881d709ce8320cb54a4d52f26d829b8f5",
        "run": 35722846538,
        "frozen_branch": "frozen/p01-terminal-branches-green-f9add608"
      },
      "p01_global_slotlog_spec": {
        "source_sha": "614f88fe020fd05b9b251a6a2283301acf7ff733",
        "run": 35723570545,
        "frozen_branch": "frozen/p01-global-slotlog-spec-green-614f88fe"
      },
      "p02_g2_2_wiring": {
        "source_sha": "38db71b416906e5b7138774842e91d3e367aad09",
        "run": 35722282451,
        "frozen_branch": "frozen/p02-g2-2-wiring-green-38db71b4"
      },
      "final_external_integration": {
        "source_sha": "c102d9d482d708a7a865803e94f294c6da82ed9a",
        "run": 35722252805,
        "frozen_branch": "frozen/final-external-integration-green-c102d9d4"
      },
      "final_external_two_gap": {
        "source_sha": "b406b806da58ebe6bc1f85863ee44054ad42edb2",
        "run": 35722743845,
        "frozen_branch": "frozen/final-external-two-gap-green-b406b806"
      }
    },
    "interface_policy": "INTERFACE_ONLY_FAIL_CLOSED_NO_PROOF_FABRICATION",
    "certified_source_policy": "NO_SORRY_ADMIT_AXIOM_PLACEHOLDERS",
    "taxonomy": "TWO_GAP_0_OF_2__P_VS_NP_ENDPOINT_OPEN__GLOBAL_0_OF_7"
  },
  "taxonomy": {
    "FINAL_EXTERNAL_TWO_GAP": {
      "progress": "0/2",
      "P01ConstructionGap": "OPEN_IMPLEMENTATION",
      "G21Pointwise": "OPEN_MATH"
    },
    "P_VS_NP_ENDPOINT": "OPEN",
    "P_VS_NP_EXTERNAL_MATH_CERTIFIED": false,
    "FINAL_ROOT_MATH": null,
    "GLOBAL_7_PROBLEMS": {
      "FINAL_PROOF": "0/7"
    },
    "FINAL_ROOT": null,
    "FINAL_EXTERNAL_ISSUED": false
  }
}

```

## ShantiDraconis/M-Core / certs/final_external/v1/manifest.json

Blob SHA: `450eb16bf3b9e6b8cf66215d0a93b5696850d1f9`

```json
{
  "schema": "elyon.final-external.v1.0.0",
  "certificate_type": "INFRASTRUCTURE_CERTIFIED",
  "name": "ELYON_FINAL_EXTERNAL",
  "version": "v1.0.0",
  "alias": "elyon",
  "scope": [
    "MCORE",
    "AINUM",
    "OS",
    "HUB",
    "BRAIN",
    "APP",
    "ELYON"
  ],
  "infra_state": "READY_FOR_FREEZE",
  "math_state": "OPEN_MATH_TWO_EXACT_PRODUCERS",
  "final_proof": {
    "numerator": 0,
    "denominator": 7,
    "display": "0/7",
    "terminal_status": {
      "P01": "OPEN_IMPLEMENTATION - certified through parser/leaf, terminal branches and global-slotlog; exact open payload P01ConstructionGap / Nonempty P01MachineConstruction",
      "P02": "OPEN_MATH - G2.1 literal route CLOSED_BY_FALSIFICATION; G2.2 wiring GREEN_FROZEN_CERTIFIED; exact open payload G21Pointwise ≃ P02Target ≃ SAT not in P",
      "P03": "OPEN_MATH",
      "P04": "OPEN_MATH",
      "P05": "OPEN_MATH",
      "P06": "OPEN_MATH",
      "P07": "OPEN_MATH",
      "G3": "CLOSED_GREEN_FROZEN_CERTIFIED"
    },
    "claim_policy": "NO_CLAIM_OF_P_NP_CLAY_BEAL_SOLVED",
    "taxonomy": {
      "FINAL_EXTERNAL_TWO_GAP": "0/2",
      "P_VS_NP_ENDPOINT": "OPEN",
      "P_VS_NP_EXTERNAL_MATH_CERTIFIED": false,
      "FINAL_ROOT_MATH": null,
      "GLOBAL_7_PROBLEMS": "0/7",
      "rule": "Two internal P vs NP producers count as one global problem endpoint only after both close."
    }
  },
  "release_state": "SEALED_CLOSED",
  "max_machine_state": "REVIEW_PENDING",
  "anchors": {
    "ELYON": {
      "base": "483f6bdc06b74a0239481085e25c9a9fdccb1a8f",
      "audit": "0f71ffea68ed52691201144140fb1a342d03b8d7",
      "run": "35378862267",
      "run_status": "SUCCESS",
      "state": "SEALED_CLOSED",
      "role": "official_anchor_v1_until_explicit_revision"
    },
    "P01": {
      "prefix": "614f88fe020fd05b9b251a6a2283301acf7ff733",
      "state": "GREEN_FROZEN_CERTIFIED_ADVANCED_PREFIX",
      "runs": [
        "35722427864 SUCCESS integrated parser/leaf",
        "35722846538 SUCCESS terminal branches",
        "35723570545 SUCCESS phase/global-slotlog"
      ],
      "pending_ATK": [
        "P01ConstructionGap",
        "Nonempty P01MachineConstruction"
      ]
    },
    "P02": {
      "frontier": "38db71b416906e5b7138774842e91d3e367aad09",
      "status": "G2_2_WIRING_GREEN_FROZEN_CERTIFIED__G21_POINTWISE_OPEN_MATH",
      "runs": [
        "35722282451 SUCCESS"
      ],
      "pending_ATK": "G21Pointwise / P02Target / Nonempty FailureGenerator(SATBits circuitBitEncoding), equivalent to SAT not in P"
    },
    "MCORE_HUB": {
      "hub_anchor": "11adcd32...",
      "state": "GREEN_FROZEN_SCAFFOLD"
    }
  },
  "human_review": {
    "authority": "UNSET",
    "quorum": "UNSET",
    "evidence_policy": "UNSET",
    "status": "REVIEW_PENDING",
    "notes": "Must be defined by human authority. Cannot be chosen by technical validator. Evidence must be GPG/Sigstore + PR comment + APPROVED_BY_HUMAN tag in review.json"
  },
  "production": {
    "app": {
      "app_repository": "UNSET",
      "app_commit": "UNSET",
      "app_pass_test": "UNSET",
      "current_state": "NOT_CONNECTED"
    },
    "crypto": {
      "crypto_provider": "UNSET",
      "public_key_or_key_id": "UNSET",
      "algorithm": "UNSET",
      "attestation": "UNSET",
      "current_state": "GREEN_FROZEN_SCAFFOLD production_crypto_verified=false"
    },
    "hardware_attestation": {
      "status": "UNSET",
      "allowed_values": [
        "UNSET",
        "OUT_OF_SCOPE_FOR_V1",
        "TPM2_ATTESTED",
        "SECURE_BOOT_ATTESTED"
      ],
      "current_claim": "hardware_secure_boot_claimed=false"
    }
  },
  "G3": {
    "statement": "G3ExternalContract for the normalized Cook-style external model",
    "repository": "ShantiDraconis/m-core-p-vs-np",
    "namespace": "MCore.Real.CookNormalizedG3Contract",
    "source_file": "lean/MCore/Real/CookNormalizedG3Contract.lean",
    "closure_condition": "cook_normalized_g3_contract_closed",
    "source_sha": "f2cafea7a74f3ef8ad4140943515622545c9f1d8",
    "run": 35719428075,
    "status": "CLOSED_GREEN_FROZEN_CERTIFIED",
    "notes": "Formal normalized external contract closed. Independent exhaustive fidelity to every Cook/CMI prose convention is a separate audit statement and is not endpoint proof credit."
  },
  "artifacts_required": [
    "manifest.json",
    "README.md",
    "SHA256SUMS",
    "provenance.json",
    "gate_ledger.json",
    "axiom_footprint.json",
    "reproducibility.md",
    "signature.bundle / .asc",
    "MATH_TERMINAL_BOUNDARY_20260922.json",
    "status.json",
    "revocation.json"
  ],
  "toolchain": {
    "normative": "Lean 4.19 + lake",
    "policy": "Other tools (Python, OS runner, Coq/Agda/Isabelle) only included if effectively used in final package. Must be recorded in provenance.json with exact versions."
  },
  "axiom_policy": {
    "allowed_when_present": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "forbidden": [
      "sorryAx",
      "sorry",
      "admit",
      "custom theorem-carrying axioms",
      "hidden oracle",
      "circularity"
    ],
    "audit_required": true
  },
  "brain_policy": {
    "v1": "OBSERVE_REASON_ABSTAIN",
    "change_requires": "explicit policy version bump"
  },
  "publication": {
    "canonical": "Zenodo",
    "mirror_optional": "Figshare",
    "destination": "M-Core/certs/final_external/v1/",
    "mirror": "Genesis_Elyon/certs/final_external/v1/",
    "optional_mirror": "zero-ai-00/certs/",
    "license_code": "MIT / Apache-2.0",
    "license_docs": "CC-BY-4.0",
    "prize_policy": "Technical certificate does not declare prize recognition. Clay/Beal claims separate."
  },
  "root": {
    "derivation": "deterministic hash of SHAs/hashes of all layers and certs: hash(MCORE)+hash(AINUM)+hash(OS)+hash(HUB)+hash(BRAIN)+hash(APP)+hash(ELYON)+hashes(P01..P07 certs)",
    "value": null,
    "status": "PREPARATORY_ROOT_IN_SEPARATE_FILE; FINAL_ROOT_NULL_UNTIL_ISSUANCE_GATES",
    "FINAL_ROOT": null,
    "PREPARATORY_ROOT": null,
    "derivation_final": "hash(MCORE)+hash(AINUM)+hash(OS)+hash(HUB)+hash(BRAIN)+hash(APP)+hash(ELYON)+hashes(P01..P07) + production crypto + hardware + human_review + final frozen anchors",
    "derivation_preparatory": "SHA256 of canonical SHA256SUMS payload; payload includes MATH_TERMINAL_BOUNDARY_20260922.json and immutable preparatory package files, excluding SHA256SUMS/PREPARATORY_ROOT to avoid self-reference",
    "preparatory_root_location": "PREPARATORY_ROOT",
    "FINAL_ROOT_MATH": null,
    "linked_preparatory_root": "4cdaf7b62ee2ff85676c7dcd98fb6dfe965fa8afd4abccf19ba6aedb42878f24"
  },
  "timestamps": {
    "created_at": null,
    "approved_at": null,
    "published_at": null,
    "policy": "three separate timestamps"
  },
  "versioning": {
    "v1": "immutable after freeze",
    "future": "SUPERSEDES previous with explicit reason",
    "revocation": "status.json / revocation.json in same path, with REVOKED / SUPERSEDED / INVALIDATED"
  },
  "issuance_gate": {
    "FINAL_EXTERNAL_ISSUED": false,
    "condition": "P01ConstructionGap closed AND G21Pointwise closed AND G3 CLOSED AND human_review != UNSET AND production.app != UNSET AND production.crypto != UNSET AND hardware_attestation != UNSET AND all required infra GREEN+FROZEN",
    "current": "BLOCKED fail-closed: P01ConstructionGap OPEN_IMPLEMENTATION; G21Pointwise OPEN_MATH; P_VS_NP_ENDPOINT OPEN; human_review UNSET; app UNSET; crypto UNSET; hardware UNSET",
    "public_status": "PREPARATORY_NOT_ISSUED"
  },
  "package_state": "PREPARATORY",
  "public_status": "PREPARATORY_NOT_ISSUED",
  "public_label": "PREPARATORY / non-issued infrastructure record - NOT A CLAIM OF ISSUED CERTIFICATE",
  "maximum_auto_state": "REVIEW_PENDING",
  "package_state_policy": "PACKAGE_SHA256SUMS can be calculated now. FINAL_ROOT must remain null while any issuance prerequisite UNSET",
  "package_revision": "v1.3.1-preparatory",
  "freeze_state": "FROZEN_PREPARATORY"
}

```
