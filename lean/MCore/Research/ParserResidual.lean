import MCore.Real.CNFStructure

namespace MCore.Real

/-- First executable residual below ParserRoundtripGoal.
    It isolates decimal decoding from the recursive Circuit parser. -/
def DecimalRoundtripGoal : Prop :=
  ∀ n : Nat,
    parseNatChars (toString n).toList 0 false = some (n, [])

/-- Exact parent/child contract for the first parser residual.
    No direction is postulated here: both maps must be supplied by proofs. -/
structure ParserDecimalBridge where
  parserToDecimal : MCore.Research.ParserRoundtripGoal → DecimalRoundtripGoal
  decimalToParser : DecimalRoundtripGoal → MCore.Research.ParserRoundtripGoal

end MCore.Real
