import Erdos339.LowerDensity
import Erdos339.UpperDensity

/-!
# Erdős Problem 339: both original questions

The lower-density theorem `erdos_339` is the attributed, locally restored
upstream proof, not a new contribution. `erdos_339_upperDensity` is the
AI-assisted extension in this repository. The combined theorem below makes
the full scope explicit without adding any mathematical hypotheses.
-/

open scoped Pointwise

namespace Erdos339

/-- Both original clauses of Erdős Problem 339, for every natural order.
The order-zero statements are included; their premises are impossible. -/
theorem erdos_339_complete :
    (∀ (A : Set ℕ) (r : ℕ), A.IsAsymptoticAddBasisOfOrder r →
      0 < (restrictedSums r A).lowerDensity) ∧
    (∀ (A : Set ℕ) (r : ℕ), 0 < (r • A).upperDensity →
      0 < (restrictedSums r A).upperDensity) := by
  constructor
  · intro A r h
    exact erdos_339 h
  · intro A r h
    exact erdos_339_upperDensity h

end Erdos339
