import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.Order.Filter.Cofinite

/-!
# Asymptotic additive bases

An order-r basis contains a representation of all but finitely many elements
as a sum of exactly r (not necessarily distinct) members. This conventional
definition matches the one used by the pinned upstream Erdos339 theorem and
FormalConjecturesForMathlib.Combinatorics.Additive.Basis. No result about
Erdos 868 is imported or assumed.
-/

open Filter
open scoped Pointwise

namespace Set

/-- The unrestricted order-r sumset is cofinite. -/
def IsAsymptoticAddBasisOfOrder {M : Type*} [AddCommMonoid M]
    (A : Set M) (r : ℕ) : Prop :=
  ∀ᶠ n in cofinite, n ∈ r • A

lemma isAsymptoticAddBasisOfOrder_iff_atTop {A : Set ℕ} {r : ℕ} :
    A.IsAsymptoticAddBasisOfOrder r ↔ ∀ᶠ n in atTop, n ∈ r • A := by
  rw [IsAsymptoticAddBasisOfOrder, Nat.cofinite_eq_atTop]

end Set
