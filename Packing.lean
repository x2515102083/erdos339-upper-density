/-
Research component for generalized Erdős 316.
This file proves a generic grid obstruction and one three-bin example.
It does NOT yet prove the universally quantified generalized theorem.
New implementation prepared with AI assistance; no priority claim.
The historical result is attributed to Csaba Sándor (1997).
-/
import Mathlib

open scoped BigOperators

namespace Erdos316Research

/-- Integer mass exceeding the total capacity forces a full bin. -/
theorem integer_obstruction {α : Type*} (s : Finset α) (w : α → ℕ)
    (N r : ℕ) (h : r * (N - 1) < ∑ a ∈ s, w a) (c : α → Fin r) :
    ∃ j : Fin r, N ≤ ∑ a ∈ s, if c a = j then w a else 0 := by
  classical
  by_contra! hbad
  have hb : ∀ j : Fin r, (∑ a ∈ s, if c a = j then w a else 0) ≤ N - 1 := by
    intro j
    have hj := hbad j
    omega
  have hf : (∑ j : Fin r, ∑ a ∈ s, if c a = j then w a else 0) =
      ∑ a ∈ s, w a := by
    rw [Finset.sum_comm]
    simp
  have hs := Finset.sum_le_sum (fun (j : Fin r) (_ : j ∈ Finset.univ) => hb j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs
  omega

/-- The total mass r*N-1 exceeds r bins of capacity N-1, for every r>=2. -/
theorem integer_obstruction_exact {α : Type*} (s : Finset α) (w : α → ℕ)
    (N r : ℕ) (hN : 0 < N) (hr : 2 ≤ r)
    (hs : (∑ a ∈ s, w a) + 1 = r * N) (c : α → Fin r) :
    ∃ j : Fin r, N ≤ ∑ a ∈ s, if c a = j then w a else 0 := by
  have hN' : N - 1 + 1 = N := by omega
  have hcap : r * (N - 1) + r = r * N := by nlinarith
  apply integer_obstruction s w N r _ c
  omega

/-- A rational-grid certificate proves the total bound and every coloring obstruction. -/
theorem rational_grid_obstruction {α : Type*} (s : Finset α) (w : α → ℕ)
    (N r : ℕ) (hN : 0 < N) (hr : 2 ≤ r)
    (hs : (∑ a ∈ s, w a) + 1 = r * N) :
    (∑ a ∈ s, (w a : ℚ) / (N : ℚ)) < r ∧
      ∀ c : α → Fin r, ∃ j : Fin r,
        1 ≤ ∑ a ∈ s, if c a = j then (w a : ℚ) / (N : ℚ) else 0 := by
  classical
  have hNQ : (0 : ℚ) < N := by exact_mod_cast hN
  have hsQ : (∑ a ∈ s, (w a : ℚ)) + 1 = (r : ℚ) * (N : ℚ) := by
    exact_mod_cast hs
  constructor
  · rw [← Finset.sum_div, div_lt_iff₀ hNQ]
    linarith
  · intro c
    obtain ⟨j, hj⟩ := integer_obstruction_exact s w N r hN hr hs c
    refine ⟨j, ?_⟩
    have hjQ : (N : ℚ) ≤ ∑ a ∈ s, if c a = j then (w a : ℚ) else 0 := by
      exact_mod_cast hj
    have heq : (∑ a ∈ s, if c a = j then (w a : ℚ) / (N : ℚ) else 0) =
        (∑ a ∈ s, if c a = j then (w a : ℚ) else 0) / (N : ℚ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a ha
      split_ifs <;> simp
    rw [heq, le_div_iff₀ hNQ]
    simpa using hjQ

/-- Actual positive divisors, not abstract rational weights, give unit fractions. -/
theorem unit_fraction_certificate (A : Finset ℕ) (N r : ℕ)
    (hN : 0 < N) (hr : 2 ≤ r)
    (hA : ∀ a ∈ A, 0 < a ∧ a ∣ N)
    (hs : (∑ a ∈ A, N / a) + 1 = r * N) :
    (∑ a ∈ A, (1 : ℚ) / a) < r ∧
      ∀ c : ℕ → Fin r, ∃ j : Fin r,
        1 ≤ ∑ a ∈ A, if c a = j then (1 : ℚ) / a else 0 := by
  classical
  have hNQ : (N : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hquot : ∀ a ∈ A, ((N / a : ℕ) : ℚ) / (N : ℚ) = (1 : ℚ) / a := by
    intro a ha
    have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hA a ha).1)
    apply (div_eq_div_iff hNQ haQ).2
    have hh : (N / a) * a = N := Nat.div_mul_cancel (hA a ha).2
    have hhQ : ((N / a : ℕ) : ℚ) * (a : ℚ) = (N : ℚ) := by exact_mod_cast hh
    simpa using hhQ
  have hh := rational_grid_obstruction A (fun a => N / a) N r hN hr hs
  constructor
  · have heq : (∑ a ∈ A, ((N / a : ℕ) : ℚ) / (N : ℚ)) =
        ∑ a ∈ A, (1 : ℚ) / a := Finset.sum_congr rfl hquot
    rw [← heq]
    exact hh.1
  · intro c
    obtain ⟨j, hj⟩ := hh.2 c
    refine ⟨j, ?_⟩
    have heq : (∑ a ∈ A, if c a = j then ((N / a : ℕ) : ℚ) / (N : ℚ) else 0) =
        ∑ a ∈ A, if c a = j then (1 : ℚ) / a else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      split_ifs
      · exact hquot a ha
      · rfl
    rwa [heq] at hj

end Erdos316Research

#print axioms Erdos316Research.integer_obstruction
#print axioms Erdos316Research.integer_obstruction_exact
#print axioms Erdos316Research.rational_grid_obstruction
#print axioms Erdos316Research.unit_fraction_certificate

namespace Erdos316Research

def threeBinExample : Finset ℕ := {2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 27, 28, 30, 32, 35, 36, 40, 42, 45, 48, 54, 56, 60, 63, 70, 72, 80, 84, 90, 96, 105, 108, 112, 120, 126, 135, 140, 144, 160, 168, 180, 189, 210, 216, 224, 240, 252, 270, 280, 288, 315, 336, 360, 378, 420, 432, 480, 504, 540, 560, 630, 672, 720, 756, 840, 864, 945, 1008, 1080, 1120, 1260, 1440, 1512, 1680, 1890, 2016, 2160, 2520, 3024, 3360, 3780, 4320, 5040, 6048, 7560, 10080, 15120}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Explicit three-bin counterexample. No assertion about arbitrary r is made here. -/
theorem three_bin_example :
    0 ∉ threeBinExample ∧ 1 ∉ threeBinExample ∧
    (∑ a ∈ threeBinExample, (1 : ℚ) / a) < 3 ∧
    ∀ c : ℕ → Fin 3, ∃ j : Fin 3,
      1 ≤ ∑ a ∈ threeBinExample, if c a = j then (1 : ℚ) / a else 0 := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  exact unit_fraction_certificate threeBinExample 30240 3
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

end Erdos316Research

#print axioms Erdos316Research.three_bin_example
