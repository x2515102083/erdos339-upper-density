/-
Finite cutoff refinement: x2515102083, with ChatGPT assistance.
The telescoping reciprocal inequality is imported from the attributed core.
No global mathematical novelty is asserted for this elementary refinement.
-/
import ErdosProblems.Erdos440

open Finset Erdos440
open scoped BigOperators

namespace Erdos440Cutoff

/-- A strict, freely tunable finite bound for the counting function. -/
theorem strict_cutoff (A : IncreasingSequence) (X t : ℕ)
    (hX : 0 < X) (ht : 0 < t) :
    t * A.count X < t * (t - 1) + X := by
  classical
  let L := (A.goodEdges X).filter fun i => A i < t
  let H := (A.goodEdges X).filter fun i => t ≤ A i
  have hL : L.card ≤ t - 1 := by
    calc
      L.card ≤ (Finset.range (t - 1)).card := by
        apply Finset.card_le_card
        intro i hi
        have hi' : A i < t := (Finset.mem_filter.mp hi).2
        have hai := A.index_succ_le i
        exact Finset.mem_range.mpr (by omega)
      _ = t - 1 := Finset.card_range _
  have hsplit : L.card + H.card = A.count X := by
    simpa only [L, H, Nat.not_lt, IncreasingSequence.count] using
      Finset.card_filter_add_card_filter_not (s := A.goodEdges X) (fun i => A i < t)
  by_cases hH : H.Nonempty
  · have hex : ∃ i, t ≤ A i := ⟨t, (Nat.le_succ t).trans (A.index_succ_le t)⟩
    let k := Nat.find hex
    have hak : t ≤ A k := Nat.find_spec hex
    have hs : ∀ i ∈ H, k ≤ i ∧ i < X + 1 := by
      intro i hi
      obtain ⟨hiG, hit⟩ := Finset.mem_filter.mp hi
      have hiX : i < X := IncreasingSequence.edge_lt_threshold
        (IncreasingSequence.mem_goodEdges_iff.mp hiG)
      exact ⟨Nat.find_min' hex hit, by omega⟩
    obtain ⟨j, hj⟩ := hH
    have hkX : k ≤ X + 1 := le_trans (hs j hj).1 (Nat.le_of_lt (hs j hj).2)
    have hXR : (0 : ℝ) < X := by exact_mod_cast hX
    have htR : (0 : ℝ) < t := by exact_mod_cast ht
    have hmass : (H.card : ℝ) / X < 1 / (t : ℝ) := by
      calc
        (H.card : ℝ) / X = ∑ i ∈ H, (1 : ℝ) / X := by
          simp [div_eq_mul_inv]
        _ ≤ ∑ i ∈ H, (1 : ℝ) / A.edgeLcm i := by
          apply Finset.sum_le_sum
          intro i hi
          have hiG : i ∈ A.goodEdges X := (Finset.mem_filter.mp hi).1
          have hiX := IncreasingSequence.mem_goodEdges_iff.mp hiG
          have hp : 0 < A.edgeLcm i := Nat.lcm_pos (A.positive i) (A.positive (i + 1))
          exact one_div_le_one_div_of_le (by exact_mod_cast hp) (by exact_mod_cast hiX)
        _ ≤ ∑ i ∈ H, ((1 : ℝ) / A i - 1 / A (i + 1)) :=
          Finset.sum_le_sum fun i _ => A.reciprocal_edgeLcm_le_drop i
        _ ≤ (1 : ℝ) / A k - 1 / A (X + 1) := A.sum_subset_drops_le H hkX hs
        _ < (1 : ℝ) / A k := by
          exact sub_lt_self _ (one_div_pos.2 (by exact_mod_cast A.positive (X + 1)))
        _ ≤ (1 : ℝ) / t := one_div_le_one_div_of_le htR (by exact_mod_cast hak)
    have hmulR : (H.card : ℝ) * t < X := by
      have hh := (div_lt_div_iff₀ hXR htR).1 hmass
      simpa only [one_mul] using hh
    have hmul : H.card * t < X := by exact_mod_cast hmulR
    have hlmul := Nat.mul_le_mul_left t hL
    nlinarith
  · have hzero : H.card = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty.mp hH]
      simp
    have hlmul := Nat.mul_le_mul_left t hL
    nlinarith

/-- At a positive square, the strict finite estimate saves two from 2 sqrt(X). -/
theorem square_threshold (A : IncreasingSequence) (m : ℕ) (hm : 0 < m) :
    A.count (m ^ 2) + 2 ≤ 2 * m := by
  have h := strict_cutoff A (m ^ 2) m (pow_pos hm _) hm
  have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
  have he : m * (m - 1) + m = m * m := by
    calc
      m * (m - 1) + m = m * (m - 1 + 1) := by ring
      _ = m * m := by rw [hm1]
  by_contra hnot
  have hc : 2 * m ≤ A.count (m ^ 2) + 1 := by omega
  have hmul := Nat.mul_le_mul_left m hc
  nlinarith

end Erdos440Cutoff

#print axioms Erdos440Cutoff.strict_cutoff
#print axioms Erdos440Cutoff.square_threshold
