/-
New real-threshold bridge and integration: x2515102083, with ChatGPT assistance.
The imported natural-threshold solution is by the authors credited in ATTRIBUTION.md.
This file does not claim the imported mathematics or formalization as new work.
-/
import ErdosProblems.Erdos440

noncomputable section
open Filter Finset Erdos440
open scoped Topology BigOperators

namespace Erdos440Real

/-- A finite enumeration of all qualifying indices, not a truncated approximation. -/
def realGoodEdges (A : IncreasingSequence) (x : ℝ) : Finset ℕ :=
  (Finset.range (⌊x⌋₊ + 1)).filter fun i => (A.edgeLcm i : ℝ) ≤ x

def realCount (A : IncreasingSequence) (x : ℝ) : ℕ :=
  (realGoodEdges A x).card

def realRatio (A : IncreasingSequence) (x : ℝ) : ℝ :=
  (realCount A x : ℝ) / Real.sqrt x

/-- Every qualifying index is included, even though the definition is finite. -/
theorem mem_realGoodEdges_iff (A : IncreasingSequence) (x : ℝ) (i : ℕ) :
    i ∈ realGoodEdges A x ↔ (A.edgeLcm i : ℝ) ≤ x := by
  simp only [realGoodEdges, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact And.right
  · intro h
    have hx : 0 ≤ x := (Nat.cast_nonneg (A.edgeLcm i)).trans h
    have hn : A.edgeLcm i ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx).2 h
    have hi := IncreasingSequence.edge_lt_threshold hn
    exact ⟨by omega, h⟩

theorem qualifying_indices_finite (A : IncreasingSequence) (x : ℝ) :
    {i : ℕ | (A.edgeLcm i : ℝ) ≤ x}.Finite := by
  have heq : {i : ℕ | (A.edgeLcm i : ℝ) ≤ x} =
      (realGoodEdges A x : Set ℕ) := by
    ext i
    exact (mem_realGoodEdges_iff A x i).symm
  rw [heq]
  exact Finset.finite_toSet _

theorem realCount_eq_ncard (A : IncreasingSequence) (x : ℝ) :
    realCount A x = {i : ℕ | (A.edgeLcm i : ℝ) ≤ x}.ncard := by
  have heq : {i : ℕ | (A.edgeLcm i : ℝ) ≤ x} =
      (realGoodEdges A x : Set ℕ) := by
    ext i
    exact (mem_realGoodEdges_iff A x i).symm
  simp [heq, realCount]

theorem realCount_eq_count_floor (A : IncreasingSequence) {x : ℝ} (hx : 0 ≤ x) :
    realCount A x = A.count ⌊x⌋₊ := by
  have heq : realGoodEdges A x = A.goodEdges ⌊x⌋₊ := by
    ext i
    rw [mem_realGoodEdges_iff, IncreasingSequence.mem_goodEdges_iff]
    exact (Nat.le_floor_iff hx).symm
  rw [realCount, IncreasingSequence.count, heq]

theorem realCount_natCast (A : IncreasingSequence) (n : ℕ) :
    realCount A (n : ℝ) = A.count n := by
  rw [realCount_eq_count_floor A (Nat.cast_nonneg n), Nat.floor_natCast]

theorem realRatio_natCast (A : IncreasingSequence) (n : ℕ) :
    realRatio A (n : ℝ) = A.ratio n := by
  simp only [realRatio, realCount_natCast, IncreasingSequence.ratio]

/-- Exact cofinality, in both directions, rather than only a subsequence estimate. -/
theorem map_floor_atTop :
    Filter.map (Nat.floor : ℝ → ℕ) (atTop : Filter ℝ) = (atTop : Filter ℕ) := by
  ext s
  change (∀ᶠ x : ℝ in atTop, ⌊x⌋₊ ∈ s) ↔ (∀ᶠ n : ℕ in atTop, n ∈ s)
  constructor
  · intro h
    have hn : ∀ᶠ n : ℕ in atTop, ⌊(n : ℝ)⌋₊ ∈ s :=
      tendsto_natCast_atTop_atTop.eventually h
    simpa only [Nat.floor_natCast] using hn
  · intro h
    obtain ⟨N, hN⟩ := eventually_atTop.1 h
    filter_upwards [eventually_ge_atTop (N : ℝ)] with x hx
    exact hN _ ((Nat.le_floor_iff ((Nat.cast_nonneg N).trans hx)).2 hx)

def floorRatio (A : IncreasingSequence) (x : ℝ) : ℝ := A.ratio ⌊x⌋₊
def factor (x : ℝ) : ℝ := Real.sqrt (⌊x⌋₊ : ℝ) / Real.sqrt x

lemma natRatio_nonneg (A : IncreasingSequence) (n : ℕ) : 0 ≤ A.ratio n :=
  div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)

lemma natRatio_le_four (A : IncreasingSequence) (n : ℕ) : A.ratio n ≤ 4 := by
  by_cases hn : n = 0
  · subst n
    simp [IncreasingSequence.ratio]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hn
    have hs : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      simpa using Real.sqrt_le_sqrt hn1'
    have hns : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := by
      apply Real.le_sqrt_of_sq_le
      exact_mod_cast Nat.sqrt_le' n
    have hc : (A.count n : ℝ) ≤ 2 * (Nat.sqrt n : ℝ) + 2 := by
      exact_mod_cast A.count_le_two_sqrt_add_two n
    unfold IncreasingSequence.ratio
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hs)).2
    nlinarith

lemma floorRatio_nonneg (A : IncreasingSequence) (x : ℝ) : 0 ≤ floorRatio A x :=
  natRatio_nonneg A _

lemma floorRatio_le_four (A : IncreasingSequence) (x : ℝ) : floorRatio A x ≤ 4 :=
  natRatio_le_four A _

lemma factor_nonneg (x : ℝ) : 0 ≤ factor x :=
  div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

lemma factor_le_one {x : ℝ} (hx : 1 ≤ x) : factor x ≤ 1 := by
  unfold factor
  rw [div_le_one (Real.sqrt_pos.2 (by linarith))]
  exact Real.sqrt_le_sqrt (Nat.floor_le (by linarith : 0 ≤ x))

lemma floor_div_tendsto_one :
    Tendsto (fun x : ℝ => (⌊x⌋₊ : ℝ) / x) atTop (𝓝 1) := by
  have hl : Tendsto (fun x : ℝ => 1 - 1 / x) atTop (𝓝 1) := by
    simpa only [one_div, sub_zero] using
      (tendsto_const_nhds.sub tendsto_inv_atTop_zero :
        Tendsto (fun x : ℝ => 1 - x⁻¹) atTop (𝓝 (1 - 0)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hxp : 0 < x := by linarith
    have hf := Nat.lt_floor_add_one x
    rw [le_div_iff₀ hxp]
    have heq : (1 - 1 / x) * x = x - 1 := by field_simp
    rw [heq]
    linarith
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [div_le_one (by linarith : 0 < x)]
    exact Nat.floor_le (by linarith)

lemma factor_tendsto_one : Tendsto factor atTop (𝓝 1) := by
  have h := (Real.continuous_sqrt.tendsto 1).comp floor_div_tendsto_one
  have heq : factor = fun x : ℝ => Real.sqrt ((⌊x⌋₊ : ℝ) / x) := by
    funext x
    exact (Real.sqrt_div (Nat.cast_nonneg (⌊x⌋₊)) x).symm
  rw [heq]
  simpa only [Function.comp_def, Real.sqrt_one] using h

lemma realRatio_product (A : IncreasingSequence) {x : ℝ} (hx : 1 ≤ x) :
    realRatio A x = floorRatio A x * factor x := by
  have hx0 : 0 ≤ x := by linarith
  have hf : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).2 (by simpa using hx)
  have hfpos : 0 < (⌊x⌋₊ : ℝ) := by exact_mod_cast hf
  have hfn : Real.sqrt (⌊x⌋₊ : ℝ) ≠ 0 := (Real.sqrt_pos.2 hfpos).ne'
  have hxn : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  rw [realRatio, realCount_eq_count_floor A hx0, floorRatio, IncreasingSequence.ratio, factor]
  field_simp

lemma realRatio_eventually_eq (A : IncreasingSequence) :
    realRatio A =ᶠ[atTop] floorRatio A * factor := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  exact realRatio_product A hx

lemma limsup_floorRatio (A : IncreasingSequence) :
    (atTop : Filter ℝ).limsup (floorRatio A) = (atTop : Filter ℕ).limsup A.ratio := by
  change Filter.limsSup (Filter.map (A.ratio ∘ Nat.floor) (atTop : Filter ℝ)) =
    Filter.limsSup (Filter.map A.ratio (atTop : Filter ℕ))
  rw [← Filter.map_map, map_floor_atTop]

lemma liminf_floorRatio (A : IncreasingSequence) :
    (atTop : Filter ℝ).liminf (floorRatio A) = (atTop : Filter ℕ).liminf A.ratio := by
  change Filter.limsInf (Filter.map (A.ratio ∘ Nat.floor) (atTop : Filter ℝ)) =
    Filter.limsInf (Filter.map A.ratio (atTop : Filter ℕ))
  rw [← Filter.map_map, map_floor_atTop]

/-- The real-threshold limsup equals, rather than merely bounds, the natural one. -/
theorem real_limsup_eq_nat (A : IncreasingSequence) :
    (atTop : Filter ℝ).limsup (realRatio A) = (atTop : Filter ℕ).limsup A.ratio := by
  have hu0 : 0 ≤ᶠ[atTop] floorRatio A := Eventually.of_forall (floorRatio_nonneg A)
  have hv0 : 0 ≤ᶠ[atTop] factor := Eventually.of_forall factor_nonneg
  have hu : IsBoundedUnder (· ≤ ·) (atTop : Filter ℝ) (floorRatio A) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall (floorRatio_le_four A))
  have hv : IsBoundedUnder (· ≤ ·) (atTop : Filter ℝ) factor :=
    isBoundedUnder_of_eventually_le
      ((eventually_ge_atTop (1 : ℝ)).mono fun _ hx => factor_le_one hx)
  have heq : (atTop : Filter ℝ).limsup (floorRatio A * factor) =
      (atTop : Filter ℝ).limsup (floorRatio A) := by
    apply le_antisymm
    · simpa only [factor_tendsto_one.limsup_eq, mul_one] using
        (limsup_mul_le hu0.frequently hu hv0 hv)
    · simpa only [factor_tendsto_one.liminf_eq, mul_one] using
        (le_limsup_mul hu0.frequently hu hv0 hv)
  rw [Filter.limsup_congr (realRatio_eventually_eq A), heq, limsup_floorRatio]

/-- The real-threshold liminf is also preserved; passing only to a subsequence is insufficient. -/
theorem real_liminf_eq_nat (A : IncreasingSequence) :
    (atTop : Filter ℝ).liminf (realRatio A) = (atTop : Filter ℕ).liminf A.ratio := by
  have hu0 : 0 ≤ᶠ[atTop] floorRatio A := Eventually.of_forall (floorRatio_nonneg A)
  have hv0 : 0 ≤ᶠ[atTop] factor := Eventually.of_forall factor_nonneg
  have hu : IsBoundedUnder (· ≤ ·) (atTop : Filter ℝ) (floorRatio A) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall (floorRatio_le_four A))
  have hv : IsBoundedUnder (· ≤ ·) (atTop : Filter ℝ) factor :=
    isBoundedUnder_of_eventually_le
      ((eventually_ge_atTop (1 : ℝ)).mono fun _ hx => factor_le_one hx)
  have heq : (atTop : Filter ℝ).liminf (factor * floorRatio A) =
      (atTop : Filter ℝ).liminf (floorRatio A) := by
    apply le_antisymm
    · simpa only [factor_tendsto_one.limsup_eq, one_mul] using
        (liminf_mul_le hv0 hv hu0 hu.isCoboundedUnder_ge)
    · simpa only [factor_tendsto_one.liminf_eq, one_mul] using
        (le_liminf_mul hv0 hv hu0 hu.isCoboundedUnder_ge)
  rw [Filter.liminf_congr (realRatio_eventually_eq A), mul_comm, heq, liminf_floorRatio]

theorem realCount_isBigO_sqrt (A : IncreasingSequence) :
    (fun x : ℝ => (realCount A x : ℝ)) =O[atTop] Real.sqrt := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨4, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hr : realRatio A x ≤ 4 := by
    rw [realRatio_product A hx]
    calc
      floorRatio A x * factor x ≤ floorRatio A x * 1 :=
        mul_le_mul_of_nonneg_left (factor_le_one hx) (floorRatio_nonneg A x)
      _ ≤ 4 := by simpa using floorRatio_le_four A x
  have hc : (0 : ℝ) ≤ realCount A x := Nat.cast_nonneg _
  simp only [Real.norm_eq_abs, abs_of_nonneg hc, abs_of_nonneg (Real.sqrt_nonneg x)]
  exact (div_le_iff₀ (Real.sqrt_pos.2 (by linarith : 0 < x))).1 hr

/-- Complete real-threshold resolution, including the sharp universal limsup and its witness.
The natural-threshold core is explicitly attributed, not asserted as a new solution. -/
theorem complete_original_problem :
    (∀ A : IncreasingSequence,
      (fun x : ℝ => (realCount A x : ℝ)) =O[atTop] Real.sqrt) ∧
    (∀ A : IncreasingSequence, (atTop : Filter ℝ).limsup (realRatio A) ≤ sharpConstant) ∧
    (∃ A : IncreasingSequence, (atTop : Filter ℝ).limsup (realRatio A) = sharpConstant) ∧
    (∀ A : IncreasingSequence, (atTop : Filter ℝ).liminf (realRatio A) ≤ 1) ∧
    (∃ A : IncreasingSequence, (atTop : Filter ℝ).liminf (realRatio A) = 1) := by
  refine ⟨realCount_isBigO_sqrt, ?_, ?_, ?_, ?_⟩
  · intro A
    rw [real_limsup_eq_nat]
    exact Erdos440.limsup_ratio_le_sharpConstant A
  · refine ⟨sharpSequenceWitness, ?_⟩
    rw [real_limsup_eq_nat]
    exact sharpSequenceWitness_limsup_eq_sharpConstant
  · intro A
    rw [real_liminf_eq_nat]
    exact Erdos440.liminf_ratio_le_one A
  · refine ⟨positiveNaturals, ?_⟩
    rw [real_liminf_eq_nat]
    exact positiveNaturals_liminf_eq_one

end Erdos440Real

#print axioms Erdos440Real.mem_realGoodEdges_iff
#print axioms Erdos440Real.qualifying_indices_finite
#print axioms Erdos440Real.realCount_eq_ncard
#print axioms Erdos440Real.realCount_eq_count_floor
#print axioms Erdos440Real.map_floor_atTop
#print axioms Erdos440Real.real_limsup_eq_nat
#print axioms Erdos440Real.real_liminf_eq_nat
#print axioms Erdos440Real.complete_original_problem
