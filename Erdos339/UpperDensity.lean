import Erdos339.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Erdős 339: the upper-density clause

The mathematical finite-count argument is due to Norbert Hegyvári, François
Hennecart and Alain Plagne, J. Reine Angew. Math. 560 (2003), 199–220.
`Erdos339.Finite` retains the finite machinery from plby/lean-proofs, formalized
by Codex and GPT-5.6 Sol. The limsup transfer and upper-density endpoint below
are a new AI-assisted extension, not an upstream theorem or attribution.
-/

open Filter Function
open scoped Pointwise BigOperators Topology

namespace Erdos339

private lemma partialDensity_nonneg (S : Set ℕ) (N : ℕ) :
    0 ≤ S.partialDensity Set.univ N := by
  rw [partialDensity_nat_eq_prefix_card]
  positivity

private lemma density_bounded (S : Set ℕ) :
    atTop.IsBoundedUnder (· ≤ ·) (fun N : ℕ ↦ S.partialDensity Set.univ N) :=
  ⟨1, Filter.eventually_map.mpr (Eventually.of_forall (Set.partialDensity_le_one S Set.univ))⟩

private lemma density_cobounded (S : Set ℕ) :
    atTop.IsCoboundedUnder (· ≤ ·) (fun N : ℕ ↦ S.partialDensity Set.univ N) :=
  isCoboundedUnder_le_of_le atTop (partialDensity_nonneg S)

lemma upperDensity_nonneg (S : Set ℕ) : 0 ≤ S.upperDensity := by
  apply le_limsup_of_le (density_bounded S)
  intro b hb
  obtain ⟨N, hN⟩ := hb.exists
  exact (partialDensity_nonneg S N).trans hN

/-- Finite subsets of the natural numbers have upper density zero. -/
lemma upperDensity_eq_zero_of_finite {S : Set ℕ} (hS : S.Finite) :
    S.upperDensity = 0 := by
  classical
  have hcard (N : ℕ) : (prefixFinset S N).card ≤ hS.toFinset.card := by
    apply Finset.card_le_card
    intro n hn
    exact hS.mem_toFinset.mpr (mem_prefixFinset.mp hn).1
  have hlim : Tendsto (fun N : ℕ ↦ S.partialDensity Set.univ N) atTop (𝓝 0) := by
    refine tendsto_const_nhds.squeeze
      (tendsto_natCast_atTop_atTop.const_div_atTop (hS.toFinset.card : ℝ))
      (partialDensity_nonneg S) ?_
    intro N
    change S.partialDensity Set.univ N ≤ (hS.toFinset.card : ℝ) / N
    rw [partialDensity_nat_eq_prefix_card]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcard N) (Nat.cast_nonneg N)
  exact hlim.limsup_eq

/-- A finite summand set has a finite iterated sumset, including the zero-fold sum. -/
private lemma finite_nsmul {A : Set ℕ} (hA : A.Finite) (r : ℕ) :
    (r • A).Finite := by
  obtain ⟨M, hM⟩ := hA.bddAbove
  apply (Set.finite_le_nat (r * M)).subset
  intro n hn
  obtain ⟨f, hf, rfl⟩ := mem_nsmul_iff_tuple.mp hn
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin r)))
    (fun i _ ↦ hM (hf i))
  simpa using hsum

/-- An eventual prefix count comparison transfers to upper densities, with the
cutoff dilation appearing as an additional multiplicative factor. -/
lemma upperDensity_le_of_eventually_prefix_le {S T : Set ℕ} {q C : ℕ}
    (hq : 0 < q)
    (hcount : ∀ᶠ N in atTop,
      (prefixFinset S N).card ≤ C * (prefixFinset T (q * N)).card) :
    S.upperDensity ≤ (q * C : ℕ) * T.upperDensity := by
  let K : ℝ := (q * C : ℕ)
  let v : ℕ → ℝ := fun N ↦ T.partialDensity Set.univ (q * N)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqtop : Tendsto (fun N : ℕ ↦ q * N) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with N hN
    exact hN.trans (by nlinarith)
  have hv_nonneg (N : ℕ) : 0 ≤ v N := partialDensity_nonneg T (q * N)
  have hv_bdd : atTop.IsBoundedUnder (· ≤ ·) v :=
    ⟨1, Filter.eventually_map.mpr (Eventually.of_forall
      (fun N ↦ Set.partialDensity_le_one T Set.univ (q * N)))⟩
  have hv_cobdd : atTop.IsCoboundedUnder (· ≤ ·) v :=
    isCoboundedUnder_le_of_le atTop hv_nonneg
  have hKv_bdd : atTop.IsBoundedUnder (· ≤ ·) (fun N ↦ K * v N) := by
    refine ⟨K, Filter.eventually_map.mpr (Eventually.of_forall fun N ↦ ?_)⟩
    simpa using mul_le_mul_of_nonneg_left
      (Set.partialDensity_le_one T Set.univ (q * N)) hK
  have hpartial : ∀ᶠ N in atTop,
      S.partialDensity Set.univ N ≤ K * v N := by
    filter_upwards [hcount, eventually_ge_atTop 1] with N hc hN
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    rw [partialDensity_nat_eq_prefix_card]
    calc
      (prefixFinset S N).card / (N : ℝ) ≤
          ((C : ℝ) * (prefixFinset T (q * N)).card) / (N : ℝ) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hc) (Nat.cast_nonneg N)
      _ = K * v N := by
        dsimp [K, v]
        rw [partialDensity_nat_eq_prefix_card]
        push_cast
        field_simp [hqR, hNR]
  have hmono : Monotone (fun x : ℝ ↦ K * x) :=
    fun _ _ h ↦ mul_le_mul_of_nonneg_left h hK
  have hmap : K * atTop.limsup v = atTop.limsup (fun N ↦ K * v N) :=
    hmono.map_limsup_of_continuousAt v
      (continuous_const.mul continuous_id).continuousAt hv_bdd hv_cobdd
  have hsub : atTop.limsup v ≤ T.upperDensity := by
    exact hqtop.limsup_comp_le_limsup
      (isCoboundedUnder_le_of_le _ (partialDensity_nonneg T)) (density_bounded T)
  calc
    S.upperDensity ≤ atTop.limsup (fun N ↦ K * v N) :=
      limsup_le_limsup hpartial (density_cobounded S) hKv_bdd
    _ = K * atTop.limsup v := hmap.symm
    _ ≤ K * T.upperDensity := mul_le_mul_of_nonneg_left hsub hK

/-- Quantitative form of the upper-density implication for infinite `A`. -/
theorem upperDensity_nsmul_le_restrictedSums {A : Set ℕ} {r : ℕ}
    (hA : A.Infinite) :
    (r • A).upperDensity ≤
      ((2 ^ r * (Fintype.card (EqPattern r) * (1 + r * (r + 1)) ^ r) : ℕ) : ℝ) *
        (restrictedSums r A).upperDensity := by
  apply upperDensity_le_of_eventually_prefix_le (by positivity)
  filter_upwards [eventually_large_prefix_of_infinite (r := r) hA] with N hN
  exact nsmul_prefix_le_restricted_prefix hN

/-- Erdős Problem 339, second original clause: positive upper density of the
unrestricted `r`-fold sumset implies positive upper density of distinct sums.
No natural-density limit is assumed. The statement also covers `r = 0`, whose
hypothesis is impossible because the zero-fold sumset is finite. -/
theorem erdos_339_upperDensity {A : Set ℕ} {r : ℕ}
    (h : 0 < (r • A).upperDensity) :
    0 < (restrictedSums r A).upperDensity := by
  have hA : A.Infinite := by
    by_contra hfin
    have hzero := upperDensity_eq_zero_of_finite (finite_nsmul (Set.not_infinite.mp hfin) r)
    linarith
  have hbound := upperDensity_nsmul_le_restrictedSums (r := r) hA
  have hprod := lt_of_lt_of_le h hbound
  by_contra hnot
  have hnonpos := le_of_not_gt hnot
  have hK : (0 : ℝ) ≤
      ((2 ^ r * (Fintype.card (EqPattern r) * (1 + r * (r + 1)) ^ r) : ℕ) : ℝ) := by
    positivity
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hK hnonpos)) hprod

#print axioms erdos_339_upperDensity

end Erdos339
