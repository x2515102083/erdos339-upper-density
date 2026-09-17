/-
Copyright (c) 2026 x2515102083. Released under the Apache 2.0 license.
Formalization development: x2515102083 with ChatGPT (GPT-6 Astra Pro).
Mathematical construction: Clemen, Dumitrescu and Liu, arXiv:2505.04283,
Section 5 (2025). This file targets counterexamples for every n >= 4.
The classification definitions and statement are adapted without changing
mathematical content from Formal Conjectures, commit
 d5ba143cc2fafd48cc6d5b6320a3aab287c38df7, ErdosProblems/958.lean,
Copyright 2026 The Formal Conjectures Authors, Apache License 2.0.
-/
import Geometry
import Counting

set_option maxHeartbeats 1600000
set_option maxRecDepth 2000

namespace Erdos958

open Erdos958Large

def IsEquidistantOnLine (A : Finset Point) : Prop :=
  ∃ a v : Point, v ≠ 0 ∧ (A : Set Point) =
    {x | ∃ i : ℕ, i < A.card ∧ x = a + (i : ℝ) • v}

def IsEquidistantOnCircle (A : Finset Point) : Prop :=
  ∃ (c : Point) (r θ α : ℝ), 0 < r ∧ α ≠ 0 ∧ (A : Set Point) =
    {x | ∃ i : ℕ, i < A.card ∧
      x = c + r • (!₂[Real.cos (θ + (i : ℝ) * α), Real.sin (θ + (i : ℝ) * α)])}

lemma common_line_of_equidistant {A : Finset Point} (h : IsEquidistantOnLine A) :
    ∃ a v : Point, ∀ x ∈ A, ∃ s : ℝ, x = a + s • v := by
  obtain ⟨a, v, _, he⟩ := h
  refine ⟨a, v, ?_⟩
  intro x hx
  have hx' : x ∈ (A : Set Point) := hx
  rw [he] at hx'
  obtain ⟨i, _, hi⟩ := hx'
  exact ⟨(i : ℝ), hi⟩

lemma common_circle_of_equidistant {A : Finset Point} (h : IsEquidistantOnCircle A) :
    ∃ c : Point, ∃ r : ℝ, ∀ x ∈ A, dist x c = r := by
  obtain ⟨c, r, θ, α, hr, _, he⟩ := h
  refine ⟨c, r, ?_⟩
  intro x hx
  have hx' : x ∈ (A : Set Point) := hx
  rw [he] at hx'
  obtain ⟨i, _, hi⟩ := hx'
  change x = c + r • unit (θ + (i : ℝ) * α) at hi
  rw [hi, dist_eq_norm]
  have hv : c + r • unit (θ + (i : ℝ) * α) - c = r • unit (θ + (i : ℝ) * α) := by abel
  rw [hv, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  have hu : ‖unit (θ + (i : ℝ) * α)‖ = 1 := by
    simpa only [dist_zero_right] using unit_norm (θ + (i : ℝ) * α)
  rw [hu, mul_one]

end Erdos958

namespace Erdos958Large

noncomputable def step (m : ℕ) : ℝ := Real.pi / (6 * ((m : ℝ) + 1))

lemma step_pos (m : ℕ) : 0 < step m := by
  unfold step
  exact div_pos Real.pi_pos (by positivity)

lemma step_scale (m : ℕ) : ((m : ℝ) + 1) * step m = Real.pi / 6 := by
  unfold step
  have hm : (m : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
  field_simp [hm]
  <;> ring

lemma step_mul_lt (m : ℕ) : (m : ℝ) * step m < Real.pi / 3 := by
  have hs := step_scale m
  have ht := step_pos m
  nlinarith [Real.pi_pos]

lemma step_lt_pi (m : ℕ) : step m < Real.pi := by
  have hs := step_scale m
  have ht := step_pos m
  have hn : 0 ≤ (m : ℝ) * step m := mul_nonneg (Nat.cast_nonneg _) ht.le
  nlinarith [Real.pi_pos]

lemma step_short (m : ℕ) {k : ℕ} (hk : k ≤ m) : (k : ℝ) * step m < Real.pi / 3 := by
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (step_pos m).le).trans_lt
    (step_mul_lt m)

lemma step_bound (m : ℕ) {k : ℕ} (hk : k ≤ m) : (k : ℝ) * step m ≤ Real.pi := by
  have h := step_short m hk
  linarith [Real.pi_pos]

noncomputable def planarConfig (m : ℕ) : ArcConfig Point m where
  c := 0
  p := arc (step m)
  d := chord (step m)
  inj := by
    intro i j hi hj he
    exact arc_injOn (step_pos m) (step_bound m (le_refl m)) hi hj he
  ne := by
    intro i _
    exact unit_ne_zero _
  radial := by
    intro i _
    rw [dist_comm]
    exact unit_norm _
  chords := by
    intro i j hij _
    exact arc_dist (step m) hij.le
  dinj := by
    intro i j _ hi _ hj he
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact ((chord_strict (step_pos m) hij (step_bound m hj.le)).ne he).elim
    · rfl
    · exact ((chord_strict (step_pos m) hji (step_bound m hi.le)).ne he.symm).elim
  dne := by
    intro i _ hi
    exact ne_of_lt (chord_lt_one (step_pos m) (step_short m hi.le))

lemma center_mem_planar (m : ℕ) : (0 : Point) ∈ (planarConfig m).points :=
  (planarConfig m).center_mem

lemma zero_angle_mem {m : ℕ} (hm : 2 ≤ m) : unit 0 ∈ (planarConfig m).points := by
  have h := (planarConfig m).arc_mem (i := 1) (by omega)
  change arc (step m) 1 ∈ (planarConfig m).points at h
  simpa [arc] using h

lemma positive_angle_mem {m : ℕ} (hm : 3 ≤ m) : unit (step m) ∈ (planarConfig m).points := by
  have h := (planarConfig m).arc_mem (i := 2) (by omega)
  change arc (step m) 2 ∈ (planarConfig m).points at h
  simpa [arc] using h

lemma negative_angle_mem {m : ℕ} (hm : 1 ≤ m) : unit (-step m) ∈ (planarConfig m).points := by
  have h := (planarConfig m).arc_mem (i := 0) (by omega)
  change arc (step m) 0 ∈ (planarConfig m).points at h
  simpa [arc] using h

lemma planar_not_line {m : ℕ} (hm : 3 ≤ m) :
    ¬ Erdos958.IsEquidistantOnLine (planarConfig m).points := by
  intro h
  obtain ⟨a, v, hv⟩ := Erdos958.common_line_of_equidistant h
  obtain ⟨x, hx⟩ := hv 0 (center_mem_planar m)
  obtain ⟨y, hy⟩ := hv (unit 0) (zero_angle_mem (by omega))
  obtain ⟨z, hz⟩ := hv (unit (step m)) (positive_angle_mem hm)
  have hs : Real.sin (step m) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (step_pos m) (step_lt_pi m))
  exact no_common_line hs ⟨a, v, x, y, z, hx, hy, hz⟩

lemma planar_not_circle {m : ℕ} (hm : 3 ≤ m) :
    ¬ Erdos958.IsEquidistantOnCircle (planarConfig m).points := by
  intro h
  obtain ⟨c, r, hr⟩ := Erdos958.common_circle_of_equidistant h
  have hc : Real.cos (step m) < 1 := by
    simpa using Real.cos_lt_cos_of_nonneg_of_le_pi (show (0 : ℝ) ≤ 0 by rfl)
      (step_lt_pi m).le (step_pos m)
  exact no_common_circle hc ⟨c, r, hr 0 (center_mem_planar m),
    hr (unit 0) (zero_angle_mem (by omega)),
    hr (unit (step m)) (positive_angle_mem hm),
    hr (unit (-step m)) (negative_angle_mem (by omega))⟩

theorem counterexample_by_arcs (m : ℕ) (hm : 3 ≤ m) :
    ∃ A : Finset Point, A.card = m + 1 ∧ (distanceSet A).card = m ∧
      (distanceSet A).image (distanceMultiplicity A) = Finset.Icc 1 m ∧
      ¬ Erdos958.IsEquidistantOnLine A ∧ ¬ Erdos958.IsEquidistantOnCircle A := by
  exact ⟨(planarConfig m).points, (planarConfig m).card_points,
    (planarConfig m).card_distances (by omega),
    (planarConfig m).multiplicity_image (by omega), planar_not_line hm, planar_not_circle hm⟩

theorem counterexample_every_n (n : ℕ) (hn : 4 ≤ n) :
    ∃ A : Finset Point, A.card = n ∧
      ((distanceSet A).card = n - 1 ∧
        (distanceSet A).image (distanceMultiplicity A) = Finset.Icc 1 (n - 1)) ∧
      ¬ Erdos958.IsEquidistantOnLine A ∧ ¬ Erdos958.IsEquidistantOnCircle A := by
  obtain ⟨A, ha, hd, hf, hl, hc⟩ := counterexample_by_arcs (n - 1) (by omega)
  exact ⟨A, by omega, ⟨hd, hf⟩, hl, hc⟩

theorem not_eventual_classification :
    ¬ ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset Point, A.card = n →
      (((distanceSet A).card = n - 1 ∧
          (distanceSet A).image (distanceMultiplicity A) = Finset.Icc 1 (n - 1)) →
        (Erdos958.IsEquidistantOnLine A ∨ Erdos958.IsEquidistantOnCircle A)) := by
  rintro ⟨N, hN⟩
  obtain ⟨A, ha, hp, hl, hc⟩ := counterexample_every_n (max N 4) (le_max_right N 4)
  exact (hN (max N 4) (le_max_left N 4) A ha hp).elim hl hc

end Erdos958Large

namespace Erdos958

open Erdos958Large

/-- The original eventual-classification statement, with `answer(False)` resolved to `False`. -/
theorem erdos_958 : False ↔
    ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset Point, A.card = n →
      (((distanceSet A).card = n - 1 ∧
          (distanceSet A).image (distanceMultiplicity A) = Finset.Icc 1 (n - 1)) →
        (IsEquidistantOnLine A ∨ IsEquidistantOnCircle A)) := by
  constructor
  · intro h
    exact h.elim
  · exact not_eventual_classification

end Erdos958

#print axioms Erdos958Large.counterexample_every_n
#print axioms Erdos958Large.not_eventual_classification
#print axioms Erdos958.erdos_958
