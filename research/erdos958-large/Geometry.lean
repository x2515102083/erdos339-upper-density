/-
Copyright (c) 2026 x2515102083. Released under the Apache 2.0 license.
Formalization development: x2515102083 with ChatGPT (GPT-6 Astra Pro).
Mathematical construction: Clemen, Dumitrescu and Liu, arXiv:2505.04283,
Section 5 (2025). This research file alone is not a full solution or award claim.
-/
import Mathlib

set_option maxHeartbeats 1600000
set_option maxRecDepth 2000

open Finset

namespace Erdos958Large

abbrev Point := EuclideanSpace ℝ (Fin 2)
noncomputable def unit (t : ℝ) : Point := !₂[Real.cos t, Real.sin t]
noncomputable def arc (t : ℝ) (i : ℕ) : Point := unit (((i : ℝ) - 1) * t)
noncomputable def chord (t : ℝ) (k : ℕ) : ℝ := dist (unit 0) (unit ((k : ℝ) * t))

lemma dist_sq (p q : Point) :
    dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two,
    Real.sq_sqrt, add_nonneg (sq_nonneg _) (sq_nonneg _)]

lemma unit_dist_sq (a b : ℝ) :
    dist (unit a) (unit b) ^ 2 = 2 - 2 * Real.cos (a - b) := by
  rw [dist_sq]
  simp only [unit, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq b]

lemma unit_norm (a : ℝ) : dist (unit a) 0 = 1 := by
  have h := dist_sq (unit a) 0
  simp [unit] at h
  have hn := dist_nonneg (x := unit a) (y := (0 : Point))
  nlinarith [Real.sin_sq_add_cos_sq a]

lemma unit_ne_zero (a : ℝ) : unit a ≠ 0 := by
  intro h
  have := unit_norm a
  simp [h] at this

lemma chord_zero (t : ℝ) : chord t 0 = 0 := by simp [chord]
lemma chord_nonneg (t : ℝ) (k : ℕ) : 0 ≤ chord t k := dist_nonneg
lemma chord_sq (t : ℝ) (k : ℕ) :
    chord t k ^ 2 = 2 - 2 * Real.cos ((k : ℝ) * t) := by
  simpa [chord] using unit_dist_sq 0 ((k : ℝ) * t)

lemma arc_dist (t : ℝ) {i j : ℕ} (hij : i ≤ j) :
    dist (arc t i) (arc t j) = chord t (j - i) := by
  have h := unit_dist_sq (((i : ℝ) - 1) * t) (((j : ℝ) - 1) * t)
  have he : ((i : ℝ) - 1) * t - ((j : ℝ) - 1) * t = -((j - i : ℕ) : ℝ) * t := by
    rw [Nat.cast_sub hij]
    ring
  rw [he, neg_mul, Real.cos_neg] at h
  have hc := chord_sq t (j - i)
  have hn := chord_nonneg t (j - i)
  have hd := dist_nonneg (x := arc t i) (y := arc t j)
  change dist (arc t i) (arc t j) ^ 2 = _ at h
  nlinarith

lemma chord_strict {t : ℝ} (ht : 0 < t) {i j : ℕ}
    (hij : i < j) (hj : (j : ℝ) * t ≤ Real.pi) : chord t i < chord t j := by
  have hi0 : 0 ≤ (i : ℝ) * t := mul_nonneg (Nat.cast_nonneg _) ht.le
  have hj0 : 0 ≤ (j : ℝ) * t := mul_nonneg (Nat.cast_nonneg _) ht.le
  have hij' : (i : ℝ) * t < (j : ℝ) * t :=
    mul_lt_mul_of_pos_right (by exact_mod_cast hij) ht
  have hc := Real.strictAntiOn_cos ⟨hi0, hij'.le.trans hj⟩ ⟨hj0, hj⟩ hij'
  have hsi := chord_sq t i
  have hsj := chord_sq t j
  have hni := chord_nonneg t i
  have hnj := chord_nonneg t j
  nlinarith

lemma chord_pos {t : ℝ} (ht : 0 < t) {k : ℕ} (hk : 0 < k)
    (hkp : (k : ℝ) * t ≤ Real.pi) : 0 < chord t k := by
  simpa [chord_zero] using chord_strict ht hk hkp

lemma chord_lt_one {t : ℝ} (ht : 0 < t) {k : ℕ}
    (hk : (k : ℝ) * t < Real.pi / 3) : chord t k < 1 := by
  have hkn : 0 ≤ (k : ℝ) * t := mul_nonneg (Nat.cast_nonneg _) ht.le
  have hp : 0 < Real.pi := Real.pi_pos
  have hc := Real.strictAntiOn_cos
    (show (k : ℝ) * t ∈ Set.Icc (0 : ℝ) Real.pi by constructor; exact hkn; linarith)
    (show Real.pi / 3 ∈ Set.Icc (0 : ℝ) Real.pi by constructor <;> linarith) hk
  rw [Real.cos_pi_div_three] at hc
  have hs := chord_sq t k
  have hn := chord_nonneg t k
  nlinarith

lemma arc_injOn {m : ℕ} {t : ℝ} (ht : 0 < t)
    (hm : (m : ℝ) * t ≤ Real.pi) : Set.InjOn (arc t) (Set.Iio m) := by
  intro i hi j hj he
  simp only [Set.mem_Iio] at hi hj
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hb : ((j - i : ℕ) : ℝ) * t ≤ Real.pi := by
      have : j - i ≤ m := by omega
      exact (mul_le_mul_of_nonneg_right (by exact_mod_cast this) ht.le).trans hm
    have hp := chord_pos ht (show 0 < j - i by omega) hb
    have hd := arc_dist t hij.le
    rw [he, dist_self] at hd
    linarith
  · rfl
  · have hb : ((i - j : ℕ) : ℝ) * t ≤ Real.pi := by
      have : i - j ≤ m := by omega
      exact (mul_le_mul_of_nonneg_right (by exact_mod_cast this) ht.le).trans hm
    have hp := chord_pos ht (show 0 < i - j by omega) hb
    have hd := arc_dist t hji.le
    rw [he, dist_self] at hd
    linarith

lemma no_common_circle {t : ℝ} (hc : Real.cos t < 1) :
    ¬ ∃ c : Point, ∃ r : ℝ,
      dist (0 : Point) c = r ∧ dist (unit 0) c = r ∧
      dist (unit t) c = r ∧ dist (unit (-t)) c = r := by
  rintro ⟨c, r, h0, h1, hp, hn⟩
  have e0 := dist_sq (0 : Point) c
  have e1 := dist_sq (unit 0) c
  have ep := dist_sq (unit t) c
  have en := dist_sq (unit (-t)) c
  rw [h0] at e0
  rw [h1] at e1
  rw [hp] at ep
  rw [hn] at en
  simp [unit] at e0 e1 ep en
  have hc0 : 2 * c 0 = 1 := by nlinarith [e0, e1]
  have he : 2 * c 0 * Real.cos t = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  nlinarith

lemma no_common_line {t : ℝ} (hs : Real.sin t ≠ 0) :
    ¬ ∃ a v : Point, ∃ x y z : ℝ,
      (0 : Point) = a + x • v ∧ unit 0 = a + y • v ∧ unit t = a + z • v := by
  rintro ⟨a, v, x, y, z, h0, h1, ht⟩
  have h00 := congrArg (fun p : Point => p 0) h0
  have h01 := congrArg (fun p : Point => p 1) h0
  have h10 := congrArg (fun p : Point => p 0) h1
  have h11 := congrArg (fun p : Point => p 1) h1
  have ht1 := congrArg (fun p : Point => p 1) ht
  simp [unit] at h00 h01 h10 h11 ht1
  have hv0 : (y - x) * v 0 = 1 := by nlinarith
  have hv1 : (y - x) * v 1 = 0 := by nlinarith
  have hyx : y - x ≠ 0 := by intro h; rw [h, zero_mul] at hv0; norm_num at hv0
  have hv : v 1 = 0 := (mul_eq_zero.mp hv1).resolve_left hyx
  apply hs
  rw [hv] at h01 ht1
  nlinarith

#print axioms arc_injOn
#print axioms no_common_circle
#print axioms no_common_line

-- Interface probes for the following finite-pair counting file.
#check Sym2.eq_iff
#check Sym2.eq_iff_eq_or_eq
#check Finset.mk_mem_sym2_iff
#check Finset.card_image_iff
#check Finset.filter_image
#check Finset.mem_offDiag
#check Real.cos_lt_cos_of_nonneg_of_le_pi
#check Real.sin_pos_of_pos_of_lt_pi

end Erdos958Large
