import Mathlib.Data.Nat.Interval
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
Arithmetic reformulation of Erdős 488, not a proof of the conjecture.
Prepared for x2515102083 with ChatGPT assistance. No novelty is asserted.
The count is literally the number of positive integers at most t divisible
by some member of A. The dilation bridge is proved, not assumed.
-/
namespace Erdos488Rounded

noncomputable def hits (A : Finset ℕ) (t : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 t).filter (fun x => ∃ a ∈ A, a ∣ x)

noncomputable def count (A : Finset ℕ) (t : ℕ) : ℕ := (hits A t).card

def dilate (d : ℕ) (A : Finset ℕ) : Finset ℕ := A.image (d * ·)

def Admissible (A : Finset ℕ) (n : ℕ) : Prop :=
  A.Nonempty ∧ ∀ a ∈ A, 2 ≤ a ∧ a ≤ n

theorem admissible_mono {A : Finset ℕ} {n m : ℕ}
    (hA : Admissible A n) (hnm : n ≤ m) : Admissible A m := by
  exact ⟨hA.1, fun a ha => ⟨(hA.2 a ha).1, (hA.2 a ha).2.trans hnm⟩⟩

theorem count_pos {A : Finset ℕ} {n : ℕ} (hA : Admissible A n) :
    0 < count A n := by
  classical
  obtain ⟨a, ha⟩ := hA.1
  apply Finset.card_pos.mpr
  refine ⟨a, ?_⟩
  simp only [hits, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨by have := (hA.2 a ha).1; omega, (hA.2 a ha).2⟩, a, ha, dvd_rfl⟩

theorem hits_dilate (A : Finset ℕ) {d : ℕ} (hd : 0 < d) (t : ℕ) :
    hits (dilate d A) t = (hits A (t / d)).image (d * ·) := by
  classical
  ext x
  simp only [hits, dilate, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨hx1, hxt⟩, b, ⟨a, ha, rfl⟩, k, hk⟩
    refine ⟨a * k, ⟨⟨?_, ?_⟩, a, ha, ⟨k, rfl⟩⟩, ?_⟩
    · have heq : x = d * (a * k) := by simpa [Nat.mul_assoc] using hk
      nlinarith
    · apply (Nat.le_div_iff_mul_le hd).2
      nlinarith [show x = d * (a * k) by simpa [Nat.mul_assoc] using hk]
    · simpa [Nat.mul_assoc] using hk.symm
  · rintro ⟨y, ⟨⟨hy1, hyt⟩, a, ha, k, hk⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, d * a, ⟨a, ha, rfl⟩, k, ?_⟩
    · nlinarith
    · have := (Nat.le_div_iff_mul_le hd).1 hyt
      nlinarith
    · rw [hk]
      ring

theorem count_dilate (A : Finset ℕ) {d : ℕ} (hd : 0 < d) (t : ℕ) :
    count (dilate d A) t = count A (t / d) := by
  classical
  unfold count
  rw [hits_dilate A hd t]
  apply Finset.card_image_of_injective
  intro x y hxy
  exact Nat.eq_of_mul_eq_mul_left hd hxy

theorem predecessor_div {d : ℕ} (hd : 0 < d) (n : ℕ) :
    (d * (n + 1) - 1) / d = n := by
  have hpos : 1 ≤ d * (n + 1) := by nlinarith
  have hsub := Nat.sub_add_cancel hpos
  apply Nat.le_antisymm
  · have hlt : (d * (n + 1) - 1) / d < n + 1 :=
      (Nat.div_lt_iff_lt_mul hd).2 (by nlinarith)
    omega
  · apply (Nat.le_div_iff_mul_le hd).2
    nlinarith

theorem admissible_dilate_predecessor {A : Finset ℕ} {n d : ℕ}
    (hA : Admissible A n) (hd : 0 < d) :
    Admissible (dilate d A) (d * (n + 1) - 1) := by
  classical
  refine ⟨hA.1.image _, ?_⟩
  intro b hb
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
  have ha2 := (hA.2 a ha).1
  have han := (hA.2 a ha).2
  have hsub := Nat.sub_add_cancel (show 1 ≤ d * (n + 1) by nlinarith)
  constructor <;> nlinarith

/-- A failure of the rounded inequality gives an explicit counterexample
to the original strict inequality after a finite common dilation. -/
theorem lift_rounded_failure {A : Finset ℕ} {n m : ℕ}
    (hA : Admissible A n) (hnm : n < m)
    (hfail : 2 * m * count A n < (n + 1) * count A m) :
    ∃ d N M : ℕ, 0 < d ∧ Admissible (dilate d A) N ∧ N < M ∧
      2 * M * count (dilate d A) N ≤ N * count (dilate d A) M := by
  let d := count A m
  have hd : 0 < d := count_pos (admissible_mono hA hnm.le)
  let N := d * (n + 1) - 1
  let M := d * m
  refine ⟨d, N, M, hd, admissible_dilate_predecessor hA hd, ?_, ?_⟩
  · have hsub := Nat.sub_add_cancel (show 1 ≤ d * (n + 1) by nlinarith)
    dsimp [N, M]
    nlinarith
  · rw [count_dilate A hd, count_dilate A hd]
    have hNdiv : N / d = n := predecessor_div hd n
    have hMdiv : M / d = m := by simp [M, Nat.mul_comm, Nat.ne_of_gt hd]
    rw [hNdiv, hMdiv]
    have hgap : 2 * m * count A n + 1 ≤ (n + 1) * d := by
      change 2 * m * count A n + 1 ≤ (n + 1) * count A m
      omega
    have hscaled := Nat.mul_le_mul_left d hgap
    have hsub := Nat.sub_add_cancel (show 1 ≤ d * (n + 1) by nlinarith)
    change 2 * (d * m) * count A n ≤ (d * (n + 1) - 1) * d
    nlinarith

def StrictConjecture : Prop :=
  ∀ A n m, Admissible A n → n < m → n * count A m < 2 * m * count A n

def RoundedConjecture : Prop :=
  ∀ A n m, Admissible A n → n < m → (n + 1) * count A m ≤ 2 * m * count A n

/-- This proves equivalence only: neither conjecture is assumed proved. -/
theorem strict_iff_rounded : StrictConjecture ↔ RoundedConjecture := by
  constructor
  · intro h A n m hA hnm
    by_contra hf
    have hfail : 2 * m * count A n < (n + 1) * count A m := by omega
    obtain ⟨d, N, M, hd, hreg, hlt, hge⟩ := lift_rounded_failure hA hnm hfail
    exact (not_lt_of_ge hge) (h (dilate d A) N M hreg hlt)
  · intro h A n m hA hnm
    have hp := count_pos (admissible_mono hA hnm.le)
    have hr := h A n m hA hnm
    nlinarith

#print axioms count_dilate
#print axioms predecessor_div
#print axioms lift_rounded_failure
#print axioms strict_iff_rounded
end Erdos488Rounded
