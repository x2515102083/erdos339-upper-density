/-
Copyright 2026 x2515102083.
Released under the Apache 2.0 license.
AI-assisted formalization of known mathematics; no first-priority claim.
The seed 12167, 12168 is recorded in JSP-000301 and the classical literature.
The infinite-family theorem is an additional result, not the counting conjecture
in Erdos problem 365.
-/
import Mathlib

namespace NextProblems.PowerfulPairs

/-- A positive natural number whose every prime divisor divides it at least twice. -/
def Powerful (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- Both consecutive integers are powerful and neither is a square. -/
def Good (n : ℕ) : Prop :=
  Powerful n ∧ Powerful (n + 1) ∧ ¬ IsSquare n ∧ ¬ IsSquare (n + 1)

lemma powerful_prime_cube {p : ℕ} (hp : p.Prime) : Powerful (p ^ 3) := by
  refine ⟨pow_pos hp.pos _, ?_⟩
  intro q hq hqp
  have hd : q ∣ p := hq.dvd_of_dvd_pow hqp
  rcases (Nat.dvd_prime hp).mp hd with h | h
  · exact (hq.ne_one h).elim
  · subst q
    exact ⟨p, by ring⟩

lemma powerful_mul_sq {a x : ℕ} (ha : Powerful a) (hx : 0 < x) :
    Powerful (a * x ^ 2) := by
  refine ⟨mul_pos ha.1 (pow_pos hx _), ?_⟩
  intro p hp hd
  rcases hp.dvd_mul.mp hd with h | h
  · exact dvd_mul_of_dvd_left (ha.2 p hp h) _
  · have hpx : p ∣ x := hp.dvd_of_dvd_pow h
    exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hpx 2) _

lemma nonsquare_mul_sq {a x : ℕ} (hx : 0 < x)
    (ha : ¬ IsSquare (a : ℚ)) : ¬ IsSquare (a * x ^ 2) := by
  rintro ⟨r, hr⟩
  apply ha
  refine ⟨(r : ℚ) / x, ?_⟩
  have hxq : (x : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hx
  have hq : (a : ℚ) * (x : ℚ) ^ 2 = (r : ℚ) * (r : ℚ) := by
    exact_mod_cast hr
  field_simp
  nlinarith [hq]

lemma powerful_12167 : Powerful 12167 := by
  convert powerful_prime_cube (by norm_num : Nat.Prime 23) using 1 <;> norm_num

lemma powerful_12168 : Powerful 12168 := by
  have h := powerful_mul_sq (powerful_prime_cube (by norm_num : Nat.Prime 2))
    (by norm_num : 0 < (39 : ℕ))
  norm_num at h
  exact h

/-- Complete negative answer to the scoped yes/no question JSP-000301. -/
theorem seed_good : Good 12167 := by
  refine ⟨powerful_12167, powerful_12168, ?_, ?_⟩ <;> norm_num

/-- An elementary Pell-type recurrence; no existence theorem is assumed. -/
def pair : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | k + 1 =>
      (24335 * (pair k).1 + 24336 * (pair k).2,
       24334 * (pair k).1 + 24335 * (pair k).2)

lemma pair_spec (k : ℕ) :
    0 < (pair k).1 ∧ 0 < (pair k).2 ∧
      12167 * (pair k).1 ^ 2 + 1 = 12168 * (pair k).2 ^ 2 := by
  induction k with
  | zero => norm_num [pair]
  | succ k ih =>
      simp only [pair, Prod.fst, Prod.snd]
      refine ⟨by omega, by omega, ?_⟩
      nlinarith only [ih.2.2]

def first (k : ℕ) : ℕ := 12167 * (pair k).1 ^ 2

lemma first_good (k : ℕ) : Good (first k) := by
  obtain ⟨hs, ht, heq⟩ := pair_spec k
  have hn : first k + 1 = 12168 * (pair k).2 ^ 2 := heq
  refine ⟨powerful_mul_sq powerful_12167 hs, ?_, ?_, ?_⟩
  · rw [hn]
    exact powerful_mul_sq powerful_12168 ht
  · exact nonsquare_mul_sq hs (by norm_num)
  · rw [hn]
    exact nonsquare_mul_sq ht (by norm_num)

lemma first_strictMono : StrictMono first := by
  apply strictMono_nat_of_lt_succ
  intro k
  have hs := (pair_spec k).1
  have ht := (pair_spec k).2.1
  have hstep : (pair k).1 < (pair (k + 1)).1 := by
    simp only [pair, Prod.fst]
    omega
  have hp := Nat.pow_lt_pow_left hstep (by decide : (2 : ℕ) ≠ 0)
  exact Nat.mul_lt_mul_of_pos_left hp (by norm_num)

/-- Arbitrarily large consecutive powerful nonsquares, with an explicit construction. -/
theorem arbitrarily_large (N : ℕ) : ∃ n > N, Good n := by
  refine ⟨first (N + 1), ?_, first_good (N + 1)⟩
  have h := first_strictMono.id_le (N + 1)
  omega

/-- The exact universal assertion in JSP-000301 is false. -/
theorem jsp_000301 :
    ¬ ∀ n : ℕ, Powerful n → Powerful (n + 1) → IsSquare n ∨ IsSquare (n + 1) := by
  intro h
  rcases h 12167 seed_good.1 seed_good.2.1 with hs | hs
  · exact seed_good.2.2.1 hs
  · exact seed_good.2.2.2 hs

#print axioms seed_good
#print axioms arbitrarily_large
#print axioms jsp_000301

end NextProblems.PowerfulPairs
