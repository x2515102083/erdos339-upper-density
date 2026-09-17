import Mathlib

/-!
# Consecutive nonsquare powerful numbers in prescribed seed residue classes

New formalization prepared for GitHub account x2515102083 with ChatGPT assistance.
The seed 12167, 12168 is Golomb's classical counterexample; the Pell method is
classical and no mathematical discovery or first-formalization claim is made.
This file does not import or copy another problem-specific formalization.
-/
namespace PowerfulResidues

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

/-- The literal positive-integer definition used in the catalog question. -/
def Powerful (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- Both consecutive numbers are powerful and neither is a square. -/
def Good (n : ℕ) : Prop :=
  Powerful n ∧ Powerful (n + 1) ∧ ¬ IsSquare n ∧ ¬ IsSquare (n + 1)

theorem powerful_cube {x : ℕ} (hx : 0 < x) : Powerful (x ^ 3) := by
  refine ⟨by positivity, ?_⟩
  intro p hp hpx
  obtain ⟨k, hk⟩ := hp.dvd_of_dvd_pow hpx
  refine ⟨p * k ^ 3, ?_⟩
  rw [hk]
  ring

theorem powerful_mul_square {a u : ℕ} (ha : Powerful a) (hu : 0 < u) :
    Powerful (a * u ^ 2) := by
  refine ⟨by have := ha.1; positivity, ?_⟩
  intro p hp hdiv
  rcases hp.dvd_mul.mp hdiv with hpa | hpu
  · obtain ⟨k, hk⟩ := ha.2 p hp hpa
    refine ⟨k * u ^ 2, ?_⟩
    rw [hk]
    ring
  · obtain ⟨k, hk⟩ := hp.dvd_of_dvd_pow hpu
    refine ⟨a * k ^ 2, ?_⟩
    rw [hk]
    ring

/-- A nonzero square multiplier cannot change a nonsquare's square class. -/
theorem nonsquare_mul_square {a u : ℕ} (ha : ¬ IsSquare a) (hu : 0 < u) :
    ¬ IsSquare (a * u ^ 2) := by
  rintro ⟨z, hz⟩
  have huQ : (u : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hu)
  have hzQ : (a : ℚ) * (u : ℚ) ^ 2 = (z : ℚ) * (z : ℚ) := by
    exact_mod_cast hz
  apply ha
  apply Rat.isSquare_natCast_iff.mp
  refine ⟨(z : ℚ) / (u : ℚ), ?_⟩
  have h : (a : ℚ) = ((z : ℚ) / (u : ℚ)) ^ 2 := by
    rw [div_pow]
    apply (eq_div_iff (pow_ne_zero 2 huQ)).2
    simpa only [pow_two] using hzQ
  simpa only [pow_two] using h

/-- An explicit integral Pell orbit attached to an arbitrary consecutive seed. -/
def orbit (a : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | k + 1 =>
    let z := orbit a k
    ((2 * a + 1) * z.1 + 2 * (a + 1) * z.2,
      2 * a * z.1 + (2 * a + 1) * z.2)

def term (a k : ℕ) : ℕ := a * (orbit a k).1 ^ 2

@[simp] theorem term_zero (a : ℕ) : term a 0 = a := by
  simp [term, orbit]

theorem orbit_positive (a k : ℕ) : 0 < (orbit a k).1 ∧ 0 < (orbit a k).2 := by
  induction k with
  | zero => simp [orbit]
  | succ k ih =>
    simp only [orbit]
    constructor <;> nlinarith [ih.1, ih.2,
      Nat.zero_le (a * (orbit a k).1), Nat.zero_le (a * (orbit a k).2)]

/-- The norm identity is proved for every index, not checked at sample values. -/
theorem orbit_equation (a k : ℕ) :
    a * (orbit a k).1 ^ 2 + 1 = (a + 1) * (orbit a k).2 ^ 2 := by
  induction k with
  | zero => simp [orbit]
  | succ k ih =>
    have h :
        a * ((2 * a + 1) * (orbit a k).1 + 2 * (a + 1) * (orbit a k).2) ^ 2
          + (a + 1) * (orbit a k).2 ^ 2 =
        (a + 1) * (2 * a * (orbit a k).1 + (2 * a + 1) * (orbit a k).2) ^ 2
          + a * (orbit a k).1 ^ 2 := by ring
    simp only [orbit]
    omega

theorem orbit_fst_lt_succ (a k : ℕ) : (orbit a k).1 < (orbit a (k + 1)).1 := by
  have hp := orbit_positive a k
  simp only [orbit]
  nlinarith [hp.1, hp.2, Nat.zero_le (a * (orbit a k).1),
    Nat.zero_le (a * (orbit a k).2)]

theorem term_lt_succ {a : ℕ} (ha : 0 < a) (k : ℕ) : term a k < term a (k + 1) := by
  have h := orbit_fst_lt_succ a k
  unfold term
  apply Nat.mul_lt_mul_of_pos_left _ ha
  nlinarith [orbit_positive a k, orbit_positive a (k + 1)]

theorem term_strictMono {a : ℕ} (ha : 0 < a) : StrictMono (term a) :=
  strictMono_nat_of_lt_succ (term_lt_succ ha)

theorem index_le_term {a : ℕ} (ha : 0 < a) (k : ℕ) : k ≤ term a k := by
  induction k with
  | zero => omega
  | succ k ih => have := term_lt_succ ha k; omega

theorem term_good {a : ℕ} (ha : Good a) (k : ℕ) : Good (term a k) := by
  have hp := orbit_positive a k
  have heq : term a k + 1 = (a + 1) * (orbit a k).2 ^ 2 := orbit_equation a k
  refine ⟨powerful_mul_square ha.1 hp.1, ?_, nonsquare_mul_square ha.2.2.1 hp.1, ?_⟩
  · rw [heq]
    exact powerful_mul_square ha.2.1 hp.2
  · rw [heq]
    exact nonsquare_mul_square ha.2.2.2 hp.2

/-- Modulo any modulus the norm-preserving matrix is a permutation: determinant 1. -/
def residuePerm (a m : ℕ) : Equiv.Perm (ZMod m × ZMod m) where
  toFun z := (((2 : ZMod m) * a + 1) * z.1 + 2 * ((a : ZMod m) + 1) * z.2,
    2 * (a : ZMod m) * z.1 + (2 * (a : ZMod m) + 1) * z.2)
  invFun z := (((2 : ZMod m) * a + 1) * z.1 - 2 * ((a : ZMod m) + 1) * z.2,
    -(2 * (a : ZMod m) * z.1) + (2 * (a : ZMod m) + 1) * z.2)
  left_inv z := by apply Prod.ext <;> dsimp <;> ring
  right_inv z := by apply Prod.ext <;> dsimp <;> ring

def modOrbit (a m k : ℕ) : ZMod m × ZMod m :=
  ((orbit a k).1, (orbit a k).2)

theorem modOrbit_eq_pow (a m k : ℕ) :
    modOrbit a m k = (residuePerm a m ^ k) (1, 1) := by
  induction k with
  | zero => simp [modOrbit, orbit]
  | succ k ih =>
    have hs : modOrbit a m (k + 1) = residuePerm a m (modOrbit a m k) := by
      apply Prod.ext <;> simp [modOrbit, orbit, residuePerm, Nat.cast_add, Nat.cast_mul]
    rw [hs, ih, pow_succ']
    rfl

/-- A positive return period exists for every positive modulus; it is not guessed. -/
theorem exists_residue_period (a : ℕ) {m : ℕ} (hm : 0 < m) :
    ∃ q : ℕ, 0 < q ∧ ∀ k : ℕ, modOrbit a m (q * k) = (1, 1) := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let e := residuePerm a m
  let q := orderOf e
  have hq : 0 < q := (isOfFinOrder_of_finite e).orderOf_pos
  refine ⟨q, hq, ?_⟩
  intro k
  rw [modOrbit_eq_pow]
  change (e ^ (q * k)) (1, 1) = (1, 1)
  rw [pow_mul, show e ^ q = 1 from pow_orderOf_eq_one e, one_pow]
  rfl

/-- Every good seed returns arbitrarily far out in its own class modulo any positive modulus. -/
theorem unbounded_in_seed_residue {a : ℕ} (ha : Good a) {m : ℕ} (hm : 0 < m)
    (B : ℕ) : ∃ n : ℕ, B < n ∧ Good n ∧ (n : ZMod m) = (a : ZMod m) := by
  obtain ⟨q, hq, hperiod⟩ := exists_residue_period a hm
  let k := q * (B + 1)
  have hB : B < k := by dsimp [k]; nlinarith
  have hlarge : B < term a k := hB.trans_le (index_le_term ha.1.1 k)
  have hfst : ((orbit a k).1 : ZMod m) = 1 := congrArg Prod.fst (hperiod (B + 1))
  refine ⟨term a k, hlarge, term_good ha k, ?_⟩
  simp only [term, Nat.cast_mul, Nat.cast_pow, hfst, one_pow, mul_one]

/-- Golomb's already-known seed, with ordinary primality and squareness. -/
theorem seed_good : Good 12167 := by
  have ha : Powerful 12167 := by
    change Powerful (23 ^ 3)
    exact powerful_cube (by decide)
  have hb : Powerful 12168 := by
    change Powerful (2 ^ 3 * 39 ^ 2)
    exact powerful_mul_square (powerful_cube (by decide)) (by decide)
  refine ⟨ha, hb, ?_, ?_⟩ <;> norm_num

/-- A full unconditional conclusion, stronger than the catalog's yes/no disproof. -/
theorem unbounded_counterexamples_in_every_seed_residue (m : ℕ) (hm : 0 < m) (B : ℕ) :
    ∃ n : ℕ, B < n ∧ Powerful n ∧ Powerful (n + 1) ∧
      ¬ IsSquare n ∧ ¬ IsSquare (n + 1) ∧ (n : ZMod m) = (12167 : ZMod m) := by
  obtain ⟨n, hn, hg, hr⟩ := unbounded_in_seed_residue seed_good hm B
  exact ⟨n, hn, hg.1, hg.2.1, hg.2.2.1, hg.2.2.2, hr⟩

/-- Direct negation of the entire scoped catalog question; no bounded parameter is assumed. -/
theorem jsp_000301_false :
    ¬ (∀ n : ℕ, 0 < n → Powerful n → Powerful (n + 1) →
      IsSquare n ∨ IsSquare (n + 1)) := by
  intro h
  rcases h 12167 seed_good.1.1 seed_good.1 seed_good.2.1 with hs | hs
  · exact seed_good.2.2.1 hs
  · exact seed_good.2.2.2 hs

#print axioms powerful_mul_square
#print axioms nonsquare_mul_square
#print axioms orbit_equation
#print axioms term_strictMono
#print axioms term_good
#print axioms exists_residue_period
#print axioms unbounded_in_seed_residue
#print axioms seed_good
#print axioms unbounded_counterexamples_in_every_seed_residue
#print axioms jsp_000301_false

end PowerfulResidues
