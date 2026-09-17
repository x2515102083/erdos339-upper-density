/-
Copyright 2026 x2515102083.
Released under the Apache 2.0 license.
AI-assisted formalization of the known negative answers to Erdos 1209(i),(ii).
Statement reference: google-deepmind/formal-conjectures,
FormalConjectures/ErdosProblems/1209.lean at
cbee53b0ccb3bacf2d9e9b2bf2eea493a373b22c.
This file does NOT claim to settle the other clauses of problem 1209.
-/
import Mathlib

namespace NextProblems.Erdos1209

/-- A prime can be chosen arbitrarily large so that a prescribed positive
translation has a prime square divisor. Dirichlet's theorem supplies the prime. -/
lemma exists_prime_bad_shift (n B : ℕ) (hn : 0 < n) :
    ∃ p > B, p.Prime ∧ ¬ Squarefree (n + p) := by
  obtain ⟨q, hqbound, hqprime⟩ := Nat.exists_infinite_primes (n + 1)
  have hnot : ¬ q ∣ n := by
    intro h
    have hle := Nat.le_of_dvd hn h
    omega
  have hcop : n.Coprime q := (hqprime.coprime_iff_not_dvd.mpr hnot).symm
  have hz : IsCoprime (n : ℤ) ((q ^ 2 : ℕ) : ℤ) := by
    simpa using hcop.pow_right 2
  obtain ⟨p, hpB, hprime, hmod⟩ := Nat.forall_exists_prime_gt_and_zmodEq B
    (q := q ^ 2) (a := -(n : ℤ)) (pow_ne_zero 2 hqprime.ne_zero) hz.neg_left
  have hzero : (p : ℤ) + n ≡ 0 [ZMOD ((q ^ 2 : ℕ) : ℤ)] := by
    simpa using hmod.add (Int.ModEq.refl (n : ℤ))
  have hdZ : ((q ^ 2 : ℕ) : ℤ) ∣ (p : ℤ) + n :=
    Int.modEq_zero_iff_dvd.mp hzero
  have hdN : q ^ 2 ∣ p + n := by exact_mod_cast hdZ
  refine ⟨p, hpB, hprime, ?_⟩
  intro hsf
  have hu : IsUnit q := hsf q (by simpa [pow_two, Nat.add_comm] using hdN)
  have hqone : q = 1 := by simpa using hu
  exact hqprime.ne_one hqone

lemma exists_pick (k B : ℕ) :
    ∃ p > B, p.Prime ∧ ¬ Squarefree ((k + 1) + p) :=
  exists_prime_bad_shift (k + 1) B (Nat.succ_pos k)

noncomputable def pick (k B : ℕ) : ℕ := Classical.choose (exists_pick k B)

lemma pick_spec (k B : ℕ) :
    B < pick k B ∧ (pick k B).Prime ∧ ¬ Squarefree ((k + 1) + pick k B) :=
  Classical.choose_spec (exists_pick k B)

/-- The next prime is larger than both the requested bound and the preceding term. -/
noncomputable def sequence (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => pick 0 (f 0)
  | k + 1 => pick (k + 1) (max (f (k + 1)) (sequence f k))

lemma sequence_spec (f : ℕ → ℕ) (k : ℕ) :
    f k < sequence f k ∧ (sequence f k).Prime ∧
      ¬ Squarefree ((k + 1) + sequence f k) := by
  cases k with
  | zero => exact pick_spec 0 (f 0)
  | succ k =>
      obtain ⟨hb, hp, hs⟩ := pick_spec (k + 1) (max (f (k + 1)) (sequence f k))
      exact ⟨lt_of_le_of_lt (le_max_left _ _) hb, hp, hs⟩

lemma sequence_strictMono (f : ℕ → ℕ) : StrictMono (sequence f) := by
  apply strictMono_nat_of_lt_succ
  intro k
  exact lt_of_le_of_lt (le_max_right (f (k + 1)) (sequence f k))
    (pick_spec (k + 1) (max (f (k + 1)) (sequence f k))).1

lemma prime_shifts (f : ℕ → ℕ) :
    {n : ℕ | ∀ k, (n + sequence f k).Prime} = {0} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact (sequence_spec f k).2.2 (h k).squarefree
  · rintro rfl
    intro k
    simpa using (sequence_spec f k).2.1

lemma squarefree_shifts (f : ℕ → ℕ) :
    {n : ℕ | ∀ k, Squarefree (n + sequence f k)} = {0} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact (sequence_spec f k).2.2 (h k)
  · rintro rfl
    intro k
    simpa using (sequence_spec f k).2.1.squarefree

/-- One and the same arbitrarily fast sequence witnesses both negative answers. -/
theorem simultaneous_unique_shift (f : ℕ → ℕ) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ k, f k ≤ a k) ∧
      {n : ℕ | ∀ k, (n + a k).Prime} = {0} ∧
      {n : ℕ | ∀ k, Squarefree (n + a k)} = {0} := by
  exact ⟨sequence f, sequence_strictMono f,
    fun k => (sequence_spec f k).1.le, prime_shifts f, squarefree_shifts f⟩

/-- Exact statement of Erdos 1209(i), with its proposed answer resolved as False. -/
theorem erdos_1209_i : False ↔
    ∃ f : ℕ → ℕ, ∀ a : ℕ → ℕ, StrictMono a → (∀ k, f k ≤ a k) →
      (∃ n, ∀ k, (n + a k).Prime) → {n : ℕ | ∀ k, (n + a k).Prime}.Infinite := by
  constructor
  · exact False.elim
  · rintro ⟨f, hf⟩
    have h := hf (sequence f) (sequence_strictMono f)
      (fun k => (sequence_spec f k).1.le)
      ⟨0, fun k => by simpa using (sequence_spec f k).2.1⟩
    rw [prime_shifts] at h
    exact h (Set.finite_singleton 0)

/-- Exact statement of Erdos 1209(ii), with its proposed answer resolved as False. -/
theorem erdos_1209_ii : False ↔
    ∃ f : ℕ → ℕ, ∀ a : ℕ → ℕ, StrictMono a → (∀ k, f k ≤ a k) →
      (∃ n, ∀ k, Squarefree (n + a k)) →
        {n : ℕ | ∀ k, Squarefree (n + a k)}.Infinite := by
  constructor
  · exact False.elim
  · rintro ⟨f, hf⟩
    have h := hf (sequence f) (sequence_strictMono f)
      (fun k => (sequence_spec f k).1.le)
      ⟨0, fun k => by simpa using (sequence_spec f k).2.1.squarefree⟩
    rw [squarefree_shifts] at h
    exact h (Set.finite_singleton 0)

#print axioms simultaneous_unique_shift
#print axioms erdos_1209_i
#print axioms erdos_1209_ii

end NextProblems.Erdos1209
