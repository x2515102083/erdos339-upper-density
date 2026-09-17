import Mathlib

/-!
# Counterexamples to two auxiliary conjectures, NOT to Erdos 488

The targets are Conjectures 6.11 and 4.8 in Przemyslaw Chojecki,
"Signed Transport, Pair-Tail Reduction, and Low Layers in an Erdos
Density-Doubling Problem", dated 20 March 2026, pp. 17 and 10 respectively:
https://www.ulam.ai/research/erdos488.pdf

The finite counts below use ordinary `decide`, with no native computation
axiom. The predicates are literal finite-set divisibility counts.
Prepared for x2515102083 with ChatGPT assistance. No priority or prize claim.
-/

set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Erdos488RouteAudit

/-- Positive integers at most t divisible by at least one generator. -/
def hits (A : Finset ℕ) (t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 t).filter (fun x => ∃ a ∈ A, a ∣ x)

def count (A : Finset ℕ) (t : ℕ) : ℕ := (hits A t).card

def incidence (A : Finset ℕ) (t : ℕ) : ℕ := A.sum (fun a => t / a)

def IsPrimitive (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ∣ b → a = b

/-- The extra odd element makes the gcd equal to 1. -/
def sparseSet : Finset ℕ :=
  {4, 6, 10, 14, 22, 26, 34, 38, 46, 58, 62, 74, 82, 86, 94, 227}

theorem sparse_structure :
    sparseSet.Nonempty ∧ IsPrimitive sparseSet ∧
    (∀ a ∈ sparseSet, 2 ≤ a ∧ a ≤ 228) ∧ sparseSet.gcd id = 1 := by
  unfold IsPrimitive
  decide

theorem sparse_values :
    count sparseSet 228 = 99 ∧ incidence sparseSet 228 = 183 ∧
      sparseSet.card = 16 := by
  decide

/-- The exact finite incidence formulation of the paper's Conjecture 6.11.
The paper's total order-slack equals 2*count-incidence-card for EVERY ordering. -/
def SparseOrderSlackConjecture : Prop :=
  ∀ (G : Finset ℕ) (n : ℕ), G.Nonempty → IsPrimitive G →
    (∀ g ∈ G, 2 ≤ g ∧ g ≤ n) → 2 * count G n < n →
      incidence G n + G.card ≤ 2 * count G n

/-- A primitive gcd-one witness refutes the auxiliary sparse conjecture. -/
theorem not_sparse_order_slack : ¬ SparseOrderSlackConjecture := by
  intro h
  obtain ⟨hne, hprim, hbounds, _⟩ := sparse_structure
  obtain ⟨hcount, hinc, hcard⟩ := sparse_values
  have hsparse : 2 * count sparseSet 228 < 228 := by omega
  have hbad := h sparseSet 228 hne hprim hbounds hsparse
  omega

/-- Union of the core multiples with all tail multiples removed. -/
def splitHits (U V : Finset ℕ) (t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 t).filter
    (fun x => (∃ a ∈ U, a ∣ x) ∧ ¬ (∃ v ∈ V, v ∣ x))

def splitCount (U V : Finset ℕ) (t : ℕ) : ℕ := (splitHits U V t).card

/-- Exactly the primes from 5 through 79. No primality oracle is used. -/
def primeTail : Finset ℕ :=
  {5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79}

theorem tail_structure :
    primeTail.Nonempty ∧ (∀ v ∈ primeTail, 3 < v ∧ v ≤ 191) ∧
      IsPrimitive ({2, 3} ∪ primeTail) ∧
      (∀ p ∈ ({2, 3} ∪ primeTail : Finset ℕ), Nat.Prime p) := by
  unfold IsPrimitive
  decide

theorem split_values :
    splitCount {2, 3} primeTail 191 = 25 ∧
      splitCount {2, 3} primeTail 3158 = 827 := by
  decide

/-- The exact strict pair-vs-tail target, with a nonempty later tail. -/
def PairTailConjecture : Prop :=
  ∀ (a b : ℕ) (V : Finset ℕ) (n m : ℕ),
    2 ≤ a → a < b → V.Nonempty → (∀ v ∈ V, b < v ∧ v ≤ n) →
      b ≤ n → n < m →
      n * splitCount {a, b} V m < 2 * m * splitCount {a, b} V n

/-- Refutes Conjecture 4.8 even with an entirely prime, primitive full set. -/
theorem not_pair_tail : ¬ PairTailConjecture := by
  intro h
  obtain ⟨hne, hbounds, _, _⟩ := tail_structure
  obtain ⟨hn, hm⟩ := split_values
  have hbad := h 2 3 primeTail 191 3158 (by omega) (by omega)
    hne hbounds (by omega) (by omega)
  omega

/-- A quantitative, strictly reversed inequality (not just equality). -/
theorem pair_tail_gap :
    2 * 3158 * splitCount {2, 3} primeTail 191 + 57 =
      191 * splitCount {2, 3} primeTail 3158 := by
  obtain ⟨hn, hm⟩ := split_values
  omega

/-- Every literal union count is at most the interval length. -/
theorem count_le (A : Finset ℕ) (t : ℕ) : count A t ≤ t := by
  calc
    count A t ≤ (Finset.Icc 1 t).card := Finset.card_filter_le _ _
    _ = t := by simp

/-- Extra assurance: for the tail example, the original UNION conjecture
holds for all n >= 3 and m > n. This is not a counterexample to Erdos 488. -/
theorem original_for_sets_containing_two_three (A : Finset ℕ)
    (h2 : 2 ∈ A) (h3 : 3 ∈ A) (n m : ℕ) (hn : 3 ≤ n) (hnm : n < m) :
    n * count A m < 2 * m * count A n := by
  let E := (Finset.Icc 1 (n / 2)).image (fun k : ℕ => 2 * k)
  have hcardE : E.card = n / 2 := by
    rw [Finset.card_image_of_injective _ (fun x y h => by omega)]
    simp
  have h3not : 3 ∉ E := by
    simp only [E, Finset.mem_image, Finset.mem_Icc]
    rintro ⟨k, _, hk⟩
    omega
  have hsub : insert 3 E ⊆ hits A n := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · simp only [hits, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, hn⟩, 3, h3, dvd_rfl⟩
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
      simp only [hits, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, ?_⟩, 2, h2, dvd_mul_right 2 k⟩
      omega
  have hlow : n / 2 + 1 ≤ count A n := by
    have hh := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem h3not, hcardE] at hh
    exact hh
  have hdouble : n + 1 ≤ 2 * count A n := by omega
  have hu := count_le A m
  have hu' := Nat.mul_le_mul_left n hu
  have hl' := Nat.mul_le_mul_left m hdouble
  nlinarith

theorem tail_example_satisfies_original (n m : ℕ) (hn : 79 ≤ n) (hnm : n < m) :
    n * count ({2, 3} ∪ primeTail) m < 2 * m * count ({2, 3} ∪ primeTail) n := by
  apply original_for_sets_containing_two_three
  · simp
  · simp
  · omega
  · exact hnm

#print axioms sparse_structure
#print axioms sparse_values
#print axioms not_sparse_order_slack
#print axioms tail_structure
#print axioms split_values
#print axioms not_pair_tail
#print axioms pair_tail_gap
#print axioms tail_example_satisfies_original

end Erdos488RouteAudit
