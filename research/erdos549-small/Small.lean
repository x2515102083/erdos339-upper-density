/-
Copyright 2026 x2515102083. Released under the Apache 2.0 license.
Prepared with ChatGPT assistance. Mathematical disproof credit remains with
Norin, Sun and Zhao (2016). This file independently formalizes a concrete
35-vertex five-cycle construction. It does not import another Erdos 549 proof.
Prior 63-vertex formalization and awards PR #839 must be disclosed; no first
formalization or award entitlement is asserted.
-/
import RamseyDefs

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open Finset
namespace Erdos549Small

abbrev TV := Fin 9 ⊕ Fin 18

def TreeAdj : TV → TV → Prop
  | Sum.inl i, Sum.inr j => i = 0 ∨ j = 0
  | Sum.inr j, Sum.inl i => i = 0 ∨ j = 0
  | _, _ => False

instance : DecidableRel TreeAdj := by
  intro x y
  cases x <;> cases y <;> dsimp [TreeAdj] <;> infer_instance

def tree : SimpleGraph TV where
  Adj := TreeAdj
  symm := by intro x y; cases x <;> cases y <;> simp [TreeAdj]
  loopless := by intro x; cases x <;> simp [TreeAdj]

instance : DecidableRel tree.Adj := inferInstanceAs (DecidableRel TreeAdj)

def leftCenter : TV := Sum.inl 0
def rightCenter : TV := Sum.inr 0

/-- The given partition has exactly 9 and 18 vertices, with no internal edges. -/
theorem tree_bipartition :
    (∀ i j : Fin 9, ¬ tree.Adj (Sum.inl i) (Sum.inl j)) ∧
    (∀ i j : Fin 18, ¬ tree.Adj (Sum.inr i) (Sum.inr j)) := by
  constructor <;> intros <;> exact id

theorem center_edge : tree.Adj leftCenter rightCenter := by decide

theorem every_vertex_neighbor : ∀ x : TV,
    tree.Adj leftCenter x ∨ tree.Adj rightCenter x := by decide

theorem tree_edge_count : tree.edgeFinset.card = 26 := by decide

theorem tree_connected : tree.Connected := by
  have hr : ∀ x : TV, tree.Reachable leftCenter x := by
    intro x
    cases x with
    | inl i =>
      exact center_edge.reachable.trans
        (show tree.Adj rightCenter (Sum.inl i) from Or.inr rfl).reachable
    | inr j =>
      exact (show tree.Adj leftCenter (Sum.inr j) from Or.inl rfl).reachable
  exact ⟨fun x y => (hr x).symm.trans (hr y)⟩

/-- The actual graph, rather than a supplied assumption, is a tree. -/
theorem tree_isTree : tree.IsTree := by
  apply (SimpleGraph.isTree_iff_connected_and_card).2
  refine ⟨tree_connected, ?_⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, tree_edge_count]
  decide

/-- Five cliques of size seven; consecutive cliques are joined except at equal labels. -/
def BlueAdj (u v : Fin 35) : Prop :=
  u ≠ v ∧
    (u.val / 7 = v.val / 7 ∨
      ((u.val / 7 + 1) % 5 = v.val / 7 ∨
       (v.val / 7 + 1) % 5 = u.val / 7) ∧ u.val % 7 ≠ v.val % 7)

instance : DecidableRel BlueAdj := by
  intro u v
  unfold BlueAdj
  infer_instance

def blue : SimpleGraph (Fin 35) where
  Adj := BlueAdj
  symm := by
    intro u v h
    rcases h with ⟨hne, h | ⟨hcyc, hlab⟩⟩
    · exact ⟨hne.symm, Or.inl h.symm⟩
    · exact ⟨hne.symm, Or.inr ⟨hcyc.elim Or.inr Or.inl, hlab.symm⟩⟩
  loopless := by intro u h; exact h.1 rfl

instance : DecidableRel blue.Adj := inferInstanceAs (DecidableRel BlueAdj)

/-- This finite fact is kernel-reduced with ordinary decide, not native_decide. -/
theorem blue_union_bound : ∀ u v : Fin 35, blue.Adj u v →
    (blue.neighborFinset u ∪ blue.neighborFinset v).card ≤ 26 := by decide

theorem blue_degree : ∀ u : Fin 35, (blue.neighborFinset u).card = 18 := by decide

theorem red_degree : ∀ u : Fin 35, (blueᶜ.neighborFinset u).card = 16 := by decide

/-- No non-induced copy exists: the image of all 27 vertices would lie in a set of size 26. -/
theorem not_contained_blue : ¬ tree.IsContained blue := by
  rintro ⟨f⟩
  have hs : (Finset.univ.image f) ⊆
      blue.neighborFinset (f leftCenter) ∪ blue.neighborFinset (f rightCenter) := by
    intro y hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
    rcases every_vertex_neighbor x with hx | hx
    · exact Finset.mem_union_left _ (by simpa using f.toHom.map_adj hx)
    · exact Finset.mem_union_right _ (by simpa using f.toHom.map_adj hx)
  have hc : (Finset.univ.image f).card = 27 := by
    rw [Finset.card_image_of_injective _ f.injective]
    decide
  have hle := Finset.card_le_card hs
  have hb := blue_union_bound (f leftCenter) (f rightCenter) (f.toHom.map_adj center_edge)
  omega

/-- The high-degree center would require 18 distinct red neighbors, but every vertex has 16. -/
theorem not_contained_red : ¬ tree.IsContained blueᶜ := by
  rintro ⟨f⟩
  let g : Fin 18 → Fin 35 := fun j => f (Sum.inr j)
  have hg : Function.Injective g := by
    intro i j h
    exact Sum.inr.inj (f.injective h)
  have hs : (Finset.univ.image g) ⊆ blueᶜ.neighborFinset (f leftCenter) := by
    intro y hy
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    have h : tree.Adj leftCenter (Sum.inr j) := Or.inl rfl
    simpa [g] using f.toHom.map_adj h
  have hc : (Finset.univ.image g).card = 18 := by
    rw [Finset.card_image_of_injective _ hg]
    decide
  have hle := Finset.card_le_card hs
  have hb := red_degree (f leftCenter)
  omega

/-- Explicit coloring obstruction at 35 = 4*9-1, for ordinary (not induced) copies. -/
theorem no_monochromatic_copy :
    ¬ (tree.IsContained blue ∨ tree.IsContained blueᶜ) := by
  exact not_or.mpr ⟨not_contained_blue, not_contained_red⟩

/-- This use of sInf does not assume the set of Ramsey witnesses is nonempty.
An asserted positive value 35 itself implies nonemptiness, hence membership. -/
theorem ramsey_ne_35 : SimpleGraph.diagonalGraphRamsey tree ≠ 35 := by
  intro h
  change sInf {n : ℕ | ∀ C : SimpleGraph (Fin n),
      tree.IsContained C ∨ tree.IsContained Cᶜ} = 35 at h
  have hp : 0 < sInf {n : ℕ | ∀ C : SimpleGraph (Fin n),
      tree.IsContained C ∨ tree.IsContained Cᶜ} := by rw [h]; decide
  have hm := Nat.sInf_mem (Nat.nonempty_of_pos_sInf hp)
  rw [h] at hm
  exact no_monochromatic_copy (hm blue)

/-- Complete negation of the original universally quantified formula.
The types, tree condition, partition conditions, and Ramsey definitions match
Formal Conjectures ErdosProblems/549.lean at the cited fixed revision. -/
theorem not_erdos_549 : ¬
    ∀ (k : ℕ) (hk : 2 ≤ k) (T : SimpleGraph (Fin k ⊕ Fin (2 * k))),
      T.IsTree →
      (∀ x₁ x₂, ¬ T.Adj (Sum.inl x₁) (Sum.inl x₂)) →
      (∀ y₁ y₂, ¬ T.Adj (Sum.inr y₁) (Sum.inr y₂)) →
      SimpleGraph.diagonalGraphRamsey T = 4 * k - 1 := by
  intro h
  exact ramsey_ne_35 (h 9 (by decide) tree tree_isTree tree_bipartition.1 tree_bipartition.2)

/-- A positive existential certificate, in addition to the negation theorem. -/
theorem explicit_counterexample :
    ∃ T : SimpleGraph (Fin 9 ⊕ Fin 18), T.IsTree ∧
      (∀ x y : Fin 9, ¬ T.Adj (Sum.inl x) (Sum.inl y)) ∧
      (∀ x y : Fin 18, ¬ T.Adj (Sum.inr x) (Sum.inr y)) ∧
      SimpleGraph.diagonalGraphRamsey T ≠ 35 :=
  ⟨tree, tree_isTree, tree_bipartition.1, tree_bipartition.2, ramsey_ne_35⟩

#print axioms tree_isTree
#print axioms blue_union_bound
#print axioms blue_degree
#print axioms red_degree
#print axioms no_monochromatic_copy
#print axioms ramsey_ne_35
#print axioms not_erdos_549
#print axioms explicit_counterexample
end Erdos549Small
