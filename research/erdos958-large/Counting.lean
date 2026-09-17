/-
Copyright (c) 2026 x2515102083. Released under Apache 2.0.
Formalization development: x2515102083 with ChatGPT (GPT-6 Astra Pro).
This file proves the complete distance-multiplicity count for an abstract
short-arc configuration, to be instantiated with actual planar points.
-/
import Mathlib

set_option maxHeartbeats 1600000
set_option maxRecDepth 2000

open Finset

/- The following two definitions are reproduced from
FormalConjecturesForMathlib/Geometry/Metric.lean at
 d5ba143cc2fafd48cc6d5b6320a3aab287c38df7.
Copyright 2025 The Formal Conjectures Authors, Apache License 2.0.
-/
noncomputable def distanceSet {X : Type*} [MetricSpace X] (points : Finset X) : Finset ℝ :=
  points.offDiag.image fun (pair : X × X) => dist pair.1 pair.2

noncomputable def distanceMultiplicity {X : Type*} [MetricSpace X]
    (points : Finset X) (d : ℝ) : ℕ :=
  (points.offDiag.filter fun (pair : X × X) => dist pair.1 pair.2 = d).card / 2

namespace Erdos958Large

structure ArcConfig (X : Type*) [MetricSpace X] (m : ℕ) where
  c : X
  p : ℕ → X
  d : ℕ → ℝ
  inj : ∀ {i j : ℕ}, i < m → j < m → p i = p j → i = j
  ne : ∀ i, i < m → p i ≠ c
  radial : ∀ i, i < m → dist c (p i) = 1
  chords : ∀ i j, i < j → j < m → dist (p i) (p j) = d (j - i)
  dinj : ∀ {i j : ℕ}, 1 ≤ i → i < m → 1 ≤ j → j < m → d i = d j → i = j
  dne : ∀ i, 1 ≤ i → i < m → d i ≠ 1

namespace ArcConfig

variable {X : Type*} [MetricSpace X] {m : ℕ} (C : ArcConfig X m)

noncomputable def points : Finset X := by
  classical
  exact insert C.c ((range m).image C.p)

lemma mem_points (x : X) : x ∈ C.points ↔ x = C.c ∨ ∃ i, i < m ∧ x = C.p i := by
  classical
  simp [points, eq_comm]

lemma center_mem : C.c ∈ C.points := (C.mem_points _).mpr (Or.inl rfl)
lemma arc_mem {i : ℕ} (hi : i < m) : C.p i ∈ C.points :=
  (C.mem_points _).mpr (Or.inr ⟨i, hi, rfl⟩)

lemma card_points : C.points.card = m + 1 := by
  classical
  have hn : C.c ∉ (range m).image C.p := by
    rintro h
    obtain ⟨i, hi, he⟩ := mem_image.mp h
    exact C.ne i (mem_range.mp hi) he
  have hc : ((range m).image C.p).card = m := by
    calc
      _ = (range m).card := card_image_iff.mpr (by
        intro i hi j hj he
        exact C.inj (mem_range.mp hi) (mem_range.mp hj) he)
      _ = m := card_range m
  simpa [points, card_insert_of_notMem hn, hc]

noncomputable def spokes : Finset (X × X) := by
  classical
  exact ((range m).image fun i => (C.c, C.p i)) ∪
    ((range m).image fun i => (C.p i, C.c))

noncomputable def chordEdges (k : ℕ) : Finset (X × X) := by
  classical
  exact ((range (m - k)).image fun i => (C.p i, C.p (i + k))) ∪
    ((range (m - k)).image fun i => (C.p (i + k), C.p i))

lemma mem_spokes (q : X × X) : q ∈ C.spokes ↔
    ∃ i, i < m ∧ (q = (C.c, C.p i) ∨ q = (C.p i, C.c)) := by
  classical
  simp only [spokes, mem_union, mem_image, mem_range]
  constructor
  · rintro (⟨i, hi, he⟩ | ⟨i, hi, he⟩)
    · exact ⟨i, hi, Or.inl he.symm⟩
    · exact ⟨i, hi, Or.inr he.symm⟩
  · rintro ⟨i, hi, he | he⟩
    · exact Or.inl ⟨i, hi, he.symm⟩
    · exact Or.inr ⟨i, hi, he.symm⟩

lemma mem_chordEdges (k : ℕ) (q : X × X) : q ∈ C.chordEdges k ↔
    ∃ i, i < m - k ∧ (q = (C.p i, C.p (i + k)) ∨ q = (C.p (i + k), C.p i)) := by
  classical
  simp only [chordEdges, mem_union, mem_image, mem_range]
  constructor
  · rintro (⟨i, hi, he⟩ | ⟨i, hi, he⟩)
    · exact ⟨i, hi, Or.inl he.symm⟩
    · exact ⟨i, hi, Or.inr he.symm⟩
  · rintro ⟨i, hi, he | he⟩
    · exact Or.inl ⟨i, hi, he.symm⟩
    · exact Or.inr ⟨i, hi, he.symm⟩

lemma spokes_offDiag {q : X × X} (hq : q ∈ C.spokes) : q ∈ C.points.offDiag := by
  obtain ⟨i, hi, rfl | rfl⟩ := (C.mem_spokes q).mp hq
  · exact mem_offDiag.mpr ⟨C.center_mem, C.arc_mem hi, (C.ne i hi).symm⟩
  · exact mem_offDiag.mpr ⟨C.arc_mem hi, C.center_mem, C.ne i hi⟩

lemma spokes_dist {q : X × X} (hq : q ∈ C.spokes) : dist q.1 q.2 = 1 := by
  obtain ⟨i, hi, rfl | rfl⟩ := (C.mem_spokes q).mp hq
  · exact C.radial i hi
  · simpa only [dist_comm] using C.radial i hi

lemma chordEdges_offDiag {k : ℕ} (hk : 1 ≤ k) {q : X × X}
    (hq : q ∈ C.chordEdges k) : q ∈ C.points.offDiag := by
  obtain ⟨i, hi, hq⟩ := (C.mem_chordEdges k q).mp hq
  have hi' : i < m := by omega
  have hj : i + k < m := by omega
  have hne : C.p i ≠ C.p (i + k) := by
    intro he
    have := C.inj hi' hj he
    omega
  rcases hq with rfl | rfl
  · exact mem_offDiag.mpr ⟨C.arc_mem hi', C.arc_mem hj, hne⟩
  · exact mem_offDiag.mpr ⟨C.arc_mem hj, C.arc_mem hi', hne.symm⟩

lemma chordEdges_dist {k : ℕ} (hk : 1 ≤ k) {q : X × X}
    (hq : q ∈ C.chordEdges k) : dist q.1 q.2 = C.d k := by
  obtain ⟨i, hi, hq⟩ := (C.mem_chordEdges k q).mp hq
  have he : dist (C.p i) (C.p (i + k)) = C.d k := by
    simpa using C.chords i (i + k) (by omega) (by omega)
  rcases hq with rfl | rfl
  · exact he
  · simpa only [dist_comm] using he

lemma classify_pair (q : X × X) : q ∈ C.points.offDiag ↔
    q ∈ C.spokes ∨ ∃ k, 1 ≤ k ∧ k < m ∧ q ∈ C.chordEdges k := by
  constructor
  · rcases q with ⟨x, y⟩
    intro h
    obtain ⟨hx, hy, hxy⟩ := mem_offDiag.mp h
    rcases (C.mem_points x).mp hx with rfl | ⟨i, hi, rfl⟩
    · rcases (C.mem_points y).mp hy with rfl | ⟨j, hj, rfl⟩
      · exact (hxy rfl).elim
      · exact Or.inl ((C.mem_spokes _).mpr ⟨j, hj, Or.inl rfl⟩)
    · rcases (C.mem_points y).mp hy with rfl | ⟨j, hj, rfl⟩
      · exact Or.inl ((C.mem_spokes _).mpr ⟨i, hi, Or.inr rfl⟩)
      · have hij : i ≠ j := by intro he; exact hxy (congrArg C.p he)
        rcases lt_or_gt_of_ne hij with hij | hji
        · right
          refine ⟨j - i, by omega, by omega, ?_⟩
          apply (C.mem_chordEdges _ _).mpr
          refine ⟨i, by omega, Or.inl ?_⟩
          have he : i + (j - i) = j := by omega
          simp only [he]
        · right
          refine ⟨i - j, by omega, by omega, ?_⟩
          apply (C.mem_chordEdges _ _).mpr
          refine ⟨j, by omega, Or.inr ?_⟩
          have he : j + (i - j) = i := by omega
          simp only [he]
  · rintro (h | ⟨k, hk, _, h⟩)
    · exact C.spokes_offDiag h
    · exact C.chordEdges_offDiag hk h

lemma card_spokes : C.spokes.card = 2 * m := by
  classical
  have hco : ((range m).image fun i => (C.c, C.p i)).card = m := by
    calc
      _ = (range m).card := card_image_iff.mpr (by
        intro i hi j hj he
        exact C.inj (mem_range.mp hi) (mem_range.mp hj) (congrArg Prod.snd he))
      _ = m := card_range m
  have hci : ((range m).image fun i => (C.p i, C.c)).card = m := by
    calc
      _ = (range m).card := card_image_iff.mpr (by
        intro i hi j hj he
        exact C.inj (mem_range.mp hi) (mem_range.mp hj) (congrArg Prod.fst he))
      _ = m := card_range m
  have hd : Disjoint ((range m).image fun i => (C.c, C.p i))
      ((range m).image fun i => (C.p i, C.c)) := by
    apply disjoint_left.mpr
    intro q hq hq'
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hq
    obtain ⟨j, hj, he⟩ := mem_image.mp hq'
    exact C.ne j (mem_range.mp hj) (congrArg Prod.fst he)
  rw [spokes, card_union_of_disjoint hd, hco, hci]
  omega

lemma card_chordEdges {k : ℕ} (hk : 1 ≤ k) :
    (C.chordEdges k).card = 2 * (m - k) := by
  classical
  have hcu : ((range (m - k)).image fun i => (C.p i, C.p (i + k))).card = m - k := by
    calc
      _ = (range (m - k)).card := card_image_iff.mpr (by
        intro i hi j hj he
        have hi' := mem_range.mp hi
        have hj' := mem_range.mp hj
        exact C.inj (by omega) (by omega) (congrArg Prod.fst he))
      _ = m - k := card_range (m - k)
  have hcd : ((range (m - k)).image fun i => (C.p (i + k), C.p i)).card = m - k := by
    calc
      _ = (range (m - k)).card := card_image_iff.mpr (by
        intro i hi j hj he
        have hi' := mem_range.mp hi
        have hj' := mem_range.mp hj
        exact C.inj (by omega) (by omega) (congrArg Prod.snd he))
      _ = m - k := card_range (m - k)
  have hd : Disjoint ((range (m - k)).image fun i => (C.p i, C.p (i + k)))
      ((range (m - k)).image fun i => (C.p (i + k), C.p i)) := by
    apply disjoint_left.mpr
    intro q hq hq'
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hq
    obtain ⟨j, hj, he⟩ := mem_image.mp hq'
    have hi' := mem_range.mp hi
    have hj' := mem_range.mp hj
    have h1 : j + k = i := C.inj (by omega) (by omega) (congrArg Prod.fst he)
    have h2 : j = i + k := C.inj (by omega) (by omega) (congrArg Prod.snd he)
    omega
  rw [chordEdges, card_union_of_disjoint hd, hcu, hcd]
  omega

lemma radius_fibre :
    (C.points.offDiag.filter fun q => dist q.1 q.2 = 1) = C.spokes := by
  classical
  ext q
  constructor
  · intro h
    obtain ⟨hq, hd⟩ := mem_filter.mp h
    rcases (C.classify_pair q).mp hq with hs | ⟨k, hk, hkm, he⟩
    · exact hs
    · exact (C.dne k hk hkm ((C.chordEdges_dist hk he).symm.trans hd)).elim
  · intro h
    exact mem_filter.mpr ⟨C.spokes_offDiag h, C.spokes_dist h⟩

lemma chord_fibre {k : ℕ} (hk : 1 ≤ k) (hkm : k < m) :
    (C.points.offDiag.filter fun q => dist q.1 q.2 = C.d k) = C.chordEdges k := by
  classical
  ext q
  constructor
  · intro h
    obtain ⟨hq, hd⟩ := mem_filter.mp h
    rcases (C.classify_pair q).mp hq with hs | ⟨l, hl, hlm, he⟩
    · exact (C.dne k hk hkm (hd.symm.trans (C.spokes_dist hs))).elim
    · have hlk : l = k := C.dinj hl hlm hk hkm ((C.chordEdges_dist hl he).symm.trans hd)
      simpa only [hlk] using he
  · intro h
    exact mem_filter.mpr ⟨C.chordEdges_offDiag hk h, C.chordEdges_dist hk h⟩

lemma multiplicity_radius : distanceMultiplicity C.points 1 = m := by
  rw [distanceMultiplicity, C.radius_fibre, C.card_spokes]
  omega

lemma multiplicity_chord {k : ℕ} (hk : 1 ≤ k) (hkm : k < m) :
    distanceMultiplicity C.points (C.d k) = m - k := by
  rw [distanceMultiplicity, C.chord_fibre hk hkm, C.card_chordEdges hk]
  omega

lemma distances (hm : 1 ≤ m) : distanceSet C.points = insert 1 ((Ico 1 m).image C.d) := by
  classical
  ext d
  constructor
  · intro h
    obtain ⟨q, hq, rfl⟩ := mem_image.mp h
    rcases (C.classify_pair q).mp hq with hs | ⟨k, hk, hkm, he⟩
    · rw [C.spokes_dist hs]
      exact mem_insert_self _ _
    · apply mem_insert_of_mem
      exact mem_image.mpr ⟨k, mem_Ico.mpr ⟨hk, hkm⟩, (C.chordEdges_dist hk he).symm⟩
  · intro h
    rcases mem_insert.mp h with rfl | h
    · have he : (C.c, C.p 0) ∈ C.spokes := (C.mem_spokes _).mpr ⟨0, by omega, Or.inl rfl⟩
      exact mem_image.mpr ⟨(C.c, C.p 0), C.spokes_offDiag he, C.spokes_dist he⟩
    · obtain ⟨k, hk, rfl⟩ := mem_image.mp h
      obtain ⟨hk, hkm⟩ := mem_Ico.mp hk
      have he : (C.p 0, C.p k) ∈ C.chordEdges k := by
        apply (C.mem_chordEdges _ _).mpr
        exact ⟨0, by omega, Or.inl (by simp)⟩
      exact mem_image.mpr ⟨(C.p 0, C.p k), C.chordEdges_offDiag hk he, C.chordEdges_dist hk he⟩

lemma card_distances (hm : 1 ≤ m) : (distanceSet C.points).card = m := by
  classical
  have hn : (1 : ℝ) ∉ (Ico 1 m).image C.d := by
    intro h
    obtain ⟨k, hk, he⟩ := mem_image.mp h
    exact C.dne k (mem_Ico.mp hk).1 (mem_Ico.mp hk).2 he
  have hi : Set.InjOn C.d (↑(Ico 1 m) : Set ℕ) := by
    intro i hi j hj he
    exact C.dinj (mem_Ico.mp hi).1 (mem_Ico.mp hi).2
      (mem_Ico.mp hj).1 (mem_Ico.mp hj).2 he
  rw [C.distances hm, card_insert_of_notMem hn, card_image_iff.mpr hi]
  simp only [Nat.card_Ico]
  omega

lemma multiplicity_image (hm : 1 ≤ m) :
    (distanceSet C.points).image (distanceMultiplicity C.points) = Icc 1 m := by
  classical
  ext n
  constructor
  · intro h
    obtain ⟨d, hd, he⟩ := mem_image.mp h
    rw [C.distances hm] at hd
    rcases mem_insert.mp hd with rfl | hd
    · rw [C.multiplicity_radius] at he
      exact mem_Icc.mpr (by omega)
    · obtain ⟨k, hk, rfl⟩ := mem_image.mp hd
      obtain ⟨hk, hkm⟩ := mem_Ico.mp hk
      rw [C.multiplicity_chord hk hkm] at he
      exact mem_Icc.mpr (by omega)
  · intro h
    obtain ⟨hn, hnm⟩ := mem_Icc.mp h
    by_cases he : n = m
    · subst n
      apply mem_image.mpr
      refine ⟨1, ?_, C.multiplicity_radius⟩
      rw [C.distances hm]
      exact mem_insert_self _ _
    · have hk : 1 ≤ m - n := by omega
      have hkm : m - n < m := by omega
      apply mem_image.mpr
      refine ⟨C.d (m - n), ?_, ?_⟩
      · rw [C.distances hm]
        exact mem_insert_of_mem (mem_image.mpr ⟨m - n, mem_Ico.mpr ⟨hk, hkm⟩, rfl⟩)
      · rw [C.multiplicity_chord hk hkm]
        omega

end ArcConfig

#print axioms ArcConfig.card_points
#print axioms ArcConfig.card_distances
#print axioms ArcConfig.multiplicity_image

end Erdos958Large
