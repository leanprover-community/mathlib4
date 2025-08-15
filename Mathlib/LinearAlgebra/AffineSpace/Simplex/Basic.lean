/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.AffineSpace.Restrict

/-!
# Simplex in affine space

This file defines n-dimensional simplices in affine space.

## Main definitions

* `Simplex` is a bundled type with collection of `n + 1` points in affine space that are affinely
  independent, where `n` is the dimension of the simplex.

* `Triangle` is a simplex with three points, defined as an abbreviation for simplex with `n = 2`.

* `face` is a simplex with a subset of the points of the original simplex.

## References

* https://en.wikipedia.org/wiki/Simplex

-/

noncomputable section

open Finset Function Module
open scoped Affine

namespace Affine

variable (k : Type*) {V V₂ V₃ : Type*} (P P₂ P₃ : Type*)
variable [Ring k] [AddCommGroup V] [AddCommGroup V₂] [AddCommGroup V₃]
variable [Module k V] [Module k V₂] [Module k V₃]
variable [AffineSpace V P] [AffineSpace V₂ P₂] [AffineSpace V₃ P₃]

/-- A `Simplex k P n` is a collection of `n + 1` affinely
independent points. -/
structure Simplex (n : ℕ) where
  points : Fin (n + 1) → P
  independent : AffineIndependent k points

/-- A `Triangle k P` is a collection of three affinely independent points. -/
abbrev Triangle :=
  Simplex k P 2

namespace Simplex

variable {P P₂ P₃}

/-- Construct a 0-simplex from a point. -/
def mkOfPoint (p : P) : Simplex k P 0 :=
  have : Subsingleton (Fin (1 + 0)) := by rw [add_zero]; infer_instance
  ⟨fun _ => p, affineIndependent_of_subsingleton k _⟩

/-- The point in a simplex constructed with `mkOfPoint`. -/
@[simp]
theorem mkOfPoint_points (p : P) (i : Fin 1) : (mkOfPoint k p).points i = p :=
  rfl

instance [Inhabited P] : Inhabited (Simplex k P 0) :=
  ⟨mkOfPoint k default⟩

instance nonempty : Nonempty (Simplex k P 0) :=
  ⟨mkOfPoint k <| AddTorsor.nonempty.some⟩

variable {k}

/-- Two simplices are equal if they have the same points. -/
@[ext]
theorem ext {n : ℕ} {s1 s2 : Simplex k P n} (h : ∀ i, s1.points i = s2.points i) : s1 = s2 := by
  cases s1
  cases s2
  congr with i
  exact h i

/-- Two simplices are equal if and only if they have the same points. -/
add_decl_doc Affine.Simplex.ext_iff

/-- A face of a simplex is a simplex with the given subset of
points. -/
def face {n : ℕ} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : ℕ} (h : #fs = m + 1) :
    Simplex k P m :=
  ⟨s.points ∘ fs.orderEmbOfFin h, s.independent.comp_embedding (fs.orderEmbOfFin h).toEmbedding⟩

/-- The points of a face of a simplex are given by `mono_of_fin`. -/
theorem face_points {n : ℕ} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : ℕ}
    (h : #fs = m + 1) (i : Fin (m + 1)) :
    (s.face h).points i = s.points (fs.orderEmbOfFin h i) :=
  rfl

/-- The points of a face of a simplex are given by `mono_of_fin`. -/
theorem face_points' {n : ℕ} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : ℕ}
    (h : #fs = m + 1) : (s.face h).points = s.points ∘ fs.orderEmbOfFin h :=
  rfl

/-- A single-point face equals the 0-simplex constructed with
`mkOfPoint`. -/
@[simp]
theorem face_eq_mkOfPoint {n : ℕ} (s : Simplex k P n) (i : Fin (n + 1)) :
    s.face (Finset.card_singleton i) = mkOfPoint k (s.points i) := by
  ext
  simp [Affine.Simplex.mkOfPoint_points, Affine.Simplex.face_points, Finset.orderEmbOfFin_singleton]

/-- The set of points of a face. -/
@[simp]
theorem range_face_points {n : ℕ} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : ℕ}
    (h : #fs = m + 1) : Set.range (s.face h).points = s.points '' ↑fs := by
  rw [face_points', Set.range_comp, Finset.range_orderEmbOfFin]

/-- The face of a simplex with all but one point. -/
def faceOpposite {n : ℕ} [NeZero n] (s : Simplex k P n) (i : Fin (n + 1)) : Simplex k P (n - 1) :=
  s.face (fs := {i}ᶜ) (by simp [card_compl, NeZero.one_le])

@[simp] lemma range_faceOpposite_points {n : ℕ} [NeZero n] (s : Simplex k P n) (i : Fin (n + 1)) :
    Set.range (s.faceOpposite i).points = s.points '' {i}ᶜ  := by
  simp [faceOpposite]

lemma faceOpposite_point_eq_point_succAbove {n : ℕ} [NeZero n] (s : Simplex k P n)
    (i : Fin (n + 1)) (j : Fin (n - 1 + 1)) :
    (s.faceOpposite i).points j =
      s.points (Fin.succAbove i (Fin.cast (Nat.sub_one_add_one (NeZero.ne _)) j)) := by
  simp_rw [faceOpposite, face, comp_apply, Finset.orderEmbOfFin_compl_singleton_apply]

lemma faceOpposite_point_eq_point_rev (s : Simplex k P 1) (i : Fin 2) (n : Fin 1) :
    (s.faceOpposite i).points n = s.points i.rev := by
  have h : i.rev = Fin.succAbove i n := by decide +revert
  simp [h, faceOpposite_point_eq_point_succAbove]

@[simp] lemma faceOpposite_point_eq_point_one (s : Simplex k P 1) (n : Fin 1) :
    (s.faceOpposite 0).points n = s.points 1 :=
  s.faceOpposite_point_eq_point_rev _ _

@[simp] lemma faceOpposite_point_eq_point_zero (s : Simplex k P 1) (n : Fin 1) :
    (s.faceOpposite 1).points n = s.points 0 :=
  s.faceOpposite_point_eq_point_rev _ _

/-- Needed to make `affineSpan (s.points '' {i}ᶜ)` nonempty. -/
instance {α} [Nontrivial α] (i : α) : Nonempty ({i}ᶜ : Set _) :=
  (Set.nonempty_compl_of_nontrivial i).to_subtype

@[simp] lemma mem_affineSpan_image_iff [Nontrivial k] {n : ℕ} (s : Simplex k P n)
    {fs : Set (Fin (n + 1))} {i : Fin (n + 1)} :
    s.points i ∈ affineSpan k (s.points '' fs) ↔ i ∈ fs :=
  s.independent.mem_affineSpan_iff _ _

@[deprecated mem_affineSpan_image_iff (since := "2025-05-18")]
lemma mem_affineSpan_range_face_points_iff [Nontrivial k] {n : ℕ} (s : Simplex k P n)
    {fs : Finset (Fin (n + 1))} {m : ℕ} (h : #fs = m + 1) {i : Fin (n + 1)} :
    s.points i ∈ affineSpan k (Set.range (s.face h).points) ↔ i ∈ fs := by
  simp

@[deprecated mem_affineSpan_image_iff (since := "2025-05-18")]
lemma mem_affineSpan_range_faceOpposite_points_iff [Nontrivial k] {n : ℕ} [NeZero n]
    (s : Simplex k P n) {i j : Fin (n + 1)} :
    s.points i ∈ affineSpan k (Set.range (s.faceOpposite j).points) ↔ i ≠ j := by
  simp

/-- Push forward an affine simplex under an injective affine map. -/
@[simps -fullyApplied]
def map {n : ℕ} (s : Affine.Simplex k P n) (f : P →ᵃ[k] P₂) (hf : Function.Injective f) :
    Affine.Simplex k P₂ n where
  points := f ∘ s.points
  independent := s.independent.map' f hf

@[simp]
theorem map_id {n : ℕ} (s : Affine.Simplex k P n) :
    s.map (AffineMap.id _ _) Function.injective_id = s :=
  ext fun _ => rfl

theorem map_comp {n : ℕ} (s : Affine.Simplex k P n)
    (f : P →ᵃ[k] P₂) (hf : Function.Injective f)
    (g : P₂ →ᵃ[k] P₃) (hg : Function.Injective g) :
    s.map (g.comp f) (hg.comp hf) = (s.map f hf).map g hg :=
  ext fun _ => rfl

@[simp]
theorem face_map {n : ℕ} (s : Simplex k P n) (f : P →ᵃ[k] P₂) (hf : Function.Injective f)
    {fs : Finset (Fin (n + 1))} {m : ℕ} (h : #fs = m + 1) :
    (s.map f hf).face h = (s.face h).map f hf :=
  rfl

@[simp]
theorem faceOpposite_map {n : ℕ} [NeZero n] (s : Simplex k P n) (f : P →ᵃ[k] P₂)
    (hf : Function.Injective f) (i : Fin (n + 1)) :
    (s.map f hf).faceOpposite i = (s.faceOpposite i).map f hf :=
  rfl

@[simp]
theorem map_mkOfPoint (f : P →ᵃ[k] P₂) (hf : Function.Injective f) (p : P) :
    (mkOfPoint k p).map f hf = mkOfPoint k (f p) :=
  rfl

/-- Remap a simplex along an `Equiv` of index types. -/
@[simps]
def reindex {m n : ℕ} (s : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1)) : Simplex k P n :=
  ⟨s.points ∘ e.symm, (affineIndependent_equiv e.symm).2 s.independent⟩

/-- Reindexing by `Equiv.refl` yields the original simplex. -/
@[simp]
theorem reindex_refl {n : ℕ} (s : Simplex k P n) : s.reindex (Equiv.refl (Fin (n + 1))) = s :=
  ext fun _ => rfl

/-- Reindexing by the composition of two equivalences is the same as reindexing twice. -/
@[simp]
theorem reindex_trans {n₁ n₂ n₃ : ℕ} (e₁₂ : Fin (n₁ + 1) ≃ Fin (n₂ + 1))
    (e₂₃ : Fin (n₂ + 1) ≃ Fin (n₃ + 1)) (s : Simplex k P n₁) :
    s.reindex (e₁₂.trans e₂₃) = (s.reindex e₁₂).reindex e₂₃ :=
  rfl

/-- Reindexing by an equivalence and its inverse yields the original simplex. -/
@[simp]
theorem reindex_reindex_symm {m n : ℕ} (s : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1)) :
    (s.reindex e).reindex e.symm = s := by rw [← reindex_trans, Equiv.self_trans_symm, reindex_refl]

/-- Reindexing by the inverse of an equivalence and that equivalence yields the original simplex. -/
@[simp]
theorem reindex_symm_reindex {m n : ℕ} (s : Simplex k P m) (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e.symm).reindex e = s := by rw [← reindex_trans, Equiv.symm_trans_self, reindex_refl]

/-- Reindexing a simplex produces one with the same set of points. -/
@[simp]
theorem reindex_range_points {m n : ℕ} (s : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1)) :
    Set.range (s.reindex e).points = Set.range s.points := by
  rw [reindex, Set.range_comp, Equiv.range_eq_univ, Set.image_univ]

theorem reindex_map {m n : ℕ} (s : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1))
    (f : P →ᵃ[k] P₂) (hf : Function.Injective f) :
    (s.map f hf).reindex e = (s.reindex e).map f hf :=
  rfl

section restrict
attribute [local instance] AffineSubspace.toAddTorsor

/-- Restrict an affine simplex to an affine subspace that contains it. -/
@[simps]
def restrict {n : ℕ} (s : Affine.Simplex k P n) (S : AffineSubspace k P)
    (hS : affineSpan k (Set.range s.points) ≤ S) :
    letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    Affine.Simplex (V := S.direction) k S n :=
  letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  { points i := ⟨s.points i, hS <| mem_affineSpan _ <| Set.mem_range_self _⟩
    independent := AffineIndependent.of_comp S.subtype s.independent }

/-- Restricting to `S₁` then mapping to a larger `S₂` is the same as restricting to `S₂`. -/
@[simp]
theorem restrict_map_inclusion {n : ℕ} (s : Affine.Simplex k P n)
    (S₁ S₂ : AffineSubspace k P) (hS₁) (hS₂ : S₁ ≤ S₂) :
    letI := Nonempty.map (AffineSubspace.inclusion hS₁) inferInstance
    letI := Nonempty.map (Set.inclusion hS₂) ‹_›
    (s.restrict S₁ hS₁).map (AffineSubspace.inclusion hS₂) (Set.inclusion_injective hS₂) =
      s.restrict S₂ (hS₁.trans hS₂) :=
  rfl

@[simp]
theorem map_subtype_restrict
    {n : ℕ} (S : AffineSubspace k P) [Nonempty S] (s : Affine.Simplex k S n) :
    (s.map (AffineSubspace.subtype _) Subtype.coe_injective).restrict
      S (affineSpan_le.2 <| by rintro x ⟨y, rfl⟩; exact Subtype.prop _) = s := by
  rfl

/-- Restricting to `S₁` then mapping through the restriction of `f` to `S₁ →ᵃ[k] S₂` is the same
as mapping through unrestricted `f`, then restricting to `S₂`. -/
theorem restrict_map_restrict
    {n : ℕ} (s : Affine.Simplex k P n) (f : P →ᵃ[k] P₂) (hf : Function.Injective f)
    (S₁ : AffineSubspace k P) (S₂ : AffineSubspace k P₂)
    (hS₁ : affineSpan k (Set.range s.points) ≤ S₁) (hfS : AffineSubspace.map f S₁ ≤ S₂) :
    letI := Nonempty.map (AffineSubspace.inclusion hS₁) inferInstance
    letI : Nonempty (S₁.map f) := AffineSubspace.nonempty_map
    letI := Nonempty.map (AffineSubspace.inclusion hfS) inferInstance
    (s.restrict S₁ hS₁).map (f.restrict hfS) (AffineMap.restrict.injective hf _) =
      (s.map f hf).restrict S₂ (
        Eq.trans_le
          (by simp [AffineSubspace.map_span, Set.range_comp])
          (AffineSubspace.map_mono f hS₁) |>.trans hfS) := by
  rfl

/-- Restricting to `affineSpan k (Set.range s.points)` can be reversed by mapping through
`AffineSubspace.subtype`. -/
@[simp]
theorem restrict_map_subtype {n : ℕ} (s : Affine.Simplex k P n) :
    (s.restrict _ le_rfl).map (AffineSubspace.subtype _) Subtype.coe_injective = s :=
  rfl

end restrict

end Simplex

end Affine

namespace Affine

namespace Simplex

variable {k V P : Type*} [Ring k] [PartialOrder k] [AddCommGroup V] [Module k V] [AffineSpace V P]

/-- The interior of a simplex is the set of points that can be expressed as an affine combination
of the vertices with weights strictly between 0 and 1. This is equivalent to the intrinsic
interior of the convex hull of the vertices. -/
protected def interior {n : ℕ} (s : Simplex k P n) : Set P :=
  {p | ∃ w : Fin (n + 1) → k,
    (∑ i, w i = 1) ∧ (∀ i, w i ∈ Set.Ioo 0 1) ∧ Finset.univ.affineCombination k s.points w = p}

lemma affineCombination_mem_interior_iff {n : ℕ} {s : Simplex k P n} {w : Fin (n + 1) → k}
    (hw : ∑ i, w i = 1) :
    Finset.univ.affineCombination k s.points w ∈ s.interior ↔ ∀ i, w i ∈ Set.Ioo 0 1 := by
  refine ⟨fun ⟨w', hw', hw'01, hww'⟩ ↦ ?_, fun h ↦ ⟨w, hw, h, rfl⟩⟩
  simp_rw [← (affineIndependent_iff_eq_of_fintype_affineCombination_eq k s.points).1
    s.independent w' w hw' hw hww']
  exact hw'01

/-- `s.closedInterior` is the set of points that can be expressed as an affine combination
of the vertices with weights between 0 and 1 inclusive. This is equivalent to the convex hull of
the vertices or the closure of the interior. -/
protected def closedInterior {n : ℕ} (s : Simplex k P n) : Set P :=
  {p | ∃ w : Fin (n + 1) → k,
    (∑ i, w i = 1) ∧ (∀ i, w i ∈ Set.Icc 0 1) ∧ Finset.univ.affineCombination k s.points w = p}

lemma affineCombination_mem_closedInterior_iff {n : ℕ} {s : Simplex k P n} {w : Fin (n + 1) → k}
    (hw : ∑ i, w i = 1) :
    Finset.univ.affineCombination k s.points w ∈ s.closedInterior ↔ ∀ i, w i ∈ Set.Icc 0 1 := by
  refine ⟨fun ⟨w', hw', hw'01, hww'⟩ ↦ ?_, fun h ↦ ⟨w, hw, h, rfl⟩⟩
  simp_rw [← (affineIndependent_iff_eq_of_fintype_affineCombination_eq k s.points).1
    s.independent w' w hw' hw hww']
  exact hw'01

lemma interior_subset_closedInterior {n : ℕ} (s : Simplex k P n) :
    s.interior ⊆ s.closedInterior :=
  fun _ ⟨w, hw, hw01, hww⟩ ↦ ⟨w, hw, fun i ↦ ⟨(hw01 i).1.le, (hw01 i).2.le⟩, hww⟩

lemma closedInterior_subset_affineSpan {n : ℕ} {s : Simplex k P n} :
    s.closedInterior ⊆ affineSpan k (Set.range s.points) := by
  rintro p ⟨w, hw, hi, rfl⟩
  exact affineCombination_mem_affineSpan_of_nonempty hw _

@[simp] lemma interior_eq_empty (s : Simplex k P 0) : s.interior = ∅ := by
  ext p
  simp only [Simplex.interior, Nat.reduceAdd, univ_unique, Fin.default_eq_zero, Fin.isValue,
    sum_singleton, Set.mem_Ioo, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists,
    not_and]
  intro w h hi
  simpa [h] using hi 0

@[simp] lemma closedInterior_eq_singleton [ZeroLEOneClass k] (s : Simplex k P 0) :
    s.closedInterior = {s.points 0} := by
  ext p
  simp only [Simplex.closedInterior, Nat.reduceAdd, univ_unique, Fin.default_eq_zero, Fin.isValue,
    sum_singleton, Set.mem_Icc, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, h0, hi, rfl⟩
    simp [affineCombination_apply, h0]
  · rintro rfl
    exact ⟨1, by simp [affineCombination_apply]⟩

end Simplex

end Affine
