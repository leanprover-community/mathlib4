/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.LinearAlgebra.AffineSpace.Restrict

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

@[expose] public section

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

-- Although `simp` can prove this, it is still useful as a `simp` lemma, since the `simp`-generated
-- proof uses `range_eq_singleton_iff`, which does not apply when the LHS of this lemma appears
-- as part of a more complicated expression.
/-- The set of points in a simplex constructed with `mkOfPoint`. -/
@[simp] lemma range_mkOfPoint_points (p : P) : Set.range (mkOfPoint k p).points = {p} := by
  simp

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

lemma affineSpan_face_le {n : ℕ} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : ℕ}
    (h : #fs = m + 1) :
    affineSpan k (Set.range (s.face h).points) ≤ affineSpan k (Set.range s.points) :=
  affineSpan_mono k (s.range_face_points h ▸ Set.image_subset_range _ _)

lemma points_mem_affineSpan_face [Nontrivial k] {n : ℕ} (s : Simplex k P n)
    {fs : Finset (Fin (n + 1))} {m : ℕ} (h : #fs = m + 1) {i : Fin (n + 1)} :
    s.points i ∈ affineSpan k (Set.range (s.face h).points) ↔ i ∈ fs := by
  rw [range_face_points]
  exact s.independent.mem_affineSpan_iff i fs

/-- The face of a simplex with all but one point. -/
def faceOpposite {n : ℕ} [NeZero n] (s : Simplex k P n) (i : Fin (n + 1)) : Simplex k P (n - 1) :=
  s.face (fs := {i}ᶜ) (by simp [card_compl, NeZero.one_le])

@[simp] lemma range_faceOpposite_points {n : ℕ} [NeZero n] (s : Simplex k P n) (i : Fin (n + 1)) :
    Set.range (s.faceOpposite i).points = s.points '' {i}ᶜ := by
  simp [faceOpposite]

lemma affineSpan_faceOpposite_le {n : ℕ} [NeZero n] (s : Simplex k P n) (i : Fin (n + 1)) :
    affineSpan k (Set.range (s.faceOpposite i).points) ≤ affineSpan k (Set.range s.points) :=
  s.affineSpan_face_le _

lemma points_mem_affineSpan_faceOpposite [Nontrivial k] {n : ℕ} [NeZero n] (s : Simplex k P n)
    {i j : Fin (n + 1)} :
    s.points j ∈ affineSpan k (Set.range (s.faceOpposite i).points) ↔ j ≠ i := by
  rw [faceOpposite, s.points_mem_affineSpan_face]
  simp

lemma points_notMem_affineSpan_faceOpposite [Nontrivial k] {n : ℕ} [NeZero n] (s : Simplex k P n)
    (i : Fin (n + 1)) : s.points i ∉ affineSpan k (Set.range (s.faceOpposite i).points) := by
  rw [points_mem_affineSpan_faceOpposite]
  simp

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

lemma affineCombination_mem_affineSpan_faceOpposite_iff {n : ℕ} [NeZero n] {s : Simplex k P n}
    {w : Fin (n + 1) → k} (hw : ∑ i, w i = 1) {i : Fin (n + 1)} :
    Finset.univ.affineCombination k s.points w ∈
      affineSpan k (Set.range (s.faceOpposite i).points) ↔ w i = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [range_faceOpposite_points] at h
    exact s.independent.eq_zero_of_affineCombination_mem_affineSpan hw h (Finset.mem_univ i)
      (by simp)
  · rw [range_faceOpposite_points]
    rcases subsingleton_or_nontrivial k with hk | hk
    · have : Subsingleton V := Module.subsingleton k _
      have : Subsingleton P := (AddTorsor.subsingleton_iff V P).1 inferInstance
      rw [(affineSpan_eq_top_iff_nonempty_of_subsingleton k).2 (by simp)]
      simp
    · exact affineCombination_mem_affineSpan_image hw (by simpa using h) s.points

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

lemma range_face_reindex {m n : ℕ} (s : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1))
    {fs : Finset (Fin (n + 1))} {n' : ℕ} (h : #fs = n' + 1) :
    Set.range ((s.reindex e).face h).points =
      Set.range (s.face (fs := fs.map e.symm.toEmbedding) (h ▸ Finset.card_map _)).points := by
  simp only [range_face_points, reindex_points, Set.image_comp]
  simp

lemma range_faceOpposite_reindex {m n : ℕ} [NeZero m] [NeZero n] (s : Simplex k P m)
    (e : Fin (m + 1) ≃ Fin (n + 1)) (i : Fin (n + 1)) :
    Set.range ((s.reindex e).faceOpposite i).points =
      Set.range (s.faceOpposite (e.symm i)).points := by
  rw [faceOpposite, range_face_reindex]
  simp [Equiv.image_compl]

section restrict

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
    letI := Nonempty.map (AffineSubspace.inclusion hfS) inferInstance
    (s.restrict S₁ hS₁).map (f.restrict hfS) (AffineMap.restrict.injective hf _) =
      (s.map f hf).restrict S₂ (Eq.trans_le
          (by simp [AffineSubspace.map_span, Set.range_comp])
          (AffineSubspace.map_mono f hS₁) |>.trans hfS) := by
  rfl

/-- Restricting to `affineSpan k (Set.range s.points)` can be reversed by mapping through
`AffineSubspace.subtype`. -/
@[simp]
theorem restrict_map_subtype {n : ℕ} (s : Affine.Simplex k P n) :
    (s.restrict _ le_rfl).map (AffineSubspace.subtype _) Subtype.coe_injective = s :=
  rfl

lemma restrict_reindex {m n : ℕ} (s : Affine.Simplex k P n) (e : Fin (n + 1) ≃ Fin (m + 1))
    {S : AffineSubspace k P} (hS : affineSpan k (Set.range s.points) ≤ S) :
    letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.reindex e).restrict S (s.reindex_range_points e ▸ hS) = (s.restrict S hS).reindex e :=
  rfl

lemma face_restrict {n : ℕ} (s : Affine.Simplex k P n) {S : AffineSubspace k P}
    (hS : affineSpan k (Set.range s.points) ≤ S) {fs : Finset (Fin (n + 1))} {m : ℕ}
    (h : #fs = m + 1) :
    letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).face h = (s.face h).restrict S ((s.affineSpan_face_le h).trans hS) := by
  letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  ext i
  rw [restrict_points_coe]
  simp_rw [Affine.Simplex.face_points]
  simp

lemma faceOpposite_restrict {n : ℕ} [NeZero n] (s : Affine.Simplex k P n) {S : AffineSubspace k P}
    (hS : affineSpan k (Set.range s.points) ≤ S) (i : Fin (n + 1)) :
    letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).faceOpposite i = (s.faceOpposite i).restrict S
      ((s.affineSpan_faceOpposite_le i).trans hS) :=
  s.face_restrict hS _

end restrict

end Simplex

end Affine

namespace Affine

namespace Simplex

variable {k V V₂ P P₂ : Type*} [Ring k] [AddCommGroup V] [Module k V] [AffineSpace V P]
variable [AddCommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂]

/-- The interior of a simplex is the set of points that can be expressed as an affine combination
of the vertices with weights in a set `I`. -/
protected def setInterior (I : Set k) {n : ℕ} (s : Simplex k P n) : Set P :=
  {p | ∃ w : Fin (n + 1) → k,
    (∑ i, w i = 1) ∧ (∀ i, w i ∈ I) ∧ Finset.univ.affineCombination k s.points w = p}

lemma affineCombination_mem_setInterior_iff {I : Set k} {n : ℕ} {s : Simplex k P n}
    {w : Fin (n + 1) → k} (hw : ∑ i, w i = 1) :
    Finset.univ.affineCombination k s.points w ∈ s.setInterior I ↔ ∀ i, w i ∈ I := by
  refine ⟨fun ⟨w', hw', hw'01, hww'⟩ ↦ ?_, fun h ↦ ⟨w, hw, h, rfl⟩⟩
  simp_rw [← (affineIndependent_iff_eq_of_fintype_affineCombination_eq k s.points).1
    s.independent w' w hw' hw hww']
  exact hw'01

@[simp] lemma setInterior_reindex (I : Set k) {m n : ℕ} (s : Simplex k P n)
    (e : Fin (n + 1) ≃ Fin (m + 1)) : (s.reindex e).setInterior I = s.setInterior I := by
  ext p
  refine ⟨fun ⟨w, hw, hwI, h⟩ ↦ ?_, fun ⟨w, hw, hwI, h⟩ ↦ ?_⟩
  · subst h
    simp_rw [reindex]
    rw [← Function.comp_id w, ← e.self_comp_symm, ← Function.comp_assoc,
      ← Equiv.coe_toEmbedding, ← Finset.univ.affineCombination_map e.symm.toEmbedding,
      map_univ_equiv]
    have hw' : ∑ i, (w ∘ e) i = 1 := by rwa [sum_comp_equiv, map_univ_equiv]
    rw [affineCombination_mem_setInterior_iff hw']
    exact fun i ↦ hwI (e i)
  · subst h
    rw [← Function.comp_id w, ← Function.comp_id s.points, ← e.symm_comp_self,
      ← Function.comp_assoc, ← Function.comp_assoc, ← e.coe_toEmbedding,
      ← Finset.univ.affineCombination_map e.toEmbedding, map_univ_equiv]
    change Finset.univ.affineCombination k (s.reindex e).points _ ∈ _
    have hw' : ∑ i, (w ∘ e.symm) i = 1 := by rwa [sum_comp_equiv, map_univ_equiv]
    rw [affineCombination_mem_setInterior_iff hw']
    exact fun i ↦ hwI (e.symm i)

lemma setInterior_mono {I J : Set k} (hij : I ⊆ J) {n : ℕ} (s : Simplex k P n) :
    s.setInterior I ⊆ s.setInterior J :=
  fun _ ⟨w, hw, hw01, hww⟩ ↦ ⟨w, hw, fun i ↦ hij (hw01 i), hww⟩

lemma setInterior_subset_affineSpan {I : Set k} {n : ℕ} {s : Simplex k P n} :
    s.setInterior I ⊆ affineSpan k (Set.range s.points) := by
  rintro p ⟨w, hw, hi, rfl⟩
  exact affineCombination_mem_affineSpan_of_nonempty hw _

lemma setInterior_map (I : Set k) {n : ℕ} (s : Simplex k P n) {f : P →ᵃ[k] P₂}
    (hf : Function.Injective f) : (s.map f hf).setInterior I = f '' s.setInterior I := by
  ext p
  rw [Set.mem_image]
  by_cases hp : p ∈ affineSpan k (Set.range (s.map f hf).points)
  · obtain ⟨w, hw1, hw⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp
    rw [hw, Affine.Simplex.affineCombination_mem_setInterior_iff hw1, Simplex.map_points,
      ← Finset.map_affineCombination _ _ _ hw1]
    simp_rw [hf.eq_iff]
    simp [Affine.Simplex.affineCombination_mem_setInterior_iff hw1]
  · apply iff_of_false
    · exact fun h ↦ hp (Set.mem_of_mem_of_subset h (s.map f hf).setInterior_subset_affineSpan)
    · contrapose hp
      obtain ⟨q, hq, hqp⟩ := hp
      rw [s.map_points, Set.range_comp, ← AffineSubspace.map_span, AffineSubspace.mem_map]
      exact ⟨q, (Set.mem_of_mem_of_subset hq s.setInterior_subset_affineSpan), hqp⟩

lemma setInterior_restrict (I : Set k) {n : ℕ} (s : Simplex k P n) {S : AffineSubspace k P}
    (hS : affineSpan k (Set.range s.points) ≤ S) :
    letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).setInterior I = S.subtype ⁻¹' (s.setInterior I) := by
  letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  rw [← S.subtype_injective.image_injective.eq_iff,
    Set.image_preimage_eq_of_subset (s.setInterior_subset_affineSpan.trans (by simpa using! hS)),
    ← (s.restrict S hS).setInterior_map I S.subtype_injective]
  rfl

section PartialOrder
variable [PartialOrder k]

/-- The interior of a simplex is the set of points that can be expressed as an affine combination
of the vertices with weights strictly between 0 and 1. This is equivalent to the intrinsic
interior of the convex hull of the vertices. -/
protected def interior {n : ℕ} (s : Simplex k P n) : Set P :=
  s.setInterior (Set.Ioo 0 1)

@[simp] lemma interior_reindex {m n : ℕ} (s : Simplex k P n) (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).interior = s.interior :=
  s.setInterior_reindex _ _

lemma affineCombination_mem_interior_iff {n : ℕ} {s : Simplex k P n} {w : Fin (n + 1) → k}
    (hw : ∑ i, w i = 1) :
    Finset.univ.affineCombination k s.points w ∈ s.interior ↔ ∀ i, w i ∈ Set.Ioo 0 1 :=
  affineCombination_mem_setInterior_iff hw

/-- `s.closedInterior` is the set of points that can be expressed as an affine combination
of the vertices with weights between 0 and 1 inclusive. This is equivalent to the convex hull of
the vertices or the closure of the interior. -/
protected def closedInterior {n : ℕ} (s : Simplex k P n) : Set P :=
  s.setInterior (Set.Icc 0 1)

@[simp] lemma closedInterior_reindex {m n : ℕ} (s : Simplex k P n) (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).closedInterior = s.closedInterior :=
  s.setInterior_reindex _ _

lemma affineCombination_mem_closedInterior_iff {n : ℕ} {s : Simplex k P n} {w : Fin (n + 1) → k}
    (hw : ∑ i, w i = 1) :
    Finset.univ.affineCombination k s.points w ∈ s.closedInterior ↔ ∀ i, w i ∈ Set.Icc 0 1 :=
  affineCombination_mem_setInterior_iff hw

lemma interior_subset_closedInterior {n : ℕ} (s : Simplex k P n) :
    s.interior ⊆ s.closedInterior :=
  fun _ ⟨w, hw, hw01, hww⟩ ↦ ⟨w, hw, fun i ↦ ⟨(hw01 i).1.le, (hw01 i).2.le⟩, hww⟩

lemma point_notMem_interior {n : ℕ} (s : Simplex k P n) (i : Fin (n + 1)) :
    s.points i ∉ s.interior := by
  rw [← Finset.univ.affineCombination_piSingle k s.points (Finset.mem_univ i),
    affineCombination_mem_interior_iff (Fintype.sum_pi_single' _ _), not_forall]
  exact ⟨i, by simp⟩

lemma point_mem_closedInterior [ZeroLEOneClass k] {n : ℕ} (s : Simplex k P n) (i : Fin (n + 1)) :
    s.points i ∈ s.closedInterior := by
  rw [← Finset.univ.affineCombination_piSingle k s.points (Finset.mem_univ i),
    affineCombination_mem_closedInterior_iff (Fintype.sum_pi_single' _ _)]
  intro j
  obtain rfl | hj := eq_or_ne j i <;> simp_all

lemma nonempty_closedInterior [ZeroLEOneClass k] {n : ℕ} (s : Simplex k P n) :
    s.closedInterior.Nonempty :=
  ⟨s.points 0, s.point_mem_closedInterior 0⟩

lemma interior_ssubset_closedInterior [ZeroLEOneClass k] {n : ℕ} (s : Simplex k P n) :
    s.interior ⊂ s.closedInterior := by
  rw [Set.ssubset_iff_exists]
  exact ⟨s.interior_subset_closedInterior, s.points 0, s.point_mem_closedInterior 0,
    s.point_notMem_interior 0⟩

lemma closedInterior_subset_affineSpan {n : ℕ} {s : Simplex k P n} :
    s.closedInterior ⊆ affineSpan k (Set.range s.points) := by
  rintro p ⟨w, hw, hi, rfl⟩
  exact affineCombination_mem_affineSpan_of_nonempty hw _

@[simp] lemma interior_eq_empty (s : Simplex k P 0) : s.interior = ∅ := by
  ext p
  simp only [Simplex.interior, Simplex.setInterior, Nat.reduceAdd, univ_unique, Fin.default_eq_zero,
    Fin.isValue, sum_singleton, Set.mem_Ioo, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
    not_exists, not_and]
  intro w h hi
  simpa [h] using hi 0

@[simp] lemma closedInterior_eq_singleton [ZeroLEOneClass k] (s : Simplex k P 0) :
    s.closedInterior = {s.points 0} := by
  ext p
  simp only [Simplex.closedInterior, Simplex.setInterior, Nat.reduceAdd, univ_unique,
    Fin.default_eq_zero, Fin.isValue, sum_singleton, Set.mem_Icc, Set.mem_setOf_eq,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, h0, hi, rfl⟩
    simp [affineCombination_apply, h0]
  · rintro rfl
    exact ⟨1, by simp [affineCombination_apply]⟩

omit [PartialOrder k] in
lemma affineCombination_mem_setInterior_face_iff_mem (I : Set k) {n : ℕ} (s : Simplex k P n)
    {fs : Finset (Fin (n + 1))} {m : ℕ} (h : #fs = m + 1) {w : Fin (n + 1) → k}
    (hw : ∑ i, w i = 1) : Finset.univ.affineCombination k s.points w ∈ (s.face h).setInterior I ↔
      (∀ i ∈ fs, w i ∈ I) ∧ (∀ i ∉ fs, w i = 0) := by
  refine ⟨fun hi ↦ ?_, fun ⟨hii, hi0⟩ ↦ ?_⟩
  · obtain ⟨w', hw', he⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype
      (Set.mem_of_mem_of_subset hi setInterior_subset_affineSpan)
    rw [he, affineCombination_mem_setInterior_iff hw'] at hi
    have he' := s.independent.indicator_extend_eq_of_affineCombination_comp_embedding_eq_of_fintype
      hw hw' (fs.orderEmbOfFin h).toEmbedding he.symm
    simp_rw [he'.symm]
    refine ⟨fun i hi ↦ ?_, fun i hi ↦ by simp [hi]⟩
    simp only [RelEmbedding.coe_toEmbedding, range_orderEmbOfFin, mem_coe, hi, Set.indicator_of_mem]
    rw [← mem_coe, ← fs.range_orderEmbOfFin h] at hi
    obtain ⟨j, rfl⟩ := hi
    simp [(fs.orderEmbOfFin h).injective.extend_apply, hi]
  · let w' : Fin (m + 1) → k := w ∘ fs.orderEmbOfFin h
    have hw' : ∑ i, w' i = 1 := by
      rw [Fintype.sum_of_injective _ (fs.orderEmbOfFin h).injective w' w
        (fun i hi ↦ hi0 _ (by simpa using hi)) (fun _ ↦ rfl), hw]
    have hw'01 (i) : w' i ∈ I := hii (fs.orderEmbOfFin h i) (by simp)
    rw [← (s.face h).affineCombination_mem_setInterior_iff hw'] at hw'01
    convert! hw'01
    convert! Finset.univ.affineCombination_map (fs.orderEmbOfFin h).toEmbedding w s.points using 1
    simp only [map_orderEmbOfFin_univ, Finset.affineCombination_indicator_subset _ _ fs.subset_univ]
    congr
    grind [Set.indicator_eq_self, support_subset_iff]

lemma affineCombination_mem_interior_face_iff_mem_Ioo {n : ℕ} (s : Simplex k P n)
    {fs : Finset (Fin (n + 1))} {m : ℕ} (h : #fs = m + 1) {w : Fin (n + 1) → k}
    (hw : ∑ i, w i = 1) : Finset.univ.affineCombination k s.points w ∈ (s.face h).interior ↔
      (∀ i ∈ fs, w i ∈ Set.Ioo 0 1) ∧ (∀ i ∉ fs, w i = 0) :=
  affineCombination_mem_setInterior_face_iff_mem _ _ _ hw

lemma affineCombination_mem_closedInterior_face_iff_mem_Icc {n : ℕ} (s : Simplex k P n)
    {fs : Finset (Fin (n + 1))} {m : ℕ} (h : #fs = m + 1) {w : Fin (n + 1) → k}
    (hw : ∑ i, w i = 1) : Finset.univ.affineCombination k s.points w ∈ (s.face h).closedInterior ↔
      (∀ i ∈ fs, w i ∈ Set.Icc 0 1) ∧ (∀ i ∉ fs, w i = 0) :=
  affineCombination_mem_setInterior_face_iff_mem _ _ _ hw

lemma affineCombination_mem_interior_face_iff_pos [IsOrderedAddMonoid k] {n : ℕ}
    (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : ℕ} [NeZero m] (h : #fs = m + 1)
    {w : Fin (n + 1) → k} (hw : ∑ i, w i = 1) :
    Finset.univ.affineCombination k s.points w ∈ (s.face h).interior ↔
      (∀ i ∈ fs, 0 < w i) ∧ (∀ i ∉ fs, w i = 0) := by
  rw [s.affineCombination_mem_interior_face_iff_mem_Ioo h hw]
  refine ⟨by grind, fun ⟨hii, hi0⟩ ↦ ⟨fun i hi ↦ ⟨hii i hi, ?_⟩, hi0⟩⟩
  rw [← hw, ← Finset.sum_subset (Finset.subset_univ fs) fun j _ ↦ hi0 j]
  obtain ⟨j, hj, hji⟩ := fs.exists_mem_ne (by grind [→ NeZero.ne]) i
  exact Finset.single_lt_sum hji hi hj (hii j hj) fun t ht _ ↦ (hii t ht).le

lemma affineCombination_mem_closedInterior_face_iff_nonneg [IsOrderedAddMonoid k] {n : ℕ}
    (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : ℕ} (h : #fs = m + 1)
    {w : Fin (n + 1) → k} (hw : ∑ i, w i = 1) :
    Finset.univ.affineCombination k s.points w ∈ (s.face h).closedInterior ↔
      (∀ i ∈ fs, 0 ≤ w i) ∧ (∀ i ∉ fs, w i = 0) := by
  rw [s.affineCombination_mem_closedInterior_face_iff_mem_Icc h hw]
  refine ⟨by grind, fun ⟨hii, hi0⟩ ↦ ⟨fun i hi ↦ ⟨hii i hi, ?_⟩, hi0⟩⟩
  rw [← hw, ← Finset.sum_subset (Finset.subset_univ fs) fun j _ ↦ hi0 j]
  exact Finset.single_le_sum (fun t ht ↦ (hii t ht)) hi

lemma interior_map {n : ℕ} (s : Simplex k P n) {f : P →ᵃ[k] P₂} (hf : Function.Injective f) :
    (s.map f hf).interior = f '' s.interior :=
  s.setInterior_map _ hf

lemma closedInterior_map {n : ℕ} (s : Simplex k P n) {f : P →ᵃ[k] P₂} (hf : Function.Injective f) :
    (s.map f hf).closedInterior = f '' s.closedInterior :=
  s.setInterior_map _ hf

lemma interior_restrict {n : ℕ} (s : Simplex k P n) {S : AffineSubspace k P}
    (hS : affineSpan k (Set.range s.points) ≤ S) :
    letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).interior = S.subtype ⁻¹' s.interior :=
  s.setInterior_restrict _ hS

lemma closedInterior_restrict {n : ℕ} (s : Simplex k P n) {S : AffineSubspace k P}
    (hS : affineSpan k (Set.range s.points) ≤ S) :
    letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).closedInterior = S.subtype ⁻¹' s.closedInterior :=
  s.setInterior_restrict _ hS

theorem closedInterior_face_subset_closedInterior [ZeroLEOneClass k] {n : ℕ} (s : Simplex k P n)
    {fs : Finset (Fin (n + 1))} {m : ℕ} (h : #fs = m + 1) :
    (s.face h).closedInterior ⊆ s.closedInterior := by
  intro p hp
  have hp' : p ∈ affineSpan k (Set.range s.points) :=
    Set.mem_of_mem_of_subset hp <|
      (s.face h).closedInterior_subset_affineSpan.trans <|
        affineSpan_mono k <| by simp
  obtain ⟨w, hw1, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp'
  rw [affineCombination_mem_closedInterior_face_iff_mem_Icc _ _ hw1] at hp
  rw [affineCombination_mem_closedInterior_iff hw1]
  intro i
  by_cases hi : i ∈ fs <;> aesop

@[simp]
theorem point_mem_closedInterior_face_iff [Nontrivial k] [ZeroLEOneClass k] {n : ℕ}
    (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : ℕ} (h : #fs = m + 1) {j : Fin (n + 1)} :
    s.points j ∈ (s.face h).closedInterior ↔ j ∈ fs := by
  refine ⟨fun hj ↦ ?_, fun hfs ↦ ?_⟩
  · suffices s.points j ∈ affineSpan k (s.points '' fs) by simpa
    obtain ⟨w, hw, hw', hs⟩ := hj
    rw [← hs]
    exact Set.mem_of_mem_of_subset (affineCombination_mem_affineSpan hw _) (by simp)
  · obtain ⟨i, rfl⟩ : ∃ i, fs.orderEmbOfFin h i = j := range_orderEmbOfFin fs h |>.ge hfs
    exact point_mem_closedInterior _ _

theorem closedInterior_face_ssubset_closedInterior [Nontrivial k] [ZeroLEOneClass k] {n : ℕ}
    (s : Simplex k P n) {fs : Finset (Fin (n + 1))} (hfs : fs ≠ .univ) {m : ℕ} (h : #fs = m + 1) :
    (s.face h).closedInterior ⊂ s.closedInterior := by
  obtain ⟨a, ha⟩ := Classical.not_forall.mp <| Finset.eq_univ_iff_forall.not.mp hfs
  apply (Set.ssubset_iff_of_subset (s.closedInterior_face_subset_closedInterior h)).mpr
  exact ⟨s.points a, s.point_mem_closedInterior a, fun hs ↦ ha (by simpa using hs)⟩

theorem disjoint_interior_closedInterior_face [Nontrivial k] [ZeroLEOneClass k] {n : ℕ}
    (s : Simplex k P n) {fs : Finset (Fin (n + 1))} (hfs : fs ≠ .univ) {m : ℕ} (h : #fs = m + 1) :
    Disjoint s.interior (s.face h).closedInterior := by
  refine Set.disjoint_left.mpr fun p hleft hright ↦ ?_
  have hp : p ∈ affineSpan k (Set.range s.points) :=
    Set.mem_of_mem_of_subset hleft <| s.interior_subset_closedInterior.trans <|
      s.closedInterior_subset_affineSpan
  grind [affineCombination_mem_interior_iff, affineCombination_mem_closedInterior_face_iff_mem_Icc,
    eq_affineCombination_of_mem_affineSpan_of_fintype]

@[simp]
theorem point_mem_closedInterior_faceOpposite_iff [Nontrivial k] [ZeroLEOneClass k] {n : ℕ}
    [NeZero n] (s : Simplex k P n) {i j : Fin (n + 1)} :
    s.points j ∈ (s.faceOpposite i).closedInterior ↔ j ≠ i := by
  simp [faceOpposite]

theorem closedInterior_faceOpposite_subset_closedInterior [ZeroLEOneClass k] {n : ℕ} [NeZero n]
    (s : Simplex k P n) (i : Fin (n + 1)) :
    (s.faceOpposite i).closedInterior ⊆ s.closedInterior :=
  s.closedInterior_face_subset_closedInterior _

theorem closedInterior_faceOpposite_ssubset_closedInterior [Nontrivial k] [ZeroLEOneClass k] {n : ℕ}
    [NeZero n] (s : Simplex k P n) (i : Fin (n + 1)) :
    (s.faceOpposite i).closedInterior ⊂ s.closedInterior :=
  s.closedInterior_face_ssubset_closedInterior (by simp) _

theorem disjoint_interior_closedInterior_faceOpposite [Nontrivial k] [ZeroLEOneClass k] {n : ℕ}
    [NeZero n] (s : Simplex k P n) (i : Fin (n + 1)) :
    Disjoint s.interior (s.faceOpposite i).closedInterior :=
  s.disjoint_interior_closedInterior_face (by simp) _

end PartialOrder

section LinearOrder
variable [LinearOrder k]

/-- The closed interior is the union of the open interior and the surface. -/
theorem closedInterior_eq_interior_union [IsOrderedAddMonoid k] [ZeroLEOneClass k] {n : ℕ}
    [NeZero n] (s : Simplex k P n) :
    s.closedInterior = s.interior ∪ ⋃ i : Fin (n + 1), (s.faceOpposite i).closedInterior := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain hp' := Set.mem_of_mem_of_subset hp s.closedInterior_subset_affineSpan
    obtain ⟨w, hw1, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp'
    rw [Set.mem_union, or_iff_not_imp_left]
    intro h
    rw [affineCombination_mem_closedInterior_iff hw1] at hp
    simp_rw [affineCombination_mem_interior_iff hw1, Set.mem_Ioo] at h
    push +distrib Not at h
    obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), w j = 0 := by
      obtain ⟨i, hi | hi⟩ := h
      · exact ⟨i, le_antisymm hi (hp i).1⟩
      · have hi1 : w i = 1 := le_antisymm (hp i).2 hi
        rw [← hi1, ← Finset.sum_erase_add _ _ (show i ∈ Finset.univ by simp), add_eq_right,
          Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ (hp j).1)] at hw1
        exact ⟨i + 1, hw1 _ (by simp)⟩
    refine Set.mem_iUnion.mpr ⟨j, ?_⟩
    rw [faceOpposite, affineCombination_mem_closedInterior_face_iff_mem_Icc _ _ hw1]
    exact ⟨fun k _ ↦ hp k, by simpa using hj⟩
  · refine Set.union_subset s.interior_subset_closedInterior (Set.iUnion_subset fun i ↦ ?_)
    exact s.closedInterior_faceOpposite_subset_closedInterior i

theorem closedInterior_sdiff_interior [Nontrivial k] [IsOrderedAddMonoid k] [ZeroLEOneClass k]
    {n : ℕ} [NeZero n] (s : Simplex k P n) :
    s.closedInterior \ s.interior = ⋃ i : Fin (n + 1), (s.faceOpposite i).closedInterior := by
  simpa [closedInterior_eq_interior_union] using
    fun i ↦ (s.disjoint_interior_closedInterior_faceOpposite i).symm

@[deprecated (since := "2026-06-03")]
alias closedInterior_diff_interior := closedInterior_sdiff_interior

end LinearOrder

end Simplex

end Affine
