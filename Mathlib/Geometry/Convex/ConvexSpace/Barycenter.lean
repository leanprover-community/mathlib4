/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.AffineMap

import Mathlib.Tactic.FinCases

/-!
# The barycenter of the standard simplex and the barycentric subdivision

We define `StdSimplex.barycenter` as the barycenter of the standard simplex
`StdSimplex K M` when `M` is a non empty finite type. More generally,
if `S : Finset M` is a non empty finite subset of `M`, we define the
barycenter of the vertices corresponding to the elements in `S` as
`StdSimplex.subBarycenter`.

We introduce similar definitions for a convex map
`f : ConvexSpace.AffineMap K (StdSimplex K M) Y` from the standard simplex,
as the image by `f` of the barycenter of `StdSimplex K M` (resp. the barycenter
of a non empty finite subset of `M`).

We define a "subdivision" of `f : ConvexSpace.AffineMap K (StdSimplex K (Fin n)) Y`:
for each `σ : Equiv.Perm (Fin n)`, we define `f.sd σ` (in the same type) as the
affine map with sends the `i`th vertex of `StdSimplex K (Fin n)` to `f.sdVertex σ i`
which is the image by `f` of the barycenter of the vertices in `{ x : Fin n | i ≤ σ⁻¹ x}`.
(See `Mathlib/Geometry/Convex/ConvexSpace/Subdivision.lean` for the definition of
the subdivision operator on affine singular chains of `Y`.)

-/

@[expose] public section

namespace Convexity

namespace StdSimplex

variable {K M : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- In the standard simplex with vertices `M`, this is the barycenter of
a nonempty finite subset `S` of `M`. -/
@[simps -isSimp weights]
noncomputable def subBarycenter (S : Finset M) (hS : S.Nonempty) : StdSimplex K M where
  weights := S.sum (fun m ↦ .single m S.card⁻¹)
  nonneg := Finset.sum_nonneg (by simp)
  total := by
    rw [← Finsupp.sum_finsetSum_index (by simp) (by simp)]
    simpa using IsUnit.mul_inv_cancel (Ne.isUnit (by simpa [← Finset.nonempty_iff_ne_empty]))

lemma weights_subBarycenter_apply_eq (S : Finset M) (m : M) (hm : m ∈ S) :
    (subBarycenter (K := K) S (by grind)).weights m = (S.card⁻¹ : K) := by
  rw [weights_subBarycenter, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finset.sum_eq_single m (fun a ha ha' ↦ Finsupp.single_eq_of_ne ha'.symm) (by tauto),
    Finsupp.single_eq_same]

lemma weights_subBarycenter_apply_eq_zero
    (S : Finset M) (hS : S.Nonempty) (m : M) (hm : m ∉ S) :
    (subBarycenter (K := K) S hS).weights m = 0 := by
  simp only [weights_subBarycenter, Finsupp.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_zero]
  intro x hx
  rw [Finsupp.single_apply_eq_zero]
  rintro rfl
  exact (hm hx).elim

@[deprecated (since := "2026-11-13")] alias subBarycenter_weights_apply_eq_zero :=
  weights_subBarycenter_apply_eq_zero

@[simp]
lemma subBarycenter_singleton (m : M) :
    subBarycenter (K := K) {m} (by simp) = .single m := by
  ext
  simp [weights_subBarycenter]

/-- The barycenter of the standard simplex. -/
noncomputable abbrev barycenter [Nonempty M] [Fintype M] : StdSimplex K M :=
  subBarycenter .univ (by simp)

lemma weights_barycenter_apply [Nonempty M] [Fintype M] (m : M) :
    (barycenter (K := K) (M := M)).weights m = (Fintype.card M : K)⁻¹ := by
  simp [barycenter, weights_subBarycenter]

lemma barycenter_of_unique [Unique M] :
    barycenter (K := K) (M := M) = .single default := by
  subsingleton

@[simp]
lemma barycenter_fin_one :
    barycenter (K := K) (M := Fin 1) = .single 0 :=
  barycenter_of_unique

lemma map_subBarycenter_of_injective
    {M N : Type*} [DecidableEq N] (S : Finset M) (hS : S.Nonempty)
    (f : M → N) (hf : Function.Injective f) :
    map f (subBarycenter (K := K) S hS) = subBarycenter (Finset.image f S) (by simpa) := by
  ext n
  rw [weights_map]
  by_cases hn : n ∈ Set.range f
  · obtain ⟨m, rfl⟩ := hn
    rw [Finsupp.mapDomain_apply_of_injective hf]
    by_cases hm : m ∈ S
    · rw [weights_subBarycenter_apply_eq _ _ hm,
        weights_subBarycenter_apply_eq _ _ (by grind),
        Finset.card_image_of_injective S hf]
    · rw [weights_subBarycenter_apply_eq_zero _ _ _ (by grind),
        weights_subBarycenter_apply_eq_zero _ _ _ (by grind)]
  · rw [weights_subBarycenter_apply_eq_zero _ (by simpa) _ (by grind),
      Finsupp.mapDomain_of_notMem_range _ _ hn]

end StdSimplex

namespace ConvexSpace.AffineMap

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {Y : Type*} [ConvexSpace K Y]

section

variable {M : Type*} (f : ConvexSpace.AffineMap K (StdSimplex K M) Y)

/-- Given an affine map from the standard simplex with vertices `M` and
a nonempty finite subset `S` of `M`, this is the image of the isobarycenter
of the face of the standard simplex corresponding to `S`. -/
noncomputable def subBarycenter (S : Finset M) (hS : S.Nonempty) : Y :=
  f (.subBarycenter S hS)

@[simp]
lemma subBarycenter_single (m : M) :
    f.subBarycenter {m} (by simp) = f (.single m) := by
  simp [subBarycenter]

lemma subBarycenter_comp_of_injective
    [DecidableEq M] {N : Type*} (S : Finset N) (hS : S.Nonempty)
    (g : N → M) (hg : Function.Injective g) :
    (f.comp (StdSimplex.affineMap (R := K) g)).subBarycenter S hS =
      f.subBarycenter (Finset.image g S) (by simpa) := by
  simp [subBarycenter, StdSimplex.map_subBarycenter_of_injective _ _ _ hg]

/-- The image of the isobarycenter of the standard simplex by an affine map. -/
noncomputable abbrev barycenter [Nonempty M] [Fintype M] : Y := f .barycenter

end

lemma subBarycenter_mk_comp_of_injective {M N : Type*} [DecidableEq N]
    (f : N → Y) (S : Finset M) (hS : S.Nonempty) (g : M → N)
    (hg : Function.Injective g) :
    (StdSimplex.affineMapMk (R := K) (f ∘ g)).subBarycenter S hS =
      (StdSimplex.affineMapMk (R := K) f).subBarycenter (Finset.image g S)
        (by simpa) := by
  rw [← subBarycenter_comp_of_injective _ _ hS _ hg]
  congr
  aesop

section

variable {n : ℕ}

/-- Given an affine map `f` from the standard simplex of dimension `n - 1`,
a permutation `σ` of `Fin n` and `i : Fin n`, this is the image by `f`
of the isobarycenter of the face of the standard simplex corresponding
to `{ x : Fin n | i ≤ σ⁻¹ x}` (i.e. `{σ i, σ (i + 1), ..., σ (n - 1)}`). -/
noncomputable def sdVertex
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin n)) Y)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) : Y :=
  f.subBarycenter { x : Fin n | i ≤ σ⁻¹ x} ⟨σ i, by simp⟩

lemma sdVertex_def (f : ConvexSpace.AffineMap K (StdSimplex K (Fin n)) Y)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    f.sdVertex σ i = f.subBarycenter { x : Fin n | i ≤ σ⁻¹ x } ⟨σ i, by simp⟩ :=
  rfl

@[simp]
lemma sdVertex_zero
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin (n + 1))) Y)
    (σ : Equiv.Perm (Fin (n + 1))) :
    f.sdVertex σ 0 = f.barycenter := by
  simp [sdVertex_def, subBarycenter]

@[simp]
lemma sdVertex_last
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin (n + 1))) Y)
    (σ : Equiv.Perm (Fin (n + 1))) :
    f.sdVertex σ (Fin.last n) = f (.single (σ (Fin.last n))) := by
  have : ({ x | σ.symm x = Fin.last n } : Finset _) = {σ (Fin.last n)} := by
    ext
    simp [Equiv.symm_apply_eq]
  simp [sdVertex_def, this]

@[simp]
lemma sdVertex_mk_one (y : Y) (σ : Equiv.Perm (Fin 1)) :
    (StdSimplex.affineMapMk (R := K) ![y]).sdVertex σ = ![y] := by
  ext
  simp [sdVertex_def]

/-- Given an affine map `f` from the standard simplex of dimension `n` to `Y` and
a permutation `σ` of `Fin n`, this is the subdivision of `f` corresponding to `σ`:
this is again an affine map from the standard simplex of dimension `n`, and the
images of the vertices are given by `f.sdVertex σ : Fin n → Y` -/
noncomputable abbrev sd
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin n)) Y) (σ : Equiv.Perm (Fin n)) :
    ConvexSpace.AffineMap K (StdSimplex K (Fin n)) Y :=
  StdSimplex.affineMapMk (f.sdVertex σ)

@[simp]
lemma sd_eq_self
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin 1)) Y) (σ : Equiv.Perm (Fin 1)) :
    f.sd σ = f := by
  obtain ⟨f, rfl⟩ := StdSimplex.affineMapMk_surjective f
  obtain ⟨s, rfl⟩ : ∃ (s : Y), f = ![s] := ⟨f 0, by ext i; fin_cases i; simp⟩
  simp [sd]

end

end ConvexSpace.AffineMap

end Convexity
