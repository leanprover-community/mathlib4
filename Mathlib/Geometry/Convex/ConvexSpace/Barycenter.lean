/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.AffineMap

/-!
# The barycenter of the standard simplex

We define `StdSimplex.barycenter` as the barycenter of the standard simplex
`StdSimplex K M` when `M` is a non empty finite type. More generaly,
if `S : Finset M` is a non empty finite subset of `M`, we define the
barycenter of the vertex corresponding to the elements in `S` as
`StdSimplex.subBarycenter`.

We introduce similar definitions for a convex map
`f : ConvexSpace.AffineMap K (StdSimplex K M) Y` from the standard simplex,
as the image by `f` of the barycenter of `StdSimplex K M` (resp. the barycenter
of a non empty finite subset of `M`).

For each `σ : Equiv.Perm (Fin n)` and `f : ConvexSpace.AffineMap K (StdSimplex K (Fin n)) Y`,
we define `f.sd σ` (in the same type) as the affine map with sends the `i`th
vertex of `StdSimplex K (Fin n)` to `f.sdVertex σ i` which is the image by `f`
of the barycenter of the vertices in `{ x : Fin n | i ≤ σ⁻¹ x}`.

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

lemma subBarycenter_weights_apply_eq_zero
    (S : Finset M) (hS : S.Nonempty) (m : M) (hm : m ∉ S) :
    (subBarycenter (K := K) S hS).weights m = 0 := by
  simp only [weights_subBarycenter, Finsupp.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_zero]
  intro x hx
  rw [Finsupp.single_apply_eq_zero]
  rintro rfl
  exact (hm hx).elim

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
  sorry--simp [subBarycenter, StdSimplex.map_subBarycenter_of_injective _ _ _ hg]

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
  sorry
  --obtain ⟨s, rfl⟩ := Fin.exists_vecCons₁ f
  --simp [sd]

end

end ConvexSpace.AffineMap

end Convexity
