/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs

/-!
# The barycenter of the standard simplex

-/

@[expose] public section

namespace Convexity.StdSimplex

variable {K M : Type*} [Field K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K]

/-- In the standard simplex with vertices `M`, this is the barycenter of
a nonempty finite subset `S` of `M`. -/
@[simps -isSimp]
noncomputable def subBarycenter
     (S : Finset M) (hS : S.Nonempty) : StdSimplex K M where
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

end Convexity.StdSimplex
