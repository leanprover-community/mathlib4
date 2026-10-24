/-
Copyright (c) 2026 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Bi-alternating maps

This file defines `LinearMap.BilinMap.toAlternatingMap`.
-/

public section

namespace LinearMap

variable {R S A M N Pairwise ι : Type*}
variable [CommSemiring R] [CommSemiring S] [CommRing A]
variable [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N] [Algebra R A] [Algebra S A]
variable [SMulCommClass S R A] [Fintype ι] [DecidableEq ι]

namespace BilinMap

/-- For fixed `u`, the `S`-alternating map `v ↦ det (B (u i) (v j))`. -/
def toAlternatingMapAux (B : M →ₗ[R] N →ₗ[S] A) (u : ι → M) : N [⋀^ι]→ₗ[S] A :=
  MultilinearMap.alternatization
    ((MultilinearMap.mkPiAlgebra S ι A).compLinearMap fun i ↦ B (u i))

open Equiv in
theorem toAlternatingMapAux_apply (B : M →ₗ[R] N →ₗ[S] A) (u : ι → M) (v : ι → N) :
    toAlternatingMapAux B u v = (Matrix.of fun i j ↦ B (u i) (v j)).det := by
  trans ∑ σ : Perm ι, Perm.sign σ • ∏ i, B (u i) (v (σ i))
  · simp only [toAlternatingMapAux, MultilinearMap.alternatization_apply,
      MultilinearMap.domDomCongr_apply, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply]
  · rw [← Matrix.det_transpose, Matrix.det_apply]
    rfl

/-- The pairing `u, v ↦ det (B (u i) (v j))`, alternating in both arguments. -/
def toAlternatingMap (B : M →ₗ[R] N →ₗ[S] A) : M [⋀^ι]→ₗ[R] (N [⋀^ι]→ₗ[S] A) where
  toMultilinearMap := .mk' (toAlternatingMapAux B)
    (fun u i x y ↦ by
      ext v
      simp only [toAlternatingMapAux_apply, AlternatingMap.add_apply]
      convert! Matrix.det_updateRow_add
        (.of fun i j => B (u i) (v j)) i (fun j => B x (v j)) (fun j => B y (v j))
      all_goals
        ext
        simp [Matrix.updateRow_apply, Function.update_apply];
        split <;> simp)
    (fun u i c x ↦ by
      ext v
      simp only [toAlternatingMapAux_apply, AlternatingMap.smul_apply]
      convert! Matrix.det_updateRow_smul
        (.of fun i j => B (u i) (v j)) i (c • 1) (fun j => B x (v j))
      all_goals
        ext
        simp [Matrix.updateRow_apply, Function.update_apply] <;> split <;> simp)
  map_eq_zero_of_eq' u i j h hij := by
    change toAlternatingMapAux B u = 0
    ext v
    rw [AlternatingMap.zero_apply, toAlternatingMapAux_apply]
    exact Matrix.det_zero_of_row_eq hij (by ext k; simp [h])

end BilinMap

-- for dot notation
export BilinMap (toAlternatingMap)

namespace BilinMap

@[simp]
theorem toAlternatingMap_apply (B : M →ₗ[R] N →ₗ[S] A) (u : ι → M) (v : ι → N) :
    B.toAlternatingMap u v = (Matrix.of fun i j ↦ B (u i) (v j)).det :=
  toAlternatingMapAux_apply B u v

/-- Naturality in the first argument: pulling back along `f : P → M`. -/
theorem toAlternatingMap_comp {P : Type*} [AddCommMonoid P] [Module R P]
    (B : M →ₗ[R] N →ₗ[S] A) (f : P →ₗ[R] M) :
    (B ∘ₗ f).toAlternatingMap (ι := ι) = B.toAlternatingMap.compLinearMap f := by
  ext u v
  rfl

/-- Naturality in the second argument: pulling back along `g : Q → N`. -/
theorem toAlternatingMap_compl₂ {Q : Type*} [AddCommMonoid Q] [Module S Q]
    (B : M →ₗ[R] N →ₗ[S] A) (g : Q →ₗ[S] N) (u : ι → M) :
    (B.compl₂ g).toAlternatingMap u = (B.toAlternatingMap u).compLinearMap g := by
  change toAlternatingMapAux (B.compl₂ g) u = (toAlternatingMapAux B u).compLinearMap g
  change MultilinearMap.alternatization
      ((MultilinearMap.mkPiAlgebra S ι A).compLinearMap fun i ↦ B (u i) ∘ₗ g) = _
  ext v
  simp [toAlternatingMapAux, MultilinearMap.alternatization]

end BilinMap

end LinearMap
