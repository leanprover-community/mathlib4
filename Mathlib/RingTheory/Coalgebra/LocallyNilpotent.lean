/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.RingTheory.Coalgebra.Convolution

import Mathlib.Algebra.Ring.GeomSum

/-!
# Locally nilpotent elements of the convolution algebra

Let `C` be a coalgebra and `A` an algebra. If `f : C →ₗ[R] A` is locally nilpotent for the
convolution product, meaning that for each `x` the convolution powers `(f ^ k) x` eventually
vanish, then `1 - f` is invertible in the convolution algebra, with inverse the geometric series
`∑ k, f ^ k`.
-/

public section

open Coalgebra WithConv Finset

namespace LinearMap

variable {R C A : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [Ring A] [Algebra R A] {f : WithConv (C →ₗ[R] A)}
  (hf : ∀ x, ∃ N, ∀ k, N ≤ k → (f ^ k) x = 0)

include hf in
private lemma hasFiniteSupport_convPow_apply (x : C) :
    Function.HasFiniteSupport fun k ↦ (f ^ k) x := by
  obtain ⟨N, hN⟩ := hf x
  exact (finite_toSet (Finset.range N)).subset fun k hk ↦ by
    simpa using fun h ↦ hk (hN k h)

/-- The geometric series `∑ k, f ^ k` in the convolution algebra, for `f` locally nilpotent. -/
noncomputable def convGeomSeries (f : WithConv (C →ₗ[R] A))
    (hf : ∀ x, ∃ N, ∀ k, N ≤ k → (f ^ k) x = 0) : WithConv (C →ₗ[R] A) :=
  toConv
    { toFun x := ∑ᶠ k, (f ^ k) x
      map_add' x y := by
        simp only [map_add]
        exact finsum_add_distrib (hasFiniteSupport_convPow_apply hf x)
          (hasFiniteSupport_convPow_apply hf y)
      map_smul' r x := by
        simp only [map_smul, RingHom.id_apply]
        exact (smul_finsum' r (hasFiniteSupport_convPow_apply hf x)).symm }

variable {hf}

theorem convGeomSeries_apply_of_le {x : C} {N : ℕ} (hN : ∀ k, N ≤ k → (f ^ k) x = 0) :
    convGeomSeries f hf x = (∑ k ∈ Finset.range N, f ^ k) x := by
  have : (Function.support fun k ↦ (f ^ k) x) ⊆ Finset.range N := fun k hk ↦ by
    simpa using fun h ↦ hk (hN k h)
  simpa [convGeomSeries] using finsum_eq_sum_of_support_subset _ this

variable (hf)

theorem convGeomSeries_mul_one_sub : convGeomSeries f hf * (1 - f) = 1 := by
  ext x
  let N (y : C) : ℕ := (hf y).choose
  have hN (y : C) : ∀ k, N y ≤ k → (f ^ k) y = 0 := (hf y).choose_spec
  let 𝓡 := ℛ R x
  let M := (𝓡.index.sup fun i ↦ N (𝓡.left i)) ⊔ N x
  have key : ∀ i ∈ 𝓡.index,
      convGeomSeries f hf (𝓡.left i) = (∑ k ∈ Finset.range M, f ^ k) (𝓡.left i) := fun i hi ↦
    convGeomSeries_apply_of_le fun k hk ↦
      hN _ k ((Finset.le_sup (f := fun i ↦ N (𝓡.left i)) hi).trans (le_sup_left.trans hk))
  rw [𝓡.convMul_apply, Finset.sum_congr rfl fun i hi ↦ by rw [key i hi], ← 𝓡.convMul_apply,
    geom_sum_mul_neg]
  simp [hN x M le_sup_right]

theorem one_sub_mul_convGeomSeries : (1 - f) * convGeomSeries f hf = 1 := by
  ext x
  let N (y : C) : ℕ := (hf y).choose
  have hN (y : C) : ∀ k, N y ≤ k → (f ^ k) y = 0 := (hf y).choose_spec
  let 𝓡 := ℛ R x
  let M := (𝓡.index.sup fun i ↦ N (𝓡.right i)) ⊔ N x
  have key : ∀ i ∈ 𝓡.index,
      convGeomSeries f hf (𝓡.right i) = (∑ k ∈ Finset.range M, f ^ k) (𝓡.right i) := fun i hi ↦
    convGeomSeries_apply_of_le fun k hk ↦
      hN _ k ((Finset.le_sup (f := fun i ↦ N (𝓡.right i)) hi).trans (le_sup_left.trans hk))
  rw [𝓡.convMul_apply, Finset.sum_congr rfl fun i hi ↦ by rw [key i hi], ← 𝓡.convMul_apply,
    mul_neg_geom_sum]
  simp [hN x M le_sup_right]

include hf in
theorem isUnit_one_sub_of_forall_exists_convPow_apply_eq_zero : IsUnit (1 - f) :=
  ⟨⟨1 - f, convGeomSeries f hf, one_sub_mul_convGeomSeries hf, convGeomSeries_mul_one_sub hf⟩, rfl⟩

end LinearMap
