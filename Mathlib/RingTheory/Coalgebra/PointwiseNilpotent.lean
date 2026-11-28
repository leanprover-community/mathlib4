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
# Pointwise nilpotent elements of the convolution algebra

Let `C` be a coalgebra and `A` an algebra. A linear map `f : C →ₗ[R] A` is pointwise nilpotent
for the convolution product if for each `x` only finitely many of the convolution powers
`(f ^ k) x` are nonzero. Then `1 - f` is invertible in the convolution algebra, with inverse the
geometric series `∑ k, f ^ k`.

## References

* [Grinberg, D. and Reiner, V., *Hopf Algebras in Combinatorics*][GrinbergReiner2020],
  Definition 1.7.10 (pointwise `⋆`-nilpotent maps).
-/

public section

open Coalgebra WithConv

namespace LinearMap

variable {R C A : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [Ring A] [Algebra R A] {f : WithConv (C →ₗ[R] A)}

/-- A linear map `f` from a coalgebra to an algebra is pointwise nilpotent for the convolution
product if for each `x` only finitely many of the convolution powers `(f ^ k) x` are nonzero. -/
@[expose] def IsPointwiseConvNilpotent (f : WithConv (C →ₗ[R] A)) : Prop :=
  ∀ x, Function.HasFiniteSupport fun k ↦ (f ^ k) x

theorem isPointwiseConvNilpotent_iff :
    IsPointwiseConvNilpotent f ↔ ∀ x, ∃ N, ∀ k, N ≤ k → (f ^ k) x = 0 := by
  refine forall_congr' fun x ↦ ⟨fun h ↦ ?_, fun ⟨N, hN⟩ ↦
    (Set.finite_lt_nat N).subset fun k hk ↦ not_le.1 fun h ↦ hk (hN k h)⟩
  obtain ⟨N, hN⟩ := h.bddAbove
  exact ⟨N + 1, fun k hk ↦ by_contra fun hk' ↦ by have := hN hk'; omega⟩

namespace IsPointwiseConvNilpotent

variable (hf : IsPointwiseConvNilpotent f)

/-- The geometric series `∑ k, f ^ k` in the convolution algebra, for `f` pointwise nilpotent. -/
noncomputable def geomSeries : WithConv (C →ₗ[R] A) :=
  toConv
    { toFun x := ∑ᶠ k, (f ^ k) x
      map_add' x y := by simp only [map_add, finsum_add_distrib (hf x) (hf y)]
      map_smul' r x := by simp only [map_smul, RingHom.id_apply, smul_finsum' r (hf x)] }

theorem geomSeries_apply_of_le {x : C} {N : ℕ} (hN : ∀ k, N ≤ k → (f ^ k) x = 0) :
    hf.geomSeries x = (∑ k ∈ Finset.range N, f ^ k) x := by
  have : (Function.support fun k ↦ (f ^ k) x) ⊆ Finset.range N := fun k hk ↦ by
    simpa using fun h ↦ hk (hN k h)
  simpa [geomSeries] using finsum_eq_sum_of_support_subset _ this

theorem geomSeries_mul_one_sub : hf.geomSeries * (1 - f) = 1 := by
  ext x
  choose N hN using isPointwiseConvNilpotent_iff.1 hf
  let 𝓡 := ℛ R x
  let M := (𝓡.index.sup fun i ↦ N (𝓡.left i)) ⊔ N x
  have key : ∀ i ∈ 𝓡.index,
      hf.geomSeries (𝓡.left i) = (∑ k ∈ Finset.range M, f ^ k) (𝓡.left i) := fun i hi ↦
    hf.geomSeries_apply_of_le fun k hk ↦
      hN _ k ((Finset.le_sup (f := fun i ↦ N (𝓡.left i)) hi).trans (le_sup_left.trans hk))
  rw [𝓡.convMul_apply, Finset.sum_congr rfl fun i hi ↦ by rw [key i hi], ← 𝓡.convMul_apply,
    geom_sum_mul_neg]
  simp [hN x M le_sup_right]

theorem one_sub_mul_geomSeries : (1 - f) * hf.geomSeries = 1 := by
  ext x
  choose N hN using isPointwiseConvNilpotent_iff.1 hf
  let 𝓡 := ℛ R x
  let M := (𝓡.index.sup fun i ↦ N (𝓡.right i)) ⊔ N x
  have key : ∀ i ∈ 𝓡.index,
      hf.geomSeries (𝓡.right i) = (∑ k ∈ Finset.range M, f ^ k) (𝓡.right i) := fun i hi ↦
    hf.geomSeries_apply_of_le fun k hk ↦
      hN _ k ((Finset.le_sup (f := fun i ↦ N (𝓡.right i)) hi).trans (le_sup_left.trans hk))
  rw [𝓡.convMul_apply, Finset.sum_congr rfl fun i hi ↦ by rw [key i hi], ← 𝓡.convMul_apply,
    mul_neg_geom_sum]
  simp [hN x M le_sup_right]

include hf in
theorem isUnit_one_sub : IsUnit (1 - f) :=
  ⟨⟨1 - f, hf.geomSeries, hf.one_sub_mul_geomSeries, hf.geomSeries_mul_one_sub⟩, rfl⟩

end IsPointwiseConvNilpotent

end LinearMap
