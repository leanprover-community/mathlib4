/-
Copyright (c) 2025 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Rank decomposition and bases adapted to a linear map

This file develops a small API around a linear map `f : V →ₗ[K] W` that chooses a complement
of `ker f`, builds bases compatible with the direct-sum decomposition
`V = ker f ⊕ C f`, and produces a rank-normal form for the matrix of `f`:
after choosing suitable bases on domain and codomain, the matrix of `f` is a block matrix
`fromBlocks 1 0 0 0` (an identity of size `rank f` in the top-left block and zeros elsewhere).

## Main definitions

* `LinearMap.prodEquivOfC` :
  a linear equivalence `(C f × ker f) ≃ₗ[K] V`
  induced by the complementary decomposition.

* `LinearMap.decomposition_basis` :
  a basis of `V` obtained by transporting the product of the canonical bases on
  `C f` and `ker f` along `prodEquivOfC`.

* `LinearMap.ker_complement_restriction` :
  the restriction of `f` to `C f` (include, then apply `f`).

* `LinearMap.ker_complement_basis_image` :
  the image in `W` of the canonical basis of `C f` under the restriction map.

* `LinearMap.range_decomposition_basis` :
  a basis of `W` built by extending the previous image (which spans `range f`)
  via `Basis.sumExtend`.

* `LinearMap.CEquivRange` :
  a linear equivalence `C f ≃ₗ[K] range f`.

## Main results

* `LinearMap.exists_basis_for_normal_form_abstract` :
  there exist bases `v₁` of `V` and `v₂` of `W` such that `toMatrix v₁ v₂ f = fromBlocks 1 0 0 0`.

* `LinearMap.exists_basis_for_normal_form` :
  in the finite-dimensional case, after reindexing by `Fin r ⊕ Fin (n - r)` and
  `Fin r ⊕ Fin (m - r)` (with `r = rank f`, `n = finrank K V`, `m = finrank K W`),
  one gets the same block form `fromBlocks 1 0 0 0`.

-/

open Submodule Module Basis

noncomputable section

variable {K : Type*} [DivisionRing K] {V W : Type*}
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W] (f : V →ₗ[K] W)

namespace LinearMap

variable {C : Submodule K V} (h : IsCompl C (ker f))

/-- `C × (ker f)` is isomorphic to the whole space -/
def prodEquivOfC : (C × (ker f)) ≃ₗ[K] V :=
  prodEquivOfIsCompl _ _ h

lemma apply_ker_component_eq_zero (y : V) : f ((f.prodEquivOfC h).symm y).1 = f y := by
  nth_rw 2 [← Submodule.IsCompl.projection_add_projection_eq_self h y]
  rw [map_add, h.symm.projection_apply_mem y, add_zero]
  rfl

/-- When `V` decomposes as `ker f ⊕ C f`, the basis is obtained by transporting the
product of bases on the kernel and on its complement along `f.prodEquivOfC`. -/
def decomposition_basis : Basis ((ofVectorSpaceIndex K C) ⊕
    (ofVectorSpaceIndex K (ker f))) K V :=
  .map (.prod (ofVectorSpace K _) (ofVectorSpace K _)) (f.prodEquivOfC h)

/-- The restriction of `f` to the kernel complement -/
def ker_complement_restriction (C : Submodule K V) : C →ₗ[K] W :=
  f.comp C.subtype

lemma ker_complement_restriction_ker_eq_bot (h : IsCompl C (ker f)) :
    ker (f.ker_complement_restriction C) = ⊥ := by
  simpa [ker_complement_restriction, ker_comp, ← disjoint_iff_comap_eq_bot] using h.disjoint

lemma ker_complement_restriction_injective (h : IsCompl C (ker f)) :
    Function.Injective (f.ker_complement_restriction C) := by
  simpa [← ker_eq_bot] using (ker_complement_restriction_ker_eq_bot f h)

/-- Given the basis of `C f` and the restriction map
`f ∘ Submodule.subtype (C f)`, define the function that sends the
basis indices to vectors of `W`. -/
def ker_complement_basis_image (C : Submodule K V) :
    ofVectorSpaceIndex K C → W :=
  (f.ker_complement_restriction C) ∘ (ofVectorSpace K C)

lemma linear_independent_ker_complement_basis_image (h : IsCompl C (ker f)) :
    LinearIndependent K (f.ker_complement_basis_image C) :=
  (ofVectorSpace K C).linearIndependent.map' _
    (f.ker_complement_restriction_ker_eq_bot h)

/-- A basis of `W` obtained by extending the image of the `C f` basis (which corresponds
to `range f`) to a full basis via `Basis.sumExtend`. -/
def range_decomposition_basis (h : IsCompl C (ker f)) :
    Basis ((ofVectorSpaceIndex K C) ⊕
    (sumExtendIndex (f.linear_independent_ker_complement_basis_image h))) K W :=
  Basis.sumExtend (f.linear_independent_ker_complement_basis_image h)

/-- `f.C` is isomorphic to `range f` -/
def CEquivRange : C ≃ₗ[K] (range f) := by
  let g : C →ₗ[K] range f :=
    codRestrict (range f) (f.ker_complement_restriction C)
    (fun x ↦ ⟨C.subtype x, rfl⟩)
  apply LinearEquiv.ofBijective g
  constructor
  · simpa [← ker_eq_bot, g, ker_codRestrict] using (f.ker_complement_restriction_injective h)
  intro ⟨_, y, hyx⟩
  use ((f.prodEquivOfC h).2 y).1
  simp [g, codRestrict, ← hyx, ker_complement_restriction, apply_ker_component_eq_zero]

lemma finrank_C_eq_rank {r : ℕ} (hr : rank f = r) (h : IsCompl C (ker f)) : finrank K C = r := by
  simp [finrank_eq_of_rank_eq hr, LinearEquiv.finrank_eq (f.CEquivRange h)]

lemma finrank_ker_eq [FiniteDimensional K V] {r n : ℕ} (hr : rank f = r) (hn : finrank K V = n) :
    finrank K (ker f) = n - r := by
  rw [← hn, ← finrank_range_add_finrank_ker f, ← finrank_eq_of_rank_eq hr, add_tsub_cancel_left]

instance : DecidableEq (ofVectorSpaceIndex K C) := Classical.typeDecidableEq _

lemma apply_C_basis_eq_range_basis (j) :
    f (f.decomposition_basis h (Sum.inl j)) = (f.range_decomposition_basis h (Sum.inl j)) := by
  simp [decomposition_basis, prodEquivOfC, range_decomposition_basis, sumExtend,
    Equiv.sumCongr, ker_complement_basis_image, ker_complement_restriction]

end LinearMap

end



noncomputable section

variable {R : Type} [Field R] {m n r : ℕ} {M₁ M₂ : Type*}
variable [AddCommGroup M₁] [Module R M₁] [FiniteDimensional R M₁]
variable [AddCommGroup M₂] [Module R M₂] [FiniteDimensional R M₂] (f : M₁ →ₗ[R] M₂)
variable {C : Submodule R M₁} (h : IsCompl C (LinearMap.ker f))
open Matrix LinearMap


theorem exists_basis_for_normal_form_abstract :

  haveI : Finite ((ofVectorSpaceIndex R C) ⊕
      (sumExtendIndex (f.linear_independent_ker_complement_basis_image h))) :=
    Fintype.finite (FiniteDimensional.fintypeBasisIndex (f.range_decomposition_basis h))

  ∃ (v₁ : Basis ((ofVectorSpaceIndex R C) ⊕ (ofVectorSpaceIndex R (ker f))) R M₁)
    (v₂ : Basis ((ofVectorSpaceIndex R C) ⊕
      (sumExtendIndex (f.linear_independent_ker_complement_basis_image h))) R M₂),
    LinearMap.toMatrix v₁ v₂ f = fromBlocks 1 0 0 0 := by
  use (f.decomposition_basis h), (f.range_decomposition_basis h)
  funext i j
  match i, j with
  | Sum.inl i', Sum.inl j' =>
    simp [toMatrix_apply, f.apply_C_basis_eq_range_basis h j',
      Finsupp.single, Pi.single, Function.update, Matrix.one_apply]
  | Sum.inr i', Sum.inr j' => simp [toMatrix_apply, decomposition_basis, prodEquivOfC]
  | Sum.inl i', Sum.inr j' => simp [toMatrix_apply, decomposition_basis, prodEquivOfC]
  | Sum.inr i', Sum.inl j' => simp [toMatrix_apply, f.apply_C_basis_eq_range_basis h j']

end
