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
`V = ker f ⊕ kerComplement f`, and produces a rank-normal form for the matrix of `f`:
after choosing suitable bases on domain and codomain, the matrix of `f` is a block matrix
`fromBlocks 1 0 0 0` (an identity of size `rank f` in the top-left block and zeros elsewhere).

## Main definitions

* `LinearMap.kerComplement` :
  a fixed choice of a subspace complementary to `ker f`.

* `LinearMap.prodEquivOfkerComplement` :
  a linear equivalence `(kerComplement f × ker f) ≃ₗ[K] V`
  induced by the complementary decomposition.

* `LinearMap.decomposition_basis` :
  a basis of `V` obtained by transporting the product of the canonical bases on
  `kerComplement f` and `ker f` along `prodEquivOfkerComplement`.

* `LinearMap.ker_complement_restriction` :
  the restriction of `f` to `kerComplement f` (include, then apply `f`).

* `LinearMap.ker_complement_basis_image` :
  the image in `W` of the canonical basis of `kerComplement f` under the restriction map.

* `LinearMap.range_decomposition_basis` :
  a basis of `W` built by extending the previous image (which spans `range f`)
  via `Basis.sumExtend`.

* `LinearMap.kerComplementEquivRange` :
  a linear equivalence `kerComplement f ≃ₗ[K] range f`.

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

/-- A subspace complementary to the `ker f` -/
def kerComplement : Submodule K V :=
  (ker f).exists_isCompl.choose

lemma isCompl_ker_kerComplement : IsCompl f.kerComplement (ker f) :=
  (ker f).exists_isCompl.choose_spec.symm

/-- `f.kerComplement × (ker f)` is isomorphic to the whole space -/
def prodEquivOfkerComplement : (f.kerComplement × (ker f)) ≃ₗ[K] V :=
  prodEquivOfIsCompl _ _ f.isCompl_ker_kerComplement

lemma apply_ker_component_eq_zero (y : V) : f (f.prodEquivOfkerComplement.symm y).1 = f y := by
  nth_rw 2 [← Submodule.IsCompl.projection_add_projection_eq_self f.isCompl_ker_kerComplement y]
  rw [map_add, f.isCompl_ker_kerComplement.symm.projection_apply_mem y, add_zero]
  rfl

/-- When `V` decomposes as `ker f ⊕ kerComplement f`, the basis is obtained by transporting the
product of bases on the kernel and on its complement along `f.prodEquivOfkerComplement`. -/
def decomposition_basis : Basis ((ofVectorSpaceIndex K f.kerComplement) ⊕
    (ofVectorSpaceIndex K (ker f))) K V :=
  .map (.prod (ofVectorSpace K _) (ofVectorSpace K _)) (f.prodEquivOfkerComplement)

/-- The restriction of `f` to the kernel complement -/
def ker_complement_restriction : f.kerComplement →ₗ[K] W :=
  f.comp f.kerComplement.subtype

lemma ker_complement_restriction_ker_eq_bot : ker f.ker_complement_restriction = ⊥ := by
  simpa [ker_complement_restriction, ker_comp, ← disjoint_iff_comap_eq_bot]
    using f.isCompl_ker_kerComplement.disjoint

lemma ker_complement_restriction_injective : Function.Injective f.ker_complement_restriction := by
  simpa [← ker_eq_bot] using (ker_complement_restriction_ker_eq_bot f)

/-- Given the basis of `kerComplement f` and the restriction map
`f ∘ Submodule.subtype (kerComplement f)`, define the function that sends the
basis indices to vectors of `W`. -/
def ker_complement_basis_image : ofVectorSpaceIndex K f.kerComplement → W :=
  f.ker_complement_restriction ∘ (ofVectorSpace K f.kerComplement)

lemma linear_independent_ker_complement_basis_image :
    LinearIndependent K f.ker_complement_basis_image :=
  (ofVectorSpace K f.kerComplement).linearIndependent.map' _ f.ker_complement_restriction_ker_eq_bot

/-- A basis of `W` obtained by extending the image of the `kerComplement f` basis (which corresponds
to `range f`) to a full basis via `Basis.sumExtend`. -/
def range_decomposition_basis : Basis ((ofVectorSpaceIndex K f.kerComplement) ⊕
      (sumExtendIndex f.linear_independent_ker_complement_basis_image)) K W :=
  Basis.sumExtend f.linear_independent_ker_complement_basis_image

instance [FiniteDimensional K W] :
    Fintype (sumExtendIndex f.linear_independent_ker_complement_basis_image) :=
  @Fintype.sumRight _ _ (FiniteDimensional.fintypeBasisIndex f.range_decomposition_basis)

instance : DecidableEq (ofVectorSpaceIndex K f.kerComplement) := Classical.typeDecidableEq _

instance : DecidableEq (ofVectorSpaceIndex K (ker f)) := Classical.typeDecidableEq _

/-- `f.kerComplement` is isomorphic to `range f` -/
def kerComplementEquivRange : f.kerComplement ≃ₗ[K] (range f) := by
  let g : f.kerComplement →ₗ[K] range f :=
    codRestrict (range f) f.ker_complement_restriction (fun x ↦ ⟨f.kerComplement.subtype x, rfl⟩)
  apply LinearEquiv.ofBijective g
  constructor
  · simpa [← ker_eq_bot, g, ker_codRestrict] using f.ker_complement_restriction_injective
  intro ⟨_, y, hyx⟩
  use (f.prodEquivOfkerComplement.2 y).1
  simp [g, codRestrict, ← hyx, ker_complement_restriction, apply_ker_component_eq_zero]

lemma finrank_kerComplement_eq_rank {r : ℕ} (hr : rank f = r) : finrank K f.kerComplement = r := by
  simp [finrank_eq_of_rank_eq hr, LinearEquiv.finrank_eq f.kerComplementEquivRange]

lemma finrank_ker_eq [FiniteDimensional K V] {r n : ℕ} (hr : rank f = r) (hn : finrank K V = n) :
    finrank K (ker f) = n - r := by
  rw [← hn, ← finrank_range_add_finrank_ker f, ← finrank_eq_of_rank_eq hr, add_tsub_cancel_left]

lemma card_cokernel_basis_index_eq {m r : ℕ} [FiniteDimensional K V] [FiniteDimensional K W]
    (hm : finrank K W = m) (hr : f.rank = r) :
    Fintype.card (sumExtendIndex f.linear_independent_ker_complement_basis_image) = m - r := by
  have := finrank_eq_card_basis f.range_decomposition_basis
  rw [Fintype.card_sum, hm] at this
  simp [this, ← finrank_eq_card_basis (ofVectorSpace K f.kerComplement),
    f.finrank_kerComplement_eq_rank hr]

lemma apply_kerComplement_basis_eq_range_basis (j) :
    f (f.decomposition_basis (Sum.inl j)) = (f.range_decomposition_basis (Sum.inl j)) := by
  simp [decomposition_basis, prodEquivOfkerComplement, range_decomposition_basis, sumExtend,
    Equiv.sumCongr, ker_complement_basis_image, ker_complement_restriction]

end LinearMap

end



section

variable {R : Type} [Field R] {m n r : ℕ} {M₁ M₂ : Type*}
variable [AddCommGroup M₁] [Module R M₁] [FiniteDimensional R M₁]
variable [AddCommGroup M₂] [Module R M₂] [FiniteDimensional R M₂] (f : M₁ →ₗ[R] M₂)

open Matrix LinearMap

theorem exists_basis_for_normal_form_abstract :
  ∃ (v₁ : Basis ((ofVectorSpaceIndex R f.kerComplement) ⊕ (ofVectorSpaceIndex R (ker f))) R M₁)
    (v₂ : Basis ((ofVectorSpaceIndex R f.kerComplement) ⊕
      (sumExtendIndex f.linear_independent_ker_complement_basis_image)) R M₂),
    LinearMap.toMatrix v₁ v₂ f = fromBlocks 1 0 0 0 := by
  use f.decomposition_basis, f.range_decomposition_basis
  funext i j
  match i, j with
  | Sum.inl i', Sum.inl j' => simp [toMatrix_apply, f.apply_kerComplement_basis_eq_range_basis j',
      Finsupp.single, Pi.single, Function.update, Matrix.one_apply]
  | Sum.inr i', Sum.inr j' => simp [toMatrix_apply, decomposition_basis, prodEquivOfkerComplement]
  | Sum.inl i', Sum.inr j' => simp [toMatrix_apply, decomposition_basis, prodEquivOfkerComplement]
  | Sum.inr i', Sum.inl j' => simp [toMatrix_apply, f.apply_kerComplement_basis_eq_range_basis j']

theorem exists_basis_for_normal_form (hn : finrank R M₁ = n) (hm : finrank R M₂ = m)
    (hr : rank f = r) :
    ∃ (v₁ : Basis (Fin r ⊕ Fin (n - r)) R M₁) (v₂ : Basis (Fin r ⊕ Fin (m - r)) R M₂),
    f.toMatrix v₁ v₂ = fromBlocks 1 0 0 0 := by
  have ⟨v₁, v₂, hvf⟩ := exists_basis_for_normal_form_abstract f
  let hu₁ : (ofVectorSpaceIndex R f.kerComplement) ⊕ (ofVectorSpaceIndex R (ker f)) ≃
      Fin r ⊕ Fin (n - r) := by
    refine Equiv.sumCongr (Fintype.equivFinOfCardEq ?_) (Fintype.equivFinOfCardEq ?_)
    · rw [← finrank_kerComplement_eq_rank f hr, ← finrank_eq_card_basis (ofVectorSpace _ _)]
    · rw [← f.finrank_ker_eq hr hn, ← finrank_eq_card_basis (ofVectorSpace _ _)]
  let u₁ : Basis (Fin r ⊕ Fin (n - r)) R M₁ := v₁.reindex hu₁
  let hu₂ : (ofVectorSpaceIndex R f.kerComplement) ⊕
      (sumExtendIndex f.linear_independent_ker_complement_basis_image) ≃ Fin r ⊕ Fin (m - r) := by
    refine Equiv.sumCongr (Fintype.equivFinOfCardEq ?_) (Fintype.equivFinOfCardEq ?_)
    · rw [← finrank_kerComplement_eq_rank f hr, ← finrank_eq_card_basis (ofVectorSpace _ _)]
    · rw [card_cokernel_basis_index_eq f hm hr]
  let u₂ : Basis (Fin r ⊕ Fin (m - r)) R M₂ := v₂.reindex hu₂
  use u₁, u₂
  calc
    f.toMatrix u₁ u₂ = (f.toMatrix v₁ v₂).reindex hu₂ hu₁ := by
      funext i j
      simp [u₁, u₂, toMatrix_apply]
    _ = (fromBlocks 1 0 0 0).reindex hu₂ hu₁ := by rw [hvf]
    _ = _ := by
      funext i j
      match i, j with
      | Sum.inl i', Sum.inl j' => simp [hu₂, hu₁, Matrix.one_apply]
      | Sum.inr i', Sum.inr j' => simp [hu₂, hu₁]
      | Sum.inl i', Sum.inr j' => simp [hu₂, hu₁]
      | Sum.inr i', Sum.inl j' => simp [hu₂, hu₁]

end
