/-
Copyright (c) 2025 Zichen Wang, Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Yi Yuan
-/
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Rank decomposition and bases adapted to a linear map

This file develops a small API around a linear map `f : V →ₗ[K] W` that chooses a complement
of `ker f`, builds bases compatible with the direct-sum decomposition `V = ker f ⊕ C` for ker
complement `C`, and produces a rank-normal form for the matrix of `f`
-/

open Submodule Module Basis

noncomputable section

variable {K : Type*} [DivisionRing K] {V W : Type*}
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W] (f : V →ₗ[K] W)

namespace LinearMap

variable {C : Submodule K V} (h : IsCompl C (ker f))

/-- When `V` decomposes as `x ⊕ y`, the basis is obtained by transporting the product of bases
on the `x` and on `y`. -/
def decomposition_basis {x y : Submodule K V} (h : IsCompl x y) :
    Basis ((ofVectorSpaceIndex K x) ⊕ (ofVectorSpaceIndex K y)) K V :=
  .map (.prod (ofVectorSpace K _) (ofVectorSpace K _)) (prodEquivOfIsCompl _ _ h)

lemma linear_independent_ker_complement_basis_image (h : IsCompl C (ker f)) :
    LinearIndependent K ((f.comp C.subtype) ∘ (ofVectorSpace K C)) :=
  (ofVectorSpace K C).linearIndependent.map' _
    (by simpa [ker_comp, ← disjoint_iff_comap_eq_bot] using h.disjoint)

/-- A basis of `W` obtained by extending the image of the `C f` basis (which corresponds
to `range f`) to a full basis via `Basis.sumExtend`. -/
def range_decomposition_basis (h : IsCompl C (ker f)) : Basis ((ofVectorSpaceIndex K C) ⊕
    (sumExtendIndex (f.linear_independent_ker_complement_basis_image h))) K W :=
  Basis.sumExtend (f.linear_independent_ker_complement_basis_image h)

/-- `C` is isomorphic to `range f` -/
def kerComplementEquivRange : C ≃ₗ[K] (range f) := by
  let g : C →ₗ[K] range f := codRestrict (range f) (f.comp C.subtype) (fun x ↦ ⟨C.subtype x, rfl⟩)
  apply LinearEquiv.ofBijective g
  constructor
  · simpa [← ker_eq_bot, g, ker_codRestrict, ker_comp, ← disjoint_iff_comap_eq_bot] using h.disjoint
  · intro ⟨_, y, hyx⟩
    use ((prodEquivOfIsCompl _ _ h).2 y).1
    simp [g, codRestrict, ← hyx]
    nth_rw 2 [← Submodule.IsCompl.projection_add_projection_eq_self h y]
    rw [map_add, h.symm.projection_apply_mem y, add_zero]
    rfl

end LinearMap

end



noncomputable section

variable {R : Type} [Field R] {m n r : ℕ} {M₁ M₂ : Type*}
variable [AddCommGroup M₁] [Module R M₁] [FiniteDimensional R M₁]
variable [AddCommGroup M₂] [Module R M₂] [FiniteDimensional R M₂] (f : M₁ →ₗ[R] M₂)

open Matrix LinearMap

instance {C : Submodule R M₁} : DecidableEq (ofVectorSpaceIndex R C) := Classical.typeDecidableEq _

theorem exists_basis_for_normal_form_abstract {C : Submodule R M₁} (h : IsCompl C (ker f)) :
  haveI : Finite ((ofVectorSpaceIndex R C) ⊕
      (sumExtendIndex (f.linear_independent_ker_complement_basis_image h))) :=
    Fintype.finite (FiniteDimensional.fintypeBasisIndex (f.range_decomposition_basis h))

  ∃ (v₁ : Basis ((ofVectorSpaceIndex R C) ⊕ (ofVectorSpaceIndex R (ker f))) R M₁)
    (v₂ : Basis ((ofVectorSpaceIndex R C) ⊕
      (sumExtendIndex (f.linear_independent_ker_complement_basis_image h))) R M₂),
    LinearMap.toMatrix v₁ v₂ f = fromBlocks 1 0 0 0 := by
  have (j : ofVectorSpaceIndex R C) : f (decomposition_basis h (Sum.inl j))
      = (f.range_decomposition_basis h (Sum.inl j)) := by
    simp [decomposition_basis, range_decomposition_basis, sumExtend, Equiv.sumCongr]
  use (decomposition_basis h), (f.range_decomposition_basis h)
  funext i j
  match i, j with
  | Sum.inl i', Sum.inl j' => simp [toMatrix_apply, this j', Finsupp.single, Pi.single,
      Function.update, Matrix.one_apply]
  | Sum.inr i', Sum.inr j' => simp [toMatrix_apply, decomposition_basis]
  | Sum.inl i', Sum.inr j' => simp [toMatrix_apply, decomposition_basis]
  | Sum.inr i', Sum.inl j' => simp [toMatrix_apply, this j']

end
