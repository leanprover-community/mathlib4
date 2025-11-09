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

/-- When `V` decomposes as `ker f ⊕ C`, the basis is obtained by transporting the product of bases
on the kernel and on its complement along `f.prodEquivOfC`. -/
def decomposition_basis : Basis ((ofVectorSpaceIndex K C) ⊕
    (ofVectorSpaceIndex K (ker f))) K V :=
  .map (.prod (ofVectorSpace K _) (ofVectorSpace K _)) (prodEquivOfIsCompl _ _ h)

/-- Given the basis of `C f` and the restriction map
`f ∘ Submodule.subtype (C f)`, define the function that sends the
basis indices to vectors of `W`. -/
def ker_complement_basis_image (C : Submodule K V) : ofVectorSpaceIndex K C → W :=
  (f.comp C.subtype) ∘ (ofVectorSpace K C)

lemma linear_independent_ker_complement_basis_image (h : IsCompl C (ker f)) :
    LinearIndependent K (f.ker_complement_basis_image C) :=
  (ofVectorSpace K C).linearIndependent.map' _
    (by simpa [ker_comp, ← disjoint_iff_comap_eq_bot] using h.disjoint)

/-- A basis of `W` obtained by extending the image of the `C f` basis (which corresponds
to `range f`) to a full basis via `Basis.sumExtend`. -/
def range_decomposition_basis (h : IsCompl C (ker f)) :
    Basis ((ofVectorSpaceIndex K C) ⊕
    (sumExtendIndex (f.linear_independent_ker_complement_basis_image h))) K W :=
  Basis.sumExtend (f.linear_independent_ker_complement_basis_image h)

/-- `C` is isomorphic to `range f` -/
def CEquivRange : C ≃ₗ[K] (range f) := by
  let g : C →ₗ[K] range f := codRestrict (range f) (f.comp C.subtype)
    (fun x ↦ ⟨C.subtype x, rfl⟩)
  apply LinearEquiv.ofBijective g
  constructor
  · simpa [← ker_eq_bot, g, ker_codRestrict, ker_comp, ← disjoint_iff_comap_eq_bot] using h.disjoint
  intro ⟨_, y, hyx⟩
  use ((prodEquivOfIsCompl _ _ h).2 y).1
  simp [g, codRestrict, ← hyx]
  nth_rw 2 [← Submodule.IsCompl.projection_add_projection_eq_self h y]
  rw [map_add, h.symm.projection_apply_mem y, add_zero]
  rfl

lemma apply_C_basis_eq_range_basis (j) :
    f (f.decomposition_basis h (Sum.inl j)) = (f.range_decomposition_basis h (Sum.inl j)) := by
  simp [decomposition_basis, range_decomposition_basis, sumExtend,
    Equiv.sumCongr, ker_complement_basis_image]

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
  use (f.decomposition_basis h), (f.range_decomposition_basis h)
  funext i j
  match i, j with
  | Sum.inl i', Sum.inl j' => simp [toMatrix_apply, f.apply_C_basis_eq_range_basis h j',
      Finsupp.single, Pi.single, Function.update, Matrix.one_apply]
  | Sum.inr i', Sum.inr j' => simp [toMatrix_apply, decomposition_basis]
  | Sum.inl i', Sum.inr j' => simp [toMatrix_apply, decomposition_basis]
  | Sum.inr i', Sum.inl j' => simp [toMatrix_apply, f.apply_C_basis_eq_range_basis h j']

end
