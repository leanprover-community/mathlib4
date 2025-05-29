/-
Copyright (c) 2021 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Multilinear.Pi

/-!
# Multilinear maps in relation to bases.

This file proves lemmas about the action of multilinear maps on basis vectors.

-/


open MultilinearMap

variable {ι R : Type*} [CommSemiring R]
  {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  {N : Type*} [AddCommMonoid N] [Module R N]

/-- Two multilinear maps indexed by a `Fintype` are equal if they are equal when all arguments
are basis vectors. -/
theorem Basis.ext_multilinear [Finite ι] {f g : MultilinearMap R M N} {ιM : ι → Type*}
    (e : ∀ i, Basis (ιM i) R (M i))
    (h : ∀ v : (i : ι) → ιM i, (f fun i ↦ e i (v i)) = g fun i ↦ e i (v i)) : f = g := by
  cases nonempty_fintype ι
  classical
  ext m
  rcases Function.Surjective.piMap (fun i ↦ (e i).repr.symm.surjective) m with ⟨x, rfl⟩
  unfold Pi.map
  simp_rw [(e _).repr_symm_apply, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum_finset, map_smul_univ, h]

@[deprecated (since := "2025-05-12")]
alias Basis.ext_multilinear_fin := Basis.ext_multilinear



section Basis
variable {κ : ι → Type*} {ι' : Type*} {M : ι → Type*} {N : Type*}

variable [Fintype ι] [∀ i, Fintype (κ i)] [CommSemiring R]
variable [∀ i, AddCommMonoid (M i)] [AddCommMonoid N]
variable [∀ i, Module R (M i)] [Module R N]

-- /-- The linear equivalence between families indexed by `p : Π i : ι, κ i` of multilinear maps
-- on the `fun i ↦ M i (p i)` and the space of multilinear map on `fun i ↦ Π₀ j : κ i, M i j`. -/
-- noncomputable def _root_.Basis.multilinearMap (b : ∀ i, Basis (κ i) R (M i)) (b' : Basis ι' R N) :
--     Basis ((Π i, κ i) × ι') R (MultilinearMap R M N) :=
--   .ofEquivFun <| by
--     classical
--     -- switch to dfinsupp
--     let b := fun i => (b i).equivFun
--     let b' := b'.repr ≪≫ₗ (finsuppLequivDFinsupp R)
--     suffices
--         MultilinearMap R (fun i => Π₀ j : κ i, R) (Π₀ i : ι', R) ≃ₗ[R]
--           Π₀ (x : ((i : ι) → κ i) × ι'), R from
--       b'.congrRightMultilinear R ≪≫ₗ LinearEquiv.congrLeftMultilinear (b · |>.symm) ≪≫ₗ this

--     refine (fromDFinsuppEquiv _ _).symm ≪≫ₗ
--       LinearEquiv.piCongrRight (fun i => MultilinearMap.piRingEquiv.symm) ≪≫ₗ ?_
--     -- some annoying swap between Π and Π₀
--     sorry

end Basis
