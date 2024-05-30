/-
Copyright (c) 2024 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Reducing a module modulo an element of the ring

Given a commutative ring `R` and an element `r : R`, the association
`M ↦ M ⧸ rM` extends to a functor on the category of `R`-modules. This functor
is isomorphic to the functor of tensoring by `R ⧸ (r)` on either side, but can
be more convenient to work with since we can work with quotient types instead
of fiddling with simple tensors.

## Tags

module, commutative algebra
-/

open scoped Pointwise

variable {R} (M : Type*) {M' M''} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup M''] [Module R M''] (r : R)

/-- An abbreviation for `M⧸rM` that keeps us from having to write
`(⊤ : Submodule R M)` over and over to satisfy the typechecker. -/
abbrev QuotSMulTop := M ⧸ r • (⊤ : Submodule R M)

namespace QuotSMulTop

open Submodule Function TensorProduct

/-- Reducing a module modulo `r` is the same as left tensoring with `R/(r)`. -/
noncomputable def equivQuotTensor :
    QuotSMulTop M r ≃ₗ[R] (R ⧸ Ideal.span {r}) ⊗[R] M :=
  quotEquivOfEq _ _ (ideal_span_singleton_smul _ _).symm ≪≫ₗ
   (quotTensorEquivQuotSMul M _).symm

/-- Reducing a module modulo `r` is the same as right tensoring with `R/(r)`. -/
noncomputable def equivTensorQuot :
    QuotSMulTop M r ≃ₗ[R] M ⊗[R] (R ⧸ Ideal.span {r}) :=
  quotEquivOfEq _ _ (ideal_span_singleton_smul _ _).symm ≪≫ₗ
   (tensorQuotEquivQuotSMul M _).symm

variable {M}

/-- The action of the functor `QuotSMulTop · r` on morphisms. -/
def map : (M →ₗ[R] M') →ₗ[R] QuotSMulTop M r →ₗ[R] QuotSMulTop M' r :=
  Submodule.mapQLinear _ _ ∘ₗ LinearMap.id.codRestrict _ fun _ =>
    map_le_iff_le_comap.mp <| le_of_eq_of_le (map_pointwise_smul _ _ _) <|
      smul_mono_right r le_top

@[simp]
lemma map_apply_mk (f : M →ₗ[R] M') (x : M) :
    map r f (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (f x) : QuotSMulTop M' r) := rfl

-- weirdly expensive to typecheck the type here?
lemma map_comp_mkQ (f : M →ₗ[R] M') :
    map r f ∘ₗ mkQ (r • ⊤) = mkQ (r • ⊤) ∘ₗ f := by
  ext; rfl

variable (M)

@[simp]
lemma map_id : map r (LinearMap.id : M →ₗ[R] M) = .id :=
  DFunLike.ext _ _ <| (mkQ_surjective _).forall.mpr fun _ => rfl

variable {M}

@[simp]
lemma map_comp (g : M' →ₗ[R] M'') (f : M →ₗ[R] M') :
    map r (g ∘ₗ f) = map r g ∘ₗ map r f :=
  DFunLike.ext _ _ <| (mkQ_surjective _).forall.mpr fun _ => rfl

lemma equivQuotTensor_naturality_mk (f : M →ₗ[R] M') (x : M) :
    equivQuotTensor M' r (map r f (Submodule.Quotient.mk x)) =
      f.lTensor (R ⧸ Ideal.span {r})
        (equivQuotTensor M r (Submodule.Quotient.mk x)) :=
  (LinearMap.lTensor_tmul (R ⧸ Ideal.span {r}) f 1 x).symm

lemma equivQuotTensor_naturality (f : M →ₗ[R] M') :
    equivQuotTensor M' r ∘ₗ map r f =
      f.lTensor (R ⧸ Ideal.span {r}) ∘ₗ equivQuotTensor M r :=
  quot_hom_ext _ _ _ (equivQuotTensor_naturality_mk r f)

lemma equivTensorQuot_naturality_mk (f : M →ₗ[R] M') (x : M) :
    equivTensorQuot M' r (map r f (Submodule.Quotient.mk x)) =
      f.rTensor (R ⧸ Ideal.span {r})
        (equivTensorQuot M r (Submodule.Quotient.mk x)) :=
  (LinearMap.rTensor_tmul (R ⧸ Ideal.span {r}) f 1 x).symm

lemma equivTensorQuot_naturality (f : M →ₗ[R] M') :
    equivTensorQuot M' r ∘ₗ map r f =
      f.rTensor (R ⧸ Ideal.span {r}) ∘ₗ equivTensorQuot M r :=
  quot_hom_ext _ _ _ (equivTensorQuot_naturality_mk r f)

lemma map_surjective {f : M →ₗ[R] M'} (hf : Surjective f) : Surjective (map r f) :=
  have H₁ := (mkQ_surjective (r • ⊤ : Submodule R M')).comp hf
  @Surjective.of_comp _ _ _ _ (mkQ (r • ⊤ : Submodule R M)) <| by
    rwa [← LinearMap.coe_comp, map_comp_mkQ, LinearMap.coe_comp]

lemma map_exact {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}
    (hfg : Exact f g) (hg : Surjective g) : Exact (map r f) (map r g) :=
  (Exact.iff_of_ladder_linearEquiv (equivQuotTensor_naturality r f).symm
                             (equivQuotTensor_naturality r g).symm).mp
    (lTensor_exact (R ⧸ Ideal.span {r}) hfg hg)

variable (M M')

-- TODO: Naturality for `tensorQuotSMulTopEquivQuotSMulTop`
-- and `modSMulByTensorEquivQuotSMulTop`

/-- Tensoring on the left and applying `QuotSMulTop · r` commute. -/
noncomputable def tensorQuotSMulTopEquivQuotSMulTop :
    M ⊗[R] QuotSMulTop M' r ≃ₗ[R] QuotSMulTop (M ⊗[R] M') r :=
  (equivTensorQuot M' r).lTensor M ≪≫ₗ
    (TensorProduct.assoc R M M' (R ⧸ Ideal.span {r})).symm ≪≫ₗ
      (equivTensorQuot (M ⊗[R] M') r).symm

/-- Tensoring on the right and applying `QuotSMulTop · r` commute. -/
noncomputable def modSMulByTensorEquivQuotSMulTop :
    QuotSMulTop M' r ⊗[R] M ≃ₗ[R] QuotSMulTop (M' ⊗[R] M) r :=
  (equivQuotTensor M' r).rTensor M ≪≫ₗ
    TensorProduct.assoc R (R ⧸ Ideal.span {r}) M' M ≪≫ₗ
      (equivQuotTensor (M' ⊗[R] M) r).symm

end QuotSMulTop
