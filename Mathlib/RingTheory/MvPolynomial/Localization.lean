/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!

# Localization and multivariate polynomial rings

In this file we show some results connecting multivariate polynomial rings and localization.

## Main results

- `MvPolynomial.isLocalization`: If `S` is the localization of `R` at a submonoid `M`, then
  `MvPolynomial σ S` is the localization of `MvPolynomial σ R` at the image of `M` in
  `MvPolynomial σ R`.

-/

variable {σ R : Type*} [CommRing R] (M : Submonoid R)
variable (S : Type*) [CommRing S] [Algebra R S]

namespace MvPolynomial

variable [IsLocalization M S]

attribute [local instance] algebraMvPolynomial

/--
If `S` is the localization of `R` at a submonoid `M`, then `MvPolynomial σ S`
is the localization of `MvPolynomial σ R` at `M.map MvPolynomial.C`.

See also `Polynomial.isLocalization` for the univariate case. -/
instance isLocalization : IsLocalization (M.map <| C (σ := σ)) (MvPolynomial σ S) :=
  isLocalizedModule_iff_isLocalization.mp <| (isLocalizedModule_iff_isBaseChange M S _).mpr <|
    .of_equiv (algebraTensorAlgEquiv _ _).toLinearEquiv fun _ ↦ by simp

lemma isLocalization_C_mk' (a : R) (m : M) :
    C (IsLocalization.mk' S a m) = IsLocalization.mk' (MvPolynomial σ S) (C (σ := σ) a)
      ⟨C m, Submonoid.mem_map_of_mem C m.property⟩ := by
  simp_rw [IsLocalization.eq_mk'_iff_mul_eq, algebraMap_def, map_C, ← map_mul,
    IsLocalization.mk'_spec]

end MvPolynomial

namespace IsLocalization.Away

open MvPolynomial

variable (r : R) [IsLocalization.Away r S]

/-- The canonical algebra map from `MvPolynomial Unit R` quotiented by
`C r * X () - 1` to the localization of `R` away from `r`. -/
private noncomputable
def auxHom : (MvPolynomial Unit R) ⧸ (Ideal.span { C r * X () - 1 }) →ₐ[R] S :=
  Ideal.Quotient.liftₐ (Ideal.span { C r * X () - 1}) (aeval (fun _ ↦ invSelf r)) <| by
    intro p hp
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
    · rintro p ⟨q, rfl⟩
      simp
    · simp
    · intro p q _ _ hp hq
      simp [hp, hq]
    · intro a x _ hx
      simp [hx]

@[simp]
private lemma auxHom_mk (p : MvPolynomial Unit R) :
    auxHom S r p = aeval (S₁ := S) (fun _ ↦ invSelf r) p :=
  rfl

private noncomputable
def auxInv : S →+* (MvPolynomial Unit R) ⧸ Ideal.span { C r * X () - 1 } :=
  letI g : R →+* MvPolynomial Unit R ⧸ (Ideal.span { C r * X () - 1 }) :=
    (Ideal.Quotient.mk _).comp C
  IsLocalization.Away.lift (S := S) (g := g) r <| by
    simp only [RingHom.coe_comp, Function.comp_apply, g]
    rw [isUnit_iff_exists_inv]
    use (Ideal.Quotient.mk _ <| X ())
    rw [← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact Ideal.mem_span_singleton_self (C r * X () - 1)

private lemma auxHom_auxInv : (auxHom S r).toRingHom.comp (auxInv S r) = RingHom.id S := by
  apply IsLocalization.ringHom_ext (Submonoid.powers r)
  ext x
  simp [auxInv]

private lemma auxInv_auxHom : (auxInv S r).comp (auxHom (S := S) r).toRingHom = RingHom.id _ := by
  rw [← RingHom.cancel_right (Ideal.Quotient.mk_surjective)]
  ext x
  · simp [auxInv]
  · simp only [auxInv, AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
      Function.comp_apply, auxHom_mk, aeval_X, RingHomCompTriple.comp_eq, invSelf, Away.lift,
      lift_mk'_spec]
    simp only [map_one]
    rw [← map_one (Ideal.Quotient.mk _), ← map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem,
      ← Ideal.neg_mem_iff, neg_sub]
    exact Ideal.mem_span_singleton_self (C r * X x - 1)

/-- The canonical algebra isomorphism from `MvPolynomial Unit R` quotiented by
`C r * X () - 1` to the localization of `R` away from `r`. -/
noncomputable def mvPolynomialQuotientEquiv :
    ((MvPolynomial Unit R) ⧸ Ideal.span { C r * X () - 1 }) ≃ₐ[R] S where
  toFun := auxHom S r
  invFun := auxInv S r
  left_inv x := by
    simpa using congrFun (congrArg DFunLike.coe <| auxInv_auxHom S r) x
  right_inv s := by
    simpa using congrFun (congrArg DFunLike.coe <| auxHom_auxInv S r) s
  map_mul' := by simp
  map_add' := by simp
  commutes' := by simp

@[simp]
lemma mvPolynomialQuotientEquiv_apply (p : MvPolynomial Unit R) :
    mvPolynomialQuotientEquiv S r (Ideal.Quotient.mk _ p) = aeval (S₁ := S) (fun _ ↦ invSelf r) p :=
  rfl

end IsLocalization.Away
