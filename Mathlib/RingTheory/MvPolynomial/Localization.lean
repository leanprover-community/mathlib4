/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.MvPolynomial.Basic

/-!

# Localization and multivariate polynomial rings

In this file we show some results connecting multivariate polynomial rings and localization.

## Main results

- `MvPolynomial.isLocalization`: If `S` is the localization of `R` at a submonoid `M`, then
  `MvPolynomial σ S` is the localization of `MvPolynomial σ R` at the image of `M` in
  `MvPolynomial σ R`.

-/

open Classical

variable {σ R : Type*} [CommRing R] (M : Submonoid R)
variable (S : Type*) [CommRing S] [Algebra R S]

namespace MvPolynomial

variable [IsLocalization M S]

attribute [local instance] algebraMvPolynomial

/--
If `S` is the localization of `R` at a submonoid `M`, then `MvPolynomial σ S`
is the localization of `MvPolynomial σ R` at `M.map MvPolynomial.C`.
-/
instance isLocalization : IsLocalization (M.map <| C (σ := σ))
    (MvPolynomial σ S) where
  map_units' := by
    rintro ⟨p, q, hq, rfl⟩
    simp only [algebraMap_def, map_C]
    exact IsUnit.map _ (IsLocalization.map_units _ ⟨q, hq⟩)
  surj' p := by
    simp only [algebraMap_def, Prod.exists, Subtype.exists,
      Submonoid.mem_map, exists_prop, exists_exists_and_eq_and, map_C]
    refine induction_on' p ?_ ?_
    · intro u s
      obtain ⟨⟨r, m⟩, hr⟩ := IsLocalization.surj M s
      use monomial u r, m, m.property
      simp only [map_monomial]
      rw [← hr, mul_comm, C_mul_monomial, mul_comm]
    · intro p p' ⟨x, m, hm, hxm⟩ ⟨x', m', hm', hxm'⟩
      use x * (C m') + x' * (C m), m * m', Submonoid.mul_mem _ hm hm'
      simp only [map_mul, map_add, map_C]
      rw [add_mul, ← mul_assoc, hxm, ← mul_assoc, ← hxm, ← hxm']
      ring
  exists_of_eq {p q} := by
    intro h
    simp_rw [algebraMap_def, ext_iff, coeff_map] at h
    choose c hc using (fun m ↦ IsLocalization.exists_of_eq (M := M) (h m))
    simp only [Subtype.exists, Submonoid.mem_map, exists_prop, exists_exists_and_eq_and]
    refine ⟨Finset.prod (p.support ∪ q.support) (fun m ↦ c m), ?_, ?_⟩
    · exact M.prod_mem (fun m _ ↦ (c m).property)
    · ext m
      simp only [coeff_C_mul]
      by_cases h : m ∈ p.support ∪ q.support
      · exact Finset.prod_mul_eq_prod_mul_of_exists m h (hc m)
      · simp only [Finset.mem_union, mem_support_iff, ne_eq, not_or, Decidable.not_not] at h
        rw [h.left, h.right]

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
    refine Submodule.span_induction hp ?_ ?_ ?_ ?_
    · rintro p ⟨q, rfl⟩
      simp
    · simp
    · intro p q hp hq
      simp [hp, hq]
    · intro a x hx
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
    rw [← _root_.map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.mk_eq_mk_iff_sub_mem]
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
      Function.comp_apply, auxHom_mk, aeval_X, RingHomCompTriple.comp_eq]
    erw [IsLocalization.lift_mk'_spec]
    simp only [map_one, RingHom.coe_comp, Function.comp_apply]
    rw [← _root_.map_one (Ideal.Quotient.mk _)]
    rw [← _root_.map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← Ideal.neg_mem_iff, neg_sub]
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
