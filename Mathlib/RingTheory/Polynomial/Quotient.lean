/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, David Kurniadi Angdinata, Devon Tuma, Riccardo Brasca

! This file was ported from Lean 3 source module ring_theory.polynomial.quotient
! leanprover-community/mathlib commit 61d8b8248633da198afea97ae7a90ee63bdf8c1c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Polynomial.Div
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.Tactic.SimpIntro

/-!
# Quotients of polynomial rings
-/


set_option linter.uppercaseLean3 false

open Polynomial

namespace Polynomial

variable {R : Type _} [CommRing R]

noncomputable def quotientSpanXSubCAlgEquivAux2 (x : R) :
    (R[X] ⧸ (RingHom.ker (aeval x).toRingHom : Ideal R[X])) ≃ₐ[R] R :=
let e :=
  RingHom.quotientKerEquivOfRightInverse (by intro x; exact eval_C :
    Function.RightInverse (fun a : R => (C a : R[X])) (@aeval R R _ _ _ x))
{ e with commutes' := fun r => e.apply_symm_apply r }

noncomputable def quotientSpanXSubCAlgEquivAux1 (x : R) :
  (R[X] ⧸ Ideal.span {X - C x}) ≃ₐ[R] (R[X] ⧸ (RingHom.ker (aeval x).toRingHom : Ideal R[X])) :=
@Ideal.quotientEquivAlgOfEq R R[X] _ _ _ _ _ (ker_evalRingHom x).symm

-- port note: need to split this definition into two sub-definitions to prevent time out
noncomputable def quotientSpanXSubCAlgEquiv (x : R) :
    (R[X] ⧸ Ideal.span ({X - C x} : Set R[X])) ≃ₐ[R] R :=
(quotientSpanXSubCAlgEquivAux1 x).trans (quotientSpanXSubCAlgEquivAux2 x)
#align polynomial.quotient_span_X_sub_C_alg_equiv Polynomial.quotientSpanXSubCAlgEquiv

@[simp]
theorem quotientSpanXSubCAlgEquiv_mk (x : R) (p : R[X]) :
    quotientSpanXSubCAlgEquiv x (Ideal.Quotient.mk _ p) = p.eval x :=
  rfl
#align polynomial.quotient_span_X_sub_C_alg_equiv_mk Polynomial.quotientSpanXSubCAlgEquiv_mk

@[simp]
theorem quotientSpanXSubCAlgEquiv_symm_apply (x : R) (y : R) :
    (quotientSpanXSubCAlgEquiv x).symm y = algebraMap R _ y :=
  rfl
#align polynomial.quotient_span_X_sub_C_alg_equiv_symm_apply Polynomial.quotientSpanXSubCAlgEquiv_symm_apply

end Polynomial

namespace Ideal

noncomputable section

open Polynomial

variable {R : Type _} [CommRing R]

theorem quotient_map_C_eq_zero {I : Ideal R} :
    ∀ a ∈ I, ((Quotient.mk (map (C : R →+* R[X]) I : Ideal R[X])).comp C) a = 0 := by
  intro a ha
  rw [RingHom.comp_apply, Quotient.eq_zero_iff_mem]
  exact mem_map_of_mem _ ha
#align ideal.quotient_map_C_eq_zero Ideal.quotient_map_C_eq_zero

theorem eval₂_C_mk_eq_zero {I : Ideal R} :
    ∀ f ∈ (map (C : R →+* R[X]) I : Ideal R[X]), eval₂RingHom (C.comp (Quotient.mk I)) X f = 0 := by
  intro a ha
  rw [← sum_monomial_eq a]
  dsimp
  rw [eval₂_sum]
  refine' Finset.sum_eq_zero fun n _ => _
  dsimp
  rw [eval₂_monomial (C.comp (Quotient.mk I)) X]
  refine' mul_eq_zero_of_left (Polynomial.ext fun m => _) (X ^ n)
  erw [coeff_C]
  by_cases h : m = 0
  · simpa [h] using Quotient.eq_zero_iff_mem.2 ((mem_map_C_iff.1 ha) n)
  · simp [h]
#align ideal.eval₂_C_mk_eq_zero Ideal.eval₂_C_mk_eq_zero

lemma polynomialQuotientEquivQuotientPolynomial_eval₂RingHom_left_inverse (I : Ideal R) :
  Function.LeftInverse
    (Quotient.lift (map C I : Ideal R[X]) (eval₂RingHom (C.comp (Quotient.mk I)) X)
      eval₂_C_mk_eq_zero)
    (eval₂RingHom
      (Quotient.lift I ((Quotient.mk (map C I : Ideal R[X])).comp C) quotient_map_C_eq_zero)
      (Quotient.mk (map C I : Ideal R[X]) X)) := by
intro f
refine Polynomial.induction_on' f ?_ ?_
· intro p q hp hq
  simp only [coe_eval₂RingHom] at hp
  simp only [coe_eval₂RingHom] at hq
  simp only [coe_eval₂RingHom, hp, hq, RingHom.map_add]
. rintro n ⟨x⟩
  erw [← smul_X_eq_monomial, smul_eq_C_mul, _root_.map_mul, coe_eval₂RingHom, eval₂_C, eval₂_X_pow,
    Quotient.lift_mk, coe_eval₂RingHom, eval₂_mul, eval₂_C, RingHom.comp_apply, eval₂_X_pow]

lemma polynomialQuotientEquivQuotientPolynomial_eval₂_right_inverse' (I : Ideal R)
  (f : R[X]) :
  ((eval₂
      (Quotient.lift I ((Quotient.mk (map C I : Ideal R[X])).comp C) quotient_map_C_eq_zero)
      (Quotient.mk (map C I : Ideal R[X]) X)) <|
    eval₂ (C.comp (Quotient.mk I)) X f) =
  Quotient.mk (map C I : Ideal R[X]) f := by
refine Polynomial.induction_on' f ?_ ?_
· intros p q hp hq
  rw [eval₂_add, eval₂_add, hp, hq, RingHom.map_add]
· intro n a
  rw [← smul_X_eq_monomial, smul_eq_C_mul, eval₂_mul, eval₂_C, eval₂_X_pow, RingHom.comp_apply,
    RingHom.map_mul, eval₂_mul, eval₂_C, eval₂_X_pow, Quotient.lift_mk]
  simp_rw [_root_.map_pow]
  rfl

lemma polynomialQuotientEquivQuotientPolynomial_eval₂RingHom_right_inverse (I : Ideal R)
  (f : R[X] ⧸ (map C I : Ideal R[X])) :
  ((eval₂RingHom
      (Quotient.lift I ((Quotient.mk (map C I : Ideal R[X])).comp C) quotient_map_C_eq_zero)
      (Quotient.mk (map C I : Ideal R[X]) X)) <|
    (Quotient.lift (map C I : Ideal R[X]) (eval₂RingHom (C.comp (Quotient.mk I)) X)
      eval₂_C_mk_eq_zero) <| f) = f := by
obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
exact polynomialQuotientEquivQuotientPolynomial_eval₂_right_inverse' I f

/-- If `I` is an ideal of `R`, then the ring polynomials over the quotient ring `I.quotient` is
isomorphic to the quotient of `R[X]` by the ideal `map C I`,
where `map C I` contains exactly the polynomials whose coefficients all lie in `I` -/
def polynomialQuotientEquivQuotientPolynomial (I : Ideal R) :
    (R ⧸ I)[X] ≃+* R[X] ⧸ (map C I : Ideal R[X]) :=
let e : (R ⧸ I)[X] →+* R[X] ⧸ map C I := eval₂RingHom
  (Quotient.lift I ((Quotient.mk (map C I : Ideal R[X])).comp C) quotient_map_C_eq_zero)
  (Quotient.mk (map C I : Ideal R[X]) X)
{ e with
  invFun := Quotient.lift (map C I : Ideal R[X]) (eval₂RingHom (C.comp (Quotient.mk I)) X)
      eval₂_C_mk_eq_zero
  -- port note: need to split this definition into two sub-lemmas to prevent time out
  left_inv := polynomialQuotientEquivQuotientPolynomial_eval₂RingHom_left_inverse I
  right_inv := polynomialQuotientEquivQuotientPolynomial_eval₂RingHom_right_inverse I }
#align ideal.polynomial_quotient_equiv_quotient_polynomial Ideal.polynomialQuotientEquivQuotientPolynomial

@[simp]
theorem polynomialQuotientEquivQuotientPolynomial_symm_mk (I : Ideal R) (f : R[X]) :
    I.polynomialQuotientEquivQuotientPolynomial.symm (Quotient.mk _ f) = f.map (Quotient.mk I) := by
  rw [polynomialQuotientEquivQuotientPolynomial, RingEquiv.symm_mk, RingEquiv.coe_mk,
    Equiv.coe_fn_mk, Quotient.lift_mk, coe_eval₂RingHom, eval₂_eq_eval_map, ← Polynomial.map_map,
    ← eval₂_eq_eval_map, Polynomial.eval₂_C_X]
#align ideal.polynomial_quotient_equiv_quotient_polynomial_symm_mk Ideal.polynomialQuotientEquivQuotientPolynomial_symm_mk

@[simp]
theorem polynomialQuotientEquivQuotientPolynomial_map_mk (I : Ideal R) (f : R[X]) :
    I.polynomialQuotientEquivQuotientPolynomial (f.map <| Ideal.Quotient.mk I) =
    Quotient.mk ((map C I : Ideal R[X])) f := by
  apply (polynomialQuotientEquivQuotientPolynomial I).symm.injective
  rw [RingEquiv.symm_apply_apply, polynomialQuotientEquivQuotientPolynomial_symm_mk]
#align ideal.polynomial_quotient_equiv_quotient_polynomial_map_mk Ideal.polynomialQuotientEquivQuotientPolynomial_map_mk

/-- If `P` is a prime ideal of `R`, then `R[x]/(P)` is an integral domain. -/
theorem isDomain_map_C_quotient {P : Ideal R} (_ : IsPrime P) :
    IsDomain (R[X] ⧸ (map (C : R →+* R[X]) P : Ideal R[X])) :=
  RingEquiv.isDomain (Polynomial (R ⧸ P)) (polynomialQuotientEquivQuotientPolynomial P).symm
#align ideal.is_domain_map_C_quotient Ideal.isDomain_map_C_quotient

set_option synthInstance.etaExperiment true in
/-- Given any ring `R` and an ideal `I` of `R[X]`, we get a map `R → R[x] → R[x]/I`.
  If we let `R` be the image of `R` in `R[x]/I` then we also have a map `R[x] → R'[x]`.
  In particular we can map `I` across this map, to get `I'` and a new map `R' → R'[x] → R'[x]/I`.
  This theorem shows `I'` will not contain any non-zero constant polynomials
  -/
theorem eq_zero_of_polynomial_mem_map_range (I : Ideal R[X]) (x : ((Quotient.mk I).comp C).range)
    (hx : C x ∈ I.map (Polynomial.mapRingHom ((Quotient.mk I).comp C).rangeRestrict)) :
    (x : R[X] ⧸ I) = 0 := by
  let i := ((Quotient.mk I).comp C).rangeRestrict
  have hi' : RingHom.ker (Polynomial.mapRingHom i) ≤ I := by
    refine' fun f hf => polynomial_mem_ideal_of_coeff_mem_ideal I f fun n => _
    rw [mem_comap, ← Quotient.eq_zero_iff_mem, ← RingHom.comp_apply]
    rw [RingHom.mem_ker, coe_mapRingHom] at hf
    replace hf := congr_arg (fun f : Polynomial _ => f.coeff n) hf
    simp only [coeff_map, coeff_zero] at hf
    rwa [Subtype.ext_iff, RingHom.coe_rangeRestrict] at hf
  obtain ⟨x, hx'⟩ := x
  obtain ⟨y, rfl⟩ := RingHom.mem_range.1 hx'
  simp only [RingHom.comp_apply, Quotient.eq_zero_iff_mem]
  suffices C (i y) ∈ I.map (Polynomial.mapRingHom i) by
    obtain ⟨f, hf⟩ :=
      mem_image_of_mem_map_of_surjective (Polynomial.mapRingHom i)
        (Polynomial.map_surjective _ (RingHom.rangeRestrict_surjective _)) this
    refine' sub_add_cancel (C y) f ▸ I.add_mem (hi' _ : C y - f ∈ I) hf.1
    rw [RingHom.mem_ker, RingHom.map_sub, hf.2, sub_eq_zero, coe_map_ring_hom, map_C]
  exact hx
#align ideal.eq_zero_of_polynomial_mem_map_range Ideal.eq_zero_of_polynomial_mem_map_range

end

end Ideal

namespace MvPolynomial

variable {R : Type _} {σ : Type _} [CommRing R] {r : R}

theorem quotient_map_C_eq_zero {I : Ideal R} {i : R} (hi : i ∈ I) :
    (Ideal.Quotient.mk (Ideal.map (C : R →+* MvPolynomial σ R) I : Ideal (MvPolynomial σ R))).comp C
        i =
      0 := by
  simp only [Function.comp_apply, RingHom.coe_comp, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ hi
#align mv_polynomial.quotient_map_C_eq_zero MvPolynomial.quotient_map_C_eq_zero

theorem eval₂_C_mk_eq_zero {I : Ideal R} {a : MvPolynomial σ R}
    (ha : a ∈ (Ideal.map (C : R →+* MvPolynomial σ R) I : Ideal (MvPolynomial σ R))) :
    eval₂Hom (C.comp (Ideal.Quotient.mk I)) X a = 0 := by
  rw [as_sum a]
  rw [coe_eval₂_hom, eval₂_sum]
  refine' Finset.sum_eq_zero fun n hn => _
  simp only [eval₂_monomial, Function.comp_apply, RingHom.coeCcomp]
  refine' mul_eq_zero_of_left _ _
  suffices coeff n a ∈ I by
    rw [← @Ideal.mk_ker R _ I, RingHom.mem_ker] at this
    simp only [this, C_0]
  exact mem_map_C_iff.1 ha n
#align mv_polynomial.eval₂_C_mk_eq_zero MvPolynomial.eval₂_C_mk_eq_zero

/-- If `I` is an ideal of `R`, then the ring `mv_polynomial σ I.quotient` is isomorphic as an
`R`-algebra to the quotient of `mv_polynomial σ R` by the ideal generated by `I`. -/
def quotientEquivQuotientMvPolynomial (I : Ideal R) :
    MvPolynomial σ (R ⧸ I) ≃ₐ[R] MvPolynomial σ R ⧸ (Ideal.map C I : Ideal (MvPolynomial σ R)) where
  toFun :=
    eval₂Hom
      (Ideal.Quotient.lift I ((Ideal.Quotient.mk (Ideal.map C I : Ideal (MvPolynomial σ R))).comp C)
        fun i hi => quotient_map_C_eq_zero hi)
      fun i => Ideal.Quotient.mk (Ideal.map C I : Ideal (MvPolynomial σ R)) (X i)
  invFun :=
    Ideal.Quotient.lift (Ideal.map C I : Ideal (MvPolynomial σ R))
      (eval₂Hom (C.comp (Ideal.Quotient.mk I)) X) fun a ha => eval₂_C_mk_eq_zero ha
  map_mul' := RingHom.map_mul _
  map_add' := RingHom.map_add _
  left_inv := by
    intro f
    apply induction_on f
    · rintro ⟨r⟩
      rw [coe_eval₂_hom, eval₂_C]
      simp only [Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_C,
        Function.comp_apply, Ideal.Quotient.mk_eq_mk, MvPolynomial.C_inj, RingHom.coeCcomp]
    · simp_intro p q hp hq only [RingHom.map_add, MvPolynomial.coe_eval₂Hom, coe_eval₂_hom,
        MvPolynomial.eval₂_add]
      rw [hp, hq]
    · simp_intro p i hp only [coe_eval₂_hom]
      simp only [hp, coe_eval₂_hom, Ideal.Quotient.lift_mk, eval₂_mul, RingHom.map_mul, eval₂_X]
  right_inv := by
    rintro ⟨f⟩
    apply induction_on f
    · intro r
      simp only [Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.lift_mk, Ideal.Quotient.mk_eq_mk,
        RingHom.coeCcomp, eval₂_hom_C]
    · simp_intro p q hp hq only [Submodule.Quotient.quot_mk_eq_mk, eval₂_add, RingHom.map_add,
        coe_eval₂_hom, Ideal.Quotient.lift_mk, Ideal.Quotient.mk_eq_mk]
      rw [hp, hq]
    · simp_intro p i hp only [Submodule.Quotient.quot_mk_eq_mk, coe_eval₂_hom,
        Ideal.Quotient.lift_mk, Ideal.Quotient.mk_eq_mk, eval₂_mul, RingHom.map_mul, eval₂_X]
      simp only [hp]
  commutes' r := eval₂Hom_C _ _ (Ideal.Quotient.mk I r)
#align mv_polynomial.quotient_equiv_quotient_mv_polynomial MvPolynomial.quotientEquivQuotientMvPolynomial

end MvPolynomial
