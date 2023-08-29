/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, David Kurniadi Angdinata, Devon Tuma, Riccardo Brasca
-/
import Mathlib.Data.Polynomial.Div
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Ideal.QuotientOperations

#align_import ring_theory.polynomial.quotient from "leanprover-community/mathlib"@"4f840b8d28320b20c87db17b3a6eef3d325fca87"

/-!
# Quotients of polynomial rings
-/


set_option linter.uppercaseLean3 false

open Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R]

noncomputable def quotientSpanXSubCAlgEquivAux2 (x : R) :
    (R[X] ⧸ (RingHom.ker (aeval x).toRingHom : Ideal R[X])) ≃ₐ[R] R :=
  let e := RingHom.quotientKerEquivOfRightInverse (fun x => by
    exact eval_C : Function.RightInverse (fun a : R => (C a : R[X])) (@aeval R R _ _ _ x))
    -- 🎉 no goals
  { e with commutes' := fun r => e.apply_symm_apply r }

noncomputable def quotientSpanXSubCAlgEquivAux1 (x : R) :
    (R[X] ⧸ Ideal.span {X - C x}) ≃ₐ[R] (R[X] ⧸ (RingHom.ker (aeval x).toRingHom : Ideal R[X])) :=
  @Ideal.quotientEquivAlgOfEq R R[X] _ _ _ _ _ (ker_evalRingHom x).symm

-- porting note: need to split this definition into two sub-definitions to prevent time out
/-- For a commutative ring $R$, evaluating a polynomial at an element $x \in R$ induces an
isomorphism of $R$-algebras $R[X] / \langle X - x \rangle \cong R$. -/
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

/-- For a commutative ring $R$, evaluating a polynomial at an element $y \in R$ induces an
isomorphism of $R$-algebras $R[X] / \langle x, X - y \rangle \cong R / \langle x \rangle$. -/
noncomputable def quotientSpanCXSubCAlgEquiv (x y : R) :
    (R[X] ⧸ (Ideal.span {C x, X - C y} : Ideal R[X])) ≃ₐ[R] R ⧸ (Ideal.span {x} : Ideal R) :=
  (Ideal.quotientEquivAlgOfEq R <| by rw [Ideal.span_insert, sup_comm]).trans <|
                                      -- 🎉 no goals
    (DoubleQuot.quotQuotEquivQuotSupₐ R _ _).symm.trans <|
      (Ideal.quotientEquivAlg _ _ (quotientSpanXSubCAlgEquiv y) rfl).trans <|
        Ideal.quotientEquivAlgOfEq R <| by
          simp only [Ideal.map_span, Set.image_singleton]; congr 2; exact eval_C
          -- ⊢ Ideal.span {↑↑(quotientSpanXSubCAlgEquiv y) (↑(Ideal.Quotient.mkₐ R (Ideal.s …
                                                           -- ⊢ ↑↑(quotientSpanXSubCAlgEquiv y) (↑(Ideal.Quotient.mkₐ R (Ideal.span {X - ↑C  …
                                                                    -- 🎉 no goals
#align polynomial.quotient_span_C_X_sub_C_alg_equiv Polynomial.quotientSpanCXSubCAlgEquiv

set_option maxHeartbeats 250000 in
/-- For a commutative ring $R$, evaluating a polynomial at elements $y(X) \in R[X]$ and $x \in R$
induces an isomorphism of $R$-algebras $R[X, Y] / \langle X - x, Y - y(X) \rangle \cong R$. -/
noncomputable def quotientSpanCXSubCXSubCAlgEquiv {x : R} {y : R[X]} :
    @AlgEquiv R (R[X][X] ⧸ (Ideal.span {C (X - C x), X - C y} : Ideal <| R[X][X])) R _ _ _
      (Ideal.Quotient.algebra R) _ :=
((quotientSpanCXSubCAlgEquiv (X - C x) y).restrictScalars R).trans <| quotientSpanXSubCAlgEquiv x

end Polynomial

namespace Ideal

noncomputable section

open Polynomial

variable {R : Type*} [CommRing R]

theorem quotient_map_C_eq_zero {I : Ideal R} :
    ∀ a ∈ I, ((Quotient.mk (map (C : R →+* R[X]) I : Ideal R[X])).comp C) a = 0 := by
  intro a ha
  -- ⊢ ↑(RingHom.comp (Quotient.mk (map C I)) C) a = 0
  rw [RingHom.comp_apply, Quotient.eq_zero_iff_mem]
  -- ⊢ ↑C a ∈ map C I
  exact mem_map_of_mem _ ha
  -- 🎉 no goals
#align ideal.quotient_map_C_eq_zero Ideal.quotient_map_C_eq_zero

theorem eval₂_C_mk_eq_zero {I : Ideal R} :
    ∀ f ∈ (map (C : R →+* R[X]) I : Ideal R[X]), eval₂RingHom (C.comp (Quotient.mk I)) X f = 0 := by
  intro a ha
  -- ⊢ ↑(eval₂RingHom (RingHom.comp C (Quotient.mk I)) X) a = 0
  rw [← sum_monomial_eq a]
  -- ⊢ ↑(eval₂RingHom (RingHom.comp C (Quotient.mk I)) X) (sum a fun n a => ↑(monom …
  dsimp
  -- ⊢ eval₂ (RingHom.comp C (Quotient.mk I)) X (sum a fun n a => ↑(monomial n) a)  …
  rw [eval₂_sum]
  -- ⊢ (sum a fun n a => eval₂ (RingHom.comp C (Quotient.mk I)) X (↑(monomial n) a) …
  refine' Finset.sum_eq_zero fun n _ => _
  -- ⊢ (fun n a => eval₂ (RingHom.comp C (Quotient.mk I)) X (↑(monomial n) a)) n (c …
  dsimp
  -- ⊢ eval₂ (RingHom.comp C (Quotient.mk I)) X (↑(monomial n) (coeff a n)) = 0
  rw [eval₂_monomial (C.comp (Quotient.mk I)) X]
  -- ⊢ ↑(RingHom.comp C (Quotient.mk I)) (coeff a n) * X ^ n = 0
  refine' mul_eq_zero_of_left (Polynomial.ext fun m => _) (X ^ n)
  -- ⊢ coeff (↑(RingHom.comp C (Quotient.mk I)) (coeff a n)) m = coeff 0 m
  erw [coeff_C]
  -- ⊢ (if m = 0 then ↑(Quotient.mk I) (coeff a n) else 0) = coeff 0 m
  by_cases h : m = 0
  -- ⊢ (if m = 0 then ↑(Quotient.mk I) (coeff a n) else 0) = coeff 0 m
  · simpa [h] using Quotient.eq_zero_iff_mem.2 ((mem_map_C_iff.1 ha) n)
    -- 🎉 no goals
  · simp [h]
    -- 🎉 no goals
#align ideal.eval₂_C_mk_eq_zero Ideal.eval₂_C_mk_eq_zero

/-- If `I` is an ideal of `R`, then the ring polynomials over the quotient ring `I.quotient` is
isomorphic to the quotient of `R[X]` by the ideal `map C I`,
where `map C I` contains exactly the polynomials whose coefficients all lie in `I`. -/
def polynomialQuotientEquivQuotientPolynomial (I : Ideal R) :
    (R ⧸ I)[X] ≃+* R[X] ⧸ (map C I : Ideal R[X]) where
  toFun :=
    eval₂RingHom
      (Quotient.lift I ((Quotient.mk (map C I : Ideal R[X])).comp C) quotient_map_C_eq_zero)
      (Quotient.mk (map C I : Ideal R[X]) X)
  invFun :=
    Quotient.lift (map C I : Ideal R[X]) (eval₂RingHom (C.comp (Quotient.mk I)) X)
      eval₂_C_mk_eq_zero
  map_mul' f g := by simp only [coe_eval₂RingHom, eval₂_mul]
                     -- 🎉 no goals
  map_add' f g := by simp only [eval₂_add, coe_eval₂RingHom]
                     -- 🎉 no goals
    -- ⊢ ↑(Quotient.lift (map C I) (eval₂RingHom (RingHom.comp C (Quotient.mk I)) X)  …
  left_inv := by
    -- ⊢ ∀ (p q : (R ⧸ I)[X]), ↑(Quotient.lift (map C I) (eval₂RingHom (RingHom.comp  …
    intro f
      -- ⊢ ↑(Quotient.lift (map C I) (eval₂RingHom (RingHom.comp C (Quotient.mk I)) X)  …
    refine Polynomial.induction_on' f ?_ ?_
      -- ⊢ ↑(Quotient.lift (map C I) (eval₂RingHom (RingHom.comp C (Quotient.mk I)) X)  …
    · intro p q hp hq
      -- 🎉 no goals
      simp only [coe_eval₂RingHom] at hp hq
      -- ⊢ ↑(Quotient.lift (map C I) (eval₂RingHom (RingHom.comp C (Quotient.mk I)) X)  …
      simp only [coe_eval₂RingHom, hp, hq, RingHom.map_add]
    · rintro n ⟨x⟩
      simp only [← smul_X_eq_monomial, C_mul', Quotient.lift_mk, Submodule.Quotient.quot_mk_eq_mk,
        Quotient.mk_eq_mk, eval₂_X_pow, eval₂_smul, coe_eval₂RingHom, RingHom.map_pow, eval₂_C,
        RingHom.coe_comp, RingHom.map_mul, eval₂_X, Function.comp_apply]
    -- ⊢ ↑(eval₂RingHom (Quotient.lift I (RingHom.comp (Quotient.mk (map C I)) C) (_  …
  right_inv := by
    -- ⊢ ∀ (p q : R[X]), ↑(eval₂RingHom (Quotient.lift I (RingHom.comp (Quotient.mk ( …
    rintro ⟨f⟩
    refine Polynomial.induction_on' f ?_ ?_
      -- ⊢ ↑(eval₂RingHom (Quotient.lift I (RingHom.comp (Quotient.mk (map C I)) C) (_  …
    · -- Porting note: was `simp_intro p q hp hq`
      intros p q hp hq
      simp only [Submodule.Quotient.quot_mk_eq_mk, Quotient.mk_eq_mk, map_add, Quotient.lift_mk,
      -- 🎉 no goals
        coe_eval₂RingHom] at hp hq ⊢
      -- ⊢ ↑(eval₂RingHom (Quotient.lift I (RingHom.comp (Quotient.mk (map C I)) C) (_  …
      rw [hp, hq]
    · intro n a
      simp only [← smul_X_eq_monomial, ← C_mul' a (X ^ n), Quotient.lift_mk,
        Submodule.Quotient.quot_mk_eq_mk, Quotient.mk_eq_mk, eval₂_X_pow, eval₂_smul,
        coe_eval₂RingHom, RingHom.map_pow, eval₂_C, RingHom.coe_comp, RingHom.map_mul, eval₂_X,
        Function.comp_apply]
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
    I.polynomialQuotientEquivQuotientPolynomial (f.map <| Quotient.mk I) =
    Quotient.mk (map C I : Ideal R[X]) f := by
  apply (polynomialQuotientEquivQuotientPolynomial I).symm.injective
  -- ⊢ ↑(RingEquiv.symm (polynomialQuotientEquivQuotientPolynomial I)) (↑(polynomia …
  rw [RingEquiv.symm_apply_apply, polynomialQuotientEquivQuotientPolynomial_symm_mk]
  -- 🎉 no goals
#align ideal.polynomial_quotient_equiv_quotient_polynomial_map_mk Ideal.polynomialQuotientEquivQuotientPolynomial_map_mk

/-- If `P` is a prime ideal of `R`, then `R[x]/(P)` is an integral domain. -/
theorem isDomain_map_C_quotient {P : Ideal R} (_ : IsPrime P) :
    IsDomain (R[X] ⧸ (map (C : R →+* R[X]) P : Ideal R[X])) :=
  MulEquiv.isDomain (Polynomial (R ⧸ P)) (polynomialQuotientEquivQuotientPolynomial P).symm
#align ideal.is_domain_map_C_quotient Ideal.isDomain_map_C_quotient

/-- Given any ring `R` and an ideal `I` of `R[X]`, we get a map `R → R[x] → R[x]/I`.
  If we let `R` be the image of `R` in `R[x]/I` then we also have a map `R[x] → R'[x]`.
  In particular we can map `I` across this map, to get `I'` and a new map `R' → R'[x] → R'[x]/I`.
  This theorem shows `I'` will not contain any non-zero constant polynomials. -/
theorem eq_zero_of_polynomial_mem_map_range (I : Ideal R[X]) (x : ((Quotient.mk I).comp C).range)
    (hx : C x ∈ I.map (Polynomial.mapRingHom ((Quotient.mk I).comp C).rangeRestrict)) : x = 0 := by
  let i := ((Quotient.mk I).comp C).rangeRestrict
  -- ⊢ x = 0
  have hi' : RingHom.ker (Polynomial.mapRingHom i) ≤ I := by
    refine' fun f hf => polynomial_mem_ideal_of_coeff_mem_ideal I f fun n => _
    rw [mem_comap, ← Quotient.eq_zero_iff_mem, ← RingHom.comp_apply]
    rw [RingHom.mem_ker, coe_mapRingHom] at hf
    replace hf := congr_arg (fun f : Polynomial _ => f.coeff n) hf
    simp only [coeff_map, coeff_zero] at hf
    rwa [Subtype.ext_iff, RingHom.coe_rangeRestrict] at hf
  obtain ⟨x, hx'⟩ := x
  -- ⊢ { val := x, property := hx' } = 0
  obtain ⟨y, rfl⟩ := RingHom.mem_range.1 hx'
  -- ⊢ { val := ↑(RingHom.comp (Quotient.mk I) C) y, property := hx' } = 0
  refine' Subtype.eq _
  -- ⊢ ↑{ val := ↑(RingHom.comp (Quotient.mk I) C) y, property := hx' } = ↑0
  simp only [RingHom.comp_apply, Quotient.eq_zero_iff_mem, ZeroMemClass.coe_zero]
  -- ⊢ ↑C y ∈ I
  suffices C (i y) ∈ I.map (Polynomial.mapRingHom i) by
    obtain ⟨f, hf⟩ := mem_image_of_mem_map_of_surjective (Polynomial.mapRingHom i)
      (Polynomial.map_surjective _ (RingHom.rangeRestrict_surjective ((Quotient.mk I).comp C))) this
    refine' sub_add_cancel (C y) f ▸ I.add_mem (hi' _ : C y - f ∈ I) hf.1
    rw [RingHom.mem_ker, RingHom.map_sub, hf.2, sub_eq_zero, coe_mapRingHom, map_C]
  exact hx
  -- 🎉 no goals
#align ideal.eq_zero_of_polynomial_mem_map_range Ideal.eq_zero_of_polynomial_mem_map_range

end

end Ideal

namespace MvPolynomial

variable {R : Type*} {σ : Type*} [CommRing R] {r : R}

theorem quotient_map_C_eq_zero {I : Ideal R} {i : R} (hi : i ∈ I) :
    (Ideal.Quotient.mk (Ideal.map (C : R →+* MvPolynomial σ R) I :
      Ideal (MvPolynomial σ R))).comp C i = 0 := by
  simp only [Function.comp_apply, RingHom.coe_comp, Ideal.Quotient.eq_zero_iff_mem]
  -- ⊢ ↑C i ∈ Ideal.map C I
  exact Ideal.mem_map_of_mem _ hi
  -- 🎉 no goals
#align mv_polynomial.quotient_map_C_eq_zero MvPolynomial.quotient_map_C_eq_zero

theorem eval₂_C_mk_eq_zero {I : Ideal R} {a : MvPolynomial σ R}
    (ha : a ∈ (Ideal.map (C : R →+* MvPolynomial σ R) I : Ideal (MvPolynomial σ R))) :
    eval₂Hom (C.comp (Ideal.Quotient.mk I)) X a = 0 := by
  rw [as_sum a]
  -- ⊢ ↑(eval₂Hom (RingHom.comp C (Ideal.Quotient.mk I)) X) (Finset.sum (support a) …
  rw [coe_eval₂Hom, eval₂_sum]
  -- ⊢ (Finset.sum (support a) fun x => eval₂ (RingHom.comp C (Ideal.Quotient.mk I) …
  refine' Finset.sum_eq_zero fun n _ => _
  -- ⊢ eval₂ (RingHom.comp C (Ideal.Quotient.mk I)) X (↑(monomial n) (coeff n a)) = 0
  simp only [eval₂_monomial, Function.comp_apply, RingHom.coe_comp]
  -- ⊢ (↑C (↑(Ideal.Quotient.mk I) (coeff n a)) * Finsupp.prod n fun n e => X n ^ e …
  refine' mul_eq_zero_of_left _ _
  -- ⊢ ↑C (↑(Ideal.Quotient.mk I) (coeff n a)) = 0
  suffices coeff n a ∈ I by
    rw [← @Ideal.mk_ker R _ I, RingHom.mem_ker] at this
    simp only [this, C_0]
  exact mem_map_C_iff.1 ha n
  -- 🎉 no goals
#align mv_polynomial.eval₂_C_mk_eq_zero MvPolynomial.eval₂_C_mk_eq_zero

lemma quotientEquivQuotientMvPolynomial_rightInverse (I : Ideal R) :
    Function.RightInverse
      (eval₂ (Ideal.Quotient.lift I
        ((Ideal.Quotient.mk (Ideal.map C I : Ideal (MvPolynomial σ R))).comp C)
          fun i hi => quotient_map_C_eq_zero hi)
          fun i => Ideal.Quotient.mk (Ideal.map C I : Ideal (MvPolynomial σ R)) (X i))
      (Ideal.Quotient.lift (Ideal.map C I : Ideal (MvPolynomial σ R))
        (eval₂Hom (C.comp (Ideal.Quotient.mk I)) X) fun a ha => eval₂_C_mk_eq_zero ha) := by
  intro f
  -- ⊢ ↑(Ideal.Quotient.lift (Ideal.map C I) (eval₂Hom (RingHom.comp C (Ideal.Quoti …
  apply induction_on f
  · intro r
    -- ⊢ ↑(Ideal.Quotient.lift (Ideal.map C I) (eval₂Hom (RingHom.comp C (Ideal.Quoti …
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    -- ⊢ ↑(Ideal.Quotient.lift (Ideal.map C I) (eval₂Hom (RingHom.comp C (Ideal.Quoti …
    rw [eval₂_C, Ideal.Quotient.lift_mk, RingHom.comp_apply, Ideal.Quotient.lift_mk, eval₂Hom_C,
      RingHom.comp_apply]
  · intros p q hp hq
    -- ⊢ ↑(Ideal.Quotient.lift (Ideal.map C I) (eval₂Hom (RingHom.comp C (Ideal.Quoti …
    simp only [RingHom.map_add, MvPolynomial.coe_eval₂Hom, coe_eval₂Hom, MvPolynomial.eval₂_add]
      at hp hq ⊢
    rw [hp, hq]
    -- 🎉 no goals
  · intros p i hp
    -- ⊢ ↑(Ideal.Quotient.lift (Ideal.map C I) (eval₂Hom (RingHom.comp C (Ideal.Quoti …
    simp only [coe_eval₂Hom] at hp
    -- ⊢ ↑(Ideal.Quotient.lift (Ideal.map C I) (eval₂Hom (RingHom.comp C (Ideal.Quoti …
    simp only [hp, coe_eval₂Hom, Ideal.Quotient.lift_mk, eval₂_mul, RingHom.map_mul, eval₂_X]
    -- 🎉 no goals

lemma quotientEquivQuotientMvPolynomial_leftInverse (I : Ideal R) :
    Function.LeftInverse
      (eval₂ (Ideal.Quotient.lift I
        ((Ideal.Quotient.mk (Ideal.map C I : Ideal (MvPolynomial σ R))).comp C)
          fun i hi => quotient_map_C_eq_zero hi)
          fun i => Ideal.Quotient.mk (Ideal.map C I : Ideal (MvPolynomial σ R)) (X i))
      (Ideal.Quotient.lift (Ideal.map C I : Ideal (MvPolynomial σ R))
        (eval₂Hom (C.comp (Ideal.Quotient.mk I)) X) fun a ha => eval₂_C_mk_eq_zero ha) := by
  intro f
  -- ⊢ eval₂ (Ideal.Quotient.lift I (RingHom.comp (Ideal.Quotient.mk (Ideal.map C I …
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
  -- ⊢ eval₂ (Ideal.Quotient.lift I (RingHom.comp (Ideal.Quotient.mk (Ideal.map C I …
  apply induction_on f
  · intro r
    -- ⊢ eval₂ (Ideal.Quotient.lift I (RingHom.comp (Ideal.Quotient.mk (Ideal.map C I …
    rw [Ideal.Quotient.lift_mk, eval₂Hom_C, RingHom.comp_apply, eval₂_C, Ideal.Quotient.lift_mk,
      RingHom.comp_apply]
  · intros p q hp hq
    -- ⊢ eval₂ (Ideal.Quotient.lift I (RingHom.comp (Ideal.Quotient.mk (Ideal.map C I …
    erw [Ideal.Quotient.lift_mk] at hp hq ⊢
    -- ⊢ eval₂ (Ideal.Quotient.lift I (RingHom.comp (Ideal.Quotient.mk (Ideal.map C I …
    simp only [Submodule.Quotient.quot_mk_eq_mk, eval₂_add, RingHom.map_add, coe_eval₂Hom,
      Ideal.Quotient.lift_mk, Ideal.Quotient.mk_eq_mk] at hp hq ⊢
    rw [hp, hq]
    -- 🎉 no goals
  · intros p i hp
    -- ⊢ eval₂ (Ideal.Quotient.lift I (RingHom.comp (Ideal.Quotient.mk (Ideal.map C I …
    simp only [Submodule.Quotient.quot_mk_eq_mk, coe_eval₂Hom, Ideal.Quotient.lift_mk,
      Ideal.Quotient.mk_eq_mk, eval₂_mul, RingHom.map_mul, eval₂_X] at hp ⊢
    simp only [hp]
    -- 🎉 no goals

-- Porting note: this definition was split to avoid timeouts.
/-- If `I` is an ideal of `R`, then the ring `MvPolynomial σ I.quotient` is isomorphic as an
`R`-algebra to the quotient of `MvPolynomial σ R` by the ideal generated by `I`. -/
noncomputable def quotientEquivQuotientMvPolynomial (I : Ideal R) :
    MvPolynomial σ (R ⧸ I) ≃ₐ[R] MvPolynomial σ R ⧸ (Ideal.map C I : Ideal (MvPolynomial σ R)) :=
  let e : MvPolynomial σ (R ⧸ I) →ₐ[R]
      MvPolynomial σ R ⧸ (Ideal.map C I : Ideal (MvPolynomial σ R)) :=
    { eval₂Hom
      (Ideal.Quotient.lift I ((Ideal.Quotient.mk (Ideal.map C I : Ideal (MvPolynomial σ R))).comp C)
        fun _ hi => quotient_map_C_eq_zero hi)
      fun i => Ideal.Quotient.mk (Ideal.map C I : Ideal (MvPolynomial σ R)) (X i) with
      commutes' := fun r => eval₂Hom_C _ _ (Ideal.Quotient.mk I r) }
  { e with
    invFun := Ideal.Quotient.lift (Ideal.map C I : Ideal (MvPolynomial σ R))
      (eval₂Hom (C.comp (Ideal.Quotient.mk I)) X) fun _ ha => eval₂_C_mk_eq_zero ha
    left_inv := quotientEquivQuotientMvPolynomial_rightInverse I
    right_inv := quotientEquivQuotientMvPolynomial_leftInverse I }
#align mv_polynomial.quotient_equiv_quotient_mv_polynomial MvPolynomial.quotientEquivQuotientMvPolynomial

end MvPolynomial
