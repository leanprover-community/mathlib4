/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Finsupp.Fin
import Mathlib.Logic.Equiv.Fin

#align_import data.mv_polynomial.equiv from "leanprover-community/mathlib"@"2f5b500a507264de86d666a5f87ddb976e2d8de4"

/-!
# Equivalences between polynomial rings

This file establishes a number of equivalences between polynomial rings,
based on equivalences between the underlying types.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[CommSemiring R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `MvPolynomial σ R` which mathematicians might call `X^s`

+ `a : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : MvPolynomial σ R`

## Tags

equivalence, isomorphism, morphism, ring hom, hom

-/


noncomputable section

open Polynomial Set Function Finsupp AddMonoidAlgebra

universe u v w x

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

namespace MvPolynomial

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

section Equiv

variable (R) [CommSemiring R]

/-- The ring isomorphism between multivariable polynomials in a single variable and
polynomials over the ground ring.
-/
@[simps]
def pUnitAlgEquiv : MvPolynomial PUnit R ≃ₐ[R] R[X] where
  toFun := eval₂ Polynomial.C fun _ => Polynomial.X
  invFun := Polynomial.eval₂ MvPolynomial.C (X PUnit.unit)
  left_inv := by
    let f : R[X] →+* MvPolynomial PUnit R := Polynomial.eval₂RingHom MvPolynomial.C (X PUnit.unit)
    let g : MvPolynomial PUnit R →+* R[X] := eval₂Hom Polynomial.C fun _ => Polynomial.X
    show ∀ p, f.comp g p = p
    apply is_id
    · ext a
      dsimp [f, g]
      rw [eval₂_C, Polynomial.eval₂_C]
    · rintro ⟨⟩
      dsimp [f, g]
      rw [eval₂_X, Polynomial.eval₂_X]
  right_inv p :=
    Polynomial.induction_on p (fun a => by rw [Polynomial.eval₂_C, MvPolynomial.eval₂_C])
    (fun p q hp hq => by rw [Polynomial.eval₂_add, MvPolynomial.eval₂_add, hp, hq]) fun p n _ => by
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
        eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
  map_mul' _ _ := eval₂_mul _ _
  map_add' _ _ := eval₂_add _ _
  commutes' _ := eval₂_C _ _ _
#align mv_polynomial.punit_alg_equiv MvPolynomial.pUnitAlgEquiv

section Map

variable {R} (σ)

/-- If `e : A ≃+* B` is an isomorphism of rings, then so is `map e`. -/
@[simps apply]
def mapEquiv [CommSemiring S₁] [CommSemiring S₂] (e : S₁ ≃+* S₂) :
    MvPolynomial σ S₁ ≃+* MvPolynomial σ S₂ :=
  { map (e : S₁ →+* S₂) with
    toFun := map (e : S₁ →+* S₂)
    invFun := map (e.symm : S₂ →+* S₁)
    left_inv := map_leftInverse e.left_inv
    right_inv := map_rightInverse e.right_inv }
#align mv_polynomial.map_equiv MvPolynomial.mapEquiv

@[simp]
theorem mapEquiv_refl : mapEquiv σ (RingEquiv.refl R) = RingEquiv.refl _ :=
  RingEquiv.ext map_id
#align mv_polynomial.map_equiv_refl MvPolynomial.mapEquiv_refl

@[simp]
theorem mapEquiv_symm [CommSemiring S₁] [CommSemiring S₂] (e : S₁ ≃+* S₂) :
    (mapEquiv σ e).symm = mapEquiv σ e.symm :=
  rfl
#align mv_polynomial.map_equiv_symm MvPolynomial.mapEquiv_symm

@[simp]
theorem mapEquiv_trans [CommSemiring S₁] [CommSemiring S₂] [CommSemiring S₃] (e : S₁ ≃+* S₂)
    (f : S₂ ≃+* S₃) : (mapEquiv σ e).trans (mapEquiv σ f) = mapEquiv σ (e.trans f) :=
  RingEquiv.ext fun p => by
    simp only [RingEquiv.coe_trans, comp_apply, mapEquiv_apply, RingEquiv.coe_ringHom_trans,
      map_map]
#align mv_polynomial.map_equiv_trans MvPolynomial.mapEquiv_trans

variable {A₁ A₂ A₃ : Type*} [CommSemiring A₁] [CommSemiring A₂] [CommSemiring A₃]
variable [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]

/-- If `e : A ≃ₐ[R] B` is an isomorphism of `R`-algebras, then so is `map e`. -/
@[simps apply]
def mapAlgEquiv (e : A₁ ≃ₐ[R] A₂) : MvPolynomial σ A₁ ≃ₐ[R] MvPolynomial σ A₂ :=
  { mapAlgHom (e : A₁ →ₐ[R] A₂), mapEquiv σ (e : A₁ ≃+* A₂) with toFun := map (e : A₁ →+* A₂) }
#align mv_polynomial.map_alg_equiv MvPolynomial.mapAlgEquiv

@[simp]
theorem mapAlgEquiv_refl : mapAlgEquiv σ (AlgEquiv.refl : A₁ ≃ₐ[R] A₁) = AlgEquiv.refl :=
  AlgEquiv.ext map_id
#align mv_polynomial.map_alg_equiv_refl MvPolynomial.mapAlgEquiv_refl

@[simp]
theorem mapAlgEquiv_symm (e : A₁ ≃ₐ[R] A₂) : (mapAlgEquiv σ e).symm = mapAlgEquiv σ e.symm :=
  rfl
#align mv_polynomial.map_alg_equiv_symm MvPolynomial.mapAlgEquiv_symm

@[simp]
theorem mapAlgEquiv_trans (e : A₁ ≃ₐ[R] A₂) (f : A₂ ≃ₐ[R] A₃) :
    (mapAlgEquiv σ e).trans (mapAlgEquiv σ f) = mapAlgEquiv σ (e.trans f) := by
  ext
  simp only [AlgEquiv.trans_apply, mapAlgEquiv_apply, map_map]
  rfl
#align mv_polynomial.map_alg_equiv_trans MvPolynomial.mapAlgEquiv_trans

end Map

section

variable (S₁ S₂ S₃)

/-- The function from multivariable polynomials in a sum of two types,
to multivariable polynomials in one of the types,
with coefficients in multivariable polynomials in the other type.

See `sumRingEquiv` for the ring isomorphism.
-/
def sumToIter : MvPolynomial (Sum S₁ S₂) R →+* MvPolynomial S₁ (MvPolynomial S₂ R) :=
  eval₂Hom (C.comp C) fun bc => Sum.recOn bc X (C ∘ X)
#align mv_polynomial.sum_to_iter MvPolynomial.sumToIter

@[simp]
theorem sumToIter_C (a : R) : sumToIter R S₁ S₂ (C a) = C (C a) :=
  eval₂_C _ _ a
set_option linter.uppercaseLean3 false in
#align mv_polynomial.sum_to_iter_C MvPolynomial.sumToIter_C

@[simp]
theorem sumToIter_Xl (b : S₁) : sumToIter R S₁ S₂ (X (Sum.inl b)) = X b :=
  eval₂_X _ _ (Sum.inl b)
set_option linter.uppercaseLean3 false in
#align mv_polynomial.sum_to_iter_Xl MvPolynomial.sumToIter_Xl

@[simp]
theorem sumToIter_Xr (c : S₂) : sumToIter R S₁ S₂ (X (Sum.inr c)) = C (X c) :=
  eval₂_X _ _ (Sum.inr c)
set_option linter.uppercaseLean3 false in
#align mv_polynomial.sum_to_iter_Xr MvPolynomial.sumToIter_Xr

/-- The function from multivariable polynomials in one type,
with coefficients in multivariable polynomials in another type,
to multivariable polynomials in the sum of the two types.

See `sumRingEquiv` for the ring isomorphism.
-/
def iterToSum : MvPolynomial S₁ (MvPolynomial S₂ R) →+* MvPolynomial (Sum S₁ S₂) R :=
  eval₂Hom (eval₂Hom C (X ∘ Sum.inr)) (X ∘ Sum.inl)
#align mv_polynomial.iter_to_sum MvPolynomial.iterToSum

@[simp]
theorem iterToSum_C_C (a : R) : iterToSum R S₁ S₂ (C (C a)) = C a :=
  Eq.trans (eval₂_C _ _ (C a)) (eval₂_C _ _ _)
set_option linter.uppercaseLean3 false in
#align mv_polynomial.iter_to_sum_C_C MvPolynomial.iterToSum_C_C

@[simp]
theorem iterToSum_X (b : S₁) : iterToSum R S₁ S₂ (X b) = X (Sum.inl b) :=
  eval₂_X _ _ _
set_option linter.uppercaseLean3 false in
#align mv_polynomial.iter_to_sum_X MvPolynomial.iterToSum_X

@[simp]
theorem iterToSum_C_X (c : S₂) : iterToSum R S₁ S₂ (C (X c)) = X (Sum.inr c) :=
  Eq.trans (eval₂_C _ _ (X c)) (eval₂_X _ _ _)
set_option linter.uppercaseLean3 false in
#align mv_polynomial.iter_to_sum_C_X MvPolynomial.iterToSum_C_X

variable (σ)

/-- The algebra isomorphism between multivariable polynomials in no variables
and the ground ring. -/
@[simps!]
def isEmptyAlgEquiv [he : IsEmpty σ] : MvPolynomial σ R ≃ₐ[R] R :=
  AlgEquiv.ofAlgHom (aeval (IsEmpty.elim he)) (Algebra.ofId _ _)
    (by ext)
    (by
      ext i m
      exact IsEmpty.elim' he i)
#align mv_polynomial.is_empty_alg_equiv MvPolynomial.isEmptyAlgEquiv

/-- The ring isomorphism between multivariable polynomials in no variables
and the ground ring. -/
@[simps!]
def isEmptyRingEquiv [IsEmpty σ] : MvPolynomial σ R ≃+* R :=
  (isEmptyAlgEquiv R σ).toRingEquiv
#align mv_polynomial.is_empty_ring_equiv MvPolynomial.isEmptyRingEquiv

variable {σ}

/-- A helper function for `sumRingEquiv`. -/
@[simps]
def mvPolynomialEquivMvPolynomial [CommSemiring S₃] (f : MvPolynomial S₁ R →+* MvPolynomial S₂ S₃)
    (g : MvPolynomial S₂ S₃ →+* MvPolynomial S₁ R) (hfgC : (f.comp g).comp C = C)
    (hfgX : ∀ n, f (g (X n)) = X n) (hgfC : (g.comp f).comp C = C) (hgfX : ∀ n, g (f (X n)) = X n) :
    MvPolynomial S₁ R ≃+* MvPolynomial S₂ S₃ where
  toFun := f
  invFun := g
  left_inv := is_id (RingHom.comp _ _) hgfC hgfX
  right_inv := is_id (RingHom.comp _ _) hfgC hfgX
  map_mul' := f.map_mul
  map_add' := f.map_add
#align mv_polynomial.mv_polynomial_equiv_mv_polynomial MvPolynomial.mvPolynomialEquivMvPolynomial

/-- The ring isomorphism between multivariable polynomials in a sum of two types,
and multivariable polynomials in one of the types,
with coefficients in multivariable polynomials in the other type.
-/
def sumRingEquiv : MvPolynomial (Sum S₁ S₂) R ≃+* MvPolynomial S₁ (MvPolynomial S₂ R) := by
  apply mvPolynomialEquivMvPolynomial R (Sum S₁ S₂) _ _ (sumToIter R S₁ S₂) (iterToSum R S₁ S₂)
  · refine RingHom.ext (hom_eq_hom _ _ ?hC ?hX)
    case hC => ext1; simp only [RingHom.comp_apply, iterToSum_C_C, sumToIter_C]
    case hX => intro; simp only [RingHom.comp_apply, iterToSum_C_X, sumToIter_Xr]
  · simp [iterToSum_X, sumToIter_Xl]
  · ext1; simp only [RingHom.comp_apply, sumToIter_C, iterToSum_C_C]
  · rintro ⟨⟩ <;> simp only [sumToIter_Xl, iterToSum_X, sumToIter_Xr, iterToSum_C_X]
#align mv_polynomial.sum_ring_equiv MvPolynomial.sumRingEquiv

/-- The algebra isomorphism between multivariable polynomials in a sum of two types,
and multivariable polynomials in one of the types,
with coefficients in multivariable polynomials in the other type.
-/
@[simps!]
def sumAlgEquiv : MvPolynomial (Sum S₁ S₂) R ≃ₐ[R] MvPolynomial S₁ (MvPolynomial S₂ R) :=
  { sumRingEquiv R S₁ S₂ with
    commutes' := by
      intro r
      have A : algebraMap R (MvPolynomial S₁ (MvPolynomial S₂ R)) r = (C (C r) : _) := rfl
      have B : algebraMap R (MvPolynomial (Sum S₁ S₂) R) r = C r := rfl
      simp only [sumRingEquiv, mvPolynomialEquivMvPolynomial, Equiv.toFun_as_coe,
        Equiv.coe_fn_mk, B, sumToIter_C, A] }
#align mv_polynomial.sum_alg_equiv MvPolynomial.sumAlgEquiv

section

-- this speeds up typeclass search in the lemma below
attribute [local instance] IsScalarTower.right

/-- The algebra isomorphism between multivariable polynomials in `Option S₁` and
polynomials with coefficients in `MvPolynomial S₁ R`.
-/
@[simps!]
def optionEquivLeft : MvPolynomial (Option S₁) R ≃ₐ[R] Polynomial (MvPolynomial S₁ R) :=
  AlgEquiv.ofAlgHom (MvPolynomial.aeval fun o => o.elim Polynomial.X fun s => Polynomial.C (X s))
    (Polynomial.aevalTower (MvPolynomial.rename some) (X none))
    (by ext : 2 <;> simp) (by ext i : 2; cases i <;> simp)
#align mv_polynomial.option_equiv_left MvPolynomial.optionEquivLeft

end

/-- The algebra isomorphism between multivariable polynomials in `Option S₁` and
multivariable polynomials with coefficients in polynomials.
-/
def optionEquivRight : MvPolynomial (Option S₁) R ≃ₐ[R] MvPolynomial S₁ R[X] :=
  AlgEquiv.ofAlgHom (MvPolynomial.aeval fun o => o.elim (C Polynomial.X) X)
    (MvPolynomial.aevalTower (Polynomial.aeval (X none)) fun i => X (Option.some i))
    (by
      ext : 2 <;>
        simp only [MvPolynomial.algebraMap_eq, Option.elim, AlgHom.coe_comp, AlgHom.id_comp,
          IsScalarTower.coe_toAlgHom', comp_apply, aevalTower_C, Polynomial.aeval_X, aeval_X,
          Option.elim', aevalTower_X, AlgHom.coe_id, id, eq_self_iff_true, imp_true_iff])
    (by
      ext ⟨i⟩ : 2 <;>
        simp only [Option.elim, AlgHom.coe_comp, comp_apply, aeval_X, aevalTower_C,
          Polynomial.aeval_X, AlgHom.coe_id, id, aevalTower_X])
#align mv_polynomial.option_equiv_right MvPolynomial.optionEquivRight

variable (n : ℕ)

/-- The algebra isomorphism between multivariable polynomials in `Fin (n + 1)` and
polynomials over multivariable polynomials in `Fin n`.
-/
def finSuccEquiv : MvPolynomial (Fin (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R) :=
  (renameEquiv R (_root_.finSuccEquiv n)).trans (optionEquivLeft R (Fin n))
#align mv_polynomial.fin_succ_equiv MvPolynomial.finSuccEquiv

theorem finSuccEquiv_eq :
    (finSuccEquiv R n : MvPolynomial (Fin (n + 1)) R →+* Polynomial (MvPolynomial (Fin n) R)) =
      eval₂Hom (Polynomial.C.comp (C : R →+* MvPolynomial (Fin n) R)) fun i : Fin (n + 1) =>
        Fin.cases Polynomial.X (fun k => Polynomial.C (X k)) i := by
  ext i : 2
  · simp only [finSuccEquiv, optionEquivLeft_apply, aeval_C, AlgEquiv.coe_trans, RingHom.coe_coe,
      coe_eval₂Hom, comp_apply, renameEquiv_apply, eval₂_C, RingHom.coe_comp, rename_C]
    rfl
  · refine Fin.cases ?_ ?_ i <;> simp [finSuccEquiv]
#align mv_polynomial.fin_succ_equiv_eq MvPolynomial.finSuccEquiv_eq

@[simp]
theorem finSuccEquiv_apply (p : MvPolynomial (Fin (n + 1)) R) :
    finSuccEquiv R n p =
      eval₂Hom (Polynomial.C.comp (C : R →+* MvPolynomial (Fin n) R))
        (fun i : Fin (n + 1) => Fin.cases Polynomial.X (fun k => Polynomial.C (X k)) i) p := by
  rw [← finSuccEquiv_eq, RingHom.coe_coe]
#align mv_polynomial.fin_succ_equiv_apply MvPolynomial.finSuccEquiv_apply

theorem finSuccEquiv_comp_C_eq_C {R : Type u} [CommSemiring R] (n : ℕ) :
    (↑(MvPolynomial.finSuccEquiv R n).symm : Polynomial (MvPolynomial (Fin n) R) →+* _).comp
        (Polynomial.C.comp MvPolynomial.C) =
      (MvPolynomial.C : R →+* MvPolynomial (Fin n.succ) R) := by
  refine RingHom.ext fun x => ?_
  rw [RingHom.comp_apply]
  refine
    (MvPolynomial.finSuccEquiv R n).injective
      (Trans.trans ((MvPolynomial.finSuccEquiv R n).apply_symm_apply _) ?_)
  simp only [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C]
set_option linter.uppercaseLean3 false in
#align mv_polynomial.fin_succ_equiv_comp_C_eq_C MvPolynomial.finSuccEquiv_comp_C_eq_C

variable {n} {R}

theorem finSuccEquiv_X_zero : finSuccEquiv R n (X 0) = Polynomial.X := by simp
set_option linter.uppercaseLean3 false in
#align mv_polynomial.fin_succ_equiv_X_zero MvPolynomial.finSuccEquiv_X_zero

theorem finSuccEquiv_X_succ {j : Fin n} : finSuccEquiv R n (X j.succ) = Polynomial.C (X j) := by
  simp
set_option linter.uppercaseLean3 false in
#align mv_polynomial.fin_succ_equiv_X_succ MvPolynomial.finSuccEquiv_X_succ

/-- The coefficient of `m` in the `i`-th coefficient of `finSuccEquiv R n f` equals the
    coefficient of `Finsupp.cons i m` in `f`. -/
theorem finSuccEquiv_coeff_coeff (m : Fin n →₀ ℕ) (f : MvPolynomial (Fin (n + 1)) R) (i : ℕ) :
    coeff m (Polynomial.coeff (finSuccEquiv R n f) i) = coeff (m.cons i) f := by
  induction' f using MvPolynomial.induction_on' with j r p q hp hq generalizing i m
  swap
  · simp only [(finSuccEquiv R n).map_add, Polynomial.coeff_add, coeff_add, hp, hq]
  simp only [finSuccEquiv_apply, coe_eval₂Hom, eval₂_monomial, RingHom.coe_comp, prod_pow,
    Polynomial.coeff_C_mul, coeff_C_mul, coeff_monomial, Fin.prod_univ_succ, Fin.cases_zero,
    Fin.cases_succ, ← map_prod, ← RingHom.map_pow, Function.comp_apply]
  rw [← mul_boole, mul_comm (Polynomial.X ^ j 0), Polynomial.coeff_C_mul_X_pow]; congr 1
  obtain rfl | hjmi := eq_or_ne j (m.cons i)
  · simpa only [cons_zero, cons_succ, if_pos rfl, monomial_eq, C_1, one_mul, prod_pow] using
      coeff_monomial m m (1 : R)
  · simp only [hjmi, if_false]
    obtain hij | rfl := ne_or_eq i (j 0)
    · simp only [hij, if_false, coeff_zero]
    simp only [eq_self_iff_true, if_true]
    have hmj : m ≠ j.tail := by
      rintro rfl
      rw [cons_tail] at hjmi
      contradiction
    simpa only [monomial_eq, C_1, one_mul, prod_pow, Finsupp.tail_apply, if_neg hmj.symm] using
      coeff_monomial m j.tail (1 : R)
#align mv_polynomial.fin_succ_equiv_coeff_coeff MvPolynomial.finSuccEquiv_coeff_coeff

theorem eval_eq_eval_mv_eval' (s : Fin n → R) (y : R) (f : MvPolynomial (Fin (n + 1)) R) :
    eval (Fin.cons y s : Fin (n + 1) → R) f =
      Polynomial.eval y (Polynomial.map (eval s) (finSuccEquiv R n f)) := by
  -- turn this into a def `Polynomial.mapAlgHom`
  let φ : (MvPolynomial (Fin n) R)[X] →ₐ[R] R[X] :=
    { Polynomial.mapRingHom (eval s) with
      commutes' := fun r => by
        convert Polynomial.map_C (eval s)
        exact (eval_C _).symm }
  show
    aeval (Fin.cons y s : Fin (n + 1) → R) f =
      (Polynomial.aeval y).comp (φ.comp (finSuccEquiv R n).toAlgHom) f
  congr 2
  apply MvPolynomial.algHom_ext
  rw [Fin.forall_fin_succ]
  simp only [φ, aeval_X, Fin.cons_zero, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp,
    Polynomial.coe_aeval_eq_eval, Polynomial.map_C, AlgHom.coe_mk, RingHom.toFun_eq_coe,
    Polynomial.coe_mapRingHom, comp_apply, finSuccEquiv_apply, eval₂Hom_X',
    Fin.cases_zero, Polynomial.map_X, Polynomial.eval_X, Fin.cons_succ,
    Fin.cases_succ, eval_X, Polynomial.eval_C,
    RingHom.coe_mk, MonoidHom.coe_coe, AlgHom.coe_coe, implies_true, and_self,
    RingHom.toMonoidHom_eq_coe]
#align mv_polynomial.eval_eq_eval_mv_eval' MvPolynomial.eval_eq_eval_mv_eval'

theorem coeff_eval_eq_eval_coeff (s' : Fin n → R) (f : Polynomial (MvPolynomial (Fin n) R))
    (i : ℕ) : Polynomial.coeff (Polynomial.map (eval s') f) i = eval s' (Polynomial.coeff f i) := by
  simp only [Polynomial.coeff_map]
#align mv_polynomial.coeff_eval_eq_eval_coeff MvPolynomial.coeff_eval_eq_eval_coeff

theorem support_coeff_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {i : ℕ} {m : Fin n →₀ ℕ} :
    m ∈ (Polynomial.coeff ((finSuccEquiv R n) f) i).support ↔ Finsupp.cons i m ∈ f.support := by
  apply Iff.intro
  · intro h
    simpa [← finSuccEquiv_coeff_coeff] using h
  · intro h
    simpa [mem_support_iff, ← finSuccEquiv_coeff_coeff m f i] using h
#align mv_polynomial.support_coeff_fin_succ_equiv MvPolynomial.support_coeff_finSuccEquiv

/--
The `totalDegree` of a multivariable polynomial `p` is at least `i` more than the `totalDegree` of
the `i`th coefficient of `finSuccEquiv` applied to `p`, if this is nonzero.
-/
lemma totalDegree_coeff_finSuccEquiv_add_le (f : MvPolynomial (Fin (n + 1)) R) (i : ℕ)
    (hi : (finSuccEquiv R n f).coeff i ≠ 0) :
    totalDegree ((finSuccEquiv R n f).coeff i) + i ≤ totalDegree f := by
  have hf'_sup : ((finSuccEquiv R n f).coeff i).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, ne_eq, support_eq_empty]
    exact hi
  -- Let σ be a monomial index of ((finSuccEquiv R n p).coeff i) of maximal total degree
  have ⟨σ, hσ1, hσ2⟩ := Finset.exists_mem_eq_sup (support _) hf'_sup
                          (fun s => Finsupp.sum s fun _ e => e)
  -- Then cons i σ is a monomial index of p with total degree equal to the desired bound
  let σ' : Fin (n+1) →₀ ℕ := cons i σ
  convert le_totalDegree (s := σ') _
  · rw [totalDegree, hσ2, sum_cons, add_comm]
  · rw [← support_coeff_finSuccEquiv]
    exact hσ1

theorem finSuccEquiv_support (f : MvPolynomial (Fin (n + 1)) R) :
    (finSuccEquiv R n f).support = Finset.image (fun m : Fin (n + 1) →₀ ℕ => m 0) f.support := by
  ext i
  rw [Polynomial.mem_support_iff, Finset.mem_image, Finsupp.ne_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨cons i m, ?_, cons_zero _ _⟩
    rw [← support_coeff_finSuccEquiv]
    simpa using hm
  · rintro ⟨m, h, rfl⟩
    refine ⟨tail m, ?_⟩
    rwa [← coeff, zero_apply, ← mem_support_iff, support_coeff_finSuccEquiv, cons_tail]
#align mv_polynomial.fin_succ_equiv_support MvPolynomial.finSuccEquiv_support

theorem finSuccEquiv_support' {f : MvPolynomial (Fin (n + 1)) R} {i : ℕ} :
    Finset.image (Finsupp.cons i) (Polynomial.coeff ((finSuccEquiv R n) f) i).support =
      f.support.filter fun m => m 0 = i := by
  ext m
  rw [Finset.mem_filter, Finset.mem_image, mem_support_iff]
  conv_lhs =>
    congr
    ext
    rw [mem_support_iff, finSuccEquiv_coeff_coeff, Ne]
  constructor
  · rintro ⟨m', ⟨h, hm'⟩⟩
    simp only [← hm']
    exact ⟨h, by rw [cons_zero]⟩
  · intro h
    use tail m
    rw [← h.2, cons_tail]
    simp [h.1]
#align mv_polynomial.fin_succ_equiv_support' MvPolynomial.finSuccEquiv_support'

-- TODO: generalize `finSuccEquiv R n` to an arbitrary ZeroHom
theorem support_finSuccEquiv_nonempty {f : MvPolynomial (Fin (n + 1)) R} (h : f ≠ 0) :
    (finSuccEquiv R n f).support.Nonempty := by
  rwa [Polynomial.support_nonempty, AddEquivClass.map_ne_zero_iff]
#align mv_polynomial.support_fin_succ_equiv_nonempty MvPolynomial.support_finSuccEquiv_nonempty

theorem degree_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} (h : f ≠ 0) :
    (finSuccEquiv R n f).degree = degreeOf 0 f := by
  -- TODO: these should be lemmas
  have h₀ : ∀ {α β : Type _} (f : α → β), (fun x => x) ∘ f = f := fun f => rfl
  have h₁ : ∀ {α β : Type _} (f : α → β), f ∘ (fun x => x) = f := fun f => rfl
  have h₂ : WithBot.some = Nat.cast := rfl

  have h' : ((finSuccEquiv R n f).support.sup fun x => x) = degreeOf 0 f := by
    rw [degreeOf_eq_sup, finSuccEquiv_support f, Finset.sup_image, h₀]
  rw [Polynomial.degree, ← h', ← h₂, Finset.coe_sup_of_nonempty (support_finSuccEquiv_nonempty h),
    Finset.max_eq_sup_coe, h₁]
#align mv_polynomial.degree_fin_succ_equiv MvPolynomial.degree_finSuccEquiv

theorem natDegree_finSuccEquiv (f : MvPolynomial (Fin (n + 1)) R) :
    (finSuccEquiv R n f).natDegree = degreeOf 0 f := by
  by_cases c : f = 0
  · rw [c, (finSuccEquiv R n).map_zero, Polynomial.natDegree_zero, degreeOf_zero]
  · rw [Polynomial.natDegree, degree_finSuccEquiv (by simpa only [Ne] )]
    erw [WithBot.unbot'_coe]
    simp
#align mv_polynomial.nat_degree_fin_succ_equiv MvPolynomial.natDegree_finSuccEquiv

theorem degreeOf_coeff_finSuccEquiv (p : MvPolynomial (Fin (n + 1)) R) (j : Fin n) (i : ℕ) :
    degreeOf j (Polynomial.coeff (finSuccEquiv R n p) i) ≤ degreeOf j.succ p := by
  rw [degreeOf_eq_sup, degreeOf_eq_sup, Finset.sup_le_iff]
  intro m hm
  rw [← Finsupp.cons_succ j i m]
  exact Finset.le_sup
    (f := fun (g : Fin (Nat.succ n) →₀ ℕ) => g (Fin.succ j))
    (support_coeff_finSuccEquiv.1 hm)
#align mv_polynomial.degree_of_coeff_fin_succ_equiv MvPolynomial.degreeOf_coeff_finSuccEquiv

/-- Consider a multivariate polynomial `φ` whose variables are indexed by `Option σ`,
and suppose that `σ ≃ Fin n`.
Then one may view `φ` as a polynomial over `MvPolynomial (Fin n) R`, by

1. renaming the variables via `Option σ ≃ Fin (n+1)`, and then singling out the `0`-th variable
    via `MvPolynomial.finSuccEquiv`;
2. first viewing it as polynomial over `MvPolynomial σ R` via `MvPolynomial.optionEquivLeft`,
    and then renaming the variables.

This lemma shows that both constructions are the same. -/
lemma finSuccEquiv_rename_finSuccEquiv (e : σ ≃ Fin n) (φ : MvPolynomial (Option σ) R) :
    ((finSuccEquiv R n) ((rename ((Equiv.optionCongr e).trans (_root_.finSuccEquiv n).symm)) φ)) =
      Polynomial.map (rename e).toRingHom (optionEquivLeft R σ φ) := by
  suffices (finSuccEquiv R n).toRingEquiv.toRingHom.comp (rename ((Equiv.optionCongr e).trans
        (_root_.finSuccEquiv n).symm)).toRingHom =
      (Polynomial.mapRingHom (rename e).toRingHom).comp (optionEquivLeft R σ) by
    exact DFunLike.congr_fun this φ
  apply ringHom_ext
  · simp [Polynomial.algebraMap_apply, algebraMap_eq]
  · rintro (i|i) <;> simp

end

end Equiv

end MvPolynomial
