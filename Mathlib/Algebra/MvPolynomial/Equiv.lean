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

+ `f : MvPolynomial σ R`

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

@[simp]
theorem mapEquiv_refl : mapEquiv σ (RingEquiv.refl R) = RingEquiv.refl _ :=
  RingEquiv.ext map_id

@[simp]
theorem mapEquiv_symm [CommSemiring S₁] [CommSemiring S₂] (e : S₁ ≃+* S₂) :
    (mapEquiv σ e).symm = mapEquiv σ e.symm :=
  rfl

@[simp]
theorem mapEquiv_trans [CommSemiring S₁] [CommSemiring S₂] [CommSemiring S₃] (e : S₁ ≃+* S₂)
    (f : S₂ ≃+* S₃) : (mapEquiv σ e).trans (mapEquiv σ f) = mapEquiv σ (e.trans f) :=
  RingEquiv.ext fun p => by
    simp only [RingEquiv.coe_trans, comp_apply, mapEquiv_apply, RingEquiv.coe_ringHom_trans,
      map_map]

variable {A₁ A₂ A₃ : Type*} [CommSemiring A₁] [CommSemiring A₂] [CommSemiring A₃]
variable [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]

/-- If `e : A ≃ₐ[R] B` is an isomorphism of `R`-algebras, then so is `map e`. -/
@[simps apply]
def mapAlgEquiv (e : A₁ ≃ₐ[R] A₂) : MvPolynomial σ A₁ ≃ₐ[R] MvPolynomial σ A₂ :=
  { mapAlgHom (e : A₁ →ₐ[R] A₂), mapEquiv σ (e : A₁ ≃+* A₂) with toFun := map (e : A₁ →+* A₂) }

@[simp]
theorem mapAlgEquiv_refl : mapAlgEquiv σ (AlgEquiv.refl : A₁ ≃ₐ[R] A₁) = AlgEquiv.refl :=
  AlgEquiv.ext map_id

@[simp]
theorem mapAlgEquiv_symm (e : A₁ ≃ₐ[R] A₂) : (mapAlgEquiv σ e).symm = mapAlgEquiv σ e.symm :=
  rfl

@[simp]
theorem mapAlgEquiv_trans (e : A₁ ≃ₐ[R] A₂) (f : A₂ ≃ₐ[R] A₃) :
    (mapAlgEquiv σ e).trans (mapAlgEquiv σ f) = mapAlgEquiv σ (e.trans f) := by
  ext
  simp only [AlgEquiv.trans_apply, mapAlgEquiv_apply, map_map]
  rfl

end Map

section

variable (S₁ S₂ S₃)

/-- The function from multivariable polynomials in a sum of two types,
to multivariable polynomials in one of the types,
with coefficients in multivariable polynomials in the other type.

See `sumRingEquiv` for the ring isomorphism.
-/
def sumToIter : MvPolynomial (S₁ ⊕ S₂) R →+* MvPolynomial S₁ (MvPolynomial S₂ R) :=
  eval₂Hom (C.comp C) fun bc => Sum.recOn bc X (C ∘ X)

@[simp]
theorem sumToIter_C (a : R) : sumToIter R S₁ S₂ (C a) = C (C a) :=
  eval₂_C _ _ a

@[simp]
theorem sumToIter_Xl (b : S₁) : sumToIter R S₁ S₂ (X (Sum.inl b)) = X b :=
  eval₂_X _ _ (Sum.inl b)

@[simp]
theorem sumToIter_Xr (c : S₂) : sumToIter R S₁ S₂ (X (Sum.inr c)) = C (X c) :=
  eval₂_X _ _ (Sum.inr c)

/-- The function from multivariable polynomials in one type,
with coefficients in multivariable polynomials in another type,
to multivariable polynomials in the sum of the two types.

See `sumRingEquiv` for the ring isomorphism.
-/
def iterToSum : MvPolynomial S₁ (MvPolynomial S₂ R) →+* MvPolynomial (S₁ ⊕ S₂) R :=
  eval₂Hom (eval₂Hom C (X ∘ Sum.inr)) (X ∘ Sum.inl)

@[simp]
theorem iterToSum_C_C (a : R) : iterToSum R S₁ S₂ (C (C a)) = C a :=
  Eq.trans (eval₂_C _ _ (C a)) (eval₂_C _ _ _)

@[simp]
theorem iterToSum_X (b : S₁) : iterToSum R S₁ S₂ (X b) = X (Sum.inl b) :=
  eval₂_X _ _ _

@[simp]
theorem iterToSum_C_X (c : S₂) : iterToSum R S₁ S₂ (C (X c)) = X (Sum.inr c) :=
  Eq.trans (eval₂_C _ _ (X c)) (eval₂_X _ _ _)

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

variable {R S₁ σ} in
@[simp]
lemma aeval_injective_iff_of_isEmpty [IsEmpty σ] [CommSemiring S₁] [Algebra R S₁] {f : σ → S₁} :
    Function.Injective (aeval f : MvPolynomial σ R →ₐ[R] S₁) ↔
      Function.Injective (algebraMap R S₁) := by
  have : aeval f = (Algebra.ofId R S₁).comp (@isEmptyAlgEquiv R σ _ _).toAlgHom := by
    ext i
    exact IsEmpty.elim' ‹IsEmpty σ› i
  rw [this, ← Injective.of_comp_iff' _ (@isEmptyAlgEquiv R σ _ _).bijective]
  rfl

/-- The ring isomorphism between multivariable polynomials in no variables
and the ground ring. -/
@[simps!]
def isEmptyRingEquiv [IsEmpty σ] : MvPolynomial σ R ≃+* R :=
  (isEmptyAlgEquiv R σ).toRingEquiv

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

/-- The ring isomorphism between multivariable polynomials in a sum of two types,
and multivariable polynomials in one of the types,
with coefficients in multivariable polynomials in the other type.
-/
def sumRingEquiv : MvPolynomial (S₁ ⊕ S₂) R ≃+* MvPolynomial S₁ (MvPolynomial S₂ R) := by
  apply mvPolynomialEquivMvPolynomial R (S₁ ⊕ S₂) _ _ (sumToIter R S₁ S₂) (iterToSum R S₁ S₂)
  · refine RingHom.ext (hom_eq_hom _ _ ?hC ?hX)
    case hC => ext1; simp only [RingHom.comp_apply, iterToSum_C_C, sumToIter_C]
    case hX => intro; simp only [RingHom.comp_apply, iterToSum_C_X, sumToIter_Xr]
  · simp [iterToSum_X, sumToIter_Xl]
  · ext1; simp only [RingHom.comp_apply, sumToIter_C, iterToSum_C_C]
  · rintro ⟨⟩ <;> simp only [sumToIter_Xl, iterToSum_X, sumToIter_Xr, iterToSum_C_X]

/-- The algebra isomorphism between multivariable polynomials in a sum of two types,
and multivariable polynomials in one of the types,
with coefficients in multivariable polynomials in the other type.
-/
@[simps!]
def sumAlgEquiv : MvPolynomial (S₁ ⊕ S₂) R ≃ₐ[R] MvPolynomial S₁ (MvPolynomial S₂ R) :=
  { sumRingEquiv R S₁ S₂ with
    commutes' := by
      intro r
      have A : algebraMap R (MvPolynomial S₁ (MvPolynomial S₂ R)) r = (C (C r) :) := rfl
      have B : algebraMap R (MvPolynomial (S₁ ⊕ S₂) R) r = C r := rfl
      simp only [sumRingEquiv, mvPolynomialEquivMvPolynomial, Equiv.toFun_as_coe,
        Equiv.coe_fn_mk, B, sumToIter_C, A] }

lemma sumAlgEquiv_comp_rename_inr :
    (sumAlgEquiv R S₁ S₂).toAlgHom.comp (rename Sum.inr) = IsScalarTower.toAlgHom R
        (MvPolynomial S₂ R) (MvPolynomial S₁ (MvPolynomial S₂ R)) := by
  ext i
  simp

lemma sumAlgEquiv_comp_rename_inl :
    (sumAlgEquiv R S₁ S₂).toAlgHom.comp (rename Sum.inl) =
      MvPolynomial.mapAlgHom (Algebra.ofId _ _) := by
  ext i
  simp

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

lemma optionEquivLeft_X_some (x : S₁) : optionEquivLeft R S₁ (X (some x)) = Polynomial.C (X x) := by
  simp [optionEquivLeft_apply, aeval_X]

lemma optionEquivLeft_X_none : optionEquivLeft R S₁ (X none) = Polynomial.X := by
  simp [optionEquivLeft_apply, aeval_X]

lemma optionEquivLeft_C (r : R) : optionEquivLeft R S₁ (C r) = Polynomial.C (C r) := by
  simp only [optionEquivLeft_apply, aeval_C, Polynomial.algebraMap_apply, algebraMap_eq]

end

/-- The algebra isomorphism between multivariable polynomials in `Option S₁` and
multivariable polynomials with coefficients in polynomials.
-/
@[simps!]
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

lemma optionEquivRight_X_some (x : S₁) : optionEquivRight R S₁ (X (some x)) = X x := by
  simp [optionEquivRight_apply, aeval_X]

lemma optionEquivRight_X_none : optionEquivRight R S₁ (X none) = C Polynomial.X := by
  simp [optionEquivRight_apply, aeval_X]

lemma optionEquivRight_C (r : R) : optionEquivRight R S₁ (C r) = C (Polynomial.C r) := by
  simp only [optionEquivRight_apply, aeval_C, algebraMap_apply, Polynomial.algebraMap_eq]

section FinSuccEquivNth

variable {n : ℕ} (p : Fin (n + 1))

/-- The algebra isomorphism between multivariable polynomials in `Fin (n + 1)` and polynomials over
  multivariable polynomials in `Fin n`, where the `p`-th (pivot) variable is the indeterminate `X`.

  `finSuccEquiv` is the special case when `p = 0`. -/
def finSuccEquivNth : MvPolynomial (Fin (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R) :=
  (renameEquiv R (_root_.finSuccEquiv' p)).trans (optionEquivLeft R (Fin n))

theorem finSuccEquivNth_eq :
    (finSuccEquivNth R p : MvPolynomial (Fin (n + 1)) R →+* Polynomial (MvPolynomial (Fin n) R)) =
      eval₂Hom (Polynomial.C.comp (C : R →+* MvPolynomial (Fin n) R))
        (Fin.insertNth p Polynomial.X (Polynomial.C ∘ X)) := by
  ext j : 2
  · simp only [finSuccEquivNth, optionEquivLeft_apply, aeval_C, AlgEquiv.coe_trans, RingHom.coe_coe,
      coe_eval₂Hom, comp_apply, renameEquiv_apply, eval₂_C, RingHom.coe_comp, rename_C]
    rfl
  · refine Fin.succAboveCases p ?_ ?_ j <;> simp [finSuccEquivNth]

theorem finSuccEquivNth_apply (f : MvPolynomial (Fin (n + 1)) R) :
    finSuccEquivNth R p f =
      eval₂Hom (Polynomial.C.comp (C : R →+* MvPolynomial (Fin n) R))
        (Fin.insertNth p Polynomial.X (Polynomial.C ∘ X)) f := by
  rw [← finSuccEquivNth_eq, RingHom.coe_coe]

theorem finSuccEquivNth_comp_C_eq_C :
    (↑(finSuccEquivNth R p).symm : Polynomial (MvPolynomial (Fin n) R) →+* _).comp
        (Polynomial.C.comp C) = (C : R →+* MvPolynomial (Fin n.succ) R) := by
  refine RingHom.ext fun x => ?_
  rw [RingHom.comp_apply]
  refine
    (finSuccEquivNth R p).injective
      (Trans.trans ((finSuccEquivNth R p).apply_symm_apply _) ?_)
  simp only [finSuccEquivNth_apply, MvPolynomial.eval₂Hom_C]

variable {R} {p}

@[simp]
theorem finSuccEquivNth_X_same : finSuccEquivNth R p (X p) = Polynomial.X := by
  simp [finSuccEquivNth_apply]

@[simp]
theorem finSuccEquivNth_X_above {i : Fin n} (h : p < i.succ) :
    finSuccEquivNth R p (X i.succ) = Polynomial.C (X i) := by
  simp [finSuccEquivNth_apply, Fin.insertNth_apply_above h _ _]

@[simp]
theorem finSuccEquivNth_X_below {i : Fin n} (h : i.castSucc < p) :
    finSuccEquivNth R p (X i.castSucc) = Polynomial.C (X i) := by
  simp [finSuccEquivNth_apply, Fin.insertNth_apply_below h _ _]

/-- The coefficient of `m` in the `i`-th coefficient of `finSuccEquivNth R p f` equals the
    coefficient of `m.insertNth p i` in `f`. -/
theorem finSuccEquivNth_coeff_coeff (m : Fin n →₀ ℕ) (f : MvPolynomial (Fin (n + 1)) R) (i : ℕ) :
    coeff m (Polynomial.coeff (finSuccEquivNth R p f) i) = coeff (m.insertNth p i) f := by
  induction' f using MvPolynomial.induction_on' with u a p q hp hq generalizing i m
  · simp only [finSuccEquivNth_apply, coe_eval₂Hom, eval₂_monomial, RingHom.coe_comp, comp_apply,
      prod_pow, Fin.prod_univ_succAbove _ p, Fin.insertNth_apply_same,
      Fin.insertNth_apply_succAbove, Polynomial.coeff_C_mul, coeff_C_mul, coeff_monomial,
      ← map_prod, ← RingHom.map_pow]
    rw [← mul_boole, mul_comm (Polynomial.X ^ u p), Polynomial.coeff_C_mul_X_pow]; congr 1
    obtain rfl | hjmi := eq_or_ne u (m.insertNth p i)
    · simpa only [insertNth_apply_same, if_pos rfl, insertNth_apply_succAbove, monomial_eq, C_1,
        one_mul, prod_pow] using coeff_monomial m m (1 : R)
    · simp only [hjmi, if_false]
      obtain hij | rfl := ne_or_eq i (u p)
      · simp only [hij, if_false, coeff_zero]
      simp only [eq_self_iff_true, if_true]
      have hmj : m ≠ u.removeNth p := by
        rintro rfl
        rw [insertNth_self_removeNth] at hjmi
        contradiction
      simpa only [monomial_eq, C_1, one_mul, prod_pow, Finsupp.removeNth_apply, if_neg hmj.symm]
        using coeff_monomial m (u.removeNth p) (1 : R)
  · simp only [map_add, Polynomial.coeff_add, coeff_add, hp, hq]

/-- The evaluation of `f` at `Fin.insertNth p y s` equals the evaluation at `y` of the polynomial
obtained by partially evaluating `finSuccEquivNth R p f` at `s`.
-/
theorem eval_eq_eval_mv_eval_finSuccEquivNth (s : Fin n → R) (y : R)
    (f : MvPolynomial (Fin (n + 1)) R) :
      eval (Fin.insertNth p y s : Fin (n + 1) → R) f =
        Polynomial.eval y (Polynomial.map (eval s) (finSuccEquivNth R p f)) := by
  show
    aeval (Fin.insertNth p y s : Fin (n + 1) → R) f = (Polynomial.aeval y).comp
      ((Polynomial.mapAlgHom (aeval s)).comp (finSuccEquivNth R p).toAlgHom) f
  congr 2
  apply MvPolynomial.algHom_ext
  simp only [Fin.forall_iff_succAbove p, aeval_X, Fin.insertNth_apply_same, Polynomial.mapAlgHom,
    AlgHom.toRingHom_eq_coe, coe_aeval_eq_eval, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp,
    Polynomial.coe_aeval_eq_eval, AlgHom.coe_mk, coe_mapRingHom, AlgHom.coe_coe, comp_apply,
    finSuccEquivNth_apply, eval₂Hom_X', Polynomial.map_X, Polynomial.eval_X,
    Fin.insertNth_apply_succAbove, Polynomial.map_C, eval_X, Polynomial.eval_C, implies_true,
    and_self]

/-- A monomial index `m` is in the support of the `i`-th coefficient of `finSuccEquivNth R p f` if
and only if `m.insertNth p i` is in the support of `f`. -/
theorem support_coeff_finSuccEquivNth {f : MvPolynomial (Fin (n + 1)) R} {i : ℕ} {m : Fin n →₀ ℕ} :
    m ∈ (Polynomial.coeff ((finSuccEquivNth R p) f) i).support ↔ m.insertNth p i ∈ f.support := by
  constructor <;> intro h
  · simpa [← finSuccEquivNth_coeff_coeff] using h
  · simpa [mem_support_iff, ← finSuccEquivNth_coeff_coeff m f i] using h

/--
The `totalDegree` of a multivariable polynomial `f` is at least `i` more than the `totalDegree` of
the `i`th coefficient of `finSuccEquivNth R p` applied to `f`, if this is nonzero.
-/
theorem totalDegree_coeff_finSuccEquivNth_add_le (f : MvPolynomial (Fin (n + 1)) R) (i : ℕ)
    (hi : (finSuccEquivNth R p f).coeff i ≠ 0) :
      totalDegree ((finSuccEquivNth R p f).coeff i) + i ≤ totalDegree f := by
  have hf'_sup : ((finSuccEquivNth R p f).coeff i).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, ne_eq, support_eq_empty]
    exact hi
  -- Let σ be a monomial index of ((finSuccEquivNth R p f).coeff i) of maximal total degree
  have ⟨σ, hσ1, hσ2⟩ := Finset.exists_mem_eq_sup (support _) hf'_sup
                          (fun s => Finsupp.sum s fun _ e => e)
  -- Then σ.insertNth p i is a monomial index of f with total degree equal to the desired bound
  convert le_totalDegree (s := σ.insertNth p i) _
  · rw [totalDegree, hσ2, sum_insertNth _ _ p, add_comm]
  · rwa [← support_coeff_finSuccEquivNth]

/-- The support of `finSuccEquivNth R p f` equals the support of `f` projected onto the `p`-th
variable. -/
theorem support_finSuccEquivNth (f : MvPolynomial (Fin (n + 1)) R) :
    (finSuccEquivNth R p f).support = Finset.image (fun m : Fin (n + 1) →₀ ℕ => m p) f.support := by
  ext i
  rw [Polynomial.mem_support_iff, Finset.mem_image, Finsupp.ne_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m.insertNth p i, ?_, insertNth_apply_same _ _ _⟩
    rw [← support_coeff_finSuccEquivNth]
    simpa using hm
  · rintro ⟨m, h, rfl⟩
    refine ⟨m.removeNth p, ?_⟩
    rwa [← coeff, zero_apply, ← mem_support_iff, support_coeff_finSuccEquivNth,
      insertNth_self_removeNth]

theorem mem_support_finSuccEquivNth {f : MvPolynomial (Fin (n + 1)) R} {x} :
    x ∈ (finSuccEquivNth R p f).support ↔ x ∈ (fun m : Fin (n + 1) →₀ _ ↦ m p) '' f.support := by
  simpa using congr(x ∈ $(support_finSuccEquivNth f))

theorem image_support_finSuccEquivNth {f : MvPolynomial (Fin (n + 1)) R} {i : ℕ} :
    Finset.image (Finsupp.insertNth p i) (Polynomial.coeff ((finSuccEquivNth R p) f) i).support =
      f.support.filter fun m => m p = i := by
  ext m
  rw [Finset.mem_filter, Finset.mem_image, mem_support_iff]
  conv_lhs =>
    congr
    ext
    rw [mem_support_iff, finSuccEquivNth_coeff_coeff, Ne]
  constructor
  · rintro ⟨m', ⟨h, hm'⟩⟩
    simp only [← hm']
    exact ⟨h, by rw [insertNth_apply_same]⟩
  · intro h
    use m.removeNth p
    rw [← h.2, insertNth_removeNth]
    simp [h.1]

lemma mem_image_support_coeff_finSuccEquivNth {f : MvPolynomial (Fin (n + 1)) R} {i : ℕ} {x} :
    x ∈ Finsupp.insertNth p i '' ((finSuccEquivNth R p f).coeff i).support ↔
      x ∈ f.support ∧ x p = i := by
  simpa using congr(x ∈ $image_support_finSuccEquivNth)

lemma mem_support_coeff_finSuccEquivNth {f : MvPolynomial (Fin (n + 1)) R} {i : ℕ} {x} :
    x ∈ ((finSuccEquivNth R p f).coeff i).support ↔ x.insertNth p i ∈ f.support := by
  rw [← (Finsupp.insertNth_right_injective p).mem_finset_image (a := x),
    image_support_finSuccEquivNth]
  simp only [Finset.mem_filter, mem_support_iff, ne_eq, insertNth_apply_same, and_true]

theorem support_finSuccEquivNth_nonempty {f : MvPolynomial (Fin (n + 1)) R} (h : f ≠ 0) :
    (finSuccEquivNth R p f).support.Nonempty := by
  rwa [Polynomial.support_nonempty, EmbeddingLike.map_ne_zero_iff]

/-- The degree of `finSuccEquivNth R p f` equals the `p`-th degree of `f`. -/
theorem degree_finSuccEquivNth {f : MvPolynomial (Fin (n + 1)) R} (h : f ≠ 0) :
    (finSuccEquivNth R p f).degree = degreeOf p f := by
  have hCast : WithBot.some = Nat.cast := rfl
  have h' : ((finSuccEquivNth R p f).support.sup id) = degreeOf p f := by
    rw [degreeOf_eq_sup, support_finSuccEquivNth f, Finset.sup_image, Function.id_comp]
  rw [Polynomial.degree, ← h', ← hCast, Finset.coe_sup_of_nonempty
    (Polynomial.support_nonempty.mpr (EmbeddingLike.map_ne_zero_iff.mpr h)),
    Finset.max_eq_sup_coe, Function.comp_id]

/-- The `natDegree` of `finSuccEquivNth R p f` equals the `p`-th `natDegree` of `f`. -/
theorem natDegree_finSuccEquivNth (f : MvPolynomial (Fin (n + 1)) R) :
    (finSuccEquivNth R p f).natDegree = degreeOf p f := by
  by_cases c : f = 0
  · rw [c, map_zero, Polynomial.natDegree_zero, degreeOf_zero]
  · rw [Polynomial.natDegree, degree_finSuccEquivNth (by simpa only [Ne])]
    erw [WithBot.unbot'_coe, Nat.cast_id]

/-- The degree of `j` in the `i`th coefficient of `finSuccEquivNth R p f` is at most the degree of
`j.succ` in `f`. -/
theorem degreeOf_coeff_finSuccEquivNth (f : MvPolynomial (Fin (n + 1)) R) (j : Fin n) (i : ℕ) :
    degreeOf j (Polynomial.coeff (finSuccEquivNth R p f) i) ≤ degreeOf (p.succAbove j) f := by
  rw [degreeOf_eq_sup, degreeOf_eq_sup, Finset.sup_le_iff]
  intro m hm
  rw [← Finsupp.insertNth_apply_succAbove p i m j]
  exact Finset.le_sup (f := fun (g : Fin n.succ →₀ ℕ) => g (Fin.succAbove p j))
    (support_coeff_finSuccEquivNth.1 hm)

/-- Consider a multivariate polynomial `φ` whose variables are indexed by `Option σ`,
and suppose that `σ ≃ Fin n`.
Then one may view `φ` as a polynomial over `MvPolynomial (Fin n) R`, by

1. renaming the variables via `Option σ ≃ Fin (n+1)`, and then singling out the `p`-th variable
    via `MvPolynomial.finSuccEquivNth R p`;
2. first viewing it as polynomial over `MvPolynomial σ R` via `MvPolynomial.optionEquivLeft`,
    and then renaming the variables.

This theorem shows that both constructions are the same. -/
theorem finSuccEquivNth_rename_finSuccEquivNth (e : σ ≃ Fin n) (φ : MvPolynomial (Option σ) R) :
    ((finSuccEquivNth R p) ((rename ((Equiv.optionCongr e).trans (_root_.finSuccEquiv' p).symm)) φ))
      = Polynomial.map (rename e).toRingHom (optionEquivLeft R σ φ) := by
  suffices (finSuccEquivNth R p).toRingEquiv.toRingHom.comp (rename ((Equiv.optionCongr e).trans
        (_root_.finSuccEquiv' p).symm)).toRingHom =
      (Polynomial.mapRingHom (rename e).toRingHom).comp (optionEquivLeft R σ) by
    exact DFunLike.congr_fun this φ
  apply ringHom_ext
  · simp [finSuccEquivNth_apply, Polynomial.algebraMap_apply, algebraMap_eq]
  · rintro (i|i) <;> simp [finSuccEquivNth_apply]

end FinSuccEquivNth

variable (n : ℕ)

/-- The algebra isomorphism between multivariable polynomials in `Fin (n + 1)` and
polynomials over multivariable polynomials in `Fin n`.
-/
def finSuccEquiv : MvPolynomial (Fin (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R) :=
  finSuccEquivNth R 0

theorem finSuccEquiv_eq :
    (finSuccEquiv R n : MvPolynomial (Fin (n + 1)) R →+* Polynomial (MvPolynomial (Fin n) R)) =
      eval₂Hom (Polynomial.C.comp (C : R →+* MvPolynomial (Fin n) R))
        (Fin.cases Polynomial.X (Polynomial.C ∘ X)) := by
  convert finSuccEquivNth_eq R 0
  funext
  simp only [Fin.insertNth_zero', Fin.cons]

theorem finSuccEquiv_apply (p : MvPolynomial (Fin (n + 1)) R) :
    finSuccEquiv R n p =
      eval₂Hom (Polynomial.C.comp (C : R →+* MvPolynomial (Fin n) R))
        (Fin.cases Polynomial.X (Polynomial.C ∘ X)) p := by
  rw [← finSuccEquiv_eq, RingHom.coe_coe]

theorem finSuccEquiv_comp_C_eq_C {R : Type u} [CommSemiring R] (n : ℕ) :
    (↑(finSuccEquiv R n).symm : Polynomial (MvPolynomial (Fin n) R) →+* _).comp
        (Polynomial.C.comp C) = (C : R →+* MvPolynomial (Fin n.succ) R) :=
  finSuccEquivNth_comp_C_eq_C R 0

variable {n} {R}

@[simp]
theorem finSuccEquiv_X_zero : finSuccEquiv R n (X 0) = Polynomial.X := by simp [finSuccEquiv_apply]

@[simp]
theorem finSuccEquiv_X_succ {j : Fin n} : finSuccEquiv R n (X j.succ) = Polynomial.C (X j) := by
  simp [finSuccEquiv_apply]

/-- The coefficient of `m` in the `i`-th coefficient of `finSuccEquiv R n f` equals the
    coefficient of `Finsupp.cons i m` in `f`. -/
theorem finSuccEquiv_coeff_coeff (m : Fin n →₀ ℕ) (f : MvPolynomial (Fin (n + 1)) R) (i : ℕ) :
    coeff m (Polynomial.coeff (finSuccEquiv R n f) i) = coeff (m.cons i) f := by
  convert finSuccEquivNth_coeff_coeff m f i
  funext
  simp only [insertNth_zero]

theorem eval_eq_eval_mv_eval' (s : Fin n → R) (y : R) (f : MvPolynomial (Fin (n + 1)) R) :
    eval (Fin.cons y s : Fin (n + 1) → R) f =
      Polynomial.eval y (Polynomial.map (eval s) (finSuccEquiv R n f)) := by
  convert eval_eq_eval_mv_eval_finSuccEquivNth s y f
  funext
  simp only [Fin.insertNth_zero']

theorem coeff_eval_eq_eval_coeff (s' : Fin n → R) (f : Polynomial (MvPolynomial (Fin n) R))
    (i : ℕ) : Polynomial.coeff (Polynomial.map (eval s') f) i = eval s' (Polynomial.coeff f i) := by
  simp only [Polynomial.coeff_map]

theorem support_coeff_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {i : ℕ} {m : Fin n →₀ ℕ} :
    m ∈ ((finSuccEquiv R n f).coeff i).support ↔ m.cons i ∈ f.support := by
  convert support_coeff_finSuccEquivNth
  funext
  simp only [insertNth_zero]

/--
The `totalDegree` of a multivariable polynomial `p` is at least `i` more than the `totalDegree` of
the `i`th coefficient of `finSuccEquiv` applied to `p`, if this is nonzero.
-/
theorem totalDegree_coeff_finSuccEquiv_add_le (f : MvPolynomial (Fin (n + 1)) R) (i : ℕ)
    (hi : (finSuccEquiv R n f).coeff i ≠ 0) :
    totalDegree ((finSuccEquiv R n f).coeff i) + i ≤ totalDegree f :=
  totalDegree_coeff_finSuccEquivNth_add_le f i hi

theorem support_finSuccEquiv (f : MvPolynomial (Fin (n + 1)) R) :
    (finSuccEquiv R n f).support = Finset.image (fun m : Fin (n + 1) →₀ ℕ => m 0) f.support :=
  support_finSuccEquivNth f

@[deprecated (since := "2024-11-05")] alias finSuccEquiv_support := support_finSuccEquiv

theorem mem_support_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {x} :
    x ∈ (finSuccEquiv R n f).support ↔ x ∈ (fun m : Fin (n + 1) →₀ _ ↦ m 0) '' f.support := by
  simpa using congr(x ∈ $(support_finSuccEquiv f))

theorem image_support_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {i : ℕ} :
    ((finSuccEquiv R n f).coeff i).support.image (Finsupp.cons i) = {m ∈ f.support | m 0 = i} := by
  convert image_support_finSuccEquivNth
  funext
  simp only [insertNth_zero]

@[deprecated (since := "2024-11-05")] alias finSuccEquiv_support' := image_support_finSuccEquiv

lemma mem_image_support_coeff_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {i : ℕ} {x} :
    x ∈ Finsupp.cons i '' ((finSuccEquiv R n f).coeff i).support ↔
      x ∈ f.support ∧ x 0 = i := by
  simpa using congr(x ∈ $image_support_finSuccEquiv)

lemma mem_support_coeff_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {i : ℕ} {x} :
    x ∈ ((finSuccEquiv R n f).coeff i).support ↔ x.cons i ∈ f.support := by
  convert mem_support_coeff_finSuccEquivNth
  funext
  simp only [insertNth_zero]

-- TODO: generalize `finSuccEquiv R n` to an arbitrary ZeroHom
theorem support_finSuccEquiv_nonempty {f : MvPolynomial (Fin (n + 1)) R} (h : f ≠ 0) :
    (finSuccEquiv R n f).support.Nonempty := by
  rwa [Polynomial.support_nonempty, EmbeddingLike.map_ne_zero_iff]

theorem degree_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} (h : f ≠ 0) :
    (finSuccEquiv R n f).degree = degreeOf 0 f :=
  degree_finSuccEquivNth h

theorem natDegree_finSuccEquiv (f : MvPolynomial (Fin (n + 1)) R) :
    (finSuccEquiv R n f).natDegree = degreeOf 0 f :=
  natDegree_finSuccEquivNth f

theorem degreeOf_coeff_finSuccEquiv (p : MvPolynomial (Fin (n + 1)) R) (j : Fin n) (i : ℕ) :
    degreeOf j (Polynomial.coeff (finSuccEquiv R n p) i) ≤ degreeOf j.succ p :=
  degreeOf_coeff_finSuccEquivNth p j i

/-- Consider a multivariate polynomial `φ` whose variables are indexed by `Option σ`,
and suppose that `σ ≃ Fin n`.
Then one may view `φ` as a polynomial over `MvPolynomial (Fin n) R`, by

1. renaming the variables via `Option σ ≃ Fin (n+1)`, and then singling out the `0`-th variable
    via `MvPolynomial.finSuccEquiv`;
2. first viewing it as polynomial over `MvPolynomial σ R` via `MvPolynomial.optionEquivLeft`,
    and then renaming the variables.

This theorem shows that both constructions are the same. -/
theorem finSuccEquiv_rename_finSuccEquiv (e : σ ≃ Fin n) (φ : MvPolynomial (Option σ) R) :
    ((finSuccEquiv R n) ((rename ((Equiv.optionCongr e).trans (_root_.finSuccEquiv n).symm)) φ)) =
      Polynomial.map (rename e).toRingHom (optionEquivLeft R σ φ) :=
  finSuccEquivNth_rename_finSuccEquivNth e φ

end

@[simp]
theorem rename_polynomial_aeval_X {σ τ : Type*} (f : σ → τ) (i : σ) (p : R[X]) :
    rename f (Polynomial.aeval (X i) p) = Polynomial.aeval (X (f i) : MvPolynomial τ R) p := by
  rw [← aeval_algHom_apply, rename_X]

end Equiv

end MvPolynomial
