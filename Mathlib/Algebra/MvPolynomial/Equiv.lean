/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
import Mathlib.Algebra.BigOperators.Finsupp.Fin
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.Finsupp.Option
import Mathlib.Logic.Equiv.Fin.Basic

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
    change ∀ p, f.comp g p = p
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

theorem pUnitAlgEquiv_monomial {d : PUnit →₀ ℕ} {r : R} :
    MvPolynomial.pUnitAlgEquiv R (MvPolynomial.monomial d r)
      = Polynomial.monomial (d ()) r := by
  simp [Polynomial.C_mul_X_pow_eq_monomial]

theorem pUnitAlgEquiv_symm_monomial {d : PUnit →₀ ℕ} {r : R} :
    (MvPolynomial.pUnitAlgEquiv R).symm (Polynomial.monomial (d ()) r)
      = MvPolynomial.monomial d r := by
  simp [MvPolynomial.monomial_eq]

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

section Eval

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

theorem eval₂_pUnitAlgEquiv_symm {f : Polynomial R} {φ : R →+* S} {a : Unit → S} :
    ((MvPolynomial.pUnitAlgEquiv R).symm f : MvPolynomial Unit R).eval₂ φ a =
      f.eval₂ φ (a ()) := by
  simp only [MvPolynomial.pUnitAlgEquiv_symm_apply]
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp [hf, hg]
  | monomial n r => simp

theorem eval₂_const_pUnitAlgEquiv_symm {f : Polynomial R} {φ : R →+* S} {a : S} :
    ((MvPolynomial.pUnitAlgEquiv R).symm f : MvPolynomial Unit R).eval₂ φ (fun _ ↦ a) =
      f.eval₂ φ a := by
  rw [eval₂_pUnitAlgEquiv_symm]

theorem eval₂_pUnitAlgEquiv {f : MvPolynomial PUnit R} {φ : R →+* S} {a : PUnit → S} :
    ((MvPolynomial.pUnitAlgEquiv R) f : Polynomial R).eval₂ φ (a default) = f.eval₂ φ a := by
  simp only [MvPolynomial.pUnitAlgEquiv_apply]
  induction f using MvPolynomial.induction_on' with
  | monomial d r => simp
  | add f g hf hg => simp [hf, hg]

theorem eval₂_const_pUnitAlgEquiv {f : MvPolynomial PUnit R} {φ : R →+* S} {a : S} :
    ((MvPolynomial.pUnitAlgEquiv R) f : Polynomial R).eval₂ φ a = f.eval₂ φ (fun _ ↦ a) := by
  rw [← eval₂_pUnitAlgEquiv]

end Eval

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

section isEmptyRingEquiv
variable [IsEmpty σ]

variable (σ) in
/-- The algebra isomorphism between multivariable polynomials in no variables
and the ground ring. -/
@[simps! apply]
def isEmptyAlgEquiv : MvPolynomial σ R ≃ₐ[R] R :=
  .ofAlgHom (aeval isEmptyElim) (Algebra.ofId _ _) (by ext) (by ext i m; exact isEmptyElim i)

variable {R S₁} in
@[simp]
lemma aeval_injective_iff_of_isEmpty [CommSemiring S₁] [Algebra R S₁] {f : σ → S₁} :
    Function.Injective (aeval f : MvPolynomial σ R →ₐ[R] S₁) ↔
      Function.Injective (algebraMap R S₁) := by
  have : aeval f = (Algebra.ofId R S₁).comp (@isEmptyAlgEquiv R σ _ _).toAlgHom := by
    ext i
    exact IsEmpty.elim' ‹IsEmpty σ› i
  rw [this, ← Injective.of_comp_iff' _ (@isEmptyAlgEquiv R σ _ _).bijective]
  rfl

variable (σ) in
/-- The ring isomorphism between multivariable polynomials in no variables
and the ground ring. -/
@[simps! apply]
def isEmptyRingEquiv : MvPolynomial σ R ≃+* R := (isEmptyAlgEquiv R σ).toRingEquiv

lemma isEmptyRingEquiv_symm_toRingHom : (isEmptyRingEquiv R σ).symm.toRingHom = C := rfl
@[simp] lemma isEmptyRingEquiv_symm_apply (r : R) : (isEmptyRingEquiv R σ).symm r = C r := rfl

lemma isEmptyRingEquiv_eq_coeff_zero {σ R : Type*} [CommSemiring R] [IsEmpty σ] {x} :
    isEmptyRingEquiv R σ x = x.coeff 0 := by
  obtain ⟨x, rfl⟩ := (isEmptyRingEquiv R σ).symm.surjective x; simp

end isEmptyRingEquiv

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

section commAlgEquiv
variable {R S₁ S₂ : Type*} [CommSemiring R]

variable (R S₁ S₂) in
/-- The algebra isomorphism between multivariable polynomials in variables `S₁` of multivariable
polynomials in variables `S₂` and multivariable polynomials in variables `S₂` of multivariable
polynomials in variables `S₁`. -/
noncomputable
def commAlgEquiv : MvPolynomial S₁ (MvPolynomial S₂ R) ≃ₐ[R] MvPolynomial S₂ (MvPolynomial S₁ R) :=
  (sumAlgEquiv R S₁ S₂).symm.trans <| (renameEquiv _ (.sumComm S₁ S₂)).trans (sumAlgEquiv R S₂ S₁)

@[simp] lemma commAlgEquiv_C (p) : commAlgEquiv R S₁ S₂ (.C p) = .map C p := by
  suffices (commAlgEquiv R S₁ S₂).toAlgHom.comp
      (IsScalarTower.toAlgHom R (MvPolynomial S₂ R) _) = mapAlgHom (Algebra.ofId _ _) by
    exact DFunLike.congr_fun this p
  ext x : 1
  simp [commAlgEquiv]

lemma commAlgEquiv_C_X (i) : commAlgEquiv R S₁ S₂ (.C (.X i)) = .X i := by simp

@[simp] lemma commAlgEquiv_X (i) : commAlgEquiv R S₁ S₂ (.X i) = .C (.X i) := by simp [commAlgEquiv]

end commAlgEquiv

section

-- this speeds up typeclass search in the lemma below
attribute [local instance] IsScalarTower.right

/-- The algebra isomorphism between multivariable polynomials in `Option S₁` and
polynomials with coefficients in `MvPolynomial S₁ R`.
-/
@[simps! -isSimp]
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

theorem optionEquivLeft_monomial (m : Option S₁ →₀ ℕ) (r : R) :
    optionEquivLeft R S₁ (monomial m r) = .monomial (m none) (monomial m.some r) := by
  rw [optionEquivLeft_apply, aeval_monomial, prod_option_index]
  · rw [MvPolynomial.monomial_eq, ← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [Polynomial.algebraMap_apply, algebraMap_eq, Option.elim_none, Option.elim_some,
      map_mul, mul_assoc]
    simp only [mul_comm, map_finsuppProd, map_pow]
  · simp
  · intros; rw [pow_add]

/-- The coefficient of `n.some` in the `n none`-th coefficient of `optionEquivLeft R S₁ f`
equals the coefficient of `n` in `f` -/
theorem optionEquivLeft_coeff_coeff (n : Option S₁ →₀ ℕ) (f : MvPolynomial (Option S₁) R) :
    coeff n.some (Polynomial.coeff (optionEquivLeft R S₁ f) (n none)) = coeff n f := by
  induction f using MvPolynomial.induction_on' generalizing n with
  | monomial j r =>
    rw [optionEquivLeft_monomial]
    classical
    simp only [Polynomial.coeff_monomial, MvPolynomial.coeff_monomial, apply_ite]
    simp only [coeff_zero]
    by_cases hj : j = n
    · simp [hj]
    · rw [if_neg hj]
      simp only [ite_eq_right_iff]
      intro hj_none hj_some
      apply False.elim (hj _)
      simp only [Finsupp.ext_iff, Option.forall, hj_none, true_and]
      simpa only [Finsupp.ext_iff] using hj_some
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, coeff_add, hp, hq]

theorem optionEquivLeft_elim_eval (s : S₁ → R) (y : R) (f : MvPolynomial (Option S₁) R) :
    eval (fun x ↦ Option.elim x y s) f =
      Polynomial.eval y (Polynomial.map (eval s) (optionEquivLeft R S₁ f)) := by
  -- turn this into a def `Polynomial.mapAlgHom`
  let φ : (MvPolynomial S₁ R)[X] →ₐ[R] R[X] :=
    { Polynomial.mapRingHom (eval s) with
      commutes' := fun r => by
        convert Polynomial.map_C (eval s)
        exact (eval_C _).symm }
  change
    aeval (fun x ↦ Option.elim x y s) f =
      (Polynomial.aeval y).comp (φ.comp (optionEquivLeft _ _).toAlgHom) f
  congr 2
  apply MvPolynomial.algHom_ext
  rw [Option.forall]
  simp only [aeval_X, Option.elim_none, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp,
    Polynomial.coe_aeval_eq_eval, AlgHom.coe_mk, coe_mapRingHom, AlgHom.coe_coe, comp_apply,
    optionEquivLeft_apply, Polynomial.map_X, Polynomial.eval_X, Option.elim_some, Polynomial.map_C,
    eval_X, Polynomial.eval_C, implies_true, and_self, φ]

@[simp]
lemma natDegree_optionEquivLeft (p : MvPolynomial (Option S₁) R) :
    (optionEquivLeft R S₁ p).natDegree = p.degreeOf .none := by
  apply le_antisymm
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    ext σ
    trans p.coeff (σ.embDomain .some + .single .none N)
    · simpa using optionEquivLeft_coeff_coeff R S₁ (σ.embDomain .some + .single .none N) p
    simp only [coeff_zero, ← notMem_support_iff]
    intro H
    simpa using (degreeOf_lt_iff ((zero_le _).trans_lt hN)).mp hN _ H
  · rw [degreeOf_le_iff]
    intro σ hσ
    refine Polynomial.le_natDegree_of_ne_zero fun H ↦ ?_
    have := optionEquivLeft_coeff_coeff R S₁ σ p
    rw [H, coeff_zero, eq_comm, ← notMem_support_iff] at this
    exact this hσ

lemma totalDegree_coeff_optionEquivLeft_add_le
    (p : MvPolynomial (Option S₁) R) (i : ℕ) (hi : i ≤ p.totalDegree) :
    ((optionEquivLeft R S₁ p).coeff i).totalDegree + i ≤ p.totalDegree := by
  classical
  by_cases hpi : (optionEquivLeft R S₁ p).coeff i = 0
  · rw [hpi]; simpa
  rw [totalDegree, add_comm, Finset.add_sup (by simpa only [support_nonempty]), Finset.sup_le_iff]
  intro σ hσ
  refine le_trans ?_ (Finset.le_sup (b := σ.embDomain .some + .single .none i) ?_)
  · simp [Finsupp.sum_add_index, Finsupp.sum_embDomain, add_comm i]
  · simpa [mem_support_iff, ← optionEquivLeft_coeff_coeff R S₁] using hσ

lemma totalDegree_coeff_optionEquivLeft_le
    (p : MvPolynomial (Option S₁) R) (i : ℕ) :
    ((optionEquivLeft R S₁ p).coeff i).totalDegree ≤ p.totalDegree := by
  classical
  by_cases hpi : (optionEquivLeft R S₁ p).coeff i = 0
  · rw [hpi]; simp
  rw [totalDegree, Finset.sup_le_iff]
  intro σ hσ
  refine le_trans ?_ (Finset.le_sup (b := σ.embDomain .some + .single .none i) ?_)
  · simp [Finsupp.sum_add_index, Finsupp.sum_embDomain]
  · simpa [mem_support_iff, ← optionEquivLeft_coeff_coeff R S₁] using hσ

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
          aevalTower_X, AlgHom.coe_id, id])
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

variable (n : ℕ)

/-- The algebra isomorphism between multivariable polynomials in `Fin (n + 1)` and
polynomials over multivariable polynomials in `Fin n`.
-/
def finSuccEquiv : MvPolynomial (Fin (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R) :=
  (renameEquiv R (_root_.finSuccEquiv n)).trans (optionEquivLeft R (Fin n))

theorem finSuccEquiv_eq :
    (finSuccEquiv R n : MvPolynomial (Fin (n + 1)) R →+* Polynomial (MvPolynomial (Fin n) R)) =
      eval₂Hom (Polynomial.C.comp (C : R →+* MvPolynomial (Fin n) R)) fun i : Fin (n + 1) =>
        Fin.cases Polynomial.X (fun k => Polynomial.C (X k)) i := by
  ext i : 2
  · simp only [finSuccEquiv, optionEquivLeft_apply, aeval_C, AlgEquiv.coe_trans, RingHom.coe_coe,
      coe_eval₂Hom, comp_apply, renameEquiv_apply, eval₂_C, RingHom.coe_comp, rename_C]
    rfl
  · refine Fin.cases ?_ ?_ i <;> simp [optionEquivLeft_apply, finSuccEquiv]

theorem finSuccEquiv_apply (p : MvPolynomial (Fin (n + 1)) R) :
    finSuccEquiv R n p =
      eval₂Hom (Polynomial.C.comp (C : R →+* MvPolynomial (Fin n) R))
        (fun i : Fin (n + 1) => Fin.cases Polynomial.X (fun k => Polynomial.C (X k)) i) p := by
  rw [← finSuccEquiv_eq, RingHom.coe_coe]

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

variable {n} {R}

theorem finSuccEquiv_X_zero : finSuccEquiv R n (X 0) = Polynomial.X := by simp [finSuccEquiv_apply]

theorem finSuccEquiv_X_succ {j : Fin n} : finSuccEquiv R n (X j.succ) = Polynomial.C (X j) := by
  simp [finSuccEquiv_apply]

/-- The coefficient of `m` in the `i`-th coefficient of `finSuccEquiv R n f` equals the
    coefficient of `Finsupp.cons i m` in `f`. -/
theorem finSuccEquiv_coeff_coeff (m : Fin n →₀ ℕ) (f : MvPolynomial (Fin (n + 1)) R) (i : ℕ) :
    coeff m (Polynomial.coeff (finSuccEquiv R n f) i) = coeff (m.cons i) f := by
  induction f using MvPolynomial.induction_on' generalizing i m with
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, coeff_add, hp, hq]
  | monomial j r =>
    simp only [finSuccEquiv_apply, coe_eval₂Hom, eval₂_monomial, RingHom.coe_comp, Finsupp.prod_pow,
      Polynomial.coeff_C_mul, coeff_C_mul, coeff_monomial, Fin.prod_univ_succ, Fin.cases_zero,
      Fin.cases_succ, ← map_prod, ← RingHom.map_pow, Function.comp_apply]
    rw [← mul_boole, mul_comm (Polynomial.X ^ j 0), Polynomial.coeff_C_mul_X_pow]; congr 1
    obtain rfl | hjmi := eq_or_ne j (m.cons i)
    · simpa only [cons_zero, cons_succ, if_pos rfl, monomial_eq, C_1, one_mul,
        Finsupp.prod_pow] using coeff_monomial m m (1 : R)
    · simp only [hjmi, if_false]
      obtain hij | rfl := ne_or_eq i (j 0)
      · simp only [hij, if_false, coeff_zero]
      simp only [if_true]
      have hmj : m ≠ j.tail := by
        rintro rfl
        rw [cons_tail] at hjmi
        contradiction
      simpa only [monomial_eq, C_1, one_mul, Finsupp.prod_pow, tail_apply, if_neg hmj.symm] using
        coeff_monomial m j.tail (1 : R)

theorem eval_eq_eval_mv_eval' (s : Fin n → R) (y : R) (f : MvPolynomial (Fin (n + 1)) R) :
    eval (Fin.cons y s : Fin (n + 1) → R) f =
      Polynomial.eval y (Polynomial.map (eval s) (finSuccEquiv R n f)) := by
  -- turn this into a def `Polynomial.mapAlgHom`
  let φ : (MvPolynomial (Fin n) R)[X] →ₐ[R] R[X] :=
    { Polynomial.mapRingHom (eval s) with
      commutes' := fun r => by
        convert Polynomial.map_C (eval s)
        exact (eval_C _).symm }
  change
    aeval (Fin.cons y s : Fin (n + 1) → R) f =
      (Polynomial.aeval y).comp (φ.comp (finSuccEquiv R n).toAlgHom) f
  congr 2
  apply MvPolynomial.algHom_ext
  rw [Fin.forall_iff_succ]
  simp only [φ, aeval_X, Fin.cons_zero, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp,
    Polynomial.coe_aeval_eq_eval, Polynomial.map_C, AlgHom.coe_mk,
    Polynomial.coe_mapRingHom, comp_apply, finSuccEquiv_apply, eval₂Hom_X',
    Fin.cases_zero, Polynomial.map_X, Polynomial.eval_X, Fin.cons_succ,
    Fin.cases_succ, eval_X, Polynomial.eval_C, AlgHom.coe_coe, implies_true, and_self]

theorem coeff_eval_eq_eval_coeff (s' : S₁ → R) (f : Polynomial (MvPolynomial S₁ R))
    (i : ℕ) : Polynomial.coeff (Polynomial.map (eval s') f) i = eval s' (Polynomial.coeff f i) := by
  simp only [Polynomial.coeff_map]

theorem support_coeff_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {i : ℕ} {m : Fin n →₀ ℕ} :
    m ∈ ((finSuccEquiv R n f).coeff i).support ↔ m.cons i ∈ f.support := by
  apply Iff.intro
  · intro h
    simpa [← finSuccEquiv_coeff_coeff] using h
  · intro h
    simpa [mem_support_iff, ← finSuccEquiv_coeff_coeff m f i] using h

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
  let σ' : Fin (n + 1) →₀ ℕ := cons i σ
  convert le_totalDegree (s := σ') _
  · rw [totalDegree, hσ2, sum_cons, add_comm]
  · rw [← support_coeff_finSuccEquiv]
    exact hσ1

theorem support_finSuccEquiv (f : MvPolynomial (Fin (n + 1)) R) :
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

theorem mem_support_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {x} :
    x ∈ (finSuccEquiv R n f).support ↔ x ∈ (fun m : Fin (n + 1) →₀ _ ↦ m 0) '' f.support := by
  simpa using congr(x ∈ $(support_finSuccEquiv f))

theorem image_support_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {i : ℕ} :
    ((finSuccEquiv R n f).coeff i).support.image (Finsupp.cons i) = {m ∈ f.support | m 0 = i} := by
  ext m
  rw [Finset.mem_filter, Finset.mem_image, mem_support_iff]
  conv_lhs =>
    congr
    ext
    rw [mem_support_iff, finSuccEquiv_coeff_coeff, Ne]
  constructor
  · grind [cons_zero]
  · intro h
    use tail m
    rw [← h.2, cons_tail]
    simp [h.1]

lemma mem_image_support_coeff_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {i : ℕ} {x} :
    x ∈ Finsupp.cons i '' ((finSuccEquiv R n f).coeff i).support ↔
      x ∈ f.support ∧ x 0 = i := by
  simpa using congr(x ∈ $image_support_finSuccEquiv)

lemma mem_support_coeff_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {i : ℕ} {x} :
    x ∈ ((finSuccEquiv R n f).coeff i).support ↔ x.cons i ∈ f.support := by
  rw [← (Finsupp.cons_right_injective i).mem_finset_image (a := x),
    image_support_finSuccEquiv]
  simp only [Finset.mem_filter, mem_support_iff, ne_eq, cons_zero, and_true]

-- TODO: generalize `finSuccEquiv R n` to an arbitrary ZeroHom
theorem support_finSuccEquiv_nonempty {f : MvPolynomial (Fin (n + 1)) R} (h : f ≠ 0) :
    (finSuccEquiv R n f).support.Nonempty := by
  rwa [Polynomial.support_nonempty, EmbeddingLike.map_ne_zero_iff]

theorem degree_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} (h : f ≠ 0) :
    (finSuccEquiv R n f).degree = degreeOf 0 f := by
  -- TODO: these should be lemmas
  have h₀ : ∀ {α β : Type _} (f : α → β), (fun x => x) ∘ f = f := fun f => rfl
  have h₁ : ∀ {α β : Type _} (f : α → β), f ∘ (fun x => x) = f := fun f => rfl
  have h' : ((finSuccEquiv R n f).support.sup fun x => x) = degreeOf 0 f := by
    rw [degreeOf_eq_sup, support_finSuccEquiv, Finset.sup_image, h₀]
  rw [Polynomial.degree, ← h', Nat.cast_withBot,
    Finset.coe_sup_of_nonempty (support_finSuccEquiv_nonempty h), Finset.max_eq_sup_coe, h₁]

theorem natDegree_finSuccEquiv (f : MvPolynomial (Fin (n + 1)) R) :
    (finSuccEquiv R n f).natDegree = degreeOf 0 f := by
  by_cases c : f = 0
  · rw [c, map_zero, Polynomial.natDegree_zero, degreeOf_zero]
  · rw [Polynomial.natDegree, degree_finSuccEquiv c, Nat.cast_withBot, WithBot.unbotD_coe]

theorem degreeOf_coeff_finSuccEquiv (p : MvPolynomial (Fin (n + 1)) R) (j : Fin n) (i : ℕ) :
    degreeOf j (Polynomial.coeff (finSuccEquiv R n p) i) ≤ degreeOf j.succ p := by
  rw [degreeOf_eq_sup, degreeOf_eq_sup, Finset.sup_le_iff]
  intro m hm
  rw [← Finsupp.cons_succ j i m]
  exact Finset.le_sup
    (f := fun (g : Fin (Nat.succ n) →₀ ℕ) => g (Fin.succ j))
    (support_coeff_finSuccEquiv.1 hm)

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
  · simp [Polynomial.algebraMap_apply, algebraMap_eq, finSuccEquiv_apply, optionEquivLeft_apply]
  · rintro (i | i) <;> simp [finSuccEquiv_apply, optionEquivLeft_apply]

end

@[simp]
theorem rename_polynomial_aeval_X {σ τ : Type*} (f : σ → τ) (i : σ) (p : R[X]) :
    rename f (Polynomial.aeval (X i) p) = Polynomial.aeval (X (f i) : MvPolynomial τ R) p := by
  rw [← aeval_algHom_apply, rename_X]

end Equiv

end MvPolynomial

section toMvPolynomial

variable {R S σ τ : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- The embedding of `R[X]` into `R[Xᵢ]` as an `R`-algebra homomorphism. -/
noncomputable def Polynomial.toMvPolynomial (i : σ) : R[X] →ₐ[R] MvPolynomial σ R :=
  aeval (MvPolynomial.X i)

@[simp]
lemma Polynomial.toMvPolynomial_C (i : σ) (r : R) : (C r).toMvPolynomial i = MvPolynomial.C r := by
  simp [toMvPolynomial]

@[simp]
lemma Polynomial.toMvPolynomial_X (i : σ) : X.toMvPolynomial i = MvPolynomial.X (R := R) i := by
  simp [toMvPolynomial]

lemma Polynomial.toMvPolynomial_eq_rename_comp (i : σ) :
    toMvPolynomial (R := R) i =
      (MvPolynomial.rename (fun _ : Unit ↦ i)).comp (MvPolynomial.pUnitAlgEquiv R).symm := by
  ext
  simp

lemma Polynomial.toMvPolynomial_injective (i : σ) :
    Function.Injective (toMvPolynomial (R := R) i) := by
  simp only [toMvPolynomial_eq_rename_comp, AlgHom.coe_comp, AlgHom.coe_coe,
    EquivLike.injective_comp]
  exact MvPolynomial.rename_injective (fun x ↦ i) fun _ _ _ ↦ rfl

@[simp]
lemma MvPolynomial.eval_comp_toMvPolynomial (f : σ → R) (i : σ) :
    (eval f).comp (toMvPolynomial (R := R) i) = Polynomial.evalRingHom (f i) := by
  ext <;> simp

@[simp]
lemma MvPolynomial.eval_toMvPolynomial (f : σ → R) (i : σ) (p : R[X]) :
    eval f (p.toMvPolynomial i) = Polynomial.eval (f i) p :=
  DFunLike.congr_fun (eval_comp_toMvPolynomial ..) p

@[simp]
lemma MvPolynomial.aeval_comp_toMvPolynomial (f : σ → S) (i : σ) :
    (aeval (R := R) f).comp (toMvPolynomial i) = Polynomial.aeval (f i) := by
  ext
  simp

@[simp]
lemma MvPolynomial.aeval_toMvPolynomial (f : σ → S) (i : σ) (p : R[X]) :
    aeval f (p.toMvPolynomial i) = Polynomial.aeval (f i) p :=
  DFunLike.congr_fun (aeval_comp_toMvPolynomial ..) p

@[simp]
lemma MvPolynomial.rename_comp_toMvPolynomial (f : σ → τ) (a : σ) :
    (rename (R := R) f).comp (Polynomial.toMvPolynomial a) = Polynomial.toMvPolynomial (f a) := by
  ext
  simp

@[simp]
lemma MvPolynomial.rename_toMvPolynomial (f : σ → τ) (a : σ) (p : R[X]) :
    (rename (R := R) f) (p.toMvPolynomial a) = p.toMvPolynomial (f a) :=
  DFunLike.congr_fun (rename_comp_toMvPolynomial ..) p

end toMvPolynomial
