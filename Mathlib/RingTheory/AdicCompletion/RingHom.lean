/-
Copyright (c) 2025 Jiedong Jiang All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Lift of ring homomorphisms to adic completions
Let `R`, `S` be rings, `I` be an ideal of `S`.
In this file we prove that a compatible family of ring homomorphisms from a ring `R` to
`S ⧸ I ^ n` can be lifted to a ring homomorphism `R →+* AdicCompletion I S`.
If `S` is `I`-adically complete, this  compatible family of ring homomorphisms can be
lifted to a ring homomorphism `R →+* S`.

## Main definitions

- `AdicCompletion.liftRingHom`: given a compatible family of ring maps
  `R →+* S ⧸ I ^ n`, construct a ring map `R →+* AdicCompletion I S`.
- `IsAdicComplete.liftRingHom`: if `R` is
  `I`-adically complete, then a compatible family of
  ring maps `S →+* R ⧸ I ^ n` can be lifted to a unique ring map `S →+* R`.
  Together with `mk_liftRingHom_apply` and `eq_liftRingHom`, it gives the universal property
  of `R` being `I`-adically complete.
-/

open Ideal Quotient

variable {R S : Type*} [NonAssocSemiring R] [CommRing S] (I : Ideal S)

namespace AdicCompletion

variable {I} in
/--
Helper lemma for the construction of `S ⧸ I ^ n → S ⧸ (I ^ n • ⊤)`.
-/
lemma _root_.Ideal.pow_le_pow_smul_top {n : ℕ} : I ^ n ≤ I ^ n • ⊤ :=
  le_of_eq ((smul_eq_mul (I ^ n) _) ▸ (mul_top _).symm : I ^ n = I ^ n • ⊤)

variable {I} in
/--
Helper lemma for the construction of `S ⧸ (I ^ n • ⊤) → S ⧸ I ^ n`.
-/
lemma _root_.Ideal.pow_smul_top_le_pow {n : ℕ} : I ^ n • ⊤ ≤ I ^ n :=
  le_of_eq ((smul_eq_mul (I ^ n) _) ▸ (mul_top _).symm : I ^ n = I ^ n • ⊤).symm

-- noncomputable def evalₐ (n : ℕ) : AdicCompletion I S →+* S ⧸ I ^ n := evalₐ I n

-- @[simp]
-- theorem evalₐ_coe (n : ℕ) : (evalₐ I n : AdicCompletion I S →+* S ⧸ I ^ n) = evalₐ I n := rfl

-- move to `Mathlib.RingTheory.Ideal.Quotient.Operations` after `Ideal.quotientEquivAlgOfEq_mk`
@[simp]
theorem quotientEquivAlgOfEq_coe_algHom (R : Type*) [CommSemiring R]
    [Algebra R S] {I J : Ideal S} (h : I = J) :
    (quotientEquivAlgOfEq R h : S ⧸ I →ₐ[R] S ⧸ J) = factorₐ R (le_of_eq h) := rfl

-- move to `Mathlib.RingTheory.Ideal.Quotient.Operations` after `Ideal.quotientEquivAlgOfEq_mk`
@[simp]
theorem quotientEquivAlgOfEq_coe_RingHom (R : Type*) [CommSemiring R]
    [Algebra R S] {I J : Ideal S} (h : I = J) :
    (quotientEquivAlgOfEq R h : S ⧸ I →+* S ⧸ J) = factor (le_of_eq h) := rfl

-- move to `Mathlib.RingTheory.Ideal.Quotient.Operations` after `Ideal.Quotient.factorₐ_apply_mk`
@[simp low]
theorem factorₐ_apply (R : Type*) [CommSemiring R]
    [Algebra R S] {I J : Ideal S} (h : I ≤ J) (x : S ⧸ I) :
    factorₐ R h x = factor h x := rfl

@[simp]
theorem factor_evalₐ_apply (n : ℕ) (x : AdicCompletion I S) :
    (factor pow_le_pow_smul_top) (evalₐ I n x) = (eval I S n x) := by
  simp [evalₐ]

theorem factor_eval_eq_evalₐ (n : ℕ) (x : AdicCompletion I S) :
    (factor pow_smul_top_le_pow) (eval I S n x) = (evalₐ I n x) := by
  simp [evalₐ]

/--
The composition map `S →+* AdicCompletion I S →+* S ⧸ I ^ n` equals to the natural quotient map.
-/
@[simp]
theorem evalₐ_of_apply (n : ℕ) (x : S) :
    (evalₐ I n) (of I S x) = Ideal.Quotient.mk _ x := by
  simp [evalₐ, -smul_eq_mul, -Algebra.id.smul_eq_mul]

theorem surjective_evalₐ (n : ℕ) : Function.Surjective (evalₐ I n) := by
  simp only [ evalₐ, smul_eq_mul, quotientEquivAlgOfEq_coe_algHom,
    AlgHom.coe_comp]
  apply Function.Surjective.comp
  · exact factor_surjective mul_le_right
  · exact eval_surjective I S n

/--
Given a compatible family of ring maps `R →+* S ⧸ I ^ n`,
construct a ring map `R →+* AdicCompletion I S`.
-/
def liftRingHom (f : (n : ℕ) → R →+* S ⧸ I ^ n)
    (hf : ∀ {m n : ℕ} (hle : m ≤ n), (factorPow I hle).comp (f n) = f m) :
    R →+* AdicCompletion I S where
  toFun := fun x ↦ ⟨fun n ↦ (factor pow_le_pow_smul_top) (f n x),
    fun hkl ↦ by simp [transitionMap, Submodule.factorPow, ← hf hkl]⟩
  map_add' x y := by
    simp only [map_add]
    rfl
  map_zero' := by
    simp only [map_zero]
    rfl
  map_mul' x y := by
    simp only [map_mul]
    rfl
  map_one' := by
    simp only [map_one]
    rfl

variable (f : (n : ℕ) → R →+* S ⧸ I ^ n)
  (hf : ∀ {m n : ℕ} (hle : m ≤ n), (factorPow I hle).comp (f n) = f m)

@[simp]
theorem factor_eval_liftRingHom_apply (n : ℕ) (x : R) :
    (factor pow_smul_top_le_pow) (eval I S n (liftRingHom I f hf x)) = (f n x) := by
  simp [liftRingHom, eval]

@[simp]
theorem evalₐ_liftRingHom_apply (n : ℕ) (x : R) :
    (evalₐ I n) (liftRingHom I f hf x) = f n x := by
  rw [← factor_eval_eq_evalₐ]
  simp [liftRingHom, eval]

@[simp]
theorem evalₐ_comp_liftRingHom (n : ℕ) :
    (evalₐ I n : _ →+* _).comp (liftRingHom I f hf) = f n := by
  ext
  exact evalₐ_liftRingHom_apply I f hf n _

/--
When `S` is `I`-adic complete, the canonical map from `M` to its `I`-adic completion is an `S`-algebra
isomorphism.
-/
noncomputable def ofAlgEquiv [IsAdicComplete I S] : S →ₐ[S] AdicCompletion I S :=
  { ofLinearEquiv I S with
    map_mul' := fun x y ↦ sorry
  }


@[simp]
theorem ofLinearEquiv_apply [IsAdicComplete I S] (x : M) :
    ofLinearEquiv I M x = of I M x :=
  rfl

end AdicCompletion

namespace IsAdicComplete

variable [IsAdicComplete I S]

def liftRingHom (f : (n : ℕ) → R →+* S ⧸ I ^ n)
    (hf : ∀ {m n : ℕ} (hle : m ≤ n), (factorPow I hle).comp (f n) = f m) :
    R →+* S :=
  (linearEquiv I S).symm.toRingHom.comp (AdicCompletion.liftRingHom I f hf)

namespace StrictMono

end StrictMono

end IsAdicComplete
