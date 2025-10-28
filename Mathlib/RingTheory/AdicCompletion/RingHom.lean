/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Lift of ring homomorphisms to adic completions
Let `R`, `S` be rings, `I` be an ideal of `S`.
In this file we prove that a compatible family of ring homomorphisms from a ring `R` to
`S ⧸ I ^ n` can be lifted to a ring homomorphism `R →+* AdicCompletion I S`.
If `S` is `I`-adically complete, then this compatible family of ring homomorphisms can be
lifted to a ring homomorphism `R →+* S`.

## Main definitions

- `AdicCompletion.liftRingHom`: given a compatible family of ring maps
  `R →+* S ⧸ I ^ n`, the lift ring map `R →+* AdicCompletion I S`.
- `IsAdicComplete.liftRingHom`: if `R` is
  `I`-adically complete, then a compatible family of
  ring maps `S →+* R ⧸ I ^ n` can be lifted to a unique ring map `S →+* R`.
  Together with `mk_liftRingHom_apply` and `eq_liftRingHom`, it gives the universal property
  of `R` being `I`-adically complete.
-/

open Ideal Quotient

variable {R S : Type*} [NonAssocSemiring R] [CommRing S] (I : Ideal S)

variable {I} in
/--
Helper lemma for the construction of `S ⧸ I ^ n → S ⧸ (I ^ n • ⊤)`.
-/
private lemma Ideal.pow_le_pow_smul_top {n : ℕ} : I ^ n ≤ I ^ n • ⊤ :=
  le_of_eq ((smul_eq_mul (I ^ n) _) ▸ (mul_top _).symm : I ^ n = I ^ n • ⊤)

variable {I} in
/--
Helper lemma for the construction of `S ⧸ (I ^ n • ⊤) → S ⧸ I ^ n`.
-/
private lemma Ideal.pow_smul_top_le_pow {n : ℕ} : I ^ n • ⊤ ≤ I ^ n :=
  le_of_eq ((smul_eq_mul (I ^ n) _) ▸ (mul_top _).symm : I ^ n = I ^ n • ⊤).symm

namespace AdicCompletion

/--
The composition map `S →+* AdicCompletion I S →+* S ⧸ I ^ n` equals to the natural quotient map.
-/
@[simp]
theorem evalₐ_of_apply (n : ℕ) (x : S) :
    (evalₐ I n) (of I S x) = Ideal.Quotient.mk _ x := by
  simp [evalₐ, -smul_eq_mul, -Algebra.id.smul_eq_mul]

theorem surjective_evalₐ (n : ℕ) : Function.Surjective (evalₐ I n) := by
  simp only [evalₐ, smul_eq_mul, quotientEquivAlgOfEq_coe_eq_factorₐ,
    AlgHom.coe_comp]
  apply Function.Surjective.comp
  · exact factor_surjective mul_le_right
  · exact eval_surjective I S n

/--
The universal property of `IsAdicComplete` for rings.
The lift ring map `R →+* AdicCompletion I S` of a compatible family of
ring maps `R →+* S ⧸ I ^ n`.
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
  rw [← factor_eval_eq_evalₐ I n _ pow_smul_top_le_pow]
  simp [liftRingHom, eval]

@[simp]
theorem evalₐ_comp_liftRingHom (n : ℕ) :
    (evalₐ I n : _ →+* _).comp (liftRingHom I f hf) = f n := by
  ext; simp

variable [IsAdicComplete I S]
/--
When `S` is `I`-adic complete, the canonical map from `S` to
its `I`-adic completion is an `S`-algebra isomorphism.
-/
noncomputable def ofAlgEquiv : S ≃ₐ[S] AdicCompletion I S where
  __ := ofLinearEquiv I S
  map_mul' _ _ := by ext; simp
  commutes' _ := rfl

@[simp]
theorem ofAlgEquiv_apply (x : S) : ofAlgEquiv I x = of I S x :=
  rfl

@[simp]
theorem of_ofAlgEquiv_symm_apply (x : AdicCompletion I S) :
    of I S ((ofAlgEquiv I).symm x) = x := by
  simp [ofAlgEquiv]

@[simp]
theorem factor_mk_ofAlgEquiv_symm_apply (n : ℕ) (x : AdicCompletion I S) :
    factor pow_le_pow_smul_top (Ideal.Quotient.mk (I ^ n) ((ofAlgEquiv I).symm x)) =
    eval I S n x := by
  nth_rw 2 [← of_ofAlgEquiv_symm_apply I x]
  simp [-of_ofAlgEquiv_symm_apply, eval]

@[simp]
theorem mk_ofAlgEquiv_symm_apply (n : ℕ) (x : AdicCompletion I S) :
    Ideal.Quotient.mk (I ^ n) ((ofAlgEquiv I).symm x) = evalₐ I n x := by
  simp only [evalₐ, AlgHom.coe_comp, Function.comp_apply, AlgHom.ofLinearMap_apply]
  rw [← factor_mk_ofAlgEquiv_symm_apply I n x]
  simp

end AdicCompletion

namespace IsAdicComplete

open AdicCompletion

section

variable [IsAdicComplete I S] (f : (n : ℕ) → R →+* S ⧸ I ^ n)
    (hf : ∀ {m n : ℕ} (hle : m ≤ n), (factorPow I hle).comp (f n) = f m)

/--
Universal property of `IsAdicComplete` for rings.
The lift ring map `lift I f hf : R →+* S` of a sequence of compatible
ring maps `f n : R →+* S ⧸ (I ^ n)`.
-/
noncomputable def liftRingHom :
    R →+* S :=
  ((ofAlgEquiv I).symm : _ →+* _).comp (AdicCompletion.liftRingHom I f hf)

@[simp]
theorem of_liftRingHom_apply (x : R) :
    of I S (liftRingHom I f hf x) = (AdicCompletion.liftRingHom I f hf x) := by
  simp [liftRingHom]

@[simp]
theorem ofAlgEquiv_comp_liftRingHom :
    (ofAlgEquiv I : S →+* AdicCompletion I S).comp (liftRingHom I f hf) =
      AdicCompletion.liftRingHom I f hf := by
  ext; simp

/--
The composition of lift linear map `lift I f hf : R →+* S` with the canonical
projection `S →+* S ⧸ (I ^ n)` is `f n` .
-/
@[simp]
theorem mk_liftRingHom_apply (n : ℕ) (x : R) :
    Ideal.Quotient.mk (I ^ n) (liftRingHom I f hf x) = f n x:= by
  simp only [liftRingHom, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
  rw [← evalₐ_of_apply I n]
  simp

@[simp]
theorem mk_comp_liftRingHom (n : ℕ) :
    (Ideal.Quotient.mk (I ^ n)).comp (liftRingHom I f hf) = f n := by
  ext; simp

/--
Uniqueness of the lift.
Given a compatible family of linear maps `f n : R →ₗ[R] S ⧸ (I ^ n)`.
If `F : R →+* S` makes the following diagram commutes
```
  R
  | \
 F|  \ f n
  |   \
  v    v
  S --> S ⧸ (I ^ n)
```
Then it is the map `IsAdicComplete.lift`.
-/
theorem eq_liftRingHom (F : R →+* S)
    (hF : ∀ {n x}, Ideal.Quotient.mk (I ^ n) (F x) = f n x) :
    F = liftRingHom I f hf := by
  ext x
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  simp only [smul_eq_mul, mul_top]
  simp [SModEq, liftRingHom, hF]

end

namespace StrictMono

variable {a : ℕ → ℕ} (ha : StrictMono a)
    (f : (n : ℕ) → R →+* S ⧸ I ^ a n)

variable {I M}
/--
Instead of providing all `R →+* S ⧸ I ^ n`, one can just provide
`R →+* S ⧸ I ^ a n` for a strictly increasing sequence `a n` to recover all
`R →+* S ⧸ I ^ n`. `RingHom` variant of `IsAdicComplete.StrictMono.extend`.
-/
def extendRingHom (n : ℕ) :
    R →+* S ⧸ I ^ n :=
  (factorPow I (ha.id_le n)).comp (f n)

variable (hf : ∀ {m}, (factorPow I (ha.monotone m.le_succ)).comp (f (m + 1)) = f m)

include hf in
/--
`RingHom` variant of `IsAdicComplete.StrictMono.factorPow_comp_eq_of_factorPow_comp_succ_eq`.
-/
theorem factorPow_comp_eq_of_factorPow_comp_succ_eq'
    {m n : ℕ} (hle : m ≤ n) : (factorPow I (ha.monotone hle)).comp (f n) = f m := by
  ext x
  symm
  refine Submodule.eq_factor_of_eq_factor_succ ?_ (fun n ↦ f n x) ?_ m n hle
  · exact fun _ _ le ↦ Ideal.pow_le_pow_right (ha.monotone le)
  · intro s
    simp only [RingHom.ext_iff] at hf
    simpa using (hf x).symm

include hf in
theorem extendRingHom_eq (n : ℕ) : extendRingHom ha f (a n) = f n :=
  factorPow_comp_eq_of_factorPow_comp_succ_eq' ha f hf (ha.id_le n)

include hf in
theorem factorPow_comp_extendRingHom {m n : ℕ} (hle : m ≤ n) :
    (factorPow I hle).comp (extendRingHom ha f n) = extendRingHom ha f m := by
  ext
  simp [extendRingHom, ← factorPow_comp_eq_of_factorPow_comp_succ_eq' ha f hf hle]

variable [IsAdicComplete I S]

variable (I)
/--
A variant of `IsAdicComplete.liftRingHom`. Only takes `f n : R →+* S ⧸ I ^ (a n)`
from a strictly increasing sequence `a n`.
-/
noncomputable def liftRingHom : R →+* S :=
  IsAdicComplete.liftRingHom I (extendRingHom ha f) (factorPow_comp_extendRingHom ha f hf)

theorem of_liftRingHom_apply (x : R) :
    of I S (liftRingHom I ha f hf x) =
    AdicCompletion.liftRingHom I (extendRingHom ha f) (factorPow_comp_extendRingHom ha f hf) x :=
  IsAdicComplete.of_liftRingHom_apply I (extendRingHom ha f)
      (factorPow_comp_extendRingHom ha f hf) x

theorem ofAlgEquiv_comp_liftRingHom :
    (ofAlgEquiv I : _ →+* _).comp (liftRingHom I ha f hf) =
      AdicCompletion.liftRingHom I (extendRingHom ha f) (factorPow_comp_extendRingHom ha f hf) :=
  IsAdicComplete.ofAlgEquiv_comp_liftRingHom I (extendRingHom ha f)
      (factorPow_comp_extendRingHom ha f hf)

@[simp]
theorem mk_liftRingHom_apply {n : ℕ} (x : R) :
    (Ideal.Quotient.mk _ (liftRingHom I ha f hf x)) = f n x := by
  simp [liftRingHom, IsAdicComplete.liftRingHom, extendRingHom_eq ha f hf]

@[simp]
theorem mk_comp_liftRingHom {n : ℕ} :
    (Ideal.Quotient.mk (I ^ (a n))).comp (liftRingHom I ha f hf) = f n := by
  ext; simp

theorem eq_liftRingHom {F : R →+* S}
    (hF : ∀ {m s}, Ideal.Quotient.mk _ (F s) = f m s) : F = liftRingHom I ha f hf := by
  ext s
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  simp only [smul_eq_mul, mul_top]
  apply SModEq.mono (Ideal.pow_le_pow_right (ha.id_le n))
  simp [SModEq, hF, mk_liftRingHom_apply I ha f hf]

end StrictMono

end IsAdicComplete
