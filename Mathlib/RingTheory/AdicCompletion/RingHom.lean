/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Lift of ring homomorphisms to adic completions
Let `R`, `S` be rings, `I` be an ideal of `S`.
In this file we prove that a compatible family of ring homomorphisms from a ring `R` to
`S ⧸ I ^ n` can be lifted to a ring homomorphism `R →+* AdicCompletion I S`.
If `S` is `I`-adically complete, then this compatible family of ring homomorphisms can be
lifted to a ring homomorphism `R →+* S`.

## Main definitions

- `IsAdicComplete.liftRingHom`: if `R` is
  `I`-adically complete, then a compatible family of
  ring maps `S →+* R ⧸ I ^ n` can be lifted to a unique ring map `S →+* R`.
  Together with `mk_liftRingHom_apply` and `eq_liftRingHom`, it gives the universal property
  of `R` being `I`-adically complete.
-/

@[expose] public section

open Ideal Quotient

variable {R S : Type*} [NonAssocSemiring R] [CommRing S] (I : Ideal S)

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
theorem of_liftRingHom (x : R) :
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
theorem mk_liftRingHom (n : ℕ) (x : R) :
    Ideal.Quotient.mk (I ^ n) (liftRingHom I f hf x) = f n x := by
  simp only [liftRingHom, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
  rw [← evalₐ_of I n]
  simp

@[simp]
theorem mk_comp_liftRingHom (n : ℕ) :
    (Ideal.Quotient.mk (I ^ n)).comp (liftRingHom I f hf) = f n := by
  ext; simp

/--
Uniqueness of the lift.
Given a compatible family of linear maps `f n : R →ₗ[R] S ⧸ (I ^ n)`.
If `F : R →+* S` makes the following diagram commute
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
    (hF : ∀ n, (Ideal.Quotient.mk (I ^ n)).comp F = f n) :
    F = liftRingHom I f hf := by
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' I
  intro n m
  simp [← hF n]

section

variable {R S A : Type*} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal S)
  [IsAdicComplete I S] [CommRing A] [Algebra R A]

/-- `AlgHom` version of `IsAdicCompletion.liftRingHom`. -/
noncomputable
def liftAlgHom (f : (n : ℕ) → A →ₐ[R] S ⧸ I ^ n)
    (hf : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp (f n) = f m) :
    A →ₐ[R] S :=
  ((ofAlgEquiv I).symm.toAlgHom.restrictScalars R).comp (AdicCompletion.liftAlgHom I f hf)

variable (f : (n : ℕ) → A →ₐ[R] S ⧸ I ^ n)
    (hf : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp (f n) = f m)

@[simp]
lemma mk_liftAlgHom (n : ℕ) (x : A) : liftAlgHom I f hf x = f n x := by
  simp [liftAlgHom]

@[simp]
lemma mkₐ_comp_liftAlgHom (n : ℕ) :
    (Ideal.Quotient.mkₐ R (I ^ n)).comp (liftAlgHom I f hf) = f n :=
  AlgHom.ext fun _ ↦ mk_liftAlgHom _ _ hf _ _

lemma algHom_ext {f g : A →ₐ[R] S}
    (H : ∀ n, (Ideal.Quotient.mkₐ R (I ^ n)).comp f = (Ideal.Quotient.mkₐ R (I ^ n)).comp g) :
    f = g := by
  rw [← AlgHom.cancel_left (f := ((ofAlgEquiv I).restrictScalars R).toAlgHom)
    (ofAlgEquiv I).injective]
  ext1 x
  refine AdicCompletion.ext_evalₐ fun n ↦ ?_
  simpa using congr($(H n) x)

end

end

namespace StrictMono

variable {a : ℕ → ℕ} (ha : StrictMono a) (f : (n : ℕ) → R →+* S ⧸ I ^ a n)
variable (hf : ∀ {m}, (factorPow I (ha.monotone m.le_succ)).comp (f (m + 1)) = f m)

variable {I}

include hf in
/--
`RingHom` variant of `IsAdicComplete.StrictMono.factorPow_comp_eq_of_factorPow_comp_succ_eq`.
-/
theorem factorPow_comp_eq_of_factorPow_comp_succ_eq'
    {m n : ℕ} (hle : m ≤ n) : (factorPow I (ha.monotone hle)).comp (f n) = f m := by
  ext x
  symm
  refine Submodule.eq_factor_of_eq_factor_succ ?_ (fun n ↦ f n x) ?_ hle
  · exact fun _ _ le ↦ Ideal.pow_le_pow_right (ha.monotone le)
  · intro s
    simp only [RingHom.ext_iff] at hf
    simpa using (hf x).symm

variable [IsAdicComplete I S]

variable (I)

set_option backward.isDefEq.respectTransparency false in
/--
A variant of `IsAdicComplete.liftRingHom`. Only takes `f n : R →+* S ⧸ I ^ (a n)`
from a strictly increasing sequence `a n`.
-/
noncomputable def liftRingHom : R →+* S :=
  IsAdicComplete.liftRingHom I (fun n ↦ (factorPow I (ha.id_le n)).comp (f n))
    (fun hle ↦ by ext; simp [← factorPow_comp_eq_of_factorPow_comp_succ_eq' ha f hf hle])

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem mk_liftRingHom {n : ℕ} (x : R) :
    Ideal.Quotient.mk _ (liftRingHom I ha f hf x) = f n x := by
  simp [liftRingHom, IsAdicComplete.liftRingHom,
      factorPow_comp_eq_of_factorPow_comp_succ_eq' ha f hf ha.le_apply]

@[simp]
theorem mk_comp_liftRingHom {n : ℕ} :
    (Ideal.Quotient.mk (I ^ (a n))).comp (liftRingHom I ha f hf) = f n := by
  ext; simp

theorem eq_liftRingHom {F : R →+* S}
    (hF : ∀ n, (Ideal.Quotient.mk _).comp F = f n) : F = liftRingHom I ha f hf := by
  apply DFunLike.coe_injective
  apply IsHausdorff.StrictMono.funext' I ha
  intro n m
  simp [← hF n]

end StrictMono

end IsAdicComplete
