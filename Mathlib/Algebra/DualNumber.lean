/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.TrivSqZeroExt

#align_import algebra.dual_number from "leanprover-community/mathlib"@"b8d2eaa69d69ce8f03179a5cda774fc0cde984e4"

/-!
# Dual numbers

The dual numbers over `R` are of the form `a + bε`, where `a` and `b` are typically elements of a
commutative ring `R`, and `ε` is a symbol satisfying `ε^2 = 0` that commutes with every other
element. They are a special case of `TrivSqZeroExt R M` with `M = R`.

## Notation

In the `DualNumber` locale:

* `R[ε]` is a shorthand for `DualNumber R`
* `ε` is a shorthand for `DualNumber.eps`

## Main definitions

* `DualNumber`
* `DualNumber.eps`
* `DualNumber.lift`

## Implementation notes

Rather than duplicating the API of `TrivSqZeroExt`, this file reuses the functions there.

## References

* https://en.wikipedia.org/wiki/Dual_number
-/


variable {R A B : Type*}

/-- The type of dual numbers, numbers of the form $a + bε$ where $ε^2 = 0$.-/
abbrev DualNumber (R : Type*) : Type _ :=
  TrivSqZeroExt R R
#align dual_number DualNumber

/-- The unit element $ε$ that squares to zero. -/
def DualNumber.eps [Zero R] [One R] : DualNumber R :=
  TrivSqZeroExt.inr 1
#align dual_number.eps DualNumber.eps

-- mathport name: dual_number.eps
scoped[DualNumber] notation "ε" => DualNumber.eps

-- mathport name: dual_number
scoped[DualNumber] postfix:1024 "[ε]" => DualNumber

open DualNumber

namespace DualNumber

open TrivSqZeroExt

@[simp]
theorem fst_eps [Zero R] [One R] : fst ε = (0 : R) :=
  fst_inr _ _
#align dual_number.fst_eps DualNumber.fst_eps

@[simp]
theorem snd_eps [Zero R] [One R] : snd ε = (1 : R) :=
  snd_inr _ _
#align dual_number.snd_eps DualNumber.snd_eps

/-- A version of `TrivSqZeroExt.snd_mul` with `*` instead of `•`. -/
@[simp]
theorem snd_mul [Semiring R] (x y : R[ε]) : snd (x * y) = fst x * snd y + snd x * fst y :=
  TrivSqZeroExt.snd_mul _ _
#align dual_number.snd_mul DualNumber.snd_mul

@[simp]
theorem eps_mul_eps [Semiring R] : (ε * ε : R[ε]) = 0 :=
  inr_mul_inr _ _ _
#align dual_number.eps_mul_eps DualNumber.eps_mul_eps

@[simp]
theorem inr_eq_smul_eps [MulZeroOneClass R] (r : R) : inr r = (r • ε : R[ε]) :=
  ext (mul_zero r).symm (mul_one r).symm
#align dual_number.inr_eq_smul_eps DualNumber.inr_eq_smul_eps

/-- `ε` commutes with every element of the algebra. -/
theorem commute_eps_left [Semiring R] (x : DualNumber R) : Commute ε x := by
  ext <;> simp

/-- `ε` commutes with every element of the algebra. -/
theorem commute_eps_right [Semiring R] (x : DualNumber R) : Commute x ε := (commute_eps_left x).symm

/-- For two algebra morphisms out of `A[ε]` to agree, it suffices for them to agree on the elements
of `A` and the `A`-multiples of `ε`. -/
@[ext]
theorem algHom_ext {A} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    ⦃f g : A[ε] →ₐ[R] B⦄
    (hinl : f.comp (inlAlgHom _ _ _) = g.comp (inlAlgHom _ _ _))
    (hinr : f.toLinearMap ∘ₗ (LinearMap.toSpanSingleton A A[ε] ε).restrictScalars R =
        g.toLinearMap ∘ₗ (LinearMap.toSpanSingleton A A[ε] ε).restrictScalars R) :
      f = g :=
  algHom_ext' hinl (by
    ext a
    show f (inr a) = g (inr a)
    simpa only [inr_eq_smul_eps] using FunLike.congr_fun hinr a)
#align dual_number.alg_hom_ext DualNumber.algHom_ext

variable {A : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-- A universal property of the dual numbers, providing a unique `A[ε] →ₐ[R] B` for every map
`f : A →ₐ[R] B` and a choice of element `e : B` which squares to `0` and commutes with the range of
`f`.

This isomorphism is named to match the similar `Complex.lift`.
Note that when `f : R →ₐ[R] B := Algebra.ofId R B`, the commutativity assumption is automatic, and
we are free to choose any element `e : B`. -/
-- @[simps! apply_apply]
def lift :
    {fe : (A →ₐ[R] B) × B // fe.2 * fe.2 = 0 ∧ ∀ a, Commute fe.2 (fe.1 a)} ≃ (A[ε] →ₐ[R] B) := by
  refine Equiv.trans ?_ TrivSqZeroExt.liftEquiv
  exact {
    toFun := fun ⟨(f, e), he, hc⟩ => ⟨
      (f, MulOpposite.op e • f.toLinearMap),
      fun x y => show (f x * e) * (f y * e) = 0 by rw [(hc _).mul_mul_mul_comm, he, mul_zero],
      fun r x => show f (r * x) * e = f r * (f x * e) by rw [map_mul, mul_assoc],
      fun r x => show f (x * r) * e = (f x * e) * f r by rw [map_mul, (hc _).right_comm]⟩
    invFun := fun ⟨(f, g), hg, hfg, hgf⟩ => ⟨
      (f, g 1),
      hg _ _,
      fun a => show g 1 * f a = f a * g 1 by
        rw [←hfg, ←hgf, smul_eq_mul, op_smul_eq_mul, mul_one, one_mul]⟩
    left_inv := fun ⟨(f, e), he, hc⟩ => Subtype.ext <| Prod.ext rfl <|
      show f 1 * e = e by rw [map_one, one_mul]
    right_inv := fun ⟨(f, g), hg, hfg, hgf⟩ => Subtype.ext <| Prod.ext rfl <| LinearMap.ext fun x =>
      show f x * g 1 = g x by rw [← hfg, smul_eq_mul, mul_one] }
#align dual_number.lift DualNumber.lift

@[simp] theorem coe_lift_symm_apply (F : A[ε] →ₐ[R] B) :
    (lift.symm F).val = (F.comp (inlAlgHom _ _ _), F ε) := rfl

-- When applied to `ε`, `DualNumber.lift` produces the element of `B` that squares to 0.
theorem lift_apply_eps
    (fe : {fe : (A →ₐ[R] B) × B // fe.2 * fe.2 = 0 ∧ ∀ a, Commute fe.2 (fe.1 a)}) :
    lift fe (ε : A[ε]) = fe.val.2 := by
  simp only [lift_apply_apply, fst_eps, map_zero, snd_eps, map_one, one_mul, zero_add]
#align dual_number.lift_apply_eps DualNumber.lift_apply_eps

-- Lifting `DualNumber.eps` itself gives the identity.
@[simp]
theorem lift_inlAlgHom_eps :
    lift ⟨(inlAlgHom _ _ _, ε), eps_mul_eps, fun _ => commute_eps_left _⟩ = AlgHom.id R A[ε] :=
  lift.apply_symm_apply <| AlgHom.id R A[ε]
#align dual_number.lift_eps DualNumber.lift_inlAlgHom_epsₓ

end DualNumber
