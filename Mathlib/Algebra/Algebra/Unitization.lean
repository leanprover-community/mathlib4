/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux

! This file was ported from Lean 3 source module algebra.algebra.unitization
! leanprover-community/mathlib commit 8f66240cab125b938b327d3850169d490cfbcdd8
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Basic
import Mathbin.LinearAlgebra.Prod
import Mathbin.Algebra.Hom.NonUnitalAlg

/-!
# Unitization of a non-unital algebra

Given a non-unital `R`-algebra `A` (given via the type classes
`[non_unital_ring A] [module R A] [smul_comm_class R A A] [is_scalar_tower R A A]`) we construct
the minimal unital `R`-algebra containing `A` as an ideal. This object `algebra.unitization R A` is
a type synonym for `R × A` on which we place a different multiplicative structure, namely,
`(r₁, a₁) * (r₂, a₂) = (r₁ * r₂, r₁ • a₂ + r₂ • a₁ + a₁ * a₂)` where the multiplicative identity
is `(1, 0)`.

Note, when `A` is a *unital* `R`-algebra, then `unitization R A` constructs a new multiplicative
identity different from the old one, and so in general `unitization R A` and `A` will not be
isomorphic even in the unital case. This approach actually has nice functorial properties.

There is a natural coercion from `A` to `unitization R A` given by `λ a, (0, a)`, the image
of which is a proper ideal (TODO), and when `R` is a field this ideal is maximal. Moreover,
this ideal is always an essential ideal (it has nontrivial intersection with every other nontrivial
ideal).

Every non-unital algebra homomorphism from `A` into a *unital* `R`-algebra `B` has a unique
extension to a (unital) algebra homomorphism from `unitization R A` to `B`.

## Main definitions

* `unitization R A`: the unitization of a non-unital `R`-algebra `A`.
* `unitization.algebra`: the unitization of `A` as a (unital) `R`-algebra.
* `unitization.coe_non_unital_alg_hom`: coercion as a non-unital algebra homomorphism.
* `non_unital_alg_hom.to_alg_hom φ`: the extension of a non-unital algebra homomorphism `φ : A → B`
  into a unital `R`-algebra `B` to an algebra homomorphism `unitization R A →ₐ[R] B`.

## Main results

* `non_unital_alg_hom.to_alg_hom_unique`: the extension is unique

## TODO

* prove the unitization operation is a functor between the appropriate categories
* prove the image of the coercion is an essential ideal, maximal if scalars are a field.
-/


/-- The minimal unitization of a non-unital `R`-algebra `A`. This is just a type synonym for
`R × A`.-/
def Unitization (R A : Type _) :=
  R × A
#align unitization Unitization

namespace Unitization

section Basic

variable {R A : Type _}

/-- The canonical inclusion `R → unitization R A`. -/
def inl [Zero A] (r : R) : Unitization R A :=
  (r, 0)
#align unitization.inl Unitization.inl

/-- The canonical inclusion `A → unitization R A`. -/
instance [Zero R] : CoeTC A (Unitization R A) where coe a := (0, a)

/-- The canonical projection `unitization R A → R`. -/
def fst (x : Unitization R A) : R :=
  x.1
#align unitization.fst Unitization.fst

/-- The canonical projection `unitization R A → A`. -/
def snd (x : Unitization R A) : A :=
  x.2
#align unitization.snd Unitization.snd

@[ext]
theorem ext {x y : Unitization R A} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y :=
  Prod.ext h1 h2
#align unitization.ext Unitization.ext

section

variable (A)

@[simp]
theorem fst_inl [Zero A] (r : R) : (inl r : Unitization R A).fst = r :=
  rfl
#align unitization.fst_inl Unitization.fst_inl

@[simp]
theorem snd_inl [Zero A] (r : R) : (inl r : Unitization R A).snd = 0 :=
  rfl
#align unitization.snd_inl Unitization.snd_inl

end

section

variable (R)

@[simp]
theorem fst_coe [Zero R] (a : A) : (a : Unitization R A).fst = 0 :=
  rfl
#align unitization.fst_coe Unitization.fst_coe

@[simp]
theorem snd_coe [Zero R] (a : A) : (a : Unitization R A).snd = a :=
  rfl
#align unitization.snd_coe Unitization.snd_coe

end

theorem inl_injective [Zero A] : Function.Injective (inl : R → Unitization R A) :=
  Function.LeftInverse.injective <| fst_inl _
#align unitization.inl_injective Unitization.inl_injective

theorem coe_injective [Zero R] : Function.Injective (coe : A → Unitization R A) :=
  Function.LeftInverse.injective <| snd_coe _
#align unitization.coe_injective Unitization.coe_injective

end Basic

/-! ### Structures inherited from `prod`

Additive operators and scalar multiplication operate elementwise. -/


section Additive

variable {T : Type _} {S : Type _} {R : Type _} {A : Type _}

instance [Inhabited R] [Inhabited A] : Inhabited (Unitization R A) :=
  Prod.inhabited

instance [Zero R] [Zero A] : Zero (Unitization R A) :=
  Prod.hasZero

instance [Add R] [Add A] : Add (Unitization R A) :=
  Prod.hasAdd

instance [Neg R] [Neg A] : Neg (Unitization R A) :=
  Prod.hasNeg

instance [AddSemigroup R] [AddSemigroup A] : AddSemigroup (Unitization R A) :=
  Prod.addSemigroup

instance [AddZeroClass R] [AddZeroClass A] : AddZeroClass (Unitization R A) :=
  Prod.addZeroClass

instance [AddMonoid R] [AddMonoid A] : AddMonoid (Unitization R A) :=
  Prod.addMonoid

instance [AddGroup R] [AddGroup A] : AddGroup (Unitization R A) :=
  Prod.addGroup

instance [AddCommSemigroup R] [AddCommSemigroup A] : AddCommSemigroup (Unitization R A) :=
  Prod.addCommSemigroup

instance [AddCommMonoid R] [AddCommMonoid A] : AddCommMonoid (Unitization R A) :=
  Prod.addCommMonoid

instance [AddCommGroup R] [AddCommGroup A] : AddCommGroup (Unitization R A) :=
  Prod.addCommGroup

instance [SMul S R] [SMul S A] : SMul S (Unitization R A) :=
  Prod.smul

instance [SMul T R] [SMul T A] [SMul S R] [SMul S A] [SMul T S] [IsScalarTower T S R]
    [IsScalarTower T S A] : IsScalarTower T S (Unitization R A) :=
  Prod.isScalarTower

instance [SMul T R] [SMul T A] [SMul S R] [SMul S A] [SMulCommClass T S R] [SMulCommClass T S A] :
    SMulCommClass T S (Unitization R A) :=
  Prod.sMulCommClass

instance [SMul S R] [SMul S A] [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ A] [IsCentralScalar S R]
    [IsCentralScalar S A] : IsCentralScalar S (Unitization R A) :=
  Prod.isCentralScalar

instance [Monoid S] [MulAction S R] [MulAction S A] : MulAction S (Unitization R A) :=
  Prod.mulAction

instance [Monoid S] [AddMonoid R] [AddMonoid A] [DistribMulAction S R] [DistribMulAction S A] :
    DistribMulAction S (Unitization R A) :=
  Prod.distribMulAction

instance [Semiring S] [AddCommMonoid R] [AddCommMonoid A] [Module S R] [Module S A] :
    Module S (Unitization R A) :=
  Prod.module

@[simp]
theorem fst_zero [Zero R] [Zero A] : (0 : Unitization R A).fst = 0 :=
  rfl
#align unitization.fst_zero Unitization.fst_zero

@[simp]
theorem snd_zero [Zero R] [Zero A] : (0 : Unitization R A).snd = 0 :=
  rfl
#align unitization.snd_zero Unitization.snd_zero

@[simp]
theorem fst_add [Add R] [Add A] (x₁ x₂ : Unitization R A) : (x₁ + x₂).fst = x₁.fst + x₂.fst :=
  rfl
#align unitization.fst_add Unitization.fst_add

@[simp]
theorem snd_add [Add R] [Add A] (x₁ x₂ : Unitization R A) : (x₁ + x₂).snd = x₁.snd + x₂.snd :=
  rfl
#align unitization.snd_add Unitization.snd_add

@[simp]
theorem fst_neg [Neg R] [Neg A] (x : Unitization R A) : (-x).fst = -x.fst :=
  rfl
#align unitization.fst_neg Unitization.fst_neg

@[simp]
theorem snd_neg [Neg R] [Neg A] (x : Unitization R A) : (-x).snd = -x.snd :=
  rfl
#align unitization.snd_neg Unitization.snd_neg

@[simp]
theorem fst_smul [SMul S R] [SMul S A] (s : S) (x : Unitization R A) : (s • x).fst = s • x.fst :=
  rfl
#align unitization.fst_smul Unitization.fst_smul

@[simp]
theorem snd_smul [SMul S R] [SMul S A] (s : S) (x : Unitization R A) : (s • x).snd = s • x.snd :=
  rfl
#align unitization.snd_smul Unitization.snd_smul

section

variable (A)

@[simp]
theorem inl_zero [Zero R] [Zero A] : (inl 0 : Unitization R A) = 0 :=
  rfl
#align unitization.inl_zero Unitization.inl_zero

@[simp]
theorem inl_add [Add R] [AddZeroClass A] (r₁ r₂ : R) :
    (inl (r₁ + r₂) : Unitization R A) = inl r₁ + inl r₂ :=
  ext rfl (add_zero 0).symm
#align unitization.inl_add Unitization.inl_add

@[simp]
theorem inl_neg [Neg R] [AddGroup A] (r : R) : (inl (-r) : Unitization R A) = -inl r :=
  ext rfl neg_zero.symm
#align unitization.inl_neg Unitization.inl_neg

@[simp]
theorem inl_smul [Monoid S] [AddMonoid A] [SMul S R] [DistribMulAction S A] (s : S) (r : R) :
    (inl (s • r) : Unitization R A) = s • inl r :=
  ext rfl (smul_zero s).symm
#align unitization.inl_smul Unitization.inl_smul

end

section

variable (R)

@[simp]
theorem coe_zero [Zero R] [Zero A] : ↑(0 : A) = (0 : Unitization R A) :=
  rfl
#align unitization.coe_zero Unitization.coe_zero

@[simp]
theorem coe_add [AddZeroClass R] [Add A] (m₁ m₂ : A) : (↑(m₁ + m₂) : Unitization R A) = m₁ + m₂ :=
  ext (add_zero 0).symm rfl
#align unitization.coe_add Unitization.coe_add

@[simp]
theorem coe_neg [AddGroup R] [Neg A] (m : A) : (↑(-m) : Unitization R A) = -m :=
  ext neg_zero.symm rfl
#align unitization.coe_neg Unitization.coe_neg

@[simp]
theorem coe_smul [Zero R] [Zero S] [SMulWithZero S R] [SMul S A] (r : S) (m : A) :
    (↑(r • m) : Unitization R A) = r • m :=
  ext (smul_zero _).symm rfl
#align unitization.coe_smul Unitization.coe_smul

end

theorem inl_fst_add_coe_snd_eq [AddZeroClass R] [AddZeroClass A] (x : Unitization R A) :
    inl x.fst + ↑x.snd = x :=
  ext (add_zero x.1) (zero_add x.2)
#align unitization.inl_fst_add_coe_snd_eq Unitization.inl_fst_add_coe_snd_eq

/-- To show a property hold on all `unitization R A` it suffices to show it holds
on terms of the form `inl r + a`.

This can be used as `induction x using unitization.ind`. -/
theorem ind {R A} [AddZeroClass R] [AddZeroClass A] {P : Unitization R A → Prop}
    (h : ∀ (r : R) (a : A), P (inl r + a)) (x) : P x :=
  inl_fst_add_coe_snd_eq x ▸ h x.1 x.2
#align unitization.ind Unitization.ind

/-- This cannot be marked `@[ext]` as it ends up being used instead of `linear_map.prod_ext` when
working with `R × A`. -/
theorem linearMap_ext {N} [Semiring S] [AddCommMonoid R] [AddCommMonoid A] [AddCommMonoid N]
    [Module S R] [Module S A] [Module S N] ⦃f g : Unitization R A →ₗ[S] N⦄
    (hl : ∀ r, f (inl r) = g (inl r)) (hr : ∀ a : A, f a = g a) : f = g :=
  LinearMap.prod_ext (LinearMap.ext hl) (LinearMap.ext hr)
#align unitization.linear_map_ext Unitization.linearMap_ext

variable (R A)

/-- The canonical `R`-linear inclusion `A → unitization R A`. -/
@[simps apply]
def coeHom [Semiring R] [AddCommMonoid A] [Module R A] : A →ₗ[R] Unitization R A :=
  { LinearMap.inr R R A with toFun := coe }
#align unitization.coe_hom Unitization.coeHom

/-- The canonical `R`-linear projection `unitization R A → A`. -/
@[simps apply]
def sndHom [Semiring R] [AddCommMonoid A] [Module R A] : Unitization R A →ₗ[R] A :=
  { LinearMap.snd _ _ _ with toFun := snd }
#align unitization.snd_hom Unitization.sndHom

end Additive

/-! ### Multiplicative structure -/


section Mul

variable {R A : Type _}

instance [One R] [Zero A] : One (Unitization R A) :=
  ⟨(1, 0)⟩

instance [Mul R] [Add A] [Mul A] [SMul R A] : Mul (Unitization R A) :=
  ⟨fun x y => (x.1 * y.1, x.1 • y.2 + y.1 • x.2 + x.2 * y.2)⟩

@[simp]
theorem fst_one [One R] [Zero A] : (1 : Unitization R A).fst = 1 :=
  rfl
#align unitization.fst_one Unitization.fst_one

@[simp]
theorem snd_one [One R] [Zero A] : (1 : Unitization R A).snd = 0 :=
  rfl
#align unitization.snd_one Unitization.snd_one

@[simp]
theorem fst_mul [Mul R] [Add A] [Mul A] [SMul R A] (x₁ x₂ : Unitization R A) :
    (x₁ * x₂).fst = x₁.fst * x₂.fst :=
  rfl
#align unitization.fst_mul Unitization.fst_mul

@[simp]
theorem snd_mul [Mul R] [Add A] [Mul A] [SMul R A] (x₁ x₂ : Unitization R A) :
    (x₁ * x₂).snd = x₁.fst • x₂.snd + x₂.fst • x₁.snd + x₁.snd * x₂.snd :=
  rfl
#align unitization.snd_mul Unitization.snd_mul

section

variable (A)

@[simp]
theorem inl_one [One R] [Zero A] : (inl 1 : Unitization R A) = 1 :=
  rfl
#align unitization.inl_one Unitization.inl_one

@[simp]
theorem inl_mul [Monoid R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A] (r₁ r₂ : R) :
    (inl (r₁ * r₂) : Unitization R A) = inl r₁ * inl r₂ :=
  ext rfl <|
    show (0 : A) = r₁ • (0 : A) + r₂ • 0 + 0 * 0 by
      simp only [smul_zero, add_zero, MulZeroClass.mul_zero]
#align unitization.inl_mul Unitization.inl_mul

theorem inl_mul_inl [Monoid R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A] (r₁ r₂ : R) :
    (inl r₁ * inl r₂ : Unitization R A) = inl (r₁ * r₂) :=
  (inl_mul A r₁ r₂).symm
#align unitization.inl_mul_inl Unitization.inl_mul_inl

end

section

variable (R)

@[simp]
theorem coe_mul [Semiring R] [AddCommMonoid A] [Mul A] [SMulWithZero R A] (a₁ a₂ : A) :
    (↑(a₁ * a₂) : Unitization R A) = a₁ * a₂ :=
  ext (MulZeroClass.mul_zero _).symm <|
    show a₁ * a₂ = (0 : R) • a₂ + (0 : R) • a₁ + a₁ * a₂ by simp only [zero_smul, zero_add]
#align unitization.coe_mul Unitization.coe_mul

end

theorem inl_mul_coe [Semiring R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A] (r : R)
    (a : A) : (inl r * a : Unitization R A) = ↑(r • a) :=
  ext (MulZeroClass.mul_zero r) <|
    show r • a + (0 : R) • 0 + 0 * a = r • a by
      rw [smul_zero, add_zero, MulZeroClass.zero_mul, add_zero]
#align unitization.inl_mul_coe Unitization.inl_mul_coe

theorem coe_mul_inl [Semiring R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A] (r : R)
    (a : A) : (a * inl r : Unitization R A) = ↑(r • a) :=
  ext (MulZeroClass.zero_mul r) <|
    show (0 : R) • 0 + r • a + a * 0 = r • a by
      rw [smul_zero, zero_add, MulZeroClass.mul_zero, add_zero]
#align unitization.coe_mul_inl Unitization.coe_mul_inl

instance mulOneClass [Monoid R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A] :
    MulOneClass (Unitization R A) :=
  { Unitization.hasOne,
    Unitization.hasMul with
    one_mul := fun x =>
      ext (one_mul x.1) <|
        show (1 : R) • x.2 + x.1 • 0 + 0 * x.2 = x.2 by
          rw [one_smul, smul_zero, add_zero, MulZeroClass.zero_mul, add_zero]
    mul_one := fun x =>
      ext (mul_one x.1) <|
        show (x.1 • 0 : A) + (1 : R) • x.2 + x.2 * 0 = x.2 by
          rw [smul_zero, zero_add, one_smul, MulZeroClass.mul_zero, add_zero] }
#align unitization.mul_one_class Unitization.mulOneClass

instance [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] :
    NonAssocSemiring (Unitization R A) :=
  { Unitization.mulOneClass,
    Unitization.addCommMonoid with
    zero_mul := fun x =>
      ext (MulZeroClass.zero_mul x.1) <|
        show (0 : R) • x.2 + x.1 • 0 + 0 * x.2 = 0 by
          rw [zero_smul, zero_add, smul_zero, MulZeroClass.zero_mul, add_zero]
    mul_zero := fun x =>
      ext (MulZeroClass.mul_zero x.1) <|
        show (x.1 • 0 : A) + (0 : R) • x.2 + x.2 * 0 = 0 by
          rw [smul_zero, zero_add, zero_smul, MulZeroClass.mul_zero, add_zero]
    left_distrib := fun x₁ x₂ x₃ =>
      ext (mul_add x₁.1 x₂.1 x₃.1) <|
        show
          x₁.1 • (x₂.2 + x₃.2) + (x₂.1 + x₃.1) • x₁.2 + x₁.2 * (x₂.2 + x₃.2) =
            x₁.1 • x₂.2 + x₂.1 • x₁.2 + x₁.2 * x₂.2 + (x₁.1 • x₃.2 + x₃.1 • x₁.2 + x₁.2 * x₃.2)
          by
          simp only [smul_add, add_smul, mul_add]
          abel
    right_distrib := fun x₁ x₂ x₃ =>
      ext (add_mul x₁.1 x₂.1 x₃.1) <|
        show
          (x₁.1 + x₂.1) • x₃.2 + x₃.1 • (x₁.2 + x₂.2) + (x₁.2 + x₂.2) * x₃.2 =
            x₁.1 • x₃.2 + x₃.1 • x₁.2 + x₁.2 * x₃.2 + (x₂.1 • x₃.2 + x₃.1 • x₂.2 + x₂.2 * x₃.2)
          by
          simp only [add_smul, smul_add, add_mul]
          abel }

instance [CommMonoid R] [NonUnitalSemiring A] [DistribMulAction R A] [IsScalarTower R A A]
    [SMulCommClass R A A] : Monoid (Unitization R A) :=
  { Unitization.mulOneClass with
    mul_assoc := fun x y z =>
      ext (mul_assoc x.1 y.1 z.1) <|
        show
          (x.1 * y.1) • z.2 + z.1 • (x.1 • y.2 + y.1 • x.2 + x.2 * y.2) +
              (x.1 • y.2 + y.1 • x.2 + x.2 * y.2) * z.2 =
            x.1 • (y.1 • z.2 + z.1 • y.2 + y.2 * z.2) + (y.1 * z.1) • x.2 +
              x.2 * (y.1 • z.2 + z.1 • y.2 + y.2 * z.2)
          by
          simp only [smul_add, mul_add, add_mul, smul_smul, smul_mul_assoc, mul_smul_comm,
            mul_assoc]
          nth_rw 2 [mul_comm]
          nth_rw 3 [mul_comm]
          abel }

instance [CommMonoid R] [NonUnitalCommSemiring A] [DistribMulAction R A] [IsScalarTower R A A]
    [SMulCommClass R A A] : CommMonoid (Unitization R A) :=
  { Unitization.monoid with
    mul_comm := fun x₁ x₂ =>
      ext (mul_comm x₁.1 x₂.1) <|
        show x₁.1 • x₂.2 + x₂.1 • x₁.2 + x₁.2 * x₂.2 = x₂.1 • x₁.2 + x₁.1 • x₂.2 + x₂.2 * x₁.2 by
          rw [add_comm (x₁.1 • x₂.2), mul_comm] }

instance [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] : Semiring (Unitization R A) :=
  { Unitization.monoid, Unitization.nonAssocSemiring with }

instance [CommSemiring R] [NonUnitalCommSemiring A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] : CommSemiring (Unitization R A) :=
  { Unitization.commMonoid, Unitization.nonAssocSemiring with }

variable (R A)

/-- The canonical inclusion of rings `R →+* unitization R A`. -/
@[simps apply]
def inlRingHom [Semiring R] [NonUnitalSemiring A] [Module R A] : R →+* Unitization R A
    where
  toFun := inl
  map_one' := inl_one A
  map_mul' := inl_mul A
  map_zero' := inl_zero A
  map_add' := inl_add A
#align unitization.inl_ring_hom Unitization.inlRingHom

end Mul

/-! ### Star structure -/


section Star

variable {R A : Type _}

instance [Star R] [Star A] : Star (Unitization R A) :=
  ⟨fun ra => (star ra.fst, star ra.snd)⟩

@[simp]
theorem fst_star [Star R] [Star A] (x : Unitization R A) : (star x).fst = star x.fst :=
  rfl
#align unitization.fst_star Unitization.fst_star

@[simp]
theorem snd_star [Star R] [Star A] (x : Unitization R A) : (star x).snd = star x.snd :=
  rfl
#align unitization.snd_star Unitization.snd_star

@[simp]
theorem inl_star [Star R] [AddMonoid A] [StarAddMonoid A] (r : R) :
    inl (star r) = star (inl r : Unitization R A) :=
  ext rfl (by simp only [snd_star, star_zero, snd_inl])
#align unitization.inl_star Unitization.inl_star

@[simp]
theorem coe_star [AddMonoid R] [StarAddMonoid R] [Star A] (a : A) :
    ↑(star a) = star (a : Unitization R A) :=
  ext (by simp only [fst_star, star_zero, fst_coe]) rfl
#align unitization.coe_star Unitization.coe_star

instance [AddMonoid R] [AddMonoid A] [StarAddMonoid R] [StarAddMonoid A] :
    StarAddMonoid (Unitization R A)
    where
  star_involutive x := ext (star_star x.fst) (star_star x.snd)
  star_add x y := ext (star_add x.fst y.fst) (star_add x.snd y.snd)

instance [CommSemiring R] [StarRing R] [AddCommMonoid A] [StarAddMonoid A] [Module R A]
    [StarModule R A] : StarModule R (Unitization R A) where star_smul r x := ext (by simp) (by simp)

instance [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [StarRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A] : StarRing (Unitization R A) :=
  { Unitization.starAddMonoid with
    star_mul := fun x y =>
      ext (by simp [star_mul]) (by simp [star_mul, add_comm (star x.fst • star y.snd)]) }

end Star

/-! ### Algebra structure -/


section Algebra

variable (S R A : Type _) [CommSemiring S] [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [Algebra S R] [DistribMulAction S A]
  [IsScalarTower S R A]

instance algebra : Algebra S (Unitization R A) :=
  {
    (Unitization.inlRingHom R A).comp
      (algebraMap S
        R) with
    commutes' := fun r x => by
      induction x using Unitization.ind
      simp only [mul_add, add_mul, RingHom.toFun_eq_coe, RingHom.coe_comp, Function.comp_apply,
        inl_ring_hom_apply, inl_mul_inl]
      rw [inl_mul_coe, coe_mul_inl, mul_comm]
    smul_def' := fun s x => by
      induction x using Unitization.ind
      simp only [mul_add, smul_add, RingHom.toFun_eq_coe, RingHom.coe_comp, Function.comp_apply,
        inl_ring_hom_apply, Algebra.algebraMap_eq_smul_one]
      rw [inl_mul_inl, inl_mul_coe, smul_one_mul, inl_smul, coe_smul, smul_one_smul] }
#align unitization.algebra Unitization.algebra

theorem algebraMap_eq_inl_comp : ⇑(algebraMap S (Unitization R A)) = inl ∘ algebraMap S R :=
  rfl
#align unitization.algebra_map_eq_inl_comp Unitization.algebraMap_eq_inl_comp

theorem algebraMap_eq_inlRingHom_comp :
    algebraMap S (Unitization R A) = (inlRingHom R A).comp (algebraMap S R) :=
  rfl
#align unitization.algebra_map_eq_inl_ring_hom_comp Unitization.algebraMap_eq_inlRingHom_comp

theorem algebraMap_eq_inl : ⇑(algebraMap R (Unitization R A)) = inl :=
  rfl
#align unitization.algebra_map_eq_inl Unitization.algebraMap_eq_inl

theorem algebraMap_eq_inl_hom : algebraMap R (Unitization R A) = inlRingHom R A :=
  rfl
#align unitization.algebra_map_eq_inl_hom Unitization.algebraMap_eq_inl_hom

/-- The canonical `R`-algebra projection `unitization R A → R`. -/
@[simps]
def fstHom : Unitization R A →ₐ[R] R where
  toFun := fst
  map_one' := fst_one
  map_mul' := fst_mul
  map_zero' := fst_zero
  map_add' := fst_add
  commutes' := fst_inl A
#align unitization.fst_hom Unitization.fstHom

end Algebra

section coe

/-- The coercion from a non-unital `R`-algebra `A` to its unitization `unitization R A`
realized as a non-unital algebra homomorphism. -/
@[simps]
def coeNonUnitalAlgHom (R A : Type _) [CommSemiring R] [NonUnitalSemiring A] [Module R A] :
    A →ₙₐ[R] Unitization R A where
  toFun := coe
  map_smul' := coe_smul R
  map_zero' := coe_zero R
  map_add' := coe_add R
  map_mul' := coe_mul R
#align unitization.coe_non_unital_alg_hom Unitization.coeNonUnitalAlgHom

end coe

section AlgHom

variable {S R A : Type _} [CommSemiring S] [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A] {B : Type _} [Semiring B] [Algebra S B] [Algebra S R]
  [DistribMulAction S A] [IsScalarTower S R A] {C : Type _} [Ring C] [Algebra R C]

theorem algHom_ext {φ ψ : Unitization R A →ₐ[S] B} (h : ∀ a : A, φ a = ψ a)
    (h' : ∀ r, φ (algebraMap R (Unitization R A) r) = ψ (algebraMap R (Unitization R A) r)) :
    φ = ψ := by
  ext
  induction x using Unitization.ind
  simp only [map_add, ← algebra_map_eq_inl, h, h']
#align unitization.alg_hom_ext Unitization.algHom_ext

/-- See note [partially-applied ext lemmas] -/
@[ext]
theorem algHom_ext' {φ ψ : Unitization R A →ₐ[R] C}
    (h :
      φ.toNonUnitalAlgHom.comp (coeNonUnitalAlgHom R A) =
        ψ.toNonUnitalAlgHom.comp (coeNonUnitalAlgHom R A)) :
    φ = ψ :=
  algHom_ext (NonUnitalAlgHom.congr_fun h) (by simp [AlgHom.commutes])
#align unitization.alg_hom_ext' Unitization.algHom_ext'

/-- Non-unital algebra homomorphisms from `A` into a unital `R`-algebra `C` lift uniquely to
`unitization R A →ₐ[R] C`. This is the universal property of the unitization. -/
@[simps apply_apply]
def lift : (A →ₙₐ[R] C) ≃ (Unitization R A →ₐ[R] C)
    where
  toFun φ :=
    { toFun := fun x => algebraMap R C x.fst + φ x.snd
      map_one' := by simp only [fst_one, map_one, snd_one, φ.map_zero, add_zero]
      map_mul' := fun x y => by
        induction x using Unitization.ind
        induction y using Unitization.ind
        simp only [mul_add, add_mul, coe_mul, fst_add, fst_mul, fst_inl, fst_coe,
          MulZeroClass.mul_zero, add_zero, MulZeroClass.zero_mul, map_mul, snd_add, snd_mul,
          snd_inl, smul_zero, snd_coe, zero_add, φ.map_add, φ.map_smul, φ.map_mul, zero_smul,
          zero_add]
        rw [← Algebra.commutes _ (φ x_a)]
        simp only [Algebra.algebraMap_eq_smul_one, smul_one_mul, add_assoc]
      map_zero' := by simp only [fst_zero, map_zero, snd_zero, φ.map_zero, add_zero]
      map_add' := fun x y => by
        induction x using Unitization.ind
        induction y using Unitization.ind
        simp only [fst_add, fst_inl, fst_coe, add_zero, map_add, snd_add, snd_inl, snd_coe,
          zero_add, φ.map_add]
        rw [add_add_add_comm]
      commutes' := fun r => by
        simp only [algebra_map_eq_inl, fst_inl, snd_inl, φ.map_zero, add_zero] }
  invFun φ := φ.toNonUnitalAlgHom.comp (coeNonUnitalAlgHom R A)
  left_inv φ := by
    ext
    simp
  right_inv φ :=
    Unitization.algHom_ext'
      (by
        ext
        simp)
#align unitization.lift Unitization.lift

theorem lift_symm_apply (φ : Unitization R A →ₐ[R] C) (a : A) : Unitization.lift.symm φ a = φ a :=
  rfl
#align unitization.lift_symm_apply Unitization.lift_symm_apply

end AlgHom

end Unitization

