/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.NonUnitalSubalgebra
import Mathlib.LinearAlgebra.Prod

#align_import algebra.algebra.unitization from "leanprover-community/mathlib"@"8f66240cab125b938b327d3850169d490cfbcdd8"

/-!
# Unitization of a non-unital algebra

Given a non-unital `R`-algebra `A` (given via the type classes
`[NonUnitalRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]`) we construct
the minimal unital `R`-algebra containing `A` as an ideal. This object `Unitization R A` is
a type synonym for `R × A` on which we place a different multiplicative structure, namely,
`(r₁, a₁) * (r₂, a₂) = (r₁ * r₂, r₁ • a₂ + r₂ • a₁ + a₁ * a₂)` where the multiplicative identity
is `(1, 0)`.

Note, when `A` is a *unital* `R`-algebra, then `Unitization R A` constructs a new multiplicative
identity different from the old one, and so in general `Unitization R A` and `A` will not be
isomorphic even in the unital case. This approach actually has nice functorial properties.

There is a natural coercion from `A` to `Unitization R A` given by `fun a ↦ (0, a)`, the image
of which is a proper ideal (TODO), and when `R` is a field this ideal is maximal. Moreover,
this ideal is always an essential ideal (it has nontrivial intersection with every other nontrivial
ideal).

Every non-unital algebra homomorphism from `A` into a *unital* `R`-algebra `B` has a unique
extension to a (unital) algebra homomorphism from `Unitization R A` to `B`.

## Main definitions

* `Unitization R A`: the unitization of a non-unital `R`-algebra `A`.
* `Unitization.algebra`: the unitization of `A` as a (unital) `R`-algebra.
* `Unitization.coeNonUnitalAlgHom`: coercion as a non-unital algebra homomorphism.
* `NonUnitalAlgHom.toAlgHom φ`: the extension of a non-unital algebra homomorphism `φ : A → B`
  into a unital `R`-algebra `B` to an algebra homomorphism `Unitization R A →ₐ[R] B`.
* `Unitization.lift`: the universal property of the unitization, the extension
  `NonUnitalAlgHom.toAlgHom` actually implements an equivalence
  `(A →ₙₐ[R] B) ≃ (Unitization R A ≃ₐ[R] B)`

## Main results

* `AlgHom.ext'`: an extensionality lemma for algebra homomorphisms whose domain is
  `Unitization R A`; it suffices that they agree on `A`.

## TODO

* prove the unitization operation is a functor between the appropriate categories
* prove the image of the coercion is an essential ideal, maximal if scalars are a field.
-/


/-- The minimal unitization of a non-unital `R`-algebra `A`. This is just a type synonym for
`R × A`. -/
def Unitization (R A : Type*) :=
  R × A
#align unitization Unitization

namespace Unitization

section Basic

variable {R A : Type*}

/-- The canonical inclusion `R → Unitization R A`. -/
def inl [Zero A] (r : R) : Unitization R A :=
  (r, 0)
#align unitization.inl Unitization.inl

-- Porting note: we need a def to which we can attach `@[coe]`
/-- The canonical inclusion `A → Unitization R A`. -/
@[coe]
def inr [Zero R] (a : A) : Unitization R A :=
  (0, a)

instance [Zero R] : CoeTC A (Unitization R A) where
  coe := inr

/-- The canonical projection `Unitization R A → R`. -/
def fst (x : Unitization R A) : R :=
  x.1
#align unitization.fst Unitization.fst

/-- The canonical projection `Unitization R A → A`. -/
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
theorem fst_inr [Zero R] (a : A) : (a : Unitization R A).fst = 0 :=
  rfl
#align unitization.fst_coe Unitization.fst_inr

@[simp]
theorem snd_inr [Zero R] (a : A) : (a : Unitization R A).snd = a :=
  rfl
#align unitization.snd_coe Unitization.snd_inr

end

theorem inl_injective [Zero A] : Function.Injective (inl : R → Unitization R A) :=
  Function.LeftInverse.injective <| fst_inl _
#align unitization.inl_injective Unitization.inl_injective

theorem inr_injective [Zero R] : Function.Injective ((↑) : A → Unitization R A) :=
  Function.LeftInverse.injective <| snd_inr _
#align unitization.coe_injective Unitization.inr_injective

instance instNontrivialLeft {𝕜 A} [Nontrivial 𝕜] [Nonempty A] :
    Nontrivial (Unitization 𝕜 A) :=
  nontrivial_prod_left

instance instNontrivialRight {𝕜 A} [Nonempty 𝕜] [Nontrivial A] :
    Nontrivial (Unitization 𝕜 A) :=
  nontrivial_prod_right

end Basic

/-! ### Structures inherited from `Prod`

Additive operators and scalar multiplication operate elementwise. -/


section Additive

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

instance instCanLift [Zero R] : CanLift (Unitization R A) A inr (fun x ↦ x.fst = 0) where
  prf x hx := ⟨x.snd, ext (hx ▸ fst_inr R (snd x)) rfl⟩

instance instInhabited [Inhabited R] [Inhabited A] : Inhabited (Unitization R A) :=
  instInhabitedProd

instance instZero [Zero R] [Zero A] : Zero (Unitization R A) :=
  Prod.instZero

instance instAdd [Add R] [Add A] : Add (Unitization R A) :=
  Prod.instAdd

instance instNeg [Neg R] [Neg A] : Neg (Unitization R A) :=
  Prod.instNeg

instance instAddSemigroup [AddSemigroup R] [AddSemigroup A] : AddSemigroup (Unitization R A) :=
  Prod.instAddSemigroup

instance instAddZeroClass [AddZeroClass R] [AddZeroClass A] : AddZeroClass (Unitization R A) :=
  Prod.instAddZeroClass

instance instAddMonoid [AddMonoid R] [AddMonoid A] : AddMonoid (Unitization R A) :=
  Prod.instAddMonoid

instance instAddGroup [AddGroup R] [AddGroup A] : AddGroup (Unitization R A) :=
  Prod.instAddGroup

instance instAddCommSemigroup [AddCommSemigroup R] [AddCommSemigroup A] :
    AddCommSemigroup (Unitization R A) :=
  Prod.instAddCommSemigroup

instance instAddCommMonoid [AddCommMonoid R] [AddCommMonoid A] : AddCommMonoid (Unitization R A) :=
  Prod.instAddCommMonoid

instance instAddCommGroup [AddCommGroup R] [AddCommGroup A] : AddCommGroup (Unitization R A) :=
  Prod.instAddCommGroup

instance instSMul [SMul S R] [SMul S A] : SMul S (Unitization R A) :=
  Prod.smul

instance instIsScalarTower [SMul T R] [SMul T A] [SMul S R] [SMul S A] [SMul T S]
    [IsScalarTower T S R] [IsScalarTower T S A] : IsScalarTower T S (Unitization R A) :=
  Prod.isScalarTower

instance instSMulCommClass [SMul T R] [SMul T A] [SMul S R] [SMul S A] [SMulCommClass T S R]
    [SMulCommClass T S A] : SMulCommClass T S (Unitization R A) :=
  Prod.smulCommClass

instance instIsCentralScalar [SMul S R] [SMul S A] [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ A] [IsCentralScalar S R]
    [IsCentralScalar S A] : IsCentralScalar S (Unitization R A) :=
  Prod.isCentralScalar

instance instMulAction [Monoid S] [MulAction S R] [MulAction S A] : MulAction S (Unitization R A) :=
  Prod.mulAction

instance instDistribMulAction [Monoid S] [AddMonoid R] [AddMonoid A] [DistribMulAction S R]
    [DistribMulAction S A] : DistribMulAction S (Unitization R A) :=
  Prod.distribMulAction

instance instModule [Semiring S] [AddCommMonoid R] [AddCommMonoid A] [Module S R] [Module S A] :
    Module S (Unitization R A) :=
  Prod.instModule

variable (R A) in
/-- The identity map between `Unitization R A` and `R × A` as an `AddEquiv`. -/
def addEquiv [Add R] [Add A] : Unitization R A ≃+ R × A :=
  AddEquiv.refl _

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
theorem inr_zero [Zero R] [Zero A] : ↑(0 : A) = (0 : Unitization R A) :=
  rfl
#align unitization.coe_zero Unitization.inr_zero

@[simp]
theorem inr_add [AddZeroClass R] [Add A] (m₁ m₂ : A) : (↑(m₁ + m₂) : Unitization R A) = m₁ + m₂ :=
  ext (add_zero 0).symm rfl
#align unitization.coe_add Unitization.inr_add

@[simp]
theorem inr_neg [AddGroup R] [Neg A] (m : A) : (↑(-m) : Unitization R A) = -m :=
  ext neg_zero.symm rfl
#align unitization.coe_neg Unitization.inr_neg

@[simp]
theorem inr_smul [Zero R] [Zero S] [SMulWithZero S R] [SMul S A] (r : S) (m : A) :
    (↑(r • m) : Unitization R A) = r • (m : Unitization R A) :=
  ext (smul_zero _).symm rfl
#align unitization.coe_smul Unitization.inr_smul

end

theorem inl_fst_add_inr_snd_eq [AddZeroClass R] [AddZeroClass A] (x : Unitization R A) :
    inl x.fst + (x.snd : Unitization R A) = x :=
  ext (add_zero x.1) (zero_add x.2)
#align unitization.inl_fst_add_coe_snd_eq Unitization.inl_fst_add_inr_snd_eq

/-- To show a property hold on all `Unitization R A` it suffices to show it holds
on terms of the form `inl r + a`.

This can be used as `induction x`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
theorem ind {R A} [AddZeroClass R] [AddZeroClass A] {P : Unitization R A → Prop}
    (inl_add_inr : ∀ (r : R) (a : A), P (inl r + (a : Unitization R A))) (x) : P x :=
  inl_fst_add_inr_snd_eq x ▸ inl_add_inr x.1 x.2
#align unitization.ind Unitization.ind

/-- This cannot be marked `@[ext]` as it ends up being used instead of `LinearMap.prod_ext` when
working with `R × A`. -/
theorem linearMap_ext {N} [Semiring S] [AddCommMonoid R] [AddCommMonoid A] [AddCommMonoid N]
    [Module S R] [Module S A] [Module S N] ⦃f g : Unitization R A →ₗ[S] N⦄
    (hl : ∀ r, f (inl r) = g (inl r)) (hr : ∀ a : A, f a = g a) : f = g :=
  LinearMap.prod_ext (LinearMap.ext hl) (LinearMap.ext hr)
#align unitization.linear_map_ext Unitization.linearMap_ext

variable (R A)

/-- The canonical `R`-linear inclusion `A → Unitization R A`. -/
@[simps apply]
def inrHom [Semiring R] [AddCommMonoid A] [Module R A] : A →ₗ[R] Unitization R A :=
  { LinearMap.inr R R A with toFun := (↑) }
#align unitization.coe_hom Unitization.inrHom

/-- The canonical `R`-linear projection `Unitization R A → A`. -/
@[simps apply]
def sndHom [Semiring R] [AddCommMonoid A] [Module R A] : Unitization R A →ₗ[R] A :=
  { LinearMap.snd _ _ _ with toFun := snd }
#align unitization.snd_hom Unitization.sndHom

end Additive

/-! ### Multiplicative structure -/


section Mul

variable {R A : Type*}

instance instOne [One R] [Zero A] : One (Unitization R A) :=
  ⟨(1, 0)⟩

instance instMul [Mul R] [Add A] [Mul A] [SMul R A] : Mul (Unitization R A) :=
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
    show (0 : A) = r₁ • (0 : A) + r₂ • (0 : A) + 0 * 0 by
      simp only [smul_zero, add_zero, mul_zero]
#align unitization.inl_mul Unitization.inl_mul

theorem inl_mul_inl [Monoid R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A] (r₁ r₂ : R) :
    (inl r₁ * inl r₂ : Unitization R A) = inl (r₁ * r₂) :=
  (inl_mul A r₁ r₂).symm
#align unitization.inl_mul_inl Unitization.inl_mul_inl

end

section

variable (R)

@[simp]
theorem inr_mul [Semiring R] [AddCommMonoid A] [Mul A] [SMulWithZero R A] (a₁ a₂ : A) :
    (↑(a₁ * a₂) : Unitization R A) = a₁ * a₂ :=
  ext (mul_zero _).symm <|
    show a₁ * a₂ = (0 : R) • a₂ + (0 : R) • a₁ + a₁ * a₂ by simp only [zero_smul, zero_add]
#align unitization.coe_mul Unitization.inr_mul

end

theorem inl_mul_inr [Semiring R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A] (r : R)
    (a : A) : ((inl r : Unitization R A) * a) = ↑(r • a) :=
  ext (mul_zero r) <|
    show r • a + (0 : R) • (0 : A) + 0 * a = r • a by
      rw [smul_zero, add_zero, zero_mul, add_zero]
#align unitization.inl_mul_coe Unitization.inl_mul_inr

theorem inr_mul_inl [Semiring R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A] (r : R)
    (a : A) : a * (inl r : Unitization R A) = ↑(r • a) :=
  ext (zero_mul r) <|
    show (0 : R) • (0 : A) + r • a + a * 0 = r • a by
      rw [smul_zero, zero_add, mul_zero, add_zero]
#align unitization.coe_mul_inl Unitization.inr_mul_inl

instance instMulOneClass [Monoid R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A] :
    MulOneClass (Unitization R A) :=
  { Unitization.instOne, Unitization.instMul with
    one_mul := fun x =>
      ext (one_mul x.1) <|
        show (1 : R) • x.2 + x.1 • (0 : A) + 0 * x.2 = x.2 by
          rw [one_smul, smul_zero, add_zero, zero_mul, add_zero]
    mul_one := fun x =>
      ext (mul_one x.1) <|
        show (x.1 • (0 : A)) + (1 : R) • x.2 + x.2 * (0 : A) = x.2 by
          rw [smul_zero, zero_add, one_smul, mul_zero, add_zero] }
#align unitization.mul_one_class Unitization.instMulOneClass

instance instNonAssocSemiring [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] :
    NonAssocSemiring (Unitization R A) :=
  { Unitization.instMulOneClass,
    Unitization.instAddCommMonoid with
    zero_mul := fun x =>
      ext (zero_mul x.1) <|
        show (0 : R) • x.2 + x.1 • (0 : A) + 0 * x.2 = 0 by
          rw [zero_smul, zero_add, smul_zero, zero_mul, add_zero]
    mul_zero := fun x =>
      ext (mul_zero x.1) <|
        show x.1 • (0 : A) + (0 : R) • x.2 + x.2 * 0 = 0 by
          rw [smul_zero, zero_add, zero_smul, mul_zero, add_zero]
    left_distrib := fun x₁ x₂ x₃ =>
      ext (mul_add x₁.1 x₂.1 x₃.1) <|
        show x₁.1 • (x₂.2 + x₃.2) + (x₂.1 + x₃.1) • x₁.2 + x₁.2 * (x₂.2 + x₃.2) =
            x₁.1 • x₂.2 + x₂.1 • x₁.2 + x₁.2 * x₂.2 + (x₁.1 • x₃.2 + x₃.1 • x₁.2 + x₁.2 * x₃.2) by
          simp only [smul_add, add_smul, mul_add]
          abel
    right_distrib := fun x₁ x₂ x₃ =>
      ext (add_mul x₁.1 x₂.1 x₃.1) <|
        show (x₁.1 + x₂.1) • x₃.2 + x₃.1 • (x₁.2 + x₂.2) + (x₁.2 + x₂.2) * x₃.2 =
            x₁.1 • x₃.2 + x₃.1 • x₁.2 + x₁.2 * x₃.2 + (x₂.1 • x₃.2 + x₃.1 • x₂.2 + x₂.2 * x₃.2) by
          simp only [add_smul, smul_add, add_mul]
          abel }

instance instMonoid [CommMonoid R] [NonUnitalSemiring A] [DistribMulAction R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : Monoid (Unitization R A) :=
  { Unitization.instMulOneClass with
    mul_assoc := fun x y z =>
      ext (mul_assoc x.1 y.1 z.1) <|
        show (x.1 * y.1) • z.2 + z.1 • (x.1 • y.2 + y.1 • x.2 + x.2 * y.2) +
            (x.1 • y.2 + y.1 • x.2 + x.2 * y.2) * z.2 =
            x.1 • (y.1 • z.2 + z.1 • y.2 + y.2 * z.2) + (y.1 * z.1) • x.2 +
            x.2 * (y.1 • z.2 + z.1 • y.2 + y.2 * z.2) by
          simp only [smul_add, mul_add, add_mul, smul_smul, smul_mul_assoc, mul_smul_comm,
            mul_assoc]
          rw [mul_comm z.1 x.1]
          rw [mul_comm z.1 y.1]
          abel }

instance instCommMonoid [CommMonoid R] [NonUnitalCommSemiring A] [DistribMulAction R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : CommMonoid (Unitization R A) :=
  { Unitization.instMonoid with
    mul_comm := fun x₁ x₂ =>
      ext (mul_comm x₁.1 x₂.1) <|
        show x₁.1 • x₂.2 + x₂.1 • x₁.2 + x₁.2 * x₂.2 = x₂.1 • x₁.2 + x₁.1 • x₂.2 + x₂.2 * x₁.2 by
          rw [add_comm (x₁.1 • x₂.2), mul_comm] }

instance instSemiring [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] : Semiring (Unitization R A) :=
  { Unitization.instMonoid, Unitization.instNonAssocSemiring with }

instance instCommSemiring [CommSemiring R] [NonUnitalCommSemiring A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : CommSemiring (Unitization R A) :=
  { Unitization.instCommMonoid, Unitization.instNonAssocSemiring with }

instance instNonAssocRing [CommRing R] [NonUnitalNonAssocRing A] [Module R A] :
    NonAssocRing (Unitization R A) :=
  { Unitization.instAddCommGroup, Unitization.instNonAssocSemiring with }

instance instRing [CommRing R] [NonUnitalRing A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] : Ring (Unitization R A) :=
  { Unitization.instAddCommGroup, Unitization.instSemiring with }

instance instCommRing [CommRing R] [NonUnitalCommRing A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] : CommRing (Unitization R A) :=
  { Unitization.instAddCommGroup, Unitization.instCommSemiring with }

variable (R A)

/-- The canonical inclusion of rings `R →+* Unitization R A`. -/
@[simps apply]
def inlRingHom [Semiring R] [NonUnitalSemiring A] [Module R A] : R →+* Unitization R A where
  toFun := inl
  map_one' := inl_one A
  map_mul' := inl_mul A
  map_zero' := inl_zero A
  map_add' := inl_add A
#align unitization.inl_ring_hom Unitization.inlRingHom

end Mul

/-! ### Star structure -/


section Star

variable {R A : Type*}

instance instStar [Star R] [Star A] : Star (Unitization R A) :=
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
theorem inr_star [AddMonoid R] [StarAddMonoid R] [Star A] (a : A) :
    ↑(star a) = star (a : Unitization R A) :=
  ext (by simp only [fst_star, star_zero, fst_inr]) rfl
#align unitization.coe_star Unitization.inr_star

instance instStarAddMonoid [AddMonoid R] [AddMonoid A] [StarAddMonoid R] [StarAddMonoid A] :
    StarAddMonoid (Unitization R A) where
  star_involutive x := ext (star_star x.fst) (star_star x.snd)
  star_add x y := ext (star_add x.fst y.fst) (star_add x.snd y.snd)

instance instStarModule [CommSemiring R] [StarRing R] [AddCommMonoid A] [StarAddMonoid A]
    [Module R A] [StarModule R A] : StarModule R (Unitization R A) where
  star_smul r x := ext (by simp) (by simp)

instance instStarRing [CommSemiring R] [StarRing R] [NonUnitalNonAssocSemiring A] [StarRing A]
    [Module R A] [StarModule R A] :
    StarRing (Unitization R A) :=
  { Unitization.instStarAddMonoid with
    star_mul := fun x y =>
      ext (by simp [-star_mul']) (by simp [-star_mul', add_comm (star x.fst • star y.snd)]) }

end Star

/-! ### Algebra structure -/


section Algebra

variable (S R A : Type*) [CommSemiring S] [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [Algebra S R] [DistribMulAction S A]
  [IsScalarTower S R A]

instance instAlgebra : Algebra S (Unitization R A) :=
  { (Unitization.inlRingHom R A).comp (algebraMap S R) with
    commutes' := fun s x => by
      induction' x with r a
      show inl (algebraMap S R s) * _ = _ * inl (algebraMap S R s)
      rw [mul_add, add_mul, inl_mul_inl, inl_mul_inl, inl_mul_inr, inr_mul_inl, mul_comm]
    smul_def' := fun s x => by
      induction' x with r a
      show _ = inl (algebraMap S R s) * _
      rw [mul_add, smul_add,Algebra.algebraMap_eq_smul_one, inl_mul_inl, inl_mul_inr, smul_one_mul,
        inl_smul, inr_smul, smul_one_smul] }
#align unitization.algebra Unitization.instAlgebra

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

theorem algebraMap_eq_inlRingHom : algebraMap R (Unitization R A) = inlRingHom R A :=
  rfl
#align unitization.algebra_map_eq_inl_hom Unitization.algebraMap_eq_inlRingHom

/-- The canonical `R`-algebra projection `Unitization R A → R`. -/
@[simps]
def fstHom : Unitization R A →ₐ[R] R where
  toFun := fst
  map_one' := fst_one
  map_mul' := fst_mul
  map_zero' := fst_zero (A := A)
  map_add' := fst_add
  commutes' := fst_inl A
#align unitization.fst_hom Unitization.fstHom

end Algebra

section coe

/-- The coercion from a non-unital `R`-algebra `A` to its unitization `Unitization R A`
realized as a non-unital algebra homomorphism. -/
@[simps]
def inrNonUnitalAlgHom (R A : Type*) [CommSemiring R] [NonUnitalSemiring A] [Module R A] :
    A →ₙₐ[R] Unitization R A where
  toFun := (↑)
  map_smul' := inr_smul R
  map_zero' := inr_zero R
  map_add' := inr_add R
  map_mul' := inr_mul R
#align unitization.coe_non_unital_alg_hom Unitization.inrNonUnitalAlgHom

/-- The coercion from a non-unital `R`-algebra `A` to its unitization `unitization R A`
realized as a non-unital star algebra homomorphism. -/
@[simps!]
def inrNonUnitalStarAlgHom (R A : Type*) [CommSemiring R] [StarAddMonoid R]
    [NonUnitalSemiring A] [Star A] [Module R A] :
    A →⋆ₙₐ[R] Unitization R A where
  toNonUnitalAlgHom := inrNonUnitalAlgHom R A
  map_star' := inr_star

/-- The star algebra equivalence obtained by restricting `Unitization.inrNonUnitalStarAlgHom`
to its range. -/
@[simps!]
def inrRangeEquiv (R A : Type*) [CommSemiring R] [StarAddMonoid R] [NonUnitalSemiring A]
    [Star A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] :
    A ≃⋆ₐ[R] NonUnitalStarAlgHom.range (inrNonUnitalStarAlgHom R A) :=
  StarAlgEquiv.ofLeftInverse' (snd_inr R)

end coe

section AlgHom

variable {S R A : Type*} [CommSemiring S] [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A] {B : Type*} [Semiring B] [Algebra S B] [Algebra S R]
  [DistribMulAction S A] [IsScalarTower S R A] {C : Type*} [Semiring C] [Algebra R C]

theorem algHom_ext {F : Type*}
    [FunLike F (Unitization R A) B] [AlgHomClass F S (Unitization R A) B] {φ ψ : F}
    (h : ∀ a : A, φ a = ψ a)
    (h' : ∀ r, φ (algebraMap R (Unitization R A) r) = ψ (algebraMap R (Unitization R A) r)) :
    φ = ψ := by
  refine DFunLike.ext φ ψ (fun x ↦ ?_)
  induction x
  simp only [map_add, ← algebraMap_eq_inl, h, h']
#align unitization.alg_hom_ext Unitization.algHom_ext

lemma algHom_ext'' {F : Type*}
    [FunLike F (Unitization R A) C] [AlgHomClass F R (Unitization R A) C] {φ ψ : F}
    (h : ∀ a : A, φ a = ψ a) : φ = ψ :=
  algHom_ext h (fun r => by simp only [AlgHomClass.commutes])

/-- See note [partially-applied ext lemmas] -/
@[ext 1100]
theorem algHom_ext' {φ ψ : Unitization R A →ₐ[R] C}
    (h :
      φ.toNonUnitalAlgHom.comp (inrNonUnitalAlgHom R A) =
        ψ.toNonUnitalAlgHom.comp (inrNonUnitalAlgHom R A)) :
    φ = ψ :=
  algHom_ext'' (NonUnitalAlgHom.congr_fun h)
#align unitization.alg_hom_ext' Unitization.algHom_ext'

/- porting note: this was extracted from `Unitization.lift` below, where it had previously
been inlined. Unfortunately, `Unitization.lift` was relatively slow in Lean 3, but in Lean 4 it
just times out. Note that this doesn't require a backport because this file is a leaf in the
import hierarchy. -/
/-- A non-unital algebra homomorphism from `A` into a unital `R`-algebra `C` lifts to a unital
algebra homomorphism from the unitization into `C`. This is extended to an `Equiv` in
`Unitization.lift` and that should be used instead. This declaration only exists for performance
reasons. -/
@[simps]
def _root_.NonUnitalAlgHom.toAlgHom (φ :A →ₙₐ[R] C) : Unitization R A →ₐ[R] C where
  toFun := fun x => algebraMap R C x.fst + φ x.snd
  map_one' := by simp only [fst_one, map_one, snd_one, φ.map_zero, add_zero]
  map_mul' := fun x y => by
    induction' x with x_r x_a
    induction' y with y_r y_a
    simp only [fst_mul, fst_add, fst_inl, fst_inr, snd_mul, snd_add, snd_inl, snd_inr, add_zero,
      map_mul, zero_add, map_add, map_smul φ]
    rw [add_mul, mul_add, mul_add]
    rw [← Algebra.commutes _ (φ x_a)]
    simp only [Algebra.algebraMap_eq_smul_one, smul_one_mul, add_assoc]
  map_zero' := by simp only [fst_zero, map_zero, snd_zero, φ.map_zero, add_zero]
  map_add' := fun x y => by
    induction' x with x_r x_a
    induction' y with y_r y_a
    simp only [fst_add, fst_inl, fst_inr, add_zero, map_add, snd_add, snd_inl, snd_inr,
      zero_add, φ.map_add]
    rw [add_add_add_comm]
  commutes' := fun r => by
    simp only [algebraMap_eq_inl, fst_inl, snd_inl, φ.map_zero, add_zero]


/-- Non-unital algebra homomorphisms from `A` into a unital `R`-algebra `C` lift uniquely to
`Unitization R A →ₐ[R] C`. This is the universal property of the unitization. -/
@[simps! apply symm_apply apply_apply]
def lift : (A →ₙₐ[R] C) ≃ (Unitization R A →ₐ[R] C) where
  toFun := NonUnitalAlgHom.toAlgHom
  invFun φ := φ.toNonUnitalAlgHom.comp (inrNonUnitalAlgHom R A)
  left_inv φ := by ext; simp [NonUnitalAlgHomClass.toNonUnitalAlgHom]
  right_inv φ := by ext; simp [NonUnitalAlgHomClass.toNonUnitalAlgHom]
#align unitization.lift Unitization.lift

theorem lift_symm_apply_apply (φ : Unitization R A →ₐ[R] C) (a : A) :
    Unitization.lift.symm φ a = φ a :=
  rfl
#align unitization.lift_symm_apply Unitization.lift_symm_apply

@[simp]
lemma _root_.NonUnitalAlgHom.toAlgHom_zero :
    ⇑(0 : A →ₙₐ[R] R).toAlgHom = Unitization.fst := by
  ext
  simp

end AlgHom

section StarAlgHom

variable {R A C : Type*} [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [StarRing A]
variable [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] [StarModule R A]
variable [Semiring C] [Algebra R C] [StarRing C] [StarModule R C]

/-- See note [partially-applied ext lemmas] -/
@[ext]
theorem starAlgHom_ext {φ ψ : Unitization R A →⋆ₐ[R] C}
    (h : (φ : Unitization R A →⋆ₙₐ[R] C).comp (Unitization.inrNonUnitalStarAlgHom R A) =
      (ψ : Unitization R A →⋆ₙₐ[R] C).comp (Unitization.inrNonUnitalStarAlgHom R A)) :
    φ = ψ :=
  Unitization.algHom_ext'' <| DFunLike.congr_fun h

/-- Non-unital star algebra homomorphisms from `A` into a unital star `R`-algebra `C` lift uniquely
to `Unitization R A →⋆ₐ[R] C`. This is the universal property of the unitization. -/
@[simps! apply symm_apply apply_apply]
def starLift : (A →⋆ₙₐ[R] C) ≃ (Unitization R A →⋆ₐ[R] C) :=
{ toFun := fun φ ↦
  { toAlgHom := Unitization.lift φ.toNonUnitalAlgHom
    map_star' := fun x => by
      induction x
      simp [map_star] }
  invFun := fun φ ↦ φ.toNonUnitalStarAlgHom.comp (inrNonUnitalStarAlgHom R A),
  left_inv := fun φ => by ext; simp,
  right_inv := fun φ => Unitization.algHom_ext'' <| by
    simp }

-- Note (#6057) : tagging simpNF because linter complains
@[simp high, nolint simpNF]
theorem starLift_symm_apply_apply (φ : Unitization R A →ₐ[R] C) (a : A) :
    Unitization.lift.symm φ a = φ a :=
  rfl

end StarAlgHom

section StarNormal

variable {R A : Type*} [Semiring R] [AddCommMonoid A] [Mul A] [SMulWithZero R A]
variable [StarAddMonoid R] [Star A] {a : A}

@[simp]
lemma isStarNormal_inr : IsStarNormal (a : Unitization R A) ↔ IsStarNormal a := by
  simp only [isStarNormal_iff, commute_iff_eq, ← inr_star, ← inr_mul, inr_injective.eq_iff]

variable (R a) in
instance instIsStarNormal (a : A) [IsStarNormal a] :
    IsStarNormal (a : Unitization R A) :=
  isStarNormal_inr.mpr ‹_›

@[simp]
lemma isSelfAdjoint_inr : IsSelfAdjoint (a : Unitization R A) ↔ IsSelfAdjoint a := by
  simp only [isSelfAdjoint_iff, ← inr_star, ← inr_mul, inr_injective.eq_iff]

variable (R) in
lemma _root_.IsSelfAdjoint.inr (ha : IsSelfAdjoint a) : IsSelfAdjoint (a : Unitization R A) :=
  isSelfAdjoint_inr.mpr ha

alias ⟨_root_.IsSelfAdjoint.of_inr, _⟩ := isSelfAdjoint_inr
alias ⟨_root_.IsStarNormal.of_inr, _⟩ := isStarNormal_inr

end StarNormal

end Unitization
