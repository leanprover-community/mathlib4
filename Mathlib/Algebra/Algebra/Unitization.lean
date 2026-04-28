/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Star.Module
public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Algebra.Star.NonUnitalSubalgebra
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.GroupWithZero.Action.TransferInstance
public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.Module.TransferInstance

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

@[expose] public section


/-- The minimal unitization of a non-unital `R`-algebra `A`. This is just a structure wrapper for
`R × A`. -/
@[ext]
structure Unitization (R A : Type*) extends R × A

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `mk x` being printed as `{ toProd := x }` by `delabStructureInstance`. -/
@[app_delab Unitization.mk]
meta def Unitization.delabMk : Delab := delabApp

end Notation

namespace Unitization

section Basic

variable {R A : Type*}

lemma mk_toProd (x : Unitization R A) : mk x.toProd = x := rfl
lemma toProd_mk (x : R × A) : toProd (mk x) = x := rfl

/-- The canonical equivalence between `Unitization R A` and `R × A`. -/
@[simps apply symm_apply]
def equiv : Unitization R A ≃ R × A where
  toFun := toProd
  invFun := mk
  left_inv := mk_toProd
  right_inv := toProd_mk

lemma toProd_injective : (toProd : Unitization R A → R × A).Injective :=
  equiv.injective

lemma toProd_surjective : (toProd : Unitization R A → R × A).Surjective :=
  equiv.surjective

lemma toProd_bijective : (toProd : Unitization R A → R × A).Bijective :=
  equiv.bijective

lemma mk_injective : (mk : R × A → Unitization R A).Injective :=
  equiv.symm.injective

lemma mk_surjective : (mk : R × A → Unitization R A).Surjective :=
  equiv.symm.surjective

lemma mk_bijective : (mk : R × A → Unitization R A).Bijective :=
  equiv.symm.bijective

@[simp]
lemma toProd_inj_iff {x y : Unitization R A} : toProd x = toProd y ↔ x = y :=
  toProd_injective.eq_iff

/-- The canonical inclusion `R → Unitization R A`. -/
def inl [Zero A] (r : R) : Unitization R A :=
  mk (r, 0)

/-- The canonical inclusion `A → Unitization R A`. -/
@[coe]
def inr [Zero R] (a : A) : Unitization R A :=
  mk (0, a)

instance [Zero R] : Coe A (Unitization R A) where
  coe := inr

section

variable (A)

@[simp]
theorem fst_inl [Zero A] (r : R) : (inl r : Unitization R A).fst = r :=
  rfl

@[simp]
theorem snd_inl [Zero A] (r : R) : (inl r : Unitization R A).snd = 0 :=
  rfl

end

section

variable (R)

@[simp]
theorem fst_inr [Zero R] (a : A) : (a : Unitization R A).fst = 0 :=
  rfl

@[simp]
theorem snd_inr [Zero R] (a : A) : (a : Unitization R A).snd = a :=
  rfl

end

theorem inl_injective [Zero A] : Function.Injective (inl : R → Unitization R A) :=
  Function.LeftInverse.injective (g := Prod.fst ∘ toProd) <| fst_inl _

theorem inr_injective [Zero R] : Function.Injective ((↑) : A → Unitization R A) :=
  Function.LeftInverse.injective (g := Prod.snd ∘ toProd) <| snd_inr _

@[simp, norm_cast] theorem inr_inj [Zero R] {x y : A} :
    (inr x : Unitization R A) = inr y ↔ x = y := inr_injective.eq_iff

@[simp] theorem inl_inj [Zero A] {x y : R} :
    (inl x : Unitization R A) = inl y ↔ x = y :=
  inl_injective.eq_iff

instance instNontrivialLeft {𝕜 A} [Nontrivial 𝕜] [Nonempty A] :
    Nontrivial (Unitization 𝕜 A) :=
  equiv.nontrivial

instance instNontrivialRight {𝕜 A} [Nonempty 𝕜] [Nontrivial A] :
    Nontrivial (Unitization 𝕜 A) :=
  equiv.nontrivial

end Basic

/-! ### Structures inherited from `Prod`

Additive operators and scalar multiplication operate elementwise. -/


section Additive

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

instance instCanLift [Zero R] : CanLift (Unitization R A) A inr (fun x ↦ x.fst = 0) where
  prf x hx := ⟨x.snd, Unitization.ext (hx ▸ fst_inr R x.snd) rfl⟩

instance instInhabited [Inhabited R] [Inhabited A] : Inhabited (Unitization R A) :=
  equiv.inhabited

instance instZero [Zero R] [Zero A] : Zero (Unitization R A) :=
  equiv.zero

instance instAdd [Add R] [Add A] : Add (Unitization R A) :=
  equiv.add

instance instSub [Sub R] [Sub A] : Sub (Unitization R A) :=
  equiv.sub

instance instNeg [Neg R] [Neg A] : Neg (Unitization R A) :=
  equiv.Neg

instance instSMul [SMul S R] [SMul S A] : SMul S (Unitization R A) :=
  equiv.smul S

instance instAddSemigroup [AddSemigroup R] [AddSemigroup A] : AddSemigroup (Unitization R A) :=
  fast_instance% equiv.addSemigroup

instance instAddZeroClass [AddZeroClass R] [AddZeroClass A] : AddZeroClass (Unitization R A) :=
  fast_instance% equiv.addZeroClass

instance instAddMonoid [AddMonoid R] [AddMonoid A] : AddMonoid (Unitization R A) :=
  fast_instance% equiv.addMonoid

instance instAddGroup [AddGroup R] [AddGroup A] : AddGroup (Unitization R A) :=
  fast_instance% equiv.addGroup

instance instAddCommSemigroup [AddCommSemigroup R] [AddCommSemigroup A] :
    AddCommSemigroup (Unitization R A) :=
  fast_instance% equiv.addCommSemigroup

instance instAddCommMonoid [AddCommMonoid R] [AddCommMonoid A] : AddCommMonoid (Unitization R A) :=
  fast_instance% equiv.addCommMonoid

instance instAddCommGroup [AddCommGroup R] [AddCommGroup A] : AddCommGroup (Unitization R A) :=
  fast_instance% equiv.addCommGroup

@[simp]
theorem toProd_zero [Zero R] [Zero A] : (0 : Unitization R A).toProd = 0 :=
  rfl

@[simp]
theorem toProd_add [Add R] [Add A] (x₁ x₂ : Unitization R A) :
    (x₁ + x₂).toProd = x₁.toProd + x₂.toProd :=
  rfl

@[simp]
theorem toProd_neg [Neg R] [Neg A] (x : Unitization R A) : (-x).toProd = -x.toProd :=
  rfl

@[simp]
theorem toProd_smul [SMul S R] [SMul S A] (s : S) (x : Unitization R A) :
    (s • x).toProd = s • x.toProd :=
  rfl

instance instIsScalarTower [SMul T R] [SMul T A] [SMul S R] [SMul S A] [SMul T S]
    [IsScalarTower T S R] [IsScalarTower T S A] : IsScalarTower T S (Unitization R A) :=
  equiv.isScalarTower T S

instance instSMulCommClass [SMul T R] [SMul T A] [SMul S R] [SMul S A] [SMulCommClass T S R]
    [SMulCommClass T S A] : SMulCommClass T S (Unitization R A) :=
  equiv.smulCommClass T S

instance instIsCentralScalar [SMul S R] [SMul S A] [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ A] [IsCentralScalar S R]
    [IsCentralScalar S A] : IsCentralScalar S (Unitization R A) :=
  equiv.isCentralScalar S

instance instMulAction [Monoid S] [MulAction S R] [MulAction S A] : MulAction S (Unitization R A) :=
  fast_instance% equiv.mulAction S

instance instDistribMulAction [Monoid S] [AddMonoid R] [AddMonoid A] [DistribMulAction S R]
    [DistribMulAction S A] : DistribMulAction S (Unitization R A) :=
  fast_instance% equiv.distribMulAction S

instance instModule [Semiring S] [AddCommMonoid R] [AddCommMonoid A] [Module S R] [Module S A] :
    Module S (Unitization R A) :=
  fast_instance% equiv.module S

variable (R A) in
/-- The identity map between `Unitization R A` and `R × A` as an `AddEquiv`. -/
@[simps! apply symm_apply]
def addEquiv [Add R] [Add A] : Unitization R A ≃+ R × A where
  toEquiv := equiv
  map_add' _ _ := rfl

-- not marked `simp` because the LHS would not be in simp normal form.
lemma toEquiv_addEquiv [Add R] [Add A] : (addEquiv R A).toEquiv = equiv :=
  rfl

variable (R S A) in
/-- The identity map between `Unitization R A` and `R × A` as a `LinearEquiv`. -/
@[simps! apply symm_apply]
def linearEquiv [Semiring S] [AddCommMonoid R] [AddCommMonoid A] [Module S R] [Module S A] :
    Unitization R A ≃ₗ[S] R × A where
  toAddEquiv := addEquiv R A
  map_smul' _ _ := rfl

@[simp]
lemma toAddEquiv_linearEquiv [Semiring S] [AddCommMonoid R] [AddCommMonoid A]
    [Module S R] [Module S A] : (linearEquiv S R A).toAddEquiv = addEquiv R A :=
  rfl

@[simp]
theorem fst_zero [Zero R] [Zero A] : (0 : Unitization R A).fst = 0 :=
  rfl

@[simp]
theorem snd_zero [Zero R] [Zero A] : (0 : Unitization R A).snd = 0 :=
  rfl

@[simp]
theorem fst_add [Add R] [Add A] (x₁ x₂ : Unitization R A) : (x₁ + x₂).fst = x₁.fst + x₂.fst :=
  rfl

@[simp]
theorem snd_add [Add R] [Add A] (x₁ x₂ : Unitization R A) : (x₁ + x₂).snd = x₁.snd + x₂.snd :=
  rfl

@[simp]
theorem fst_neg [Neg R] [Neg A] (x : Unitization R A) : (-x).fst = -x.fst :=
  rfl

@[simp]
theorem snd_neg [Neg R] [Neg A] (x : Unitization R A) : (-x).snd = -x.snd :=
  rfl

@[simp]
theorem fst_smul [SMul S R] [SMul S A] (s : S) (x : Unitization R A) : (s • x).fst = s • x.fst :=
  rfl

@[simp]
theorem snd_smul [SMul S R] [SMul S A] (s : S) (x : Unitization R A) : (s • x).snd = s • x.snd :=
  rfl

section

variable (A)

@[simp]
theorem inl_zero [Zero R] [Zero A] : (inl 0 : Unitization R A) = 0 :=
  rfl

@[simp]
theorem inl_add [Add R] [AddZeroClass A] (r₁ r₂ : R) :
    (inl (r₁ + r₂) : Unitization R A) = inl r₁ + inl r₂ :=
  Unitization.ext rfl (add_zero 0).symm

@[simp]
theorem inl_neg [Neg R] [AddGroup A] (r : R) : (inl (-r) : Unitization R A) = -inl r :=
  Unitization.ext rfl neg_zero.symm

@[simp]
theorem inl_sub [AddGroup R] [AddGroup A] (r₁ r₂ : R) :
    (inl (r₁ - r₂) : Unitization R A) = inl r₁ - inl r₂ :=
  Unitization.ext rfl (sub_zero 0).symm

@[simp]
theorem inl_smul [Zero A] [SMul S R] [SMulZeroClass S A] (s : S) (r : R) :
    (inl (s • r) : Unitization R A) = s • inl r :=
  Unitization.ext rfl (smul_zero s).symm

end

section

variable (R)

@[simp, norm_cast]
theorem inr_zero [Zero R] [Zero A] : ↑(0 : A) = (0 : Unitization R A) :=
  rfl

@[simp, norm_cast]
theorem inr_add [AddZeroClass R] [Add A] (m₁ m₂ : A) : (↑(m₁ + m₂) : Unitization R A) = m₁ + m₂ :=
  Unitization.ext (add_zero 0).symm rfl

@[simp, norm_cast]
theorem inr_neg [AddGroup R] [Neg A] (m : A) : (↑(-m) : Unitization R A) = -m :=
  Unitization.ext neg_zero.symm rfl

@[simp, norm_cast]
theorem inr_sub [AddGroup R] [AddGroup A] (m₁ m₂ : A) : (↑(m₁ - m₂) : Unitization R A) = m₁ - m₂ :=
  Unitization.ext (sub_zero 0).symm rfl

@[simp, norm_cast]
theorem inr_smul [Zero R] [SMulZeroClass S R] [SMul S A] (r : S) (m : A) :
    (↑(r • m) : Unitization R A) = r • (m : Unitization R A) :=
  Unitization.ext (smul_zero _).symm rfl

end

theorem inl_fst_add_inr_snd_eq [AddZeroClass R] [AddZeroClass A] (x : Unitization R A) :
    inl x.fst + (x.snd : Unitization R A) = x :=
  Unitization.ext (add_zero x.fst) (zero_add x.snd)

/-- To show a property hold on all `Unitization R A` it suffices to show it holds
on terms of the form `inl r + a`.

This can be used as `induction x`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
theorem ind {R A} [AddZeroClass R] [AddZeroClass A] {P : Unitization R A → Prop}
    (inl_add_inr : ∀ (r : R) (a : A), P (inl r + (a : Unitization R A))) (x) : P x :=
  inl_fst_add_inr_snd_eq x ▸ inl_add_inr x.fst x.snd

@[ext]
theorem linearMap_ext {N} [CommSemiring S] [AddCommMonoid R] [AddCommMonoid A] [AddCommMonoid N]
    [Module S R] [Module S A] [Module S N] ⦃f g : Unitization R A →ₗ[S] N⦄
    (hl : ∀ r, f (inl r) = g (inl r)) (hr : ∀ a : A, f a = g a) : f = g :=
  (linearEquiv S R A).arrowCongr (.refl ..) |>.injective <|
    LinearMap.prod_ext (LinearMap.ext hl) (LinearMap.ext hr)

variable [Semiring S] [Semiring R] [AddCommMonoid A] [SMul R A] [Module S R] [Module S A]

variable (S R A) in
/-- The canonical `S`-linear inclusion `A → Unitization R A`. -/
@[simps apply]
def inrHom : A →ₗ[S] Unitization R A where
  toFun := (↑)
  map_add' := inr_add R
  map_smul' := inr_smul R

omit [SMul R A] in
lemma inrHom_injective : Function.Injective (inrHom S R A) := Unitization.inr_injective

variable (S R A) in
/-- The canonical `S`-linear projection `Unitization R A → A`. -/
@[simps apply]
def sndHom : Unitization R A →ₗ[S] A where
  toFun a := a.snd
  map_add' := snd_add
  map_smul' := snd_smul

end Additive

/-! ### Multiplicative structure -/


section Mul

variable {R A : Type*}

instance instOne [One R] [Zero A] : One (Unitization R A) :=
  ⟨.mk (1, 0)⟩

instance instMul [Mul R] [Add A] [Mul A] [SMul R A] : Mul (Unitization R A) :=
  ⟨fun x y => .mk (x.fst * y.fst, x.fst • y.snd + y.fst • x.snd + x.snd * y.snd)⟩

@[simp]
theorem fst_one [One R] [Zero A] : (1 : Unitization R A).fst = 1 :=
  rfl

@[simp]
theorem snd_one [One R] [Zero A] : (1 : Unitization R A).snd = 0 :=
  rfl

@[simp]
theorem fst_mul [Mul R] [Add A] [Mul A] [SMul R A] (x₁ x₂ : Unitization R A) :
    (x₁ * x₂).fst = x₁.fst * x₂.fst :=
  rfl

@[simp]
theorem snd_mul [Mul R] [Add A] [Mul A] [SMul R A] (x₁ x₂ : Unitization R A) :
    (x₁ * x₂).snd = x₁.fst • x₂.snd + x₂.fst • x₁.snd + x₁.snd * x₂.snd :=
  rfl

section

variable (A)

@[simp]
theorem inl_one [One R] [Zero A] : (inl 1 : Unitization R A) = 1 :=
  rfl

@[simp]
theorem inl_mul [Mul R] [NonUnitalNonAssocSemiring A] [SMulZeroClass R A] (r₁ r₂ : R) :
    (inl (r₁ * r₂) : Unitization R A) = inl r₁ * inl r₂ :=
  Unitization.ext rfl <| by simp

theorem inl_mul_inl [Mul R] [NonUnitalNonAssocSemiring A] [SMulZeroClass R A] (r₁ r₂ : R) :
    (inl r₁ * inl r₂ : Unitization R A) = inl (r₁ * r₂) :=
  (inl_mul A r₁ r₂).symm

end

section

variable (R)

@[simp, norm_cast]
theorem inr_mul [MulZeroClass R] [AddZeroClass A] [Mul A] [SMulWithZero R A] (a₁ a₂ : A) :
    (↑(a₁ * a₂) : Unitization R A) = a₁ * a₂ :=
  Unitization.ext (mul_zero _).symm <| by simp

end

@[norm_cast]
theorem inl_mul_inr [MulZeroClass R] [NonUnitalNonAssocSemiring A] [SMulZeroClass R A] (r : R)
    (a : A) : ((inl r : Unitization R A) * a) = ↑(r • a) :=
  Unitization.ext (mul_zero r) <| by simp

@[norm_cast]
theorem inr_mul_inl [MulZeroClass R] [NonUnitalNonAssocSemiring A] [SMulZeroClass R A] (r : R)
    (a : A) : a * (inl r : Unitization R A) = ↑(r • a) :=
  Unitization.ext (zero_mul r) <| by simp

instance instMulOneClass [Monoid R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A] :
    MulOneClass (Unitization R A) :=
  fast_instance%
  { Unitization.instOne, Unitization.instMul with
    one_mul x := Unitization.ext (one_mul x.fst) <| by simp
    mul_one x := Unitization.ext (mul_one x.fst) <| by simp }

instance instNonAssocSemiring [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] :
    NonAssocSemiring (Unitization R A) :=
  fast_instance%
  { Unitization.instMulOneClass,
    Unitization.instAddCommMonoid with
    zero_mul _ := Unitization.ext (zero_mul _) <| by simp
    mul_zero _ := Unitization.ext (mul_zero _) <| by simp
    left_distrib _ _ _ := Unitization.ext (mul_add ..) <| by
      simp [smul_add, add_smul, mul_add]
      abel
    right_distrib _ _ _ := Unitization.ext (add_mul ..) <| by
      simp [smul_add, add_smul, add_mul]
      abel }

instance instMonoid [CommMonoid R] [NonUnitalSemiring A] [DistribMulAction R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : Monoid (Unitization R A) :=
  fast_instance%
  { Unitization.instMulOneClass with
    mul_assoc x y z := Unitization.ext (mul_assoc ..) <| by
      simp only [snd_mul, fst_mul, smul_add, smul_smul, add_mul, smul_mul_assoc, mul_assoc, mul_add,
        mul_smul_comm, mul_comm z.fst x.fst, mul_comm z.fst y.fst]
      abel }

instance instCommMonoid [CommMonoid R] [NonUnitalCommSemiring A] [DistribMulAction R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : CommMonoid (Unitization R A) :=
  fast_instance%
  { Unitization.instMonoid with
    mul_comm _ _ := Unitization.ext (mul_comm ..) <| by simp [add_comm, mul_comm] }

instance instSemiring [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] : Semiring (Unitization R A) :=
  fast_instance%
  { Unitization.instMonoid, Unitization.instNonAssocSemiring with }

instance instCommSemiring [CommSemiring R] [NonUnitalCommSemiring A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : CommSemiring (Unitization R A) :=
  fast_instance%
  { Unitization.instCommMonoid, Unitization.instNonAssocSemiring with }

instance instNonAssocRing [CommRing R] [NonUnitalNonAssocRing A] [Module R A] :
    NonAssocRing (Unitization R A) :=
  fast_instance%
  { Unitization.instAddCommGroup, Unitization.instNonAssocSemiring with }

instance instRing [CommRing R] [NonUnitalRing A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] : Ring (Unitization R A) :=
  fast_instance%
  { Unitization.instAddCommGroup, Unitization.instSemiring with }

instance instCommRing [CommRing R] [NonUnitalCommRing A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] : CommRing (Unitization R A) :=
  fast_instance%
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

end Mul

/-! ### Star structure -/


section Star

variable {R A : Type*}

instance instStar [Star R] [Star A] : Star (Unitization R A) :=
  ⟨fun ra => .mk (star ra.fst, star ra.snd)⟩

@[simp]
theorem fst_star [Star R] [Star A] (x : Unitization R A) : (star x).fst = star x.fst :=
  rfl

@[simp]
theorem snd_star [Star R] [Star A] (x : Unitization R A) : (star x).snd = star x.snd :=
  rfl

@[simp]
theorem inl_star [Star R] [AddMonoid A] [StarAddMonoid A] (r : R) :
    inl (star r) = star (inl r : Unitization R A) :=
  Unitization.ext rfl (by simp only [snd_star, star_zero, snd_inl])

@[simp, norm_cast]
theorem inr_star [AddMonoid R] [StarAddMonoid R] [Star A] (a : A) :
    ↑(star a) = star (a : Unitization R A) :=
  Unitization.ext (by simp only [fst_star, star_zero, fst_inr]) rfl

instance instStarAddMonoid [AddMonoid R] [AddMonoid A] [StarAddMonoid R] [StarAddMonoid A] :
    StarAddMonoid (Unitization R A) where
  star_involutive x := Unitization.ext (star_star x.fst) (star_star x.snd)
  star_add x y := Unitization.ext (star_add x.fst y.fst) (star_add x.snd y.snd)

instance instStarModule [CommSemiring R] [StarRing R] [AddCommMonoid A] [StarAddMonoid A]
    [Module R A] [StarModule R A] : StarModule R (Unitization R A) where
  star_smul _ _ := Unitization.ext (by simp) (by simp)

instance instStarRing [CommSemiring R] [StarRing R] [NonUnitalNonAssocSemiring A] [StarRing A]
    [Module R A] [StarModule R A] :
    StarRing (Unitization R A) :=
  fast_instance%
  { Unitization.instStarAddMonoid with
    star_mul x y := Unitization.ext
      (by simp [-star_mul']) (by simp [-star_mul', add_comm (star x.fst • star y.snd)]) }

end Star

/-! ### Algebra structure -/


section Algebra

variable (S R A : Type*) [CommSemiring S] [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [Algebra S R] [DistribMulAction S A]
  [IsScalarTower S R A]

instance instAlgebra : Algebra S (Unitization R A) where
  algebraMap := (Unitization.inlRingHom R A).comp (algebraMap S R)
  commutes' := fun s x => by
    induction x with
    | inl_add_inr =>
      change inl (algebraMap S R s) * _ = _ * inl (algebraMap S R s)
      rw [mul_add, add_mul, inl_mul_inl, inl_mul_inl, inl_mul_inr, inr_mul_inl, mul_comm]
  smul_def' := fun s x => by
    induction x with
    | inl_add_inr =>
      change _ = inl (algebraMap S R s) * _
      rw [mul_add, smul_add, Algebra.algebraMap_eq_smul_one, inl_mul_inl, inl_mul_inr,
        smul_one_mul, inl_smul, inr_smul, smul_one_smul]

theorem algebraMap_eq_inl_comp : ⇑(algebraMap S (Unitization R A)) = inl ∘ algebraMap S R :=
  rfl

theorem algebraMap_eq_inlRingHom_comp :
    algebraMap S (Unitization R A) = (inlRingHom R A).comp (algebraMap S R) :=
  rfl

theorem algebraMap_eq_inl : ⇑(algebraMap R (Unitization R A)) = inl :=
  rfl

theorem algebraMap_eq_inlRingHom : algebraMap R (Unitization R A) = inlRingHom R A :=
  rfl

/-- The canonical `R`-algebra projection `Unitization R A → R`. -/
@[simps]
def fstHom : Unitization R A →ₐ[R] R where
  toFun a := a.fst
  map_one' := fst_one
  map_mul' := fst_mul
  map_zero' := fst_zero (A := A)
  map_add' := fst_add
  commutes' := fst_inl A

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

/-- The coercion from a non-unital `R`-algebra `A` to its unitization `Unitization R A`
realized as a non-unital star algebra homomorphism. -/
@[simps! apply]
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
  StarAlgEquiv.ofLeftInverse' (g := fun a ↦ a.snd) (snd_inr R ·)

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

/-- A non-unital algebra homomorphism from `A` into a unital `R`-algebra `C` lifts to a unital
algebra homomorphism from the unitization into `C`. This is extended to an `Equiv` in
`Unitization.lift` and that should be used instead. This declaration only exists for performance
reasons. -/
@[simps]
def _root_.NonUnitalAlgHom.toAlgHom (φ : A →ₙₐ[R] C) : Unitization R A →ₐ[R] C where
  toFun := fun x => algebraMap R C x.fst + φ x.snd
  map_one' := by simp only [fst_one, map_one, snd_one, φ.map_zero, add_zero]
  map_mul' := fun x y => by
    induction x with
    | inl_add_inr x_r x_a =>
      induction y with
      | inl_add_inr =>
        simp only [fst_mul, fst_add, fst_inl, fst_inr, snd_mul, snd_add, snd_inl, snd_inr, add_zero,
          map_mul, zero_add, map_add, map_smul φ]
        rw [add_mul, mul_add, mul_add]
        rw [← Algebra.commutes _ (φ x_a)]
        simp only [Algebra.algebraMap_eq_smul_one, smul_one_mul, add_assoc]
  map_zero' := by simp only [fst_zero, map_zero, snd_zero, φ.map_zero, add_zero]
  map_add' := fun x y => by
    induction x with
    | inl_add_inr =>
      induction y with
      | inl_add_inr =>
        simp only [fst_add, fst_inl, fst_inr, add_zero, map_add, snd_add, snd_inl, snd_inr,
          zero_add, φ.map_add]
        rw [add_add_add_comm]
  commutes' := fun r => by
    simp only [algebraMap_eq_inl, fst_inl, snd_inl, φ.map_zero, add_zero]


set_option backward.isDefEq.respectTransparency false in
/-- Non-unital algebra homomorphisms from `A` into a unital `R`-algebra `C` lift uniquely to
`Unitization R A →ₐ[R] C`. This is the universal property of the unitization. -/
@[simps! apply symm_apply apply_apply]
def lift : (A →ₙₐ[R] C) ≃ (Unitization R A →ₐ[R] C) where
  toFun := NonUnitalAlgHom.toAlgHom
  invFun φ := φ.toNonUnitalAlgHom.comp (inrNonUnitalAlgHom R A)
  left_inv φ := by ext; simp [NonUnitalAlgHomClass.toNonUnitalAlgHom]
  right_inv φ := by ext; simp [NonUnitalAlgHomClass.toNonUnitalAlgHom]

theorem lift_symm_apply_apply (φ : Unitization R A →ₐ[R] C) (a : A) :
    Unitization.lift.symm φ a = φ a :=
  rfl

@[simp]
lemma _root_.NonUnitalAlgHom.toAlgHom_zero :
    ⇑(0 : A →ₙₐ[R] R).toAlgHom = (fun x ↦ x.fst) := by
  ext
  simp

end AlgHom

section StarAlgHom

variable {R A C : Type*} [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [StarRing A]
variable [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [Semiring C] [Algebra R C] [StarRing C]

/-- See note [partially-applied ext lemmas] -/
@[ext]
theorem starAlgHom_ext {φ ψ : Unitization R A →⋆ₐ[R] C}
    (h : (φ : Unitization R A →⋆ₙₐ[R] C).comp (Unitization.inrNonUnitalStarAlgHom R A) =
      (ψ : Unitization R A →⋆ₙₐ[R] C).comp (Unitization.inrNonUnitalStarAlgHom R A)) :
    φ = ψ :=
  Unitization.algHom_ext'' <| DFunLike.congr_fun h

variable [StarModule R C]

/-- Non-unital star algebra homomorphisms from `A` into a unital star `R`-algebra `C` lift uniquely
to `Unitization R A →⋆ₐ[R] C`. This is the universal property of the unitization. -/
@[simps! apply symm_apply apply_apply]
def starLift : (A →⋆ₙₐ[R] C) ≃ (Unitization R A →⋆ₐ[R] C) :=
{ toFun := fun φ ↦
  { toAlgHom := Unitization.lift φ.toNonUnitalAlgHom
    map_star' := fun x => by
      simp [map_star] }
  invFun φ := φ.toNonUnitalStarAlgHom.comp (inrNonUnitalStarAlgHom R A),
  left_inv _ := by ext; simp,
  right_inv _ := by ext; simp }

#adaptation_note /-- After https://github.com/leanprover/lean4/pull/12179
the simpNF linter complains about this being `@[simp]`. -/
theorem starLift_symm_apply_apply (φ : Unitization R A →⋆ₐ[R] C) (a : A) :
    Unitization.starLift.symm φ a = φ a :=
  rfl

end StarAlgHom

section StarMap

variable {R A B C : Type*} [CommSemiring R] [StarRing R]
variable [NonUnitalSemiring A] [StarRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonUnitalSemiring B] [StarRing B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
variable [NonUnitalSemiring C] [StarRing C] [Module R C] [SMulCommClass R C C] [IsScalarTower R C C]
variable [StarModule R B] [StarModule R C]

/-- The functorial map on morphisms between the category of non-unital C⋆-algebras with non-unital
star homomorphisms and unital C⋆-algebras with unital star homomorphisms.

This sends `φ : A →⋆ₙₐ[R] B` to a map `Unitization R A →⋆ₐ[R] Unitization R B` given by the formula
`(r, a) ↦ (r, φ a)` (or perhaps more precisely,
`algebraMap R _ r + ↑a ↦ algebraMap R _ r + ↑(φ a)`). -/
@[simps! apply]
def starMap (φ : A →⋆ₙₐ[R] B) : Unitization R A →⋆ₐ[R] Unitization R B :=
  Unitization.starLift <| (Unitization.inrNonUnitalStarAlgHom R B).comp φ

@[simp high]
lemma starMap_inr (φ : A →⋆ₙₐ[R] B) (a : A) :
    starMap φ (inr a) = inr (φ a) := by
  simp

@[simp high]
lemma starMap_inl (φ : A →⋆ₙₐ[R] B) (r : R) :
    starMap φ (inl r) = algebraMap R (Unitization R B) r := by
  simp

/-- If `φ : A →⋆ₙₐ[R] B` is injective, the lift `starMap φ : Unitization R A →⋆ₐ[R] Unitization R B`
is also injective. -/
lemma starMap_injective {φ : A →⋆ₙₐ[R] B} (hφ : Function.Injective φ) :
    Function.Injective (starMap φ) := by
  intro x y h
  ext
  · simpa using congr($(h).fst)
  · exact hφ <| by simpa [algebraMap_eq_inl] using congr($(h).snd)

/-- If `φ : A →⋆ₙₐ[R] B` is surjective, the lift
`starMap φ : Unitization R A →⋆ₐ[R] Unitization R B` is also surjective. -/
lemma starMap_surjective {φ : A →⋆ₙₐ[R] B} (hφ : Function.Surjective φ) :
    Function.Surjective (starMap φ) := by
  intro x
  induction x using Unitization.ind with
  | inl_add_inr r b =>
    obtain ⟨a, rfl⟩ := hφ b
    exact ⟨mk (r, a), by rfl⟩

/-- `starMap` is functorial: `starMap (ψ.comp φ) = (starMap ψ).comp (starMap φ)`. -/
lemma starMap_comp {φ : A →⋆ₙₐ[R] B} {ψ : B →⋆ₙₐ[R] C} :
    starMap (ψ.comp φ) = (starMap ψ).comp (starMap φ) := by
  ext; all_goals simp

/-- `starMap` is functorial:
`starMap (NonUnitalStarAlgHom.id R B) = StarAlgHom.id R (Unitization R B)`. -/
@[simp]
lemma starMap_id : starMap (NonUnitalStarAlgHom.id R B) = StarAlgHom.id R (Unitization R B) := by
  ext; all_goals simp

end StarMap

section StarNormal

variable {R A : Type*} [Semiring R]
variable [StarAddMonoid R] [Star A] {a : A}


@[simp]
lemma isSelfAdjoint_inr : IsSelfAdjoint (a : Unitization R A) ↔ IsSelfAdjoint a := by
  simp only [isSelfAdjoint_iff, ← inr_star, inr_injective.eq_iff]

alias ⟨_root_.IsSelfAdjoint.of_inr, _⟩ := isSelfAdjoint_inr

variable (R) in
lemma _root_.IsSelfAdjoint.inr (ha : IsSelfAdjoint a) : IsSelfAdjoint (a : Unitization R A) :=
  isSelfAdjoint_inr.mpr ha

variable [AddCommMonoid A] [Mul A] [SMulWithZero R A]

@[simp]
lemma isStarNormal_inr : IsStarNormal (a : Unitization R A) ↔ IsStarNormal a := by
  simp only [isStarNormal_iff, commute_iff_eq, ← inr_star, ← inr_mul, inr_injective.eq_iff]

alias ⟨_root_.IsStarNormal.of_inr, _⟩ := isStarNormal_inr

variable (R a) in
instance instIsStarNormal (a : A) [IsStarNormal a] :
    IsStarNormal (a : Unitization R A) :=
  isStarNormal_inr.mpr ‹_›

end StarNormal

@[simp]
lemma isIdempotentElem_inr_iff (R : Type*) {A : Type*} [MulZeroClass R]
    [AddZeroClass A] [Mul A] [SMulWithZero R A] {a : A} :
    IsIdempotentElem (a : Unitization R A) ↔ IsIdempotentElem a := by
  simp only [IsIdempotentElem, ← inr_mul, inr_injective.eq_iff]

alias ⟨_, IsIdempotentElem.inr⟩ := isIdempotentElem_inr_iff

@[grind =]
lemma isStarProjection_inr_iff {R A : Type*} [Semiring R] [StarRing R] [NonUnitalSemiring A]
    [StarRing A] [Module R A] {p : A} :
    IsStarProjection (p : Unitization R A) ↔ IsStarProjection p := by
  simp [isStarProjection_iff]

protected alias ⟨_root_.IsStarProjection.of_inr, _root_.IsStarProjection.inr⟩ :=
  isStarProjection_inr_iff

end Unitization
