/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Lift

/-!
# MonoidAlgebra.mapDomain

-/

@[expose] public section

assert_not_exists NonUnitalAlgHom AlgEquiv

open Function
open Finsupp hiding single mapDomain

noncomputable section

variable {R S T M N O : Type*}

/-! ### Multiplicative monoids -/

namespace MonoidAlgebra
variable [Semiring R] [Semiring S] {f : M → N} {a : M} {r : R}

/-- Given a function `f : M → N` between magmas, return the corresponding map `R[M] → R[N]` obtained
by summing the coefficients along each fiber of `f`. -/
@[to_additive /--
Given a function `f : M → N` between magmas, return the corresponding map `R[M] → R[N]` obtained
by summing the coefficients along each fiber of `f`. -/]
abbrev mapDomain (f : M → N) (v : MonoidAlgebra R M) : MonoidAlgebra R N := Finsupp.mapDomain f v

@[to_additive]
lemma mapDomain_sum (f : M → N) (s : MonoidAlgebra S M) (v : M → S → MonoidAlgebra R M) :
    mapDomain f (s.sum v) = s.sum fun a b ↦ mapDomain f (v a b) := Finsupp.mapDomain_sum

@[to_additive]
lemma mapDomain_single : mapDomain f (single a r) = single (f a) r := Finsupp.mapDomain_single

@[to_additive]
lemma mapDomain_injective (hf : Injective f) : Injective (mapDomain (R := R) f) :=
  Finsupp.mapDomain_injective hf

@[to_additive (dont_translate := R) (attr := simp) mapDomain_one]
theorem mapDomain_one [One M] [One N] {F : Type*} [FunLike F M N] [OneHomClass F M N] (f : F) :
    mapDomain f (1 : MonoidAlgebra R M) = (1 : MonoidAlgebra R N) := by
  simp [one_def]

@[to_additive (dont_translate := R) mapDomain_mul]
theorem mapDomain_mul [Mul M] [Mul N] {F : Type*} [FunLike F M N] [MulHomClass F M N] (f : F)
    (x y : MonoidAlgebra R M) : mapDomain f (x * y) = mapDomain f x * mapDomain f y := by
  simp [mul_def, mapDomain_sum, add_mul, mul_add, sum_mapDomain_index]

variable [Monoid M] [Monoid N] [Monoid O]

variable (R) in
/-- If `f : G → H` is a multiplicative homomorphism between two monoids, then
`MonoidAlgebra.mapDomain f` is a ring homomorphism between their monoid algebras.

See also `MulEquiv.monoidAlgebraCongrRight`. -/
@[to_additive (attr := simps) /--
If `f : G → H` is a multiplicative homomorphism between two additive monoids, then
`AddMonoidAlgebra.mapDomain f` is a ring homomorphism between their additive monoid algebras.

See also `AddEquiv.addMonoidAlgebraCongrRight`. -/]
def mapDomainRingHom {F : Type*} [FunLike F M N] [MonoidHomClass F M N] (f : F) :
    MonoidAlgebra R M →+* MonoidAlgebra R N where
  __ : MonoidAlgebra R M →+ MonoidAlgebra R N := Finsupp.mapDomain.addMonoidHom f
  map_one' := mapDomain_one f
  map_mul' := mapDomain_mul f

attribute [local ext high] ringHom_ext

@[to_additive (dont_translate := R) (attr := simp)]
lemma mapDomainRingHom_id :
    mapDomainRingHom R (MonoidHom.id M) = .id (MonoidAlgebra R M) := by ext <;> simp

@[to_additive (dont_translate := R) (attr := simp)]
lemma mapDomainRingHom_comp (f : N →* O) (g : M →* N) :
    mapDomainRingHom R (f.comp g) = (mapDomainRingHom R f).comp (mapDomainRingHom R g) := by
  ext <;> simp

@[to_additive (dont_translate := R S)]
lemma mapRangeRingHom_comp_mapDomainRingHom (f : R →+* S) (g : M →* N) :
    (mapRangeRingHom N f).comp (mapDomainRingHom R g) =
      (mapDomainRingHom S g).comp (mapRangeRingHom M f) := by aesop

end MonoidAlgebra

namespace Equiv
variable [Semiring R] [Mul M] [Mul N] [Mul O]

/-- Equivalent monoids have additively isomorphic monoid algebras.

`MonoidAlgebra.mapDomain` as an `AddEquiv`. -/
@[to_additive (dont_translate := R) (attr := simps apply symm_apply)
/-- Equivalent additive monoids have additively isomorphic additive monoid algebras.

`AddMonoidAlgebra.mapDomain` as an `AddEquiv`. -/]
def monoidAlgebraCongrRight (e : M ≃ N) : MonoidAlgebra R M ≃+ MonoidAlgebra R N where
  toFun x := x.mapDomain e
  invFun x := x.mapDomain e.symm
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' x y := by ext; simp

@[simp] lemma symm_monoidAlgebraCongrRight (e : M ≃ N) :
    e.monoidAlgebraCongrRight.symm = e.symm.monoidAlgebraCongrRight (R := R) := rfl

@[simp] lemma monoidAlgebraCongrRight_trans (e₁ : M ≃ N) (e₂ : N ≃ O) :
    (e₁.trans e₂).monoidAlgebraCongrRight (R := R) =
      e₁.monoidAlgebraCongrRight.trans e₂.monoidAlgebraCongrRight := by
  ext; simp [Finsupp.mapDomain_comp]

end Equiv

namespace AddEquiv
variable [Semiring R] [Semiring S] [Semiring T] [Mul M]

/-- Additively isomorphic rings have additively isomorphic monoid algebras.

`Finsupp.mapRange` as an `AddEquiv`. -/
@[to_additive (dont_translate := R S) (attr := simps)
/-- Additively isomorphic rings have additively isomorphic additive monoid algebras.

`Finsupp.mapRange` as an `AddEquiv`. -/]
def monoidAlgebraCongrLeft (e : R ≃+ S) : MonoidAlgebra R M ≃+ MonoidAlgebra S M where
  toFun x := .mapRange e e.map_zero x
  invFun x := .mapRange e.symm e.symm.map_zero x
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' x y := by ext; simp

@[simp] lemma symm_monoidAlgebraCongrLeft (e : R ≃+ S) :
    e.monoidAlgebraCongrLeft.symm = e.symm.monoidAlgebraCongrLeft (M := M) := rfl

@[simp] lemma monoidAlgebraCongrLeft_trans (e₁ : R ≃+ S) (e₂ : S ≃+ T) :
    (e₁.trans e₂).monoidAlgebraCongrLeft (M := M) =
      e₁.monoidAlgebraCongrLeft.trans e₂.monoidAlgebraCongrLeft := by ext; simp

end AddEquiv

namespace MulEquiv
variable [Semiring R] [Monoid M] [Monoid N] [Monoid O]

/-- Isomorphic monoids have isomorphic monoid algebras. -/
@[to_additive (dont_translate := R) (attr := simps! apply symm_apply)
/-- Isomorphic monoids have isomorphic additive monoid algebras. -/]
def monoidAlgebraCongrRight (e : M ≃* N) : MonoidAlgebra R M ≃+* MonoidAlgebra R N :=
  .ofRingHom (MonoidAlgebra.mapDomainRingHom R e) (MonoidAlgebra.mapDomainRingHom R e.symm)
    (by apply MonoidAlgebra.ringHom_ext <;> simp) (by apply MonoidAlgebra.ringHom_ext <;> simp)

lemma toRingHom_monoidAlgebraCongrRight (e : M ≃* N) :
    e.monoidAlgebraCongrRight.toRingHom = MonoidAlgebra.mapDomainRingHom R e := rfl

@[simp] lemma symm_monoidAlgebraCongrRight (e : M ≃* N) :
    e.monoidAlgebraCongrRight.symm = e.symm.monoidAlgebraCongrRight (R := R) := rfl

@[simp] lemma monoidAlgebraCongrRight_trans (e₁ : M ≃* N) (e₂ : N ≃* O) :
    (e₁.trans e₂).monoidAlgebraCongrRight (R := R) =
      e₁.monoidAlgebraCongrRight.trans e₂.monoidAlgebraCongrRight := by
  ext; simp [Finsupp.mapDomain_comp]

end MulEquiv

namespace RingEquiv
variable [Semiring R] [Semiring S] [Semiring T] [Monoid M]

/-- Isomorphic rings have isomorphic monoid algebras. -/
@[to_additive (dont_translate := R S) (attr := simps! apply symm_apply)
/-- Isomorphic rings have isomorphic additive monoid algebras. -/]
def monoidAlgebraCongrLeft (e : R ≃+* S) : MonoidAlgebra R M ≃+* MonoidAlgebra S M :=
  .ofRingHom (MonoidAlgebra.mapRangeRingHom M e) (MonoidAlgebra.mapRangeRingHom M e.symm)
    (by apply MonoidAlgebra.ringHom_ext <;> simp) (by apply MonoidAlgebra.ringHom_ext <;> simp)

lemma toRingHom_monoidAlgebraCongrLeft (e : R ≃+* S) :
    e.monoidAlgebraCongrLeft.toRingHom = MonoidAlgebra.mapRangeRingHom M e := rfl

@[simp] lemma symm_monoidAlgebraCongrLeft (e : R ≃+* S) :
    e.monoidAlgebraCongrLeft.symm = e.symm.monoidAlgebraCongrLeft (M := M) := rfl

@[simp] lemma monoidAlgebraCongrLeft_trans (e₁ : R ≃+* S) (e₂ : S ≃+* T) :
    (e₁.trans e₂).monoidAlgebraCongrLeft (M := M) =
      e₁.monoidAlgebraCongrLeft.trans e₂.monoidAlgebraCongrLeft := by ext; simp

end RingEquiv

/-!
#### Conversions between `AddMonoidAlgebra` and `MonoidAlgebra`

We have not defined `k[G] = MonoidAlgebra k (Multiplicative G)`
because historically this caused problems;
since the changes that have made `nsmul` definitional, this would be possible,
but for now we just construct the ring isomorphisms using `RingEquiv.refl _`.
-/

variable (k G) in
/-- The equivalence between `AddMonoidAlgebra` and `MonoidAlgebra` in terms of
`Multiplicative` -/
protected def AddMonoidAlgebra.toMultiplicative [Semiring k] [Add G] :
    AddMonoidAlgebra k G ≃+* MonoidAlgebra k (Multiplicative G) where
  __ := Finsupp.domCongr Multiplicative.ofAdd
  toFun := equivMapDomain Multiplicative.ofAdd
  map_mul' x y := by
    repeat' rw [equivMapDomain_eq_mapDomain (M := k)]
    dsimp [Multiplicative.ofAdd]
    exact MonoidAlgebra.mapDomain_mul (M := Multiplicative G) (MulHom.id (Multiplicative G)) x y

variable (k G) in
/-- The equivalence between `MonoidAlgebra` and `AddMonoidAlgebra` in terms of `Additive` -/
protected def MonoidAlgebra.toAdditive [Semiring k] [Mul G] :
    MonoidAlgebra k G ≃+* AddMonoidAlgebra k (Additive G) where
  toFun x := x.mapDomain .ofMul
  invFun x := x.mapDomain Additive.toMul
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' x y := Finsupp.mapDomain_add ..
  map_mul' := MonoidAlgebra.mapDomain_mul (MulHom.id G)
