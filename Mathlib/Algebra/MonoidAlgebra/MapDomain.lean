/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
-/
import Mathlib.Algebra.MonoidAlgebra.Lift
import Mathlib.Data.Finsupp.SMul

/-!
# MonoidAlgebra.mapDomain

-/

assert_not_exists NonUnitalAlgHom AlgEquiv

open Function
open Finsupp hiding single mapDomain

noncomputable section

variable {R S M N O : Type*}

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
`Finsupp.mapDomain f` is a ring homomorphism between their monoid algebras. -/
@[to_additive (attr := simps) /--
If `f : G → H` is a multiplicative homomorphism between two monoids, then
`Finsupp.mapDomain f` is a ring homomorphism between their monoid algebras. -/]
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
  __ := Finsupp.domCongr Additive.ofMul
  toFun := equivMapDomain Additive.ofMul
  map_mul' x y := by
    repeat' rw [equivMapDomain_eq_mapDomain (M := k)]
    dsimp [Additive.ofMul]
    convert MonoidAlgebra.mapDomain_mul (MulHom.id G) x y
