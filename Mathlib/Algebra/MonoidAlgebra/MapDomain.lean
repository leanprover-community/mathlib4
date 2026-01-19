/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Defs

/-!
# Maps of monoid algebras

This file defines maps of monoid algebras along both the ring and monoid arguments.
-/

@[expose] public section

assert_not_exists NonUnitalAlgHom AlgEquiv

open Function
open Finsupp hiding single mapDomain

noncomputable section

variable {F R S T M N O : Type*}

/-! ### Multiplicative monoids -/

namespace MonoidAlgebra
variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

/-- Given a function `f : M → N` between magmas, return the corresponding map `R[M] → R[N]` obtained
by summing the coefficients along each fiber of `f`. -/
@[to_additive /--
Given a function `f : M → N` between magmas, return the corresponding map `R[M] → R[N]` obtained
by summing the coefficients along each fiber of `f`. -/]
abbrev mapDomain (f : M → N) (x : R[M]) : R[N] := Finsupp.mapDomain f x

@[to_additive]
lemma mapDomain_zero (f : M → N) : mapDomain f (0 : R[M]) = 0 := Finsupp.mapDomain_zero ..

@[to_additive]
lemma mapDomain_add (f : M → N) (x y : R[M]) :
    mapDomain f (x + y) = mapDomain f x + mapDomain f y := Finsupp.mapDomain_add ..

@[to_additive]
lemma mapDomain_sum (f : M → N) (x : S[M]) (v : M → S → R[M]) :
    mapDomain f (x.sum v) = x.sum fun a b ↦ mapDomain f (v a b) := Finsupp.mapDomain_sum

@[to_additive (relevant_arg := M)]
lemma mapDomain_single : mapDomain f (single a r) = single (f a) r := by ext; simp

@[to_additive]
lemma mapDomain_injective (hf : Injective f) : Injective (mapDomain (R := R) f) :=
  Finsupp.mapDomain_injective hf

@[to_additive (dont_translate := R) (attr := simp) mapDomain_one]
theorem mapDomain_one [One M] [One N] {F : Type*} [FunLike F M N] [OneHomClass F M N] (f : F) :
    mapDomain f (1 : R[M]) = (1 : R[N]) := by
  simp [one_def]

section Mul
variable [Mul M] [Mul N] [Mul O] [FunLike F M N] [MulHomClass F M N]

@[to_additive (dont_translate := R) mapDomain_mul]
lemma mapDomain_mul (f : F) (x y : R[M]) : mapDomain f (x * y) = mapDomain f x * mapDomain f y := by
  simp [mul_def, mapDomain_sum, add_mul, mul_add, sum_mapDomain_index]

variable (R) in
/-- If `f : G → H` is a multiplicative homomorphism between two monoids, then
`MonoidAlgebra.mapDomain f` is a ring homomorphism between their monoid algebras.

See also `MulEquiv.monoidAlgebraCongrRight`. -/
@[to_additive (attr := simps) /--
If `f : G → H` is a multiplicative homomorphism between two additive monoids, then
`AddMonoidAlgebra.mapDomain f` is a ring homomorphism between their additive monoid algebras. -/]
def mapDomainNonUnitalRingHom (f : M →ₙ* N) : R[M] →ₙ+* R[N] where
  toFun := mapDomain f
  map_zero' := mapDomain_zero _
  map_add' := mapDomain_add _
  map_mul' := mapDomain_mul f

@[to_additive (dont_translate := R) (attr := simp)]
lemma mapDomainNonUnitalRingHom_id : mapDomainNonUnitalRingHom R (.id M) = .id R[M] := by ext; simp

@[to_additive (dont_translate := R) (attr := simp)]
lemma mapDomainNonUnitalRingHom_comp (f : N →ₙ* O) (g : M →ₙ* N) :
    mapDomainNonUnitalRingHom R (f.comp g) =
      (mapDomainNonUnitalRingHom R f).comp (mapDomainNonUnitalRingHom R g) := by
  ext; simp [Finsupp.mapDomain_comp]

variable (R) in
/-- Equivalent monoids have additively isomorphic monoid algebras.

`MonoidAlgebra.mapDomain` as an `AddEquiv`. -/
@[to_additive (dont_translate := R)
/-- Equivalent additive monoids have additively isomorphic additive monoid algebras.

`AddMonoidAlgebra.mapDomain` as an `AddEquiv`. -/]
def mapDomainAddEquiv (e : M ≃ N) : R[M] ≃+ R[N] where
  toFun x := x.mapDomain e
  invFun x := x.mapDomain e.symm
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' x y := by ext; simp

@[to_additive (attr := simp)]
lemma mapDomainAddEquiv_apply (e : M ≃ N) (x : R[M]) (n : N) :
    mapDomainAddEquiv R e x n = x (e.symm n) := by simp [mapDomainAddEquiv]

@[to_additive (attr := simp)]
lemma mapDomainAddEquiv_single (e : M ≃ N) (r : R) (m : M) :
    mapDomainAddEquiv R e (single m r) = single (e m) r := by simp [mapDomainAddEquiv]

@[to_additive (attr := simp)]
lemma symm_mapDomainAddEquiv (e : M ≃ N) :
    (mapDomainAddEquiv R e).symm = mapDomainAddEquiv R e.symm := rfl

@[to_additive (attr := simp)]
lemma mapDomainAddEquiv_trans (e₁ : M ≃ N) (e₂ : N ≃ O) :
    mapDomainAddEquiv R (e₁.trans e₂) =
      (mapDomainAddEquiv R e₁).trans (mapDomainAddEquiv R e₂) := by ext; simp

variable (M) in
/-- Additively isomorphic rings have additively isomorphic monoid algebras.

`Finsupp.mapRange` as an `AddEquiv`. -/
@[to_additive (dont_translate := R S)
/-- Additively isomorphic rings have additively isomorphic additive monoid algebras.

`Finsupp.mapRange` as an `AddEquiv`. -/]
def mapRangeAddEquiv (e : R ≃+ S) : R[M] ≃+ S[M] where
  toFun x := .mapRange e e.map_zero x
  invFun x := .mapRange e.symm e.symm.map_zero x
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' x y := by ext; simp

@[to_additive (attr := simp)]
lemma mapRangeAddEquiv_apply (e : R ≃+ S) (x : R[M]) (m : M) :
    mapRangeAddEquiv M e x m = e (x m) := by simp [mapRangeAddEquiv]

@[to_additive (attr := simp)]
lemma mapRangeAddEquiv_single (e : R ≃+ S) (r : R) (m : M) :
    mapRangeAddEquiv M e (single m r) = single m (e r) := by simp [mapRangeAddEquiv]

@[to_additive (attr := simp)]
lemma symm_mapRangeAddEquiv (e : R ≃+ S) :
    (mapRangeAddEquiv M e).symm = mapRangeAddEquiv M e.symm := rfl

@[to_additive (attr := simp)]
lemma mapRangeAddEquiv_trans (e₁ : R ≃+ S) (e₂ : S ≃+ T) :
    mapRangeAddEquiv M (e₁.trans e₂) = (mapRangeAddEquiv M e₁).trans (mapRangeAddEquiv M e₂) := by
  ext; simp

end Mul

variable [Monoid M] [Monoid N] [Monoid O]

variable (R) in
/-- If `f : G → H` is a multiplicative homomorphism between two monoids, then
`MonoidAlgebra.mapDomain f` is a ring homomorphism between their monoid algebras. -/
@[to_additive (attr := simps) /--
If `f : G → H` is a multiplicative homomorphism between two additive monoids, then
`AddMonoidAlgebra.mapDomain f` is a ring homomorphism between their additive monoid algebras. -/]
def mapDomainRingHom (f : M →* N) : R[M] →+* R[N] where
  toFun := mapDomain f
  map_zero' := mapDomain_zero _
  map_add' := mapDomain_add _
  map_one' := mapDomain_one f
  map_mul' := mapDomain_mul f

attribute [local ext high] ringHom_ext

@[to_additive (dont_translate := R) (attr := simp)]
lemma mapDomainRingHom_id : mapDomainRingHom R (.id M) = .id R[M] := by ext <;> simp

@[to_additive (dont_translate := R) (attr := simp)]
lemma mapDomainRingHom_comp (f : N →* O) (g : M →* N) :
    mapDomainRingHom R (f.comp g) = (mapDomainRingHom R f).comp (mapDomainRingHom R g) := by
  ext <;> simp

variable (M) in
/-- The ring homomorphism of monoid algebras induced by a homomorphism of the base rings. -/
@[to_additive (dont_translate := R S)
/-- The ring homomorphism of additive monoid algebras induced by a homomorphism of the base rings.
-/]
noncomputable def mapRangeRingHom (f : R →+* S) : R[M] →+* S[M] where
  toFun := mapRange f f.map_zero
  map_zero' := mapRange_zero
  map_add' := mapRange_add f.map_add
  map_one' := by ext; simp [one_def]
  map_mul' _ _ := by
    classical
    ext
    simp [mul_def]
    simp [MonoidAlgebra, sum_mapRange_index, map_finsuppSum, single_apply, apply_ite]

@[to_additive]
lemma coe_mapRangeRingHom (f : R →+* S) :
    ⇑(mapRangeRingHom M f) = mapRange f (map_zero _) := by
  simp [mapRangeRingHom]

@[to_additive (attr := simp)]
lemma mapRangeRingHom_apply (f : R →+* S) (x : R[M]) (m : M) :
    mapRangeRingHom M f x m = f (x m) := by simp [mapRangeRingHom]

@[to_additive (attr := simp)]
lemma mapRangeRingHom_single (f : R →+* S) (a : M) (b : R) :
    mapRangeRingHom M f (single a b) = single a (f b) := by
  classical ext; simp [single_apply, apply_ite f]

@[to_additive (dont_translate := R) (attr := simp)]
lemma mapRangeRingHom_id : mapRangeRingHom M (.id R) = .id R[M] := by ext <;> simp

@[to_additive (dont_translate := R S T) (attr := simp)]
lemma mapRangeRingHom_comp (f : S →+* T) (g : R →+* S) :
    mapRangeRingHom M (f.comp g) = (mapRangeRingHom M f).comp (mapRangeRingHom M g) := by
  ext <;> simp

@[to_additive (dont_translate := R S)]
lemma mapRangeRingHom_comp_mapDomainRingHom (f : R →+* S) (g : M →* N) :
    (mapRangeRingHom N f).comp (mapDomainRingHom R g) =
      (mapDomainRingHom S g).comp (mapRangeRingHom M f) := by aesop

variable (R) in
/-- Isomorphic monoids have isomorphic monoid algebras. -/
@[to_additive (dont_translate := R)
/-- Isomorphic monoids have isomorphic additive monoid algebras. -/]
def mapDomainRingEquiv (e : M ≃* N) : R[M] ≃+* R[N] :=
  .ofRingHom (MonoidAlgebra.mapDomainRingHom R e) (MonoidAlgebra.mapDomainRingHom R e.symm)
    (by apply MonoidAlgebra.ringHom_ext <;> simp) (by apply MonoidAlgebra.ringHom_ext <;> simp)

@[to_additive (attr := simp)]
lemma mapDomainRingEquiv_apply (e : M ≃* N) (x : R[M]) (n : N) :
    mapDomainRingEquiv R e x n = x (e.symm n) := mapDomainAddEquiv_apply ..

@[to_additive (attr := simp)]
lemma mapDomainRingEquiv_single (e : M ≃* N) (r : R) (m : M) :
    mapDomainRingEquiv R e (single m r) = single (e m) r := by simp [mapDomainRingEquiv]

@[to_additive]
lemma toRingHom_mapDomainRingEquiv (e : M ≃* N) :
    (mapDomainRingEquiv R e).toRingHom = mapDomainRingHom R e := rfl

@[to_additive (attr := simp)]
lemma symm_mapDomainRingEquiv (e : M ≃* N) :
    (mapDomainRingEquiv R e).symm = mapDomainRingEquiv R e.symm := rfl

@[to_additive (attr := simp)]
lemma mapDomainRingEquiv_trans (e₁ : M ≃* N) (e₂ : N ≃* O) :
    mapDomainRingEquiv R (e₁.trans e₂) =
      (mapDomainRingEquiv R e₁).trans (mapDomainRingEquiv R e₂) := by ext; simp

variable (M) in
/-- Isomorphic rings have isomorphic monoid algebras. -/
@[to_additive (dont_translate := R S)
/-- Isomorphic rings have isomorphic additive monoid algebras. -/]
def mapRangeRingEquiv (e : R ≃+* S) : R[M] ≃+* S[M] :=
  .ofRingHom (MonoidAlgebra.mapRangeRingHom M e) (MonoidAlgebra.mapRangeRingHom M e.symm)
    (by apply MonoidAlgebra.ringHom_ext <;> simp) (by apply MonoidAlgebra.ringHom_ext <;> simp)

@[to_additive (attr := simp)]
lemma mapRangeRingEquiv_apply (e : R ≃+* S) (x : R[M]) (m : M) :
    mapRangeRingEquiv M e x m = e (x m) := by simp [mapRangeRingEquiv]

@[to_additive (attr := simp)]
lemma mapRangeRingEquiv_single (e : R ≃+* S) (r : R) (m : M) :
    mapRangeRingEquiv M e (single m r) = single m (e r) := by simp [mapRangeRingEquiv]

@[to_additive]
lemma toRingHom_mapRangeRingEquiv (e : R ≃+* S) :
    (mapRangeRingEquiv M e).toRingHom = mapRangeRingHom M e := rfl

@[to_additive (attr := simp)]
lemma symm_mapRangeRingEquiv (e : R ≃+* S) :
    (mapRangeRingEquiv M e).symm = mapRangeRingEquiv M e.symm := rfl

@[to_additive (attr := simp)]
lemma mapRangeRingEquiv_trans (e₁ : R ≃+* S) (e₂ : S ≃+* T) :
    mapRangeRingEquiv M (e₁.trans e₂) =
      (mapRangeRingEquiv M e₁).trans (mapRangeRingEquiv M e₂) := by ext; simp

/-- Nested monoid algebras can be taken in an arbitrary order. -/
@[to_additive (dont_translate := R)
/-- Nested additive monoid algebras can be taken in an arbitrary order. -/]
def commRingEquiv : R[M][N] ≃+* R[N][M] :=
  curryRingEquiv.symm.trans <| .trans (mapDomainRingEquiv _ <| .prodComm ..) curryRingEquiv

@[to_additive (attr := simp)]
lemma symm_commRingEquiv : (commRingEquiv : R[M][N] ≃+* R[N][M]).symm = commRingEquiv := rfl

@[to_additive (dont_translate := R) (attr := simp)]
lemma commRingEquiv_single_single (m : M) (n : N) (r : R) :
    commRingEquiv (single m <| single n r) = single n (single m r) := by
  simp [commRingEquiv, MonoidAlgebra, curryRingEquiv, curryAddEquiv, mapDomainRingEquiv,
    mapDomainRingHom, EquivLike.toEquiv]

end MonoidAlgebra

/-!
#### Conversions between `AddMonoidAlgebra` and `MonoidAlgebra`

We have not defined `AddMonoidAlgebra k G = MonoidAlgebra k (Multiplicative G)`
because historically this caused problems;
since the changes that have made `nsmul` definitional, this would be possible,
but for now we just construct the ring isomorphisms using `RingEquiv.refl _`.
-/

variable (k G) in
/-- The equivalence between `AddMonoidAlgebra` and `MonoidAlgebra` in terms of
`Multiplicative` -/
protected def AddMonoidAlgebra.toMultiplicative [Semiring k] [Add G] :
    AddMonoidAlgebra k G ≃+* MonoidAlgebra k (Multiplicative G) where
  toFun x := x.mapDomain .ofAdd
  invFun x := x.mapDomain Multiplicative.toAdd
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' := mapDomain_add _
  map_mul' x y := by
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
  map_add' := mapDomain_add _
  map_mul' := MonoidAlgebra.mapDomain_mul (MulHom.id G)
