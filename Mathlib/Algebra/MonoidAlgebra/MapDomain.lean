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

assert_not_exists NonUnitalAlgHom AlgEquiv

@[expose] public noncomputable section

open Function
open Finsupp hiding single mapDomain

variable {ι F R S T M N O : Type*}

namespace MonoidAlgebra
section Semiring
variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

/-- Given a function `f : M → N` between magmas, return the corresponding map `R[M] → R[N]` obtained
by summing the coefficients along each fiber of `f`. -/
@[to_additive /--
Given a function `f : M → N` between magmas, return the corresponding map `R[M] → R[N]` obtained
by summing the coefficients along each fiber of `f`. -/]
abbrev mapDomain (f : M → N) (x : R[M]) : R[N] := Finsupp.mapDomain f x

@[to_additive (attr := simp)]
lemma coeff_mapDomain (f : M → N) (x : R[M]) :
    (mapDomain f x).coeff = x.coeff.mapDomain f := rfl

/-- This isn't marked as simp to avoid looping with unfolding `coeff`. -/
@[to_additive /-- This isn't marked as simp to avoid looping with unfolding `coeff`. -/]
lemma ofCoeff_mapDomain (f : M → N) (x : M →₀ R) :
    ofCoeff (.mapDomain f x) = mapDomain f (ofCoeff x) := rfl

@[to_additive]
lemma mapDomain_zero (f : M → N) : mapDomain f (0 : R[M]) = 0 := Finsupp.mapDomain_zero ..

@[to_additive]
lemma mapDomain_add (f : M → N) (x y : R[M]) :
    mapDomain f (x + y) = mapDomain f x + mapDomain f y := Finsupp.mapDomain_add ..

@[to_additive]
lemma mapDomain_sum (f : M → N) (x : S[M]) (v : M → S → R[M]) :
    mapDomain f (x.sum v) = x.sum fun a b ↦ mapDomain f (v a b) := Finsupp.mapDomain_sum

@[to_additive]
lemma mapDomain_single : mapDomain f (single a r) = single (f a) r := by ext; simp

@[to_additive]
lemma mapDomain_injective (hf : Injective f) : Injective (mapDomain (R := R) f) :=
  Finsupp.mapDomain_injective hf

@[to_additive (dont_translate := R) (attr := simp) mapDomain_one]
theorem mapDomain_one [One M] [One N] {F : Type*} [FunLike F M N] [OneHomClass F M N] (f : F) :
    mapDomain f (1 : R[M]) = (1 : R[N]) := by
  simp [one_def]

/-- Given a map `f : R →+ S`, return the corresponding map `R[M] → S[M]` obtained by mapping
each coefficient along `f`. -/
@[to_additive
/-- Given a map `f : R →+ S`, return the corresponding map `R[M] → S[M]` obtained by mapping
each coefficient along `f`. -/]
def map (f : R →+ S) (x : R[M]) : S[M] := .ofCoeff <| x.coeff.mapRange f f.map_zero

@[to_additive (attr := simp)]
lemma coeff_map (f : R →+ S) (x : R[M]) :
    (map f x).coeff = x.coeff.mapRange f f.map_zero := rfl

/-- This isn't marked as simp to avoid looping with unfolding `coeff`. -/
@[to_additive /-- This isn't marked as simp to avoid looping with unfolding `coeff`. -/]
lemma ofCoeff_mapRange (f : R →+ S) (x : M →₀ R) :
    ofCoeff (.mapRange f f.map_zero x) = map f (ofCoeff x) := rfl

@[to_additive (attr := simp)]
protected lemma map_zero (f : R →+ S) : map f (0 : R[M]) = 0 := mapRange_zero (hf := f.map_zero)

@[to_additive]
protected lemma map_add (f : R →+ S) (x y : R[M]) : map f (x + y) = map f x + map f y :=
  mapRange_add (hf := f.map_zero) f.map_add ..

@[to_additive]
protected lemma map_sum (f : R →+ S) (s : Finset ι) (x : ι → R[M]) :
    map f (∑ i ∈ s, x i) = ∑ i ∈ s, map f (x i) := mapRange_finset_sum ..

@[to_additive (attr := simp)]
lemma map_single (f : R →+ S) (r : R) (m : M) : map f (single m r) = single m (f r) :=
  mapRange_single (hf := f.map_zero)

@[to_additive (attr := simp)]
lemma map_id (x : R[M]) : map (.id R) x = x := by simp [map, coeff, ofCoeff]

@[to_additive (attr := simp)]
lemma map_map (f : S →+ T) (g : R →+ S) (x : R[M]) :
    map f (map g x) = map (f.comp g) x := by simp [map, coeff, ofCoeff]

@[to_additive]
lemma range_map (f : R →+ S) : Set.range (map (M := M) f) = {x | ∀ i, x.coeff i ∈ Set.range f} :=
  calc
    _ = coeffEquiv ⁻¹' (Set.range (mapRange f (map_zero f) ∘ coeffEquiv)) := by
      simp_rw [comp_def, Equiv.eq_preimage_iff_image_eq, ← Set.range_comp', coeffEquiv_apply,
        coeff_map]
    _ = _ := by simp [Finsupp.range_mapRange]

/-- `MonoidAlgebra.map` of an injective function is injective. -/
@[to_additive /-- `AddMonoidAlgebra.map` of an injective function is injective. -/]
lemma map_injective (f : R →+ S) (he : Injective f) : Injective (map (M := M) f) := by
  change Injective (coeffEquiv.symm ∘ Finsupp.mapRange f (map_zero f) ∘ coeffEquiv)
  simpa using mapRange_injective _ (map_zero f) he

/-- `MonoidAlgebra.map` of a surjective function is surjective. -/
@[to_additive /-- `AddMonoidAlgebra.map` of an surjective function is surjective. -/]
lemma map_surjective (f : R →+ S) (he : Surjective f) : Surjective (map (M := M) f) := by
  change Surjective (coeffEquiv.symm ∘ Finsupp.mapRange f (map_zero f) ∘ coeffEquiv)
  simpa [comp_def] using mapRange_surjective _ (map_zero f) he

/-- Pullback the coefficients of an element of `R[N]` under an injective `f : M → N`.

Coefficients not in the range of `f` are dropped. -/
@[to_additive
/-- Pullback the coefficients of an element of `R[N]` under an injective `f : M → N`.

Coefficients not in the range of `f` are dropped. -/]
def comapDomain (f : M → N) (hf : Injective f) (x : R[N]) : R[M] :=
  .ofCoeff <| x.coeff.comapDomain f hf.injOn

@[to_additive (attr := simp)]
lemma coeff_comapDomain (f : M → N) (hf) (x : R[N]) :
    (comapDomain f hf x).coeff = x.coeff.comapDomain f hf.injOn := by simp [comapDomain]

@[to_additive (attr := simp)]
lemma comapDomain_zero (f : M → N) (hf) : comapDomain f hf (0 : R[N]) = 0 := by simp [comapDomain]

@[to_additive (attr := simp)]
lemma comapDomain_add (f : M → N) (hf) (x y : R[N]) :
    comapDomain f hf (x + y) = comapDomain f hf x + comapDomain f hf y := by
  simp [comapDomain, comapDomain_add_of_injective hf]

@[simp]
lemma comapDomain_single_of_not_mem_range {r : R} {n : N} (hn : n ∉ Set.range f) (hf) :
    comapDomain f hf (single n r) = 0 := by simp [comapDomain, coeff, single, *]

/-- `comapDomain` as an `AddMonoidHom. -/
@[to_additive (attr := simps) comapDomainAddMonoidHom /-- `comapDomain` as an `AddMonoidHom. -/]
def comapDomainAddMonoidHom (f : M → N) (hf : Injective f) : R[N] →+ R[M] where
  toFun := comapDomain f hf
  map_zero' := by simp
  map_add' := by simp

@[to_additive (attr := simp)]
lemma comapDomain_single_map (f : M → N) (hf) (m : M) (r : R) :
    comapDomain f hf (single (f m) r) = single m r := by simp [comapDomain, single, coeff, ofCoeff]

@[to_additive]
lemma mapDomain_comapDomain {f : M → N} {x : R[N]} (hx : ↑x.coeff.support ⊆ Set.range f) (hf) :
    mapDomain f (comapDomain f hf x) = x := Finsupp.mapDomain_comapDomain _ hf _ hx

section Mul
variable [Mul M] [Mul N] [Mul O] [FunLike F M N] [MulHomClass F M N]

set_option backward.isDefEq.respectTransparency false in
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

`MonoidAlgebra.map` as an `AddEquiv`. -/
@[to_additive (dont_translate := R S)
/-- Additively isomorphic rings have additively isomorphic additive monoid algebras.

`AddMonoidAlgebra.map` as an `AddEquiv`. -/]
def mapAddEquiv (e : R ≃+ S) : R[M] ≃+ S[M] where
  toFun := .map e
  invFun := .map e.symm
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' := MonoidAlgebra.map_add _

@[deprecated (since := "2026-03-20")] alias mapRangeAddEquiv := mapAddEquiv

@[to_additive (attr := simp)]
lemma mapAddEquiv_apply (e : R ≃+ S) (x : R[M]) (m : M) :
    mapAddEquiv M e x m = e (x m) := by simp [mapAddEquiv, map, coeff, ofCoeff]

@[deprecated (since := "2026-03-20")] alias mapRangeAddEquiv_apply := mapAddEquiv_apply

@[to_additive (attr := simp)]
lemma mapAddEquiv_single (e : R ≃+ S) (r : R) (m : M) :
    mapAddEquiv M e (single m r) = single m (e r) := by simp [mapAddEquiv]

@[deprecated (since := "2026-03-20")] alias mapRangeAddEquiv_single := mapAddEquiv_single

@[to_additive (attr := simp)]
lemma symm_mapAddEquiv (e : R ≃+ S) :
    (mapAddEquiv M e).symm = mapAddEquiv M e.symm := rfl

@[deprecated (since := "2026-03-20")] alias symm_mapRangeAddEquiv := symm_mapAddEquiv

@[to_additive (attr := simp)]
lemma mapAddEquiv_trans (e₁ : R ≃+ S) (e₂ : S ≃+ T) :
    mapAddEquiv M (e₁.trans e₂) = (mapAddEquiv M e₁).trans (mapAddEquiv M e₂) := by
  ext; simp

@[deprecated (since := "2026-03-20")] alias mapRangeAddEquiv_trans := mapAddEquiv_trans

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp) (dont_translate := R S) map_mul]
protected lemma map_mul (f : R →+* S) (x y : R[M]) :
    map (f : R →+ S) (x * y) = map f x * map f y := by
  classical
  ext
  simp [mul_def]
  simp [MonoidAlgebra, sum_mapRange_index, map_finsuppSum, single_apply, apply_ite, map,
    coeff, ofCoeff]

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

@[to_additive (attr := simp) (dont_translate := R S) map_one]
protected lemma map_one (f : R →+* S) : map f (1 : R[M]) = (1 : S[M]) := by ext; simp [one_def]

variable (M) in
/-- The ring homomorphism of monoid algebras induced by a homomorphism of the base rings. -/
@[to_additive (dont_translate := R S)
/-- The ring homomorphism of additive monoid algebras induced by a homomorphism of the base rings.
-/]
noncomputable def mapRingHom (f : R →+* S) : R[M] →+* S[M] where
  toFun := .map f
  map_zero' := MonoidAlgebra.map_zero _
  map_add' := MonoidAlgebra.map_add _
  map_one' := MonoidAlgebra.map_one _
  map_mul' := MonoidAlgebra.map_mul _

@[deprecated (since := "2026-03-20")] alias mapRangeRingHom := mapRingHom

@[to_additive]
lemma coe_mapRingHom (f : R →+* S) : ⇑(mapRingHom M f) = map f := rfl

@[deprecated (since := "2026-03-20")] alias coe_mapRangeRingHom := coe_mapRingHom

@[to_additive (attr := simp)]
lemma mapRingHom_apply (f : R →+* S) (x : R[M]) (m : M) :
    mapRingHom M f x m = f (x m) := by simp [mapRingHom, map, coeff, ofCoeff]

@[deprecated (since := "2026-03-20")] alias mapRangeRingHom_apply := mapRingHom_apply

@[to_additive (attr := simp)]
lemma mapRingHom_single (f : R →+* S) (a : M) (b : R) :
    mapRingHom M f (single a b) = single a (f b) := by
  classical ext; simp [single_apply, apply_ite f]

@[deprecated (since := "2026-03-20")] alias mapRangeRingHom_single := mapRingHom_single

@[to_additive (dont_translate := R) (attr := simp)]
lemma mapRingHom_id : mapRingHom M (.id R) = .id R[M] := by ext <;> simp

@[deprecated (since := "2026-03-20")] alias mapRangeRingHom_id := mapRingHom_id

@[to_additive (dont_translate := R S T) (attr := simp)]
lemma mapRingHom_comp (f : S →+* T) (g : R →+* S) :
    mapRingHom M (f.comp g) = (mapRingHom M f).comp (mapRingHom M g) := by
  ext <;> simp

@[deprecated (since := "2026-03-20")] alias mapRangeRingHom_comp := mapRingHom_comp

@[to_additive (dont_translate := R S)]
lemma mapRingHom_comp_mapDomainRingHom (f : R →+* S) (g : M →* N) :
    (mapRingHom N f).comp (mapDomainRingHom R g) =
      (mapDomainRingHom S g).comp (mapRingHom M f) := by aesop

@[deprecated (since := "2026-03-20")]
alias mapRangeRingHom_comp_mapDomainRingHom := mapRingHom_comp_mapDomainRingHom

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
def mapRingEquiv (e : R ≃+* S) : R[M] ≃+* S[M] :=
  .ofRingHom (MonoidAlgebra.mapRingHom M e) (MonoidAlgebra.mapRingHom M e.symm)
    (by apply MonoidAlgebra.ringHom_ext <;> simp) (by apply MonoidAlgebra.ringHom_ext <;> simp)

@[deprecated (since := "2026-03-20")] alias mapRangeRingEquiv := mapRingEquiv

@[to_additive (attr := simp)]
lemma mapRingEquiv_apply (e : R ≃+* S) (x : R[M]) (m : M) :
    mapRingEquiv M e x m = e (x m) := by simp [mapRingEquiv]

@[deprecated (since := "2026-03-20")] alias mapRangeRingEquiv_apply := mapRingEquiv_apply

@[to_additive (attr := simp)]
lemma mapRingEquiv_single (e : R ≃+* S) (r : R) (m : M) :
    mapRingEquiv M e (single m r) = single m (e r) := by simp [mapRingEquiv]

@[deprecated (since := "2026-03-20")] alias mapRangeRingEquiv_single := mapRingEquiv_single

@[to_additive]
lemma toRingHom_mapRingEquiv (e : R ≃+* S) :
    (mapRingEquiv M e).toRingHom = mapRingHom M e := rfl

@[deprecated (since := "2026-03-20")]
alias toRingHom_mapRangeRingEquiv := toRingHom_mapRingEquiv

@[to_additive (attr := simp)]
lemma symm_mapRingEquiv (e : R ≃+* S) :
    (mapRingEquiv M e).symm = mapRingEquiv M e.symm := rfl

@[deprecated (since := "2026-03-20")] alias symm_mapRangeRingEquiv := symm_mapRingEquiv

@[to_additive (attr := simp)]
lemma mapRingEquiv_trans (e₁ : R ≃+* S) (e₂ : S ≃+* T) :
    mapRingEquiv M (e₁.trans e₂) =
      (mapRingEquiv M e₁).trans (mapRingEquiv M e₂) := by ext; simp

@[deprecated (since := "2026-03-20")] alias mapRangeRingEquiv_trans := mapRingEquiv_trans

/-- Nested monoid algebras can be taken in an arbitrary order. -/
@[to_additive (dont_translate := R)
/-- Nested additive monoid algebras can be taken in an arbitrary order. -/]
def commRingEquiv : R[M][N] ≃+* R[N][M] :=
  curryRingEquiv.symm.trans <| .trans (mapDomainRingEquiv _ <| .prodComm ..) curryRingEquiv

@[to_additive (attr := simp)]
lemma symm_commRingEquiv : (commRingEquiv : R[M][N] ≃+* R[N][M]).symm = commRingEquiv := rfl

set_option backward.isDefEq.respectTransparency false in
@[to_additive (dont_translate := R) (attr := simp)]
lemma commRingEquiv_single_single (m : M) (n : N) (r : R) :
    commRingEquiv (single m <| single n r) = single n (single m r) := by
  simp [commRingEquiv, MonoidAlgebra, curryRingEquiv, curryAddEquiv, mapDomainRingEquiv,
    mapDomainRingHom, EquivLike.toEquiv]

end Semiring

section Ring
variable [Ring R] [Ring S]

@[to_additive]
lemma map_neg (f : R →+ S) (x : R[M]) : map f (-x) = -map f x :=
  Finsupp.mapRange_neg (hf := f.map_zero) f.map_neg ..

@[to_additive]
lemma map_sub (f : R →+ S) (x y : R[M]) : map f (x - y) = map f x - map f y :=
  Finsupp.mapRange_sub (hf := f.map_zero) f.map_sub ..

end Ring
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
