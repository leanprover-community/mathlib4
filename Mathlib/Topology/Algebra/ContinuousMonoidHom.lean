/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Nailin Guan
-/
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Homeomorph.Lemmas

/-!

# Continuous Monoid Homs

This file defines the space of continuous homomorphisms between two topological groups.

## Main definitions

* `ContinuousMonoidHom A B`: The continuous homomorphisms `A →* B`.
* `ContinuousAddMonoidHom A B`: The continuous additive homomorphisms `A →+ B`.
-/

assert_not_exists ContinuousLinearMap
assert_not_exists ContinuousLinearEquiv

section

open Function Topology

variable (F A B C D E : Type*)
variable [Monoid A] [Monoid B] [Monoid C] [Monoid D]
variable [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]

/-- The type of continuous additive monoid homomorphisms from `A` to `B`.

When possible, instead of parametrizing results over `(f : ContinuousAddMonoidHom A B)`,
you should parametrize
over `(F : Type*) [FunLike F A B] [ContinuousMapClass F A B] [AddMonoidHomClass F A B] (f : F)`.

When you extend this structure,
make sure to extend `ContinuousMapClass` and/or `AddMonoidHomClass`, if needed. -/
structure ContinuousAddMonoidHom (A B : Type*) [AddMonoid A] [AddMonoid B] [TopologicalSpace A]
  [TopologicalSpace B] extends A →+ B, C(A, B)

/-- The type of continuous monoid homomorphisms from `A` to `B`.

When possible, instead of parametrizing results over `(f : ContinuousMonoidHom A B)`,
you should parametrize
over `(F : Type*) [FunLike F A B] [ContinuousMapClass F A B] [MonoidHomClass F A B] (f : F)`.

When you extend this structure,
make sure to extend `ContinuousMapClass` and/or `MonoidHomClass`, if needed. -/
@[to_additive /-- The type of continuous additive monoid homomorphisms from `A` to `B`. -/]
structure ContinuousMonoidHom extends A →* B, C(A, B)

/-- Reinterpret a `ContinuousMonoidHom` as a `MonoidHom`. -/
add_decl_doc ContinuousMonoidHom.toMonoidHom

/-- Reinterpret a `ContinuousAddMonoidHom` as an `AddMonoidHom`. -/
add_decl_doc ContinuousAddMonoidHom.toAddMonoidHom

/-- Reinterpret a `ContinuousMonoidHom` as a `ContinuousMap`. -/
add_decl_doc ContinuousMonoidHom.toContinuousMap

/-- Reinterpret a `ContinuousAddMonoidHom` as a `ContinuousMap`. -/
add_decl_doc ContinuousAddMonoidHom.toContinuousMap

namespace ContinuousMonoidHom

/-- The type of continuous monoid homomorphisms from `A` to `B`.-/
infixr:25 " →ₜ+ " => ContinuousAddMonoidHom
/-- The type of continuous monoid homomorphisms from `A` to `B`.-/
infixr:25 " →ₜ* " => ContinuousMonoidHom

variable {A B C D E}

@[to_additive]
instance instFunLike : FunLike (A →ₜ* B) A B where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    congr

@[to_additive]
instance instMonoidHomClass : MonoidHomClass (A →ₜ* B) A B where
  map_mul f := f.map_mul'
  map_one f := f.map_one'

@[to_additive]
instance instContinuousMapClass : ContinuousMapClass (A →ₜ* B) A B where
  map_continuous f := f.continuous_toFun

@[to_additive (attr := simp)]
lemma coe_toMonoidHom (f : A →ₜ* B) : f.toMonoidHom = f := rfl

@[to_additive (attr := simp)]
lemma coe_toContinuousMap (f : A →ₜ* B) : f.toContinuousMap = f := rfl

section

variable {F : Type*} [FunLike F A B]

/-- Turn an element of a type `F` satisfying `MonoidHomClass F A B` and `ContinuousMapClass F A B`
into a`ContinuousMonoidHom`. This is declared as the default coercion from `F` to
`(A →ₜ* B)`. -/
@[to_additive (attr := coe) /-- Turn an element of a type `F` satisfying
`AddMonoidHomClass F A B` and `ContinuousMapClass F A B` into a`ContinuousAddMonoidHom`.
This is declared as the default coercion from `F` to `ContinuousAddMonoidHom A B`. -/]
def toContinuousMonoidHom [MonoidHomClass F A B] [ContinuousMapClass F A B] (f : F) : A →ₜ* B :=
  { MonoidHomClass.toMonoidHom f with }

/-- Any type satisfying `MonoidHomClass` and `ContinuousMapClass` can be cast into
`ContinuousMonoidHom` via `ContinuousMonoidHom.toContinuousMonoidHom`. -/
@[to_additive /-- Any type satisfying `AddMonoidHomClass` and `ContinuousMapClass` can be cast into
`ContinuousAddMonoidHom` via `ContinuousAddMonoidHom.toContinuousAddMonoidHom`. -/]
instance [MonoidHomClass F A B] [ContinuousMapClass F A B] : CoeOut F (A →ₜ* B) :=
  ⟨ContinuousMonoidHom.toContinuousMonoidHom⟩

@[to_additive (attr := simp)]
lemma coe_coe [MonoidHomClass F A B] [ContinuousMapClass F A B] (f : F) :
    ⇑(f : A →ₜ* B) = f := rfl

@[to_additive (attr := simp, norm_cast)]
lemma toMonoidHom_toContinuousMonoidHom [MonoidHomClass F A B] [ContinuousMapClass F A B] (f : F) :
    ((f : A →ₜ* B) : A →* B) = f := rfl

@[to_additive (attr := simp, norm_cast)]
lemma toContinuousMap_toContinuousMonoidHom [MonoidHomClass F A B] [ContinuousMapClass F A B]
    (f : F) : ((f : A →ₜ* B) : C(A, B)) = f := rfl

end

@[to_additive (attr := ext)]
theorem ext {f g : A →ₜ* B} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

@[to_additive]
theorem toContinuousMap_injective : Injective (toContinuousMap : _ → C(A, B)) := fun f g h =>
  ext <| by convert DFunLike.ext_iff.1 h

/-- Composition of two continuous homomorphisms. -/
@[to_additive (attr := simps!) /-- Composition of two continuous homomorphisms. -/]
def comp (g : B →ₜ* C) (f : A →ₜ* B) : A →ₜ* C :=
  ⟨g.toMonoidHom.comp f.toMonoidHom, (map_continuous g).comp (map_continuous f)⟩

@[to_additive (attr := simp)]
lemma coe_comp (g : ContinuousMonoidHom B C) (f : ContinuousMonoidHom A B) :
    ⇑(g.comp f) = ⇑g ∘ ⇑f := rfl

/-- Product of two continuous homomorphisms on the same space. -/
@[to_additive (attr := simps!) prod
/-- Product of two continuous homomorphisms on the same space. -/]
def prod (f : A →ₜ* B) (g : A →ₜ* C) : A →ₜ* (B × C) :=
  ⟨f.toMonoidHom.prod g.toMonoidHom, f.continuous_toFun.prodMk g.continuous_toFun⟩

/-- Product of two continuous homomorphisms on different spaces. -/
@[to_additive (attr := simps!) prodMap
  /-- Product of two continuous homomorphisms on different spaces. -/]
def prodMap (f : A →ₜ* C) (g : B →ₜ* D) :
    (A × B) →ₜ* (C × D) :=
  ⟨f.toMonoidHom.prodMap g.toMonoidHom, f.continuous_toFun.prodMap g.continuous_toFun⟩

variable (A B C D E)

/-- The trivial continuous homomorphism. -/
@[to_additive (attr := simps!) /-- The trivial continuous homomorphism. -/]
instance : One (A →ₜ* B) where
  one := ⟨1, continuous_const⟩

@[to_additive (attr := simp)]
lemma coe_one : ⇑(1 : A →ₜ* B) = 1 :=
  rfl

@[to_additive]
instance : Inhabited (A →ₜ* B) := ⟨1⟩

/-- The identity continuous homomorphism. -/
@[to_additive (attr := simps!) /-- The identity continuous homomorphism. -/]
def id : A →ₜ* A := ⟨.id A, continuous_id⟩

@[to_additive (attr := simp)]
lemma coe_id : ⇑(ContinuousMonoidHom.id A) = _root_.id :=
  rfl

/-- The continuous homomorphism given by projection onto the first factor. -/
@[to_additive (attr := simps!)
  /-- The continuous homomorphism given by projection onto the first factor. -/]
def fst : (A × B) →ₜ* A := ⟨MonoidHom.fst A B, continuous_fst⟩

/-- The continuous homomorphism given by projection onto the second factor. -/
@[to_additive (attr := simps!)
  /-- The continuous homomorphism given by projection onto the second factor. -/]
def snd : (A × B) →ₜ* B :=
  ⟨MonoidHom.snd A B, continuous_snd⟩

/-- The continuous homomorphism given by inclusion of the first factor. -/
@[to_additive (attr := simps!)
  /-- The continuous homomorphism given by inclusion of the first factor. -/]
def inl : A →ₜ* (A × B) :=
  prod (id A) 1

/-- The continuous homomorphism given by inclusion of the second factor. -/
@[to_additive (attr := simps!)
  /-- The continuous homomorphism given by inclusion of the second factor. -/]
def inr : B →ₜ* (A × B) :=
  prod 1 (id B)


/-- The continuous homomorphism given by the diagonal embedding. -/
@[to_additive (attr := simps!) /-- The continuous homomorphism given by the diagonal embedding. -/]
def diag : A →ₜ* (A × A) := prod (id A) (id A)

/-- The continuous homomorphism given by swapping components. -/
@[to_additive (attr := simps!) /-- The continuous homomorphism given by swapping components. -/]
def swap : (A × B) →ₜ* (B × A) := prod (snd A B) (fst A B)

section CommMonoid
variable [CommMonoid E] [TopologicalSpace E] [ContinuousMul E]

/-- The continuous homomorphism given by multiplication. -/
@[to_additive (attr := simps!) /-- The continuous homomorphism given by addition. -/]
def mul : (E × E) →ₜ* E := ⟨mulMonoidHom, continuous_mul⟩

variable {A B C D E}

@[to_additive]
instance : CommMonoid (A →ₜ* E) where
  mul f g := (mul E).comp (f.prod g)
  mul_comm f g := ext fun x => mul_comm (f x) (g x)
  mul_assoc f g h := ext fun x => mul_assoc (f x) (g x) (h x)
  one_mul f := ext fun x => one_mul (f x)
  mul_one f := ext fun x => mul_one (f x)

/-- Coproduct of two continuous homomorphisms to the same space. -/
@[to_additive (attr := simps!) /-- Coproduct of two continuous homomorphisms to the same space. -/]
def coprod (f : ContinuousMonoidHom A E) (g : ContinuousMonoidHom B E) :
    ContinuousMonoidHom (A × B) E :=
  (mul E).comp (f.prodMap g)

end CommMonoid

section CommGroup

variable [CommGroup E] [TopologicalSpace E] [IsTopologicalGroup E]
/-- The continuous homomorphism given by inversion. -/
@[to_additive (attr := simps!) /-- The continuous homomorphism given by negation. -/]
def inv : ContinuousMonoidHom E E :=
  ⟨invMonoidHom, continuous_inv⟩

@[to_additive]
instance : CommGroup (ContinuousMonoidHom A E) where
  __ : CommMonoid (ContinuousMonoidHom A E) := inferInstance
  inv f := (inv E).comp f
  inv_mul_cancel f := ext fun x => inv_mul_cancel (f x)
  div f g := .comp ⟨divMonoidHom, continuous_div'⟩ (f.prod g)
  div_eq_mul_inv f g := ext fun x => div_eq_mul_inv (f x) (g x)

end CommGroup

/-- For `f : F` where `F` is a class of continuous monoid hom, this yields an element
`ContinuousMonoidHom A B`. -/
@[to_additive /-- For `f : F` where `F` is a class of continuous additive monoid hom, this yields
an element `ContinuousAddMonoidHom A B`. -/]
def ofClass (F : Type*) [FunLike F A B] [ContinuousMapClass F A B]
    [MonoidHomClass F A B] (f : F) : (ContinuousMonoidHom A B) := toContinuousMonoidHom f

end ContinuousMonoidHom

end

section

/-!

# Continuous MulEquiv

This section defines the space of continuous isomorphisms between two topological groups.

## Main definitions

-/

universe u v

variable (G : Type u) [TopologicalSpace G] (H : Type v) [TopologicalSpace H]

/-- The structure of two-sided continuous isomorphisms between additive groups.
Note that both the map and its inverse have to be continuous. -/
structure ContinuousAddEquiv [Add G] [Add H] extends G ≃+ H, G ≃ₜ H

/-- The structure of two-sided continuous isomorphisms between groups.
Note that both the map and its inverse have to be continuous. -/
@[to_additive /-- The structure of two-sided continuous isomorphisms between additive groups.
Note that both the map and its inverse have to be continuous. -/]
structure ContinuousMulEquiv [Mul G] [Mul H] extends G ≃* H, G ≃ₜ H

/-- The homeomorphism induced from a two-sided continuous isomorphism of groups. -/
add_decl_doc ContinuousMulEquiv.toHomeomorph

/-- The homeomorphism induced from a two-sided continuous isomorphism additive groups. -/
add_decl_doc ContinuousAddEquiv.toHomeomorph

@[inherit_doc]
infixl:25 " ≃ₜ* " => ContinuousMulEquiv

@[inherit_doc]
infixl:25 " ≃ₜ+ " => ContinuousAddEquiv

section

namespace ContinuousMulEquiv

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] [Mul M] [Mul N]

section coe

@[to_additive]
instance : EquivLike (M ≃ₜ* N) M N where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    cases f
    cases g
    congr
    exact MulEquiv.ext_iff.mpr (congrFun h₁)

@[to_additive]
instance : MulEquivClass (M ≃ₜ* N) M N where
  map_mul f := f.map_mul'

@[to_additive]
instance : HomeomorphClass (M ≃ₜ* N) M N where
  map_continuous f := f.continuous_toFun
  inv_continuous f := f.continuous_invFun

/-- Two continuous multiplicative isomorphisms agree if they are defined by the
same underlying function. -/
@[to_additive (attr := ext) /-- Two continuous additive isomorphisms agree if they are defined by
the same underlying function. -/]
theorem ext {f g : M ≃ₜ* N} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[to_additive (attr := simp)]
theorem coe_mk (f : M ≃* N) (hf1 hf2) : ⇑(mk f hf1 hf2) = f := rfl

@[to_additive]
theorem toEquiv_eq_coe (f : M ≃ₜ* N) : f.toEquiv = f :=
  rfl

@[to_additive (attr := simp)]
theorem toMulEquiv_eq_coe (f : M ≃ₜ* N) : f.toMulEquiv = f :=
  rfl

@[to_additive]
theorem toHomeomorph_eq_coe (f : M ≃ₜ* N) : f.toHomeomorph = f :=
  rfl

/-- Makes a continuous multiplicative isomorphism from
a homeomorphism which preserves multiplication. -/
@[to_additive /-- Makes an continuous additive isomorphism from
a homeomorphism which preserves addition. -/]
def mk' (f : M ≃ₜ N) (h : ∀ x y, f (x * y) = f x * f y) : M ≃ₜ* N :=
  ⟨⟨f.toEquiv,h⟩, f.continuous_toFun, f.continuous_invFun⟩

set_option linter.docPrime false in -- This is about `ContinuousMulEquiv.mk'`
@[simp]
lemma coe_mk' (f : M ≃ₜ N) (h : ∀ x y, f (x * y) = f x * f y) : ⇑(mk' f h) = f := rfl

end coe

section bijective

@[to_additive]
protected theorem bijective (e : M ≃ₜ* N) : Function.Bijective e :=
  EquivLike.bijective e

@[to_additive]
protected theorem injective (e : M ≃ₜ* N) : Function.Injective e :=
  EquivLike.injective e

@[to_additive]
protected theorem surjective (e : M ≃ₜ* N) : Function.Surjective e :=
  EquivLike.surjective e

@[to_additive]
theorem apply_eq_iff_eq (e : M ≃ₜ* N) {x y : M} : e x = e y ↔ x = y :=
  e.injective.eq_iff

end bijective

section refl

variable (M)

/-- The identity map is a continuous multiplicative isomorphism. -/
@[to_additive (attr := refl) /-- The identity map is a continuous additive isomorphism. -/]
def refl : M ≃ₜ* M :=
  { MulEquiv.refl _ with
    continuous_toFun := by dsimp; fun_prop
    continuous_invFun := by dsimp; fun_prop }

@[to_additive]
instance : Inhabited (M ≃ₜ* M) := ⟨ContinuousMulEquiv.refl M⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_refl : ↑(refl M) = id := rfl

@[to_additive (attr := simp)]
theorem refl_apply (m : M) : refl M m = m := rfl

end refl

section symm

/-- The inverse of a ContinuousMulEquiv. -/
@[to_additive (attr := symm) /-- The inverse of a ContinuousAddEquiv. -/]
def symm (cme : M ≃ₜ* N) : N ≃ₜ* M :=
  { cme.toMulEquiv.symm with
  continuous_toFun := cme.continuous_invFun
  continuous_invFun := cme.continuous_toFun }
initialize_simps_projections ContinuousMulEquiv (toFun → apply, invFun → symm_apply)
initialize_simps_projections ContinuousAddEquiv (toFun → apply, invFun → symm_apply)

@[to_additive]
theorem invFun_eq_symm {f : M ≃ₜ* N} : f.invFun = f.symm := rfl

@[to_additive (attr := simp)]
theorem coe_toHomeomorph_symm (f : M ≃ₜ* N) : (f : M ≃ₜ N).symm = (f.symm : N ≃ₜ M) := rfl

@[to_additive (attr := simp)]
theorem equivLike_inv_eq_symm (f : M ≃ₜ* N) : EquivLike.inv f = f.symm := rfl

@[to_additive (attr := simp)]
theorem symm_symm (f : M ≃ₜ* N) : f.symm.symm = f := rfl

@[to_additive]
theorem symm_bijective : Function.Bijective (symm : M ≃ₜ* N → _) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/-- `e.symm` is a right inverse of `e`, written as `e (e.symm y) = y`. -/
@[to_additive (attr := simp)
/-- `e.symm` is a right inverse of `e`, written as `e (e.symm y) = y`. -/]
theorem apply_symm_apply (e : M ≃ₜ* N) (y : N) : e (e.symm y) = y :=
  e.toEquiv.apply_symm_apply y

/-- `e.symm` is a left inverse of `e`, written as `e.symm (e y) = y`. -/
@[to_additive (attr := simp)
/-- `e.symm` is a left inverse of `e`, written as `e.symm (e y) = y`. -/]
theorem symm_apply_apply (e : M ≃ₜ* N) (x : M) : e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply x

@[to_additive (attr := simp)]
theorem symm_comp_self (e : M ≃ₜ* N) : e.symm ∘ e = id :=
  funext e.symm_apply_apply

@[to_additive (attr := simp)]
theorem self_comp_symm (e : M ≃ₜ* N) : e ∘ e.symm = id :=
  funext e.apply_symm_apply

@[to_additive]
theorem apply_eq_iff_symm_apply (e : M ≃ₜ* N) {x : M} {y : N} : e x = y ↔ x = e.symm y :=
  e.toEquiv.apply_eq_iff_eq_symm_apply

@[to_additive]
theorem symm_apply_eq (e : M ≃ₜ* N) {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq

@[to_additive]
theorem eq_symm_apply (e : M ≃ₜ* N) {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply

@[to_additive]
theorem eq_comp_symm {α : Type*} (e : M ≃ₜ* N) (f : N → α) (g : M → α) :
    f = g ∘ e.symm ↔ f ∘ e = g :=
  e.toEquiv.eq_comp_symm f g

@[to_additive]
theorem comp_symm_eq {α : Type*} (e : M ≃ₜ* N) (f : N → α) (g : M → α) :
    g ∘ e.symm = f ↔ g = f ∘ e :=
  e.toEquiv.comp_symm_eq f g

@[to_additive]
theorem eq_symm_comp {α : Type*} (e : M ≃ₜ* N) (f : α → M) (g : α → N) :
    f = e.symm ∘ g ↔ e ∘ f = g :=
  e.toEquiv.eq_symm_comp f g

@[to_additive]
theorem symm_comp_eq {α : Type*} (e : M ≃ₜ* N) (f : α → M) (g : α → N) :
    e.symm ∘ g = f ↔ g = e ∘ f :=
  e.toEquiv.symm_comp_eq f g

end symm

section trans

variable {L : Type*} [Mul L] [TopologicalSpace L]

/-- The composition of two ContinuousMulEquiv. -/
@[to_additive /-- The composition of two ContinuousAddEquiv. -/]
def trans (cme1 : M ≃ₜ* N) (cme2 : N ≃ₜ* L) : M ≃ₜ* L where
  __ := cme1.toMulEquiv.trans cme2.toMulEquiv
  continuous_toFun := by convert Continuous.comp cme2.continuous_toFun cme1.continuous_toFun
  continuous_invFun := by convert Continuous.comp cme1.continuous_invFun cme2.continuous_invFun

@[to_additive (attr := simp)]
theorem coe_trans (e₁ : M ≃ₜ* N) (e₂ : N ≃ₜ* L) : ↑(e₁.trans e₂) = e₂ ∘ e₁ := rfl

@[to_additive (attr := simp)]
theorem trans_apply (e₁ : M ≃ₜ* N) (e₂ : N ≃ₜ* L) (m : M) : e₁.trans e₂ m = e₂ (e₁ m) := rfl

@[to_additive (attr := simp)]
theorem symm_trans_apply (e₁ : M ≃ₜ* N) (e₂ : N ≃ₜ* L) (l : L) :
    (e₁.trans e₂).symm l = e₁.symm (e₂.symm l) := rfl

@[to_additive (attr := simp)]
theorem symm_trans_self (e : M ≃ₜ* N) : e.symm.trans e = refl N :=
  DFunLike.ext _ _ e.apply_symm_apply

@[to_additive (attr := simp)]
theorem self_trans_symm (e : M ≃ₜ* N) : e.trans e.symm = refl M :=
  DFunLike.ext _ _ e.symm_apply_apply

end trans

section unique

/-- The `MulEquiv` between two monoids with a unique element. -/
@[to_additive /-- The `AddEquiv` between two `AddMonoid`s with a unique element. -/]
def ofUnique {M N} [Unique M] [Unique N] [Mul M] [Mul N]
    [TopologicalSpace M] [TopologicalSpace N] : M ≃ₜ* N where
  __ := MulEquiv.ofUnique
  continuous_toFun := by continuity
  continuous_invFun := by continuity

/-- There is a unique monoid homomorphism between two monoids with a unique element. -/
@[to_additive /-- There is a unique additive monoid homomorphism between two additive monoids with
  a unique element. -/]
instance {M N} [Unique M] [Unique N] [Mul M] [Mul N]
    [TopologicalSpace M] [TopologicalSpace N] : Unique (M ≃ₜ* N) where
  default := ofUnique
  uniq _ := ext fun _ ↦ Subsingleton.elim _ _

end unique

/-- A family indexed by a type with a unique element
is `ContinuousMulEquiv` to the element at the single index.
This is the topological version of `MulEquiv.piUnique`. -/
@[to_additive (attr := simps!)
/-- A family indexed by a type with a unique element
is `ContinuousAddEquiv` to the element at the single index.
This is the topological equivalent of `AddEquiv.piUnique`. -/]
def piUnique {ι : Type*} (M : ι → Type*) [(j : ι) → Mul (M j)]
    [(j : ι) → TopologicalSpace (M j)] [Unique ι] :
    ((j : ι) → M j) ≃ₜ* M default where
  __ := MulEquiv.piUnique M
  continuous_toFun := continuous_apply default
  continuous_invFun := by simpa [continuous_pi_iff, Unique.forall_iff] using continuous_id'

/-- Splits the indices of `∀ (i : ι), Y i` along the predicate `p`.
This is `Equiv.piEquivPiSubtypeProd` as a `ContinuousMulEquiv`. -/
@[to_additive (attr := simps!) piEquivPiSubtypeProd
/-- Splits the indices of `∀ (i : ι), Y i` along the predicate `p`.
This is `Equiv.piEquivPiSubtypeProd` as a `ContinuousAddEquiv`. -/]
def piEquivPiSubtypeProd {ι : Type*} (p : ι → Prop) (Y : ι → Type*)
    [(i : ι) → TopologicalSpace (Y i)] [(i : ι) → Mul (Y i)] [DecidablePred p] :
    ((i : ι) → Y i) ≃ₜ* ((i : { x : ι // p x }) → Y i) × ((i : { x : ι // ¬p x }) → Y i) :=
  {Homeomorph.piEquivPiSubtypeProd p Y with map_mul' _ _ := rfl}

end ContinuousMulEquiv

end

end
