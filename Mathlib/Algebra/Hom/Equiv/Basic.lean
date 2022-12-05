/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
Ported by: Winston Yin
-/
import Mathlib.Algebra.Hom.Group
import Mathlib.Data.FunLike.Equiv
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Pi.Algebra

/-!
# Multiplicative and additive equivs

In this file we define two extensions of `equiv` called `add_equiv` and `mul_equiv`, which are
datatypes representing isomorphisms of `add_monoid`s/`add_group`s and `monoid`s/`group`s.

## Notations

* ``infix ` ≃* `:25 := mul_equiv``
* ``infix ` ≃+ `:25 := add_equiv``

The extended equivs all have coercions to functions, and the coercions are the canonical
notation when treating the isomorphisms as maps.

## Implementation notes

The fields for `mul_equiv`, `add_equiv` now avoid the unbundled `is_mul_hom` and `is_add_hom`, as
these are deprecated.

## Tags

equiv, mul_equiv, add_equiv
-/


variable {F α β A B M N P Q G H : Type _}

/-- Makes a multiplicative inverse from a bijection which preserves multiplication. -/
@[to_additive "Makes an additive inverse from a bijection which preserves addition."]
def MulHom.inverse [Mul M] [Mul N] (f : M →ₙ* N) (g : N → M) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : N →ₙ* M where
  toFun := g
  map_mul' x y :=
    calc
      g (x * y) = g (f (g x) * f (g y)) := by rw [h₂ x, h₂ y]
      _ = g (f (g x * g y)) := by rw [f.map_mul]
      _ = g x * g y := h₁ _

#align mul_hom.inverse MulHom.inverse

/-- The inverse of a bijective `monoid_hom` is a `monoid_hom`. -/
@[to_additive "The inverse of a bijective `add_monoid_hom` is an `add_monoid_hom`.", simps]
def MonoidHom.inverse {A B : Type _} [Monoid A] [Monoid B] (f : A →* B) (g : B → A) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : B →* A :=
  { (f : A →ₙ* B).inverse g h₁ h₂ with toFun := g, map_one' := by rw [← f.map_one, h₁] }
#align monoid_hom.inverse MonoidHom.inverse

/-- add_equiv α β is the type of an equiv α ≃ β which preserves addition. -/
structure AddEquiv (A B : Type _) [Add A] [Add B] extends A ≃ B, AddHom A B
#align add_equiv AddEquiv

/-- `add_equiv_class F A B` states that `F` is a type of addition-preserving morphisms.
You should extend this class when you extend `add_equiv`. -/
class AddEquivClass (F A B : Type _) [Add A] [Add B] extends EquivLike F A B where
  map_add : ∀ (f : F) (a b), f (a + b) = f a + f b
#align add_equiv_class AddEquivClass

/-- The `equiv` underlying an `add_equiv`. -/
add_decl_doc AddEquiv.toEquiv

/-- The `add_hom` underlying a `add_equiv`. -/
add_decl_doc AddEquiv.toAddHom

/-- `mul_equiv α β` is the type of an equiv `α ≃ β` which preserves multiplication. -/
@[to_additive]
structure MulEquiv (M N : Type _) [Mul M] [Mul N] extends M ≃ N, M →ₙ* N
attribute [to_additive AddEquiv.toAddHom] MulEquiv.toMulHom -- Porting note: needed despite note
#align mul_equiv MulEquiv

/-- The `equiv` underlying a `mul_equiv`. -/
add_decl_doc MulEquiv.toEquiv

/-- The `mul_hom` underlying a `mul_equiv`. -/
add_decl_doc MulEquiv.toMulHom

-- Porting note: `outParam` inserted in `Mul A`, `Mul B`
/-- `mul_equiv_class F A B` states that `F` is a type of multiplication-preserving morphisms.
You should extend this class when you extend `mul_equiv`. -/
@[to_additive]
class MulEquivClass (F A B : Type _) [outParam <| Mul A] [outParam <| Mul B] extends EquivLike F A B where
  map_mul : ∀ (f : F) (a b), f (a * b) = f a * f b
#align mul_equiv_class MulEquivClass

-- mathport name: «expr ≃* »
infixl:25 " ≃* " => MulEquiv

-- mathport name: «expr ≃+ »
infixl:25 " ≃+ " => AddEquiv

namespace MulEquivClass

variable (F)

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) [Mul M] [Mul N] [h : MulEquivClass F M N] : MulHomClass F M N :=
  { h with coe := h.coe, coe_injective' := FunLike.coe_injective' }

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) [MulOneClass M] [MulOneClass N] [MulEquivClass F M N] : MonoidHomClass F M N :=
  { MulEquivClass.instMulHomClass F with
    coe := fun _ => _,
    map_one := fun e =>
      calc
        e 1 = e 1 * 1 := (mul_one _).symm
        _ = e 1 * e (MulEquivClass.toEquivLike.inv e (1 : N) : M) := congr_arg _ (MulEquivClass.toEquivLike.right_inv e 1).symm
        _ = e (MulEquivClass.toEquivLike.inv e (1 : N)) := by rw [← map_mul, one_mul]
        _ = 1 := MulEquivClass.toEquivLike.right_inv e 1
         }

-- See note [lower instance priority]
instance (priority := 100) toMonoidWithZeroHomClass {α β : Type _} [MulZeroOneClass α] [MulZeroOneClass β]
    [MulEquivClass F α β] : MonoidWithZeroHomClass F α β :=
  { MulEquivClass.instMonoidHomClass _ with
    map_zero := fun e =>
      calc
        e 0 = e 0 * e (EquivLike.inv e 0) := by rw [← map_mul, zero_mul]
        _ = 0 := by simp }
#align mul_equiv_class.to_monoid_with_zero_hom_class MulEquivClass.toMonoidWithZeroHomClass

variable {F}

@[simp, to_additive]
theorem map_eq_one_iff {M N} [MulOneClass M] [MulOneClass N] [MulEquivClass F M N] (h : F) {x : M} :
  h x = 1 ↔ x = 1 := _root_.map_eq_one_iff h (EquivLike.injective h)
#align mul_equiv_class.map_eq_one_iff MulEquivClass.map_eq_one_iff

@[to_additive]
theorem map_ne_one_iff {M N} [MulOneClass M] [MulOneClass N] [MulEquivClass F M N] (h : F) {x : M} :
  h x ≠ 1 ↔ x ≠ 1 := _root_.map_ne_one_iff h (EquivLike.injective h)
#align mul_equiv_class.map_ne_one_iff MulEquivClass.map_ne_one_iff

end MulEquivClass

@[to_additive]
instance [Mul α] [Mul β] [MulEquivClass F α β] : CoeTC F (α ≃* β) :=
  ⟨fun f =>
    { toFun := f, invFun := EquivLike.inv f, left_inv := EquivLike.left_inv f, right_inv := EquivLike.right_inv f,
      map_mul' := MulEquivClass.map_mul f }⟩

namespace MulEquiv

@[to_additive]
instance [Mul M] [Mul N] : MulEquivClass (M ≃* N) M N where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    cases f
    cases g
    congr
    apply Equiv.coe_fn_injective h₁
  map_mul := map_mul'

variable [Mul M] [Mul N] [Mul P] [Mul Q]

@[simp, to_additive]
theorem to_equiv_eq_coe (f : M ≃* N) : f.toEquiv = f :=
  rfl
#align mul_equiv.to_equiv_eq_coe MulEquiv.to_equiv_eq_coe

@[simp, to_additive]
theorem to_fun_eq_coe {f : M ≃* N} : f.toFun = f :=
  rfl
#align mul_equiv.to_fun_eq_coe MulEquiv.to_fun_eq_coe

@[simp, to_additive]
theorem coe_to_equiv {f : M ≃* N} : (f : M ≃ N) = f.toFun :=
  rfl
#align mul_equiv.coe_to_equiv MulEquiv.coe_to_equiv

-- Porting note: restore `to_additive`
@[simp]
theorem coe_toMulHom {f : M ≃* N} : f.toMulHom = f.toFun :=
  rfl
#align mul_equiv.coe_to_mul_hom MulEquiv.coe_toMulHom
@[simp]
theorem _root_.AddEquiv.coe_toAddHom [Add M] [Add N] {f : M ≃+ N} : f.toAddHom = f.toFun :=
  rfl
#align add_equiv.coe_to_add_hom AddEquiv.coe_toAddHom

/-- A multiplicative isomorphism preserves multiplication. -/
@[to_additive "An additive isomorphism preserves addition."]
protected theorem map_mul (f : M ≃* N) : ∀ x y, f (x * y) = f x * f y := sorry
  -- _root_.map_mul f
#align mul_equiv.map_mul MulEquiv.map_mul

/-- Makes a multiplicative isomorphism from a bijection which preserves multiplication. -/
@[to_additive "Makes an additive isomorphism from a bijection which preserves addition."]
def mk' (f : M ≃ N) (h : ∀ x y, f (x * y) = f x * f y) : M ≃* N := ⟨f, h⟩
#align mul_equiv.mk' MulEquiv.mk'

@[to_additive]
protected theorem bijective (e : M ≃* N) : Function.Bijective e :=
  EquivLike.bijective e
#align mul_equiv.bijective MulEquiv.bijective

@[to_additive]
protected theorem injective (e : M ≃* N) : Function.Injective e :=
  EquivLike.injective e
#align mul_equiv.injective MulEquiv.injective

@[to_additive]
protected theorem surjective (e : M ≃* N) : Function.Surjective e :=
  EquivLike.surjective e
#align mul_equiv.surjective MulEquiv.surjective

/-- The identity map is a multiplicative isomorphism. -/
@[refl, to_additive "The identity map is an additive isomorphism."]
def refl (M : Type _) [Mul M] : M ≃* M :=
  { Equiv.refl _ with map_mul' := fun _ _ => rfl }
#align mul_equiv.refl MulEquiv.refl

@[to_additive]
instance : Inhabited (M ≃* M) := ⟨refl M⟩

/-- The inverse of an isomorphism is an isomorphism. -/
@[symm, to_additive "The inverse of an isomorphism is an isomorphism."]
def symm {M N : Type _} [Mul M] [Mul N] (h : M ≃* N) : N ≃* M :=
  ⟨h.toEquiv.symm, (h.toMulHom.inverse h.toEquiv.symm h.left_inv h.right_inv).map_mul⟩
#align mul_equiv.symm MulEquiv.symm

@[simp, to_additive]
theorem inv_fun_eq_symm {f : M ≃* N} : f.invFun = f.symm := rfl
#align mul_equiv.inv_fun_eq_symm MulEquiv.inv_fun_eq_symm

-- we don't hyperlink the note in the additive version, since that breaks syntax highlighting
-- in the whole file.
/-- See Note [custom simps projection] -/
@[to_additive "See Note custom simps projection"]
def Simps.symmApply (e : M ≃* N) : N → M :=
  e.symm
#align mul_equiv.simps.symm_apply MulEquiv.Simps.symmApply

initialize_simps_projections AddEquiv (toEquiv_toFun → apply, toEquiv_invFun → symmApply, -toEquiv)

initialize_simps_projections MulEquiv (toEquiv_toFun → apply, toEquiv_invFun → symmApply, -toEquiv)

@[simp, to_additive]
theorem to_equiv_symm (f : M ≃* N) : f.symm.toEquiv = f.toEquiv.symm :=
  rfl
#align mul_equiv.to_equiv_symm MulEquiv.to_equiv_symm

-- through `Equiv`, i.e. delete this and keep `to_equiv_mk`?
@[simp, to_additive]
theorem coe_mk (f : M → N) (g h₁ h₂ h₃) : MulEquiv.mk ⟨f, g, h₁, h₂⟩ h₃ = f :=
  rfl
#align mul_equiv.coe_mk MulEquiv.coe_mk

@[simp, to_additive]
theorem to_equiv_mk (f : M ≃ N) (h) : (MulEquiv.mk f h).toEquiv = f :=
  rfl
#align mul_equiv.to_equiv_mk MulEquiv.to_equiv_mk

@[simp, to_additive]
theorem symm_symm : ∀ f : M ≃* N, f.symm.symm = f
  | ⟨_, _⟩ => rfl
#align mul_equiv.symm_symm MulEquiv.symm_symm

@[to_additive]
theorem symm_bijective : Function.Bijective (symm : M ≃* N → N ≃* M) :=
  Equiv.bijective ⟨symm, symm, symm_symm, symm_symm⟩
#align mul_equiv.symm_bijective MulEquiv.symm_bijective

-- Porting note: this now only refers to `Equiv`, not to the underlying functions of the `Equiv`.
@[simp, to_additive]
theorem symm_mk (f : M ≃ N) (h) :
    (MulEquiv.mk f h).symm = ⟨f.symm, (MulEquiv.mk f h).symm.map_mul'⟩ :=
  rfl
#align mul_equiv.symm_mk MulEquiv.symm_mk

@[simp, to_additive]
theorem refl_symm : (refl M).symm = refl M :=
  rfl
#align mul_equiv.refl_symm MulEquiv.refl_symm

/-- Transitivity of multiplication-preserving isomorphisms -/
@[trans, to_additive "Transitivity of addition-preserving isomorphisms"]
def trans (h1 : M ≃* N) (h2 : N ≃* P) : M ≃* P :=
  { h1.toEquiv.trans h2.toEquiv with
    map_mul' := fun x y => show h2 (h1 (x * y)) = h2 (h1 x) * h2 (h1 y) by rw [h1.map_mul, h2.map_mul] }
#align mul_equiv.trans MulEquiv.trans

/-- `e.symm` is a right inverse of `e`, written as `e (e.symm y) = y`. -/
@[simp, to_additive "`e.symm` is a right inverse of `e`, written as `e (e.symm y) = y`."]
theorem apply_symm_apply (e : M ≃* N) (y : N) : e (e.symm y) = y :=
  e.toEquiv.apply_symm_apply y
#align mul_equiv.apply_symm_apply MulEquiv.apply_symm_apply

/-- `e.symm` is a left inverse of `e`, written as `e.symm (e y) = y`. -/
@[simp, to_additive "`e.symm` is a left inverse of `e`, written as `e.symm (e y) = y`."]
theorem symm_apply_apply (e : M ≃* N) (x : M) : e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply x
#align mul_equiv.symm_apply_apply MulEquiv.symm_apply_apply

@[simp, to_additive]
theorem symm_comp_self (e : M ≃* N) : e.symm ∘ e = id :=
  funext e.symm_apply_apply
#align mul_equiv.symm_comp_self MulEquiv.symm_comp_self

@[simp, to_additive]
theorem self_comp_symm (e : M ≃* N) : e ∘ e.symm = id :=
  funext e.apply_symm_apply
#align mul_equiv.self_comp_symm MulEquiv.self_comp_symm

@[simp, to_additive]
theorem coe_refl : ↑(refl M) = id :=
  rfl
#align mul_equiv.coe_refl MulEquiv.coe_refl

@[simp, to_additive]
theorem refl_apply (m : M) : refl M m = m :=
  rfl
#align mul_equiv.refl_apply MulEquiv.refl_apply

@[simp, to_additive]
theorem coe_trans (e₁ : M ≃* N) (e₂ : N ≃* P) : ↑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl
#align mul_equiv.coe_trans MulEquiv.coe_trans

@[simp, to_additive]
theorem trans_apply (e₁ : M ≃* N) (e₂ : N ≃* P) (m : M) : e₁.trans e₂ m = e₂ (e₁ m) :=
  rfl
#align mul_equiv.trans_apply MulEquiv.trans_apply

@[simp, to_additive]
theorem symm_trans_apply (e₁ : M ≃* N) (e₂ : N ≃* P) (p : P) : (e₁.trans e₂).symm p = e₁.symm (e₂.symm p) :=
  rfl
#align mul_equiv.symm_trans_apply MulEquiv.symm_trans_apply

@[simp, to_additive]
theorem apply_eq_iff_eq (e : M ≃* N) {x y : M} : e x = e y ↔ x = y :=
  e.injective.eq_iff
#align mul_equiv.apply_eq_iff_eq MulEquiv.apply_eq_iff_eq

@[to_additive]
theorem apply_eq_iff_symm_apply (e : M ≃* N) {x : M} {y : N} : e x = y ↔ x = e.symm y :=
  e.toEquiv.apply_eq_iff_eq_symm_apply
#align mul_equiv.apply_eq_iff_symm_apply MulEquiv.apply_eq_iff_symm_apply

@[to_additive]
theorem symm_apply_eq (e : M ≃* N) {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq
#align mul_equiv.symm_apply_eq MulEquiv.symm_apply_eq

@[to_additive]
theorem eq_symm_apply (e : M ≃* N) {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply
#align mul_equiv.eq_symm_apply MulEquiv.eq_symm_apply

@[to_additive]
theorem eq_comp_symm {α : Type _} (e : M ≃* N) (f : N → α) (g : M → α) : f = g ∘ e.symm ↔ f ∘ e = g :=
  e.toEquiv.eq_comp_symm f g
#align mul_equiv.eq_comp_symm MulEquiv.eq_comp_symm

@[to_additive]
theorem comp_symm_eq {α : Type _} (e : M ≃* N) (f : N → α) (g : M → α) : g ∘ e.symm = f ↔ g = f ∘ e :=
  e.toEquiv.comp_symm_eq f g
#align mul_equiv.comp_symm_eq MulEquiv.comp_symm_eq

@[to_additive]
theorem eq_symm_comp {α : Type _} (e : M ≃* N) (f : α → M) (g : α → N) : f = e.symm ∘ g ↔ e ∘ f = g :=
  e.toEquiv.eq_symm_comp f g
#align mul_equiv.eq_symm_comp MulEquiv.eq_symm_comp

@[to_additive]
theorem symm_comp_eq {α : Type _} (e : M ≃* N) (f : α → M) (g : α → N) : e.symm ∘ g = f ↔ g = e ∘ f :=
  e.toEquiv.symm_comp_eq f g
#align mul_equiv.symm_comp_eq MulEquiv.symm_comp_eq

@[simp, to_additive]
theorem symm_trans_self (e : M ≃* N) : e.symm.trans e = refl N :=
  FunLike.ext _ _ e.apply_symm_apply
#align mul_equiv.symm_trans_self MulEquiv.symm_trans_self

@[simp, to_additive]
theorem self_trans_symm (e : M ≃* N) : e.trans e.symm = refl M :=
  FunLike.ext _ _ e.symm_apply_apply
#align mul_equiv.self_trans_symm MulEquiv.self_trans_symm

@[to_additive, simp]
theorem coe_monoid_hom_refl {M} [MulOneClass M] : (refl M : M →* M) = MonoidHom.id M :=
  rfl
#align mul_equiv.coe_monoid_hom_refl MulEquiv.coe_monoid_hom_refl

@[to_additive, simp]
theorem coe_monoid_hom_trans {M N P} [MulOneClass M] [MulOneClass N] [MulOneClass P] (e₁ : M ≃* N) (e₂ : N ≃* P) :
    (e₁.trans e₂ : M →* P) = (e₂ : N →* P).comp ↑e₁ :=
  rfl
#align mul_equiv.coe_monoid_hom_trans MulEquiv.coe_monoid_hom_trans

/-- Two multiplicative isomorphisms agree if they are defined by the
    same underlying function. -/
@[ext, to_additive "Two additive isomorphisms agree if they are defined by the same underlying function."]
theorem ext {f g : MulEquiv M N} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h
#align mul_equiv.ext MulEquiv.ext

@[to_additive]
theorem ext_iff {f g : MulEquiv M N} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff
#align mul_equiv.ext_iff MulEquiv.ext_iff

@[simp, to_additive]
theorem mk_coe (e : M ≃* N) (e' h₁ h₂ h₃) : (⟨⟨e, e', h₁, h₂⟩, h₃⟩ : M ≃* N) = e :=
  ext fun _ => rfl
#align mul_equiv.mk_coe MulEquiv.mk_coe

@[simp, to_additive]
theorem mk_coe' (e : M ≃* N) (f h₁ h₂ h₃) : (MulEquiv.mk ⟨f, e, h₁, h₂⟩ h₃ : N ≃* M) = e.symm :=
  symm_bijective.injective <| ext fun _ => rfl
#align mul_equiv.mk_coe' MulEquiv.mk_coe'

@[to_additive]
protected theorem congr_arg {f : MulEquiv M N} {x x' : M} : x = x' → f x = f x' :=
  FunLike.congr_arg f
#align mul_equiv.congr_arg MulEquiv.congr_arg

@[to_additive]
protected theorem congr_fun {f g : MulEquiv M N} (h : f = g) (x : M) : f x = g x :=
  FunLike.congr_fun h x
#align mul_equiv.congr_fun MulEquiv.congr_fun

/-- The `mul_equiv` between two monoids with a unique element. -/
@[to_additive "The `add_equiv` between two add_monoids with a unique element."]
def mulEquivOfUnique {M N} [Unique M] [Unique N] [Mul M] [Mul N] : M ≃* N :=
  { Equiv.equivOfUnique M N with map_mul' := fun _ _ => Subsingleton.elim _ _ }
#align mul_equiv.mul_equiv_of_unique MulEquiv.mulEquivOfUnique

/-- There is a unique monoid homomorphism between two monoids with a unique element. -/
@[to_additive "There is a unique additive monoid homomorphism between two additive monoids with\na unique element."]
instance {M N} [Unique M] [Unique N] [Mul M] [Mul N] : Unique (M ≃* N) where
  default := mulEquivOfUnique
  uniq _ := ext fun _ => Subsingleton.elim _ _

/-!
## Monoids
-/
-- Porting note: type class problem timeout
/-- A multiplicative isomorphism of monoids sends `1` to `1` (and is hence a monoid isomorphism). -/
@[to_additive
      "An additive isomorphism of additive monoids sends `0` to `0`\n(and is hence an additive monoid isomorphism)."]
protected theorem map_one {M N} [MulOneClass M] [MulOneClass N] (h : M ≃* N) : h 1 = 1 := sorry
  -- _root_.map_one h
#align mul_equiv.map_one MulEquiv.map_one

@[to_additive]
protected theorem map_eq_one_iff {M N} [MulOneClass M] [MulOneClass N] (h : M ≃* N) {x : M} : h x = 1 ↔ x = 1 := sorry
  -- MulEquivClass.map_eq_one_iff h
#align mul_equiv.map_eq_one_iff MulEquiv.map_eq_one_iff

@[to_additive]
theorem map_ne_one_iff {M N} [MulOneClass M] [MulOneClass N] (h : M ≃* N) {x : M} : h x ≠ 1 ↔ x ≠ 1 := sorry
  -- MulEquivClass.map_ne_one_iff h
#align mul_equiv.map_ne_one_iff MulEquiv.map_ne_one_iff

-- /-- A bijective `semigroup` homomorphism is an isomorphism -/
-- @[to_additive "A bijective `add_semigroup` homomorphism is an isomorphism", simps apply]
-- noncomputable def ofBijective {M N F} [Mul M] [Mul N] [MulHomClass F M N] (f : F) (hf : Function.Bijective f) :
--     M ≃* N :=
--   { Equiv.ofBijective f hf with map_mul' := map_mul f }
-- #align mul_equiv.of_bijective MulEquiv.ofBijective

-- @[simp]
-- theorem ofBijective_apply_symm_apply {M N} [MulOneClass M] [MulOneClass N] {n : N} (f : M →* N)
--     (hf : Function.Bijective f) : f ((Equiv.ofBijective f hf).symm n) = n :=
--   (MulEquiv.ofBijective f hf).apply_symm_apply n
-- #align mul_equiv.of_bijective_apply_symm_apply MulEquiv.of_bijective_apply_symm_apply

/-- Extract the forward direction of a multiplicative equivalence
as a multiplication-preserving function.
-/
@[to_additive "Extract the forward direction of an additive equivalence\nas an addition-preserving function."]
def toMonoidHom {M N} [MulOneClass M] [MulOneClass N] (h : M ≃* N) : M →* N :=
  { h with map_one' := h.map_one }
#align mul_equiv.to_monoid_hom MulEquiv.toMonoidHom

@[simp, to_additive]
theorem coe_to_monoid_hom {M N} [MulOneClass M] [MulOneClass N] (e : M ≃* N) : ↑e.toMonoidHom = ↑e :=
  rfl
#align mul_equiv.coe_to_monoid_hom MulEquiv.coe_to_monoid_hom

@[to_additive]
theorem to_monoid_hom_injective {M N} [MulOneClass M] [MulOneClass N] :
    Function.Injective (toMonoidHom : M ≃* N → M →* N) := fun _ _ h => MulEquiv.ext (MonoidHom.ext_iff.1 h) -- FunLike.ext_iff timeout here
#align mul_equiv.to_monoid_hom_injective MulEquiv.to_monoid_hom_injective

/-- A multiplicative analogue of `equiv.arrow_congr`,
where the equivalence between the targets is multiplicative.
-/
@[to_additive "An additive analogue of `equiv.arrow_congr`,\nwhere the equivalence between the targets is additive.",
  simps apply]
def arrowCongr {M N P Q : Type _} [Mul P] [Mul Q] (f : M ≃ N) (g : P ≃* Q) : (M → P) ≃* (N → Q) where
  toFun h n := g (h (f.symm n))
  invFun k m := g.symm (k (f m))
  left_inv h := by
    ext
    simp
  right_inv k := by
    ext
    simp
  map_mul' h k := by
    ext
    exact MulEquiv.map_mul _ _ _ -- Porting note: simp doesn't work here
#align mul_equiv.arrow_congr MulEquiv.arrowCongr

/-- A multiplicative analogue of `equiv.arrow_congr`,
for multiplicative maps from a monoid to a commutative monoid.
-/
@[to_additive
      "An additive analogue of `equiv.arrow_congr`,\nfor additive maps from an additive monoid to a commutative additive monoid.",
  simps apply]
def monoidHomCongr {M N P Q} [MulOneClass M] [MulOneClass N] [CommMonoid P] [CommMonoid Q] (f : M ≃* N) (g : P ≃* Q) :
    (M →* P) ≃* (N →* Q) where
  toFun h := g.toMonoidHom.comp (h.comp f.symm.toMonoidHom)
  invFun k := g.symm.toMonoidHom.comp (k.comp f.toMonoidHom)
  left_inv h := by
    ext x
    simp
  right_inv k := by
    ext
    simp
  map_mul' h k := by
    ext
    exact MulEquiv.map_mul _ _ _ -- Porting note: simp doesn't work here
#align mul_equiv.monoid_hom_congr MulEquiv.monoidHomCongr

/-- A family of multiplicative equivalences `Π j, (Ms j ≃* Ns j)` generates a
multiplicative equivalence between `Π j, Ms j` and `Π j, Ns j`.

This is the `mul_equiv` version of `equiv.Pi_congr_right`, and the dependent version of
`mul_equiv.arrow_congr`.
-/
@[to_additive AddEquiv.piCongrRight
      "A family of additive equivalences `Π j, (Ms j ≃+ Ns j)`\ngenerates an additive equivalence between `Π j, Ms j` and `Π j, Ns j`.\n\nThis is the `add_equiv` version of `equiv.Pi_congr_right`, and the dependent version of\n`add_equiv.arrow_congr`.",
  simps apply]
def piCongrRight {η : Type _} {Ms Ns : η → Type _} [∀ j, Mul (Ms j)] [∀ j, Mul (Ns j)] (es : ∀ j, Ms j ≃* Ns j) :
    (∀ j, Ms j) ≃* ∀ j, Ns j :=
  { Equiv.piCongrRight fun j => (es j).toEquiv with
    toFun := fun x j => es j (x j),
    invFun := fun x j => (es j).symm (x j),
    map_mul' := fun x y => funext fun j => (es j).map_mul (x j) (y j) }
#align mul_equiv.Pi_congr_right MulEquiv.piCongrRight

@[simp]
theorem piCongrRight_refl {η : Type _} {Ms : η → Type _} [∀ j, Mul (Ms j)] :
    (piCongrRight fun j => MulEquiv.refl (Ms j)) = MulEquiv.refl _ :=
  rfl
#align mul_equiv.Pi_congr_right_refl MulEquiv.piCongrRight_refl

@[simp]
theorem Pi_congr_right_symm {η : Type _} {Ms Ns : η → Type _} [∀ j, Mul (Ms j)] [∀ j, Mul (Ns j)]
    (es : ∀ j, Ms j ≃* Ns j) : (piCongrRight es).symm = piCongrRight fun i => (es i).symm :=
  rfl
#align mul_equiv.Pi_congr_right_symm MulEquiv.Pi_congr_right_symm

@[simp]
theorem Pi_congr_right_trans {η : Type _} {Ms Ns Ps : η → Type _} [∀ j, Mul (Ms j)] [∀ j, Mul (Ns j)] [∀ j, Mul (Ps j)]
    (es : ∀ j, Ms j ≃* Ns j) (fs : ∀ j, Ns j ≃* Ps j) :
    (piCongrRight es).trans (piCongrRight fs) = piCongrRight fun i => (es i).trans (fs i) :=
  rfl
#align mul_equiv.Pi_congr_right_trans MulEquiv.Pi_congr_right_trans

/-- A family indexed by a nonempty subsingleton type is equivalent to the element at the single
index. -/
@[to_additive AddEquiv.piSubsingleton
      "A family indexed by a nonempty subsingleton type is\nequivalent to the element at the single index.",
  simps]
def piSubsingleton {ι : Type _} (M : ι → Type _) [∀ j, Mul (M j)] [Subsingleton ι] (i : ι) : (∀ j, M j) ≃* M i :=
  { Equiv.piSubsingleton M i with map_mul' := fun _ _ => Pi.mul_apply _ _ _ }
#align mul_equiv.Pi_subsingleton MulEquiv.piSubsingleton

/-!
# Groups
-/

-- Porting note: typeclass timeout
/-- A multiplicative equivalence of groups preserves inversion. -/
@[to_additive "An additive equivalence of additive groups preserves negation."]
protected theorem map_inv [Group G] [DivisionMonoid H] (h : G ≃* H) (x : G) : h x⁻¹ = (h x)⁻¹ := sorry
  -- _root_.map_inv h x
#align mul_equiv.map_inv MulEquiv.map_inv

/-- A multiplicative equivalence of groups preserves division. -/
@[to_additive "An additive equivalence of additive groups preserves subtractions."]
protected theorem map_div [Group G] [DivisionMonoid H] (h : G ≃* H) (x y : G) : h (x / y) = h x / h y := sorry
  -- _root_.map_div h x y
#align mul_equiv.map_div MulEquiv.map_div

end MulEquiv

/-- Given a pair of multiplicative homomorphisms `f`, `g` such that `g.comp f = id` and
`f.comp g = id`, returns an multiplicative equivalence with `to_fun = f` and `inv_fun = g`. This
constructor is useful if the underlying type(s) have specialized `ext` lemmas for multiplicative
homomorphisms. -/
@[to_additive
      "Given a pair of additive homomorphisms `f`, `g` such that `g.comp f = id` and\n`f.comp g = id`, returns an additive equivalence with `to_fun = f` and `inv_fun = g`.  This\nconstructor is useful if the underlying type(s) have specialized `ext` lemmas for additive\nhomomorphisms.",
  simps (config := { fullyApplied := false })]
def MulHom.toMulEquiv [Mul M] [Mul N] (f : M →ₙ* N) (g : N →ₙ* M) (h₁ : g.comp f = MulHom.id _)
    (h₂ : f.comp g = MulHom.id _) : M ≃* N where
  toFun := f
  invFun := g
  left_inv := MulHom.congr_fun h₁
  right_inv := MulHom.congr_fun h₂
  map_mul' := f.map_mul
#align mul_hom.to_mul_equiv MulHom.toMulEquiv

/-- Given a pair of monoid homomorphisms `f`, `g` such that `g.comp f = id` and `f.comp g = id`,
returns an multiplicative equivalence with `to_fun = f` and `inv_fun = g`.  This constructor is
useful if the underlying type(s) have specialized `ext` lemmas for monoid homomorphisms. -/
@[to_additive
      "Given a pair of additive monoid homomorphisms `f`, `g` such that `g.comp f = id`\nand `f.comp g = id`, returns an additive equivalence with `to_fun = f` and `inv_fun = g`.  This\nconstructor is useful if the underlying type(s) have specialized `ext` lemmas for additive\nmonoid homomorphisms.",
  simps (config := { fullyApplied := false })]
def MonoidHom.toMulEquiv [MulOneClass M] [MulOneClass N] (f : M →* N) (g : N →* M) (h₁ : g.comp f = MonoidHom.id _)
    (h₂ : f.comp g = MonoidHom.id _) : M ≃* N where
  toFun := f
  invFun := g
  left_inv := MonoidHom.congr_fun h₁
  right_inv := MonoidHom.congr_fun h₂
  map_mul' := f.map_mul
#align monoid_hom.to_mul_equiv MonoidHom.toMulEquiv

namespace Equiv

section HasInvolutiveNeg

variable (G) [HasInvolutiveInv G]

/-- Inversion on a `Group` or `GroupWithZero` is a permutation of the underlying type. -/
@[to_additive "Negation on an `add_group` is a permutation of the underlying type.",
  simps (config := { fullyApplied := false }) apply]
protected def inv : Perm G :=
  inv_involutive.toPerm _
#align equiv.inv Equiv.inv

variable {G}

@[simp, to_additive]
theorem inv_symm : (Equiv.inv G).symm = Equiv.inv G :=
  rfl
#align equiv.inv_symm Equiv.inv_symm

end HasInvolutiveNeg

end Equiv
