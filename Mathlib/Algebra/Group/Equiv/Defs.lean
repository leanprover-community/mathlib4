/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Logic.Equiv.Defs

/-!
# Multiplicative and additive equivs

In this file we define two extensions of `Equiv` called `AddEquiv` and `MulEquiv`, which are
datatypes representing isomorphisms of `AddMonoid`s/`AddGroup`s and `Monoid`s/`Group`s.

## Main definitions
* `≃*` (`MulEquiv`), `≃+` (`AddEquiv`): bundled equivalences that preserve multiplication/addition
  (and are therefore monoid and group isomorphisms).
* `MulEquivClass`, `AddEquivClass`: classes for types containing bundled equivalences that
  preserve multiplication/addition.

## Notations

* ``infix ` ≃* `:25 := MulEquiv``
* ``infix ` ≃+ `:25 := AddEquiv``

The extended equivs all have coercions to functions, and the coercions are the canonical
notation when treating the isomorphisms as maps.

## Tags

Equiv, MulEquiv, AddEquiv
-/

open Function

variable {F α β M N P G H : Type*}

namespace EmbeddingLike
variable [One M] [One N] [FunLike F M N] [EmbeddingLike F M N] [OneHomClass F M N]

@[to_additive (attr := simp)]
theorem map_eq_one_iff {f : F} {x : M} :
    f x = 1 ↔ x = 1 :=
  _root_.map_eq_one_iff f (EmbeddingLike.injective f)

@[to_additive]
theorem map_ne_one_iff {f : F} {x : M} :
    f x ≠ 1 ↔ x ≠ 1 :=
  map_eq_one_iff.not

end EmbeddingLike

/-- `AddEquiv α β` is the type of an equiv `α ≃ β` which preserves addition. -/
structure AddEquiv (A B : Type*) [Add A] [Add B] extends A ≃ B, AddHom A B

/-- `AddEquivClass F A B` states that `F` is a type of addition-preserving morphisms.
You should extend this class when you extend `AddEquiv`. -/
class AddEquivClass (F : Type*) (A B : outParam Type*) [Add A] [Add B] [EquivLike F A B] :
    Prop where
  /-- Preserves addition. -/
  map_add : ∀ (f : F) (a b), f (a + b) = f a + f b

/-- The `Equiv` underlying an `AddEquiv`. -/
add_decl_doc AddEquiv.toEquiv

/-- The `AddHom` underlying an `AddEquiv`. -/
add_decl_doc AddEquiv.toAddHom

/-- `MulEquiv α β` is the type of an equiv `α ≃ β` which preserves multiplication. -/
@[to_additive]
structure MulEquiv (M N : Type*) [Mul M] [Mul N] extends M ≃ N, M →ₙ* N

/-- The `Equiv` underlying a `MulEquiv`. -/
add_decl_doc MulEquiv.toEquiv

/-- The `MulHom` underlying a `MulEquiv`. -/
add_decl_doc MulEquiv.toMulHom

/-- Notation for a `MulEquiv`. -/
infixl:25 " ≃* " => MulEquiv

/-- Notation for an `AddEquiv`. -/
infixl:25 " ≃+ " => AddEquiv

@[to_additive]
lemma MulEquiv.toEquiv_injective {α β : Type*} [Mul α] [Mul β] :
    Function.Injective (toEquiv : (α ≃* β) → (α ≃ β))
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/-- `MulEquivClass F A B` states that `F` is a type of multiplication-preserving morphisms.
You should extend this class when you extend `MulEquiv`. -/
-- TODO: make this a synonym for MulHomClass?
@[to_additive]
class MulEquivClass (F : Type*) (A B : outParam Type*) [Mul A] [Mul B] [EquivLike F A B] :
    Prop where
  /-- Preserves multiplication. -/
  map_mul : ∀ (f : F) (a b), f (a * b) = f a * f b

@[to_additive]
alias MulEquivClass.map_eq_one_iff := EmbeddingLike.map_eq_one_iff

@[to_additive]
alias MulEquivClass.map_ne_one_iff := EmbeddingLike.map_ne_one_iff

namespace MulEquivClass

variable (F)
variable [EquivLike F M N]

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) instMulHomClass (F : Type*)
    [Mul M] [Mul N] [EquivLike F M N] [h : MulEquivClass F M N] : MulHomClass F M N :=
  { h with }

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) instMonoidHomClass
    [MulOneClass M] [MulOneClass N] [MulEquivClass F M N] :
    MonoidHomClass F M N :=
  { MulEquivClass.instMulHomClass F with
    map_one := fun e =>
      calc
        e 1 = e 1 * 1 := (mul_one _).symm
        _ = e 1 * e (EquivLike.inv e (1 : N) : M) :=
          congr_arg _ (EquivLike.right_inv e 1).symm
        _ = e (EquivLike.inv e (1 : N)) := by rw [← map_mul, one_mul]
        _ = 1 := EquivLike.right_inv e 1 }

end MulEquivClass

variable [EquivLike F α β]

/-- Turn an element of a type `F` satisfying `MulEquivClass F α β` into an actual
`MulEquiv`. This is declared as the default coercion from `F` to `α ≃* β`. -/
@[to_additive (attr := coe)
/-- Turn an element of a type `F` satisfying `AddEquivClass F α β` into an actual
`AddEquiv`. This is declared as the default coercion from `F` to `α ≃+ β`. -/]
def MulEquivClass.toMulEquiv [Mul α] [Mul β] [MulEquivClass F α β] (f : F) : α ≃* β :=
  { (f : α ≃ β), (f : α →ₙ* β) with }

/-- Any type satisfying `MulEquivClass` can be cast into `MulEquiv` via
`MulEquivClass.toMulEquiv`. -/
@[to_additive /-- Any type satisfying `AddEquivClass` can be cast into `AddEquiv` via
`AddEquivClass.toAddEquiv`. -/]
instance [Mul α] [Mul β] [MulEquivClass F α β] : CoeTC F (α ≃* β) :=
  ⟨MulEquivClass.toMulEquiv⟩

namespace MulEquiv
section Mul
variable [Mul M] [Mul N] [Mul P]

section coe

@[to_additive]
instance : EquivLike (M ≃* N) M N where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    cases f
    cases g
    congr
    apply Equiv.coe_fn_injective h₁

@[to_additive] -- shortcut instance that doesn't generate any subgoals
instance : CoeFun (M ≃* N) fun _ ↦ M → N where
  coe f := f

@[to_additive]
instance : MulEquivClass (M ≃* N) M N where
  map_mul f := f.map_mul'

/-- Two multiplicative isomorphisms agree if they are defined by the
same underlying function. -/
@[to_additive (attr := ext)
  /-- Two additive isomorphisms agree if they are defined by the same underlying function. -/]
theorem ext {f g : MulEquiv M N} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[to_additive]
protected theorem congr_arg {f : MulEquiv M N} {x x' : M} : x = x' → f x = f x' :=
  DFunLike.congr_arg f

@[to_additive]
protected theorem congr_fun {f g : MulEquiv M N} (h : f = g) (x : M) : f x = g x :=
  DFunLike.congr_fun h x

@[to_additive (attr := simp)]
theorem coe_mk (f : M ≃ N) (hf : ∀ x y, f (x * y) = f x * f y) : (mk f hf : M → N) = f := rfl

@[to_additive (attr := simp)]
theorem mk_coe (e : M ≃* N) (e' h₁ h₂ h₃) : (⟨⟨e, e', h₁, h₂⟩, h₃⟩ : M ≃* N) = e :=
  ext fun _ => rfl

@[to_additive (attr := simp)]
theorem toEquiv_eq_coe (f : M ≃* N) : f.toEquiv = f :=
  rfl

/-- The `simp`-normal form to turn something into a `MulHom` is via `MulHomClass.toMulHom`. -/
@[to_additive (attr := simp)]
theorem toMulHom_eq_coe (f : M ≃* N) : f.toMulHom = ↑f :=
  rfl

@[to_additive]
theorem toFun_eq_coe (f : M ≃* N) : f.toFun = f := rfl

/-- `simp`-normal form of `toFun_eq_coe`. -/
@[to_additive (attr := simp)]
theorem coe_toEquiv (f : M ≃* N) : ⇑(f : M ≃ N) = f := rfl

@[to_additive (attr := simp)]
theorem coe_toMulHom {f : M ≃* N} : (f.toMulHom : M → N) = f := rfl

/-- Makes a multiplicative isomorphism from a bijection which preserves multiplication. -/
@[to_additive /-- Makes an additive isomorphism from a bijection which preserves addition. -/]
def mk' (f : M ≃ N) (h : ∀ x y, f (x * y) = f x * f y) : M ≃* N := ⟨f, h⟩

end coe

section map

/-- A multiplicative isomorphism preserves multiplication. -/
@[to_additive /-- An additive isomorphism preserves addition. -/]
protected theorem map_mul (f : M ≃* N) : ∀ x y, f (x * y) = f x * f y :=
  map_mul f

end map

section bijective

@[to_additive]
protected theorem bijective (e : M ≃* N) : Function.Bijective e :=
  EquivLike.bijective e

@[to_additive]
protected theorem injective (e : M ≃* N) : Function.Injective e :=
  EquivLike.injective e

@[to_additive]
protected theorem surjective (e : M ≃* N) : Function.Surjective e :=
  EquivLike.surjective e

@[to_additive]
theorem apply_eq_iff_eq (e : M ≃* N) {x y : M} : e x = e y ↔ x = y :=
  e.injective.eq_iff

end bijective

section refl

/-- The identity map is a multiplicative isomorphism. -/
@[to_additive (attr := refl) /-- The identity map is an additive isomorphism. -/]
def refl (M : Type*) [Mul M] : M ≃* M :=
  { Equiv.refl _ with map_mul' := fun _ _ => rfl }

@[to_additive]
instance : Inhabited (M ≃* M) := ⟨refl M⟩

@[to_additive (attr := simp)]
theorem coe_refl : ↑(refl M) = id := rfl

@[to_additive (attr := simp)]
theorem refl_apply (m : M) : refl M m = m := rfl

end refl

section symm

/-- An alias for `h.symm.map_mul`. Introduced to fix the issue in
https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/!4.234183.20.60simps.60.20maximum.20recursion.20depth
-/
@[to_additive]
lemma symm_map_mul {M N : Type*} [Mul M] [Mul N] (h : M ≃* N) (x y : N) :
    h.symm (x * y) = h.symm x * h.symm y :=
  map_mul (h.toMulHom.inverse h.toEquiv.symm h.left_inv h.right_inv) x y

/-- The inverse of an isomorphism is an isomorphism. -/
@[to_additive (attr := symm) /-- The inverse of an isomorphism is an isomorphism. -/]
def symm {M N : Type*} [Mul M] [Mul N] (h : M ≃* N) : N ≃* M :=
  ⟨h.toEquiv.symm, h.symm_map_mul⟩

@[to_additive]
theorem invFun_eq_symm {f : M ≃* N} : f.invFun = f.symm := rfl

/-- `simp`-normal form of `invFun_eq_symm`. -/
@[to_additive (attr := simp)]
theorem coe_toEquiv_symm (f : M ≃* N) : ((f : M ≃ N).symm : N → M) = f.symm := rfl

@[to_additive (attr := simp)]
theorem equivLike_inv_eq_symm (f : M ≃* N) : EquivLike.inv f = f.symm := rfl

@[to_additive (attr := simp)]
theorem toEquiv_symm (f : M ≃* N) : (f.symm : N ≃ M) = (f : M ≃ N).symm := rfl

@[to_additive (attr := simp)]
theorem symm_symm (f : M ≃* N) : f.symm.symm = f := rfl

@[to_additive]
theorem symm_bijective : Function.Bijective (symm : (M ≃* N) → N ≃* M) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[to_additive (attr := simp)]
theorem mk_coe' (e : M ≃* N) (f h₁ h₂ h₃) : (MulEquiv.mk ⟨f, e, h₁, h₂⟩ h₃ : N ≃* M) = e.symm :=
  symm_bijective.injective <| ext fun _ => rfl

@[to_additive (attr := simp)]
theorem symm_mk (f : M ≃ N) (h) :
    (MulEquiv.mk f h).symm = ⟨f.symm, (MulEquiv.mk f h).symm_map_mul⟩ := rfl

@[to_additive (attr := simp)]
theorem refl_symm : (refl M).symm = refl M := rfl

/-- `e.symm` is a right inverse of `e`, written as `e (e.symm y) = y`. -/
@[to_additive (attr := simp)
/-- `e.symm` is a right inverse of `e`, written as `e (e.symm y) = y`. -/]
theorem apply_symm_apply (e : M ≃* N) (y : N) : e (e.symm y) = y :=
  e.toEquiv.apply_symm_apply y

/-- `e.symm` is a left inverse of `e`, written as `e.symm (e y) = y`. -/
@[to_additive (attr := simp)
/-- `e.symm` is a left inverse of `e`, written as `e.symm (e y) = y`. -/]
theorem symm_apply_apply (e : M ≃* N) (x : M) : e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply x

@[to_additive (attr := simp)]
theorem symm_comp_self (e : M ≃* N) : e.symm ∘ e = id :=
  funext e.symm_apply_apply

@[to_additive (attr := simp)]
theorem self_comp_symm (e : M ≃* N) : e ∘ e.symm = id :=
  funext e.apply_symm_apply

@[to_additive]
theorem apply_eq_iff_symm_apply (e : M ≃* N) {x : M} {y : N} : e x = y ↔ x = e.symm y :=
  e.toEquiv.apply_eq_iff_eq_symm_apply

@[to_additive]
theorem symm_apply_eq (e : M ≃* N) {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq

@[to_additive]
theorem eq_symm_apply (e : M ≃* N) {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply

@[to_additive]
theorem eq_comp_symm {α : Type*} (e : M ≃* N) (f : N → α) (g : M → α) :
    f = g ∘ e.symm ↔ f ∘ e = g :=
  e.toEquiv.eq_comp_symm f g

@[to_additive]
theorem comp_symm_eq {α : Type*} (e : M ≃* N) (f : N → α) (g : M → α) :
    g ∘ e.symm = f ↔ g = f ∘ e :=
  e.toEquiv.comp_symm_eq f g

@[to_additive]
theorem eq_symm_comp {α : Type*} (e : M ≃* N) (f : α → M) (g : α → N) :
    f = e.symm ∘ g ↔ e ∘ f = g :=
  e.toEquiv.eq_symm_comp f g

@[to_additive]
theorem symm_comp_eq {α : Type*} (e : M ≃* N) (f : α → M) (g : α → N) :
    e.symm ∘ g = f ↔ g = e ∘ f :=
  e.toEquiv.symm_comp_eq f g

@[to_additive (attr := simp)]
theorem _root_.MulEquivClass.apply_coe_symm_apply {α β} [Mul α] [Mul β] {F} [EquivLike F α β]
    [MulEquivClass F α β] (e : F) (x : β) :
    e ((e : α ≃* β).symm x) = x :=
  (e : α ≃* β).right_inv x

@[to_additive (attr := simp)]
theorem _root_.MulEquivClass.coe_symm_apply_apply {α β} [Mul α] [Mul β] {F} [EquivLike F α β]
    [MulEquivClass F α β] (e : F) (x : α) :
    (e : α ≃* β).symm (e x) = x :=
  (e : α ≃* β).left_inv x

end symm

section simps

-- we don't hyperlink the note in the additive version, since that breaks syntax highlighting
-- in the whole file.

/-- See Note [custom simps projection] -/
@[to_additive /-- See Note [custom simps projection] -/]
def Simps.symm_apply (e : M ≃* N) : N → M :=
  e.symm

initialize_simps_projections AddEquiv (toFun → apply, invFun → symm_apply)

initialize_simps_projections MulEquiv (toFun → apply, invFun → symm_apply)

end simps

section trans

/-- Transitivity of multiplication-preserving isomorphisms -/
@[to_additive (attr := trans) /-- Transitivity of addition-preserving isomorphisms -/]
def trans (h1 : M ≃* N) (h2 : N ≃* P) : M ≃* P :=
  { h1.toEquiv.trans h2.toEquiv with
    map_mul' := fun x y => show h2 (h1 (x * y)) = h2 (h1 x) * h2 (h1 y) by
      rw [map_mul, map_mul] }

@[to_additive (attr := simp)]
theorem coe_trans (e₁ : M ≃* N) (e₂ : N ≃* P) : ↑(e₁.trans e₂) = e₂ ∘ e₁ := rfl

@[to_additive (attr := simp)]
theorem trans_apply (e₁ : M ≃* N) (e₂ : N ≃* P) (m : M) : e₁.trans e₂ m = e₂ (e₁ m) := rfl

@[to_additive (attr := simp)]
theorem symm_trans_apply (e₁ : M ≃* N) (e₂ : N ≃* P) (p : P) :
    (e₁.trans e₂).symm p = e₁.symm (e₂.symm p) := rfl

@[to_additive (attr := simp)]
theorem symm_trans_self (e : M ≃* N) : e.symm.trans e = refl N :=
  DFunLike.ext _ _ e.apply_symm_apply

@[to_additive (attr := simp)]
theorem self_trans_symm (e : M ≃* N) : e.trans e.symm = refl M :=
  DFunLike.ext _ _ e.symm_apply_apply

end trans

/-- `MulEquiv.symm` defines an equivalence between `α ≃* β` and `β ≃* α`. -/
@[to_additive (attr := simps!)
/-- `AddEquiv.symm` defines an equivalence between `α ≃+ β` and `β ≃+ α` -/]
def symmEquiv (P Q : Type*) [Mul P] [Mul Q] : (P ≃* Q) ≃ (Q ≃* P) where
  toFun := .symm
  invFun := .symm

end Mul

/-!
## Monoids
-/

section MulOneClass
variable [MulOneClass M] [MulOneClass N] [MulOneClass P]

@[to_additive (attr := simp)]
theorem coe_monoidHom_refl : (refl M : M →* M) = MonoidHom.id M := rfl

@[to_additive (attr := simp)]
lemma coe_monoidHom_trans (e₁ : M ≃* N) (e₂ : N ≃* P) :
    (e₁.trans e₂ : M →* P) = (e₂ : N →* P).comp ↑e₁ := rfl

@[to_additive (attr := simp)]
lemma coe_monoidHom_comp_coe_monoidHom_symm (e : M ≃* N) :
    (e : M →* N).comp e.symm = MonoidHom.id _ := by ext; simp

@[to_additive (attr := simp)]
lemma coe_monoidHom_symm_comp_coe_monoidHom (e : M ≃* N) :
    (e.symm : N →* M).comp e = MonoidHom.id _ := by ext; simp

@[to_additive]
lemma comp_left_injective (e : M ≃* N) : Injective fun f : N →* P ↦ f.comp (e : M →* N) :=
  LeftInverse.injective (g := fun f ↦ f.comp e.symm) fun f ↦ by simp [MonoidHom.comp_assoc]

@[to_additive]
lemma comp_right_injective (e : M ≃* N) : Injective fun f : P →* M ↦ (e : M →* N).comp f :=
  LeftInverse.injective (g := (e.symm : N →* M).comp) fun f ↦ by simp [← MonoidHom.comp_assoc]

/-- A multiplicative isomorphism of monoids sends `1` to `1` (and is hence a monoid isomorphism). -/
@[to_additive
  /-- An additive isomorphism of additive monoids sends `0` to `0`
  (and is hence an additive monoid isomorphism). -/]
protected theorem map_one (h : M ≃* N) : h 1 = 1 := map_one h

@[to_additive]
protected theorem map_eq_one_iff (h : M ≃* N) {x : M} : h x = 1 ↔ x = 1 :=
  EmbeddingLike.map_eq_one_iff

@[to_additive]
theorem map_ne_one_iff (h : M ≃* N) {x : M} : h x ≠ 1 ↔ x ≠ 1 :=
  EmbeddingLike.map_ne_one_iff

/-- A bijective `Semigroup` homomorphism is an isomorphism -/
@[to_additive (attr := simps! apply)
/-- A bijective `AddSemigroup` homomorphism is an isomorphism -/]
noncomputable def ofBijective {M N F} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N]
    (f : F) (hf : Bijective f) : M ≃* N :=
  { Equiv.ofBijective f hf with map_mul' := map_mul f }

@[to_additive (attr := simp)]
theorem ofBijective_apply_symm_apply {n : N} (f : M →* N) (hf : Bijective f) :
    f ((ofBijective f hf).symm n) = n := (ofBijective f hf).apply_symm_apply n

/-- Extract the forward direction of a multiplicative equivalence
as a multiplication-preserving function.
-/
@[to_additive /-- Extract the forward direction of an additive equivalence
  as an addition-preserving function. -/]
def toMonoidHom (h : M ≃* N) : M →* N :=
  { h with map_one' := h.map_one }

@[to_additive (attr := simp)]
theorem coe_toMonoidHom (e : M ≃* N) : ⇑e.toMonoidHom = e := rfl

@[to_additive (attr := simp)]
theorem toMonoidHom_eq_coe (f : M ≃* N) : f.toMonoidHom = (f : M →* N) :=
  rfl

@[to_additive]
theorem toMonoidHom_injective : Injective (toMonoidHom : M ≃* N → M →* N) :=
  Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

end MulOneClass

/-!
# Groups
-/

/-- A multiplicative equivalence of groups preserves inversion. -/
@[to_additive /-- An additive equivalence of additive groups preserves negation. -/]
protected theorem map_inv [Group G] [DivisionMonoid H] (h : G ≃* H) (x : G) :
    h x⁻¹ = (h x)⁻¹ :=
  map_inv h x

/-- A multiplicative equivalence of groups preserves division. -/
@[to_additive /-- An additive equivalence of additive groups preserves subtractions. -/]
protected theorem map_div [Group G] [DivisionMonoid H] (h : G ≃* H) (x y : G) :
    h (x / y) = h x / h y :=
  map_div h x y

end MulEquiv

/-- Given a pair of multiplicative homomorphisms `f`, `g` such that `g.comp f = id` and
`f.comp g = id`, returns a multiplicative equivalence with `toFun = f` and `invFun = g`. This
constructor is useful if the underlying type(s) have specialized `ext` lemmas for multiplicative
homomorphisms. -/
@[to_additive (attr := simps -fullyApplied)
  /-- Given a pair of additive homomorphisms `f`, `g` such that `g.comp f = id` and
  `f.comp g = id`, returns an additive equivalence with `toFun = f` and `invFun = g`. This
  constructor is useful if the underlying type(s) have specialized `ext` lemmas for additive
  homomorphisms. -/]
def MulHom.toMulEquiv [Mul M] [Mul N] (f : M →ₙ* N) (g : N →ₙ* M) (h₁ : g.comp f = MulHom.id _)
    (h₂ : f.comp g = MulHom.id _) : M ≃* N where
  toFun := f
  invFun := g
  left_inv := DFunLike.congr_fun h₁
  right_inv := DFunLike.congr_fun h₂
  map_mul' := f.map_mul

/-- Given a pair of monoid homomorphisms `f`, `g` such that `g.comp f = id` and `f.comp g = id`,
returns a multiplicative equivalence with `toFun = f` and `invFun = g`.  This constructor is
useful if the underlying type(s) have specialized `ext` lemmas for monoid homomorphisms. -/
@[to_additive (attr := simps -fullyApplied)
  /-- Given a pair of additive monoid homomorphisms `f`, `g` such that `g.comp f = id`
  and `f.comp g = id`, returns an additive equivalence with `toFun = f` and `invFun = g`.  This
  constructor is useful if the underlying type(s) have specialized `ext` lemmas for additive
  monoid homomorphisms. -/]
def MonoidHom.toMulEquiv [MulOneClass M] [MulOneClass N] (f : M →* N) (g : N →* M)
    (h₁ : g.comp f = MonoidHom.id _) (h₂ : f.comp g = MonoidHom.id _) : M ≃* N where
  toFun := f
  invFun := g
  left_inv := DFunLike.congr_fun h₁
  right_inv := DFunLike.congr_fun h₂
  map_mul' := f.map_mul
