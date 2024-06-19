/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Data.FunLike.Embedding

#align_import data.fun_like.equiv from "leanprover-community/mathlib"@"f340f229b1f461aa1c8ee11e0a172d0a3b301a4a"

/-!
# Typeclass for a type `F` with an injective map to `A ≃ B`

This typeclass is primarily for use by isomorphisms like `MonoidEquiv` and `LinearEquiv`.

## Basic usage of `EquivLike`

A typical type of isomorphisms should be declared as:
```
structure MyIso (A B : Type*) [MyClass A] [MyClass B] extends Equiv A B :=
  (map_op' : ∀ (x y : A), toFun (MyClass.op x y) = MyClass.op (toFun x) (toFun y))

namespace MyIso

variable (A B : Type*) [MyClass A] [MyClass B]

instance instEquivLike : EquivLike (MyIso A B) A B where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by cases f; cases g; congr; exact EquivLike.coe_injective' _ _ h₁ h₂

@[ext] theorem ext {f g : MyIso A B} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

/-- Copy of a `MyIso` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : MyIso A B) (f' : A → B) (f_inv : B → A)
    (h₁ : f' = f) (h₂ : f_inv = f.invFun) : MyIso A B where
  toFun := f'
  invFun := f_inv
  left_inv := h₁.symm ▸ h₂.symm ▸ f.left_inv
  right_inv := h₁.symm ▸ h₂.symm ▸ f.right_inv
  map_op' := h₁.symm ▸ f.map_op'

end MyIso
```

This file will then provide a `CoeFun` instance and various
extensionality and simp lemmas.

## Isomorphism classes extending `EquivLike`

The `EquivLike` design provides further benefits if you put in a bit more work.
The first step is to extend `EquivLike` to create a class of those types satisfying
the axioms of your new type of isomorphisms.
Continuing the example above:

```
/-- `MyIsoClass F A B` states that `F` is a type of `MyClass.op`-preserving morphisms.
You should extend this class when you extend `MyIso`. -/
class MyIsoClass (F : Type*) (A B : outParam Type*) [MyClass A] [MyClass B]
    [EquivLike F A B]
    extends MyHomClass F A B

namespace MyIso

variable {A B : Type*} [MyClass A] [MyClass B]

-- This goes after `MyIsoClass.instEquivLike`:
instance : MyIsoClass (MyIso A B) A B where
  map_op := MyIso.map_op'

-- [Insert `ext` and `copy` here]

end MyIso
```

The second step is to add instances of your new `MyIsoClass` for all types extending `MyIso`.
Typically, you can just declare a new class analogous to `MyIsoClass`:

```
structure CoolerIso (A B : Type*) [CoolClass A] [CoolClass B] extends MyIso A B :=
  (map_cool' : toFun CoolClass.cool = CoolClass.cool)

class CoolerIsoClass (F : Type*) (A B : outParam Type*) [CoolClass A] [CoolClass B]
    [EquivLike F A B]
    extends MyIsoClass F A B :=
  (map_cool : ∀ (f : F), f CoolClass.cool = CoolClass.cool)

@[simp] lemma map_cool {F A B : Type*} [CoolClass A] [CoolClass B]
    [EquivLike F A B] [CoolerIsoClass F A B] (f : F) :
    f CoolClass.cool = CoolClass.cool :=
  CoolerIsoClass.map_cool _

namespace CoolerIso

variable {A B : Type*} [CoolClass A] [CoolClass B]

instance : EquivLike (CoolerIso A B) A B where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by cases f; cases g; congr; exact EquivLike.coe_injective' _ _ h₁ h₂

instance : CoolerIsoClass (CoolerIso A B) A B where
  map_op f := f.map_op'
  map_cool f := f.map_cool'

-- [Insert `ext` and `copy` here]

end CoolerIso
```

Then any declaration taking a specific type of morphisms as parameter can instead take the
class you just defined:
```
-- Compare with: lemma do_something (f : MyIso A B) : sorry := sorry
lemma do_something {F : Type*} [EquivLike F A B] [MyIsoClass F A B] (f : F) : sorry := sorry
```

This means anything set up for `MyIso`s will automatically work for `CoolerIsoClass`es,
and defining `CoolerIsoClass` only takes a constant amount of effort,
instead of linearly increasing the work per `MyIso`-related declaration.

-/


/-- The class `EquivLike E α β` expresses that terms of type `E` have an
injective coercion to bijections between `α` and `β`.

Note that this does not directly extend `FunLike`, nor take `FunLike` as a parameter,
so we can state `coe_injective'` in a nicer way.

This typeclass is used in the definition of the isomorphism (or equivalence) typeclasses,
such as `ZeroEquivClass`, `MulEquivClass`, `MonoidEquivClass`, ....
-/
class EquivLike (E : Sort*) (α β : outParam (Sort*)) where
  /-- The coercion to a function in the forward direction. -/
  coe : E → α → β
  /-- The coercion to a function in the backwards direction. -/
  inv : E → β → α
  /-- The coercions are left inverses. -/
  left_inv : ∀ e, Function.LeftInverse (inv e) (coe e)
  /-- The coercions are right inverses. -/
  right_inv : ∀ e, Function.RightInverse (inv e) (coe e)
  /-- The two coercions to functions are jointly injective. -/
  coe_injective' : ∀ e g, coe e = coe g → inv e = inv g → e = g
  -- This is mathematically equivalent to either of the coercions to functions being injective, but
  -- the `inv` hypothesis makes this easier to prove with `congr'`
#align equiv_like EquivLike

namespace EquivLike

variable {E F α β γ : Sort*} [iE : EquivLike E α β] [iF : EquivLike F β γ]

theorem inv_injective : Function.Injective (EquivLike.inv : E → β → α) := fun e g h ↦
  coe_injective' e g ((right_inv e).eq_rightInverse (h.symm ▸ left_inv g)) h
#align equiv_like.inv_injective EquivLike.inv_injective

instance (priority := 100) toFunLike : FunLike E α β where
  coe := (coe : E → α → β)
  coe_injective' e g h :=
    coe_injective' e g h ((left_inv e).eq_rightInverse (h.symm ▸ right_inv g))

instance (priority := 100) toEmbeddingLike : EmbeddingLike E α β where
  injective' e := (left_inv e).injective

protected theorem injective (e : E) : Function.Injective e :=
  EmbeddingLike.injective e
#align equiv_like.injective EquivLike.injective

protected theorem surjective (e : E) : Function.Surjective e :=
  (right_inv e).surjective
#align equiv_like.surjective EquivLike.surjective

protected theorem bijective (e : E) : Function.Bijective (e : α → β) :=
  ⟨EquivLike.injective e, EquivLike.surjective e⟩
#align equiv_like.bijective EquivLike.bijective

theorem apply_eq_iff_eq (f : E) {x y : α} : f x = f y ↔ x = y :=
  EmbeddingLike.apply_eq_iff_eq f
#align equiv_like.apply_eq_iff_eq EquivLike.apply_eq_iff_eq

@[simp]
theorem injective_comp (e : E) (f : β → γ) : Function.Injective (f ∘ e) ↔ Function.Injective f :=
  Function.Injective.of_comp_iff' f (EquivLike.bijective e)
#align equiv_like.injective_comp EquivLike.injective_comp

@[simp]
theorem surjective_comp (e : E) (f : β → γ) : Function.Surjective (f ∘ e) ↔ Function.Surjective f :=
  (EquivLike.surjective e).of_comp_iff f
#align equiv_like.surjective_comp EquivLike.surjective_comp

@[simp]
theorem bijective_comp (e : E) (f : β → γ) : Function.Bijective (f ∘ e) ↔ Function.Bijective f :=
  (EquivLike.bijective e).of_comp_iff f
#align equiv_like.bijective_comp EquivLike.bijective_comp

/-- This lemma is only supposed to be used in the generic context, when working with instances
of classes extending `EquivLike`.
For concrete isomorphism types such as `Equiv`, you should use `Equiv.symm_apply_apply`
or its equivalent.

TODO: define a generic form of `Equiv.symm`. -/
@[simp]
theorem inv_apply_apply (e : E) (a : α) : EquivLike.inv e (e a) = a :=
  left_inv _ _
#align equiv_like.inv_apply_apply EquivLike.inv_apply_apply

/-- This lemma is only supposed to be used in the generic context, when working with instances
of classes extending `EquivLike`.
For concrete isomorphism types such as `Equiv`, you should use `Equiv.apply_symm_apply`
or its equivalent.

TODO: define a generic form of `Equiv.symm`. -/
@[simp]
theorem apply_inv_apply (e : E) (b : β) : e (EquivLike.inv e b) = b :=
  right_inv _ _
#align equiv_like.apply_inv_apply EquivLike.apply_inv_apply

theorem comp_injective (f : α → β) (e : F) : Function.Injective (e ∘ f) ↔ Function.Injective f :=
  EmbeddingLike.comp_injective f e
#align equiv_like.comp_injective EquivLike.comp_injective

@[simp]
theorem comp_surjective (f : α → β) (e : F) : Function.Surjective (e ∘ f) ↔ Function.Surjective f :=
  Function.Surjective.of_comp_iff' (EquivLike.bijective e) f
#align equiv_like.comp_surjective EquivLike.comp_surjective

@[simp]
theorem comp_bijective (f : α → β) (e : F) : Function.Bijective (e ∘ f) ↔ Function.Bijective f :=
  (EquivLike.bijective e).of_comp_iff' f
#align equiv_like.comp_bijective EquivLike.comp_bijective

/-- This is not an instance to avoid slowing down every single `Subsingleton` typeclass search. -/
lemma subsingleton_dom [Subsingleton β] : Subsingleton F :=
  ⟨fun f g ↦ DFunLike.ext f g fun _ ↦ (right_inv f).injective <| Subsingleton.elim _ _⟩
#align equiv_like.subsingleton_dom EquivLike.subsingleton_dom

end EquivLike
