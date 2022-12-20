/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module data.fun_like.equiv
! leanprover-community/mathlib commit f340f229b1f461aa1c8ee11e0a172d0a3b301a4a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.FunLike.Embedding

/-!
# Typeclass for a type `F` with an injective map to `A ≃ B`

This typeclass is primarily for use by isomorphisms like `MonoidEquiv` and `LinearEquiv`.

## Basic usage of `EquivLike`

A typical type of morphisms should be declared as:
```
structure MyIso (A B : Type*) [MyClass A] [MyClass B]
  extends Equiv A B :=
(map_op' : ∀ {x y : A}, toFun (MyClass.op x y) = MyClass.op (toFun x) (toFun y))

namespace MyIso

variables (A B : Type*) [MyClass A] [MyClass B]

-- This instance is optional if you follow the "Isomorphism class" design below:
instance : EquivLike (MyIso A B) A (λ _, B) :=
{ coe := MyIso.toEquiv.toFun,
  inv := MyIso.toEquiv.invFun,
  left_inv := MyIso.toEquiv.left_inv,
  right_inv := MyIso.toEquiv.right_inv,
  coe_injective' := λ f g h, by cases f; cases g; congr' }

/-- Helper instance for when there's too many metavariables to apply `EquivLike.coe` directly. -/
instance : CoeFun (MyIso A B) := FunLike.instCoeFunForAll

@[ext] theorem ext {f g : MyIso A B} (h : ∀ x, f x = g x) : f = g := FunLike.ext f g h

/-- Copy of a `MyIso` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : MyIso A B) (f' : A → B) (f_inv : B → A) (h : f' = ⇑f) : MyIso A B :=
{ toFun := f',
  invFun := f_inv,
  left_inv := h.symm ▸ f.left_inv,
  right_inv := h.symm ▸ f.right_inv,
  map_op' := h.symm ▸ f.map_op' }

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
class MyIsoClass (F : Type*) (A B : outParam <| Type _) [MyClass A] [MyClass B]
  extends EquivLike F A (λ _, B), MyHomClass F A B

end

-- You can replace `MyIso.EquivLike` with the below instance:
instance : MyIsoClass (MyIso A B) A B :=
{ coe := MyIso.toFun,
  inv := MyIso.invFun,
  left_inv := MyIso.left_inv,
  right_inv := MyIso.right_inv,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_op := MyIso.map_op' }

-- [Insert `CoeFun`, `ext` and `copy` here]
```

The second step is to add instances of your new `MyIsoClass` for all types extending `MyIso`.
Typically, you can just declare a new class analogous to `MyIsoClass`:

```
structure CoolerIso (A B : Type*) [CoolClass A] [CoolClass B]
  extends MyIso A B :=
(map_cool' : toFun CoolClass.cool = CoolClass.cool)

section
set_option old_structure_cmd true

class CoolerIsoClass (F : Type*) (A B : outParam <| Type _) [CoolClass A] [CoolClass B]
  extends MyIsoClass F A B :=
(map_cool : ∀ (f : F), f CoolClass.cool = CoolClass.cool)

end

@[simp] lemma map_cool {F A B : Type*} [CoolClass A] [CoolClass B] [CoolerIsoClass F A B]
  (f : F) : f CoolClass.cool = CoolClass.cool :=
CoolerIsoClass.map_cool

instance : CoolerIsoClass (CoolerIso A B) A B :=
{ coe := CoolerIso.toFun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_op := CoolerIso.map_op',
  map_cool := CoolerIso.map_cool' }

-- [Insert `CoeFun`, `ext` and `copy` here]
```

Then any declaration taking a specific type of morphisms as parameter can instead take the
class you just defined:
```
-- Compare with: lemma do_something (f : MyIso A B) : sorry := sorry
lemma do_something {F : Type*} [MyIsoClass F A B] (f : F) : sorry := sorry
```

This means anything set up for `MyIso`s will automatically work for `CoolerIsoClass`es,
and defining `CoolerIsoClass` only takes a constant amount of effort,
instead of linearly increasing the work per `MyIso`-related declaration.

-/


/-- The class `EquivLike E α β` expresses that terms of type `E` have an
injective coercion to bijections between `α` and `β`.

This typeclass is used in the definition of the homomorphism typeclasses,
such as `zero_equiv_class`, `mul_equiv_class`, `monoid_equiv_class`, ....
-/
class EquivLike (E : Sort _) (α β : outParam (Sort _)) where
  /-- The coercion to a function in the forward direction. -/
  coe : E → α → β
  /-- The coercion to a function in the backwards direction. -/
  inv : E → β → α
  /-- The coercions are left inverses. -/
  left_inv : ∀ e, Function.LeftInverse (inv e) (coe e)
  /-- The coercions are right inverses. -/
  right_inv : ∀ e, Function.RightInverse (inv e) (coe e)
  /-- If two coercions to functions are jointly injective. -/
  coe_injective' : ∀ e g, coe e = coe g → inv e = inv g → e = g
  -- This is mathematically equivalent to either of the coercions to functions being injective, but
  -- the `inv` hypothesis makes this easier to prove with `congr'`

namespace EquivLike

variable {E F α β γ : Sort _} [iE : EquivLike E α β] [iF : EquivLike F β γ]

theorem inv_injective : Function.Injective (EquivLike.inv : E → β → α) := fun e g h ↦
  coe_injective' e g ((right_inv e).eq_rightInverse (h.symm ▸ left_inv g)) h

instance (priority := 100) toEmbeddingLike : EmbeddingLike E α β where
  coe := (coe : E → α → β)
  coe_injective' e g h :=
    coe_injective' e g h ((left_inv e).eq_rightInverse (h.symm ▸ right_inv g))
  injective' e := (left_inv e).injective

protected theorem injective (e : E) : Function.Injective e :=
  EmbeddingLike.injective e

protected theorem surjective (e : E) : Function.Surjective e :=
  (right_inv e).surjective

protected theorem bijective (e : E) : Function.Bijective (e : α → β) :=
  ⟨EquivLike.injective e, EquivLike.surjective e⟩

theorem apply_eq_iff_eq (f : E) {x y : α} : f x = f y ↔ x = y :=
  EmbeddingLike.apply_eq_iff_eq f

@[simp]
theorem injective_comp (e : E) (f : β → γ) : Function.Injective (f ∘ e) ↔ Function.Injective f :=
  Function.Injective.of_comp_iff' f (EquivLike.bijective e)

@[simp]
theorem surjective_comp (e : E) (f : β → γ) : Function.Surjective (f ∘ e) ↔ Function.Surjective f :=
  (EquivLike.surjective e).of_comp_iff f

@[simp]
theorem bijective_comp (e : E) (f : β → γ) : Function.Bijective (f ∘ e) ↔ Function.Bijective f :=
  (EquivLike.bijective e).of_comp_iff f

/-- This lemma is only supposed to be used in the generic context, when working with instances
of classes extending `EquivLike`.
For concrete isomorphism types such as `Equiv`, you should use `Equiv.symm_apply_apply`
or its equivalent.

TODO: define a generic form of `Equiv.symm`. -/
@[simp]
theorem inv_apply_apply (e : E) (a : α) : EquivLike.inv e (e a) = a :=
  left_inv _ _

/-- This lemma is only supposed to be used in the generic context, when working with instances
of classes extending `EquivLike`.
For concrete isomorphism types such as `Equiv`, you should use `Equiv.apply_symm_apply`
or its equivalent.

TODO: define a generic form of `Equiv.symm`. -/
@[simp]
theorem apply_inv_apply (e : E) (b : β) : e (EquivLike.inv e b) = b :=
  right_inv _ _

theorem comp_injective (f : α → β) (e : F) : Function.Injective (e ∘ f) ↔ Function.Injective f :=
  EmbeddingLike.comp_injective f e

@[simp]
theorem comp_surjective (f : α → β) (e : F) : Function.Surjective (e ∘ f) ↔ Function.Surjective f :=
  Function.Surjective.of_comp_iff' (EquivLike.bijective e) f

@[simp]
theorem comp_bijective (f : α → β) (e : F) : Function.Bijective (e ∘ f) ↔ Function.Bijective f :=
  (EquivLike.bijective e).of_comp_iff' f

/-- This is not an instance to avoid slowing down every single `Subsingleton` typeclass search.-/
lemma subsingleton_dom [Subsingleton β] : Subsingleton F :=
⟨fun f g ↦ FunLike.ext f g $ fun _ ↦ (right_inv f).injective $ Subsingleton.elim _ _⟩

end EquivLike
