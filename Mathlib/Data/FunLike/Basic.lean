/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.NormCast

/-!
# Typeclass for a type `F` with an injective map to `A → B`

This typeclass is primarily for use by homomorphisms like `monoid_hom` and `linear_map`.

## Basic usage of `fun_like`

A typical type of morphisms should be declared as:
```
structure my_hom (A B : Type*) [my_class A] [my_class B] :=
(to_fun : A → B)
(map_op' : ∀ {x y : A}, to_fun (my_class.op x y) = my_class.op (to_fun x) (to_fun y))

namespace my_hom

variables (A B : Type*) [my_class A] [my_class B]

-- This instance is optional if you follow the "morphism class" design below:
instance : fun_like (my_hom A B) A (λ _, B) :=
{ coe := my_hom.to_fun, coe_injective' := λ f g h, by cases f; cases g; congr' }

/-- Helper instance for when there's too many metavariables to apply
`fun_like.has_coe_to_fun` directly. -/
instance : has_coe_to_fun (my_hom A B) (λ _, A → B) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe {f : my_hom A B} : f.to_fun = (f : A → B) := rfl

@[ext] theorem ext {f g : my_hom A B} (h : ∀ x, f x = g x) : f = g := fun_like.ext f g h

/-- Copy of a `my_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : my_hom A B) (f' : A → B) (h : f' = ⇑f) : my_hom A B :=
{ to_fun := f',
  map_op' := h.symm ▸ f.map_op' }

end my_hom
```

This file will then provide a `has_coe_to_fun` instance and various
extensionality and simp lemmas.

## Morphism classes extending `fun_like`

The `fun_like` design provides further benefits if you put in a bit more work.
The first step is to extend `fun_like` to create a class of those types satisfying
the axioms of your new type of morphisms.
Continuing the example above:

```
section
set_option old_structure_cmd true

/-- `my_hom_class F A B` states that `F` is a type of `my_class.op`-preserving morphisms.
You should extend this class when you extend `my_hom`. -/
class my_hom_class (F : Type*) (A B : out_param $ Type*) [my_class A] [my_class B]
  extends fun_like F A (λ _, B) :=
(map_op : ∀ (f : F) (x y : A), f (my_class.op x y) = my_class.op (f x) (f y))

end
@[simp] lemma map_op {F A B : Type*} [my_class A] [my_class B] [my_hom_class F A B]
  (f : F) (x y : A) : f (my_class.op x y) = my_class.op (f x) (f y) :=
my_hom_class.map_op

-- You can replace `my_hom.fun_like` with the below instance:
instance : my_hom_class (my_hom A B) A B :=
{ coe := my_hom.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_op := my_hom.map_op' }

-- [Insert `has_coe_to_fun`, `to_fun_eq_coe`, `ext` and `copy` here]
```

The second step is to add instances of your new `my_hom_class` for all types extending `my_hom`.
Typically, you can just declare a new class analogous to `my_hom_class`:

```
structure cooler_hom (A B : Type*) [cool_class A] [cool_class B]
  extends my_hom A B :=
(map_cool' : to_fun cool_class.cool = cool_class.cool)

section
set_option old_structure_cmd true

class cooler_hom_class (F : Type*) (A B : out_param $ Type*) [cool_class A] [cool_class B]
  extends my_hom_class F A B :=
(map_cool : ∀ (f : F), f cool_class.cool = cool_class.cool)

end

@[simp] lemma map_cool {F A B : Type*} [cool_class A] [cool_class B] [cooler_hom_class F A B]
  (f : F) : f cool_class.cool = cool_class.cool :=
my_hom_class.map_op

-- You can also replace `my_hom.fun_like` with the below instance:
instance : cool_hom_class (cool_hom A B) A B :=
{ coe := cool_hom.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_op := cool_hom.map_op',
  map_cool := cool_hom.map_cool' }

-- [Insert `has_coe_to_fun`, `to_fun_eq_coe`, `ext` and `copy` here]
```

Then any declaration taking a specific type of morphisms as parameter can instead take the
class you just defined:
```
-- Compare with: lemma do_something (f : my_hom A B) : sorry := sorry
lemma do_something {F : Type*} [my_hom_class F A B] (f : F) : sorry := sorry
```

This means anything set up for `my_hom`s will automatically work for `cool_hom_class`es,
and defining `cool_hom_class` only takes a constant amount of effort,
instead of linearly increasing the work per `my_hom`-related declaration.

-/

-- Porting note: Not sure what to do with this!
-- Porting note: this had priority 10 in mathlib 3.
-- This instance should have low priority, to ensure we follow the chain
-- `FunLike → CoeFun`
-- attribute [instance] coe_fn_trans

/-- The class `fun_like F α β` expresses that terms of type `F` have an
injective coercion to functions from `α` to `β`.

This typeclass is used in the definition of the homomorphism typeclasses,
such as `zero_hom_class`, `mul_hom_class`, `monoid_hom_class`, ....
-/
class FunLike (F : Sort _) (α : outParam (Sort _)) (β : outParam <| α → Sort _) where
  coe : F → ∀ a : α, β a
  coe_injective' : Function.Injective coe

section Dependent

/-! ### `FunLike F α β` where `β` depends on `a : α` -/

variable (F α : Sort _) (β : α → Sort _)

namespace FunLike

variable {F α β} [i : FunLike F α β]

-- Give this a priority between `coe_fn_trans` and the default priority
-- `α` and `β` are out_params, so this instance should not be dangerous
-- Porting note: @[nolint dangerous_instance]
instance (priority := 100) : CoeFun F fun _ => ∀ a : α, β a where coe := FunLike.coe

-- Porting note: the next two lemmas presumably aren't needed.
-- @[simp]
-- theorem coe_eq_coe_fn : (FunLike.coe : F → ∀ a : α, β a) = coeFn :=
--   rfl

-- theorem coe_injective : Function.Injective (coeFn : F → ∀ a : α, β a) :=
--   FunLike.coe_injective'

@[simp]
theorem coe_fn_eq {f g : F} : (f : ∀ a : α, β a) = (g : ∀ a : α, β a) ↔ f = g :=
  ⟨fun h => FunLike.coe_injective' h, fun h => by cases h <;> rfl⟩

theorem ext' {f g : F} (h : (f : ∀ a : α, β a) = (g : ∀ a : α, β a)) : f = g :=
  FunLike.coe_injective' h

theorem ext'_iff {f g : F} : f = g ↔ (f : ∀ a : α, β a) = (g : ∀ a : α, β a) :=
  coe_fn_eq.symm

theorem ext (f g : F) (h : ∀ x : α, f x = g x) : f = g :=
  FunLike.coe_injective' (funext h)

theorem ext_iff {f g : F} : f = g ↔ ∀ x, f x = g x :=
  coe_fn_eq.symm.trans Function.funext_iff

protected theorem congr_fun {f g : F} (h₁ : f = g) (x : α) : f x = g x :=
  congr_fun (congr_arg _ h₁) x

theorem ne_iff {f g : F} : f ≠ g ↔ ∃ a, f a ≠ g a :=
  ext_iff.not.trans not_forall

theorem exists_ne {f g : F} (h : f ≠ g) : ∃ x, f x ≠ g x :=
  ne_iff.mp h

end FunLike

end Dependent

section NonDependent

/-! ### `FunLike F α (λ _, β)` where `β` does not depend on `a : α` -/

variable {F α β : Sort _} [i : FunLike F α fun _ => β]

namespace FunLike

protected theorem congr {f g : F} {x y : α} (h₁ : f = g) (h₂ : x = y) : f x = g y :=
  congr (congr_arg _ h₁) h₂

protected theorem congr_arg (f : F) {x y : α} (h₂ : x = y) : f x = f y :=
  congr_arg _ h₂

end FunLike

end NonDependent
