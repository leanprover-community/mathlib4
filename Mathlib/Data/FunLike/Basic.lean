/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.NormCast

#align_import data.fun_like.basic from "leanprover-community/mathlib"@"a148d797a1094ab554ad4183a4ad6f130358ef64"

/-!
# Typeclass for a type `F` with an injective map to `A → B`

This typeclass is primarily for use by homomorphisms like `MonoidHom` and `LinearMap`.

## Basic usage of `FunLike`

A typical type of morphisms should be declared as:
```
structure MyHom (A B : Type*) [MyClass A] [MyClass B] :=
  (toFun : A → B)
  (map_op' : ∀ {x y : A}, toFun (MyClass.op x y) = MyClass.op (toFun x) (toFun y))

namespace MyHom

variables (A B : Type*) [MyClass A] [MyClass B]

-- This instance is optional if you follow the "morphism class" design below:
instance : FunLike (MyHom A B) A (λ _, B) :=
  { coe := MyHom.toFun, coe_injective' := λ f g h, by cases f; cases g; congr' }

/-- Helper instance for when there's too many metavariables to apply
`FunLike.coe` directly. -/
instance : CoeFun (MyHom A B) (λ _, A → B) := ⟨MyHom.toFun⟩

@[ext] theorem ext {f g : MyHom A B} (h : ∀ x, f x = g x) : f = g := FunLike.ext f g h

/-- Copy of a `MyHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : MyHom A B) (f' : A → B) (h : f' = ⇑f) : MyHom A B :=
  { toFun := f',
    map_op' := h.symm ▸ f.map_op' }

end MyHom
```

This file will then provide a `CoeFun` instance and various
extensionality and simp lemmas.

## Morphism classes extending `FunLike`

The `FunLike` design provides further benefits if you put in a bit more work.
The first step is to extend `FunLike` to create a class of those types satisfying
the axioms of your new type of morphisms.
Continuing the example above:

```
/-- `MyHomClass F A B` states that `F` is a type of `MyClass.op`-preserving morphisms.
You should extend this class when you extend `MyHom`. -/
class MyHomClass (F : Type*) (A B : outParam <| Type*) [MyClass A] [MyClass B]
  extends FunLike F A (λ _, B) :=
(map_op : ∀ (f : F) (x y : A), f (MyClass.op x y) = MyClass.op (f x) (f y))

@[simp] lemma map_op {F A B : Type*} [MyClass A] [MyClass B] [MyHomClass F A B]
  (f : F) (x y : A) : f (MyClass.op x y) = MyClass.op (f x) (f y) :=
MyHomClass.map_op

-- You can replace `MyHom.FunLike` with the below instance:
instance : MyHomClass (MyHom A B) A B :=
  { coe := MyHom.toFun,
    coe_injective' := λ f g h, by cases f; cases g; congr',
    map_op := MyHom.map_op' }

-- [Insert `CoeFun`, `ext` and `copy` here]
```

The second step is to add instances of your new `MyHomClass` for all types extending `MyHom`.
Typically, you can just declare a new class analogous to `MyHomClass`:

```
structure CoolerHom (A B : Type*) [CoolClass A] [CoolClass B]
  extends MyHom A B :=
(map_cool' : toFun CoolClass.cool = CoolClass.cool)

class CoolerHomClass (F : Type*) (A B : outParam <| Type*) [CoolClass A] [CoolClass B]
  extends MyHomClass F A B :=
(map_cool : ∀ (f : F), f CoolClass.cool = CoolClass.cool)

@[simp] lemma map_cool {F A B : Type*} [CoolClass A] [CoolClass B] [CoolerHomClass F A B]
  (f : F) : f CoolClass.cool = CoolClass.cool :=
MyHomClass.map_op

-- You can also replace `MyHom.FunLike` with the below instance:
instance : CoolerHomClass (CoolHom A B) A B :=
  { coe := CoolHom.toFun,
    coe_injective' := λ f g h, by cases f; cases g; congr',
    map_op := CoolHom.map_op',
    map_cool := CoolHom.map_cool' }

-- [Insert `CoeFun`, `ext` and `copy` here]
```

Then any declaration taking a specific type of morphisms as parameter can instead take the
class you just defined:
```
-- Compare with: lemma do_something (f : MyHom A B) : sorry := sorry
lemma do_something {F : Type*} [MyHomClass F A B] (f : F) : sorry := sorry
```

This means anything set up for `MyHom`s will automatically work for `CoolerHomClass`es,
and defining `CoolerHomClass` only takes a constant amount of effort,
instead of linearly increasing the work per `MyHom`-related declaration.

-/

-- This instance should have low priority, to ensure we follow the chain
-- `FunLike → CoeFun`
-- Porting note: this is an elaboration detail from Lean 3, we are going to disable it
-- until it is clearer what the Lean 4 elaborator needs.
-- attribute [instance, priority 10] coe_fn_trans

/-- The class `FunLike F α β` expresses that terms of type `F` have an
injective coercion to functions from `α` to `β`.

This typeclass is used in the definition of the homomorphism typeclasses,
such as `ZeroHomClass`, `MulHomClass`, `MonoidHomClass`, ....
-/
@[notation_class * toFun Simps.findCoercionArgs]
class FunLike (F : Sort*) (α : outParam (Sort*)) (β : outParam <| α → Sort*) where
  /-- The coercion from `F` to a function. -/
  coe : F → ∀ a : α, β a
  /-- The coercion to functions must be injective. -/
  coe_injective' : Function.Injective coe
#align fun_like FunLike

-- https://github.com/leanprover/lean4/issues/2096
compile_def% FunLike.coe

section Dependent

/-! ### `FunLike F α β` where `β` depends on `a : α` -/

variable (F α : Sort*) (β : α → Sort*)

namespace FunLike

variable {F α β} [i : FunLike F α β]

instance (priority := 100) hasCoeToFun : CoeFun F fun _ ↦ ∀ a : α, β a where coe := FunLike.coe

#eval Lean.Elab.Command.liftTermElabM do
  Std.Tactic.Coe.registerCoercion ``FunLike.coe
    (some { numArgs := 5, coercee := 4, type := .coeFun })

-- @[simp] -- porting note: this loops in lean 4
theorem coe_eq_coe_fn : (FunLike.coe (F := F)) = (fun f => ↑f) := rfl
#align fun_like.coe_eq_coe_fn FunLike.coe_eq_coe_fn

theorem coe_injective : Function.Injective (fun f : F ↦ (f : ∀ a : α, β a)) :=
  FunLike.coe_injective'
#align fun_like.coe_injective FunLike.coe_injective

@[simp]
theorem coe_fn_eq {f g : F} : (f : ∀ a : α, β a) = (g : ∀ a : α, β a) ↔ f = g :=
  ⟨fun h ↦ FunLike.coe_injective' h, fun h ↦ by cases h; rfl⟩
                                                -- ⊢ ↑f = ↑f
                                                         -- 🎉 no goals
#align fun_like.coe_fn_eq FunLike.coe_fn_eq

theorem ext' {f g : F} (h : (f : ∀ a : α, β a) = (g : ∀ a : α, β a)) : f = g :=
  FunLike.coe_injective' h
#align fun_like.ext' FunLike.ext'

theorem ext'_iff {f g : F} : f = g ↔ (f : ∀ a : α, β a) = (g : ∀ a : α, β a) :=
  coe_fn_eq.symm
#align fun_like.ext'_iff FunLike.ext'_iff

theorem ext (f g : F) (h : ∀ x : α, f x = g x) : f = g :=
  FunLike.coe_injective' (funext h)
#align fun_like.ext FunLike.ext

theorem ext_iff {f g : F} : f = g ↔ ∀ x, f x = g x :=
  coe_fn_eq.symm.trans Function.funext_iff
#align fun_like.ext_iff FunLike.ext_iff

protected theorem congr_fun {f g : F} (h₁ : f = g) (x : α) : f x = g x :=
  congr_fun (congr_arg _ h₁) x
#align fun_like.congr_fun FunLike.congr_fun

theorem ne_iff {f g : F} : f ≠ g ↔ ∃ a, f a ≠ g a :=
  ext_iff.not.trans not_forall
#align fun_like.ne_iff FunLike.ne_iff

theorem exists_ne {f g : F} (h : f ≠ g) : ∃ x, f x ≠ g x :=
  ne_iff.mp h
#align fun_like.exists_ne FunLike.exists_ne

/-- This is not an instance to avoid slowing down every single `Subsingleton` typeclass search.-/
lemma subsingleton_cod [∀ a, Subsingleton (β a)] : Subsingleton F :=
  ⟨fun _ _ ↦ coe_injective $ Subsingleton.elim _ _⟩
#align fun_like.subsingleton_cod FunLike.subsingleton_cod

end FunLike

end Dependent

section NonDependent

/-! ### `FunLike F α (λ _, β)` where `β` does not depend on `a : α` -/

variable {F α β : Sort*} [i : FunLike F α fun _ ↦ β]

namespace FunLike

protected theorem congr {f g : F} {x y : α} (h₁ : f = g) (h₂ : x = y) : f x = g y :=
  congr (congr_arg _ h₁) h₂
#align fun_like.congr FunLike.congr

protected theorem congr_arg (f : F) {x y : α} (h₂ : x = y) : f x = f y :=
  congr_arg _ h₂
#align fun_like.congr_arg FunLike.congr_arg

end FunLike

end NonDependent
