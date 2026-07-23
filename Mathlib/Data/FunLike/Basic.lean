/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public meta import Lean.Meta.CoeAttr
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Unique
public import Mathlib.Util.CompileInductive
public import Mathlib.Tactic.Simps.NotationClass
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.Simproc.CastData

/-!
# Typeclass for a type `F` with an injective map to `A → B`

This typeclass is primarily for use by homomorphisms like `MonoidHom` and `LinearMap`.

There is the "D"ependent version `DFunLike` and the non-dependent version `FunLike`.

## Basic usage of `DFunLike` and `FunLike`

A typical type of morphisms should be declared as:
```
structure MyHom (A B : Type*) [MyClass A] [MyClass B] where
  (toFun : A → B)
  (map_op' : ∀ (x y : A), toFun (MyClass.op x y) = MyClass.op (toFun x) (toFun y))

namespace MyHom

variable (A B : Type*) [MyClass A] [MyClass B]

instance : FunLike (MyHom A B) A B where
  coe := MyHom.toFun
  coe_injective := fun f g h => by cases f; cases g; congr

@[ext] theorem ext {f g : MyHom A B} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

/-- Copy of a `MyHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : MyHom A B) (f' : A → B) (h : f' = ⇑f) : MyHom A B where
  toFun := f'
  map_op' := h.symm ▸ f.map_op'

end MyHom
```

This file will then provide a `CoeFun` instance and various
extensionality and simp lemmas.

## Morphism classes extending `DFunLike` and `FunLike`

The `FunLike` design provides further benefits if you put in a bit more work.
The first step is to extend `FunLike` to create a class of those types satisfying
the axioms of your new type of morphisms.
Continuing the example above:

```
/-- `MyHomClass F A B` states that `F` is a type of `MyClass.op`-preserving morphisms.
You should extend this class when you extend `MyHom`. -/
class MyHomClass (F : Type*) (A B : outParam Type*) [MyClass A] [MyClass B]
    [FunLike F A B] : Prop :=
  (map_op : ∀ (f : F) (x y : A), f (MyClass.op x y) = MyClass.op (f x) (f y))

@[simp]
lemma map_op {F A B : Type*} [MyClass A] [MyClass B] [FunLike F A B] [MyHomClass F A B]
    (f : F) (x y : A) :
    f (MyClass.op x y) = MyClass.op (f x) (f y) :=
  MyHomClass.map_op _ _ _

-- You can add the below instance next to `MyHomClass.instFunLike`:
instance : MyHomClass (MyHom A B) A B where
  map_op := MyHom.map_op'

-- [Insert `ext` and `copy` here]
```

Note that `A B` are marked as `outParam` even though they are not purely required to be so
due to the `FunLike` parameter already filling them in. This is required to see through
type synonyms, which is important in the category theory library. Also, it appears having them as
`outParam` is slightly faster.

The second step is to add instances of your new `MyHomClass` for all types extending `MyHom`.
Typically, you can just declare a new class analogous to `MyHomClass`:

```
structure CoolerHom (A B : Type*) [CoolClass A] [CoolClass B] extends MyHom A B where
  (map_cool' : toFun CoolClass.cool = CoolClass.cool)

class CoolerHomClass (F : Type*) (A B : outParam Type*) [CoolClass A] [CoolClass B]
  [FunLike F A B] extends MyHomClass F A B :=
    (map_cool : ∀ (f : F), f CoolClass.cool = CoolClass.cool)

@[simp] lemma map_cool {F A B : Type*} [CoolClass A] [CoolClass B] [FunLike F A B]
    [CoolerHomClass F A B] (f : F) : f CoolClass.cool = CoolClass.cool :=
  CoolerHomClass.map_cool _

variable {A B : Type*} [CoolClass A] [CoolClass B]

instance : FunLike (CoolerHom A B) A B where
  coe f := f.toFun
  coe_injective := fun f g h ↦ by cases f; cases g; congr; apply DFunLike.coe_injective; congr

instance : CoolerHomClass (CoolerHom A B) A B where
  map_op f := f.map_op'
  map_cool f := f.map_cool'

-- [Insert `ext` and `copy` here]
```

Then any declaration taking a specific type of morphisms as parameter can instead take the
class you just defined:
```
-- Compare with: lemma do_something (f : MyHom A B) : sorry := sorry
lemma do_something {F : Type*} [FunLike F A B] [MyHomClass F A B] (f : F) : sorry :=
  sorry
```

This means anything set up for `MyHom`s will automatically work for `CoolerHomClass`es,
and defining `CoolerHomClass` only takes a constant amount of effort,
instead of linearly increasing the work per `MyHom`-related declaration.

## Design rationale

The current form of FunLike was set up in pull request https://github.com/leanprover-community/mathlib4/pull/8386:
https://github.com/leanprover-community/mathlib4/pull/8386
We made `FunLike` *unbundled*: child classes don't extend `FunLike`, they take a `[FunLike F A B]`
parameter instead. This suits the instance synthesis algorithm better: it's easy to verify a type
does **not** have a `FunLike` instance by checking the discrimination tree once instead of searching
the entire `extends` hierarchy.
-/

@[expose] public section

/-- The class `DFunLike F α β` expresses that terms of type `F` have an
injective coercion to (dependent) functions from `α` to `β`.

For non-dependent functions you can also use the abbreviation `FunLike`.

This typeclass is used in the definition of the homomorphism typeclasses,
such as `ZeroHomClass`, `MulHomClass`, `MonoidHomClass`, ....
-/
@[notation_class* toFun Simps.findCoercionArgs]
class DFunLike (F : Sort*) (α : outParam (Sort*)) (β : outParam <| α → Sort*) where
  /-- The coercion from `F` to a function. -/
  coe : F → ∀ a : α, β a
  /-- The coercion to functions must be injective. -/
  coe_injective : Function.Injective coe

/-- The class `FunLike F α β` (`Fun`ction-`Like`) expresses that terms of type `F`
have an injective coercion to functions from `α` to `β`.
`FunLike` is the non-dependent version of `DFunLike`.
This typeclass is used in the definition of the homomorphism typeclasses,
such as `ZeroHomClass`, `MulHomClass`, `MonoidHomClass`, ....
-/
abbrev FunLike F α β := DFunLike F α fun _ => β

section Dependent

/-! ### `DFunLike F α β` where `β` depends on `a : α` -/

variable (F α : Sort*) (β : α → Sort*)

namespace DFunLike

variable {F α β} [i : DFunLike F α β]

@[deprecated (since := "2026-06-04")] alias coe_injective' := coe_injective

instance (priority := 100) toCoeFun : CoeFun F (fun _ ↦ ∀ a : α, β a) where
  coe := @DFunLike.coe _ _ β _ -- need to make explicit to beta reduce for non-dependent functions

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.Meta.registerCoercion ``DFunLike.coe
    (some { numArgs := 5, coercee := 4, type := .coeFun })

@[deprecated "Now a syntactic tautology" (since := "2026-06-04")]
theorem coe_eq_coe_fn : (DFunLike.coe (F := F)) = (fun f => ↑f) := rfl

@[simp]
theorem coe_fn_eq {f g : F} : (f : ∀ a : α, β a) = (g : ∀ a : α, β a) ↔ f = g :=
  ⟨fun h ↦ DFunLike.coe_injective h, fun h ↦ by cases h; rfl⟩

theorem ext' {f g : F} (h : (f : ∀ a : α, β a) = (g : ∀ a : α, β a)) : f = g :=
  DFunLike.coe_injective h

theorem ext'_iff {f g : F} : f = g ↔ (f : ∀ a : α, β a) = (g : ∀ a : α, β a) :=
  coe_fn_eq.symm

theorem ext (f g : F) (h : ∀ x : α, f x = g x) : f = g :=
  DFunLike.coe_injective (funext h)

theorem ext_iff {f g : F} : f = g ↔ ∀ x, f x = g x :=
  coe_fn_eq.symm.trans funext_iff

protected theorem congr_fun {f g : F} (h₁ : f = g) (x : α) : f x = g x :=
  congr_fun (congr_arg _ h₁) x

theorem ne_iff {f g : F} : f ≠ g ↔ ∃ a, f a ≠ g a :=
  ext_iff.not.trans not_forall

theorem exists_ne {f g : F} (h : f ≠ g) : ∃ x, f x ≠ g x :=
  ne_iff.mp h

/-- This is not an instance to avoid slowing down every single `Subsingleton` typeclass search. -/
lemma subsingleton_cod [∀ a, Subsingleton (β a)] : Subsingleton F :=
  coe_injective.subsingleton

include β in
/-- This is not an instance to avoid slowing down every single `Subsingleton` typeclass search. -/
lemma subsingleton_dom [IsEmpty α] : Subsingleton F :=
  coe_injective.subsingleton

end DFunLike

end Dependent

section NonDependent

/-! ### `FunLike F α β` where `β` does not depend on `a : α` -/

variable {F α β : Sort*} [i : FunLike F α β]

namespace DFunLike

protected theorem congr {f g : F} {x y : α} (h₁ : f = g) (h₂ : x = y) : f x = g y :=
  congr (congr_arg _ h₁) h₂

protected theorem congr_arg (f : F) {x y : α} (h₂ : x = y) : f x = f y :=
  congr_arg _ h₂

theorem dite_apply {P : Prop} [Decidable P] (f : P → F) (g : ¬P → F) (x : α) :
    (if h : P then f h else g h) x = if h : P then f h x else g h x := by
  split_ifs <;> rfl

theorem ite_apply {P : Prop} [Decidable P] (f g : F) (x : α) :
    (if P then f else g) x = if P then f x else g x :=
  dite_apply _ _ _

end DFunLike

end NonDependent
