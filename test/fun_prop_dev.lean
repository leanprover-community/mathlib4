/-
Copyright (c) 2024 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
import Mathlib.Tactic.FunProp
import Mathlib.Logic.Function.Basic
import Mathlib.Data.FunLike.Basic

/-! # Tests for the `fun_prop` tactic

This file is designed for development of fun_prop and does not depend on most of mathlib. It defines
two function properties `Con` and `Lin` which roughly correspond to `Continuity` and `IsLinearMap`.
-/

open Function

variable {α β γ δ ι : Type _} {E : α → Type _}

instance [Add α] : Add (ι → α) := ⟨fun f g i => f i + g i⟩

axiom silentSorry {α} : α
set_option linter.unusedVariables false

-- define function propositions --
----------------------------------

class Obj (α : Type _) : Type where

instance [Obj α] [Obj β] : Obj (α × β) := ⟨⟩
instance [∀ x, Obj (E x)] : Obj ((x' : α) → E x') := ⟨⟩
instance : Obj Nat := ⟨⟩

@[fun_prop] opaque Con {α β} [Obj α] [Obj β] (f : α → β) : Prop
@[fun_prop] opaque Lin {α β} [Obj α] [Obj β] (f : α → β) : Prop

-- state basic lambda calculus rules --
---------------------------------------

variable [Obj α] [Obj β] [Obj γ] [Obj δ] [∀ x, Obj (E x)]

@[fun_prop] theorem Con_id : Con (id : α → α) := silentSorry
@[fun_prop] theorem Con_const (y : β) : Con (fun x : α => y) := silentSorry
@[fun_prop] theorem Con_apply (x : α) : Con (fun f : α → β => f x) := silentSorry
@[fun_prop] theorem Con_applyDep (x : α) : Con (fun f : (x' : α) → E x' => f x) := silentSorry
@[fun_prop] theorem Con_comp (f : β → γ) (g : α → β) (hf : Con f) (hg : Con g) : Con (fun x => f (g x)) := silentSorry
@[fun_prop] theorem Con_let (f : α → β → γ) (g : α → β) (hf : Con (fun (x,y) => f x y)) (hg : Con g) : Con (fun x => let y:= g x; f x y) := silentSorry
@[fun_prop] theorem Con_pi (f : β → (i : α) → (E i)) (hf : ∀ i, Con (fun x => f x i)) : Con (fun x i => f x i) := silentSorry

-- Lin is missing `const` theorem
@[fun_prop] theorem Lin_id : Lin (fun x : α => x) := silentSorry
@[fun_prop] theorem Lin_apply (x : α) : Lin (fun f : α → β => f x) := silentSorry
@[fun_prop] theorem Lin_applyDep (x : α) : Lin (fun f : (x' : α) → E x' => f x) := silentSorry
@[fun_prop] theorem Lin_comp (f : β → γ) (g : α → β) (hf : Lin f) (hg : Lin g) : Lin (f ∘ g) := silentSorry
@[fun_prop] theorem Lin_pi {ι} (f : α → ι → γ) (hf : ∀ i, Lin (fun x => f x i)) : Lin (fun x i => f x i) := silentSorry


-- this is to stress test detection of loops
@[fun_prop]
theorem kaboom (f : α → β) (hf : Con f) : Con f := hf

-- currently only trivial loops are detected
-- make it more sophisticated such that longer loops are detected
-- @[fun_prop]
-- theorem chabam (f : α → β) (hf : Con f) : Con f := hf


-- transition theorem --
------------------------
@[fun_prop] theorem lin_to_con (f : α → β) (hf : Lin f) : Con f := silentSorry


-- theorems about function in the environment --
------------------------------------------------
@[fun_prop]
theorem prod_mk_Con (fst : α → β) (snd : α → γ) (hfst : Con fst) (hsnd : Con snd)
  : Con fun x => (fst x, snd x) := silentSorry
@[fun_prop]
theorem prod_mk_Lin (fst : α → β) (snd : α → γ) (hfst : Lin fst) (hsnd : Lin snd)
  : Lin fun x => (fst x, snd x) := silentSorry


variable [Add α] [Add β]

-- "simple form" of theorems
@[fun_prop] theorem fst_Con : Con fun x : α×β => x.1 := silentSorry
@[fun_prop] theorem snd_Con : Con fun x : α×β => x.2 := silentSorry
@[fun_prop] theorem add_Con : Con (Function.uncurry (fun x y : α => x + y)) := silentSorry
@[fun_prop] theorem add_Lin : Lin ↿(fun x y : α => x + y) := silentSorry


-- "compositional form" of theorems
@[fun_prop] theorem fst_Con' (self : α → β×γ) (hself : Con self) : Con fun x => (self x).1 := by fun_prop
@[fun_prop] theorem snd_Con' (self : α → β×γ) (hself : Con self) : Con fun x => (self x).2 := by fun_prop
@[fun_prop] theorem add_Con' (x y : α → β) (hx : Con x) (hy : Con y) : Con (fun w => x w + y w) := by fun_prop
@[fun_prop] theorem add_Lin' (x y : α → β) (hx : Lin x) (hy : Lin y) : Lin (fun w => x w + y w) := by fun_prop



-- set up hom objects/bundled morphisms --
------------------------------------------

structure ConHom (α β) [Obj α] [Obj β] where
  toFun : α → β
  con : Con toFun

infixr:25 " ->> " => ConHom

structure LinHom (α β) [Obj α] [Obj β] where
  toFun : α → β
  lin : Lin toFun

infixr:25 " -o " => LinHom

instance : CoeFun (α ->> β) (fun _ => α → β) where
  coe := fun f => f.toFun

instance : FunLike (α -o β) α β where
  coe := fun f => f.toFun
  coe_injective' := silentSorry

#eval Lean.Elab.Command.liftTermElabM do
  Lean.Meta.registerCoercion ``ConHom.toFun
    (some { numArgs := 5, coercee := 4, type := .coeFun })

instance : HasUncurry (α ->> β) α β :=
  ⟨fun f x => f x⟩
instance [HasUncurry β γ δ] : HasUncurry (α ->> β) (α × γ) δ :=
  ⟨fun f p ↦ (↿(f p.1)) p.2⟩

instance : HasUncurry (α -o β) α β :=
  ⟨fun f x => f x⟩
instance [HasUncurry β γ δ] : HasUncurry (α -o β) (α × γ) δ :=
  ⟨fun f p ↦ (↿(f p.1)) p.2⟩


instance : Obj (α ->> β) := ⟨⟩
instance : Obj (α -o β) := ⟨⟩

-- morphism theorems i.e. theorems about `FunLike.coe` --
---------------------------------------------------------

-- this is some form of cartesion closedness with homs `α ->> β`
@[fun_prop] theorem conHom_con' (f : α → β ->> γ) (g : α → β) (hf : Con f) (hg : Con g) : Con (fun x => (f x) (g x)) := silentSorry

@[fun_prop] theorem conHom_lin_in_fn' (f : α → β ->> γ) (y : β) (hf : Lin f) : Lin (fun x => f x y) := silentSorry

-- analogous theorem with `α -o β` does no hold
@[fun_prop] theorem linHom_lin (f : α -o β) : Lin f := silentSorry
@[fun_prop] theorem linHom_lin_in_fn' (f : α → β -o γ) (y : β) (hf : Lin f) : Lin (fun x => f x y) := silentSorry


def LinHom.mk' (f : α → β) (hf : Lin f := by fun_prop) : α -o β := mk f hf

@[fun_prop] theorem linHom_mk' (f : α → β → γ) (hx : ∀ y, Lin (f · y)) (hy : ∀ x, Lin (f x ·)) : Lin (fun x => LinHom.mk' (f x)) := silentSorry


section Notation
open Lean Syntax Parser
open TSyntax.Compat
macro "fun" xs:explicitBinders " ⊸ " b:term : term => expandExplicitBinders ``LinHom.mk' xs b
macro "fun" xs:explicitBinders " -o " b:term : term => expandExplicitBinders ``LinHom.mk' xs b
end Notation


example (f : α → β → γ) (hx : ∀ y, Lin (f · y)) (hy : ∀ x, Lin (f x ·)) :
  Lin (fun x => fun y ⊸ f y (x+x)) := by fun_prop

example (f : α → α → α → α) (hx : ∀ x y, Lin (f x y ·)) (hy : ∀ x z, Lin (f x · z)) (hz : ∀ y z, Lin (f · y z)) :
    Lin (fun x => fun y z ⊸ f z (x+x) y) := by fun_prop

-- the only analoge is this theorem but that is alredy provable
example (f : α → β -o γ) (g : α → β) (hf : Lin (fun (x,y) => f x y)) (hg : Lin g) : Lin (fun x => (f x) (g x)) := by fun_prop



----------------------------------------------------------------------------------------------------

example (f : α → β → γ) (hf : Con fun (x,y) => f x y) : Con f := by fun_prop

example : Con (fun x : α => x) := by fun_prop
example (y : β) : Con (fun _ : α => y) := by fun_prop
example (x : α) : Con (fun f : α → β => f x) := by fun_prop
example (x : α) : Con (fun f : (x' : α) → E x' => f x) := by fun_prop
example (x : α) (y : β) : Con (fun f : α → β → γ => f x y) := by fun_prop
example (x : α) (y : β) : Con (fun f : α → β → (x' : α) → E x' => f x y x) := by fun_prop
example (y : β) : Con (fun (f : α → β → (x' : α) → E x') x => f x y x) := by fun_prop
example : Con (fun (f : α → β → (x' : α) → E x') x y => f x y x) := by fun_prop

example (x : α) [Add α] : Con (let y := x + x; fun x' : α => x' + y) := by fun_prop

example (f : β → γ) (g : α → β) (hf : Con f) (hg : Con g) : Con (fun x => f (g x)) := by fun_prop
example (f : α → β → γ) (g : α → β) (hf : Con (fun (x,y) => f x y)) (hg : Con g) : Con (fun x => f x (g x)) := by fun_prop
example (f : α → β → γ) (g : α → β) (hf : Con (fun (x,y) => f x y)) (hg : Con g) : Con (fun x => let y := g x; f x y) := by fun_prop
example {ι} (f : α → ι → γ) (hf : ∀ i, Con (fun x => f x i)) : Con (fun x i => f x i) := by fun_prop

example : Con (fun (f : α → β → γ) x y => f x y) := by fun_prop
example : Con (fun (f : α → β → γ) y x => f x y) := by fun_prop
example : Con (fun (f : α → α → α → α → α) y x => f x y x y) := by fun_prop

-- set_option pp.notation false


-- local hypothesis are assumed to be always in fully applied form
-- so `(hf : Con f)` is not considered valid
-- is this valid assumption?
example (f : α → β → γ) (hf : Con f) : Con f := by fun_prop
example (f : α → β → γ) (hf : Con f) : Con (fun x => f x) := by fun_prop
example (f : α → β → γ) (hf : Con f) : Con (fun x y => f x y) := by fun_prop
example (f : α → β → γ) (hf : Con f) (y) : Con (fun x => f x y) := by fun_prop

example (f : α → β → γ) (hf : Con fun (x,y) => f x y) (x) : Con fun y => f x y := by fun_prop
example (f : α → β → γ) (hf : Con fun (x,y) => f x y) (y) : Con fun x => f x y := by fun_prop
example (f : α → β → γ) (hf : Con fun (x,y) => f x y)  : Con f := by fun_prop

example (f : α → β → γ) (hf : Con ↿f) (x : α) : Con fun y => f x y := by fun_prop
example (f : α → β → γ) (hf : Con ↿f) (y : β) : Con fun x => f x y := by fun_prop
example (f : α → β → γ) (hf : Con ↿f) : Con f := by fun_prop

example (f : α → β → γ) (hf : ∀ x, Con fun y => f x y) (x) : Con fun y => f x y := by fun_prop
example (f : α → β → γ) (hf : ∀ x, Con fun y => f x y) (x) : Con (f x) := by fun_prop
example (f : α → β → γ) (hf : ∀ y, Con fun x => f x y) (y) : Con fun x => f x y := by fun_prop
example (f : α → β → γ) (hf : ∀ y, Con fun x => f x y) : Con fun x => f x := by fun_prop

example (f : α → β → γ) (hf : Con fun (x,y) => f x y) (y) : Con fun x => f x y := by fun_prop
example (f : α → β → γ) (hf : Con fun (x,y) => f x y) : Con f := by fun_prop
example (f : α → α → β) (hf : Con fun (x,y) => f x y) : Con (fun x => f x x) := by fun_prop

example (f : α → β → γ → δ) (hf : ∀ x, Con fun (y,z) => f x y z) (x z) : Con (fun y => f x y z)  := by fun_prop
example (f : α → β → γ → δ) (hf : ∀ x, Con fun (y,z) => f x y z) (x y) : Con (fun z => f x y z)  := by fun_prop
example (f : α → β → γ → δ) (hf : ∀ x, Con fun (y,z) => f x y z) (x) : Con (fun z y => f x y z)  := by fun_prop
example (f : α → β → γ → δ) (hf : ∀ x, Con fun (y,z) => f x y z) (x y) : Con (f x y)  := by fun_prop
example (f : α → β → γ → δ) (hf : ∀ x, Con fun (y,z) => f x y z) (x) : Con (fun y => f x y)  := by fun_prop

example (f : α → Nat → Nat → β) (hf : ∀ i j, Con (f · i j)) : Con (fun x i j => f x (i+j) j)  := by fun_prop
example (f : α → Nat → Nat → β) (hf : ∀ i j, Con (f · i j)) (i j) : Con (fun x => f x (i+j) j)  := by fun_prop
example (f : α → Nat → Nat → β) (hf : Con f) : Con (fun x i j => f x (i+j) j)  := by fun_prop
example (f : α → Nat → Nat → β) (hf : Con f) (i j) : Con (fun x => f x (i+j) j)  := by fun_prop

example (f : α → β → γ → δ) (hf : ∀ y, Con fun (x,z) => f x y z) : Con f := by fun_prop
example (f : α → β → γ → δ) (hf : ∀ y, Con fun (x,z) => f x y z) : Con f := by fun_prop

example (f : α → β ->> γ) (hf : Con f) (y) : Con (fun x => f x y) := by fun_prop
example (f : α → β ->> γ) (hf : Con f) : Con (fun x y => f x y) := by fun_prop
example (f : α → β ->> γ) (hf : Con fun (x,y) => f x y) (y) : Con fun x => f x y := by fun_prop
example (f : α → β ->> γ) (hf : Con fun (x,y) => f x y) : Con fun x y => f x y := by fun_prop
example (f : α → β ->> γ) (hf : Con fun (x,y) => f x y) (x) : Con fun y => f x y := by fun_prop
example (f : α → α ->> (α → α)) (hf : Con fun (x,y,z) => f x y z) (x) : Con fun y => f x y := by fun_prop
example (f : α → α ->> (α → α)) (hf : Con fun (x,y,z) => f x y z) : Con fun x y => f y x x := by fun_prop

example (f : α → β ->> γ) (hf : Con ↿f) (y) : Con fun x => f x y := by fun_prop
example (f : α → β ->> γ) (x) : Con fun y : β => f x := by fun_prop
example (f : α → β ->> γ) (x) : Con fun y : β => (f x : β → γ) := by fun_prop
example (f : α → β ->> γ) (x) : Con fun y => f x y := by fun_prop
example (f : α → α ->> (α → α)) (x) : Con fun y => f x y := by fun_prop
example (f : α → α ->> (α → α)) (hf : Con ↿f) : Con fun x y => f y x x := by fun_prop


example (f : α → β ->> γ) (hf : Con f) : Con ↿f := by fun_prop

example : Con (HAdd.hAdd : α → α → α) := by fun_prop  -- under applied constant
example : Con (fun x => (HAdd.hAdd : α → α → α) x) := by fun_prop  -- under applied constant

example : Con (fun x => (HAdd.hAdd : ((ι→α) → (ι→α) → (ι→α))) x) := by fun_prop
example : Con (fun x y => (HAdd.hAdd : ((ι→α) → (ι→α) → (ι→α))) x y) := by fun_prop
example : Con (fun x y i => (HAdd.hAdd : ((ι→α) → (ι→α) → (ι→α))) x y i) := by fun_prop
example (y) : Con (fun x i => (HAdd.hAdd : ((ι→α) → (ι→α) → (ι→α))) x y i) := by fun_prop
example (y i) : Con (fun x => (HAdd.hAdd : ((ι→α) → (ι→α) → (ι→α))) x y i) := by fun_prop

-- example (f : β → γ) (x) (hf : Lin f)  : Lin (fun (g : α → β) => f (g x)) := by fun_prop


-- apply theorems about FunLike.coe
example (f : α ->> β) : Con f := by fun_prop
example (f : α -o β) : Con f := by fun_prop
example (f : α → β) (hf : Lin f) : Con f := by fun_prop
example (f : β → γ) (g : α ->> β) (hf: Con f) : Con (fun x => f (g x)) := by fun_prop
example (f : β ->> γ) (g : α → β) (hg: Con g) : Con (fun x => f (g x)) := by fun_prop
example (f : β -o γ) (g : α → β) (hg : Con g) : Con fun x => f (g x) := by fun_prop

-- set_option trace.Meta.Tactic.fun_prop true in
example (f : α → β ->> γ) (hf : Con f) (g : α → β) (hg : Lin g)  : Con (fun x => f x (g x)) := by fun_prop
example (f : α → β ->> γ) (hf : Lin (fun (x,y) => f x y)) (g : α → β) (hg : Lin g)  : Con (fun x => f x (g x)) := by fun_prop
example (f : α → β ->> γ) (hf : Lin (fun (x,y) => f x y)) (g : α → β) (hg : Lin g)  : Lin (fun x => f x (g x)) := by fun_prop

-- remove arguments before applying morphism rules
example (f : α ->> (β → γ)) (y) : Con (fun x => f x y) := by fun_prop


example (g : α → β) (hg : Con g) : Con fun (fx : (β ->> γ)×α) => fx.1 (g fx.2) := by fun_prop


-- sometimes unfold constants
example (f : α → β) (hf : Con f) : Con (fun x => id f x) := by fun_prop
example (f : α → β) (hf : Con f) : Con (fun x => (id id) f x) := by fun_prop
example (f : α → α → α) (hf : Con (fun (x,y) => f x y)) : Con (fun x => id (id f x) x) := by fun_prop
example (f : α → α → α) (hf : Con (fun (x,y) => f x y)) : Con (fun x => (id id) ((id id) f x) x) := by fun_prop
example (f : α → α → α) (hf : Con (fun (x,y) => f x y)) : Con (fun x : α×α => id (f x.1) x.2) := by fun_prop

-- this used to time out
example (f : α → β -o γ) (hf : Lin (fun (x,y) => f x y)) (g : α → β) (hg : Lin g)  : Lin (fun x => f x (g x)) := by fun_prop


example : Con fun (a : α ->> α) => a x := by fun_prop

-- this used to crash
example (f : α → (α ->> α)) (hf : Con f) : Con fun x => ((f x) : α → α) := by fun_prop
example : Con (fun f : (α ->> α ->> α) => (f x : α → α)) := by fun_prop


example : Lin (fun f : (α ->> α ->> α) => (f x : α → α)) := by fun_prop
example (y): Lin (fun f : (α ->> α ->> α) => f x y) := by fun_prop
example : Lin (fun f : (α -o α ->> α) => (f x : α → α)) := by fun_prop
example (y): Lin (fun f : (α ->> α -o α) => f x y) := by fun_prop


example (f : α -o α ->> α) (y) : Lin (fun x  => f x y) := by fun_prop
example (f : α ->> α -o α ->> α) (y) : Lin (fun x  => f y x y) := by fun_prop

example (x) : Con fun (f : α ->> α) => f (f x) := by fun_prop
example (x) : Con fun (f : α ->> α) => f (f (f x)) := by fun_prop


noncomputable
def foo : α ->> α ->> α := silentSorry
noncomputable
def bar : α ->> α ->> α := silentSorry

@[fun_prop]
theorem foo_lin : Lin fun x : α => foo x := silentSorry
@[fun_prop]
theorem bar_lin (y) : Lin fun x : α => bar x y := silentSorry

example : Lin (foo : α → α ->> α) := by fun_prop
example : Con (foo : α → α ->> α) := by fun_prop
example : Lin (fun x : α => (foo x : α → α)) := by fun_prop
example : Lin (fun x y : α => foo x y) := by fun_prop
example (y) : Lin (fun x : α => foo x y) := by fun_prop

example : Lin (fun x : α => (bar x : α → α)) := by fun_prop
example : Lin (fun x y : α => bar x y) := by fun_prop
example (y) : Lin (fun x : α => bar x y) := by fun_prop

example : Lin (fun (f : α ->> α) => (f : α → α)) := by fun_prop
example : Con (fun (f : α ->> α) => (f : α → α)) := by fun_prop
example : Lin (fun (f : α -o α) => (f : α → α)) := by fun_prop

example : Con (fun fx : (α ->> β)×α => fx.1 fx.2) := by fun_prop


def iterate (n : Nat) (f : α → α) (x : α) : α :=
  match n with
  | 0 => x
  | n+1 => iterate n f (f x)

theorem iterate_con (n : Nat) (f : α → α) (hf : Con f) : Con (iterate n f) := by
  induction n <;> (simp [iterate]; fun_prop)


example : let f := fun x : α => x; Con f := by fun_prop


example (f g : α → β) (hf : Con f := by fun_prop) (hg : outParam (Con g)) :
  Con (fun x => f x + g x) := by fun_prop


opaque foo1 : α → α := id
opaque foo2 : α → α := id

@[fun_prop]
theorem foo1_lin : Lin (foo1 : α → α) := silentSorry
@[fun_prop]
theorem foo2_lin : Lin (foo2 : α → α) := silentSorry

example : Con (fun x : α => foo1 (foo2 x)) := by fun_prop


def foo3 (x : α) := x + x
example : Con (fun x : α => foo3 x) := by fun_prop [foo3]

def myUncurry (f : α → β → γ) : α×β → γ := fun (x,y) => f x y
def diag (f : α → α → α) (x : α) := f x x

theorem diag_Con (f : α → α → α) (hf : Con (myUncurry f)) : Con (fun x => diag f x) := by
  fun_prop [diag,myUncurry]
