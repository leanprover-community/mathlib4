/-
Copyright (c) 2024 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
import Mathlib.Tactic.FunProp
import Mathlib.Logic.Function.Basic
import Mathlib.Data.FunLike.Basic
import Mathlib.Tactic.SuccessIfFailWithMsg
import Aesop

/-! # Tests for the `fun_prop` tactic

This file is designed for development of fun_prop and does not depend on most of mathlib. It defines
two function properties `Con` and `Lin` which roughly correspond to `Continuity` and `IsLinearMap`.
-/

set_option linter.style.longLine false

open Function

variable {α β γ δ ι : Type _} {E : α → Type _}

instance [Add α] : Add (ι → α) := ⟨fun f g i => f i + g i⟩

axiom silentSorry {α} : α
set_option linter.unusedVariables false

-- define function propositions --
----------------------------------

@[fun_prop] opaque Con {α β} (f : α → β) : Prop
@[fun_prop] opaque Lin {α β} (f : α → β) : Prop

-- state basic lambda calculus rules --
---------------------------------------

-- variable [Obj α] [Obj β] [Obj γ] [Obj δ] [∀ x, Obj (E x)]

@[fun_prop] theorem Con_id : Con (id : α → α) := silentSorry
@[fun_prop] theorem Con_const (y : β) : Con (fun x : α => y) := silentSorry
@[fun_prop] theorem Con_apply (x : α) : Con (fun f : α → β => f x) := silentSorry
@[fun_prop] theorem Con_applyDep (x : α) : Con (fun f : (x' : α) → E x' => f x) := silentSorry
@[fun_prop] theorem Con_comp (f : β → γ) (g : α → β) (hf : Con f) (hg : Con g) : Con (fun x => f (g x)) := silentSorry
-- @[fun_prop] theorem Con_let (f : α → β → γ) (g : α → β) (hf : Con (fun (x,y) => f x y)) (hg : Con g) : Con (fun x => let y:= g x; f x y) := silentSorry
@[fun_prop] theorem Con_pi (f : β → (i : α) → (E i)) (hf : ∀ i, Con (fun x => f x i)) : Con (fun x i => f x i) := silentSorry

-- Lin is missing `const` theorem
@[fun_prop] theorem Lin_id : Lin (fun x : α => x) := silentSorry
@[fun_prop] theorem Lin_const {β} [Zero β] : Lin (fun x : α => (0 : β)) := silentSorry
@[fun_prop] theorem Lin_apply (x : α) : Lin (fun f : α → β => f x) := silentSorry
@[fun_prop] theorem Lin_applyDep (x : α) : Lin (fun f : (x' : α) → E x' => f x) := silentSorry
@[fun_prop] theorem Lin_comp (f : β → γ) (g : α → β) (hf : Lin f) (hg : Lin g) : Lin (f ∘ g) := silentSorry
@[fun_prop] theorem Lin_pi {ι} (f : α → ι → γ) (hf : ∀ i, Lin (fun x => f x i)) : Lin (fun x i => f x i) := silentSorry


-- this is to stress test detection of loops
@[fun_prop]
theorem kaboom (f : α → β) (hf : Con f) : Con f := hf
@[fun_prop]
theorem chabam (f : α → β) (hf : Con f) : Con f := hf


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



-- "simple form" of theorems
@[fun_prop] theorem fst_Con : Con fun x : α×β => x.1 := silentSorry
@[fun_prop] theorem snd_Con : Con fun x : α×β => x.2 := silentSorry
@[fun_prop] theorem add_Con [Add α] : Con (Function.uncurry (fun x y : α => x + y)) := silentSorry
@[fun_prop] theorem add_Lin [Add α] : Lin ↿(fun x y : α => x + y) := silentSorry


-- "compositional form" of theorems
@[fun_prop] theorem fst_Con' (self : α → β×γ) (hself : Con self) : Con fun x => (self x).1 := by fun_prop
@[fun_prop] theorem snd_Con' (self : α → β×γ) (hself : Con self) : Con fun x => (self x).2 := by fun_prop
@[fun_prop] theorem add_Con' [Add β] (x y : α → β) (hx : Con x) (hy : Con y) : Con (fun w => x w + y w) := by fun_prop
@[fun_prop] theorem add_Lin' [Add β] (x y : α → β) (hx : Lin x) (hy : Lin y) : Lin (fun w => x w + y w) := by fun_prop



-- set up hom objects/bundled morphisms --
------------------------------------------

structure ConHom (α β) where
  toFun : α → β
  con : Con toFun

infixr:25 " ->> " => ConHom

structure LinHom (α β) where
  toFun : α → β
  lin : Lin toFun

infixr:25 " -o " => LinHom

instance : CoeFun (α ->> β) (fun _ => α → β) where
  coe f := f.toFun

instance : FunLike (α -o β) α β where
  coe f := f.toFun
  coe_injective' := silentSorry

#eval Lean.Elab.Command.liftTermElabM do
  Lean.Meta.registerCoercion ``ConHom.toFun
    (some { numArgs := 3, coercee := 2, type := .coeFun })

instance : HasUncurry (α ->> β) α β :=
  ⟨fun f x => f x⟩
instance [HasUncurry β γ δ] : HasUncurry (α ->> β) (α × γ) δ :=
  ⟨fun f p ↦ ↿(f p.1) p.2⟩

instance : HasUncurry (α -o β) α β :=
  ⟨fun f x => f x⟩
instance [HasUncurry β γ δ] : HasUncurry (α -o β) (α × γ) δ :=
  ⟨fun f p ↦ ↿(f p.1) p.2⟩


-- morphism theorems i.e. theorems about `FunLike.coe` --
---------------------------------------------------------

-- this is some form of Cartesian closedness with homs `α ->> β`
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


example [Add β] (f : α → β → γ) (hx : ∀ y, Lin (f · y)) (hy : ∀ x, Lin (f x ·)) :
  Lin (fun x => fun y ⊸ f y (x+x)) := by fun_prop

example [Add α] (f : α → α → α → α) (hx : ∀ x y, Lin (f x y ·)) (hy : ∀ x z, Lin (f x · z)) (hz : ∀ y z, Lin (f · y z)) :
    Lin (fun x => fun y z ⊸ f z (x+x) y) := by fun_prop

-- the only analogue is this theorem but that is already provable
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
example {ι : Type _} (f : α → ι → γ) (hf : ∀ i, Con (fun x => f x i)) : Con (fun x i => f x i) := by fun_prop

example : Con (fun (f : α → β → γ) x y => f x y) := by fun_prop
example : Con (fun (f : α → β → γ) y x => f x y) := by fun_prop
example : Con (fun (f : α → α → α → α → α) y x => f x y x y) := by fun_prop

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
example (f : α → α ->> (α → α)) (y : α) (hf : Con fun (x,y,z) => f x y z) : Con fun x => f y x x := by fun_prop
example (f : α → α ->> (α → α)) (hf : Con fun (x,y,z) => f x y z) : Con fun x y => f y x x := by fun_prop

example (f : α → β ->> γ) (hf : Con ↿f) (y) : Con fun x => f x y := by fun_prop
example (f : α → β ->> γ) (x) : Con fun y : β => f x := by fun_prop
example (f : α → β ->> γ) (x) : Con fun y : β => (f x : β → γ) := by fun_prop
example (f : α → β ->> γ) (x) : Con fun y => f x y := by fun_prop
example (f : α → α ->> (α → α)) (x) : Con fun y => f x y := by fun_prop
example (f : α → α ->> (α → α)) (hf : Con ↿f) : Con fun x y => f y x x := by fun_prop


example (f : α → β ->> γ) (hf : Con f) : Con ↿f := by fun_prop

section WithAdd
variable [Add α]

example : Con (HAdd.hAdd : α → α → α) := by fun_prop  -- under applied constant
example : Con (fun x => (HAdd.hAdd : α → α → α) x) := by fun_prop  -- under applied constant

example : Con (fun x => (HAdd.hAdd : ((ι→α) → (ι→α) → (ι→α))) x) := by fun_prop
example : Con (fun x y => (HAdd.hAdd : ((ι→α) → (ι→α) → (ι→α))) x y) := by fun_prop
example : Con (fun x y i => (HAdd.hAdd : ((ι→α) → (ι→α) → (ι→α))) x y i) := by fun_prop
example (y) : Con (fun x i => (HAdd.hAdd : ((ι→α) → (ι→α) → (ι→α))) x y i) := by fun_prop
example (y i) : Con (fun x => (HAdd.hAdd : ((ι→α) → (ι→α) → (ι→α))) x y i) := by fun_prop

end WithAdd

example (f : β → γ) (x) (hf : Lin f)  : Lin (fun (g : α → β) => f (g x)) := by fun_prop

-- apply theorems about FunLike.coe
example (f : α ->> β) : Con f := by fun_prop
example (f : α -o β) : Con f := by fun_prop
example (f : α → β) (hf : Lin f) : Con f := by fun_prop
example (f : β → γ) (g : α ->> β) (hf: Con f) : Con (fun x => f (g x)) := by fun_prop
example (f : β ->> γ) (g : α → β) (hg: Con g) : Con (fun x => f (g x)) := by fun_prop
example (f : β -o γ) (g : α → β) (hg : Con g) : Con fun x => f (g x) := by fun_prop

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


example (f : α -o α ->> α) (y) : Lin (fun x => f x y) := by fun_prop
example (f : α ->> α -o α ->> α) (y) : Lin (fun x => f y x y) := by fun_prop

example (x) : Con fun (f : α ->> α) => f (f x) := by fun_prop
example (x) : Con fun (f : α ->> α) => f (f (f x)) := by fun_prop


example [Zero α] [Add α] : Lin (fun x : α => (0 : α) + x + (0 : α) + (0 : α) + x) := by fun_prop

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
  | n + 1 => iterate n f (f x)

theorem iterate_con (n : Nat) (f : α → α) (hf : Con f) : Con (iterate n f) := by
  induction n <;> (simp [iterate]; fun_prop)


example : let f := fun x : α => x; Con f := by fun_prop
example [Add α] : let f := fun x => x + y; ∀ y : α, ∀ z : α, Con fun x => x + f x + z := by fun_prop
example [Add α] : ∀ y : α, let f := fun x => x + y; ∀ z : α, Con fun x => x + f x + z := by fun_prop
-- this is still broken
-- example : ∀ y : α, ∀ z : α, let f := fun x => x + y; Con fun x => x + f x + z := by fun_prop

example [Add β] (f g : α → β) (hf : Con f := by fun_prop) (hg : outParam (Con g)) :
  Con (fun x => f x + g x) := by fun_prop

opaque foo1 : α → α := id
opaque foo2 : α → α := id

@[fun_prop]
theorem foo1_lin : Lin (foo1 : α → α) := silentSorry
@[fun_prop]
theorem foo2_lin : Lin (foo2 : α → α) := silentSorry

example : Con (fun x : α => foo1 (foo2 x)) := by fun_prop


def foo3 [Add α] (x : α) := x + x
example [Add α] : Con (fun x : α => foo3 x) := by fun_prop [foo3]

def myUncurry (f : α → β → γ) : α×β → γ := fun (x,y) => f x y
def diag (f : α → α → α) (x : α) := f x x

theorem diag_Con (f : α → α → α) (hf : Con (myUncurry f)) : Con (fun x => diag f x) := by
  fun_prop [diag,myUncurry]
namespace MultipleLambdaTheorems

opaque A : Prop
opaque B : Prop
@[local fun_prop] theorem Con_comp' (f : β → γ) (g : α → β) (h : A) : Con (fun x => f (g x)) := silentSorry
@[local fun_prop] theorem Con_comp'' (f : β → γ) (g : α → β) (b : B) : Con (fun x => f (g x)) := silentSorry

example (f : β → γ) (g : α → β) (h : A) : Con (fun x => f (g x)) := by fun_prop (disch := assumption)
example (f : β → γ) (g : α → β) (h : B) : Con (fun x => f (g x)) := by fun_prop (disch := assumption)

end MultipleLambdaTheorems


/-- info: `?m` is not a `fun_prop` goal! -/
#guard_msgs in
#check_failure ((by fun_prop) : ?m)

-- todo: warning should not have mvar id in it
-- /-- warning: `?m.71721` is not a `fun_prop` goal! -/
-- #guard_msgs in
-- #check_failure (by exact add_Con' (by fun_prop) : Con (fun x : α => (x + x) + (x + x)))

example : Con fun ((x, _, _) : α × α × α) => x := by fun_prop
example : Con fun ((_, x, _) : α × α × α) => x := by fun_prop
example : Con fun ((_, _, x) : α × α × α) => x := by fun_prop

example [Add α] : let f := (by exact (fun x : α => x+x)); Con f := by
  intro f;
  let F := fun x : α => x+x
  have : Con F := by fun_prop -- this used to be problematic
  fun_prop


def f1 (a : α) := a
def f2 (a : α) := a

/--
error: `fun_prop` was unable to prove `Con fun x => x + f1 x`

Issues:
  No theorems found for `f1` in order to prove `Con fun a => f1 a`
-/
#guard_msgs in
example [Add α] : Con (fun x : α => x + f1 x) := by fun_prop

/--
error: `fun_prop` was unable to prove `Con fun x => f1 x + f1 x`

Issues:
  No theorems found for `f1` in order to prove `Con fun a => f1 a`
-/
#guard_msgs in
example [Add α] : Con (fun x : α => f1 x + f1 x) := by fun_prop

/--
error: `fun_prop` was unable to prove `Con fun x => f2 x + f1 x`

Issues:
  No theorems found for `f2` in order to prove `Con fun a => f2 a`
-/
#guard_msgs in
example [Add α] : Con (fun x : α => f2 x + f1 x) := by fun_prop


def f3 (a : α) := a

@[fun_prop]
theorem f3_lin : Lin (fun x : α => f3 x) := by
  unfold f3; fun_prop (maxTransitionDepth := 0) (maxSteps := 10)

example : Con (fun x : α => f3 x) := by fun_prop

/--
error: `fun_prop` was unable to prove `Con fun x => f3 x`

Issues:
  No theorems found for `f3` in order to prove `Con fun x => f3 x`
-/
#guard_msgs in
example : Con (fun x : α => f3 x) := by fun_prop (maxTransitionDepth := 0)

@[fun_prop] opaque Dif (𝕜:Type) [Add 𝕜] {α β} (f : α → β) : Prop

variable {𝕜 : Type}
@[fun_prop] theorem Dif_id [Add 𝕜] : Dif 𝕜 (id : α → α) := silentSorry
@[fun_prop] theorem Dif_const [Add 𝕜] (y : β) : Dif 𝕜 (fun x : α => y) := silentSorry
@[fun_prop] theorem Dif_apply [Add 𝕜] (x : α) : Dif 𝕜 (fun f : α → β => f x) := silentSorry
@[fun_prop] theorem Dif_applyDep [Add 𝕜] (x : α) : Dif 𝕜 (fun f : (x' : α) → E x' => f x) := silentSorry
@[fun_prop] theorem Dif_comp [Add 𝕜] (f : β → γ) (g : α → β) (hf : Dif 𝕜 f) (hg : Dif 𝕜 g) : Dif 𝕜 (fun x => f (g x)) := silentSorry
@[fun_prop] theorem Dif_pi [Add 𝕜] (f : β → (i : α) → (E i)) (hf : ∀ i, Dif 𝕜 (fun x => f x i)) : Dif 𝕜 (fun x i => f x i) := silentSorry

@[fun_prop]
theorem Dif_Con [Add 𝕜] (f : α → β) (hf : Dif 𝕜 f) : Con f := silentSorry

def f4 (a : α) := a

example (hf : Dif Nat (f4 : α → α)) : Con (f4 : α → α) := by fun_prop (disch:=aesop)

@[fun_prop]
theorem f4_dif : Dif Nat (f4 : α → α) := silentSorry

example (hf : Dif Nat (f4 : α → α)) : Con (f4 : α → α) := by fun_prop (disch:=aesop)


-- Test abbrev transparency
abbrev my_id {α} (a : α) := a
example : Con (fun x : α => my_id x) := by fun_prop
example (f : α → β) (hf : Con (my_id f)) : Con f := by fun_prop

-- Testing some issues with bundled morphisms of multiple arguments
structure Mor where
  toFun : Int → Int → Int
  hcon : Con (fun (x,y) => toFun x y)

@[fun_prop]
theorem Mor.toFun_Con (m : Mor) (f g : α → Int) (hf : Con f) (g : α → Int) (hg : Con g) :
    Con (fun x => m.toFun (f x) (g x)) := by
  have := m.hcon
  fun_prop

-- Test improved beta reduction of the head function when we interleave lambdas and lets
example [Add α] (a : α) : Con (fun x0 : α =>
  (fun x =>
    let y := x + x
    fun z : α =>
      x + y + z) x0 a) := by fun_prop

example [Add α] (a : α) :
  let f := (fun x : α =>
    let y := x + x
    fun z : α =>
      x + y + z)
  Con (fun x => f x a) := by fun_prop

example [Add α] (a a' : α) : Con (fun x0 : α =>
  (fun x =>
    let y := x + x
    fun z : α =>
      let h := x + y + z
      fun w =>
        w + x + y + z + h) x0 a a') := by fun_prop


-- test that local function is being properly unfolded
example [Add α] (a : α) :
  let f := (fun x : α =>
    let y := x + x
    fun z : α =>
      x + y + z)
  Con (fun x =>
    f x a) := by
  fun_prop


-- Test that local theorem is being used
/--
trace: [Meta.Tactic.fun_prop] [✅️] Con fun x => f x y
  [Meta.Tactic.fun_prop] [✅️] Con fun x => f x y
    [Meta.Tactic.fun_prop] candidate local theorems for f #[this : Con f]
    [Meta.Tactic.fun_prop] removing argument to later use this : Con f
    [Meta.Tactic.fun_prop] [✅️] applying: Con_comp
      [Meta.Tactic.fun_prop] [✅️] Con fun f => f y
        [Meta.Tactic.fun_prop] [✅️] applying: Con_apply
      [Meta.Tactic.fun_prop] [✅️] Con fun x => f x
        [Meta.Tactic.fun_prop] candidate local theorems for f #[this : Con f]
        [Meta.Tactic.fun_prop] [✅️] applying: this : Con f
-/
#guard_msgs in
example [Add α] (y : α):
  let f := (fun x y : α => x+x+y)
  Con (fun x => f x y) := by
  intro f
  have : Con f := by fun_prop
  set_option trace.Meta.Tactic.fun_prop true in
  fun_prop



--- pefromance tests - mainly testing fast failure ---
------------------------------------------------------


section PerformanceTests
-- set_option trace.Meta.Tactic.fun_prop true
-- set_option profiler true

variable {R : Type*} [Add R] [∀ n, OfNat R n]
example (f : R → R) (hf : Con f) :
    Con (fun x ↦ f (x + 3)) := by fun_prop -- succeeds in 5ms
example (f : R → R) (hf : Con f) :
    Con (fun x ↦ (f (x + 3)) + 2) := by fun_prop -- succeeds in 6ms
example (f : R → R) (hf : Con f) :
    Con (fun x ↦ (f (x + 3)) + (2 + f (x + 1))) := by fun_prop -- succeeds in 8ms
example (f : R → R) (hf : Con f) :
    Con (fun x ↦ (f (x + 3)) + (2 + f (x + 1)) + x) := by fun_prop -- succeeds in 10ms
example (f : R → R) (hf : Con f) :
    Con (fun x ↦ (f (x + 3)) + 2 + f (x + 1) + x + 1) := by fun_prop -- succeeds in 11ms

-- This used to fail in exponentially increasing time, up to 6s for the last example
-- We set maxHearthbeats to 1000 such that the last three examples should fail if the exponential
-- blow happen again.
set_option maxHeartbeats 1000 in
example (f : R → R) :
    Con (fun x ↦ f (x + 3)) := by
  fail_if_success fun_prop
  apply silentSorry

example (f : R → R) :
    Con (fun x ↦ (f (x + 3)) + 2) := by
  fail_if_success fun_prop
  apply silentSorry

set_option maxHeartbeats 1000 in
example (f : R → R) :
    Con (fun x ↦ ((f (x + 3)) + 2) + f (x + 1)) := by
  fail_if_success fun_prop
  apply silentSorry

set_option maxHeartbeats 1000 in
example (f : R → R) :
    Con (fun x ↦ ((f (x + 3)) + 2) + f (x + 1) + x) := by
  fail_if_success fun_prop
  apply silentSorry

set_option maxHeartbeats 1000 in
example (f : R → R) :
    Con (fun x ↦ ((f (x + 3)) + 2) + f (x + 1) + x + 1) := by
  fail_if_success fun_prop
  apply silentSorry

end PerformanceTests


/--
info: Con
  add_Con, args: [4, 5], form: simple
  add_Con', args: [4, 5], form: compositional
-/
#guard_msgs in
#print_fun_prop_theorems HAdd.hAdd Con


def fst (x : α×β) := x.1
def snd (x : α×β) := x.2

-- make sure that `fun_prop` can't see through `fst` and `snd`
example (f : α → β → γ) (hf : Con ↿f) : Con (fun x : α×β => f (fst x) (snd x)) := by
  fail_if_success fun_prop
  apply silentSorry
