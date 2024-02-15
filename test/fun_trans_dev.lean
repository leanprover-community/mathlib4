/-
Copyright (c) 2024 Tomáš Skřivan All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FunTrans.Attr
import Mathlib.Tactic.FunTrans.Elab

/-! # Tests for the `fun_trans` tactic

This file is designed for development of fun_trans and does not depend on most of mathlib. It defines
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


@[fun_prop] opaque Con {α β} [Obj α] [Obj β] (f : α → β) : Prop
@[fun_prop] opaque ConAt {α β} [Obj α] [Obj β] (f : α → β) (a : α) : Prop
@[fun_prop] opaque Lin {α β} [Obj α] [Obj β] (f : α → β) : Prop


-- state basic lambda calculus rules --
---------------------------------------

variable [Obj α] [Obj β] [Obj γ] [Obj δ] [∀ x, Obj (E x)]

@[fun_prop] theorem Con_id : Con (fun x : α => x) := silentSorry
@[fun_prop] theorem Con_const (y : β) : Con (fun x : α => y) := silentSorry
@[fun_prop] theorem Con_apply (x : α) : Con (fun f : α → β => f x) := silentSorry
@[fun_prop] theorem Con_applyDep (x : α) : Con (fun f : (x' : α) → E x' => f x) := silentSorry
@[fun_prop] theorem Con_comp (f : β → γ) (g : α → β) (hf : Con f) (hg : Con g) : Con (fun x => f (g x)) := silentSorry
@[fun_prop] theorem Con_pi (f : β → (i : α) → (E i)) (hf : ∀ i, Con (fun x => f x i)) : Con (fun x i => f x i) := silentSorry


@[fun_prop] theorem ConAt_id (x) : ConAt (fun x : α => x) x := silentSorry
@[fun_prop] theorem ConAt_ConAtst (x) (y : β) : ConAt (fun x : α => y) x := silentSorry
@[fun_prop] theorem ConAt_apply (f) (x : α) : ConAt (fun f : α → β => f x) f := silentSorry
@[fun_prop] theorem ConAt_applyDep (f) (x : α) : ConAt (fun f : (x' : α) → E x' => f x) f := silentSorry
@[fun_prop] theorem ConAt_comp (f : β → γ) (g : α → β) (x : α) (hf : ConAt f (g x)) (hg : ConAt g x) : ConAt (fun x => f (g x)) x := silentSorry
@[fun_prop] theorem ConAt_pi (f : β → (i : α) → (E i)) (x) (hf : ∀ i, ConAt (fun x => f x i) x) : ConAt (fun x i => f x i) x := silentSorry


-- Lin is missing `const` theorem
@[fun_prop] theorem Lin_id : Lin (fun x : α => x) := silentSorry
@[fun_prop] theorem Lin_apply (x : α) : Lin (fun f : α → β => f x) := silentSorry
@[fun_prop] theorem Lin_applyDep (x : α) : Lin (fun f : (x' : α) → E x' => f x) := silentSorry
@[fun_prop] theorem Lin_comp (f : β → γ) (g : α → β) (hf : Lin f) (hg : Lin g) : Lin (fun x => f (g x)) := silentSorry
@[fun_prop] theorem Lin_pi {ι} (f : α → ι → γ) (hf : ∀ i, Lin (fun x => f x i)) : Lin (fun x i => f x i) := silentSorry



-- transition theorem --
------------------------
@[fun_prop] theorem lin_to_con (f : α → β) (hf : Lin f) : Con f := silentSorry
@[fun_prop] theorem con_to_conAt (f : α → β) (x) (hf : Con f) : ConAt f x := silentSorry


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
@[fun_prop] theorem add_Con : Con (fun x : α×α => x.1 + x.2) := silentSorry


-- "compositional form" of theorems
@[fun_prop] theorem fst_Con' (self : α → β×γ) (hself : Con self) : Con fun x => (self x).1 := by fun_prop
@[fun_prop] theorem snd_Con' (self : α → β×γ) (hself : Con self) : Con fun x => (self x).2 := by fun_prop
@[fun_prop] theorem add_Con' (x y : α → β) (hx : Con x) (hy : Con y) : Con (fun w => x w + y w) := by fun_prop



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

instance : FunLike (α ->> β) α β where
  coe := fun f => f.toFun
  coe_injective' := silentSorry

instance : FunLike (α -o β) α β where
  coe := fun f => f.toFun
  coe_injective' := silentSorry


instance : HasUncurry (α ->> β) α β :=
  ⟨fun f x => f x⟩
instance [Obj β] [HasUncurry β γ δ] : HasUncurry (α ->> β) (α × γ) δ :=
  ⟨fun f p ↦ (↿(f p.1)) p.2⟩

instance : HasUncurry (α -o β) α β :=
  ⟨fun f x => f x⟩
instance [Obj β] [HasUncurry β γ δ] : HasUncurry (α -o β) (α × γ) δ :=
  ⟨fun f p ↦ (↿(f p.1)) p.2⟩


instance : Obj (α ->> β) := ⟨⟩
instance : Obj (α -o β) := ⟨⟩


-- morphism theorems i.e. theorems about `FunLike.coe` --
---------------------------------------------------------

-- this is some form of cartesion closedness with homs `α ->> β`
@[fun_prop] theorem conHom_con' (f : α → β ->> γ) (g : α → β) (hf : Con f) (hg : Con g) : Con (fun x => (f x) (g x)) := silentSorry

-- analogous theorem with `α -o β` does no hold
@[fun_prop] theorem linHom_lin (f : α -o β) : Lin f := silentSorry

set_option pp.coercions false in
set_option pp.notation false in
-- the only analoge is this theorem but that is alredy provable
example (f : α → β -o γ) (g : α → β) (hf : Lin (fun (x,y) => f x y)) (hg : Lin g) : Lin (fun x => (f x) (g x)) := by fun_prop



----------------------------------------------------------------------------------------------------
-- derivative


@[fun_trans]
opaque deriv (f : α → β) (x dx : α) : β := f x

@[fun_trans] theorem deriv_id : deriv (fun x : α => x) = fun x dx => dx := silentSorry
@[fun_trans] theorem deriv_const [Zero β] (y : β) : deriv (fun _ : α => y) = fun x dx => 0 := silentSorry
@[fun_trans] theorem deriv_apply (x : α) : deriv (fun f : α → β => f x) = fun f df => df x := silentSorry
@[fun_trans] theorem deriv_applyDep (x : α) : deriv (fun f : (x' : α) → E x' => f x) = fun f df => df x := silentSorry
@[fun_trans] theorem deriv_comp (f : β → γ) (g : α → β) (hf : Con f) (hg : Con g) :
    deriv (fun x => f (g x)) = fun x dx => deriv f (g x) (deriv g x dx) := silentSorry
@[fun_trans] theorem deriv_comp_at (f : β → γ) (g : α → β) (x) (hf : ConAt f (g x)) (hg : ConAt g x) :
    deriv (fun x => f (g x)) x = fun dx => deriv f (g x) (deriv g x dx) := silentSorry
@[fun_trans] theorem deriv_pi (f : β → (i : α) → (E i)) (hf : ∀ i, Con (fun x => f x i)) :
    deriv (fun x i => f x i) = fun x dx i => deriv (f · i) x dx := silentSorry
@[fun_trans] theorem deriv_pi_at (f : β → (i : α) → (E i)) (x) (hf : ∀ i, ConAt (fun x => f x i) x) :
    deriv (fun x i => f x i) x = fun dx i => deriv (f · i) x dx := silentSorry



@[fun_trans]
theorem prod_mk_deriv (fst : α → β) (snd : α → γ) (hfst : Con fst) (hsnd : Con snd) :
    deriv (fun x => (fst x, snd x))
    =
    fun x dx => (deriv fst x dx, deriv snd x dx) := silentSorry

@[fun_trans]
theorem prod_mk_deriv_at (fst : α → β) (snd : α → γ) (x) (hfst : ConAt fst x) (hsnd : ConAt snd x) :
    deriv (fun x => (fst x, snd x)) x
    =
    fun dx => (deriv fst x dx, deriv snd x dx) := silentSorry


variable [Add α] [Add β] [Mul α] [Mul β]
set_option trace.Meta.Tactic.fun_trans.attr true
-- "simple form" of theorems
@[fun_trans] theorem fst_deriv : deriv (fun x : α×β => x.1) = fun x dx => dx.1 := silentSorry
@[fun_trans] theorem snd_deriv : deriv (fun x : α×β => x.2) = fun x dx => dx.2 := silentSorry
@[fun_trans] theorem add_deriv : deriv (fun x : α×α => x.1 + x.2) = fun x dx => dx.1 + dx.2 := silentSorry
@[fun_trans] theorem mul_deriv : deriv (fun x : α×α => x.1 * x.2) = fun x dx => dx.1 * x.2 + dx.2 * x.1 := silentSorry



example : Con fun x : α×β => x.2 := by fun_prop

-- "compositional form" of theorems
set_option trace.Meta.Tactic.fun_trans true
set_option trace.Meta.Tactic.fun_trans.step true
set_option trace.Meta.Tactic.fun_trans.discharge true
set_option trace.Meta.Tactic.fun_trans.unify true
set_option trace.Meta.Tactic.fun_prop true
set_option trace.Meta.Tactic.fun_prop.step true
set_option trace.Meta.Tactic.fun_prop.unify true
set_option trace.Meta.Tactic.fun_prop.discharge true
@[fun_trans] theorem fst_deriv' (self : α → β×γ) (hself : Con self) :
    deriv (fun x => (self x).1) = fun x dx => (deriv self x dx).1 := by (conv => lhs; fun_trans)
@[fun_trans] theorem fst_deriv_at' (self : α → β×γ) (x) (hself : ConAt self x) :
    deriv (fun x => (self x).1) x = fun dx => (deriv self x dx).1 := by fun_trans

example (self : α → β×γ) (x) (hself : ConAt self x) :
    deriv (fun x => (self x).1) x = fun dx => (deriv self x dx).1 := by fun_trans

@[fun_trans] theorem snd_deriv' (self : α → β×γ) (hself : Con self) :
    deriv (fun x => (self x).2) = fun x dx => (deriv self x dx).2 := by fun_trans
@[fun_trans] theorem add_deriv' (x y : α → β) (hx : Con x) (hy : Con y) :
    deriv (fun w => x w + y w) = fun w dw => deriv x w dw + deriv y w dw := by fun_trans
