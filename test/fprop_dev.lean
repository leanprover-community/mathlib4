/-
Copyright (c) 2024 Tomáš Skřivan All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
import Mathlib.Tactic.FProp.Elab

/-! # Tests for the `fprop` tactic

This file is designed for developlemnt of fprop and does not depend on most of mathlib. It defineds
two function properties `Con` and `Lin` which roughly correspond to `Continuity` and `IsLinearMap`.
-/


open Mathlib Meta FProp Function


variable {α β γ δ ι : Type _} {E : α → Type _}

instance [Add α] : Add (ι → α) := ⟨fun f g i => f i + g i⟩

-- define function propositions --
----------------------------------

class Obj (α : Type _) : Type where

instance [Obj α] [Obj β] : Obj (α × β) := ⟨⟩
instance [∀ x, Obj (E x)] : Obj ((x' : α) → E x') := ⟨⟩


@[fprop] opaque Con {α β} [Obj α] [Obj β] (f : α → β) : Prop
@[fprop] opaque Lin {α β} [Obj α] [Obj β] (f : α → β) : Prop


-- state basic lambda calculus rules --
---------------------------------------

variable [Obj α] [Obj β] [Obj γ] [Obj δ] [∀ x, Obj (E x)]

@[fprop] theorem Con_id : Con (fun x : α => x) := sorry
@[fprop] theorem Con_const (y : β) : Con (fun x : α => y) := sorry
@[fprop] theorem Con_apply (x : α) : Con (fun f : α → β => f x) := sorry
@[fprop] theorem Con_applyDep (x : α) : Con (fun f : (x' : α) → E x' => f x) := sorry
@[fprop] theorem Con_comp (f : β → γ) (g : α → β) (hf : Con f) (hg : Con g) : Con (fun x => f (g x)) := sorry
@[fprop] theorem Con_pi (f : β → (i : α) → (E i)) (hf : ∀ i, Con (fun x => f x i)) : Con (fun x i => f x i) := sorry

-- Lin is missing `const` theorem
@[fprop] theorem Lin_id : Lin (fun x : α => x) := sorry
@[fprop] theorem Lin_apply (x : α) : Lin (fun f : α → β => f x) := sorry
@[fprop] theorem Lin_applyDep (x : α) : Lin (fun f : (x' : α) → E x' => f x) := sorry
@[fprop] theorem Lin_comp (f : β → γ) (g : α → β) (hf : Lin f) (hg : Lin g) : Lin (fun x => f (g x)) := sorry
@[fprop] theorem Lin_pi {ι} (f : α → ι → γ) (hf : ∀ i, Lin (fun x => f x i)) : Lin (fun x i => f x i) := sorry



-- transition theorem --
------------------------
@[fprop] theorem lin_to_con (f : α → β) (hf : Lin f) : Con f := sorry



-- theorems about function in the environment --
------------------------------------------------

@[fprop]
theorem prod_mk_Con (fst : α → β) (snd : α → γ) (hfst : Con fst) (hsnd : Con snd)
  : Con fun x => (fst x, snd x) := sorry
@[fprop]
theorem prod_mk_Lin (fst : α → β) (snd : α → γ) (hfst : Lin fst) (hsnd : Lin snd)
  : Lin fun x => (fst x, snd x) := sorry


variable [Add α] [Add β]

-- "simple form" of theorems
@[fprop] theorem fst_Con : Con fun x : α×β => x.1 := sorry
@[fprop] theorem snd_Con : Con fun x : α×β => x.2 := sorry
@[fprop] theorem add_Con : Con (fun x : α×α => x.1 + x.2) := sorry


-- "compositional form" of theorems
@[fprop] theorem fst_Con' (self : α → β×γ) (hself : Con self) : Con fun x => (self x).1 := by fprop
@[fprop] theorem snd_Con' (self : α → β×γ) (hself : Con self) : Con fun x => (self x).2 := by fprop
@[fprop] theorem add_Con' (x y : α → β) (hx : Con x) (hy : Con y) : Con (fun w => x w + y w) := by fprop



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
  coe_injective' := sorry

instance : FunLike (α -o β) α β where
  coe := fun f => f.toFun
  coe_injective' := sorry


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
@[fprop] theorem conHom_con' (f : α → β ->> γ) (g : α → β) (hf : Con f) (hg : Con g) : Con (fun x => (f x) (g x)) := sorry

-- analogous theorem with `α -o β` does no hold
@[fprop] theorem linHom_lin (f : α -o β) : Lin f := sorry
-- the only analoge is this theorem but that is alredy provable
example (f : α → β -o γ) (g : α → β) (hf : Lin (fun (x,y) => f x y)) (hg : Lin g) : Lin (fun x => (f x) (g x)) := by fprop



----------------------------------------------------------------------------------------------------

-- set_option profiler true
-- set_option profiler.threshold 10

example (f : α → β → γ) (hf : Con fun (x,y) => f x y)  : Con f := by fprop

example : Con (fun x : α => x) := by fprop
example (y : β) : Con (fun _ : α => y) := by fprop
example (x : α) : Con (fun f : α → β => f x) := by fprop
example (x : α) : Con (fun f : (x' : α) → E x' => f x) := by fprop
example (x : α) (y : β) : Con (fun f : α → β → γ => f x y) := by fprop
example (x : α) (y : β) : Con (fun f : α → β → (x' : α) → E x' => f x y x) := by fprop
example (y : β) : Con (fun (f : α → β → (x' : α) → E x') x => f x y x) := by fprop
example : Con (fun (f : α → β → (x' : α) → E x') x y => f x y x) := by fprop

example (f : β → γ) (g : α → β) (hf : Con f) (hg : Con g) : Con (fun x => f (g x)) := by fprop
example (f : α → β → γ) (g : α → β) (hf : Con (fun (x,y) => f x y)) (hg : Con g) : Con (fun x => f x (g x)) := by fprop
example (f : α → β → γ) (g : α → β) (hf : Con (fun (x,y) => f x y)) (hg : Con g) : Con (fun x => let y := g x; f x y) := by fprop
example {ι} (f : α → ι → γ) (hf : ∀ i, Con (fun x => f x i)) : Con (fun x i => f x i) := by fprop

example : Con (fun (f : α → β → γ) x y => f x y) := by fprop
example : Con (fun (f : α → β → γ) y x => f x y) := by fprop
example : Con (fun (f : α → α → α → α → α) y x => f x y x y) := by fprop

-- set_option pp.notation false 


-- local hypothesis are assumed to be always in fully applied form 
-- so `(hf : Con f)` is not considered valid 
-- is this valid assumption? 
example (f : α → β → γ) (hf : Con f) : Con f := by fprop
example (f : α → β → γ) (hf : Con f) : Con (fun x => f x) := by fprop
example (f : α → β → γ) (hf : Con f) : Con (fun x y => f x y) := by fprop
example (f : α → β → γ) (hf : Con f) (y) : Con (fun x => f x y) := by fprop

example (f : α → β → γ) (hf : Con fun (x,y) => f x y) (x) : Con fun y => f x y := by fprop
example (f : α → β → γ) (hf : Con fun (x,y) => f x y) (y) : Con fun x => f x y := by fprop
example (f : α → β → γ) (hf : Con fun (x,y) => f x y)  : Con f := by fprop

example (f : α → β → γ) (hf : Con ↿f) (x : α) : Con fun y => f x y := by fprop
example (f : α → β → γ) (hf : Con ↿f) (y : β) : Con fun x => f x y := by fprop
example (f : α → β → γ) (hf : Con ↿f) : Con f := by fprop

example (f : α → β → γ) (hf : ∀ x, Con fun y => f x y) (x) : Con fun y => f x y := by fprop
example (f : α → β → γ) (hf : ∀ x, Con fun y => f x y) (x) : Con (f x) := by fprop
example (f : α → β → γ) (hf : ∀ y, Con fun x => f x y) (y) : Con fun x => f x y := by fprop
example (f : α → β → γ) (hf : ∀ y, Con fun x => f x y) : Con fun x => f x := by fprop

example (f : α → β → γ) (hf : Con fun (x,y) => f x y) (y) : Con fun x => f x y := by fprop
example (f : α → β → γ) (hf : Con fun (x,y) => f x y) : Con f := by fprop
example (f : α → α → β) (hf : Con fun (x,y) => f x y) : Con (fun x => f x x) := by fprop

example (f : α → β → γ → δ) (hf : ∀ x, Con fun (y,z) => f x y z) (x z) : Con (fun y => f x y z)  := by fprop
example (f : α → β → γ → δ) (hf : ∀ x, Con fun (y,z) => f x y z) (x y) : Con (fun z => f x y z)  := by fprop
example (f : α → β → γ → δ) (hf : ∀ x, Con fun (y,z) => f x y z) (x) : Con (fun z y => f x y z)  := by fprop
example (f : α → β → γ → δ) (hf : ∀ x, Con fun (y,z) => f x y z) (x y) : Con (f x y)  := by fprop
example (f : α → β → γ → δ) (hf : ∀ x, Con fun (y,z) => f x y z) (x) : Con (fun y => f x y)  := by fprop

example (f : α → Nat → Nat → β) (hf : ∀ i j, Con (f · i j)) : Con (fun x i j => f x (i+j) j)  := by fprop
example (f : α → Nat → Nat → β) (hf : ∀ i j, Con (f · i j)) (i j) : Con (fun x => f x (i+j) j)  := by fprop
example (f : α → Nat → Nat → β) (hf : Con f) : Con (fun x i j => f x (i+j) j)  := by fprop
example (f : α → Nat → Nat → β) (hf : Con f) (i j) : Con (fun x => f x (i+j) j)  := by fprop

example (f : α → β → γ → δ) (hf : ∀ y, Con fun (x,z) => f x y z) : Con f := by fprop
example (f : α → β → γ → δ) (hf : ∀ y, Con fun (x,z) => f x y z) : Con f := by fprop


example (f : α → β ->> γ) (hf : Con f) (y) : Con (fun x => f x y) := by fprop
example (f : α → β ->> γ) (hf : Con f) : Con (fun x y => f x y) := by fprop
example (f : α → β ->> γ) (hf : Con fun (x,y) => f x y) (y) : Con fun x => f x y := by fprop
example (f : α → β ->> γ) (hf : Con fun (x,y) => f x y) : Con fun x y => f x y := by fprop
example (f : α → β ->> γ) (hf : Con fun (x,y) => f x y) (x) : Con fun y => f x y := by fprop
example (f : α → α ->> (α → α)) (hf : Con fun (x,y,z) => f x y z) (x) : Con fun y => f x y := by fprop
example (f : α → α ->> (α → α)) (hf : Con fun (x,y,z) => f x y z) : Con fun x y => f y x x := by fprop

example (f : α → β ->> γ) (hf : Con ↿f) (y) : Con fun x => f x y := by fprop
example (f : α → β ->> γ) (x) : Con fun y => f x y := by fprop
example (f : α → α ->> (α → α)) (x) : Con fun y => f x y := by fprop
example (f : α → α ->> (α → α)) (hf : Con ↿f) : Con fun x y => f y x x := by fprop


example (f : α → β ->> γ) (hf : Con f) : Con ↿f := by fprop

example : Con (HAdd.hAdd : α → α → α) := by fprop  -- under applied constant
example : Con (fun x => (HAdd.hAdd : α → α → α) x) := by fprop  -- under applied constant

example : Con (fun x => (HAdd.hAdd : ((ι→α) → (ι→α) → (ι→α))) x) := by fprop
example : Con (fun x y => (HAdd.hAdd : ((ι→α) → (ι→α) → (ι→α))) x y) := by fprop
example : Con (fun x y i => (HAdd.hAdd : ((ι→α) → (ι→α) → (ι→α))) x y i) := by fprop
example (y) : Con (fun x i => (HAdd.hAdd : ((ι→α) → (ι→α) → (ι→α))) x y i) := by fprop
example (y i) : Con (fun x => (HAdd.hAdd : ((ι→α) → (ι→α) → (ι→α))) x y i) := by fprop

-- example (f : β → γ) (x) (hf : Lin f)  : Lin (fun (g : α → β) => f (g x)) := by fprop


-- apply theorems about FunLike.coe
example (f : α ->> β) : Con f := by fprop
example (f : α -o β) : Con f := by fprop
example (f : α → β) (hf : Lin f) : Con f := by fprop
example (f : β → γ) (g : α ->> β) (hf: Con f) : Con (fun x => f (g x)) := by fprop
example (f : β ->> γ) (g : α → β) (hg: Con g) : Con (fun x => f (g x)) := by fprop
example (f : β -o γ) (g : α → β) (hg : Con g) : Con fun x => f (g x) := by fprop

-- set_option trace.Meta.Tactic.fprop true in
example (f : α → β ->> γ) (hf : Con f) (g : α → β) (hg : Lin g)  : Con (fun x => f x (g x)) := by fprop
example (f : α → β ->> γ) (hf : Lin (fun (x,y) => f x y)) (g : α → β) (hg : Lin g)  : Con (fun x => f x (g x)) := by fprop
example (f : α → β ->> γ) (hf : Lin (fun (x,y) => f x y)) (g : α → β) (hg : Lin g)  : Lin (fun x => f x (g x)) := by fprop

-- sometimes unfold constants 
example (f : α → β) (hf : Con f) : Con (fun x => id f x) := by fprop
example (f : α → β) (hf : Con f) : Con (fun x => (id id) f x) := by fprop
example (f : α → α → α) (hf : Con (fun (x,y) => f x y)) : Con (fun x => id (id f x) x) := by fprop
example (f : α → α → α) (hf : Con (fun (x,y) => f x y)) : Con (fun x => (id id) ((id id) f x) x) := by fprop
example (f : α → α → α) (hf : Con (fun (x,y) => f x y)) : Con (fun x : α×α => id (f x.1) x.2) := by fprop


-- is working up to here
#exit 

-- times out 
-- example (f : α → β -o γ) (hf : Lin (fun (x,y) => f x y)) (g : α → β) (hg : Lin g)  : Lin (fun x => f x (g x)) := by fprop

example (f : α ->> (β → γ)) (y) : Con (fun x => f x y) := by fprop
example (f : α ->> (β → γ)) (hf : Con (fun (x,y) => f x y)) (y) : Con (fun x => f x y) := by fprop
example : let f := fun x : α => x; Con (fun x => f x) := by fprop

