/-
Copyright (c) 2023 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.Tactic.Basic
import Mathlib.Data.Subtype

/-!
# Fiber

This files define the type `Fiber` of the fiber of a map at a given point.
-/


/-- The fiber of a map at a given point. -/
@[simp]
def Fiber {C E : Type*} (P : E → C) (c : C) := {d : E // P d = c}

namespace Fiber

variable {C E : Type*} {P : E → C} {c d : C}

/-- Coercion from the fiber to the domain. -/
instance  {c : C} : CoeOut (Fiber P c) E where
coe := fun x => x.1

@[simp]
lemma coe_mk (e : E) (h : P e = c) : ( (⟨e, h⟩ : Fiber P c) : E) = e := rfl

@[simp]
lemma mk_coe (x : Fiber P c) : ⟨x.1, x.2⟩  = x := rfl

lemma coe_inj (x y : Fiber P c) : (x : E) = y ↔ x = y := Subtype.coe_inj

@[simp]
lemma over (x : Fiber P c) : P x = c := x.2

@[simp]
lemma over_eq (x y : Fiber P c) : P x = P y := by
simp [Fiber.over]

/-- Given an element of the domain of the map, `tauto` tautologically constructs en element in the fiber of the image of the domain element. -/
@[simp]
def tauto (e : E) : Fiber P (P e) := ⟨e, rfl⟩

/-- Regarding an element of the domain as an element in the fibre of its image. -/
instance instTautoFib (e : E) : CoeDep (E) (e) (Fiber P (P e) ) where
coe := tauto e

@[simp]
lemma tauto_over (e : E) : (tauto e : Fiber P (P e)).1 = e := rfl

/-- Rebase an element of in a fiber along an equality of the basepoints. -/
@[simp]
def cast (e : Fiber P c) (eq : c = d) : Fiber P d := ⟨e.1, by simp_all only [over]⟩

@[simp]
theorem coe_eqRebase (e : Fiber P c) (eq : c = d) : (cast e eq : E) = e.1 := rfl

@[simp]
lemma cast_coe_tauto (e : Fiber P c) : cast (tauto e.1) (by simp [over]) =  e := by
simp

@[simp]
lemma cast_coe_tauto' (e : Fiber P c) : (tauto e.1) = cast e (by simp [over]) := by
cases e; rfl

/-- The total space of a map. -/
@[ext]
structure Total {C E : Type*} (P : E → C) where
base : C
fiber : Fiber P base

end Fiber
