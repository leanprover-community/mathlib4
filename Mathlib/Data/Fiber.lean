/-
Copyright (c) 2023 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.Tactic


@[simp]
def Fib {C E : Type*} (P : E → C) (c : C) := {d : E // P d = c}


namespace Fib
variable {C E : Type*} {P : E → C} {c d : C}
/- coercion from the fibre to the total category -/
instance  {c : C} : CoeOut (Fib P c) E where
  coe := fun x => x.1

@[simp]
lemma coe_mk (e : E) (h : P e = c) : ( (⟨e, h⟩ : Fib P c) : E) = e := rfl

@[simp]
lemma mk_coe (x : Fib P c) : ⟨x.1, x.2⟩  = x := rfl

lemma coe_inj (x y : Fib P c) : (x : E) = y ↔ x = y := by
  constructor
  · intro h; cases x; cases y; simp at h; subst h; rfl
  · intro h; rw [h]

@[simp]
lemma over (x : Fib P c) : P x = c := x.2

@[simp]
lemma over_eq (x y : Fib P c) : P x = P y := by simp [Fib.over]

@[simps]
def tauto (e : E) : Fib P (P e) := ⟨e, rfl⟩

/--Regarding an object of the total space as an object in the obj of its image.-/
instance instTautoFib (e : E) : CoeDep (E) (e) (Fib P (P e) ) where
  coe := tauto e

@[simp]
lemma tauto_over (e : E) : (tauto e : Fib P (P e)).1 = e := rfl

@[simp]
def eqRebase (e : Fib P c) (_ : c = d) : Fib P d := ⟨e.1, by simp_all only [over]⟩

@[simp]
lemma coe_tauto (e : Fib P c) : eqRebase (tauto e.1) (by simp [over]) =  e := by
  cases e; simp

@[simp]
lemma coe_tauto' (e : Fib P c) : (tauto e.1) =   eqRebase e (by simp [over]) := by
  cases e; rfl

@[ext]
structure Total {C E : Type*} (P : E → C) where
base : C
fiber : Fib P base

end Fib
