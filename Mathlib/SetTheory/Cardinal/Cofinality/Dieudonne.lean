/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.SetTheory.Cardinal.Cofinality.Club

/-!
# Dieudonné measure

write neat thing here
-/

@[expose] public section

variable {α : Type*} {x y : α} [LinearOrder α]

/-- A type alias which endows a well-order `α` with the Dieudonne measure. -/
def Dieudonne (α : Type*) : Type _ := α

instance : LinearOrder (Dieudonne α) := inferInstanceAs (LinearOrder α)

def toDieudonne : α ≃o Dieudonne α := .refl _
def ofDieudonne : Dieudonne α ≃o α := .refl _

@[simp] theorem ofDieudonne_toDieudonne (x : α) : ofDieudonne (toDieudonne x) = x := rfl
@[simp] theorem toDieudonne_ofDieudonne (x : Dieudonne α) : toDieudonne (ofDieudonne x) = x := rfl

@[implicit_reducible]
def dieudonne : MeasurableSpace α where
  MeasurableSet' s := ∃ t, IsClub t ∧ (t ⊆ s ∨ t ⊆ sᶜ)
  measurableSet_empty := ⟨_, .univ, by simp⟩
  measurableSet_compl _ := by simp [or_comm]
  measurableSet_iUnion := by sorry
