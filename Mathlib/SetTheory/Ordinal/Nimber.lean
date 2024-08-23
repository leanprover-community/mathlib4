/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Nimbers

The nimbers inherit the order from the ordinals - this makes definitions involving minimum excluded
values more convenient. However, the fact that nimbers are of characteristic 2 prevents the order
from interacting with the arithmetic in any nice way.

## Todo

- Prove the characterization of nimber addition in terms of the Cantor normal form.
-/

universe u v

open Function Order

noncomputable section

/-! ### Basic casts between `Ordinal` and `Nimber` -/

/-- A type synonym for ordinals with natural addition and multiplication. -/
def Nimber : Type _ :=
  -- Porting note: used to derive LinearOrder & SuccOrder but need to manually define
  Ordinal deriving Zero, Inhabited, One, WellFoundedRelation

instance Nimber.linearOrder : LinearOrder Nimber := {Ordinal.linearOrder with}
instance Nimber.succOrder : SuccOrder Nimber := {Ordinal.succOrder with}
instance Nimber.orderBot : OrderBot Nimber := {Ordinal.orderBot with}
instance Nimber.noMaxOrder : NoMaxOrder Nimber := {Ordinal.noMaxOrder with}
instance Nimber.zeroLEOneClass : ZeroLEOneClass Nimber := {Ordinal.zeroLEOneClass with}
instance Nimber.NeZero.one : NeZero (1 : Nimber) := {Ordinal.NeZero.one with}

/-- The identity function between `Ordinal` and `Nimber`. -/
@[match_pattern]
def Ordinal.toNimber : Ordinal ≃o Nimber :=
  OrderIso.refl _

/-- The identity function between `Nimber` and `Ordinal`. -/
@[match_pattern]
def Nimber.toOrdinal : Nimber ≃o Ordinal :=
  OrderIso.refl _

namespace Nimber

open Ordinal

@[simp]
theorem toOrdinal_symm_eq : Nimber.toOrdinal.symm = Ordinal.toNimber :=
  rfl

@[simp]
theorem toOrdinal_toNimber (a : Nimber) :
    Ordinal.toNimber (Nimber.toOrdinal a) = a := rfl

theorem lt_wf : @WellFounded Nimber (· < ·) :=
  Ordinal.lt_wf

instance : WellFoundedLT Nimber :=
  Ordinal.wellFoundedLT

instance : IsWellOrder Nimber (· < ·) :=
  { }

instance : ConditionallyCompleteLinearOrderBot Nimber :=
  WellFoundedLT.conditionallyCompleteLinearOrderBot _

@[simp]
theorem bot_eq_zero : ⊥ = 0 :=
  rfl

@[simp]
theorem toOrdinal_zero : toOrdinal 0 = 0 :=
  rfl

@[simp]
theorem toOrdinal_one : toOrdinal 1 = 1 :=
  rfl

@[simp]
theorem toOrdinal_eq_zero (a) : toOrdinal a = 0 ↔ a = 0 :=
  Iff.rfl

@[simp]
theorem toOrdinal_eq_one (a) : toOrdinal a = 1 ↔ a = 1 :=
  Iff.rfl

@[simp]
theorem toOrdinal_max {a b : Nimber} : toOrdinal (max a b) = max (toOrdinal a) (toOrdinal b) :=
  rfl

@[simp]
theorem toOrdinal_min {a b : Nimber} : toOrdinal (min a b) = min (toOrdinal a) (toOrdinal b) :=
  rfl

theorem succ_def (a : Nimber) : succ a = toNimber (toOrdinal a + 1) :=
  rfl

/-- A recursor for `Nimber`. Use as `induction x`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
protected def rec {β : Nimber → Sort*} (h : ∀ a, β (toNimber a)) : ∀ a, β a := fun a =>
  h (toOrdinal a)

/-- `Ordinal.induction` but for `Nimber`. -/
theorem induction {p : Nimber → Prop} : ∀ (i) (_ : ∀ j, (∀ k, k < j → p k) → p j), p i :=
  Ordinal.induction

end Nimber

namespace Ordinal

variable {a b c : Ordinal.{u}}

@[simp]
theorem toNimber_symm_eq : toNimber.symm = Nimber.toOrdinal :=
  rfl

@[simp]
theorem toNimber_toOrdinal (a : Ordinal) :  Nimber.toOrdinal (toNimber a) = a :=
  rfl

@[simp]
theorem toNimber_zero : toNimber 0 = 0 :=
  rfl

@[simp]
theorem toNimber_one : toNimber 1 = 1 :=
  rfl

@[simp]
theorem toNimber_eq_zero (a) : toNimber a = 0 ↔ a = 0 :=
  Iff.rfl

@[simp]
theorem toNimber_eq_one (a) : toNimber a = 1 ↔ a = 1 :=
  Iff.rfl

@[simp]
theorem toNimber_max (a b : Ordinal) :
    toNimber (max a b) = max (toNimber a) (toNimber b) :=
  rfl

@[simp]
theorem toNimber_min (a b : Ordinal) :
    toNimber (min a b) = min (toNimber a) (toNimber b) :=
  rfl

end Ordinal

/-! ### Nimber addition -/

namespace Nimber

variable {a b c : Nimber.{u}}

protected def add (a b : Nimber) : Nimber :=
  sInf {x | (∃ a', ∃ (_ : a' < a), x = Nimber.add a' b) ∨
    ∃ b', ∃ (_ : b' < b), x = Nimber.add a b'}ᶜ
termination_by (a, b)

instance : Add Nimber :=
  ⟨Nimber.add⟩

theorem add_def (a b : Nimber) :
    a + b = sInf {x | (∃ a' < a, x = a' + b) ∨ ∃ b' < b, x = a + b'}ᶜ := by
  change Nimber.add a b = _
  rw [Nimber.add]
  simp_rw [exists_prop]
  rfl

theorem exists_of_lt_add (a : Nimber) (h : a < b + c) :
    (∃ b' < b, a = b' + c) ∨ ∃ c' < c, a = b + c' := by
  rw [add_def] at h
  have := not_mem_of_lt_csInf

private theorem add_left_inj'

theorem add_left_inj : a + b = a + c ↔ b = c := by
  refine ⟨?_, congr_arg _⟩


theorem add_comm (a b : Nimber) : a + b = b + a := by
  rw [add_def, add_def]
  simp_rw [or_comm, ← add_comm _ b, add_comm a]
termination_by (a, b)




theorem lt_add_iff : a < b + c ↔ (∃ b' < b, a = b' + c) ∨ ∃ c' < c, a = b + c' := by
  rw [add_def]
  simp [lt_sInf_iff]

theorem nadd_le_iff : b ♯ c ≤ a ↔ (∀ b' < b, b' ♯ c < a) ∧ ∀ c' < c, b ♯ c' < a := by
  rw [nadd_def]
  simp [blsub_le_iff]

end Nimber
