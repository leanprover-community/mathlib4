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

theorem le_zero {a : Nimber} : a ≤ 0 ↔ a = 0 :=
  Ordinal.le_zero

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

protected def add (a b : Nimber.{u}) : Nimber.{u} :=
  sInf {x | (∃ a', ∃ (_ : a' < a), x = Nimber.add a' b) ∨
    ∃ b', ∃ (_ : b' < b), x = Nimber.add a b'}ᶜ
termination_by (a, b)

instance : Add Nimber :=
  ⟨Nimber.add⟩

/-- The extra binders in this definition can help the termination checker figure out an induction is
well-founded. -/
/-theorem add_def' (a b : Nimber) :
    a + b = sInf {x | (∃ a', ∃ (_ : a' < a), x = a' + b) ∨ ∃ b', ∃ (_ : b' < b), x = a + b'}ᶜ := by
  change Nimber.add a b = _
  rw [Nimber.add]
  rfl-/

theorem add_def (a b : Nimber) :
    a + b = sInf {x | (∃ a' < a, x = a' + b) ∨ ∃ b' < b, x = a + b'}ᶜ := by
  change Nimber.add a b = _
  rw [Nimber.add]
  simp_rw [exists_prop]
  rfl

/-- The set in the definition of `Nimber.add` is nonempty. -/
theorem add_nonempty (a b : Nimber) :
    {x | (∃ a' < a, x = a' + b) ∨ ∃ b' < b, x = a + b'}ᶜ.Nonempty := by
  use Ordinal.blsub₂ (succ a) (succ b) @fun x _ y _ => Nimber.add x y
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_or, not_exists, not_and]
  constructor <;>
  intro x hx <;>
  apply (Ordinal.lt_blsub₂ _ _ _).ne'
  exacts [hx.trans <| lt_succ _, lt_succ _, lt_succ _, hx.trans <| lt_succ _]

theorem exists_of_lt_add (h : a < b + c) : (∃ b' < b, a = b' + c) ∨ ∃ c' < c, a = b + c' := by
  rw [add_def] at h
  have := not_mem_of_lt_csInf h ⟨_, bot_mem_lowerBounds _⟩
  rwa [Set.mem_compl_iff, not_not] at this

theorem add_le_of_forall_ne (h₁ : ∀ b' < b, a ≠ b' + c) (h₂ : ∀ c' < c, a ≠ b + c') :
    b + c ≤ a := by
  by_contra! h
  have := exists_of_lt_add h
  tauto

private theorem add_ne_of_lt (a b : Nimber) :
    (∀ a' < a, a + b ≠ a' + b) ∧ ∀ b' < b, a + b ≠ a + b' := by
  have H := csInf_mem (add_nonempty a b)
  rw [← add_def] at H
  simpa using H

theorem add_left_injective : Injective (a + ·) := by
  intro b c h
  apply le_antisymm <;>
  apply le_of_not_lt
  · exact fun hc => (add_ne_of_lt a b).2 c hc h
  · exact fun hb => (add_ne_of_lt a c).2 b hb h.symm

@[simp]
theorem add_left_inj : a + b = a + c ↔ b = c :=
  add_left_injective.eq_iff

theorem add_left_ne_iff : a + b ≠ a + c ↔ b ≠ c :=
  add_left_inj.not

@[simp]
theorem add_right_injective : Injective (· + a) := by
  intro b c h
  apply le_antisymm <;>
  apply le_of_not_lt
  · exact fun hc => (add_ne_of_lt b a).1 c hc h
  · exact fun hb => (add_ne_of_lt c a).1 b hb h.symm

@[simp]
theorem add_right_inj : a + c = b + c ↔ a = b :=
  add_right_injective.eq_iff

theorem add_right_ne_iff : a + c ≠ b + c ↔ a ≠ b :=
  add_right_inj.not

-- Ideally the proof would be an easy induction on `add_def`, but rewriting under binders trips up
-- the termination checker.
theorem add_comm (a b : Nimber) : a + b = b + a := by
  apply le_antisymm <;>
  apply add_le_of_forall_ne <;>
  intro x hx
  on_goal 1 => rw [add_comm x, add_left_ne_iff]
  on_goal 2 => rw [add_comm a, add_right_ne_iff]
  on_goal 3 => rw [← add_comm a, add_left_ne_iff]
  on_goal 4 => rw [← add_comm x, add_right_ne_iff]
  all_goals exact hx.ne'
termination_by (a, b)

@[simp]
theorem add_eq_zero_iff {a b : Nimber} : a + b = 0 ↔ a = b := by
  constructor <;>
  intro hab
  · obtain h | rfl | h := lt_trichotomy a b
    · have ha : a + a = 0 := add_eq_zero_iff.2 rfl
      rwa [← ha, add_left_inj, eq_comm] at hab
    · rfl
    · have hb : b + b = 0 := add_eq_zero_iff.2 rfl
      rwa [← hb, add_right_inj] at hab
  · rw [← le_zero]
    apply add_le_of_forall_ne <;>
    simp_rw [ne_eq, eq_comm] <;>
    intro x hx
    · rw [add_eq_zero_iff, ← hab]
      exact hx.ne
    · rw [add_eq_zero_iff, hab]
      exact hx.ne'
termination_by (a, b)

@[simp]
theorem add_self (a : Nimber) : a + a = 0 :=
  add_eq_zero_iff.2 rfl

theorem add_assoc (a b c : Nimber) : a + b + c = a + (b + c) := by
  apply le_antisymm <;>
  apply add_le_of_forall_ne <;>
  intro x hx <;>
  try obtain ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩ := exists_of_lt_add hx
  on_goal 1 => rw [add_assoc y, add_right_ne_iff]
  on_goal 2 => rw [add_assoc _ y, add_left_ne_iff, add_right_ne_iff]
  on_goal 3 => rw [add_assoc _ _ x, add_left_ne_iff, add_left_ne_iff]
  on_goal 4 => rw [← add_assoc x, add_right_ne_iff, add_right_ne_iff]
  on_goal 5 => rw [← add_assoc _ y, add_right_ne_iff, add_left_ne_iff]
  on_goal 6 => rw [← add_assoc _ _ y, add_left_ne_iff]
  all_goals apply ne_of_gt; assumption
termination_by (a, b, c)

end Nimber
