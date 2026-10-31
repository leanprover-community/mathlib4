/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Kevin Buzzard
-/
module

public import Mathlib.Order.OrdContinuous
public import Mathlib.Order.WithBot

/-!
# Adding both `⊥` and `⊤` to a type

This files defines an abbreviation `WithBotTop ι` for `WithBot (WithTop ι)`.
We also introduce an abbreviation `EInt` for `WithBotTop ℤ`.
-/

@[expose] public section

variable {ι : Type*}

variable (ι) in
/-- The type obtained by adding both `⊥` and `⊤` to a type. -/
@[to_dual /-- The type obtained by adding both `⊤` and `⊥` to a type. -/]
abbrev WithBotTop := WithBot (WithTop ι)

/-- The canonical inclusion `ι → WithBotTop ι`. Registered as a coercion. -/
def WithBotTop.coe : ι → WithBotTop ι :=
  WithBot.some ∘ WithTop.some

namespace WithBotTop

instance : Coe ι (WithBotTop ι) := ⟨WithBotTop.coe⟩

theorem coe_injective : Function.Injective (WithBotTop.coe : ι → _) := by rintro _ _ ⟨⟩; rfl

@[simp] lemma coe_ne_bot (a : ι) : (a : WithBotTop ι) ≠ ⊥ := by rintro ⟨⟩
@[simp] lemma coe_ne_top (a : ι) : (a : WithBotTop ι) ≠ ⊤ := by rintro ⟨⟩
@[simp] lemma top_ne_bot : (⊤ : WithBotTop ι) ≠ ⊥ := by rintro ⟨⟩

section

variable {motive : (WithBotTop ι) → Sort*}
  (bot : motive ⊥) (coe : ∀ a : ι, motive a) (top : motive ⊤)

/-- A recursor for `WithBotTop` in terms of the coercion. -/
@[elab_as_elim]
protected def rec : ∀ a, motive a
  | ⊥ => bot
  | (a : ι) => coe a
  | ⊤ => top

@[simp] lemma rec_bot : WithBotTop.rec (motive := motive) bot coe top ⊥ = bot := rfl
@[simp] lemma rec_coe (a : ι) : WithBotTop.rec (motive := motive) bot coe top a = coe a := rfl
@[simp] lemma rec_top : WithBotTop.rec (motive := motive) bot coe top ⊤ = top := rfl

end

@[simp]
lemma coe_le_coe [LE ι] {a b : ι} :
    (a : WithBotTop ι) ≤ b ↔ a ≤ b := by
  rw [← WithTop.coe_le_coe (α := ι)]
  exact WithBot.coe_le_coe

@[simp]
lemma coe_lt_coe [LT ι] {a b : ι} :
    (a : WithBotTop ι) < b ↔ a < b := by
  rw [← WithTop.coe_lt_coe (α := ι)]
  exact WithBot.coe_lt_coe

@[simp]
theorem coe_strictMono [Preorder ι] : StrictMono (WithBotTop.coe : ι → _) :=
  WithBot.coe_strictMono.comp WithTop.coe_strictMono

lemma coe_monotone [Preorder ι] :
    Monotone (WithBotTop.coe : ι → _) :=
  fun _ _ _ ↦ by simpa

variable {α : Type*} [Preorder α]

theorem leftOrdContinuous_coe : LeftOrdContinuous (WithBotTop.coe : α → _) :=
  WithBot.leftOrdContinuous_coe.comp WithTop.leftOrdContinuous_coe

theorem rightOrdContinuous_coe : RightOrdContinuous (WithBotTop.coe : α → _) :=
  WithBot.rightOrdContinuous_coe.comp WithTop.rightOrdContinuous_coe

variable {α β : Type*} {ι : Sort*} [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β]
  [Nonempty ι] {f : α → β}

theorem coe_csSup {s : Set α} (hs : s.Nonempty) (hs' : BddAbove s) :
    (↑(sSup s) : WithBotTop α) = sSup ((↑) '' s) :=
  WithBotTop.leftOrdContinuous_coe.map_csSup hs hs'

theorem coe_csInf {s : Set α} (hs : s.Nonempty) (hs' : BddBelow s) :
    (↑(sInf s) : WithBotTop α) = sInf ((↑) '' s) :=
  WithBotTop.rightOrdContinuous_coe.map_csInf hs hs'

theorem coe_ciSup {f : ι → α} (hf : BddAbove (Set.range f)) :
    (↑(⨆ x, f x) : WithBotTop α) = ⨆ x, ↑(f x) :=
  WithBotTop.leftOrdContinuous_coe.map_ciSup hf

theorem coe_ciInf {f : ι → α} (hf : BddBelow (Set.range f)) :
    (↑(⨅ x, f x) : WithBotTop α) = ⨅ x, ↑(f x) :=
  WithBotTop.rightOrdContinuous_coe.map_ciInf hf

end WithBotTop

/-- The type of extended integers `[-∞, ∞]`, constructed as `WithBot (WithTop ℤ)`. -/
abbrev EInt := WithBotTop ℤ
