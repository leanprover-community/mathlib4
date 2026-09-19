/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Kevin Buzzard
-/
module

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

end WithBotTop

/-- The type of extended integers `[-∞, ∞]`, constructed as `WithBot (WithTop ℤ)`. -/
abbrev EInt := WithBotTop ℤ
