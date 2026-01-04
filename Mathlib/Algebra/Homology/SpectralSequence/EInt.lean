/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.Order.WithBot

/-!
# ℤ with bot and top

-/

@[expose] public section

open CategoryTheory Limits

def EInt := WithBot (WithTop ℤ)

namespace EInt

instance : LinearOrder EInt := inferInstanceAs (LinearOrder (WithBot (WithTop ℤ)))
instance : OrderBot EInt := inferInstanceAs (OrderBot (WithBot (WithTop ℤ)))
instance : OrderTop EInt := inferInstanceAs (OrderTop (WithBot (WithTop ℤ)))

def mk (a : ℤ) : EInt := ((a : WithTop ℤ) : WithBot (WithTop ℤ))

lemma mk_monotone : Monotone EInt.mk := by
  intro a b h
  dsimp [mk]
  rw [WithBot.coe_le_coe, WithTop.coe_le_coe]
  exact h

@[simp]
lemma some_some_le_none_iff (a : ℤ) :
    @LE.le EInt _ (some (some a)) none ↔ False := by
  tauto

@[simp]
lemma none_le_some_iff (a : ℤ) :
    @LE.le EInt _ (some none) (some a) ↔ False := by
  change (⊤ : EInt) ≤ _ ↔ _
  rw [iff_false, top_le_iff]
  intro (h : _ = some none)
  simp at h
  tauto


@[simp]
lemma some_some_le_some_some_iff (a b : ℤ) :
    @LE.le EInt _ (some (some a)) (some (some b)) ↔ a ≤ b := by
  erw [WithBot.coe_le_coe, WithTop.coe_le_coe]

@[simp]
lemma some_some_lt_some_some_iff (a b : ℤ) :
    @LT.lt EInt _ (some (some a)) (some (some b)) ↔ a < b := by
  erw [WithBot.coe_lt_coe, WithTop.coe_lt_coe, ]

@[simp]
lemma some_none_le_some_some_iff (a : ℤ) :
    @LE.le EInt _ (some none) (some (some a)) ↔ False := by
  tauto

@[simp]
lemma some_lt_none_iff (a : WithTop ℤ) :
    @LE.le EInt _ (some a) none ↔ False := by
  tauto

@[simp]
lemma mk_le_mk_iff (a b : ℤ) :
    mk a ≤ mk b ↔ a ≤ b :=
  some_some_le_some_some_iff a b

@[simp]
lemma mk_lt_mk_iff (a b : ℤ) :
    mk a < mk b ↔ a < b :=
  some_some_lt_some_some_iff a b

@[simp]
lemma le_bot_mk_iff (a : ℤ) :
    EInt.mk a ≤ ⊥ ↔ False :=
  some_some_le_none_iff a

@[simp]
lemma mk_eq_bot_iff (a : ℤ) :
    EInt.mk a = ⊥ ↔ False := by
  simp only [iff_false]
  rintro ⟨⟩

@[simp]
lemma mk_eq_top_iff (a : ℤ) :
    EInt.mk a = ⊤ ↔ False := by
  simp only [iff_false]
  rintro ⟨⟩

@[simp]
lemma top_eq_bot_mk_iff :
    (⊤ : EInt) = ⊥ ↔ False := by
  simp only [iff_false]
  rintro ⟨⟩

@[simp]
lemma top_le_mk_iff (a : ℤ) :
    ⊤ ≤ EInt.mk a ↔ False :=
  some_none_le_some_some_iff a

@[simp]
lemma top_le_bot_iff :
    (⊤ : EInt) ≤ ⊥ ↔ False := by
  simp

lemma three_cases (x : EInt) :
    x = ⊥ ∨ (∃ (n : ℤ), x = EInt.mk n) ∨ x = ⊤ := by
  obtain (_|_|n) := x
  · exact Or.inl rfl
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl ⟨n, rfl⟩)

lemma le_bot_iff (a : EInt) : a ≤ ⊥ ↔ a = ⊥ := by
  constructor
  · intro h
    obtain (rfl|⟨a, rfl⟩|rfl) := a.three_cases
    · rfl
    · simp at h
    · simp at h
  · rintro rfl
    exact le_refl _

lemma top_le_iff (a : EInt) : ⊤ ≤ a ↔ a = ⊤ := by
  constructor
  · intro h
    obtain (rfl|⟨a, rfl⟩|rfl) := a.three_cases
    · simp at h
    · simp at h
    · rfl
  · rintro rfl
    exact le_refl _

end EInt
