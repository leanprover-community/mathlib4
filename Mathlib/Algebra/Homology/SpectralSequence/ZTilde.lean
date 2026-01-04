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

def ℤt := WithBot (WithTop ℤ)

namespace ℤt

instance : LinearOrder ℤt := inferInstanceAs (LinearOrder (WithBot (WithTop ℤ)))
instance : OrderBot ℤt := inferInstanceAs (OrderBot (WithBot (WithTop ℤ)))
instance : OrderTop ℤt := inferInstanceAs (OrderTop (WithBot (WithTop ℤ)))

def mk (a : ℤ) : ℤt := ((a : WithTop ℤ) : WithBot (WithTop ℤ))

lemma mk_monotone : Monotone ℤt.mk := by
  intro a b h
  dsimp [mk]
  rw [WithBot.coe_le_coe, WithTop.coe_le_coe, ]
  exact h

@[simps! obj map]
def _root_.ιℤt : ℤ ⥤ ℤt := ℤt.mk_monotone.functor

instance {α : Type _} [Preorder α] (a : α) : IsIso (homOfLE (le_refl a)) :=
  (Iso.refl a).isIso_hom

@[simp]
lemma some_some_le_none_iff (a : ℤ) :
    @LE.le ℤt _ (some (some a)) none ↔ False := by
  tauto

@[simp]
lemma none_le_some_iff (a : ℤ) :
    @LE.le ℤt _ (some none) (some a) ↔ False := by
  change (⊤ : ℤt) ≤ _ ↔ _
  rw [iff_false, top_le_iff]
  intro (h : _ = some none)
  simp at h
  tauto


@[simp]
lemma some_some_le_some_some_iff (a b : ℤ) :
    @LE.le ℤt _ (some (some a)) (some (some b)) ↔ a ≤ b := by
  erw [WithBot.coe_le_coe, WithTop.coe_le_coe]

@[simp]
lemma some_some_lt_some_some_iff (a b : ℤ) :
    @LT.lt ℤt _ (some (some a)) (some (some b)) ↔ a < b := by
  erw [WithBot.coe_lt_coe, WithTop.coe_lt_coe, ]

@[simp]
lemma some_none_le_some_some_iff (a : ℤ) :
    @LE.le ℤt _ (some none) (some (some a)) ↔ False := by
  tauto

@[simp]
lemma some_lt_none_iff (a : WithTop ℤ) :
    @LE.le ℤt _ (some a) none ↔ False := by
  tauto

@[simp]
lemma mk_le_mk_iff (a b : ℤ) :
    mk a ≤ mk b ↔ a ≤ b :=
  some_some_le_some_some_iff a b

@[simp]
lemma mk_lt_mk_iff (a b : ℤ) :
    mk a < mk b ↔ a < b :=
  some_some_lt_some_some_iff a b

instance : OrderTop ℤt := by dsimp [ℤt]; infer_instance
instance : OrderBot ℤt := by dsimp [ℤt]; infer_instance

@[simp]
lemma le_bot_mk_iff (a : ℤ) :
    ℤt.mk a ≤ ⊥ ↔ False :=
  some_some_le_none_iff a

@[simp]
lemma mk_eq_bot_iff (a : ℤ) :
    ℤt.mk a = ⊥ ↔ False := by
  simp only [iff_false]
  rintro ⟨⟩

@[simp]
lemma mk_eq_top_iff (a : ℤ) :
    ℤt.mk a = ⊤ ↔ False := by
  simp only [iff_false]
  rintro ⟨⟩

@[simp]
lemma top_eq_bot_mk_iff :
    (⊤ : ℤt) = ⊥ ↔ False := by
  simp only [iff_false]
  rintro ⟨⟩

@[simp]
lemma top_le_mk_iff (a : ℤ) :
    ⊤ ≤ ℤt.mk a ↔ False :=
  some_none_le_some_some_iff a

@[simp]
lemma top_le_bot_iff :
    (⊤ : ℤt) ≤ ⊥ ↔ False := by
  simp

lemma three_cases (x : ℤt) :
    x = ⊥ ∨ (∃ (n : ℤ), x = ℤt.mk n) ∨ x = ⊤ := by
  obtain (_|_|n) := x
  · exact Or.inl rfl
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl ⟨n, rfl⟩)

lemma le_bot_iff (a : ℤt) : a ≤ ⊥ ↔ a = ⊥ := by
  constructor
  · intro h
    obtain (rfl|⟨a, rfl⟩|rfl) := a.three_cases
    · rfl
    · simp at h
    · simp at h
  · rintro rfl
    exact le_refl _

lemma top_le_iff (a : ℤt) : ⊤ ≤ a ↔ a = ⊤ := by
  constructor
  · intro h
    obtain (rfl|⟨a, rfl⟩|rfl) := a.three_cases
    · simp at h
    · simp at h
    · rfl
  · rintro rfl
    exact le_refl _

end ℤt
