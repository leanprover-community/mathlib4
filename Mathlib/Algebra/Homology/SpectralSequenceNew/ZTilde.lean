import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

open CategoryTheory Limits

def ℤt := WithTop (WithBot ℤ)

namespace ℤt

instance : Preorder ℤt := by
  dsimp [ℤt]
  infer_instance

def mk (a : ℤ) : ℤt := ((a : WithBot ℤ) : WithTop (WithBot ℤ))

lemma mk_monotone : Monotone ℤt.mk := by
  intro a b h
  dsimp [mk]
  rw [WithTop.coe_le_coe, WithBot.coe_le_coe]
  exact h

@[simps! obj map]
def _root_.ιℤt  : ℤ ⥤ ℤt := ℤt.mk_monotone.functor

instance {α : Type _} [Preorder α] (a : α) : IsIso (homOfLE (le_refl a)) :=
  IsIso.of_iso (Iso.refl a)

@[simp]
lemma some_le_some_none_iff (a : ℤ) :
    @LE.le ℤt _ (some (some a)) (some none) ↔ False := by
  simp only [iff_false]
  erw [WithTop.coe_le_coe]
  apply WithBot.not_coe_le_bot

@[simp]
lemma none_le_some_iff (a : WithBot ℤ) :
    @LE.le ℤt _ none (some a) ↔ False := by
  simp only [iff_false]
  apply WithTop.not_top_le_coe

@[simp]
lemma some_some_le_some_some_iff (a b : ℤ) :
    @LE.le ℤt _ (some (some a)) (some (some b)) ↔ a ≤ b := by
  erw [WithTop.coe_le_coe, WithBot.coe_le_coe]

@[simp]
lemma some_some_lt_some_some_iff (a b : ℤ) :
    @LT.lt ℤt _ (some (some a)) (some (some b)) ↔ a < b := by
  erw [WithTop.coe_lt_coe, WithBot.coe_lt_coe]

@[simp]
lemma mk_le_mk_iff (a b : ℤ) :
    mk a ≤ mk b ↔ a ≤ b := some_some_le_some_some_iff a b

@[simp]
lemma mk_lt_mk_iff (a b : ℤ) :
    mk a < mk b ↔ a < b := some_some_lt_some_some_iff a b

instance : OrderTop ℤt := by dsimp [ℤt] ; infer_instance
instance : OrderBot ℤt := by dsimp [ℤt] ; infer_instance

@[simp]
lemma le_bot_mk_iff (a : ℤ) :
    ℤt.mk a ≤ ⊥ ↔ False := some_le_some_none_iff a

@[simp]
lemma top_le_mk_iff (a : ℤ) :
    ⊤ ≤ ℤt.mk a ↔ False := none_le_some_iff a

@[simp]
lemma top_le_bot_iff  :
    (⊤ : ℤt) ≤ ⊥ ↔ False := by
  simp only [iff_false]
  apply WithTop.not_top_le_coe

lemma three_cases (x : ℤt) :
    x = ⊥ ∨ (∃ (n : ℤ), x = ℤt.mk n) ∨ x = ⊤ := by
  obtain (_|_|n) := x
  · exact Or.inr (Or.inr rfl)
  · exact Or.inl rfl
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
    · simp [le_bot_iff] at h
      exact h.symm
    · simp at h
    · rfl
  · rintro rfl
    exact le_refl _

end ℤt
