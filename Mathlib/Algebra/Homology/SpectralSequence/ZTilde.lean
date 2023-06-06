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

/-lemma isInitial_bot : IsInitial (⊥ : ℤt) :=
  @isInitialBot (WithTop (WithBot ℤ)) _  _

lemma isTerminal_top : IsTerminal (⊤ : ℤt) :=
  @isTerminalTop (WithTop (WithBot ℤ)) _ _

instance : HasTerminal ℤt := isTerminal_top.hasTerminal
instance : HasInitial ℤt := isInitial_bot.hasInitial-/

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
lemma mk_le_mk_iff (a b : ℤ) :
    mk a ≤ mk b ↔ a ≤ b := some_some_le_some_some_iff a b

instance : OrderTop ℤt := by dsimp [ℤt] ; infer_instance
instance : OrderBot ℤt := by dsimp [ℤt] ; infer_instance

end ℤt
