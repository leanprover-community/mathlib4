import Mathlib.Data.FinEnum
import Mathlib.Logic.Equiv.Fin
import Mathlib.Data.ULift

namespace FinEnum
universe u v

instance instEquivFin0Empty : ULift.{u} (Fin Nat.zero) ≃ PEmpty.{u + 1} :=
  Equiv.trans (Equiv.ulift) $ Equiv.equivOfIsEmpty _ PEmpty.{u+1}

instance instEquivFinNSuccOptionFinN (n:ℕ) : 
    ULift.{u} (Fin n.succ) ≃ (Option $ ULift.{u} (Fin n)) :=
  Equiv.trans
    (Equiv.ulift)
    (Equiv.trans (finSuccEquivLast) (Equiv.optionCongr Equiv.ulift.symm))

instance instFinEnumOptionOfFinEnum (α : Type u) [FinEnum α] :
    FinEnum $ Option α :=
  FinEnum.ofEquiv _ (Equiv.optionEquivSumPUnit.{u,0} α)

def recEmptyOption
  {P : (α : Type u) → [FinEnum α] → Sort v}
  (of_equiv : {α β : Type u} → [FinEnum α] → [FinEnum β] → α ≃ β → P α → P β)
  (h_empty : P PEmpty.{u + 1})
  (h_option : {α : Type u} → [FinEnum α] → P α → P (Option α))
  (α : Type u) [aenum : FinEnum α] : P α := by
  have ⟨card, cardeq⟩ : (n : ℕ) ×' (aenum.card = n) := ⟨aenum.card, rfl⟩
  induction card generalizing α
  case zero =>
    have fzeroeq := Equiv.trans (Equiv.ulift.{u}) (cardeq ▸ aenum.equiv.symm)
    have emptyeq := instEquivFin0Empty.{u}
    have fzerofe := FinEnum.ofEquiv _ emptyeq
    exact of_equiv fzeroeq $ of_equiv emptyeq.symm h_empty
  case succ n ih =>
    have ⟨fe, fecardeq⟩ : (e : FinEnum $ ULift.{u} $ Fin n) ×' (e.card = n)
      := ⟨FinEnum.mk n Equiv.ulift.{u}, rfl⟩
    have fsucceq := Equiv.trans (Equiv.ulift.{u}) (cardeq ▸ aenum.equiv.symm)
    have optioeq := (instEquivFinNSuccOptionFinN.{u} n)
    have opsumeq := Equiv.optionEquivSumPUnit.{u,u} (ULift $ Fin n)
    have fssumeq := Equiv.trans optioeq opsumeq
    have fssumfe := @FinEnum.sum _ _ fe FinEnum.punit.{u}
    have fsuccfe := FinEnum.ofEquiv _ fssumeq
    exact of_equiv fsucceq $ of_equiv optioeq.symm
      $ h_option (@ih (ULift.{u} $ Fin n) fe fecardeq)
