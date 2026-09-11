module -- shake: keep-all

public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Logic.Equiv.Set

deprecated_module (since := "2026-08-26")

public section

namespace Fin

@[deprecated Equiv.apply_ofInjective_symm (since := "2026-08-26")]
theorem coe_of_injective_castLE_symm {n k : ℕ} (h : n ≤ k) (i : Fin k) (hi) :
    ((Equiv.ofInjective _ (castLE_injective h)).symm ⟨i, hi⟩ : ℕ) = i := by
  rw [← val_castLE h, Equiv.apply_ofInjective_symm _ ⟨i, hi⟩]

@[deprecated Equiv.apply_ofInjective_symm (since := "2026-08-26")]
theorem coe_of_injective_castSucc_symm {n : ℕ} (i : Fin n.succ) (hi) :
    ((Equiv.ofInjective castSucc (castSucc_injective _)).symm ⟨i, hi⟩ : ℕ) = i := by
  rw [← val_castSucc, Equiv.apply_ofInjective_symm _ ⟨i, hi⟩]

end Fin
