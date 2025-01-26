/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fintype.Basic

/-!
# The order isomorphism `Fin (n + 1) ≃o {i}ᶜ`

Given `i : Fin (n + 2)`, we show that `Fin.succAboveOrderEmb` induces
an order isomorphism `Fin (n + 1) ≃o ({i}ᶜ : Finset (Fin (n + 2)))`.

-/

open Finset

noncomputable def Fin.succAboveOrderIso {n : ℕ} (i : Fin (n + 2)) :
    Fin (n + 1) ≃o ({i}ᶜ : Finset (Fin (n + 2))) where
  toEquiv :=
    Equiv.ofBijective (f := fun a ↦ ⟨Fin.succAboveOrderEmb i a,
        by simpa using Fin.succAbove_ne i a⟩) (by
      constructor
      · intro a b h
        exact (Fin.succAboveOrderEmb i).injective (by simpa using h)
      · rintro ⟨j, hj⟩
        simp only [mem_compl, mem_singleton] at hj
        by_cases h : j < i
        · refine ⟨j.castPred ?_, ?_⟩
          · rintro rfl
            simp only [Fin.lt_iff_val_lt_val, Fin.val_last] at h
            simp only [Fin.ext_iff, Fin.val_last] at hj
            omega
          · dsimp
            rw [Subtype.mk.injEq, Fin.succAbove_of_castSucc_lt _ _ h,
              Fin.castSucc_castPred]
        · refine ⟨j.pred ?_, ?_⟩
          · rintro rfl
            obtain rfl : i = 0 := by simpa using h
            simp at hj
          · dsimp
            rw [Subtype.mk.injEq, Fin.succAbove_of_le_castSucc, Fin.succ_pred]
            rw [Fin.le_iff_val_le_val, Fin.coe_castSucc, Fin.coe_pred]
            omega )
  map_rel_iff' {a b} := by
    simp only [Equiv.ofBijective_apply, Subtype.mk_le_mk, OrderEmbedding.le_iff_le]
