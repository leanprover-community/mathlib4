/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Data.List.Chain
import Mathlib.Data.List.OfFn

/-!
# Lemmas about `IsChain` and `ofFn`

This file provides lemmas involving both `List.IsChain` and `List.ofFn`.
-/

open Nat

namespace List

lemma isChain_ofFn {α : Type*} {n : ℕ} {f : Fin n → α} {r : α → α → Prop} :
    (ofFn f).IsChain r ↔ ∀ (i) (hi : i + 1 < n), r (f ⟨i, lt_of_succ_lt hi⟩) (f ⟨i + 1, hi⟩) := by
  simp_rw [isChain_iff_get, get_ofFn, length_ofFn]
  exact ⟨fun h i hi ↦ h i (by cutsat), fun h i hi ↦ h i (by cutsat)⟩

@[deprecated (since := "2025-09-24")] alias chain'_ofFn := isChain_ofFn

end List
