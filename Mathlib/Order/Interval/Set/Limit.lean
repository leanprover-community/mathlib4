/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Order.SetIsMax
import Mathlib.Order.SuccPred.Limit

/-!
# Limit elements in Set.Ici

If `J` is a linearly ordered type, `j : J`,
and `m : Set.Ici j` is successor limit, then
`↑m : J` is also successor limit.

-/

universe u

namespace Set.Ici

lemma isSuccLimit_coe {J : Type u} [LinearOrder J] {j : J}
    (m : Set.Ici j) (hm : Order.IsSuccLimit m) :
    Order.IsSuccLimit m.1 :=
  ⟨Set.not_isMin_coe _ hm.1, fun b ↦ by
    simp only [CovBy, not_lt, not_and, not_forall, Classical.not_imp, not_le]
    intro hb
    by_cases hb' : j ≤ b
    · have := hm.2 ⟨b, hb'⟩
      rw [not_covBy_iff (by exact hb)] at this
      obtain ⟨⟨x, h₁⟩, h₂, h₃⟩ := this
      refine ⟨x, h₂, h₃⟩
    · simp only [not_le] at hb'
      refine ⟨j, hb', ?_⟩
      by_contra!
      apply hm.1
      rintro ⟨k, hk⟩ _
      exact this.trans (by simpa using hk)⟩

end Set.Ici
