/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Data.W.Basic
import Mathlib.SetTheory.Cardinal.Ordinal

#align_import data.W.cardinal from "leanprover-community/mathlib"@"6eeb941cf39066417a09b1bbc6e74761cadfcb1a"

/-!
# Cardinality of W-types

This file proves some theorems about the cardinality of W-types. The main result is
`cardinal_mk_le_max_aleph0_of_finite` which says that if for any `a : α`,
`β a` is finite, then the cardinality of `WType β` is at most the maximum of the
cardinality of `α` and `ℵ₀`.
This can be used to prove theorems about the cardinality of algebraic constructions such as
polynomials. There is a surjection from a `WType` to `MvPolynomial` for example, and
this surjection can be used to put an upper bound on the cardinality of `MvPolynomial`.

## Tags

W, W type, cardinal, first order
-/


universe u

variable {α : Type u} {β : α → Type u}

noncomputable section

namespace WType

open Cardinal

-- porting note: `W` is a special name, exceptionally in upper case in Lean3
set_option linter.uppercaseLean3 false

theorem cardinal_mk_eq_sum : #(WType β) = sum (fun a : α => #(WType β) ^ #(β a)) := by
  simp only [Cardinal.power_def, ← Cardinal.mk_sigma]
  -- ⊢ #(WType β) = #((i : α) × (β i → WType β))
  exact mk_congr (equivSigma β)
  -- 🎉 no goals
#align W_type.cardinal_mk_eq_sum WType.cardinal_mk_eq_sum

/-- `#(WType β)` is the least cardinal `κ` such that `sum (λ a : α, κ ^ #(β a)) ≤ κ` -/
theorem cardinal_mk_le_of_le {κ : Cardinal.{u}} (hκ : (sum fun a : α => κ ^ #(β a)) ≤ κ) :
    #(WType β) ≤ κ := by
  induction' κ using Cardinal.inductionOn with γ
  -- ⊢ #(WType β) ≤ #γ
  simp only [Cardinal.power_def, ← Cardinal.mk_sigma, Cardinal.le_def] at hκ
  -- ⊢ #(WType β) ≤ #γ
  cases' hκ with hκ
  -- ⊢ #(WType β) ≤ #γ
  exact Cardinal.mk_le_of_injective (elim_injective _ hκ.1 hκ.2)
  -- 🎉 no goals
#align W_type.cardinal_mk_le_of_le WType.cardinal_mk_le_of_le

/-- If, for any `a : α`, `β a` is finite, then the cardinality of `WType β`
  is at most the maximum of the cardinality of `α` and `ℵ₀`  -/
theorem cardinal_mk_le_max_aleph0_of_finite [∀ a, Finite (β a)] : #(WType β) ≤ max #α ℵ₀ :=
  (isEmpty_or_nonempty α).elim
    (by
      intro h
      -- ⊢ #(WType β) ≤ max #α ℵ₀
      rw [Cardinal.mk_eq_zero (WType β)]
      -- ⊢ 0 ≤ max #α ℵ₀
      exact zero_le _)
      -- 🎉 no goals
    fun hn =>
    let m := max #α ℵ₀
    cardinal_mk_le_of_le <|
      calc
        (Cardinal.sum fun a => m ^ #(β a)) ≤ #α * ⨆ a, m ^ #(β a) := Cardinal.sum_le_iSup _
        _ ≤ m * ⨆ a, m ^ #(β a) := mul_le_mul' (le_max_left _ _) le_rfl
        _ = m :=
          mul_eq_left.{u} (le_max_right _ _)
              (ciSup_le' fun i => pow_le (le_max_right _ _) (lt_aleph0_of_finite _)) <|
            pos_iff_ne_zero.1 <|
              Order.succ_le_iff.1
                (by
                  rw [succ_zero]
                  -- ⊢ 1 ≤ ⨆ (a : α), m ^ #(β a)
                  obtain ⟨a⟩ : Nonempty α := hn
                  -- ⊢ 1 ≤ ⨆ (a : α), m ^ #(β a)
                  refine' le_trans _ (le_ciSup (bddAbove_range.{u, u} _) a)
                  -- ⊢ 1 ≤ m ^ #(β a)
                  rw [← power_zero]
                  -- ⊢ ?m.2506 ^ 0 ≤ m ^ #(β a)
                  exact
                    power_le_power_left
                      (pos_iff_ne_zero.1 (aleph0_pos.trans_le (le_max_right _ _))) (zero_le _))
#align W_type.cardinal_mk_le_max_aleph_0_of_finite WType.cardinal_mk_le_max_aleph0_of_finite

end WType
