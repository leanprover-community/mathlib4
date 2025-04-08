/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Data.W.Basic
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Cardinality of W-types

This file proves some theorems about the cardinality of W-types. The main result is
`cardinalMk_le_max_aleph0_of_finite` which says that if for any `a : α`,
`β a` is finite, then the cardinality of `WType β` is at most the maximum of the
cardinality of `α` and `ℵ₀`.
This can be used to prove theorems about the cardinality of algebraic constructions such as
polynomials. There is a surjection from a `WType` to `MvPolynomial` for example, and
this surjection can be used to put an upper bound on the cardinality of `MvPolynomial`.

## Tags

W, W type, cardinal, first order
-/


universe u v

variable {α : Type u} {β : α → Type v}

noncomputable section

namespace WType

open Cardinal


theorem cardinalMk_eq_sum_lift : #(WType β) = sum fun a ↦ #(WType β) ^ lift.{u} #(β a) :=
  (mk_congr <| equivSigma β).trans <| by
    simp_rw [mk_sigma, mk_arrow]; rw [lift_id'.{v, u}, lift_umax.{v, u}]

@[deprecated (since := "2024-11-10")] alias cardinal_mk_eq_sum' := cardinalMk_eq_sum_lift

/-- `#(WType β)` is the least cardinal `κ` such that `sum (fun a : α ↦ κ ^ #(β a)) ≤ κ` -/
theorem cardinalMk_le_of_le' {κ : Cardinal.{max u v}}
    (hκ : (sum fun a : α => κ ^ lift.{u} #(β a)) ≤ κ) :
    #(WType β) ≤ κ := by
  induction' κ using Cardinal.inductionOn with γ
  simp_rw [← lift_umax.{v, u}] at hκ
  nth_rewrite 1 [← lift_id'.{v, u} #γ] at hκ
  simp_rw [← mk_arrow, ← mk_sigma, le_def] at hκ
  obtain ⟨hκ⟩ := hκ
  exact Cardinal.mk_le_of_injective (elim_injective _ hκ.1 hκ.2)

@[deprecated (since := "2024-11-10")] alias cardinal_mk_le_of_le' := cardinalMk_le_of_le'

/-- If, for any `a : α`, `β a` is finite, then the cardinality of `WType β`
is at most the maximum of the cardinality of `α` and `ℵ₀` -/
theorem cardinalMk_le_max_aleph0_of_finite' [∀ a, Finite (β a)] :
    #(WType β) ≤ max (lift.{v} #α) ℵ₀ :=
  (isEmpty_or_nonempty α).elim
    (by
      intro h
      rw [Cardinal.mk_eq_zero (WType β)]
      exact zero_le _)
    fun hn =>
    let m := max (lift.{v} #α) ℵ₀
    cardinalMk_le_of_le' <|
      calc
        (Cardinal.sum fun a => m ^ lift.{u} #(β a)) ≤ lift.{v} #α * ⨆ a, m ^ lift.{u} #(β a) :=
          Cardinal.sum_le_iSup_lift _
        _ ≤ m * ⨆ a, m ^ lift.{u} #(β a) := mul_le_mul' (le_max_left _ _) le_rfl
        _ = m :=
          mul_eq_left (le_max_right _ _)
              (ciSup_le' fun _ => pow_le (le_max_right _ _) (lt_aleph0_of_finite _)) <|
            pos_iff_ne_zero.1 <|
              Order.succ_le_iff.1
                (by
                  rw [succ_zero]
                  obtain ⟨a⟩ : Nonempty α := hn
                  refine le_trans ?_ (le_ciSup (bddAbove_range _) a)
                  rw [← power_zero]
                  exact
                    power_le_power_left
                      (pos_iff_ne_zero.1 (aleph0_pos.trans_le (le_max_right _ _))) (zero_le _))

@[deprecated (since := "2024-11-10")]
alias cardinal_mk_le_max_aleph0_of_finite' := cardinalMk_le_max_aleph0_of_finite'

variable {β : α → Type u}

theorem cardinalMk_eq_sum : #(WType β) = sum (fun a : α => #(WType β) ^ #(β a)) :=
  cardinalMk_eq_sum_lift.trans <| by simp_rw [lift_id]

@[deprecated (since := "2024-11-10")] alias cardinal_mk_eq_sum := cardinalMk_eq_sum

/-- `#(WType β)` is the least cardinal `κ` such that `sum (fun a : α ↦ κ ^ #(β a)) ≤ κ` -/
theorem cardinalMk_le_of_le {κ : Cardinal.{u}} (hκ : (sum fun a : α => κ ^ #(β a)) ≤ κ) :
    #(WType β) ≤ κ := cardinalMk_le_of_le' <| by simp_rw [lift_id]; exact hκ

@[deprecated (since := "2024-11-10")] alias cardinal_mk_le_of_le := cardinalMk_le_of_le

/-- If, for any `a : α`, `β a` is finite, then the cardinality of `WType β`
is at most the maximum of the cardinality of `α` and `ℵ₀` -/
theorem cardinalMk_le_max_aleph0_of_finite [∀ a, Finite (β a)] : #(WType β) ≤ max #α ℵ₀ :=
  cardinalMk_le_max_aleph0_of_finite'.trans_eq <| by rw [lift_id]

@[deprecated (since := "2024-11-10")]
alias cardinal_mk_le_max_aleph0_of_finite := cardinalMk_le_max_aleph0_of_finite

end WType
