/-
Copyright (c) 2026 Matthew W. Horn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew W. Horn
-/
module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-! # Erlang's loss formula

`Real.erlangB a c` is Erlang's loss formula `B(c, a)`: the blocking probability of a loss system
with `c` servers at offered load `a`. It is defined by the recursion

`B(0, a) = 1`, `B(c + 1, a) = a * B(c, a) / (c + 1 + a * B(c, a))`,

which is the form classically used for computation, since it avoids the factorials and powers
of the closed form `(a ^ c / c!) / ∑ j ≤ c, a ^ j / j!`. `Real.erlangB_eq_div` proves the two
agree.

## Main definitions

* `Real.erlangB a c`: Erlang's loss formula, by the recursion.

## Main results

For every result below, `0 ≤ a`.

* `Real.erlangB_eq_div`: the recursion equals the closed form.
* `Real.erlangB_mem_Icc`: `Real.erlangB a c` lies in `[0, 1]`.
* `Real.erlangB_antitone`: `Real.erlangB a` is antitone in the server count.
* `Real.erlangB_mono_load`: `Real.erlangB · c` is monotone in the offered load.
* `Real.erlangB_carried_le`: the carried load `a * (1 - Real.erlangB a c)` never exceeds `c`.

## References

The recursion and its equality with the closed form are classical; see for example
[R. B. Cooper, *Introduction to queueing theory*][cooper1981].

## Tags

Erlang, loss formula, blocking probability
-/

open Finset

@[expose] public section

namespace Real

/-- Erlang's loss formula `B(c, a)`, by the recursion `B(0) = 1`,
`B(c + 1) = a * B(c) / (c + 1 + a * B(c))`. Total on all of `ℝ`; the results assume `0 ≤ a`,
which makes the denominator at least `c + 1` (`erlangB_denom_pos`). -/
noncomputable def erlangB (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | c + 1 => a * erlangB a c / ((c : ℝ) + 1 + a * erlangB a c)

/-- With no servers, everything is blocked. -/
@[simp] theorem erlangB_zero (a : ℝ) : erlangB a 0 = 1 := rfl

/-- The recursion step of `erlangB`, as an equation. -/
theorem erlangB_succ (a : ℝ) (c : ℕ) :
    erlangB a (c + 1) = a * erlangB a c / ((c : ℝ) + 1 + a * erlangB a c) := rfl

theorem erlangB_nonneg {a : ℝ} (ha : 0 ≤ a) : ∀ c : ℕ, 0 ≤ erlangB a c
  | 0 => zero_le_one
  | c + 1 => by
    have hx : 0 ≤ a * erlangB a c := mul_nonneg ha (erlangB_nonneg ha c)
    have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    rw [erlangB_succ]
    exact div_nonneg hx (by linarith)

/-- The denominator of the `erlangB` recursion is positive. -/
theorem erlangB_denom_pos {a : ℝ} (ha : 0 ≤ a) (c : ℕ) :
    0 < (c : ℝ) + 1 + a * erlangB a c := by
  have hx : 0 ≤ a * erlangB a c := mul_nonneg ha (erlangB_nonneg ha c)
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  linarith

theorem erlangB_le_one {a : ℝ} (ha : 0 ≤ a) (c : ℕ) : erlangB a c ≤ 1 := by
  cases c with
  | zero => exact le_rfl
  | succ c =>
    have hx : 0 ≤ a * erlangB a c := mul_nonneg ha (erlangB_nonneg ha c)
    have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    rw [erlangB_succ, div_le_one (erlangB_denom_pos ha c)]
    linarith

/-- `erlangB a c` is a probability. -/
theorem erlangB_mem_Icc {a : ℝ} (ha : 0 ≤ a) (c : ℕ) : erlangB a c ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨erlangB_nonneg ha c, erlangB_le_one ha c⟩

/-- The carried load never exceeds the server count: `a * (1 - erlangB a c) ≤ c`. -/
theorem erlangB_carried_le {a : ℝ} (ha : 0 ≤ a) : ∀ c : ℕ, a * (1 - erlangB a c) ≤ c
  | 0 => by simp
  | c + 1 => by
    have ih := erlangB_carried_le ha c
    have hB0 := erlangB_nonneg ha c
    have hD := erlangB_denom_pos ha c
    have hDne : ((c : ℝ) + 1 + a * erlangB a c) ≠ 0 := hD.ne'
    have key : a * (1 - a * erlangB a c / ((c : ℝ) + 1 + a * erlangB a c))
        = a * ((c : ℝ) + 1) / ((c : ℝ) + 1 + a * erlangB a c) := by
      field_simp
      ring
    rw [erlangB_succ, key, div_le_iff₀ hD]
    have haD : a ≤ (c : ℝ) + 1 + a * erlangB a c := by linarith
    have hc1 : (0 : ℝ) ≤ (c : ℝ) + 1 := by positivity
    push_cast
    linarith [mul_le_mul_of_nonneg_left haD hc1]

/-- Adding a server never increases `erlangB`, one step. -/
theorem erlangB_succ_le {a : ℝ} (ha : 0 ≤ a) (c : ℕ) : erlangB a (c + 1) ≤ erlangB a c := by
  have hB0 := erlangB_nonneg ha c
  have hD := erlangB_denom_pos ha c
  have haD : a ≤ (c : ℝ) + 1 + a * erlangB a c := by
    have ih := erlangB_carried_le ha c
    linarith
  rw [erlangB_succ, div_le_iff₀ hD]
  linarith [mul_nonneg hB0 (sub_nonneg.mpr haD)]

/-- `erlangB a` is antitone in the server count. -/
theorem erlangB_antitone {a : ℝ} (ha : 0 ≤ a) : Antitone (erlangB a) :=
  antitone_nat_of_succ_le (erlangB_succ_le ha)

/-- `erlangB · c` is monotone in the offered load. -/
theorem erlangB_mono_load {a a' : ℝ} (ha : 0 ≤ a) (haa' : a ≤ a') :
    ∀ c : ℕ, erlangB a c ≤ erlangB a' c
  | 0 => le_rfl
  | c + 1 => by
    have ih := erlangB_mono_load ha haa' c
    have hB0 := erlangB_nonneg ha c
    have hx : a * erlangB a c ≤ a' * erlangB a' c := mul_le_mul haa' ih hB0 (ha.trans haa')
    have h1 := erlangB_denom_pos ha c
    have h2 := erlangB_denom_pos (ha.trans haa') c
    rw [erlangB_succ, erlangB_succ, div_le_iff₀ h1, div_mul_eq_mul_div, le_div_iff₀ h2]
    have hc1 : (0 : ℝ) ≤ (c : ℝ) + 1 := by positivity
    linarith [mul_le_mul_of_nonneg_right hx hc1]

/-- `erlangB` multiplied against the normalizing sum telescopes to the top term: the
division-free core of `erlangB_eq_div`. -/
theorem erlangB_mul_sum {a : ℝ} (ha : 0 ≤ a) (c : ℕ) :
    erlangB a c * ∑ j ∈ range (c + 1), a ^ j / j.factorial = a ^ c / c.factorial := by
  induction c with
  | zero => norm_num [sum_range_one, Nat.factorial]
  | succ c ih =>
    have hB0 := erlangB_nonneg ha c
    have hD := erlangB_denom_pos ha c
    have hc0 : (c.factorial : ℝ) ≠ 0 := by exact_mod_cast c.factorial_pos.ne'
    have hcpos : (0 : ℝ) < (c : ℝ) + 1 := by positivity
    have hc1 : (c : ℝ) + 1 ≠ 0 := hcpos.ne'
    have hfact : ((c + 1).factorial : ℝ) = ((c : ℝ) + 1) * (c.factorial : ℝ) := by
      push_cast [Nat.factorial_succ]
      ring
    have hT : a ^ (c + 1) / ((c + 1).factorial : ℝ) * ((c : ℝ) + 1)
        = a * (a ^ c / (c.factorial : ℝ)) := by
      rw [hfact, pow_succ]
      field_simp
    rw [sum_range_succ, erlangB_succ, div_mul_eq_mul_div, div_eq_iff hD.ne']
    linear_combination a * ih - hT

/-- The recursion equals the closed form:
`erlangB a c = (a ^ c / c!) / ∑ j ≤ c, a ^ j / j!` for `0 ≤ a`. -/
theorem erlangB_eq_div {a : ℝ} (ha : 0 ≤ a) (c : ℕ) :
    erlangB a c = a ^ c / c.factorial / ∑ j ∈ range (c + 1), a ^ j / j.factorial := by
  have hS : 0 < ∑ j ∈ range (c + 1), a ^ j / j.factorial := by
    refine sum_pos' (fun j _ ↦ div_nonneg (pow_nonneg ha j) (Nat.cast_nonneg _)) ?_
    exact ⟨0, mem_range.mpr c.succ_pos, by norm_num⟩
  rw [eq_div_iff hS.ne']
  exact erlangB_mul_sum ha c

end Real
