/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne

! This file was ported from Lean 3 source module order.filter.ennreal
! leanprover-community/mathlib commit 11c2b8c18d1a8e44fe9ba8ba6b931d51b4734150
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Real.Ennreal
import Mathbin.Order.Filter.CountableInter
import Mathbin.Order.LiminfLimsup

/-!
# Order properties of extended non-negative reals

This file compiles filter-related results about `ℝ≥0∞` (see data/real/ennreal.lean).
-/


open Filter

open Filter Ennreal

namespace Ennreal

variable {α : Type _} {f : Filter α}

theorem eventually_le_limsup [CountableInterFilter f] (u : α → ℝ≥0∞) :
    ∀ᶠ y in f, u y ≤ f.limsup u :=
  by
  by_cases hx_top : f.limsup u = ⊤
  · simp_rw [hx_top]
    exact eventually_of_forall fun a => le_top
  have h_forall_le : ∀ᶠ y in f, ∀ n : ℕ, u y < f.limsup u + (1 : ℝ≥0∞) / n :=
    by
    rw [eventually_countable_forall]
    refine' fun n => eventually_lt_of_limsup_lt _
    nth_rw 1 [← add_zero (f.limsup u)]
    exact (Ennreal.add_lt_add_iff_left hx_top).mpr (by simp)
  refine' h_forall_le.mono fun y hy => le_of_forall_pos_le_add fun r hr_pos hx_top => _
  have hr_ne_zero : (r : ℝ≥0∞) ≠ 0 := by
    rw [Ne.def, coe_eq_zero]
    exact (ne_of_lt hr_pos).symm
  cases' exists_inv_nat_lt hr_ne_zero with i hi
  rw [inv_eq_one_div] at hi
  exact (hy i).le.trans (add_le_add_left hi.le (f.limsup u))
#align ennreal.eventually_le_limsup Ennreal.eventually_le_limsup

theorem limsup_eq_zero_iff [CountableInterFilter f] {u : α → ℝ≥0∞} : f.limsup u = 0 ↔ u =ᶠ[f] 0 :=
  by
  constructor <;> intro h
  · have hu_zero :=
      eventually_le.trans (eventually_le_limsup u) (eventually_of_forall fun _ => le_of_eq h)
    exact hu_zero.mono fun x hx => le_antisymm hx (zero_le _)
  · rw [limsup_congr h]
    simp_rw [Pi.zero_apply, ← Ennreal.bot_eq_zero, limsup_const_bot]
#align ennreal.limsup_eq_zero_iff Ennreal.limsup_eq_zero_iff

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic filter.is_bounded_default -/
theorem limsup_const_mul_of_ne_top {u : α → ℝ≥0∞} {a : ℝ≥0∞} (ha_top : a ≠ ⊤) :
    (f.limsup fun x : α => a * u x) = a * f.limsup u :=
  by
  by_cases ha_zero : a = 0
  · simp_rw [ha_zero, zero_mul, ← Ennreal.bot_eq_zero]
    exact limsup_const_bot
  let g := fun x : ℝ≥0∞ => a * x
  have hg_bij : Function.Bijective g :=
    function.bijective_iff_has_inverse.mpr
      ⟨fun x => a⁻¹ * x,
        ⟨fun x => by simp [← mul_assoc, Ennreal.inv_mul_cancel ha_zero ha_top], fun x => by
          simp [g, ← mul_assoc, Ennreal.mul_inv_cancel ha_zero ha_top]⟩⟩
  have hg_mono : StrictMono g :=
    Monotone.strictMono_of_injective (fun _ _ _ => by rwa [mul_le_mul_left ha_zero ha_top]) hg_bij.1
  let g_iso := StrictMono.orderIsoOfSurjective g hg_mono hg_bij.2
  refine' (OrderIso.limsup_apply g_iso _ _ _ _).symm
  all_goals
    run_tac
      is_bounded_default
#align ennreal.limsup_const_mul_of_ne_top Ennreal.limsup_const_mul_of_ne_top

theorem limsup_const_mul [CountableInterFilter f] {u : α → ℝ≥0∞} {a : ℝ≥0∞} :
    (f.limsup fun x : α => a * u x) = a * f.limsup u :=
  by
  by_cases ha_top : a ≠ ⊤
  · exact limsup_const_mul_of_ne_top ha_top
  push_neg  at ha_top
  by_cases hu : u =ᶠ[f] 0
  · have hau : (fun x => a * u x) =ᶠ[f] 0 :=
      by
      refine' hu.mono fun x hx => _
      rw [Pi.zero_apply] at hx
      simp [hx]
    simp only [limsup_congr hu, limsup_congr hau, Pi.zero_apply, ← bot_eq_zero, limsup_const_bot]
    simp
  · simp_rw [ha_top, top_mul]
    have hu_mul : ∃ᶠ x : α in f, ⊤ ≤ ite (u x = 0) (0 : ℝ≥0∞) ⊤ :=
      by
      rw [eventually_eq, not_eventually] at hu
      refine' hu.mono fun x hx => _
      rw [Pi.zero_apply] at hx
      simp [hx]
    have h_top_le : (f.limsup fun x : α => ite (u x = 0) (0 : ℝ≥0∞) ⊤) = ⊤ :=
      eq_top_iff.mpr (le_limsup_of_frequently_le hu_mul)
    have hfu : f.limsup u ≠ 0 := mt limsup_eq_zero_iff.1 hu
    simp only [h_top_le, hfu, if_false]
#align ennreal.limsup_const_mul Ennreal.limsup_const_mul

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic filter.is_bounded_default -/
theorem limsup_mul_le [CountableInterFilter f] (u v : α → ℝ≥0∞) :
    f.limsup (u * v) ≤ f.limsup u * f.limsup v :=
  calc
    f.limsup (u * v) ≤ f.limsup fun x => f.limsup u * v x :=
      by
      refine' limsup_le_limsup _ _
      · filter_upwards [@eventually_le_limsup _ f _ u]with x hx
        exact Ennreal.mul_le_mul hx le_rfl
      ·
        run_tac
          is_bounded_default
    _ = f.limsup u * f.limsup v := limsup_const_mul
    
#align ennreal.limsup_mul_le Ennreal.limsup_mul_le

theorem limsup_add_le [CountableInterFilter f] (u v : α → ℝ≥0∞) :
    f.limsup (u + v) ≤ f.limsup u + f.limsup v :=
  infₛ_le
    ((eventually_le_limsup u).mp
      ((eventually_le_limsup v).mono fun _ hxg hxf => add_le_add hxf hxg))
#align ennreal.limsup_add_le Ennreal.limsup_add_le

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic filter.is_bounded_default -/
theorem limsup_liminf_le_liminf_limsup {β} [Countable β] {f : Filter α} [CountableInterFilter f]
    {g : Filter β} (u : α → β → ℝ≥0∞) :
    (f.limsup fun a : α => g.liminf fun b : β => u a b) ≤
      g.liminf fun b => f.limsup fun a => u a b :=
  by
  have h1 : ∀ᶠ a in f, ∀ b, u a b ≤ f.limsup fun a' => u a' b :=
    by
    rw [eventually_countable_forall]
    exact fun b => Ennreal.eventually_le_limsup fun a => u a b
  refine' infₛ_le (h1.mono fun x hx => Filter.liminf_le_liminf (Filter.eventually_of_forall hx) _)
  run_tac
    filter.is_bounded_default
#align ennreal.limsup_liminf_le_liminf_limsup Ennreal.limsup_liminf_le_liminf_limsup

end Ennreal

