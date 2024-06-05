/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Topology.Instances.ENNReal

#align_import order.filter.ennreal from "leanprover-community/mathlib"@"52932b3a083d4142e78a15dc928084a22fea9ba0"

/-!
# Order properties of extended non-negative reals

This file compiles filter-related results about `ℝ≥0∞` (see Data/Real/ENNReal.lean).
-/


open Filter ENNReal

namespace ENNReal

variable {α : Type*} {f : Filter α}

theorem eventually_le_limsup [CountableInterFilter f] (u : α → ℝ≥0∞) :
    ∀ᶠ y in f, u y ≤ f.limsup u :=
  _root_.eventually_le_limsup
#align ennreal.eventually_le_limsup ENNReal.eventually_le_limsup

theorem limsup_eq_zero_iff [CountableInterFilter f] {u : α → ℝ≥0∞} :
    f.limsup u = 0 ↔ u =ᶠ[f] 0 :=
  limsup_eq_bot
#align ennreal.limsup_eq_zero_iff ENNReal.limsup_eq_zero_iff

theorem limsup_const_mul_of_ne_top {u : α → ℝ≥0∞} {a : ℝ≥0∞} (ha_top : a ≠ ⊤) :
    (f.limsup fun x : α => a * u x) = a * f.limsup u := by
  by_cases ha_zero : a = 0
  · simp_rw [ha_zero, zero_mul, ← ENNReal.bot_eq_zero]
    exact limsup_const_bot
  let g := fun x : ℝ≥0∞ => a * x
  have hg_bij : Function.Bijective g :=
    Function.bijective_iff_has_inverse.mpr
      ⟨fun x => a⁻¹ * x,
        ⟨fun x => by simp [g, ← mul_assoc, ENNReal.inv_mul_cancel ha_zero ha_top], fun x => by
          simp [g, ← mul_assoc, ENNReal.mul_inv_cancel ha_zero ha_top]⟩⟩
  have hg_mono : StrictMono g :=
    Monotone.strictMono_of_injective (fun _ _ _ => by rwa [mul_le_mul_left ha_zero ha_top]) hg_bij.1
  let g_iso := StrictMono.orderIsoOfSurjective g hg_mono hg_bij.2
  exact (OrderIso.limsup_apply g_iso).symm
#align ennreal.limsup_const_mul_of_ne_top ENNReal.limsup_const_mul_of_ne_top

theorem limsup_const_mul [CountableInterFilter f] {u : α → ℝ≥0∞} {a : ℝ≥0∞} :
    f.limsup (a * u ·) = a * f.limsup u := by
  by_cases ha_top : a ≠ ⊤
  · exact limsup_const_mul_of_ne_top ha_top
  push_neg at ha_top
  by_cases hu : u =ᶠ[f] 0
  · have hau : (a * u ·) =ᶠ[f] 0 := hu.mono fun x hx => by simp [hx]
    simp only [limsup_congr hu, limsup_congr hau, Pi.zero_apply, ← ENNReal.bot_eq_zero,
      limsup_const_bot]
    simp
  · have hu_mul : ∃ᶠ x : α in f, ⊤ ≤ ite (u x = 0) (0 : ℝ≥0∞) ⊤ := by
      rw [EventuallyEq, not_eventually] at hu
      refine hu.mono fun x hx => ?_
      rw [Pi.zero_apply] at hx
      simp [hx]
    have h_top_le : (f.limsup fun x : α => ite (u x = 0) (0 : ℝ≥0∞) ⊤) = ⊤ :=
      eq_top_iff.mpr (le_limsup_of_frequently_le hu_mul)
    have hfu : f.limsup u ≠ 0 := mt limsup_eq_zero_iff.1 hu
    simp only [ha_top, top_mul', h_top_le, hfu, ite_false]
#align ennreal.limsup_const_mul ENNReal.limsup_const_mul

theorem limsup_mul_le [CountableInterFilter f] (u v : α → ℝ≥0∞) :
    f.limsup (u * v) ≤ f.limsup u * f.limsup v :=
  calc
    f.limsup (u * v) ≤ f.limsup fun x => f.limsup u * v x := by
      refine limsup_le_limsup ?_
      filter_upwards [@eventually_le_limsup _ f _ u] with x hx using mul_le_mul' hx le_rfl
    _ = f.limsup u * f.limsup v := limsup_const_mul
#align ennreal.limsup_mul_le ENNReal.limsup_mul_le

theorem limsup_add_le [CountableInterFilter f] (u v : α → ℝ≥0∞) :
    f.limsup (u + v) ≤ f.limsup u + f.limsup v :=
  sInf_le ((eventually_le_limsup u).mp
    ((eventually_le_limsup v).mono fun _ hxg hxf => add_le_add hxf hxg))
#align ennreal.limsup_add_le ENNReal.limsup_add_le

theorem limsup_liminf_le_liminf_limsup {β} [Countable β] {f : Filter α} [CountableInterFilter f]
    {g : Filter β} (u : α → β → ℝ≥0∞) :
    (f.limsup fun a : α => g.liminf fun b : β => u a b) ≤
      g.liminf fun b => f.limsup fun a => u a b :=
  have h1 : ∀ᶠ a in f, ∀ b, u a b ≤ f.limsup fun a' => u a' b := by
    rw [eventually_countable_forall]
    exact fun b => ENNReal.eventually_le_limsup fun a => u a b
  sInf_le <| h1.mono fun x hx => Filter.liminf_le_liminf (Filter.eventually_of_forall hx)
#align ennreal.limsup_liminf_le_liminf_limsup ENNReal.limsup_liminf_le_liminf_limsup

end ENNReal
