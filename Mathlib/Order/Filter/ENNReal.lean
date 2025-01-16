/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Topology.Instances.ENNReal.Defs
import Mathlib.Topology.Algebra.Order.LiminfLimsup

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

theorem limsup_eq_zero_iff [CountableInterFilter f] {u : α → ℝ≥0∞} :
    f.limsup u = 0 ↔ u =ᶠ[f] 0 :=
  limsup_eq_bot

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

theorem limsup_const_mul [CountableInterFilter f] {u : α → ℝ≥0∞} {a : ℝ≥0∞} :
    f.limsup (a * u ·) = a * f.limsup u := by
  by_cases ha_top : a ≠ ⊤
  · exact limsup_const_mul_of_ne_top ha_top
  push_neg at ha_top
  by_cases hu : u =ᶠ[f] 0
  · have hau : (a * u ·) =ᶠ[f] 0 := hu.mono fun x hx => by simp [hx]
    simp only [limsup_congr hu, limsup_congr hau, Pi.zero_def, ← ENNReal.bot_eq_zero,
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

/-- See also `limsup_mul_le'`.-/
theorem limsup_mul_le [CountableInterFilter f] (u v : α → ℝ≥0∞) :
    f.limsup (u * v) ≤ f.limsup u * f.limsup v :=
  calc
    f.limsup (u * v) ≤ f.limsup fun x => f.limsup u * v x := by
      refine limsup_le_limsup ?_
      filter_upwards [@eventually_le_limsup _ f _ u] with x hx using mul_le_mul' hx le_rfl
    _ = f.limsup u * f.limsup v := limsup_const_mul

theorem limsup_add_le [CountableInterFilter f] (u v : α → ℝ≥0∞) :
    f.limsup (u + v) ≤ f.limsup u + f.limsup v :=
  sInf_le ((eventually_le_limsup u).mp
    ((eventually_le_limsup v).mono fun _ hxg hxf => add_le_add hxf hxg))

theorem limsup_liminf_le_liminf_limsup {β} [Countable β] {f : Filter α} [CountableInterFilter f]
    {g : Filter β} (u : α → β → ℝ≥0∞) :
    (f.limsup fun a : α => g.liminf fun b : β => u a b) ≤
      g.liminf fun b => f.limsup fun a => u a b :=
  have h1 : ∀ᶠ a in f, ∀ b, u a b ≤ f.limsup fun a' => u a' b := by
    rw [eventually_countable_forall]
    exact fun b => ENNReal.eventually_le_limsup fun a => u a b
  sInf_le <| h1.mono fun x hx => Filter.liminf_le_liminf (Filter.Eventually.of_forall hx)

end ENNReal

namespace Real

open ENNReal NNReal

/-- If `u v : ℕ → ℝ` are nonnegative and bounded above, then
  `filter.limsup (u * v) at_top ≤ filter.limsup u at_top * filter.limsup v at_top `.-/
theorem limsup_mul_le {u v : ℕ → ℝ} (hu_bdd : BddAbove (Set.range u)) (hu0 : 0 ≤ u)
    (hv_bdd : BddAbove (Set.range v)) (hv0 : 0 ≤ v) :
    Filter.limsup (u * v) atTop ≤ Filter.limsup u atTop * Filter.limsup v atTop := by
  have h_bdd : BddAbove (Set.range (u * v)) := bddAbove_range_mul hu_bdd hu0 hv_bdd hv0
  rw [NNReal.coe_limsup (mul_nonneg hu0 hv0), NNReal.coe_limsup hu0, NNReal.coe_limsup hv0,
    ← NNReal.coe_mul, NNReal.coe_le_coe, ← ENNReal.coe_le_coe, ENNReal.coe_mul,
    ENNReal.coe_limsup (bddAbove' _ h_bdd), ENNReal.coe_limsup (bddAbove' hu0 hu_bdd),
    ENNReal.coe_limsup (bddAbove' hv0 hv_bdd)]
  obtain ⟨Bu, hBu⟩ := hu_bdd
  obtain ⟨Bv, hBv⟩ := hv_bdd
  simp only [mem_upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    at hBu hBv
  have hBu' : ∀ n : ℕ, ⟨u n, hu0 n⟩ ≤ Real.toNNReal Bu := fun n ↦ by
    rw [← NNReal.coe_le_coe, coe_mk, coe_toNNReal', le_max_iff]
    exact Or.inl (hBu n)
  have hBv' : ∀ n : ℕ, ⟨v n, hv0 n⟩ ≤ Real.toNNReal Bv := fun n ↦ by
    rw [← NNReal.coe_le_coe, coe_mk, coe_toNNReal', le_max_iff]
    exact Or.inl (hBv n)
  simp_rw [← ENNReal.coe_le_coe] at hBu' hBv'
  apply ENNReal.limsup_mul_le' (Or.inr (ne_top_of_le_ne_top coe_ne_top
      (le_trans limsup_le_iSup (iSup_le hBv')))) (Or.inl (ne_top_of_le_ne_top coe_ne_top
      (le_trans limsup_le_iSup (iSup_le hBu'))))

end Real
