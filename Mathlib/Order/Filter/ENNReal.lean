/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Metrizable.Real

/-!
# Limsup and liminf of reals

This file compiles filter-related results about `ℝ`, `ℝ≥0` and `ℝ≥0∞`.
-/


open Filter ENNReal

namespace Real
variable {ι : Type*} {f : Filter ι} {u : ι → ℝ}

@[simp]
lemma limsSup_of_not_isCobounded {f : Filter ℝ} (hf : ¬ f.IsCobounded (· ≤ ·)) :
    limsSup f = 0 := by rwa [limsSup, sInf_of_not_bddBelow]

@[simp]
lemma limsSup_of_not_isBounded {f : Filter ℝ} (hf : ¬ f.IsBounded (· ≤ ·)) : limsSup f = 0 := by
  rw [limsSup]
  convert sInf_empty
  simpa [Set.eq_empty_iff_forall_notMem, IsBounded] using hf

@[simp]
lemma limsInf_of_not_isCobounded {f : Filter ℝ} (hf : ¬ f.IsCobounded (· ≥ ·)) :
    limsInf f = 0 := by rwa [limsInf, sSup_of_not_bddAbove]

@[simp]
lemma limsInf_of_not_isBounded {f : Filter ℝ} (hf : ¬ f.IsBounded (· ≥ ·)) : limsInf f = 0 := by
  rw [limsInf]
  convert sSup_empty
  simpa [Set.eq_empty_iff_forall_notMem, IsBounded] using hf

@[simp]
lemma limsup_of_not_isCoboundedUnder (hf : ¬ f.IsCoboundedUnder (· ≤ ·) u) : limsup u f = 0 :=
  limsSup_of_not_isCobounded hf

@[simp]
lemma limsup_of_not_isBoundedUnder (hf : ¬ f.IsBoundedUnder (· ≤ ·) u) : limsup u f = 0 :=
  limsSup_of_not_isBounded hf

@[simp]
lemma liminf_of_not_isCoboundedUnder (hf : ¬ f.IsCoboundedUnder (· ≥ ·) u) : liminf u f = 0 :=
  limsInf_of_not_isCobounded hf

@[simp]
lemma liminf_of_not_isBoundedUnder (hf : ¬ f.IsBoundedUnder (· ≥ ·) u) : liminf u f = 0 :=
  limsInf_of_not_isBounded hf

end Real

namespace NNReal
variable {ι : Type*} {f : Filter ι} {u : ι → ℝ≥0}

@[simp, norm_cast] lemma isBoundedUnder_le_toReal :
    IsBoundedUnder (· ≤ ·) f (fun i ↦ (u i : ℝ)) ↔ IsBoundedUnder (· ≤ ·) f u := by
  simp only [IsBoundedUnder, IsBounded, eventually_map, ← coe_le_coe, NNReal.exists, coe_mk]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b.toNNReal, by simp, by filter_upwards [hb]; simp +contextual⟩
  · rintro ⟨b, -, hb⟩
    exact ⟨b, hb⟩

@[simp, norm_cast] lemma isBoundedUnder_ge_toReal :
    IsBoundedUnder (· ≥ ·) f (fun i ↦ (u i : ℝ)) ↔ IsBoundedUnder (· ≥ ·) f u := by
  simp only [IsBoundedUnder, IsBounded, eventually_map, ← coe_le_coe, NNReal.exists, coe_mk]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b.toNNReal, by simp, by simpa⟩
  · rintro ⟨b, -, hb⟩
    exact ⟨b, hb⟩

@[simp, norm_cast] lemma isCoboundedUnder_le_toReal [f.NeBot] :
    IsCoboundedUnder (· ≤ ·) f (fun i ↦ (u i : ℝ)) ↔ IsCoboundedUnder (· ≤ ·) f u := by
  simp only [IsCoboundedUnder, IsCobounded, eventually_map, ← coe_le_coe, NNReal.forall,
    NNReal.exists]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b.toNNReal, by simp, fun x _ ↦ by simpa [*] using hb _⟩
  · rintro ⟨b, hb₀, hb⟩
    exact ⟨b, fun x hx ↦ hb _ (hx.exists.choose_spec.trans' (by simp)) hx⟩

@[simp, norm_cast] lemma isCoboundedUnder_ge_toReal :
    IsCoboundedUnder (· ≥ ·) f (fun i ↦ (u i : ℝ)) ↔ IsCoboundedUnder (· ≥ ·) f u := by
  simp only [IsCoboundedUnder, IsCobounded, eventually_map, ← coe_le_coe, NNReal.forall,
    NNReal.exists]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, hb _ (by simp), fun x _ ↦ hb _⟩
  · rintro ⟨b, hb₀, hb⟩
    refine ⟨b, fun x hx ↦ ?_⟩
    obtain hx₀ | hx₀ := le_total x 0
    · exact hx₀.trans hb₀
    · exact hb _ hx₀ hx

@[simp]
lemma limsSup_of_not_isBounded {f : Filter ℝ≥0} (hf : ¬ f.IsBounded (· ≤ ·)) : limsSup f = 0 := by
  rw [limsSup, ← bot_eq_zero]
  convert sInf_empty
  simpa [Set.eq_empty_iff_forall_notMem, IsBounded] using hf

@[simp]
lemma limsInf_of_not_isCobounded {f : Filter ℝ≥0} (hf : ¬ f.IsCobounded (· ≥ ·)) :
    limsInf f = 0 := by rwa [limsInf, sSup_of_not_bddAbove]

@[simp]
lemma limsup_of_not_isBoundedUnder (hf : ¬ f.IsBoundedUnder (· ≤ ·) u) : limsup u f = 0 :=
  limsSup_of_not_isBounded hf

@[simp]
lemma liminf_of_not_isCoboundedUnder (hf : ¬ f.IsCoboundedUnder (· ≥ ·) u) : liminf u f = 0 :=
  limsInf_of_not_isCobounded hf

@[simp, norm_cast]
lemma toReal_liminf : liminf (fun i ↦ (u i : ℝ)) f = liminf u f := by
  by_cases hf : f.IsCoboundedUnder (· ≥ ·) u; swap
  · simp [*]
  refine eq_of_forall_le_iff fun c ↦ ?_
  rw [← Real.toNNReal_le_iff_le_coe, le_liminf_iff (by simpa) ⟨0, by simp⟩, le_liminf_iff]
  simp only [← coe_lt_coe, Real.coe_toNNReal', lt_sup_iff, or_imp, isEmpty_Prop, not_lt,
    zero_le_coe, IsEmpty.forall_iff, and_true, NNReal.forall, coe_mk, forall_swap (α := _ ≤ _)]
  refine forall₂_congr fun r hr ↦ ?_
  simpa using (le_or_gt 0 r).imp_right fun hr ↦ .of_forall fun i ↦ hr.trans_le (by simp)

@[simp, norm_cast]
lemma toReal_limsup : limsup (fun i ↦ (u i : ℝ)) f = limsup u f := by
  obtain rfl | hf := f.eq_or_neBot
  · simp [limsup, limsSup]
  by_cases hf : f.IsBoundedUnder (· ≤ ·) u; swap
  · simp [*]
  have : f.IsCoboundedUnder (· ≤ ·) u := by isBoundedDefault
  refine eq_of_forall_le_iff fun c ↦ ?_
  rw [← Real.toNNReal_le_iff_le_coe, le_limsup_iff (by simpa) (by simpa), le_limsup_iff ‹_›]
  simp only [← coe_lt_coe, Real.coe_toNNReal', lt_sup_iff, or_imp, isEmpty_Prop, not_lt,
    zero_le_coe, IsEmpty.forall_iff, and_true, NNReal.forall, coe_mk, forall_swap (α := _ ≤ _)]
  refine forall₂_congr fun r hr ↦ ?_
  simpa using (le_or_gt 0 r).imp_right fun hr ↦ .of_forall fun i ↦ hr.trans_le (by simp)

end NNReal

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

/-- See also `limsup_mul_le'` -/
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
