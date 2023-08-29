/-
Copyright (c) 2022 Martin Zinkevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Zinkevich
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace

#align_import measure_theory.measure.sub from "leanprover-community/mathlib"@"562bbf524c595c153470e53d36c57b6f891cc480"

/-!
# Subtraction of measures

In this file we define `μ - ν` to be the least measure `τ` such that `μ ≤ τ + ν`.
It is the equivalent of `(μ - ν) ⊔ 0` if `μ` and `ν` were signed measures.
Compare with `ENNReal.instSub`.
Specifically, note that if you have `α = {1,2}`, and `μ {1} = 2`, `μ {2} = 0`, and
`ν {2} = 2`, `ν {1} = 0`, then `(μ - ν) {1, 2} = 2`. However, if `μ ≤ ν`, and
`ν univ ≠ ∞`, then `(μ - ν) + ν = μ`.
-/

open Set

namespace MeasureTheory

namespace Measure

/-- The measure `μ - ν` is defined to be the least measure `τ` such that `μ ≤ τ + ν`.
It is the equivalent of `(μ - ν) ⊔ 0` if `μ` and `ν` were signed measures.
Compare with `ENNReal.instSub`.
Specifically, note that if you have `α = {1,2}`, and `μ {1} = 2`, `μ {2} = 0`, and
`ν {2} = 2`, `ν {1} = 0`, then `(μ - ν) {1, 2} = 2`. However, if `μ ≤ ν`, and
`ν univ ≠ ∞`, then `(μ - ν) + ν = μ`. -/
noncomputable instance instSub {α : Type*} [MeasurableSpace α] : Sub (Measure α) :=
  ⟨fun μ ν => sInf { τ | μ ≤ τ + ν }⟩
#align measure_theory.measure.has_sub MeasureTheory.Measure.instSub

variable {α : Type*} {m : MeasurableSpace α} {μ ν : Measure α} {s : Set α}

theorem sub_def : μ - ν = sInf { d | μ ≤ d + ν } := rfl
#align measure_theory.measure.sub_def MeasureTheory.Measure.sub_def

theorem sub_le_of_le_add {d} (h : μ ≤ d + ν) : μ - ν ≤ d :=
  sInf_le h
#align measure_theory.measure.sub_le_of_le_add MeasureTheory.Measure.sub_le_of_le_add

theorem sub_eq_zero_of_le (h : μ ≤ ν) : μ - ν = 0 :=
  nonpos_iff_eq_zero'.1 <| sub_le_of_le_add <| by rwa [zero_add]
                                                  -- 🎉 no goals
#align measure_theory.measure.sub_eq_zero_of_le MeasureTheory.Measure.sub_eq_zero_of_le

theorem sub_le : μ - ν ≤ μ :=
  sub_le_of_le_add <| Measure.le_add_right le_rfl
#align measure_theory.measure.sub_le MeasureTheory.Measure.sub_le

@[simp]
theorem sub_top : μ - ⊤ = 0 :=
  sub_eq_zero_of_le le_top
#align measure_theory.measure.sub_top MeasureTheory.Measure.sub_top

@[simp]
theorem zero_sub : 0 - μ = 0 :=
  sub_eq_zero_of_le μ.zero_le
#align measure_theory.measure.zero_sub MeasureTheory.Measure.zero_sub

@[simp]
theorem sub_self : μ - μ = 0 :=
  sub_eq_zero_of_le le_rfl
#align measure_theory.measure.sub_self MeasureTheory.Measure.sub_self

/-- This application lemma only works in special circumstances. Given knowledge of
when `μ ≤ ν` and `ν ≤ μ`, a more general application lemma can be written. -/
theorem sub_apply [IsFiniteMeasure ν] (h₁ : MeasurableSet s) (h₂ : ν ≤ μ) :
    (μ - ν) s = μ s - ν s := by
  -- We begin by defining `measure_sub`, which will be equal to `(μ - ν)`.
  let measure_sub : Measure α := MeasureTheory.Measure.ofMeasurable
    (fun (t : Set α) (_ : MeasurableSet t) => μ t - ν t) (by simp)
    (by
      intro g h_meas h_disj; simp only; rw [ENNReal.tsum_sub]
      repeat' rw [← MeasureTheory.measure_iUnion h_disj h_meas]
      exacts [MeasureTheory.measure_ne_top _ _, fun i => h₂ _ (h_meas _)])
  -- Now, we demonstrate `μ - ν = measure_sub`, and apply it.
  have h_measure_sub_add : ν + measure_sub = μ := by
    ext1 t h_t_measurable_set
    simp only [Pi.add_apply, coe_add]
    rw [MeasureTheory.Measure.ofMeasurable_apply _ h_t_measurable_set, add_comm,
      tsub_add_cancel_of_le (h₂ t h_t_measurable_set)]
  have h_measure_sub_eq : μ - ν = measure_sub := by
    rw [MeasureTheory.Measure.sub_def]
    apply le_antisymm
    · apply sInf_le
      simp [le_refl, add_comm, h_measure_sub_add]
    apply le_sInf
    intro d h_d
    rw [← h_measure_sub_add, mem_setOf_eq, add_comm d] at h_d
    apply Measure.le_of_add_le_add_left h_d
  rw [h_measure_sub_eq]
  -- ⊢ ↑↑measure_sub s = ↑↑μ s - ↑↑ν s
  apply Measure.ofMeasurable_apply _ h₁
  -- 🎉 no goals
#align measure_theory.measure.sub_apply MeasureTheory.Measure.sub_apply

theorem sub_add_cancel_of_le [IsFiniteMeasure ν] (h₁ : ν ≤ μ) : μ - ν + ν = μ := by
  ext1 s h_s_meas
  -- ⊢ ↑↑(μ - ν + ν) s = ↑↑μ s
  rw [add_apply, sub_apply h_s_meas h₁, tsub_add_cancel_of_le (h₁ s h_s_meas)]
  -- 🎉 no goals
#align measure_theory.measure.sub_add_cancel_of_le MeasureTheory.Measure.sub_add_cancel_of_le

theorem restrict_sub_eq_restrict_sub_restrict (h_meas_s : MeasurableSet s) :
    (μ - ν).restrict s = μ.restrict s - ν.restrict s := by
  repeat' rw [sub_def]
  -- ⊢ restrict (sInf {d | μ ≤ d + ν}) s = sInf {d | restrict μ s ≤ d + restrict ν s}
  have h_nonempty : { d | μ ≤ d + ν }.Nonempty := ⟨μ, Measure.le_add_right le_rfl⟩
  -- ⊢ restrict (sInf {d | μ ≤ d + ν}) s = sInf {d | restrict μ s ≤ d + restrict ν s}
  rw [restrict_sInf_eq_sInf_restrict h_nonempty h_meas_s]
  -- ⊢ sInf ((fun μ => restrict μ s) '' {d | μ ≤ d + ν}) = sInf {d | restrict μ s ≤ …
  apply le_antisymm
  -- ⊢ sInf ((fun μ => restrict μ s) '' {d | μ ≤ d + ν}) ≤ sInf {d | restrict μ s ≤ …
  · refine' sInf_le_sInf_of_forall_exists_le _
    -- ⊢ ∀ (x : Measure α), x ∈ {d | restrict μ s ≤ d + restrict ν s} → ∃ y, y ∈ (fun …
    intro ν' h_ν'_in
    -- ⊢ ∃ y, y ∈ (fun μ => restrict μ s) '' {d | μ ≤ d + ν} ∧ y ≤ ν'
    rw [mem_setOf_eq] at h_ν'_in
    -- ⊢ ∃ y, y ∈ (fun μ => restrict μ s) '' {d | μ ≤ d + ν} ∧ y ≤ ν'
    refine' ⟨ν'.restrict s, _, restrict_le_self⟩
    -- ⊢ restrict ν' s ∈ (fun μ => restrict μ s) '' {d | μ ≤ d + ν}
    refine' ⟨ν' + (⊤ : Measure α).restrict sᶜ, _, _⟩
    -- ⊢ ν' + restrict ⊤ sᶜ ∈ {d | μ ≤ d + ν}
    · rw [mem_setOf_eq, add_right_comm, Measure.le_iff]
      -- ⊢ ∀ (s_1 : Set α), MeasurableSet s_1 → ↑↑μ s_1 ≤ ↑↑(ν' + ν + restrict ⊤ sᶜ) s_1
      intro t h_meas_t
      -- ⊢ ↑↑μ t ≤ ↑↑(ν' + ν + restrict ⊤ sᶜ) t
      repeat' rw [← measure_inter_add_diff t h_meas_s]
      -- ⊢ ↑↑μ (t ∩ s) + ↑↑μ (t \ s) ≤ ↑↑(ν' + ν + restrict ⊤ sᶜ) (t ∩ s) + ↑↑(ν' + ν + …
      refine' add_le_add _ _
      -- ⊢ ↑↑μ (t ∩ s) ≤ ↑↑(ν' + ν + restrict ⊤ sᶜ) (t ∩ s)
      · rw [add_apply, add_apply]
        -- ⊢ ↑↑μ (t ∩ s) ≤ ↑↑ν' (t ∩ s) + ↑↑ν (t ∩ s) + ↑↑(restrict ⊤ sᶜ) (t ∩ s)
        apply le_add_right _
        -- ⊢ ↑↑μ (t ∩ s) ≤ ↑↑ν' (t ∩ s) + ↑↑ν (t ∩ s)
        rw [← restrict_eq_self μ (inter_subset_right _ _),
          ← restrict_eq_self ν (inter_subset_right _ _)]
        apply h_ν'_in _ (h_meas_t.inter h_meas_s)
        -- 🎉 no goals
      · rw [add_apply, restrict_apply (h_meas_t.diff h_meas_s), diff_eq, inter_assoc, inter_self,
          ← add_apply]
        have h_mu_le_add_top : μ ≤ ν' + ν + ⊤ := by simp only [add_top, le_top]
        -- ⊢ ↑↑μ (t ∩ sᶜ) ≤ ↑↑(ν' + ν + ⊤) (t ∩ sᶜ)
        exact Measure.le_iff'.1 h_mu_le_add_top _
        -- 🎉 no goals
    · ext1 t h_meas_t
      -- ⊢ ↑↑((fun μ => restrict μ s) (ν' + restrict ⊤ sᶜ)) t = ↑↑(restrict ν' s) t
      simp [restrict_apply h_meas_t, restrict_apply (h_meas_t.inter h_meas_s), inter_assoc]
      -- 🎉 no goals
  · refine' sInf_le_sInf_of_forall_exists_le _
    -- ⊢ ∀ (x : Measure α), x ∈ (fun μ => restrict μ s) '' {d | μ ≤ d + ν} → ∃ y, y ∈ …
    refine' ball_image_iff.2 fun t h_t_in => ⟨t.restrict s, _, le_rfl⟩
    -- ⊢ restrict t s ∈ {d | restrict μ s ≤ d + restrict ν s}
    rw [Set.mem_setOf_eq, ← restrict_add]
    -- ⊢ restrict μ s ≤ restrict (t + ν) s
    exact restrict_mono Subset.rfl h_t_in
    -- 🎉 no goals
#align measure_theory.measure.restrict_sub_eq_restrict_sub_restrict MeasureTheory.Measure.restrict_sub_eq_restrict_sub_restrict

theorem sub_apply_eq_zero_of_restrict_le_restrict (h_le : μ.restrict s ≤ ν.restrict s)
    (h_meas_s : MeasurableSet s) : (μ - ν) s = 0 := by
  rw [← restrict_apply_self, restrict_sub_eq_restrict_sub_restrict, sub_eq_zero_of_le] <;> simp [*]
                                                                                           -- 🎉 no goals
                                                                                           -- 🎉 no goals
                                                                                           -- 🎉 no goals
#align measure_theory.measure.sub_apply_eq_zero_of_restrict_le_restrict MeasureTheory.Measure.sub_apply_eq_zero_of_restrict_le_restrict

instance isFiniteMeasure_sub [IsFiniteMeasure μ] : IsFiniteMeasure (μ - ν) :=
  isFiniteMeasure_of_le μ sub_le
#align measure_theory.measure.is_finite_measure_sub MeasureTheory.Measure.isFiniteMeasure_sub

end Measure

end MeasureTheory
