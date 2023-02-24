/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker

! This file was ported from Lean 3 source module topology.algebra.order.floor
! leanprover-community/mathlib commit 84dc0bd6619acaea625086d6f53cb35cdd554219
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Floor
import Mathbin.Topology.Algebra.Order.Group

/-!
# Topological facts about `int.floor`, `int.ceil` and `int.fract`

This file proves statements about limits and continuity of functions involving `floor`, `ceil` and
`fract`.

## Main declarations

* `tendsto_floor_at_top`, `tendsto_floor_at_bot`, `tendsto_ceil_at_top`, `tendsto_ceil_at_bot`:
  `int.floor` and `int.ceil` tend to +-∞ in +-∞.
* `continuous_on_floor`: `int.floor` is continuous on `Ico n (n + 1)`, because constant.
* `continuous_on_ceil`: `int.ceil` is continuous on `Ioc n (n + 1)`, because constant.
* `continuous_on_fract`: `int.fract` is continuous on `Ico n (n + 1)`.
* `continuous_on.comp_fract`: Precomposing a continuous function satisfying `f 0 = f 1` with
  `int.fract` yields another continuous function.
-/


open Filter Function Int Set

open Topology

variable {α β γ : Type _} [LinearOrderedRing α] [FloorRing α]

theorem tendsto_floor_atTop : Tendsto (floor : α → ℤ) atTop atTop :=
  floor_mono.tendsto_atTop_atTop fun b =>
    ⟨(b + 1 : ℤ), by
      rw [floor_int_cast]
      exact (lt_add_one _).le⟩
#align tendsto_floor_at_top tendsto_floor_atTop

theorem tendsto_floor_atBot : Tendsto (floor : α → ℤ) atBot atBot :=
  floor_mono.tendsto_atBot_atBot fun b => ⟨b, (floor_intCast _).le⟩
#align tendsto_floor_at_bot tendsto_floor_atBot

theorem tendsto_ceil_atTop : Tendsto (ceil : α → ℤ) atTop atTop :=
  ceil_mono.tendsto_atTop_atTop fun b => ⟨b, (ceil_intCast _).ge⟩
#align tendsto_ceil_at_top tendsto_ceil_atTop

theorem tendsto_ceil_atBot : Tendsto (ceil : α → ℤ) atBot atBot :=
  ceil_mono.tendsto_atBot_atBot fun b =>
    ⟨(b - 1 : ℤ), by
      rw [ceil_int_cast]
      exact (sub_one_lt _).le⟩
#align tendsto_ceil_at_bot tendsto_ceil_atBot

variable [TopologicalSpace α]

theorem continuousOn_floor (n : ℤ) :
    ContinuousOn (fun x => floor x : α → α) (Ico n (n + 1) : Set α) :=
  (continuousOn_congr <| floor_eq_on_Ico' n).mpr continuousOn_const
#align continuous_on_floor continuousOn_floor

theorem continuousOn_ceil (n : ℤ) :
    ContinuousOn (fun x => ceil x : α → α) (Ioc (n - 1) n : Set α) :=
  (continuousOn_congr <| ceil_eq_on_Ioc' n).mpr continuousOn_const
#align continuous_on_ceil continuousOn_ceil

theorem tendsto_floor_right' [OrderClosedTopology α] (n : ℤ) :
    Tendsto (fun x => floor x : α → α) (𝓝[≥] n) (𝓝 n) :=
  by
  rw [← nhdsWithin_Ico_eq_nhdsWithin_Ici (lt_add_one (n : α))]
  simpa only [floor_int_cast] using
    (continuousOn_floor n _ (left_mem_Ico.mpr <| lt_add_one (_ : α))).Tendsto
#align tendsto_floor_right' tendsto_floor_right'

theorem tendsto_ceil_left' [OrderClosedTopology α] (n : ℤ) :
    Tendsto (fun x => ceil x : α → α) (𝓝[≤] n) (𝓝 n) :=
  by
  rw [← nhdsWithin_Ioc_eq_nhdsWithin_Iic (sub_one_lt (n : α))]
  simpa only [ceil_int_cast] using
    (continuousOn_ceil _ _ (right_mem_Ioc.mpr <| sub_one_lt (_ : α))).Tendsto
#align tendsto_ceil_left' tendsto_ceil_left'

theorem tendsto_floor_right [OrderClosedTopology α] (n : ℤ) :
    Tendsto (fun x => floor x : α → α) (𝓝[≥] n) (𝓝[≥] n) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (tendsto_floor_right' _)
    (by
      refine' eventually_nhdsWithin_of_forall fun x (hx : (n : α) ≤ x) => _
      change _ ≤ _
      norm_cast
      convert ← floor_mono hx
      rw [floor_eq_iff]
      exact ⟨le_rfl, lt_add_one _⟩)
#align tendsto_floor_right tendsto_floor_right

theorem tendsto_ceil_left [OrderClosedTopology α] (n : ℤ) :
    Tendsto (fun x => ceil x : α → α) (𝓝[≤] n) (𝓝[≤] n) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (tendsto_ceil_left' _)
    (by
      refine' eventually_nhdsWithin_of_forall fun x (hx : x ≤ (n : α)) => _
      change _ ≤ _
      norm_cast
      convert ← ceil_mono hx
      rw [ceil_eq_iff]
      exact ⟨sub_one_lt _, le_rfl⟩)
#align tendsto_ceil_left tendsto_ceil_left

theorem tendsto_floor_left [OrderClosedTopology α] (n : ℤ) :
    Tendsto (fun x => floor x : α → α) (𝓝[<] n) (𝓝[≤] (n - 1)) :=
  by
  rw [← nhdsWithin_Ico_eq_nhdsWithin_Iio (sub_one_lt (n : α))]
  convert
      (tendsto_nhdsWithin_congr fun x hx => (floor_eq_on_Ico' (n - 1) x hx).symm)
        (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ tendsto_const_nhds
          (eventually_of_forall fun _ => mem_Iic.mpr <| le_rfl)) <;>
    first |norm_cast|infer_instance
  ring
#align tendsto_floor_left tendsto_floor_left

theorem tendsto_ceil_right [OrderClosedTopology α] (n : ℤ) :
    Tendsto (fun x => ceil x : α → α) (𝓝[>] n) (𝓝[≥] (n + 1)) :=
  by
  rw [← nhdsWithin_Ioc_eq_nhdsWithin_Ioi (lt_add_one (n : α))]
  convert
      (tendsto_nhdsWithin_congr fun x hx => (ceil_eq_on_Ioc' (n + 1) x hx).symm)
        (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ tendsto_const_nhds
          (eventually_of_forall fun _ => mem_Ici.mpr <| le_rfl)) <;>
    first |norm_cast|infer_instance
  ring
#align tendsto_ceil_right tendsto_ceil_right

theorem tendsto_floor_left' [OrderClosedTopology α] (n : ℤ) :
    Tendsto (fun x => floor x : α → α) (𝓝[<] n) (𝓝 (n - 1)) :=
  by
  rw [← nhdsWithin_univ]
  exact tendsto_nhdsWithin_mono_right (subset_univ _) (tendsto_floor_left n)
#align tendsto_floor_left' tendsto_floor_left'

theorem tendsto_ceil_right' [OrderClosedTopology α] (n : ℤ) :
    Tendsto (fun x => ceil x : α → α) (𝓝[>] n) (𝓝 (n + 1)) :=
  by
  rw [← nhdsWithin_univ]
  exact tendsto_nhdsWithin_mono_right (subset_univ _) (tendsto_ceil_right n)
#align tendsto_ceil_right' tendsto_ceil_right'

theorem continuousOn_fract [TopologicalAddGroup α] (n : ℤ) :
    ContinuousOn (fract : α → α) (Ico n (n + 1) : Set α) :=
  continuousOn_id.sub (continuousOn_floor n)
#align continuous_on_fract continuousOn_fract

theorem tendsto_fract_left' [OrderClosedTopology α] [TopologicalAddGroup α] (n : ℤ) :
    Tendsto (fract : α → α) (𝓝[<] n) (𝓝 1) := by
  convert (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).sub (tendsto_floor_left' n) <;>
    [·
      norm_cast
      ring, infer_instance, infer_instance]
#align tendsto_fract_left' tendsto_fract_left'

theorem tendsto_fract_left [OrderClosedTopology α] [TopologicalAddGroup α] (n : ℤ) :
    Tendsto (fract : α → α) (𝓝[<] n) (𝓝[<] 1) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (tendsto_fract_left' _)
    (eventually_of_forall fract_lt_one)
#align tendsto_fract_left tendsto_fract_left

theorem tendsto_fract_right' [OrderClosedTopology α] [TopologicalAddGroup α] (n : ℤ) :
    Tendsto (fract : α → α) (𝓝[≥] n) (𝓝 0) := by
  convert (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).sub (tendsto_floor_right' n) <;>
    [exact (sub_self _).symm, infer_instance, infer_instance]
#align tendsto_fract_right' tendsto_fract_right'

theorem tendsto_fract_right [OrderClosedTopology α] [TopologicalAddGroup α] (n : ℤ) :
    Tendsto (fract : α → α) (𝓝[≥] n) (𝓝[≥] 0) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (tendsto_fract_right' _)
    (eventually_of_forall fract_nonneg)
#align tendsto_fract_right tendsto_fract_right

-- mathport name: exprI
local notation "I" => (Icc 0 1 : Set α)

variable [OrderTopology α] [TopologicalSpace β] [TopologicalSpace γ]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Do not use this, use `continuous_on.comp_fract` instead. -/
theorem ContinuousOn.comp_fract' {f : β → α → γ} (h : ContinuousOn (uncurry f) <| univ ×ˢ I)
    (hf : ∀ s, f s 0 = f s 1) : Continuous fun st : β × α => f st.1 <| fract st.2 :=
  by
  change Continuous (uncurry f ∘ Prod.map id fract)
  rw [continuous_iff_continuousAt]
  rintro ⟨s, t⟩
  by_cases ht : t = floor t
  · rw [ht]
    rw [← continuousWithinAt_univ]
    have : (univ : Set (β × α)) ⊆ univ ×ˢ Iio ↑⌊t⌋ ∪ univ ×ˢ Ici ↑⌊t⌋ :=
      by
      rintro p -
      rw [← prod_union]
      exact ⟨trivial, lt_or_le p.2 _⟩
    refine' ContinuousWithinAt.mono _ this
    refine' ContinuousWithinAt.union _ _
    · simp only [ContinuousWithinAt, fract_int_cast, nhdsWithin_prod_eq, nhdsWithin_univ, id.def,
        comp_app, Prod.map_mk]
      have : (uncurry f) (s, 0) = (uncurry f) (s, (1 : α)) := by simp [uncurry, hf]
      rw [this]
      refine' (h _ ⟨⟨⟩, by exact_mod_cast right_mem_Icc.2 (zero_le_one' α)⟩).Tendsto.comp _
      rw [nhdsWithin_prod_eq, nhdsWithin_univ]
      rw [nhdsWithin_Icc_eq_nhdsWithin_Iic (zero_lt_one' α)]
      exact
        tendsto_id.prod_map
          (tendsto_nhdsWithin_mono_right Iio_subset_Iic_self <| tendsto_fract_left _)
    · simp only [ContinuousWithinAt, fract_int_cast, nhdsWithin_prod_eq, nhdsWithin_univ, id.def,
        comp_app, Prod.map_mk]
      refine' (h _ ⟨⟨⟩, by exact_mod_cast left_mem_Icc.2 (zero_le_one' α)⟩).Tendsto.comp _
      rw [nhdsWithin_prod_eq, nhdsWithin_univ, nhdsWithin_Icc_eq_nhdsWithin_Ici (zero_lt_one' α)]
      exact tendsto_id.prod_map (tendsto_fract_right _)
  · have : t ∈ Ioo (floor t : α) ((floor t : α) + 1) :=
      ⟨lt_of_le_of_ne (floor_le t) (Ne.symm ht), lt_floor_add_one _⟩
    apply (h ((Prod.map _ fract) _) ⟨trivial, ⟨fract_nonneg _, (fract_lt_one _).le⟩⟩).Tendsto.comp
    simp only [nhds_prod_eq, nhdsWithin_prod_eq, nhdsWithin_univ, id.def, Prod.map_mk]
    exact
      continuous_at_id.tendsto.prod_map
        (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          (((continuousOn_fract _ _ (Ioo_subset_Ico_self this)).mono
                Ioo_subset_Ico_self).ContinuousAt
            (Ioo_mem_nhds this.1 this.2))
          (eventually_of_forall fun x => ⟨fract_nonneg _, (fract_lt_one _).le⟩))
#align continuous_on.comp_fract' ContinuousOn.comp_fract'

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem ContinuousOn.comp_fract {s : β → α} {f : β → α → γ}
    (h : ContinuousOn (uncurry f) <| univ ×ˢ Icc 0 1) (hs : Continuous s)
    (hf : ∀ s, f s 0 = f s 1) : Continuous fun x : β => f x <| Int.fract (s x) :=
  (h.comp_fract' hf).comp (continuous_id.prod_mk hs)
#align continuous_on.comp_fract ContinuousOn.comp_fract

/-- A special case of `continuous_on.comp_fract`. -/
theorem ContinuousOn.comp_fract'' {f : α → β} (h : ContinuousOn f I) (hf : f 0 = f 1) :
    Continuous (f ∘ fract) :=
  ContinuousOn.comp_fract (h.comp continuousOn_snd fun x hx => (mem_prod.mp hx).2) continuous_id
    fun _ => hf
#align continuous_on.comp_fract'' ContinuousOn.comp_fract''

