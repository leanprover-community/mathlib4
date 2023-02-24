/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker

! This file was ported from Lean 3 source module topology.algebra.order.floor
! leanprover-community/mathlib commit 84dc0bd6619acaea625086d6f53cb35cdd554219
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Order.Floor
import Mathlib.Topology.Algebra.Order.Group

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


open Filter Function Int Set Topology

variable {α β γ : Type _} [LinearOrderedRing α] [FloorRing α]

theorem tendsto_floor_atTop : Tendsto (floor : α → ℤ) atTop atTop :=
  floor_mono.tendsto_atTop_atTop fun b =>
    ⟨(b + 1 : ℤ), by rw [floor_intCast]; exact (lt_add_one _).le⟩
#align tendsto_floor_at_top tendsto_floor_atTop

theorem tendsto_floor_atBot : Tendsto (floor : α → ℤ) atBot atBot :=
  floor_mono.tendsto_atBot_atBot fun b => ⟨b, (floor_intCast _).le⟩
#align tendsto_floor_at_bot tendsto_floor_atBot

theorem tendsto_ceil_atTop : Tendsto (ceil : α → ℤ) atTop atTop :=
  ceil_mono.tendsto_atTop_atTop fun b => ⟨b, (ceil_intCast _).ge⟩
#align tendsto_ceil_at_top tendsto_ceil_atTop

theorem tendsto_ceil_atBot : Tendsto (ceil : α → ℤ) atBot atBot :=
  ceil_mono.tendsto_atBot_atBot fun b =>
    ⟨(b - 1 : ℤ), by rw [ceil_intCast]; exact (sub_one_lt _).le⟩
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

section OrderClosedTopology

variable [OrderClosedTopology α]

-- porting note: new theorem
theorem tendsto_floor_right_pure_floor (x : α) : Tendsto (floor : α → ℤ) (𝓝[≥] x) (pure ⌊x⌋) :=
  tendsto_pure.2 <| mem_of_superset (Ico_mem_nhdsWithin_Ici' <| lt_floor_add_one x) <| fun _y hy =>
    floor_eq_on_Ico _ _ ⟨(floor_le x).trans hy.1, hy.2⟩

-- porting note: new theorem
theorem tendsto_floor_right_pure (n : ℤ) : Tendsto (floor : α → ℤ) (𝓝[≥] n) (pure n) := by
  simpa only [floor_intCast] using tendsto_floor_right_pure_floor (n : α)

-- porting note: new theorem
theorem tendsto_ceil_left_pure_ceil (x : α) : Tendsto (ceil : α → ℤ) (𝓝[≤] x) (pure ⌈x⌉) :=
  tendsto_pure.2 <| mem_of_superset
    (Ioc_mem_nhdsWithin_Iic' <| sub_lt_iff_lt_add.2 <| ceil_lt_add_one _) <| fun _y hy =>
      ceil_eq_on_Ioc _ _ ⟨hy.1, hy.2.trans (le_ceil _)⟩

-- porting note: new theorem
theorem tendsto_ceil_left_pure (n : ℤ) : Tendsto (ceil : α → ℤ) (𝓝[≤] n) (pure n) := by
  simpa only [ceil_intCast] using tendsto_ceil_left_pure_ceil (n : α)

-- porting note: new theorem
theorem tendsto_floor_left_pure_ceil_sub_one (x : α) :
    Tendsto (floor : α → ℤ) (𝓝[<] x) (pure (⌈x⌉ - 1)) :=
  have h₁ : ↑(⌈x⌉ - 1) < x := by rw [cast_sub, cast_one, sub_lt_iff_lt_add]; exact ceil_lt_add_one _
  have h₂ : x ≤ ↑(⌈x⌉ - 1) + 1 := by rw [cast_sub, cast_one, sub_add_cancel]; exact le_ceil _
  tendsto_pure.2 <| mem_of_superset (Ico_mem_nhdsWithin_Iio' h₁) <| fun _y hy =>
    floor_eq_on_Ico _ _ ⟨hy.1, hy.2.trans_le h₂⟩

-- porting note: new theorem
theorem tendsto_floor_left_pure_sub_one (n : ℤ) :
    Tendsto (floor : α → ℤ) (𝓝[<] n) (pure (n - 1)) := by
  simpa only [ceil_intCast] using tendsto_floor_left_pure_ceil_sub_one (n : α)

-- porting note: new theorem
theorem tendsto_ceil_right_pure_floor_add_one (x : α) :
    Tendsto (ceil : α → ℤ) (𝓝[>] x) (pure (⌊x⌋ + 1)) :=
  have : ↑(⌊x⌋ + 1) - 1 ≤ x := by rw [cast_add, cast_one, add_sub_cancel]; exact floor_le _
  tendsto_pure.2 <| mem_of_superset (Ioc_mem_nhdsWithin_Ioi' <| lt_succ_floor _) <| fun _y hy =>
    ceil_eq_on_Ioc _ _ ⟨this.trans_lt hy.1, hy.2⟩

-- porting note: new theorem
theorem tendsto_ceil_right_pure_add_one (n : ℤ) :
    Tendsto (ceil : α → ℤ) (𝓝[>] n) (pure (n + 1)) := by
  simpa only [floor_intCast] using tendsto_ceil_right_pure_floor_add_one (n : α)

theorem tendsto_floor_right (n : ℤ) : Tendsto (fun x => floor x : α → α) (𝓝[≥] n) (𝓝[≥] n) :=
  ((tendsto_pure_pure _ _).comp (tendsto_floor_right_pure n)).mono_right <|
    pure_le_nhdsWithin le_rfl
#align tendsto_floor_right tendsto_floor_right

theorem tendsto_floor_right' (n : ℤ) : Tendsto (fun x => floor x : α → α) (𝓝[≥] n) (𝓝 n) :=
  (tendsto_floor_right n).mono_right inf_le_left
#align tendsto_floor_right' tendsto_floor_right'

theorem tendsto_ceil_left (n : ℤ) : Tendsto (fun x => ceil x : α → α) (𝓝[≤] n) (𝓝[≤] n) :=
  ((tendsto_pure_pure _ _).comp (tendsto_ceil_left_pure n)).mono_right <|
    pure_le_nhdsWithin le_rfl
#align tendsto_ceil_left tendsto_ceil_left

theorem tendsto_ceil_left' (n : ℤ) :
    Tendsto (fun x => ceil x : α → α) (𝓝[≤] n) (𝓝 n) :=
  (tendsto_ceil_left n).mono_right inf_le_left
#align tendsto_ceil_left' tendsto_ceil_left'

theorem tendsto_floor_left (n : ℤ) :
    Tendsto (fun x => floor x : α → α) (𝓝[<] n) (𝓝[≤] (n - 1)) :=
  ((tendsto_pure_pure _ _).comp (tendsto_floor_left_pure_sub_one n)).mono_right <| by
    rw [← @cast_one α, ← cast_sub]; exact pure_le_nhdsWithin le_rfl
#align tendsto_floor_left tendsto_floor_left

theorem tendsto_ceil_right (n : ℤ) :
    Tendsto (fun x => ceil x : α → α) (𝓝[>] n) (𝓝[≥] (n + 1)) :=
  ((tendsto_pure_pure _ _).comp (tendsto_ceil_right_pure_add_one n)).mono_right <| by
    rw [← @cast_one α, ← cast_add]; exact pure_le_nhdsWithin le_rfl
#align tendsto_ceil_right tendsto_ceil_right

theorem tendsto_floor_left' (n : ℤ) :
    Tendsto (fun x => floor x : α → α) (𝓝[<] n) (𝓝 (n - 1)) :=
  (tendsto_floor_left n).mono_right inf_le_left
#align tendsto_floor_left' tendsto_floor_left'

theorem tendsto_ceil_right' (n : ℤ) :
    Tendsto (fun x => ceil x : α → α) (𝓝[>] n) (𝓝 (n + 1)) :=
  (tendsto_ceil_right n).mono_right inf_le_left
#align tendsto_ceil_right' tendsto_ceil_right'

end OrderClosedTopology

theorem continuousOn_fract [TopologicalAddGroup α] (n : ℤ) :
    ContinuousOn (fract : α → α) (Ico n (n + 1) : Set α) :=
  continuousOn_id.sub (continuousOn_floor n)
#align continuous_on_fract continuousOn_fract

theorem continuousAt_fract [OrderClosedTopology α] [TopologicalAddGroup α]
    {x : α} (h : fract x ≠ 0) : ContinuousAt fract x := by
  refine (continuousOn_fract ⌊x⌋).continuousAt <| Ico_mem_nhds ?_ (lt_floor_add_one _)
  refine (floor_le _).lt_of_ne fun h' => ?_
  rw [← h', fract_intCast] at h
  exact h rfl

theorem tendsto_fract_left' [OrderClosedTopology α] [TopologicalAddGroup α] (n : ℤ) :
    Tendsto (fract : α → α) (𝓝[<] n) (𝓝 1) := by
  rw [← sub_sub_cancel (n : α) 1]
  refine (tendsto_id.mono_left nhdsWithin_le_nhds).sub ?_
  exact tendsto_floor_left' n
#align tendsto_fract_left' tendsto_fract_left'

theorem tendsto_fract_left [OrderClosedTopology α] [TopologicalAddGroup α] (n : ℤ) :
    Tendsto (fract : α → α) (𝓝[<] n) (𝓝[<] 1) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (tendsto_fract_left' _)
    (eventually_of_forall fract_lt_one)
#align tendsto_fract_left tendsto_fract_left

theorem tendsto_fract_right' [OrderClosedTopology α] [TopologicalAddGroup α] (n : ℤ) :
    Tendsto (fract : α → α) (𝓝[≥] n) (𝓝 0) :=
  sub_self (n : α) ▸ (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).sub (tendsto_floor_right' n)
#align tendsto_fract_right' tendsto_fract_right'

theorem tendsto_fract_right [OrderClosedTopology α] [TopologicalAddGroup α] (n : ℤ) :
    Tendsto (fract : α → α) (𝓝[≥] n) (𝓝[≥] 0) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (tendsto_fract_right' _)
    (eventually_of_forall fract_nonneg)
#align tendsto_fract_right tendsto_fract_right

local notation "I" => (Icc 0 1 : Set α)

variable [OrderTopology α] [TopologicalSpace β] [TopologicalSpace γ]

/-- Do not use this, use `continuous_on.comp_fract` instead. -/
theorem ContinuousOn.comp_fract' {f : β → α → γ} (h : ContinuousOn (uncurry f) <| univ ×ˢ I)
    (hf : ∀ s, f s 0 = f s 1) : Continuous fun st : β × α => f st.1 (fract st.2) := by
  change Continuous (uncurry f ∘ Prod.map id fract)
  rw [continuous_iff_continuousAt]
  rintro ⟨s, t⟩
  cases' eq_or_ne (fract t) 0 with ht₀ ht₀
  · 
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
    · simp only [ContinuousWithinAt, fract_intCast, nhdsWithin_prod_eq, nhdsWithin_univ, id.def,
        comp_apply, Prod.map_mk]
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
    apply (h ((Prod.map _ fract) _) ⟨trivial, ⟨fract_nonneg _, (fract_lt_one _).le⟩⟩).tendsto.comp
    simp only [nhds_prod_eq, nhdsWithin_prod_eq, nhdsWithin_univ, id.def, Prod.map_mk]
    exact continuousAt_id.tendsto.prod_map
        (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          (((continuousOn_fract _ _ (Ioo_subset_Ico_self this)).mono
                Ioo_subset_Ico_self).ContinuousAt
            (Ioo_mem_nhds this.1 this.2))
          (eventually_of_forall fun x => ⟨fract_nonneg _, (fract_lt_one _).le⟩))
#align continuous_on.comp_fract' ContinuousOn.comp_fract'

theorem ContinuousOn.comp_fract {s : β → α} {f : β → α → γ}
    (h : ContinuousOn (uncurry f) <| univ ×ˢ Icc 0 1) (hs : Continuous s)
    (hf : ∀ s, f s 0 = f s 1) : Continuous fun x : β => f x <| Int.fract (s x) :=
  (h.comp_fract' hf).comp (continuous_id.prod_mk hs)
#align continuous_on.comp_fract ContinuousOn.comp_fract

/-- A special case of `continuous_on.comp_fract`. -/
theorem ContinuousOn.comp_fract'' {f : α → β} (h : ContinuousOn f I) (hf : f 0 = f 1) :
    Continuous (f ∘ fract) :=
  ContinuousOn.comp_fract (h.comp continuousOn_snd fun _x hx => (mem_prod.mp hx).2) continuous_id
    fun _ => hf
#align continuous_on.comp_fract'' ContinuousOn.comp_fract''

