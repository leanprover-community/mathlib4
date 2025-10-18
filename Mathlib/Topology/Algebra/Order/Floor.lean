/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Order.Filter.AtTopBot.Floor
import Mathlib.Topology.Algebra.Order.Group

/-!
# Topological facts about `Int.floor`, `Int.ceil` and `Int.fract`

This file proves statements about limits and continuity of functions involving `floor`, `ceil` and
`fract`.

## Main declarations

* `tendsto_floor_atTop`, `tendsto_floor_atBot`, `tendsto_ceil_atTop`, `tendsto_ceil_atBot`:
  `Int.floor` and `Int.ceil` tend to +-∞ in +-∞.
* `continuousOn_floor`: `Int.floor` is continuous on `Ico n (n + 1)`, because constant.
* `continuousOn_ceil`: `Int.ceil` is continuous on `Ioc n (n + 1)`, because constant.
* `continuousOn_fract`: `Int.fract` is continuous on `Ico n (n + 1)`.
* `ContinuousOn.comp_fract`: Precomposing a continuous function satisfying `f 0 = f 1` with
  `Int.fract` yields another continuous function.
-/


open Filter Function Int Set Topology

namespace FloorSemiring

open scoped Nat

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K]
  [TopologicalSpace K] [OrderTopology K]

theorem tendsto_mul_pow_div_factorial_sub_atTop (a c : K) (d : ℕ) :
    Tendsto (fun n ↦ a * c ^ n / (n - d)!) atTop (𝓝 0) := by
  rw [tendsto_order]
  constructor
  all_goals
    intro ε hε
    filter_upwards [eventually_mul_pow_lt_factorial_sub (a * ε⁻¹) c d] with n h
    rw [mul_right_comm, ← div_eq_mul_inv] at h
  · rw [div_lt_iff_of_neg hε] at h
    rwa [lt_div_iff₀' (Nat.cast_pos.mpr (Nat.factorial_pos _))]
  · rw [div_lt_iff₀ hε] at h
    rwa [div_lt_iff₀' (Nat.cast_pos.mpr (Nat.factorial_pos _))]

theorem tendsto_pow_div_factorial_atTop (c : K) :
    Tendsto (fun n ↦ c ^ n / n !) atTop (𝓝 0) := by
  convert tendsto_mul_pow_div_factorial_sub_atTop 1 c 0
  rw [one_mul]

end FloorSemiring

variable {α β γ : Type*} [Ring α] [LinearOrder α] [FloorRing α]

section
variable [IsStrictOrderedRing α]
-- TODO: move to `Mathlib/Order/Filter/AtTopBot/Floor.lean`

theorem tendsto_floor_atTop : Tendsto (floor : α → ℤ) atTop atTop :=
  floor_mono.tendsto_atTop_atTop fun b =>
    ⟨(b + 1 : ℤ), by rw [floor_intCast]; exact (lt_add_one _).le⟩

theorem tendsto_floor_atBot : Tendsto (floor : α → ℤ) atBot atBot :=
  floor_mono.tendsto_atBot_atBot fun b => ⟨b, (floor_intCast _).le⟩

theorem tendsto_ceil_atTop : Tendsto (ceil : α → ℤ) atTop atTop :=
  ceil_mono.tendsto_atTop_atTop fun b => ⟨b, (ceil_intCast _).ge⟩

theorem tendsto_ceil_atBot : Tendsto (ceil : α → ℤ) atBot atBot :=
  ceil_mono.tendsto_atBot_atBot fun b =>
    ⟨(b - 1 : ℤ), by rw [ceil_intCast]; exact (sub_one_lt _).le⟩

end

variable [TopologicalSpace α]

theorem continuousOn_floor (n : ℤ) :
    ContinuousOn (fun x => floor x : α → α) (Ico n (n + 1) : Set α) :=
  (continuousOn_congr <| floor_eq_on_Ico' n).mpr continuousOn_const

theorem continuousOn_ceil [IsStrictOrderedRing α] (n : ℤ) :
    ContinuousOn (fun x => ceil x : α → α) (Ioc (n - 1) n : Set α) :=
  (continuousOn_congr <| ceil_eq_on_Ioc' n).mpr continuousOn_const

section OrderClosedTopology

variable [IsStrictOrderedRing α] [OrderClosedTopology α]

omit [IsStrictOrderedRing α] in
theorem tendsto_floor_right_pure_floor (x : α) : Tendsto (floor : α → ℤ) (𝓝[≥] x) (pure ⌊x⌋) :=
  tendsto_pure.2 <| mem_of_superset (Ico_mem_nhdsGE <| lt_floor_add_one x) fun _y hy =>
    floor_eq_on_Ico _ _ ⟨(floor_le x).trans hy.1, hy.2⟩

theorem tendsto_floor_right_pure (n : ℤ) : Tendsto (floor : α → ℤ) (𝓝[≥] n) (pure n) := by
  simpa only [floor_intCast] using tendsto_floor_right_pure_floor (n : α)

theorem tendsto_ceil_left_pure_ceil (x : α) : Tendsto (ceil : α → ℤ) (𝓝[≤] x) (pure ⌈x⌉) :=
  tendsto_pure.2 <| mem_of_superset
    (Ioc_mem_nhdsLE <| sub_lt_iff_lt_add.2 <| ceil_lt_add_one _) fun _y hy =>
      ceil_eq_on_Ioc _ _ ⟨hy.1, hy.2.trans (le_ceil _)⟩

theorem tendsto_ceil_left_pure (n : ℤ) : Tendsto (ceil : α → ℤ) (𝓝[≤] n) (pure n) := by
  simpa only [ceil_intCast] using tendsto_ceil_left_pure_ceil (n : α)

theorem tendsto_floor_left_pure_ceil_sub_one (x : α) :
    Tendsto (floor : α → ℤ) (𝓝[<] x) (pure (⌈x⌉ - 1)) :=
  have h₁ : ↑(⌈x⌉ - 1) < x := by rw [cast_sub, cast_one, sub_lt_iff_lt_add]; exact ceil_lt_add_one _
  have h₂ : x ≤ ↑(⌈x⌉ - 1) + 1 := by rw [cast_sub, cast_one, sub_add_cancel]; exact le_ceil _
  tendsto_pure.2 <| mem_of_superset (Ico_mem_nhdsLT h₁) fun _y hy =>
    floor_eq_on_Ico _ _ ⟨hy.1, hy.2.trans_le h₂⟩

theorem tendsto_floor_left_pure_sub_one (n : ℤ) :
    Tendsto (floor : α → ℤ) (𝓝[<] n) (pure (n - 1)) := by
  simpa only [ceil_intCast] using tendsto_floor_left_pure_ceil_sub_one (n : α)

omit [IsStrictOrderedRing α] in
theorem tendsto_ceil_right_pure_floor_add_one (x : α) :
    Tendsto (ceil : α → ℤ) (𝓝[>] x) (pure (⌊x⌋ + 1)) :=
  have : ↑(⌊x⌋ + 1) - 1 ≤ x := by rw [cast_add, cast_one, add_sub_cancel_right]; exact floor_le _
  tendsto_pure.2 <| mem_of_superset (Ioc_mem_nhdsGT <| lt_succ_floor _) fun _y hy =>
    ceil_eq_on_Ioc _ _ ⟨this.trans_lt hy.1, hy.2⟩

theorem tendsto_ceil_right_pure_add_one (n : ℤ) :
    Tendsto (ceil : α → ℤ) (𝓝[>] n) (pure (n + 1)) := by
  simpa only [floor_intCast] using tendsto_ceil_right_pure_floor_add_one (n : α)

theorem tendsto_floor_right (n : ℤ) : Tendsto (fun x => floor x : α → α) (𝓝[≥] n) (𝓝[≥] n) :=
  ((tendsto_pure_pure _ _).comp (tendsto_floor_right_pure n)).mono_right <|
    pure_le_nhdsWithin le_rfl

theorem tendsto_floor_right' (n : ℤ) : Tendsto (fun x => floor x : α → α) (𝓝[≥] n) (𝓝 n) :=
  (tendsto_floor_right n).mono_right inf_le_left

theorem tendsto_ceil_left (n : ℤ) : Tendsto (fun x => ceil x : α → α) (𝓝[≤] n) (𝓝[≤] n) :=
  ((tendsto_pure_pure _ _).comp (tendsto_ceil_left_pure n)).mono_right <|
    pure_le_nhdsWithin le_rfl

theorem tendsto_ceil_left' (n : ℤ) :
    Tendsto (fun x => ceil x : α → α) (𝓝[≤] n) (𝓝 n) :=
  (tendsto_ceil_left n).mono_right inf_le_left

theorem tendsto_floor_left (n : ℤ) :
    Tendsto (fun x => floor x : α → α) (𝓝[<] n) (𝓝[≤] (n - 1)) :=
  ((tendsto_pure_pure _ _).comp (tendsto_floor_left_pure_sub_one n)).mono_right <| by
    rw [← @cast_one α, ← cast_sub]; exact pure_le_nhdsWithin le_rfl

theorem tendsto_ceil_right (n : ℤ) :
    Tendsto (fun x => ceil x : α → α) (𝓝[>] n) (𝓝[≥] (n + 1)) :=
  ((tendsto_pure_pure _ _).comp (tendsto_ceil_right_pure_add_one n)).mono_right <| by
    rw [← @cast_one α, ← cast_add]; exact pure_le_nhdsWithin le_rfl

theorem tendsto_floor_left' (n : ℤ) :
    Tendsto (fun x => floor x : α → α) (𝓝[<] n) (𝓝 (n - 1)) :=
  (tendsto_floor_left n).mono_right inf_le_left

theorem tendsto_ceil_right' (n : ℤ) :
    Tendsto (fun x => ceil x : α → α) (𝓝[>] n) (𝓝 (n + 1)) :=
  (tendsto_ceil_right n).mono_right inf_le_left

end OrderClosedTopology

theorem continuousOn_fract [IsTopologicalAddGroup α] (n : ℤ) :
    ContinuousOn (fract : α → α) (Ico n (n + 1) : Set α) :=
  continuousOn_id.sub (continuousOn_floor n)

theorem continuousAt_fract [OrderClosedTopology α] [IsTopologicalAddGroup α]
    {x : α} (h : x ≠ ⌊x⌋) : ContinuousAt fract x :=
  (continuousOn_fract ⌊x⌋).continuousAt <|
    Ico_mem_nhds ((floor_le _).lt_of_ne h.symm) (lt_floor_add_one _)

variable [IsStrictOrderedRing α]

theorem tendsto_fract_left' [OrderClosedTopology α] [IsTopologicalAddGroup α] (n : ℤ) :
    Tendsto (fract : α → α) (𝓝[<] n) (𝓝 1) := by
  rw [← sub_sub_cancel (n : α) 1]
  refine (tendsto_id.mono_left nhdsWithin_le_nhds).sub ?_
  exact tendsto_floor_left' n

theorem tendsto_fract_left [OrderClosedTopology α] [IsTopologicalAddGroup α] (n : ℤ) :
    Tendsto (fract : α → α) (𝓝[<] n) (𝓝[<] 1) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (tendsto_fract_left' _)
    (Eventually.of_forall fract_lt_one)

theorem tendsto_fract_right' [OrderClosedTopology α] [IsTopologicalAddGroup α] (n : ℤ) :
    Tendsto (fract : α → α) (𝓝[≥] n) (𝓝 0) :=
  sub_self (n : α) ▸ (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).sub (tendsto_floor_right' n)

theorem tendsto_fract_right [OrderClosedTopology α] [IsTopologicalAddGroup α] (n : ℤ) :
    Tendsto (fract : α → α) (𝓝[≥] n) (𝓝[≥] 0) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (tendsto_fract_right' _)
    (Eventually.of_forall fract_nonneg)

local notation "I" => (Icc 0 1 : Set α)

variable [OrderTopology α] [TopologicalSpace β] [TopologicalSpace γ]

/-- Do not use this, use `ContinuousOn.comp_fract` instead. -/
theorem ContinuousOn.comp_fract' {f : β → α → γ} (h : ContinuousOn (uncurry f) <| univ ×ˢ I)
    (hf : ∀ s, f s 0 = f s 1) : Continuous fun st : β × α => f st.1 (fract st.2) := by
  change Continuous (uncurry f ∘ Prod.map id fract)
  rw [continuous_iff_continuousAt]
  rintro ⟨s, t⟩
  rcases em (∃ n : ℤ, t = n) with (⟨n, rfl⟩ | ht)
  · rw [ContinuousAt, nhds_prod_eq, ← nhdsLT_sup_nhdsGE (n : α), prod_sup, tendsto_sup]
    constructor
    · refine (((h (s, 1) ⟨trivial, zero_le_one, le_rfl⟩).tendsto.mono_left ?_).comp
        (tendsto_id.prodMap (tendsto_fract_left _))).mono_right (le_of_eq ?_)
      · rw [nhdsWithin_prod_eq, nhdsWithin_univ, ← nhdsWithin_Ico_eq_nhdsLT one_pos]
        exact Filter.prod_mono le_rfl (nhdsWithin_mono _ Ico_subset_Icc_self)
      · simp [hf]
    · refine (((h (s, 0) ⟨trivial, le_rfl, zero_le_one⟩).tendsto.mono_left <| le_of_eq ?_).comp
        (tendsto_id.prodMap (tendsto_fract_right _))).mono_right (le_of_eq ?_) <;>
        simp [nhdsWithin_prod_eq, nhdsWithin_univ]
  · replace ht : t ≠ ⌊t⌋ := fun ht' => ht ⟨_, ht'⟩
    refine (h.continuousAt ?_).comp (continuousAt_id.prodMap (continuousAt_fract ht))
    exact prod_mem_nhds univ_mem (Icc_mem_nhds (fract_pos.2 ht) (fract_lt_one _))

theorem ContinuousOn.comp_fract {s : β → α} {f : β → α → γ}
    (h : ContinuousOn (uncurry f) <| univ ×ˢ Icc 0 1) (hs : Continuous s)
    (hf : ∀ s, f s 0 = f s 1) : Continuous fun x : β => f x <| Int.fract (s x) :=
  (h.comp_fract' hf).comp (continuous_id.prodMk hs)

/-- A special case of `ContinuousOn.comp_fract`. -/
theorem ContinuousOn.comp_fract'' {f : α → β} (h : ContinuousOn f I) (hf : f 0 = f 1) :
    Continuous (f ∘ fract) :=
  ContinuousOn.comp_fract (h.comp continuousOn_snd fun _x hx => (mem_prod.mp hx).2) continuous_id
    fun _ => hf
