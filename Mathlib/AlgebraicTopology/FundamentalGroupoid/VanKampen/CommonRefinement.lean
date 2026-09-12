module

public import Mathlib
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.PathHelpers

@[expose] public section

open TopologicalSpace Set unitInterval Finset

noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X]
variable (𝒰 : Set (Opens X))
variable (hfinite_intersections :
  ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)

/-- A finite set of points in the unit interval forms a valid subdivision of a path γ
    if every subinterval between consecutive points is mapped into some open set from 𝒰. -/
def IsAdaptedSubdivision {x y : X} (γ : Path x y) (S : Finset I) : Prop :=
  (0 : I) ∈ S ∧ (1 : I) ∈ S ∧
  ∀ (s₁ s₂ : I), s₁ ∈ S → s₂ ∈ S → s₁ < s₂ →
    (∀ (t : I), t ∈ S → s₁ < t → t < s₂ → False) →
    ∃ (U : Opens X), U ∈ 𝒰 ∧ ∀ (t : I), s₁ ≤ t → t ≤ s₂ → γ t ∈ (U : Set X)

namespace IsAdaptedSubdivision

variable {𝒰}

/-- Helper: given a finite set S containing 0 and 1, and points s₁ < s₂ with no points
    of S between them, there exists a containing interval [t₁, t₂] in S. -/
lemma containing_interval {S : Finset I} (h0 : (0 : I) ∈ S) (h1 : (1 : I) ∈ S)
    {s₁ s₂ : I} (h_lt : s₁ < s₂)
    (h_consec : ∀ (t : I), t ∈ S → s₁ < t → t < s₂ → False) :
    ∃ (t₁ t₂ : I), t₁ ∈ S ∧ t₂ ∈ S ∧ t₁ ≤ s₁ ∧ s₂ ≤ t₂ ∧
      (∀ (t : I), t ∈ S → t₁ < t → t < t₂ → False) := by
  -- Let t₁ be the maximum element of S that is ≤ s₁
  let S_low := S.filter (fun t : I => t ≤ s₁)
  have h_zero_le_s1 : (0 : I) ≤ s₁ := by
    have h : (0 : ℝ) ≤ (s₁ : ℝ) := s₁.prop.1
    exact_mod_cast h
  have h0_low : (0 : I) ∈ S_low := by
    simp only [S_low, mem_filter]
    exact ⟨h0, h_zero_le_s1⟩
  have h_S_low_nonempty : S_low.Nonempty := ⟨0, h0_low⟩
  let t₁ := S_low.max' h_S_low_nonempty
  have ht₁_mem : t₁ ∈ S_low := Finset.max'_mem S_low h_S_low_nonempty
  have ht₁_in_S : t₁ ∈ S := (mem_filter.mp ht₁_mem).1
  have ht₁_le : t₁ ≤ s₁ := (mem_filter.mp ht₁_mem).2

  -- Let t₂ be the minimum element of S that is ≥ s₂
  let S_high := S.filter (fun t : I => s₂ ≤ t)
  have h_s2_le_one : s₂ ≤ (1 : I) := by
    have h : (s₂ : ℝ) ≤ (1 : ℝ) := s₂.prop.2
    exact_mod_cast h
  have h1_high : (1 : I) ∈ S_high := by
    simp only [S_high, mem_filter]
    exact ⟨h1, h_s2_le_one⟩
  have h_S_high_nonempty : S_high.Nonempty := ⟨1, h1_high⟩
  let t₂ := S_high.min' h_S_high_nonempty
  have ht₂_mem : t₂ ∈ S_high := Finset.min'_mem S_high h_S_high_nonempty
  have ht₂_in_S : t₂ ∈ S := (mem_filter.mp ht₂_mem).1
  have h_le_t₂ : s₂ ≤ t₂ := (mem_filter.mp ht₂_mem).2

  -- Now show t₁ and t₂ are consecutive in S
  have h_consec' : ∀ (t : I), t ∈ S → t₁ < t → t < t₂ → False := by
    intro t ht h_t1_lt h_t_lt2
    by_cases h : t ≤ s₁
    · -- t ≤ s₁, so t ∈ S_low, contradicting maximality of t₁
      have h_t_in_low : t ∈ S_low := by
        simp only [S_low, mem_filter] <;> exact ⟨ht, h⟩
      have h_t_le_t1 : t ≤ t₁ := Finset.le_max' S_low t h_t_in_low
      have : t₁ < t₁ := by
        calc
          t₁ < t := h_t1_lt
          _ ≤ t₁ := h_t_le_t1
      exact lt_irrefl t₁ this
    · -- s₁ < t
      have h' : s₁ < t := by exact lt_of_not_ge h
      by_cases h2 : t < s₂
      · -- s₁ < t < s₂, contradicting h_consec
        exact h_consec t ht h' h2
      · -- s₂ ≤ t
        have h_s2_le_t : s₂ ≤ t := by
          by_contra h3
          exact h2 (lt_of_not_ge h3)
        -- Therefore t ∈ S_high
        have h_t_in_high : t ∈ S_high := by
          simp only [S_high, mem_filter]
          exact ⟨ht, h_s2_le_t⟩
        -- By minimality of t₂, we have t₂ ≤ t
        have h_t2_le_t : t₂ ≤ t := Finset.min'_le S_high t h_t_in_high
        -- But we assumed t < t₂, so we have t₂ ≤ t < t₂, which is a contradiction
        have h_contra : t₂ < t₂ := by
          calc
            t₂ ≤ t := h_t2_le_t
            _ < t₂ := h_t_lt2
        exact lt_irrefl t₂ h_contra

  exact ⟨t₁, t₂, ht₁_in_S, ht₂_in_S, ht₁_le, h_le_t₂, h_consec'⟩

/-- The union of two adapted subdivisions is also an adapted subdivision. -/
theorem union_is_adapted (hfinite_intersections :
    ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)
    {x y : X} {γ : Path x y} {S T : Finset I}
    (hS : IsAdaptedSubdivision 𝒰 γ S)
    (hT : IsAdaptedSubdivision 𝒰 γ T) :
    IsAdaptedSubdivision 𝒰 γ (S ∪ T) := by
  have h0 : (0 : I) ∈ S ∪ T := by
    exact mem_union_left T hS.1
  have h1 : (1 : I) ∈ S ∪ T := by
    exact mem_union_left T hS.2.1
  constructor
  · exact h0
  constructor
  · exact h1
  · intro s₁ s₂ hs₁ hs₂ h_lt h_consec
    -- [s₁, s₂] is a subinterval of the union subdivision
    -- We need to find U ∈ 𝒰 such that γ maps [s₁, s₂] into U

    -- First, find the containing interval in S
    have h_S_interval : ∃ (t₁ t₂ : I), t₁ ∈ S ∧ t₂ ∈ S ∧ t₁ ≤ s₁ ∧ s₂ ≤ t₂ ∧
        (∀ (t : I), t ∈ S → t₁ < t → t < t₂ → False) := by
      apply containing_interval hS.1 hS.2.1 h_lt
      intro t ht h_t1_lt h_t_lt2
      exact h_consec t (mem_union_left T ht) h_t1_lt h_t_lt2

    -- Find the containing interval in T
    have h_T_interval : ∃ (u₁ u₂ : I), u₁ ∈ T ∧ u₂ ∈ T ∧ u₁ ≤ s₁ ∧ s₂ ≤ u₂ ∧
        (∀ (t : I), t ∈ T → u₁ < t → t < u₂ → False) := by
      apply containing_interval hT.1 hT.2.1 h_lt
      intro t ht h_t1_lt h_t_lt2
      exact h_consec t (mem_union_right S ht) h_t1_lt h_t_lt2

    rcases h_S_interval with ⟨t₁, t₂, ht₁, ht₂, h_t₁_le, h_le_t₂, h_S_consec⟩
    rcases h_T_interval with ⟨u₁, u₂, hu₁, hu₂, h_u₁_le, h_le_u₂, h_T_consec⟩

    -- Get the open sets from S and T
    have h_t1_lt_t2 : t₁ < t₂ := by
      calc
        t₁ ≤ s₁ := h_t₁_le
        _ < s₂ := h_lt
        _ ≤ t₂ := h_le_t₂
    have h_u1_lt_u2 : u₁ < u₂ := by
      calc
        u₁ ≤ s₁ := h_u₁_le
        _ < s₂ := h_lt
        _ ≤ u₂ := h_le_u₂
    rcases hS.2.2 t₁ t₂ ht₁ ht₂ h_t1_lt_t2 h_S_consec with ⟨U, hU_mem, hU⟩
    rcases hT.2.2 u₁ u₂ hu₁ hu₂ h_u1_lt_u2 h_T_consec with ⟨V, hV_mem, hV⟩

    classical
    -- The intersection U ∩ V is in 𝒰 by finite intersection closure
    let s_finset : Finset (Opens X) := {U, V}
    have h_nonempty : s_finset.Nonempty := by
      simp [s_finset]
      <;> exact ⟨U, by simp⟩
    have h_all_in : ∀ (W : Opens X), W ∈ s_finset → W ∈ 𝒰 := by
      intro W hW
      have h : W = U ∨ W = V := by
        simpa [s_finset] using hW
      rcases h with (rfl | rfl)
      · exact hU_mem
      · exact hV_mem
    have h_inter_in : s_finset.inf (fun W : Opens X => W) ∈ 𝒰 :=
      hfinite_intersections s_finset h_nonempty h_all_in

    let W_inf : Opens X := s_finset.inf (fun W : Opens X => W)
    have h_W_inf_mem : W_inf ∈ 𝒰 := h_inter_in

    -- The underlying set of W_inf is the intersection of the underlying sets
    have h_eq_inf : s_finset.inf (fun W : Opens X => W) = U ⊓ V := by
      simp [s_finset, Finset.inf_insert, Finset.inf_singleton]
      <;> rfl
    have h_inf_set : (W_inf : Set X) = (U : Set X) ∩ (V : Set X) := by
      have h1 : W_inf = U ⊓ V := by
        dsimp only [W_inf]
        exact h_eq_inf
      rw [h1]
      exact Opens.coe_inf U V


    refine ⟨W_inf, h_W_inf_mem, ?_⟩
    intro t h_t1 h_t2
    have h1 : γ t ∈ (U : Set X) := hU t (le_trans h_t₁_le h_t1) (le_trans h_t2 h_le_t₂)
    have h2 : γ t ∈ (V : Set X) := hV t (le_trans h_u₁_le h_t1) (le_trans h_t2 h_le_u₂)
    rw [h_inf_set]
    exact ⟨h1, h2⟩

/-- Inserting a single point into an adapted subdivision gives another adapted subdivision. -/
lemma insert_is_adapted {x y : X} {γ : Path x y} {S : Finset I} {pt : I}
    (hS : IsAdaptedSubdivision 𝒰 γ S) :
    IsAdaptedSubdivision 𝒰 γ (S ∪ {pt}) := by
  classical
  by_cases h_pt_in_S : pt ∈ S
  · -- If pt ∈ S, then S ∪ {pt} = S, so we're done
    have h : S ∪ {pt} = S := by
      simp [h_pt_in_S]
      <;> tauto
    rw [h]
    exact hS
  · -- If pt ∉ S, we need to prove the result directly
    have h0 : (0 : I) ∈ S ∪ {pt} := by
      exact Finset.mem_union_left {pt} hS.1
    have h1 : (1 : I) ∈ S ∪ {pt} := by
      exact Finset.mem_union_left {pt} hS.2.1
    constructor
    · exact h0
    constructor
    · exact h1
    · intro s₁ s₂ hs₁ hs₂ h_lt h_consec
      -- We have s₁, s₂ ∈ S ∪ {pt}, s₁ < s₂, and no points of S ∪ {pt} between them
      -- We need to find U ∈ 𝒰 covering [s₁, s₂]
      -- Use the containing_interval lemma from S
      have h_S_interval : ∃ (t₁ t₂ : I), t₁ ∈ S ∧ t₂ ∈ S ∧ t₁ ≤ s₁ ∧ s₂ ≤ t₂ ∧
          (∀ (t : I), t ∈ S → t₁ < t → t < t₂ → False) := by
        apply containing_interval hS.1 hS.2.1 h_lt
        intro t ht h_t1_lt h_t_lt2
        exact h_consec t (Finset.mem_union_left {pt} ht) h_t1_lt h_t_lt2
      rcases h_S_interval with ⟨t₁, t₂, ht₁_in_S, ht₂_in_S, h_t₁_le, h_le_t₂, h_S_consec⟩
      -- Now t₁ and t₂ are consecutive in S, so there exists U ∈ 𝒰 covering [t₁, t₂]
      have h_t1_lt_t2 : t₁ < t₂ := by
        calc
          t₁ ≤ s₁ := h_t₁_le
          _ < s₂ := h_lt
          _ ≤ t₂ := h_le_t₂
      rcases hS.2.2 t₁ t₂ ht₁_in_S ht₂_in_S h_t1_lt_t2 h_S_consec with ⟨U, hU_mem, hU⟩
      -- Since [s₁, s₂] ⊆ [t₁, t₂], U also covers [s₁, s₂]
      refine ⟨U, hU_mem, ?_⟩
      intro t h_t1 h_t2
      have h_t1' : t₁ ≤ t := le_trans h_t₁_le h_t1
      have h_t2' : t ≤ t₂ := le_trans h_t2 h_le_t₂
      exact hU t h_t1' h_t2'

end IsAdaptedSubdivision

end
