module

public import Mathlib

@[expose] public section

open TopologicalSpace Set unitInterval

noncomputable section

variable {X : Type*} [TopologicalSpace X] {x y : X} (γ : Path x y)

namespace VanKampen

/-- The image of the subpathTransSubpath homotopy is contained in the image of γ
    restricted to the interval [t₀, t₂]. -/
lemma subpathTransSubpath_range {t₀ t₁ t₂ : I} (h_t0_le_t1 : t₀ ≤ t₁) (h_t1_le_t2 : t₁ ≤ t₂) :
    ∀ (p : I × I), ∃ (u : I), t₀ ≤ u ∧ u ≤ t₂ ∧
      (Path.Homotopy.subpathTransSubpath γ t₀ t₁ t₂) p = γ u := by
  have h_t0_le_t2 : t₀ ≤ t₂ := le_trans h_t0_le_t1 h_t1_le_t2

  -- First, prove the property for subpathTransSubpathRefl (for all s, t)
  have h1 : ∀ (s t : I), ∃ (u : I), t₀ ≤ u ∧ u ≤ t₂ ∧
      (Path.Homotopy.subpathTransSubpathRefl γ t₀ t₁ t₂) (s, t) = γ u := by
    intro s t
    let t_mid : I := Icc.convexComb t₁ t₂ s
    have h_t1_le_mid : t₁ ≤ t_mid := by
      have h : t_mid ∈ Set.uIcc t₁ t₂ := by
        exact (Path.range_subpathAux t₁ t₂).symm ▸ Set.mem_range_self s
      exact (Set.uIcc_of_le h_t1_le_t2).symm ▸ h |>.1
    have h_mid_le_t2 : t_mid ≤ t₂ := by
      have h : t_mid ∈ Set.uIcc t₁ t₂ := by
        exact (Path.range_subpathAux t₁ t₂).symm ▸ Set.mem_range_self s
      exact (Set.uIcc_of_le h_t1_le_t2).symm ▸ h |>.2
    have h_t0_le_mid : t₀ ≤ t_mid := le_trans h_t0_le_t1 h_t1_le_mid

    let γ1 : Path (γ t₀) (γ t_mid) := γ.subpath t₀ t_mid
    let γ2 : Path (γ t_mid) (γ t₂) := γ.subpath t_mid t₂

    have h_range1 : Set.range (γ1.trans γ2) ⊆ γ '' Set.Icc t₀ t₂ := by
      rw [Path.trans_range γ1 γ2]
      apply Set.union_subset
      · -- Set.range γ1 ⊆ γ '' Set.Icc t₀ t₂
        rw [Path.range_subpath γ t₀ t_mid, Set.uIcc_of_le h_t0_le_mid]
        intro z hz
        rcases hz with ⟨u, hu, rfl⟩
        exact ⟨u, ⟨hu.1, le_trans hu.2 h_mid_le_t2⟩, rfl⟩
      · -- Set.range γ2 ⊆ γ '' Set.Icc t₀ t₂
        rw [Path.range_subpath γ t_mid t₂, Set.uIcc_of_le h_mid_le_t2]
        intro z hz
        rcases hz with ⟨u, hu, rfl⟩
        exact ⟨u, ⟨le_trans h_t0_le_mid hu.1, hu.2⟩, rfl⟩

    have h_in_range : (γ1.trans γ2) t ∈ Set.range (γ1.trans γ2) := Set.mem_range_self t
    have h_main : (γ1.trans γ2) t ∈ γ '' Set.Icc t₀ t₂ := h_range1 h_in_range
    rcases h_main with ⟨u, hu, h_eq⟩
    exact ⟨u, hu.1, hu.2, h_eq.symm⟩

  -- Next, prove the property for transRefl (γ.subpath t₀ t₂) (for all s, t)
  have h2 : ∀ (s t : I), ∃ (u : I), t₀ ≤ u ∧ u ≤ t₂ ∧
      (Path.Homotopy.transRefl (γ.subpath t₀ t₂)) (s, t) = γ u := by
    intro s t
    have h_range : Set.range (γ.subpath t₀ t₂) = γ '' Set.Icc t₀ t₂ := by
      rw [Path.range_subpath γ t₀ t₂, Set.uIcc_of_le h_t0_le_t2]
    have h_in_range : (Path.Homotopy.transRefl (γ.subpath t₀ t₂)) (s, t) ∈
        Set.range (γ.subpath t₀ t₂) := by
      exact Set.mem_range_self _
    rw [h_range] at h_in_range
    rcases h_in_range with ⟨u, hu, h_eq⟩
    exact ⟨u, hu.1, hu.2, h_eq.symm⟩

  intro p
  let s : I := p.1
  let t : I := p.2
  let H1 := Path.Homotopy.subpathTransSubpathRefl γ t₀ t₁ t₂
  let H2 := Path.Homotopy.transRefl (γ.subpath t₀ t₂)
  let H := Path.Homotopy.subpathTransSubpath γ t₀ t₁ t₂

  have h_def : H = H1.trans H2 := by rfl

  -- We know that for any homotopy trans, its evaluation at (s, t) is either from H1 or H2
  by_cases h_s : (s : ℝ) ≤ 1 / 2
  · -- First half: use subpathTransSubpathRefl
    let s' : I := ⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.prop.1, h_s⟩⟩
    have h_main_goal : ∃ (u : I), t₀ ≤ u ∧ u ≤ t₂ ∧ H p = γ u := by
      let H_trans : Path.Homotopy _ _ := H1.trans H2
      have h_eq1 : H = H_trans := h_def
      rw [h_eq1]
      have h_trans_apply : ∀ (p' : I × I),
          H_trans p' =
            if h : (p'.1 : ℝ) ≤ 1 / 2 then
              H1 (⟨2 * p'.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨p'.1.prop.1, h⟩⟩, p'.2)
            else
              H2 (⟨2 * p'.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, p'.1.prop.2⟩⟩, p'.2) := by
        intro p'
        exact?
      have h4 := h_trans_apply p
      rw [h4]
      rw [dif_pos h_s]
      exact h1 s' t
    exact h_main_goal
  · -- Second half: use transRefl
    have h_s'_gt : ¬ (s : ℝ) ≤ 1 / 2 := h_s
    let s' : I := ⟨2 * s - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h_s'_gt).le, s.prop.2⟩⟩
    have h_main_goal : ∃ (u : I), t₀ ≤ u ∧ u ≤ t₂ ∧ H p = γ u := by
      let H_trans : Path.Homotopy _ _ := H1.trans H2
      have h_eq1 : H = H_trans := h_def
      rw [h_eq1]
      have h_trans_apply : ∀ (p' : I × I),
          H_trans p' =
            if h : (p'.1 : ℝ) ≤ 1 / 2 then
              H1 (⟨2 * p'.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨p'.1.prop.1, h⟩⟩, p'.2)
            else
              H2 (⟨2 * p'.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, p'.1.prop.2⟩⟩, p'.2) := by
        intro p'
        exact?
      have h4 := h_trans_apply p
      rw [h4]
      rw [dif_neg h_s'_gt]
      exact h2 s' t
    exact h_main_goal

end VanKampen

end

end
