module

public import Mathlib

@[expose] public section

open TopologicalSpace Path unitInterval Metric

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- Given an open cover of X, any homotopy can be subdivided into a finite grid
    of subrectangles, each of which maps into some open set from the cover. -/
theorem homotopy_has_subdivision
    (𝒰 : Set (Opens X))
    (hcover : ∀ x : X, ∃ U : Opens X, U ∈ 𝒰 ∧ x ∈ U)
    {x y : X} {γ₁ γ₂ : Path x y} (H : Path.Homotopy γ₁ γ₂) :
    ∃ (n : ℕ), 0 < n ∧ ∀ (i j : Fin n),
      ∃ (U : Opens X), U ∈ 𝒰 ∧
      ∀ (p : I × I),
        (i : ℝ) / (n : ℝ) ≤ (p.1 : ℝ) → (p.1 : ℝ) ≤ ((i : ℝ) + 1) / (n : ℝ) →
        (j : ℝ) / (n : ℝ) ≤ (p.2 : ℝ) → (p.2 : ℝ) ≤ ((j : ℝ) + 1) / (n : ℝ) →
        H p ∈ U := by
  let Y := I × I
  let H' : C(Y, X) := ⟨fun p : Y => H p, H.continuous⟩

  -- Index type for the cover: the subtype of opens in 𝒰
  let idx := {U : Opens X // U ∈ 𝒰}
  let V : idx → Set Y := fun U => H' ⁻¹' (U.val : Set X)
  have hV_open : ∀ (U : idx), IsOpen (V U) := fun U => U.val.2.preimage H'.continuous
  have hV_cover : (Set.univ : Set Y) ⊆ ⋃ (U : idx), V U := by
    intro p _
    have h1 : ∃ (U : Opens X), U ∈ 𝒰 ∧ H' p ∈ U := hcover (H' p)
    rcases h1 with ⟨U, hU_mem, hU⟩
    let U' : idx := ⟨U, hU_mem⟩
    exact Set.mem_iUnion.mpr ⟨U', hU⟩

  -- Y is compact
  have hY_compact : IsCompact (Set.univ : Set Y) := isCompact_univ

  -- Apply Lebesgue number lemma
  have h_lebesgue := Filter.HasBasis.lebesgue_number_lemma
    (Metric.uniformity_basis_dist (α := Y)) hY_compact hV_open hV_cover
  rcases h_lebesgue with ⟨ε, hε_pos, hε⟩

  -- Pick n such that 1 / n < ε
  have h_exists_n : ∃ (n : ℕ), 0 < n ∧ 1 / (n : ℝ) < ε := by
    have h1 : ∃ (n : ℕ), (n : ℝ) > 1 / ε := exists_nat_gt (1 / ε)
    rcases h1 with ⟨n, hn⟩
    have hn_pos : 0 < n := by
      by_contra h
      have h' : n = 0 := by omega
      rw [h'] at hn
      have h_contra : 1 / ε > 0 := by positivity
      linarith
    refine ⟨n, hn_pos, ?_⟩
    have h2 : (n : ℝ) > 1 / ε := hn
    have h3 : 1 / (n : ℝ) < ε := by
      calc
        1 / (n : ℝ) < 1 / (1 / ε) := by gcongr
        _ = ε := by
          field_simp [hε_pos.ne'] <;> ring
    exact h3
  rcases h_exists_n with ⟨n, hn_pos, hn⟩

  refine ⟨n, hn_pos, fun i j => ?_⟩

  have hn_pos' : 0 < (n : ℝ) := by exact_mod_cast hn_pos
  have hn_pos'' : (n : ℝ) ≠ 0 := hn_pos'.ne'
  have hn_ne_zero : n ≠ 0 := by omega
  letI : NeZero n := ⟨hn_ne_zero⟩

  -- Center point of the subrectangle
  let t₀ : ℝ := ((i : ℝ) + 1 / 2) / (n : ℝ)
  let s₀ : ℝ := ((j : ℝ) + 1 / 2) / (n : ℝ)
  have ht₀_nonneg : 0 ≤ t₀ := by positivity
  have ht₀_le_one : t₀ ≤ 1 := by
    have h1 : 0 ≤ (i : ℝ) := by exact_mod_cast Fin.zero_le i
    have h2 : (i : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr (Fin.is_lt i)
    have h3 : (i : ℝ) + 1 / 2 ≤ (n : ℝ) := by linarith
    have h4 : ((i : ℝ) + 1 / 2) / (n : ℝ) ≤ (n : ℝ) / (n : ℝ) :=
      div_le_div_of_nonneg_right h3 hn_pos'.le
    have h5 : (n : ℝ) / (n : ℝ) = 1 := by
      field_simp [hn_pos'']
    rw [h5] at h4
    exact h4
  have hs₀_nonneg : 0 ≤ s₀ := by positivity
  have hs₀_le_one : s₀ ≤ 1 := by
    have h1 : 0 ≤ (j : ℝ) := by exact_mod_cast Fin.zero_le j
    have h2 : (j : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr (Fin.is_lt j)
    have h3 : (j : ℝ) + 1 / 2 ≤ (n : ℝ) := by linarith
    have h4 : ((j : ℝ) + 1 / 2) / (n : ℝ) ≤ (n : ℝ) / (n : ℝ) :=
      div_le_div_of_nonneg_right h3 hn_pos'.le
    have h5 : (n : ℝ) / (n : ℝ) = 1 := by
      field_simp [hn_pos'']
    rw [h5] at h4
    exact h4
  let z₀ : Y := (⟨t₀, ⟨ht₀_nonneg, ht₀_le_one⟩⟩, ⟨s₀, ⟨hs₀_nonneg, hs₀_le_one⟩⟩)

  -- There exists U ∈ 𝒰 such that ball z₀ ε ⊆ H ⁻¹' U
  have h4 : ∃ (U : idx), UniformSpace.ball z₀ {p : Y × Y | dist p.1 p.2 < ε} ⊆ V U := hε z₀ (by trivial)
  rcases h4 with ⟨U, hU_ball⟩

  refine ⟨U.val, U.property, fun p ht1 ht2 hs1 hs2 => ?_⟩

  -- Let t := (p.1 : ℝ), s := (p.2 : ℝ)
  let t : ℝ := (p.1 : ℝ)
  let s : ℝ := (p.2 : ℝ)

  -- Show |t - t₀| ≤ 1/n
  have h_t_diff_lower : t - t₀ ≥ -(1 / (n : ℝ)) := by
    have h1 : t ≥ (i : ℝ) / (n : ℝ) := ht1
    have h2 : (i : ℝ) / (n : ℝ) - t₀ = -(1 / (2 * (n : ℝ))) := by
      dsimp only [t₀]
      field_simp [hn_pos''] <;> ring
    have h3 : t - t₀ ≥ (i : ℝ) / (n : ℝ) - t₀ := by linarith
    rw [h2] at h3
    have h4 : -(1 / (2 * (n : ℝ))) ≥ -(1 / (n : ℝ)) := by
      have h5 : 0 < (n : ℝ) := hn_pos'
      have h6 : 1 / (2 * (n : ℝ)) ≤ 1 / (n : ℝ) := by
        apply one_div_le_one_div_of_le
        <;> linarith
      linarith
    linarith
  have h_t_diff_upper : t - t₀ ≤ 1 / (n : ℝ) := by
    have h1 : t ≤ ((i : ℝ) + 1) / (n : ℝ) := ht2
    have h2 : ((i : ℝ) + 1) / (n : ℝ) - t₀ = 1 / (2 * (n : ℝ)) := by
      dsimp only [t₀]
      field_simp [hn_pos''] <;> ring
    have h3 : t - t₀ ≤ ((i : ℝ) + 1) / (n : ℝ) - t₀ := by linarith
    rw [h2] at h3
    have h4 : 1 / (2 * (n : ℝ)) ≤ 1 / (n : ℝ) := by
      have h5 : 0 < (n : ℝ) := hn_pos'
      apply one_div_le_one_div_of_le
      <;> linarith
    linarith
  have h5 : |t - t₀| ≤ 1 / (n : ℝ) := by
    rw [abs_le]
    exact ⟨h_t_diff_lower, h_t_diff_upper⟩

  -- Show |s - s₀| ≤ 1/n
  have h_s_diff_lower : s - s₀ ≥ -(1 / (n : ℝ)) := by
    have h1 : s ≥ (j : ℝ) / (n : ℝ) := hs1
    have h2 : (j : ℝ) / (n : ℝ) - s₀ = -(1 / (2 * (n : ℝ))) := by
      dsimp only [s₀]
      field_simp [hn_pos''] <;> ring
    have h3 : s - s₀ ≥ (j : ℝ) / (n : ℝ) - s₀ := by linarith
    rw [h2] at h3
    have h4 : -(1 / (2 * (n : ℝ))) ≥ -(1 / (n : ℝ)) := by
      have h5 : 0 < (n : ℝ) := hn_pos'
      have h6 : 1 / (2 * (n : ℝ)) ≤ 1 / (n : ℝ) := by
        apply one_div_le_one_div_of_le
        <;> linarith
      linarith
    linarith
  have h_s_diff_upper : s - s₀ ≤ 1 / (n : ℝ) := by
    have h1 : s ≤ ((j : ℝ) + 1) / (n : ℝ) := hs2
    have h2 : ((j : ℝ) + 1) / (n : ℝ) - s₀ = 1 / (2 * (n : ℝ)) := by
      dsimp only [s₀]
      field_simp [hn_pos''] <;> ring
    have h3 : s - s₀ ≤ ((j : ℝ) + 1) / (n : ℝ) - s₀ := by linarith
    rw [h2] at h3
    have h4 : 1 / (2 * (n : ℝ)) ≤ 1 / (n : ℝ) := by
      have h5 : 0 < (n : ℝ) := hn_pos'
      apply one_div_le_one_div_of_le
      <;> linarith
    linarith
  have h6 : |s - s₀| ≤ 1 / (n : ℝ) := by
    rw [abs_le]
    exact ⟨h_s_diff_lower, h_s_diff_upper⟩

  -- Show dist p z₀ ≤ 1/n
  have h_dist1 : dist p.1 z₀.1 = |t - t₀| := by rfl
  have h_dist2 : dist p.2 z₀.2 = |s - s₀| := by rfl
  have h_dist_le : dist p z₀ ≤ 1 / (n : ℝ) := by
    rw [Prod.dist_eq, h_dist1, h_dist2]
    exact max_le h5 h6

  -- Therefore dist p z₀ < ε
  have h_dist_lt : dist p z₀ < ε := by
    calc
      dist p z₀ ≤ 1 / (n : ℝ) := h_dist_le
      _ < ε := hn

  -- Therefore p ∈ ball z₀ ε
  have h9 : dist z₀ p < ε := by
    rw [dist_comm]
    exact h_dist_lt
  have h10 : p ∈ UniformSpace.ball z₀ {p : Y × Y | dist p.1 p.2 < ε} := h9

  -- Therefore p ∈ H ⁻¹' U
  have h11 : p ∈ V U := hU_ball h10

  -- Therefore H p ∈ U
  exact h11

end

end
