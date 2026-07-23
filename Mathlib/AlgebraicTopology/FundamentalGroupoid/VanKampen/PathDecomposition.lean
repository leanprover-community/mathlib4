module

public import Mathlib.Topology.Subpath
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Category.TopCat.Opens

@[expose] public section

open TopologicalSpace Set unitInterval Metric

noncomputable section

universe u

lemma abs_midpoint_le_half {a b z : ℝ} (h1 : a ≤ z) (h2 : z ≤ b) :
    |z - (a + b) / 2| ≤ (b - a) / 2 := by
  rw [abs_le]
  constructor
  · linarith
  · linarith

theorem path_has_subdivision
    {X : Type*} [TopologicalSpace X]
    (𝒰 : Set (TopologicalSpace.Opens X))
    (hcover : ∀ x : X, ∃ U : TopologicalSpace.Opens X, U ∈ 𝒰 ∧ x ∈ U)
    {x y : X} (γ : Path x y) :
    ∃ (n : ℕ) (pts : Fin (n + 1) → X) (covers : Fin n → TopologicalSpace.Opens X)
      (γs : ∀ i : Fin n, Path (pts (Fin.castSucc i)) (pts (Fin.succ i))),
      (∀ i, covers i ∈ 𝒰) ∧
      pts 0 = x ∧ pts (Fin.last n) = y ∧
      (∀ i : Fin n, Set.range (γs i) ⊆ (covers i : Set X)) ∧
      (∀ t : I, ∃ i : Fin n, γ t ∈ (covers i : Set X)) := by
  let ι := { U : TopologicalSpace.Opens X // U ∈ 𝒰 }
  let c : ι → Set I := fun U => γ ⁻¹' (U : Set X)
  have hc₁ : ∀ (i : ι), IsOpen (c i) := by
    intro U
    exact U.val.2.preimage γ.continuous
  have hc₂ : (Set.univ : Set I) ⊆ ⋃ (i : ι), c i := by
    intro t _
    have h₁ : ∃ (U : TopologicalSpace.Opens X), U ∈ 𝒰 ∧ γ t ∈ U := hcover (γ t)
    rcases h₁ with ⟨U, hU, hUt⟩
    let U' : ι := ⟨U, hU⟩
    exact Set.mem_iUnion.mpr ⟨U', hUt⟩
  have hcompact : IsCompact (Set.univ : Set I) := isCompact_univ
  rcases lebesgue_number_lemma_of_metric hcompact hc₁ hc₂ with ⟨δ, hδ_pos, hδ⟩
  have hδ_pos' : 0 < δ := hδ_pos
  have h_arch : ∃ (n : ℕ), 0 < n ∧ 1 / (n : ℝ) < δ := by
    have h : ∃ (n : ℕ), (n : ℝ) > 1 / δ := exists_nat_gt (1 / δ)
    rcases h with ⟨n, hn⟩
    have hn_pos : 0 < n := by
      by_contra h'
      have h'' : n = 0 := by omega
      rw [h''] at hn
      norm_num at hn <;> linarith
    have h1 : 1 / (n : ℝ) < δ := by
      have h2 : 0 < δ := hδ_pos'
      have h3 : (n : ℝ) > 1 / δ := hn
      calc
        1 / (n : ℝ) < 1 / (1 / δ) := by gcongr
        _ = δ := by field_simp [h2.ne'] <;> ring
    exact ⟨n, hn_pos, h1⟩
  rcases h_arch with ⟨n, hn_pos, h1n_lt_δ⟩
  set nr : ℝ := (n : ℝ) with hnr
  have hnr_pos : 0 < nr := by
    rw [hnr]
    exact_mod_cast hn_pos
  let t_pt (i : Fin (n + 1)) : I :=
    ⟨(i.val : ℝ) / nr, by
      have h₁ : 0 ≤ (i.val : ℝ) / nr := by positivity
      have h₂ : (i.val : ℝ) / nr ≤ 1 := by
        have h3 : i.val ≤ n := Nat.lt_succ_iff.mp i.is_lt
        have h41 : (i.val : ℝ) ≤ (n : ℝ) := by exact_mod_cast h3
        have h4 : (i.val : ℝ) ≤ nr := by
          rw [hnr]
          exact h41
        have h5 : (i.val : ℝ) / nr ≤ 1 := by
          calc
            (i.val : ℝ) / nr ≤ nr / nr := by gcongr
            _ = 1 := by
              field_simp [hnr_pos.ne'] <;> ring
        exact h5
      exact ⟨h₁, h₂⟩⟩
  let mid_pt (i : Fin n) : I :=
    ⟨(2 * (i.val : ℝ) + 1) / (2 * nr), by
      have h₁ : 0 ≤ (2 * (i.val : ℝ) + 1) / (2 * nr) := by positivity
      have h₂ : (2 * (i.val : ℝ) + 1) / (2 * nr) ≤ 1 := by
        have h3 : i.val < n := i.is_lt
        have h4 : (i.val : ℝ) < nr := by
          simpa [hnr] using Nat.cast_lt.mpr h3
        have h5 : 2 * (i.val : ℝ) + 1 ≤ 2 * nr := by
          have h6 : (i.val : ℝ) + 1 ≤ nr := by
            have h7 : i.val + 1 ≤ n := Nat.succ_le_iff.mpr h3
            simpa [hnr] using Nat.cast_le.mpr h7
          linarith
        have h7 : (2 * (i.val : ℝ) + 1) / (2 * nr) ≤ 1 := by
          calc
            (2 * (i.val : ℝ) + 1) / (2 * nr) ≤ (2 * nr) / (2 * nr) := by gcongr
            _ = 1 := by
              field_simp [hnr_pos.ne'] <;> ring
        exact h7
      exact ⟨h₁, h₂⟩⟩
  have h_choose : ∀ (i : Fin n), ∃ (U : ι), ball (mid_pt i) δ ⊆ c U := by
    intro i
    exact hδ (mid_pt i) (Set.mem_univ (mid_pt i))
  choose U hU using h_choose
  let covers (i : Fin n) : TopologicalSpace.Opens X := (U i).val
  have hcovers_in : ∀ (i : Fin n), covers i ∈ 𝒰 := fun i => (U i).property
  let pts (i : Fin (n + 1)) : X := γ (t_pt i)
  have h_t0 : (t_pt 0 : ℝ) = 0 := by
    simp [t_pt, hnr]
    <;> field_simp [hnr_pos.ne'] <;> ring
  have h_pts0 : pts 0 = x := by
    have h1 : pts 0 = γ (t_pt 0) := by rfl
    rw [h1]
    have h2 : t_pt 0 = 0 := by
      apply Subtype.ext
      exact h_t0
    rw [h2]
    exact γ.source
  have h_t_last_val : (t_pt (Fin.last n) : ℝ) = 1 := by
    have h1 : (Fin.last n).val = n := by simp [Fin.last]
    have h2 : ((Fin.last n).val : ℝ) / nr = 1 := by
      rw [h1]
      have h3 : (n : ℝ) = nr := by simp [hnr]
      rw [h3]
      field_simp [hnr_pos.ne'] <;> ring
    simpa [t_pt] using h2
  have h_ptsn : pts (Fin.last n) = y := by
    have h1 : pts (Fin.last n) = γ (t_pt (Fin.last n)) := by rfl
    rw [h1]
    have h2 : t_pt (Fin.last n) = 1 := by
      apply Subtype.ext
      exact h_t_last_val
    rw [h2]
    exact γ.target
  have h_half_lt_delta : 1 / (2 * nr) < δ := by
    have h7 : 1 / (2 * nr) < 1 / nr := by
      apply div_lt_div_of_pos_left
      · norm_num
      · positivity
      · linarith
    have h8 : 1 / nr < δ := by
      simpa [hnr] using h1n_lt_δ
    linarith
  have h_half_eq : (1 / nr) / 2 = 1 / (2 * nr) := by
    ring
  have h_t_pt_succ_eq : ∀ (i : Fin n), (t_pt (Fin.succ i) : ℝ) = ((i.val : ℝ) + 1) / nr := by
    intro i
    simp [t_pt, Fin.succ]
    <;> rfl
  have h_mem_ball : ∀ (i : Fin n) (w : I),
      (i.val : ℝ) / nr ≤ (w : ℝ) → (w : ℝ) ≤ ((i.val : ℝ) + 1) / nr → w ∈ ball (mid_pt i) δ := by
    intro i w h1 h2
    set a : ℝ := (i.val : ℝ) / nr with ha
    set b : ℝ := ((i.val : ℝ) + 1) / nr with hb
    set m : ℝ := (2 * (i.val : ℝ) + 1) / (2 * nr) with hm
    have h_eq_m : m = (a + b) / 2 := by
      simp [ha, hb, hm] <;> ring
    have h3 : b - a = 1 / nr := by
      simp [ha, hb, hnr_pos.ne'] <;> field_simp [hnr_pos.ne'] <;> ring
    have h4 : |(w : ℝ) - m| ≤ (b - a) / 2 := by
      rw [h_eq_m]
      exact abs_midpoint_le_half h1 h2
    have h5 : |(w : ℝ) - m| ≤ 1 / (2 * nr) := by
      rw [h3, h_half_eq] at h4
      exact h4
    have h6 : dist w (mid_pt i) ≤ 1 / (2 * nr) := by
      have h_mid : ((mid_pt i) : ℝ) = m := by
        simp [mid_pt, hm] <;> rfl
      have h : dist w (mid_pt i) = |(w : ℝ) - (mid_pt i : ℝ)| := by
        change dist (w : ℝ) ((mid_pt i) : ℝ) = |(w : ℝ) - (mid_pt i : ℝ)|
        rw [Real.dist_eq]
        <;> rfl
      rw [h, h_mid]
      exact h5
    have h7 : dist w (mid_pt i) < δ := by
      exact lt_of_le_of_lt h6 h_half_lt_delta
    exact h7
  have h_interval_subset : ∀ (i : Fin n),
      {w : I | (i.val : ℝ) / nr ≤ (w : ℝ) ∧ (w : ℝ) ≤ ((i.val : ℝ) + 1) / nr} ⊆ c (U i) := by
    intro i
    intro w hw
    have h1 : (i.val : ℝ) / nr ≤ (w : ℝ) := hw.1
    have h2 : (w : ℝ) ≤ ((i.val : ℝ) + 1) / nr := hw.2
    have h3 : w ∈ ball (mid_pt i) δ := h_mem_ball i w h1 h2
    exact hU i h3
  have h_image_subset : ∀ (i : Fin n),
      γ '' (Set.Icc (t_pt (Fin.castSucc i)) (t_pt (Fin.succ i))) ⊆ (covers i : Set X) := by
    intro i
    have h1 : ∀ (w : I), w ∈ Set.Icc (t_pt (Fin.castSucc i)) (t_pt (Fin.succ i)) → w ∈ c (U i) := by
      intro w hw
      have h2 : (t_pt (Fin.castSucc i) : ℝ) ≤ (w : ℝ) := hw.1
      have h3 : (w : ℝ) ≤ (t_pt (Fin.succ i) : ℝ) := hw.2
      have h4 : (w : ℝ) ≤ ((i.val : ℝ) + 1) / nr := by
        rw [h_t_pt_succ_eq i] at h3
        exact h3
      exact h_interval_subset i ⟨h2, h4⟩
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    exact h1 w hw
  let γs (i : Fin n) : Path (pts (Fin.castSucc i)) (pts (Fin.succ i)) :=
    γ.subpath (t_pt (Fin.castSucc i)) (t_pt (Fin.succ i))
  have h_main1 : ∀ (i : Fin n), Set.range (γs i) ⊆ (covers i : Set X) := by
    intro i
    have h_le : (t_pt (Fin.castSucc i) : ℝ) ≤ (t_pt (Fin.succ i) : ℝ) := by
      simp [t_pt]
      <;> have h : (i.val : ℝ) ≤ (i.val : ℝ) + 1 := by linarith
      exact div_le_div_of_nonneg_right h (by positivity)
    have h_range : Set.range (γs i) = γ '' (Set.Icc (t_pt (Fin.castSucc i)) (t_pt (Fin.succ i))) := by
      apply Path.range_subpath_of_le
      exact h_le
    rw [h_range]
    exact h_image_subset i
  have h_main2 : ∀ (t : I), ∃ (i : Fin n), γ t ∈ (covers i : Set X) := by
    intro t
    by_cases h_t_eq_one : (t : ℝ) = 1
    · -- Case t = 1: use the last interval i = n - 1
      have h_n_pos : 0 < n := hn_pos
      let i : Fin n := ⟨n - 1, by omega⟩
      have h1 : (i.val : ℝ) / nr ≤ (t : ℝ) := by
        have h_i_val : i.val = n - 1 := by simp [i]
        rw [h_t_eq_one, h_i_val]
        have h_pos : 0 < nr := hnr_pos
        have h : ((n - 1 : ℕ) : ℝ) / nr ≤ 1 := by
          have h2 : ((n - 1 : ℕ) : ℝ) ≤ nr := by
            simp [hnr, h_n_pos] <;> omega
          rw [div_le_one h_pos]
          exact h2
        exact h
      have h2 : (t : ℝ) ≤ ((i.val : ℝ) + 1) / nr := by
        have h_i_val : i.val = n - 1 := by simp [i]
        rw [h_t_eq_one, h_i_val]
        have h_pos : 0 < nr := hnr_pos
        have h3 : ((n - 1 : ℕ) : ℝ) + 1 = nr := by
          have h4 : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
            simp [h_n_pos] <;> omega
          rw [h4, hnr]
        rw [h3]
        field_simp [h_pos.ne'] <;> ring_nf <;> norm_num
      have h3 : t ∈ c (U i) := h_interval_subset i ⟨h1, h2⟩
      exact ⟨i, h3⟩
    · -- Case t ≠ 1: then t < 1, so k < n
      have h_t_lt_one : (t : ℝ) < 1 := by
        have h : (t : ℝ) ≤ 1 := t.prop.2
        exact lt_of_le_of_ne h h_t_eq_one
      let k_int : ℤ := ⌊(t : ℝ) * nr⌋
      have h_k1 : (k_int : ℝ) ≤ (t : ℝ) * nr := Int.floor_le ((t : ℝ) * nr)
      have h_k2 : (t : ℝ) * nr < (k_int : ℝ) + 1 := Int.lt_floor_add_one ((t : ℝ) * nr)
      have h_t_nonneg : 0 ≤ (t : ℝ) := t.prop.1
      have h_nr_pos : 0 < nr := hnr_pos
      have h_pos : 0 ≤ (t : ℝ) * nr := mul_nonneg h_t_nonneg (le_of_lt h_nr_pos)
      have h_k_nonneg_int : 0 ≤ k_int := by
        exact Int.floor_nonneg.mpr h_pos
      let k : ℕ := k_int.toNat
      have h_k_eq : (k : ℤ) = k_int := by
        simp [k, Int.toNat_of_nonneg h_k_nonneg_int]
      have h_k1' : (k : ℝ) ≤ (t : ℝ) * nr := by
        have h : ((k : ℤ) : ℝ) = (k_int : ℝ) := by exact_mod_cast h_k_eq
        have h' : (k : ℝ) = ((k : ℤ) : ℝ) := by exact?
        rw [h', h]
        exact h_k1
      have h_k2' : (t : ℝ) * nr < (k : ℝ) + 1 := by
        have h : ((k : ℤ) : ℝ) = (k_int : ℝ) := by exact_mod_cast h_k_eq
        have h' : (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) := by simp
        have h'' : ((k + 1 : ℕ) : ℝ) = ((k : ℤ) + 1 : ℝ) := by exact?
        rw [h', h'']
        have h3 : ((k : ℤ) + 1 : ℝ) = (k_int : ℝ) + 1 := by
          rw [h_k_eq] <;> rfl
        rw [h3]
        exact h_k2
      have h_k_lt_n : k < n := by
        by_contra h
        have h' : k ≥ n := by linarith
        have h''1 : (k : ℝ) ≥ (n : ℝ) := by exact_mod_cast h'
        have h'' : (k : ℝ) ≥ nr := by
          rw [hnr]
          exact h''1
        have h_contra : (t : ℝ) * nr < (k : ℝ) + 1 := h_k2'
        have h_t_lt_one' : (t : ℝ) < 1 := h_t_lt_one
        nlinarith
      let i : Fin n := ⟨k, h_k_lt_n⟩
      have h1 : (i.val : ℝ) / nr ≤ (t : ℝ) := by
        have h : (i.val : ℝ) ≤ (t : ℝ) * nr := h_k1'
        have h_pos : 0 < nr := hnr_pos
        have h_div : (i.val : ℝ) / nr ≤ ((t : ℝ) * nr) / nr := by
          apply div_le_div_of_nonneg_right h
          positivity
        have h_eq : ((t : ℝ) * nr) / nr = (t : ℝ) := by
          field_simp [h_pos.ne'] <;> ring
        rw [h_eq] at h_div
        exact h_div
      have h2 : (t : ℝ) ≤ ((i.val : ℝ) + 1) / nr := by
        have h : (t : ℝ) * nr < (i.val : ℝ) + 1 := h_k2'
        have h_pos : 0 < nr := hnr_pos
        have h_lt : (t : ℝ) < ((i.val : ℝ) + 1) / nr := by
          calc
            (t : ℝ) = ((t : ℝ) * nr) / nr := by
              field_simp [h_pos.ne'] <;> ring
            _ < ((i.val : ℝ) + 1) / nr := by
              apply div_lt_div_of_pos_right h h_pos
        exact le_of_lt h_lt
      have h3 : t ∈ c (U i) := h_interval_subset i ⟨h1, h2⟩
      exact ⟨i, h3⟩
  exact ⟨n, pts, covers, γs, hcovers_in, h_pts0, h_ptsn, h_main1, h_main2⟩

/-- Stronger version of path_has_subdivision that also returns the subdivision points ts in I
    and the fact that γs are subpaths of γ. -/
theorem path_has_subdivision_with_ts
    {X : Type*} [TopologicalSpace X]
    (𝒰 : Set (TopologicalSpace.Opens X))
    (hcover : ∀ x : X, ∃ U : TopologicalSpace.Opens X, U ∈ 𝒰 ∧ x ∈ U)
    {x y : X} (γ : Path x y) :
    ∃ (n : ℕ) (ts : Fin (n + 1) → I) (h_ts0 : ts 0 = 0) (h_ts1 : ts (Fin.last n) = 1)
      (h_ts_strict : StrictMono ts)
      (covers : Fin n → TopologicalSpace.Opens X)
      (hcovers_in : ∀ i, covers i ∈ 𝒰)
      (h_range : ∀ i : Fin n, Set.range (γ.subpath (ts (Fin.castSucc i)) (ts (Fin.succ i))) ⊆ (covers i : Set X)),
      True := by
  let ι := { U : TopologicalSpace.Opens X // U ∈ 𝒰 }
  let c : ι → Set I := fun U => γ ⁻¹' (U : Set X)
  have hc₁ : ∀ (i : ι), IsOpen (c i) := by
    intro U
    exact U.val.2.preimage γ.continuous
  have hc₂ : (Set.univ : Set I) ⊆ ⋃ (i : ι), c i := by
    intro t _
    have h₁ : ∃ (U : TopologicalSpace.Opens X), U ∈ 𝒰 ∧ γ t ∈ U := hcover (γ t)
    rcases h₁ with ⟨U, hU, hUt⟩
    let U' : ι := ⟨U, hU⟩
    exact Set.mem_iUnion.mpr ⟨U', hUt⟩
  have hcompact : IsCompact (Set.univ : Set I) := isCompact_univ
  rcases lebesgue_number_lemma_of_metric hcompact hc₁ hc₂ with ⟨δ, hδ_pos, hδ⟩
  have hδ_pos' : 0 < δ := hδ_pos
  have h_arch : ∃ (n : ℕ), 0 < n ∧ 1 / (n : ℝ) < δ := by
    have h : ∃ (n : ℕ), (n : ℝ) > 1 / δ := exists_nat_gt (1 / δ)
    rcases h with ⟨n, hn⟩
    have hn_pos : 0 < n := by
      by_contra h'
      have h'' : n = 0 := by omega
      rw [h''] at hn
      norm_num at hn <;> linarith
    have h1 : 1 / (n : ℝ) < δ := by
      have h2 : 0 < δ := hδ_pos'
      have h3 : (n : ℝ) > 1 / δ := hn
      calc
        1 / (n : ℝ) < 1 / (1 / δ) := by gcongr
        _ = δ := by field_simp [h2.ne'] <;> ring
    exact ⟨n, hn_pos, h1⟩
  rcases h_arch with ⟨n, hn_pos, h1n_lt_δ⟩
  set nr : ℝ := (n : ℝ) with hnr
  have hnr_pos : 0 < nr := by
    rw [hnr]
    exact_mod_cast hn_pos
  let t_pt (i : Fin (n + 1)) : I :=
    ⟨(i.val : ℝ) / nr, by
      have h₁ : 0 ≤ (i.val : ℝ) / nr := by positivity
      have h₂ : (i.val : ℝ) / nr ≤ 1 := by
        have h3 : i.val ≤ n := Nat.lt_succ_iff.mp i.is_lt
        have h41 : (i.val : ℝ) ≤ (n : ℝ) := by exact_mod_cast h3
        have h4 : (i.val : ℝ) ≤ nr := by
          rw [hnr]
          exact h41
        have h5 : (i.val : ℝ) / nr ≤ 1 := by
          calc
            (i.val : ℝ) / nr ≤ nr / nr := by gcongr
            _ = 1 := by
              field_simp [hnr_pos.ne'] <;> ring
        exact h5
      exact ⟨h₁, h₂⟩⟩
  let mid_pt (i : Fin n) : I :=
    ⟨(2 * (i.val : ℝ) + 1) / (2 * nr), by
      have h₁ : 0 ≤ (2 * (i.val : ℝ) + 1) / (2 * nr) := by positivity
      have h₂ : (2 * (i.val : ℝ) + 1) / (2 * nr) ≤ 1 := by
        have h3 : i.val < n := i.is_lt
        have h4 : (i.val : ℝ) < nr := by
          simpa [hnr] using Nat.cast_lt.mpr h3
        have h5 : 2 * (i.val : ℝ) + 1 ≤ 2 * nr := by
          have h6 : (i.val : ℝ) + 1 ≤ nr := by
            have h7 : i.val + 1 ≤ n := Nat.succ_le_iff.mpr h3
            simpa [hnr] using Nat.cast_le.mpr h7
          linarith
        have h7 : (2 * (i.val : ℝ) + 1) / (2 * nr) ≤ 1 := by
          calc
            (2 * (i.val : ℝ) + 1) / (2 * nr) ≤ (2 * nr) / (2 * nr) := by gcongr
            _ = 1 := by
              field_simp [hnr_pos.ne'] <;> ring
        exact h7
      exact ⟨h₁, h₂⟩⟩
  have h_choose : ∀ (i : Fin n), ∃ (U : ι), ball (mid_pt i) δ ⊆ c U := by
    intro i
    exact hδ (mid_pt i) (Set.mem_univ (mid_pt i))
  choose U hU using h_choose
  let covers (i : Fin n) : TopologicalSpace.Opens X := (U i).val
  have hcovers_in : ∀ (i : Fin n), covers i ∈ 𝒰 := fun i => (U i).property
  have h_t0 : (t_pt 0 : ℝ) = 0 := by
    simp [t_pt, hnr]
    <;> field_simp [hnr_pos.ne'] <;> ring
  have h_ts0 : t_pt 0 = 0 := by
    apply Subtype.ext
    exact h_t0
  have h_t_last_val : (t_pt (Fin.last n) : ℝ) = 1 := by
    have h1 : (Fin.last n).val = n := by simp [Fin.last]
    have h2 : ((Fin.last n).val : ℝ) / nr = 1 := by
      rw [h1]
      have h3 : (n : ℝ) = nr := by simp [hnr]
      rw [h3]
      field_simp [hnr_pos.ne'] <;> ring
    simpa [t_pt] using h2
  have h_ts1 : t_pt (Fin.last n) = 1 := by
    apply Subtype.ext
    exact h_t_last_val
  have h_ts_strict : StrictMono t_pt := by
    intro i j h
    have h' : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast h
    have h'' : (i.val : ℝ) / nr < (j.val : ℝ) / nr := by
      gcongr
    exact Subtype.mk_lt_mk.mpr h''
  have h_half_lt_delta : 1 / (2 * nr) < δ := by
    have h7 : 1 / (2 * nr) < 1 / nr := by
      apply div_lt_div_of_pos_left
      · norm_num
      · positivity
      · linarith
    have h8 : 1 / nr < δ := by
      simpa [hnr] using h1n_lt_δ
    linarith
  have h_half_eq : (1 / nr) / 2 = 1 / (2 * nr) := by
    ring
  have h_t_pt_succ_eq : ∀ (i : Fin n), (t_pt (Fin.succ i) : ℝ) = ((i.val : ℝ) + 1) / nr := by
    intro i
    simp [t_pt, Fin.succ]
    <;> rfl
  have h_mem_ball : ∀ (i : Fin n) (w : I),
      (i.val : ℝ) / nr ≤ (w : ℝ) → (w : ℝ) ≤ ((i.val : ℝ) + 1) / nr → w ∈ ball (mid_pt i) δ := by
    intro i w h1 h2
    set a : ℝ := (i.val : ℝ) / nr with ha
    set b : ℝ := ((i.val : ℝ) + 1) / nr with hb
    set m : ℝ := (2 * (i.val : ℝ) + 1) / (2 * nr) with hm
    have h_eq_m : m = (a + b) / 2 := by
      simp [ha, hb, hm] <;> ring
    have h3 : b - a = 1 / nr := by
      simp [ha, hb, hnr_pos.ne'] <;> field_simp [hnr_pos.ne'] <;> ring
    have h4 : |(w : ℝ) - m| ≤ (b - a) / 2 := by
      rw [h_eq_m]
      exact abs_midpoint_le_half h1 h2
    have h5 : |(w : ℝ) - m| ≤ 1 / (2 * nr) := by
      rw [h3, h_half_eq] at h4
      exact h4
    have h6 : dist w (mid_pt i) ≤ 1 / (2 * nr) := by
      have h_mid : ((mid_pt i) : ℝ) = m := by
        simp [mid_pt, hm] <;> rfl
      have h : dist w (mid_pt i) = |(w : ℝ) - (mid_pt i : ℝ)| := by
        change dist (w : ℝ) ((mid_pt i) : ℝ) = |(w : ℝ) - (mid_pt i : ℝ)|
        rw [Real.dist_eq]
        <;> rfl
      rw [h, h_mid]
      exact h5
    have h7 : dist w (mid_pt i) < δ := by
      exact lt_of_le_of_lt h6 h_half_lt_delta
    exact h7
  have h_interval_subset : ∀ (i : Fin n),
      {w : I | (i.val : ℝ) / nr ≤ (w : ℝ) ∧ (w : ℝ) ≤ ((i.val : ℝ) + 1) / nr} ⊆ c (U i) := by
    intro i
    intro w hw
    have h1 : (i.val : ℝ) / nr ≤ (w : ℝ) := hw.1
    have h2 : (w : ℝ) ≤ ((i.val : ℝ) + 1) / nr := hw.2
    have h3 : w ∈ ball (mid_pt i) δ := h_mem_ball i w h1 h2
    exact hU i h3
  have h_image_subset : ∀ (i : Fin n),
      γ '' (Set.Icc (t_pt (Fin.castSucc i)) (t_pt (Fin.succ i))) ⊆ (covers i : Set X) := by
    intro i
    have h1 : ∀ (w : I), w ∈ Set.Icc (t_pt (Fin.castSucc i)) (t_pt (Fin.succ i)) → w ∈ c (U i) := by
      intro w hw
      have h2 : (t_pt (Fin.castSucc i) : ℝ) ≤ (w : ℝ) := hw.1
      have h3 : (w : ℝ) ≤ (t_pt (Fin.succ i) : ℝ) := hw.2
      have h4 : (w : ℝ) ≤ ((i.val : ℝ) + 1) / nr := by
        rw [h_t_pt_succ_eq i] at h3
        exact h3
      exact h_interval_subset i ⟨h2, h4⟩
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    exact h1 w hw
  have h_range : ∀ (i : Fin n), Set.range (γ.subpath (t_pt (Fin.castSucc i)) (t_pt (Fin.succ i))) ⊆ (covers i : Set X) := by
    intro i
    have h_le : (t_pt (Fin.castSucc i) : ℝ) ≤ (t_pt (Fin.succ i) : ℝ) := by
      simp [t_pt]
      <;> have h : (i.val : ℝ) ≤ (i.val : ℝ) + 1 := by linarith
      exact div_le_div_of_nonneg_right h (by positivity)
    have h_range2 : Set.range (γ.subpath (t_pt (Fin.castSucc i)) (t_pt (Fin.succ i))) =
        γ '' (Set.Icc (t_pt (Fin.castSucc i)) (t_pt (Fin.succ i))) := by
      apply Path.range_subpath_of_le
      exact h_le
    rw [h_range2]
    exact h_image_subset i
  exact ⟨n, t_pt, h_ts0, h_ts1, h_ts_strict, covers, hcovers_in, h_range, trivial⟩

end

end
