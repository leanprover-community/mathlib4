module

public import Mathlib
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.CanonicalCocone
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.UniversalProperty
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.CommonRefinement
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.SingleCovered
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.ComposeMorphisms
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.CleanMapFromAdapted
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.RefinementLemma
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.SplitLemmaWork
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.SubpathHomotopyRange
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.EqToHomSandwich
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.EqToHomSandwich

@[expose] public section

open TopologicalSpace CategoryTheory Limits IsAdaptedSubdivision

open scoped unitInterval

noncomputable section

universe u

variable (X : Type u) [TopologicalSpace X]
variable (𝒰 : Set (Opens X))
variable (hcover : ∀ x : X, ∃ U : Opens X, U ∈ 𝒰 ∧ x ∈ U)
variable (hfinite_intersections :
  ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)

variable (s : Cocone
    (((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
      Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor))

include hcover hfinite_intersections s

/-- Helper: the range of a subpath is the image of the interval. -/
lemma subpath_range_subset {X : Type*} [TopologicalSpace X] {x y : X} (γ : Path x y)
    {s₁ s₂ : I} (h_lt : s₁ < s₂)
    {U : Opens X} (h : ∀ (t : I), s₁ ≤ t → t ≤ s₂ → γ t ∈ U) :
    Set.range (γ.subpath s₁ s₂) ⊆ (U : Set X) := by
  have h_range_eq : Set.range (γ.subpath s₁ s₂) = γ '' Set.Icc s₁ s₂ := by
    rw [Path.range_subpath γ s₁ s₂]
    <;> rw [Set.uIcc_of_le (le_of_lt h_lt)]
  rw [h_range_eq]
  intro z hz
  rcases hz with ⟨t, ht, rfl⟩
  exact h t ht.1 ht.2

/-- Adding a single point to an adapted subdivision does not change the morphism.

    Proof sketch:
    1. Use the universal property to get explicit ts, covers for both S and S'
    2. Show that ts' is ts with t inserted at position k
    3. Show that covers' is covers with covers k repeated at positions k and k+1
    4. Use single_covered_split_eq to show the two new morphisms compose to the original
    5. Use comp_list_split_explicit to show the overall composition is unchanged -/
theorem my_map_from_adapted_subdivision_refines_one_clean
    {x y : X} {γ : Path x y} {S : Finset I} {t : I}
    (hS : IsAdaptedSubdivision 𝒰 γ S)
    (hS' : IsAdaptedSubdivision 𝒰 γ (S ∪ {t})) :
    my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS =
    my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS' := by
  classical
  by_cases h_t_in_S : t ∈ S
  · -- Case 1: t ∈ S, then S ∪ {t} = S, so trivial
    have h_set_eq : S ∪ {t} = S := by
      ext x
      simp [h_t_in_S] <;> tauto
    have h_goal : ∀ (S1 S2 : Finset I) (h_eq : S1 = S2)
        (h1 : IsAdaptedSubdivision 𝒰 γ S1)
        (h2 : IsAdaptedSubdivision 𝒰 γ S2),
        my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s h1 =
        my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s h2 := by
      intro S1 S2 h_eq h1 h2
      subst h_eq
      congr
      <;> exact Subsingleton.elim h1 h2
    have h_eq : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS' =
        my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS :=
      h_goal (S ∪ {t}) S h_set_eq hS' hS
    exact h_eq.symm
  · -- Case 2: t ∉ S
    have h_t_not_in_S : t ∉ S := h_t_in_S
    -- Get the canonical decomposition for S
    have h0_in_S : (0 : I) ∈ S := hS.1
    have h1_in_S : (1 : I) ∈ S := hS.2.1
    have hS_nonempty : S.Nonempty := ⟨0, h0_in_S⟩
    let k : ℕ := S.card
    have hk : S.card = k := rfl
    have hk_pos : 0 < k := Finset.card_pos.mpr hS_nonempty
    have hk_ge2 : 2 ≤ k := by
      have h0_ne_1 : (0 : I) ≠ (1 : I) := by
        intro h
        have h' : (0 : ℝ) = (1 : ℝ) := congr_arg (fun x : I => (x : ℝ)) h
        norm_num at h' <;> exact h'
      have h : ({(0 : I), (1 : I)} : Finset I) ⊆ S := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with (rfl | rfl) <;> tauto
      have h2 : ({(0 : I), (1 : I)} : Finset I).card ≤ S.card := Finset.card_le_card h
      have h3 : ({(0 : I), (1 : I)} : Finset I).card = 2 := by
        simp [h0_ne_1] <;> rfl
      rw [h3] at h2
      exact h2
    let e : Fin k ↪o I := S.orderEmbOfFin hk
    have h_e_mem : ∀ (i : Fin k), e i ∈ S := Finset.orderEmbOfFin_mem S hk
    have h_e_strict_mono : StrictMono e := OrderEmbedding.strictMono e
    have h_e_image : Finset.image e Finset.univ = S := Finset.image_orderEmbOfFin_univ S hk
    let n : ℕ := k - 1
    have hk_eq : k = n + 1 := by omega
    let ts_S (i : Fin (n + 1)) : I := e ⟨i.val, by rw [hk_eq] <;> exact i.is_lt⟩
    have h_ts_S_strict : StrictMono ts_S := by
      intro i j h
      exact h_e_strict_mono (by simpa [ts_S] using h)
    have h_ts_S_image : Finset.image ts_S Finset.univ = S := by
      have h1 : Finset.image ts_S Finset.univ = Finset.image e Finset.univ := by
        ext x
        simp only [ts_S, Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨i, rfl⟩
          exact ⟨⟨i.val, by rw [hk_eq]; exact i.is_lt⟩, rfl⟩
        · rintro ⟨j, rfl⟩
          have h_j_lt : j.val < n + 1 := by rw [←hk_eq]; exact j.is_lt
          let i : Fin (n + 1) := ⟨j.val, h_j_lt⟩
          exact ⟨i, by simp [i] <;> rfl⟩
      rw [h1, h_e_image]
    have h_ts0_eq : ts_S 0 = (0 : I) := by
      have h0 : ts_S 0 ∈ S := by
        have h : ts_S 0 ∈ Finset.image ts_S Finset.univ := Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
        rw [h_ts_S_image] at h
        exact h
      have h0_in : (0 : I) ∈ S := h0_in_S
      have h_le : (0 : I) ≤ ts_S 0 := by
        exact?
      have h_ge : ts_S 0 ≤ (0 : I) := by
        have h_exists : ∃ (i : Fin (n + 1)), ts_S i = (0 : I) := by
          have h : (0 : I) ∈ Finset.image ts_S Finset.univ := by rw [h_ts_S_image] <;> exact h0_in
          rcases Finset.mem_image.mp h with ⟨i, _, h_eq⟩
          exact ⟨i, h_eq⟩
        rcases h_exists with ⟨i, hi⟩
        have h_i_ge : 0 ≤ i := by
          exact?
        have h_mono : StrictMono ts_S := h_ts_S_strict
        have h : ts_S 0 ≤ ts_S i := h_mono.monotone h_i_ge
        rw [hi] at h
        exact h
      exact le_antisymm h_ge h_le
    have h_ts1_eq : ts_S (Fin.last n) = (1 : I) := by
      have h1 : ts_S (Fin.last n) ∈ S := by
        have h : ts_S (Fin.last n) ∈ Finset.image ts_S Finset.univ := Finset.mem_image.mpr ⟨Fin.last n, Finset.mem_univ _, rfl⟩
        rw [h_ts_S_image] at h
        exact h
      have h1_in : (1 : I) ∈ S := h1_in_S
      have h_le : ts_S (Fin.last n) ≤ (1 : I) := by
        exact?
      have h_ge : (1 : I) ≤ ts_S (Fin.last n) := by
        have h_exists : ∃ (i : Fin (n + 1)), ts_S i = (1 : I) := by
          have h : (1 : I) ∈ Finset.image ts_S Finset.univ := by rw [h_ts_S_image] <;> exact h1_in
          rcases Finset.mem_image.mp h with ⟨i, _, h_eq⟩
          exact ⟨i, h_eq⟩
        rcases h_exists with ⟨i, hi⟩
        have h_i_le : i ≤ Fin.last n := by exact Fin.le_last i
        have h_mono : StrictMono ts_S := h_ts_S_strict
        have h : ts_S i ≤ ts_S (Fin.last n) := h_mono.monotone h_i_le
        rw [hi] at h
        exact h
      exact le_antisymm h_le h_ge
    -- Get canonical covers for S
    have h_main_exists : ∃ (covers_S : Fin n → Opens X),
        (∀ i, covers_S i ∈ 𝒰) ∧
        (∀ i, ∀ (t_val : I), ts_S (Fin.castSucc i) ≤ t_val → t_val ≤ ts_S (Fin.succ i) → γ t_val ∈ (covers_S i : Set X)) := by
      have h_helper : ∀ (i : Fin n), ∃ (U : Opens X), U ∈ 𝒰 ∧ ∀ (t_val : I), ts_S (Fin.castSucc i) ≤ t_val → t_val ≤ ts_S (Fin.succ i) → γ t_val ∈ (U : Set X) := by
        intro i
        let s₁ := ts_S (Fin.castSucc i)
        let s₂ := ts_S (Fin.succ i)
        have h_s1_in : s₁ ∈ S := by
          have h : s₁ ∈ Finset.image ts_S Finset.univ := Finset.mem_image.mpr ⟨Fin.castSucc i, Finset.mem_univ _, rfl⟩
          rw [h_ts_S_image] at h
          exact h
        have h_s2_in : s₂ ∈ S := by
          have h : s₂ ∈ Finset.image ts_S Finset.univ := Finset.mem_image.mpr ⟨Fin.succ i, Finset.mem_univ _, rfl⟩
          rw [h_ts_S_image] at h
          exact h
        have h_lt : s₁ < s₂ := h_ts_S_strict (by
          apply Fin.lt_iff_val_lt_val.mpr
          simp [Fin.castSucc, Fin.succ] <;> omega)
        have h_no_between : ∀ (x : I), x ∈ S → s₁ < x → x < s₂ → False := by
          intro x hx h1 h2
          have h_exists : ∃ (j : Fin k), e j = x := by
            have h : x ∈ Finset.image e Finset.univ := by rw [h_e_image] <;> exact hx
            rcases Finset.mem_image.mp h with ⟨j, _, rfl⟩
            exact ⟨j, rfl⟩
          rcases h_exists with ⟨j, hj⟩
          have h_j_gt : (Fin.castSucc i).val < j.val := by
            have h4 : ts_S (Fin.castSucc i) < e j := by rw [hj] <;> exact h1
            exact Fin.lt_iff_val_lt_val.mp (by simpa [ts_S] using h4)
          have h_j_lt : j.val < (Fin.succ i).val := by
            have h4 : e j < ts_S (Fin.succ i) := by rw [hj] <;> exact h2
            exact Fin.lt_iff_val_lt_val.mp (by simpa [ts_S] using h4)
          have h1 : i.val < j.val := by
            simpa [Fin.castSucc] using h_j_gt
          have h2 : j.val < i.val + 1 := by
            simpa [Fin.succ] using h_j_lt
          omega
        exact hS.2.2 s₁ s₂ h_s1_in h_s2_in h_lt h_no_between
      choose covers_S hcover_mem_S h_range_S using h_helper
      exact ⟨covers_S, hcover_mem_S, h_range_S⟩
    rcases h_main_exists with ⟨covers_S, hcover_mem_S, h_range_S⟩
    -- Now we have ts_S, covers_S for S
    -- We need to find where t fits in the subdivision
    have h_t_between : (0 : I) ≤ t ∧ t < (1 : I) := by
      constructor
      · exact?
      · by_contra h
        have h' : (1 : I) ≤ t := by exact le_of_not_gt h
        have h1_in : (1 : I) ∈ S := h1_in_S
        have h_t_in_S' : t ∈ S ∪ {t} := by simp
        have h2 : t ≤ (1 : I) := by
          exact?

        have h4 : t = (1 : I) := by exact le_antisymm h2 h'
        rw [h4] at h_t_not_in_S
        exact h_t_not_in_S h1_in
    let P : Fin k → Prop := fun i => e i ≤ t
    let zero_Fin_k : Fin k := ⟨0, hk_pos⟩
    have h_i0_P : P zero_Fin_k := by
      dsimp only [P, zero_Fin_k]
      have h_e0 : e zero_Fin_k = ts_S (0 : Fin (n + 1)) := by
        simp [ts_S, zero_Fin_k] <;> rfl
      rw [h_e0, h_ts0_eq]
      exact h_t_between.1
    let i_max : Fin k := Finset.max' (Finset.filter P Finset.univ) ⟨zero_Fin_k, by simp [h_i0_P]⟩
    have h_i_max_mem : i_max ∈ Finset.filter P Finset.univ := Finset.max'_mem _ _
    have h_i_max_P : P i_max := (Finset.mem_filter.mp h_i_max_mem).2
    have h_i_max_le_t : e i_max ≤ t := h_i_max_P
    have h_not : ¬ ((1 : I) ≤ t) := by
      intro h
      have h' : t < (1 : I) := h_t_between.2
      have h'' : (t : ℝ) < (1 : ℝ) := by exact_mod_cast h'
      have h''' : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast h
      linarith
    have h_k_pos : 0 < k := by omega
    let last_k : Fin k := ⟨k - 1, by omega⟩
    have h_e_last : e last_k = (1 : I) := by
      have h2 : (1 : I) ∈ S := h1_in_S
      have h : e last_k = (1 : I) := by
        exact?
      exact h
    have h_i_max_lt_last : i_max < last_k := by
      have h1 : e i_max < e last_k := by
        rw [h_e_last]
        exact lt_of_le_of_lt h_i_max_le_t h_t_between.2
      exact h_e_strict_mono.lt_iff_lt.mp h1
    let m_val : ℕ := i_max.val
    have h_m_val_lt_n : m_val < n := by
      dsimp only [n, m_val]
      have h : i_max.val < last_k.val := Fin.lt_iff_val_lt_val.mp h_i_max_lt_last
      simpa [last_k, Fin.last] using h
    let m : Fin n := ⟨m_val, h_m_val_lt_n⟩
    have h_e_i_max_le_t : e i_max ≤ t := h_i_max_P
    let i_succ : Fin k := ⟨i_max.val + 1, by omega⟩
    have h_i_succ_not_P : ¬ P i_succ := by
      intro h
      have h6 : i_succ ∈ Finset.filter P Finset.univ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      have h7 : i_succ ≤ i_max := Finset.le_max' (Finset.filter P Finset.univ) i_succ h6
      have h8 : i_max < i_succ := by
        apply Fin.lt_iff_val_lt_val.mpr
        simp [i_succ] <;> omega
      have h9 : ¬ (i_succ ≤ i_max) := by
        intro h10
        have h11 : i_max < i_succ := h8
        exact Fin.not_le.mpr h11 h10
      exact h9 h7
    have h_t_lt_e_succ : t < e i_succ := by
      dsimp only [P] at h_i_succ_not_P
      exact lt_of_not_ge h_i_succ_not_P
    have h_e_i_max_lt_t : e i_max < t := by
      apply lt_of_le_of_ne h_e_i_max_le_t
      intro h_eq
      have h9 : e i_max = t := h_eq
      have h10 : e i_max ∈ S := h_e_mem i_max
      rw [h9] at h10
      exact h_t_not_in_S h10
    have h_m_left : ts_S (Fin.castSucc m) < t := by
      simpa [ts_S, m] using h_e_i_max_lt_t
    have h_m_right : t < ts_S (Fin.succ m) := by
      simpa [ts_S, m] using h_t_lt_e_succ
    -- Define ts' explicitly by inserting t at position m+1
    let ts' (i : Fin (n + 2)) : I :=
      if h : i.val ≤ m.val then
        ts_S ⟨i.val, by omega⟩
      else if h' : i.val = m.val + 1 then
        t
      else
        ts_S ⟨i.val - 1, by omega⟩
    -- Define covers' explicitly by duplicating covers_S m at positions m and m+1
    let covers' (i : Fin (n + 1)) : Opens X :=
      if h : i.val < m.val then
        covers_S ⟨i.val, by omega⟩
      else if h' : i.val = m.val then
        covers_S m
      else if h'' : i.val = m.val + 1 then
        covers_S m
      else
        covers_S ⟨i.val - 1, by omega⟩
    -- Prove ts' is strictly monotone
    have h_ts'_strict : StrictMono ts' := by
      intro i j h_lt
      dsimp only [ts']
      have h_ij : i.val < j.val := by
        exact Fin.lt_iff_val_lt_val.mp h_lt
      by_cases h_i_le_m : i.val ≤ m.val
      · by_cases h_j_le_m : j.val ≤ m.val
        · rw [dif_pos h_i_le_m, dif_pos h_j_le_m]
          have h_lt2 : (⟨i.val, by omega⟩ : Fin (n + 1)) < (⟨j.val, by omega⟩ : Fin (n + 1)) := by
            apply Fin.lt_iff_val_lt_val.mpr
            exact h_ij
          exact h_ts_S_strict h_lt2
        · rw [dif_pos h_i_le_m]
          by_cases h_j_eq : j.val = m.val + 1
          · rw [dif_neg (by omega), dif_pos h_j_eq]
            have h_i_le_m2 : (⟨i.val, by omega⟩ : Fin (n + 1)) ≤ Fin.castSucc m := by
              apply Fin.le_iff_val_le_val.mpr
              exact h_i_le_m
            have h1 : ts_S ⟨i.val, by omega⟩ ≤ ts_S (Fin.castSucc m) := h_ts_S_strict.monotone h_i_le_m2
            exact lt_of_le_of_lt h1 h_m_left
          · rw [dif_neg (by omega), dif_neg h_j_eq]
            have h_i_lt_j1 : i.val < j.val - 1 := by omega
            have h_lt2 : (⟨i.val, by omega⟩ : Fin (n + 1)) < (⟨j.val - 1, by omega⟩ : Fin (n + 1)) := by
              apply Fin.lt_iff_val_lt_val.mpr
              exact h_i_lt_j1
            have h1 : ts_S ⟨i.val, by omega⟩ < ts_S ⟨j.val - 1, by omega⟩ := h_ts_S_strict h_lt2
            exact h1
      · have h_i_gt_m : m.val < i.val := by omega
        by_cases h_i_eq : i.val = m.val + 1
        · rw [dif_neg h_i_le_m, dif_pos h_i_eq]
          by_cases h_j_eq : j.val = m.val + 1
          · omega
          · by_cases h_j_gt : j.val > m.val + 1
            · rw [dif_neg (by omega), dif_neg h_j_eq]
              have h1 : t < ts_S ⟨j.val - 1, by omega⟩ := by
                have h_j1_val_ge : m.val + 1 ≤ j.val - 1 := by omega
                have h_j1_ge : (Fin.succ m : Fin (n + 1)) ≤ ⟨j.val - 1, by omega⟩ := by
                  apply Fin.le_iff_val_le_val.mpr
                  simpa [Fin.succ] using h_j1_val_ge
                have h2 : ts_S (Fin.succ m) ≤ ts_S ⟨j.val - 1, by omega⟩ := h_ts_S_strict.monotone h_j1_ge
                exact lt_of_lt_of_le h_m_right h2
              exact h1
            · omega
        · rw [dif_neg h_i_le_m, dif_neg h_i_eq]
          rw [dif_neg (by omega), dif_neg (by omega)]
          have h_i_lt_j1 : i.val - 1 < j.val - 1 := by omega
          have h_lt2 : (⟨i.val - 1, by omega⟩ : Fin (n + 1)) < (⟨j.val - 1, by omega⟩ : Fin (n + 1)) := by
            apply Fin.lt_iff_val_lt_val.mpr
            exact h_i_lt_j1
          exact h_ts_S_strict h_lt2
    -- Prove ts' has image S ∪ {t}
    have h_ts'_image : Finset.image ts' Finset.univ = S ∪ {t} := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_singleton]
      constructor
      · rintro ⟨i, rfl⟩
        dsimp only [ts']
        by_cases h1 : i.val ≤ m.val
        · rw [dif_pos h1]
          left
          have h2 : ts_S ⟨i.val, by omega⟩ ∈ Finset.image ts_S Finset.univ := Finset.mem_image.mpr ⟨⟨i.val, by omega⟩, Finset.mem_univ _, rfl⟩
          rw [h_ts_S_image] at h2
          exact h2
        · by_cases h2 : i.val = m.val + 1
          · rw [dif_neg h1, dif_pos h2]
            right
            rfl
          · rw [dif_neg h1, dif_neg h2]
            left
            have h3 : ts_S ⟨i.val - 1, by omega⟩ ∈ Finset.image ts_S Finset.univ := Finset.mem_image.mpr ⟨⟨i.val - 1, by omega⟩, Finset.mem_univ _, rfl⟩
            rw [h_ts_S_image] at h3
            exact h3
      · rintro (h | h_eq)
        · -- x ∈ S
          have h_x_in : x ∈ Finset.image ts_S Finset.univ := by rw [h_ts_S_image] <;> exact h
          rcases Finset.mem_image.mp h_x_in with ⟨i, _, rfl⟩
          by_cases h_i_le_m : i.val ≤ m.val
          · let j : Fin (n + 2) := ⟨i.val, by omega⟩
            have h_ts'_j : ts' j = ts_S i := by
              dsimp only [ts', j]
              rw [dif_pos h_i_le_m] <;> rfl
            exact ⟨j, h_ts'_j⟩
          · have h_i_gt_m : i.val > m.val := by omega
            let j : Fin (n + 2) := ⟨i.val + 1, by omega⟩
            have h_ts'_j : ts' j = ts_S i := by
              dsimp only [ts', j]
              rw [dif_neg (by omega), dif_neg (by omega)] <;> congr <;> omega
            exact ⟨j, h_ts'_j⟩
        · -- x = t
          have h_x_eq_t : x = t := h_eq
          let j : Fin (n + 2) := ⟨m.val + 1, by omega⟩
          have h_ts'_j : ts' j = t := by
            dsimp only [ts', j]
            rw [dif_neg (by omega), dif_pos (by omega)] <;> rfl
          have h_ts'_j_x : ts' j = x := by
            rw [h_ts'_j, h_x_eq_t.symm]
          exact ⟨j, h_ts'_j_x⟩
    -- Prove covers' are in 𝒰
    have hcover_mem' : ∀ i : Fin (n + 1), covers' i ∈ 𝒰 := by
      intro i
      dsimp only [covers']
      by_cases h1 : i.val < m.val
      · rw [dif_pos h1]
        exact hcover_mem_S ⟨i.val, by omega⟩
      · by_cases h2 : i.val = m.val
        · rw [dif_neg h1, dif_pos h2]
          exact hcover_mem_S m
        · by_cases h3 : i.val = m.val + 1
          · rw [dif_neg h1, dif_neg h2, dif_pos h3]
            exact hcover_mem_S m
          · rw [dif_neg h1, dif_neg h2, dif_neg h3]
            exact hcover_mem_S ⟨i.val - 1, by omega⟩
    -- Prove range condition for covers'
    have h_range' : ∀ (i : Fin (n + 1)) (t_val : I),
        ts' (Fin.castSucc i) ≤ t_val → t_val ≤ ts' (Fin.succ i) → γ t_val ∈ (covers' i : Set X) := by
      intro i t_val h1 h2
      dsimp only [covers']
      by_cases h_i_lt_m : i.val < m.val
      · rw [dif_pos h_i_lt_m]
        have h_ts1 : ts' (Fin.castSucc i) = ts_S (Fin.castSucc ⟨i.val, by omega⟩) := by
          dsimp only [ts']
          have h : (Fin.castSucc i).val ≤ m.val := by simp [Fin.castSucc, h_i_lt_m] <;> omega
          rw [dif_pos h] <;> rfl
        have h_ts2 : ts' (Fin.succ i) = ts_S (Fin.succ ⟨i.val, by omega⟩) := by
          dsimp only [ts']
          have h : (Fin.succ i).val ≤ m.val := by simp [Fin.succ, h_i_lt_m] <;> omega
          rw [dif_pos h] <;> rfl
        rw [h_ts1] at h1
        rw [h_ts2] at h2
        exact h_range_S ⟨i.val, by omega⟩ t_val h1 h2
      · rw [dif_neg h_i_lt_m]
        by_cases h_i_eq_m : i.val = m.val
        · rw [dif_pos h_i_eq_m]
          have h_ts1 : ts' (Fin.castSucc i) = ts_S (Fin.castSucc m) := by
            dsimp only [ts']
            have h_cast_val : (Fin.castSucc i).val = i.val := by simp [Fin.castSucc]
            have h : (Fin.castSucc i).val ≤ m.val := by
              rw [h_cast_val, h_i_eq_m]
            have h_eq_val : (Fin.castSucc i).val = (Fin.castSucc m).val := by
              rw [h_cast_val, h_i_eq_m] <;> simp [Fin.castSucc]
            have h_fin_eq : (⟨(Fin.castSucc i).val, by omega⟩ : Fin (n + 1)) = Fin.castSucc m := by
              apply Fin.ext
              simpa [Fin.castSucc] using h_eq_val
            rw [dif_pos h]
            rw [h_fin_eq]
          have h_ts2 : ts' (Fin.succ i) = t := by
            dsimp only [ts']
            have h_succ_val : (Fin.succ i).val = i.val + 1 := by simp [Fin.succ]
            have h1 : ¬ (Fin.succ i).val ≤ m.val := by
              rw [h_succ_val, h_i_eq_m] <;> omega
            have h2 : (Fin.succ i).val = m.val + 1 := by
              rw [h_succ_val, h_i_eq_m]
            rw [dif_neg h1, dif_pos h2] <;> congr <;> simp [Fin.succ, h_i_eq_m]
          rw [h_ts1] at h1
          rw [h_ts2] at h2
          have h3 : t_val ≤ ts_S (Fin.succ m) := by
            have h4 : t_val < ts_S (Fin.succ m) := by
              exact lt_of_le_of_lt h2 h_m_right
            exact le_of_lt h4
          exact h_range_S m t_val h1 h3
        · rw [dif_neg h_i_eq_m]
          by_cases h_i_eq_m1 : i.val = m.val + 1
          · rw [dif_pos h_i_eq_m1]
            have h_ts1 : ts' (Fin.castSucc i) = t := by
              dsimp only [ts']
              have h1 : ¬ (Fin.castSucc i).val ≤ m.val := by
                simp [Fin.castSucc, h_i_eq_m1] <;> omega
              have h2 : (Fin.castSucc i).val = m.val + 1 := by
                simp [Fin.castSucc, h_i_eq_m1] <;> omega
              rw [dif_neg h1, dif_pos h2] <;> congr <;> omega
            have h_ts2 : ts' (Fin.succ i) = ts_S (Fin.succ m) := by
              dsimp only [ts']
              have h1 : ¬ (Fin.succ i).val ≤ m.val := by
                simp [Fin.succ, h_i_eq_m1] <;> omega
              have h2 : ¬ (Fin.succ i).val = m.val + 1 := by
                simp [Fin.succ, h_i_eq_m1] <;> omega
              rw [dif_neg h1, dif_neg h2] <;> congr <;> omega
            rw [h_ts1] at h1
            rw [h_ts2] at h2
            have h3 : ts_S (Fin.castSucc m) ≤ t_val := by
              have h4 : ts_S (Fin.castSucc m) < t_val := by
                exact lt_of_lt_of_le h_m_left h1
              exact le_of_lt h4
            exact h_range_S m t_val h3 h2
          · rw [dif_neg h_i_eq_m1]
            have h_i_gt : m.val + 1 < i.val := by omega
            let j : Fin n := ⟨i.val - 1, by omega⟩
            have h_ts1 : ts' (Fin.castSucc i) = ts_S (Fin.castSucc j) := by
              dsimp only [ts', j]
              have h1 : ¬ (Fin.castSucc i).val ≤ m.val := by
                simp [Fin.castSucc, j, h_i_gt] <;> omega
              have h2 : ¬ (Fin.castSucc i).val = m.val + 1 := by
                simp [Fin.castSucc, j, h_i_gt] <;> omega
              rw [dif_neg h1, dif_neg h2]
              apply congr_arg ts_S
              apply Fin.ext
              simp [Fin.castSucc, j] <;> omega
            have h_ts2 : ts' (Fin.succ i) = ts_S (Fin.succ j) := by
              dsimp only [ts', j]
              have h1 : ¬ (Fin.succ i).val ≤ m.val := by
                simp [Fin.succ, j, h_i_gt] <;> omega
              have h2 : ¬ (Fin.succ i).val = m.val + 1 := by
                simp [Fin.succ, j, h_i_gt] <;> omega
              rw [dif_neg h1, dif_neg h2]
              apply congr_arg ts_S
              apply Fin.ext
              simp [Fin.succ, j] <;> omega
            rw [h_ts1] at h1
            rw [h_ts2] at h2
            exact h_range_S j t_val h1 h2
    -- Apply universal property to both sides
    have h_eq_S : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS =
        my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS n ts_S h_ts_S_strict h_ts_S_image covers_S hcover_mem_S h_range_S :=
      my_map_from_adapted_subdivision_universal X 𝒰 hcover hfinite_intersections s hS ts_S h_ts_S_strict h_ts_S_image covers_S hcover_mem_S h_range_S
    have h_eq_S' : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS' =
        my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS' (n + 1) ts' h_ts'_strict h_ts'_image covers' hcover_mem' h_range' :=
      my_map_from_adapted_subdivision_universal X 𝒰 hcover hfinite_intersections s hS' ts' h_ts'_strict h_ts'_image covers' hcover_mem' h_range'
    -- Core equality step
    have h_core : my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS n ts_S h_ts_S_strict h_ts_S_image covers_S hcover_mem_S h_range_S =
        my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS' (n + 1) ts' h_ts'_strict h_ts'_image covers' hcover_mem' h_range' := by
      dsimp only [my_map_from_adapted_subdivision_with_covers]
      let pts_S (i : Fin (n + 1)) : X := γ (ts_S i)
      let objs_S : Fin (n + 1) → s.pt := fun i =>
        desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts_S i))
      let γs_S (i : Fin n) : Path (pts_S (Fin.castSucc i)) (pts_S (Fin.succ i)) :=
        γ.subpath (ts_S (Fin.castSucc i)) (ts_S (Fin.succ i))
      have h_ranges_S (i : Fin n) : Set.range (γs_S i) ⊆ (covers_S i : Set X) := by
        have h_lt : Fin.castSucc i < Fin.succ i := by exact?
        have h_ts_lt : ts_S (Fin.castSucc i) < ts_S (Fin.succ i) := h_ts_S_strict h_lt
        have h_range : ∀ (t_val : I), ts_S (Fin.castSucc i) ≤ t_val → t_val ≤ ts_S (Fin.succ i) → γ t_val ∈ (covers_S i : Set X) := h_range_S i
        have h_range_eq : Set.range (γs_S i) = γ '' Set.Icc (ts_S (Fin.castSucc i)) (ts_S (Fin.succ i)) := by
          rw [Path.range_subpath γ (ts_S (Fin.castSucc i)) (ts_S (Fin.succ i))]
          <;> rw [Set.uIcc_of_le (le_of_lt h_ts_lt)]
        rw [h_range_eq]
        intro z hz
        rcases hz with ⟨t, ht, rfl⟩
        exact h_range t ht.1 ht.2
      let homs_S (i : Fin n) : objs_S (Fin.castSucc i) ⟶ objs_S (Fin.succ i) :=
        single_covered_map X 𝒰 hcover hfinite_intersections s (γs_S i) (covers_S i) (hcover_mem_S i) (h_ranges_S i)
      let pts' (i : Fin (n + 2)) : X := γ (ts' i)
      let objs' : Fin (n + 2) → s.pt := fun i =>
        desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts' i))
      let γs' (i : Fin (n + 1)) : Path (pts' (Fin.castSucc i)) (pts' (Fin.succ i)) :=
        γ.subpath (ts' (Fin.castSucc i)) (ts' (Fin.succ i))
      have h_ranges' (i : Fin (n + 1)) : Set.range (γs' i) ⊆ (covers' i : Set X) := by
        have h_lt : Fin.castSucc i < Fin.succ i := by exact?
        have h_ts_lt : ts' (Fin.castSucc i) < ts' (Fin.succ i) := h_ts'_strict h_lt
        have h_range : ∀ (t_val : I), ts' (Fin.castSucc i) ≤ t_val → t_val ≤ ts' (Fin.succ i) → γ t_val ∈ (covers' i : Set X) := h_range' i
        have h_range_eq : Set.range (γs' i) = γ '' Set.Icc (ts' (Fin.castSucc i)) (ts' (Fin.succ i)) := by
          rw [Path.range_subpath γ (ts' (Fin.castSucc i)) (ts' (Fin.succ i))]
          <;> rw [Set.uIcc_of_le (le_of_lt h_ts_lt)]
        rw [h_range_eq]
        intro z hz
        rcases hz with ⟨t, ht, rfl⟩
        exact h_range t ht.1 ht.2
      let homs' (i : Fin (n + 1)) : objs' (Fin.castSucc i) ⟶ objs' (Fin.succ i) :=
        single_covered_map X 𝒰 hcover hfinite_intersections s (γs' i) (covers' i) (hcover_mem' i) (h_ranges' i)
      let mid : s.pt := desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (γ t))
      let γ1 : Path (pts_S (Fin.castSucc m)) (γ t) :=
        γ.subpath (ts_S (Fin.castSucc m)) t
      let γ2 : Path (γ t) (pts_S (Fin.succ m)) :=
        γ.subpath t (ts_S (Fin.succ m))
      have h_range1 : Set.range γ1 ⊆ (covers_S m : Set X) := by
        have h_range : ∀ (t_val : I), ts_S (Fin.castSucc m) ≤ t_val → t_val ≤ t → γ t_val ∈ (covers_S m : Set X) := by
          intro t_val h1 h2
          have h3 : t_val ≤ ts_S (Fin.succ m) := by
            have h4 : t_val < ts_S (Fin.succ m) := by
              exact lt_of_le_of_lt h2 h_m_right
            exact le_of_lt h4
          exact h_range_S m t_val h1 h3
        have h_range_eq : Set.range γ1 = γ '' Set.Icc (ts_S (Fin.castSucc m)) t := by
          rw [Path.range_subpath γ (ts_S (Fin.castSucc m)) t]
          <;> rw [Set.uIcc_of_le (le_of_lt h_m_left)]
        rw [h_range_eq]
        intro z hz
        rcases hz with ⟨t_val, ht, rfl⟩
        exact h_range t_val ht.1 ht.2
      have h_range2 : Set.range γ2 ⊆ (covers_S m : Set X) := by
        have h_range : ∀ (t_val : I), t ≤ t_val → t_val ≤ ts_S (Fin.succ m) → γ t_val ∈ (covers_S m : Set X) := by
          intro t_val h1 h2
          have h3 : ts_S (Fin.castSucc m) ≤ t_val := by
            have h4 : ts_S (Fin.castSucc m) < t_val := by
              exact lt_of_lt_of_le h_m_left h1
            exact le_of_lt h4
          exact h_range_S m t_val h3 h2
        have h_range_eq : Set.range γ2 = γ '' Set.Icc t (ts_S (Fin.succ m)) := by
          rw [Path.range_subpath γ t (ts_S (Fin.succ m))]
          <;> rw [Set.uIcc_of_le (le_of_lt h_m_right)]
        rw [h_range_eq]
        intro z hz
        rcases hz with ⟨t_val, ht, rfl⟩
        exact h_range t_val ht.1 ht.2
      let f : objs_S (Fin.castSucc m) ⟶ mid :=
        single_covered_map X 𝒰 hcover hfinite_intersections s γ1 (covers_S m) (hcover_mem_S m) h_range1
      let g : mid ⟶ objs_S (Fin.succ m) :=
        single_covered_map X 𝒰 hcover hfinite_intersections s γ2 (covers_S m) (hcover_mem_S m) h_range2
      have h_range_both : Set.range (γ1.trans γ2) ⊆ (covers_S m : Set X) :=
        range_trans_subset γ1 γ2 h_range1 h_range2
      have h_split : f ≫ g = single_covered_map X 𝒰 hcover hfinite_intersections s (γ1.trans γ2) (covers_S m) (hcover_mem_S m) h_range_both :=
        single_covered_split_eq X 𝒰 hcover hfinite_intersections s (covers_S m) (hcover_mem_S m) γ1 h_range1 γ2 h_range2
      let t₀ : I := ts_S (Fin.castSucc m)
      let t₁ : I := t
      let t₂ : I := ts_S (Fin.succ m)
      have h_t0_le_t1 : t₀ ≤ t₁ := le_of_lt h_m_left
      have h_t1_le_t2 : t₁ ≤ t₂ := le_of_lt h_m_right
      let H : Path.Homotopy (γ1.trans γ2) (γs_S m) :=
        Path.Homotopy.subpathTransSubpath γ t₀ t₁ t₂
      have hH : ∀ (p : I × I), H p ∈ (covers_S m : Set X) := by
        intro p
        have h_exists : ∃ (u : I), t₀ ≤ u ∧ u ≤ t₂ ∧ H p = γ u :=
          VanKampen.subpathTransSubpath_range γ h_t0_le_t1 h_t1_le_t2 p
        rcases h_exists with ⟨u, hu1, hu2, h_eq⟩
        rw [h_eq]
        exact h_range_S m u hu1 hu2
      have h_both_eq : single_covered_map X 𝒰 hcover hfinite_intersections s (γ1.trans γ2) (covers_S m) (hcover_mem_S m) h_range_both =
          single_covered_map X 𝒰 hcover hfinite_intersections s (γs_S m) (covers_S m) (hcover_mem_S m) (h_ranges_S m) :=
        single_covered_map_homotopic X 𝒰 hcover hfinite_intersections s (γ1.trans γ2) (γs_S m) (covers_S m) (hcover_mem_S m) h_range_both (h_ranges_S m) H hH
      have h_eq : homs_S m = f ≫ g := by
        dsimp only [homs_S]
        rw [←h_both_eq, ←h_split]
      have h0 : objs' 0 = objs_S 0 := by
        dsimp only [objs', objs_S, pts', pts_S]
        have h_ts0 : ts' 0 = ts_S 0 := by
          dsimp only [ts']
          have h : (0 : Fin (n + 2)).val ≤ m.val := by
            simp <;> omega
          rw [dif_pos h] <;> rfl
        rw [h_ts0] <;> rfl
      have h_last : objs' (Fin.last (n + 1)) = objs_S (Fin.last n) := by
        dsimp only [objs', objs_S, pts', pts_S]
        have h_ts_last : ts' (Fin.last (n + 1)) = ts_S (Fin.last n) := by
          dsimp only [ts']
          have h1 : ¬ (Fin.last (n + 1)).val ≤ m.val := by
            simp [Fin.last] <;> omega
          have h2 : ¬ (Fin.last (n + 1)).val = m.val + 1 := by
            simp [Fin.last] <;> omega
          rw [dif_neg h1, dif_neg h2] <;> simp [Fin.last] <;> omega
        rw [h_ts_last] <;> rfl
      have h_before : ∀ (i : Fin n), i.val < m.val →
          let j : Fin (n + 1) := Fin.castSucc i
          ∃ (h1 : objs' (Fin.castSucc j) = objs_S (Fin.castSucc i))
            (h2 : objs' (Fin.succ j) = objs_S (Fin.succ i)),
          eqToHom h1.symm ≫ homs' j ≫ eqToHom h2 = homs_S i := by
        intro i h_i_lt_m
        let j : Fin (n + 1) := Fin.castSucc i
        have h_j_lt_m : j.val < m.val := by
          dsimp only [j]
          simp [Fin.castSucc, h_i_lt_m] <;> omega
        have h_covers : covers' j = covers_S i := by
          dsimp only [covers', j]
          rw [dif_pos h_j_lt_m] <;> rfl
        have h_ts1 : ts' (Fin.castSucc j) = ts_S (Fin.castSucc i) := by
          dsimp only [ts']
          have h : (Fin.castSucc j).val ≤ m.val := by simp [Fin.castSucc, j, h_i_lt_m] <;> omega
          have h_eq_val : (Fin.castSucc j).val = (Fin.castSucc i).val := by
            simp [Fin.castSucc, j] <;> omega
          rw [dif_pos h]
          apply congr_arg
          apply Fin.ext
          exact h_eq_val
        have h_ts2 : ts' (Fin.succ j) = ts_S (Fin.succ i) := by
          dsimp only [ts']
          have h : (Fin.succ j).val ≤ m.val := by simp [Fin.succ, j, h_i_lt_m] <;> omega
          have h_eq_val : (Fin.succ j).val = (Fin.succ i).val := by
            simp [Fin.succ, j] <;> omega
          rw [dif_pos h]
          apply congr_arg
          apply Fin.ext
          exact h_eq_val
        have h_pts1 : pts' (Fin.castSucc j) = pts_S (Fin.castSucc i) := by
          dsimp only [pts', pts_S]
          rw [h_ts1] <;> rfl
        have h1 : objs' (Fin.castSucc j) = objs_S (Fin.castSucc i) := by
          dsimp only [objs', objs_S]
          rw [h_pts1] <;> rfl
        have h_pts2 : pts' (Fin.succ j) = pts_S (Fin.succ i) := by
          dsimp only [pts', pts_S]
          rw [h_ts2] <;> rfl
        have h2 : objs' (Fin.succ j) = objs_S (Fin.succ i) := by
          dsimp only [objs', objs_S]
          rw [h_pts2] <;> rfl
        refine' ⟨h1, h2, _⟩
        -- Paths are equal pointwise
        have hfun : ∀ t_val, γs' j t_val = γs_S i t_val := by
          intro t_val
          dsimp only [γs', γs_S]
          have h_eq1 : ts' (Fin.castSucc j) = ts_S (Fin.castSucc i) := h_ts1
          have h_eq2 : ts' (Fin.succ j) = ts_S (Fin.succ i) := h_ts2
          simp [Path.subpath, h_eq1, h_eq2]
          <;> rfl
        -- Get hcover_mem for the cover
        have hU : covers_S i ∈ 𝒰 := hcover_mem_S i
        -- We need h_ranges' j with the rewritten cover
        have h_range1 : Set.range (γs' j) ⊆ (covers_S i : Set X) := by
          rw [←h_covers]
          exact h_ranges' j
        -- Apply single_covered_map_congr
        have h_main : eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts1).symm ≫
            single_covered_map X 𝒰 hcover hfinite_intersections s (γs' j) (covers_S i) hU h_range1 ≫
            eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts2) =
            single_covered_map X 𝒰 hcover hfinite_intersections s (γs_S i) (covers_S i) hU (h_ranges_S i) := by
          exact single_covered_map_congr X 𝒰 hcover hfinite_intersections s
            (γs' j) (γs_S i) h_pts1 h_pts2 hfun (covers_S i) hU h_range1 (h_ranges_S i)
        -- The h1 and h2 are exactly the congr_arg equalities
        have h_eq1 : h1 = congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts1 := by
          apply Subsingleton.elim
        have h_eq2 : h2 = congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts2 := by
          apply Subsingleton.elim
        rw [h_eq1, h_eq2]
        -- Now we need to relate single_covered_map with covers' j vs covers_S i
        have h_covers_eq : covers' j = covers_S i := h_covers
        have hU' : covers' j ∈ 𝒰 := hcover_mem' j
        have h_eq_map : single_covered_map X 𝒰 hcover hfinite_intersections s (γs' j) (covers' j) hU' (h_ranges' j) =
                        single_covered_map X 𝒰 hcover hfinite_intersections s (γs' j) (covers_S i) hU h_range1 := by
          have h : ∀ (U V : Opens X) (hUV : U = V) (hU : U ∈ 𝒰) (hV : V ∈ 𝒰)
              (hR1 : Set.range (γs' j) ⊆ (U : Set X))
              (hR2 : Set.range (γs' j) ⊆ (V : Set X)),
              single_covered_map X 𝒰 hcover hfinite_intersections s (γs' j) U hU hR1 =
              single_covered_map X 𝒰 hcover hfinite_intersections s (γs' j) V hV hR2 := by
            intro U V hUV hU hV hR1 hR2
            cases hUV
            exact single_covered_map_indep_of_h_range X 𝒰 hcover hfinite_intersections s (γs' j) U hU hR1 hR2
          exact h (covers' j) (covers_S i) h_covers_eq hU' hU (h_ranges' j) h_range1
        -- Rewrite homs' j in the goal
        dsimp only [homs']
        rw [h_eq_map]
        exact h_main
      have h_split1 : objs' (Fin.castSucc (Fin.castSucc m)) = objs_S (Fin.castSucc m) := by
        dsimp only [objs', objs_S, pts', pts_S]
        have h1 : (Fin.castSucc (Fin.castSucc m)).val ≤ m.val := by simp [Fin.castSucc] <;> omega
        have h_ts : ts' (Fin.castSucc (Fin.castSucc m)) = ts_S (Fin.castSucc m) := by
          dsimp only [ts']
          rw [dif_pos h1] <;> rfl
        rw [h_ts] <;> rfl
      have h_split2 : objs' (Fin.succ (Fin.castSucc m)) = mid := by
        dsimp only [objs', mid, pts']
        have h1 : ¬ (Fin.succ (Fin.castSucc m)).val ≤ m.val := by simp [Fin.castSucc, Fin.succ] <;> omega
        have h2 : (Fin.succ (Fin.castSucc m)).val = m.val + 1 := by simp [Fin.castSucc, Fin.succ] <;> omega
        have h_ts : ts' (Fin.succ (Fin.castSucc m)) = t := by
          dsimp only [ts']
          rw [dif_neg h1, dif_pos h2] <;> rfl
        rw [h_ts] <;> rfl
      have h_split3 : homs' (Fin.castSucc m) = eqToHom h_split1 ≫ f ≫ eqToHom h_split2.symm := by
        dsimp only [homs', f]
        have h_covers : covers' (Fin.castSucc m) = covers_S m := by
          dsimp only [covers']
          have h1 : (Fin.castSucc m).val = m.val := by simp [Fin.castSucc] <;> omega
          rw [dif_neg (by simp [Fin.castSucc] <;> omega), dif_pos h1] <;> rfl
        have h_path1 : ts' (Fin.castSucc (Fin.castSucc m)) = ts_S (Fin.castSucc m) := by
          dsimp only [ts']
          have h1 : (Fin.castSucc (Fin.castSucc m)).val ≤ m.val := by simp [Fin.castSucc] <;> omega
          rw [dif_pos h1] <;> rfl
        have h_path2 : ts' (Fin.succ (Fin.castSucc m)) = t := by
          dsimp only [ts']
          have h1 : ¬ (Fin.succ (Fin.castSucc m)).val ≤ m.val := by simp [Fin.castSucc, Fin.succ] <;> omega
          have h2 : (Fin.succ (Fin.castSucc m)).val = m.val + 1 := by simp [Fin.castSucc, Fin.succ] <;> omega
          rw [dif_neg h1, dif_pos h2] <;> rfl
        -- Extract endpoint equalities
        have hx : pts' (Fin.castSucc (Fin.castSucc m)) = pts_S (Fin.castSucc m) := by
          dsimp only [pts', pts_S]
          rw [h_path1] <;> rfl
        have hy : pts' (Fin.succ (Fin.castSucc m)) = γ t := by
          dsimp only [pts']
          rw [h_path2] <;> rfl
        -- Paths are equal pointwise
        have hfun : ∀ t_val, γs' (Fin.castSucc m) t_val = γ1 t_val := by
          intro t_val
          dsimp only [γs', γ1]
          have h_eq1 : ts' (Fin.castSucc (Fin.castSucc m)) = ts_S (Fin.castSucc m) := h_path1
          have h_eq2 : ts' (Fin.succ (Fin.castSucc m)) = t := h_path2
          simp [Path.subpath, h_eq1, h_eq2]
          <;> rfl
        -- Get hcover_mem for the cover
        have hU : covers_S m ∈ 𝒰 := hcover_mem_S m
        -- We need h_ranges' (Fin.castSucc m) with the rewritten cover
        have h_range_prime : Set.range (γs' (Fin.castSucc m)) ⊆ (covers_S m : Set X) := by
          rw [←h_covers]
          exact h_ranges' (Fin.castSucc m)
        -- Apply single_covered_map_congr
        have h_main : eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hx).symm ≫
            single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.castSucc m)) (covers_S m) hU h_range_prime ≫
            eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hy) =
            single_covered_map X 𝒰 hcover hfinite_intersections s γ1 (covers_S m) hU h_range1 := by
          exact single_covered_map_congr X 𝒰 hcover hfinite_intersections s
            (γs' (Fin.castSucc m)) γ1 hx hy hfun (covers_S m) hU h_range_prime h_range1
        -- The h_split1 and h_split2 are exactly the congr_arg equalities
        have h_eq1 : h_split1 = congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hx := by
          apply Subsingleton.elim
        have h_eq2 : h_split2 = congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hy := by
          apply Subsingleton.elim
        rw [h_eq1, h_eq2]
        -- Now we need to relate single_covered_map with covers' (Fin.castSucc m) vs covers_S m
        have h_covers_eq : covers' (Fin.castSucc m) = covers_S m := h_covers
        have hU' : covers' (Fin.castSucc m) ∈ 𝒰 := hcover_mem' (Fin.castSucc m)
        have h_eq_map : single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.castSucc m)) (covers' (Fin.castSucc m)) hU' (h_ranges' (Fin.castSucc m)) =
                        single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.castSucc m)) (covers_S m) hU h_range_prime := by
          have h : ∀ (U V : Opens X) (hUV : U = V) (hU : U ∈ 𝒰) (hV : V ∈ 𝒰)
              (hR1 : Set.range (γs' (Fin.castSucc m)) ⊆ (U : Set X))
              (hR2 : Set.range (γs' (Fin.castSucc m)) ⊆ (V : Set X)),
              single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.castSucc m)) U hU hR1 =
              single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.castSucc m)) V hV hR2 := by
            intro U V hUV hU hV hR1 hR2
            cases hUV
            exact single_covered_map_indep_of_h_range X 𝒰 hcover hfinite_intersections s (γs' (Fin.castSucc m)) U hU hR1 hR2
          exact h (covers' (Fin.castSucc m)) (covers_S m) h_covers_eq hU' hU (h_ranges' (Fin.castSucc m)) h_range_prime
        rw [h_eq_map]
        -- Rearrange h_main: from eqToHom(hx').symm ≫ A ≫ eqToHom(hy') = B
        -- get A = eqToHom(hx') ≫ B ≫ eqToHom(hy').symm
        let hx' := congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hx
        let hy' := congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hy
        let A := single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.castSucc m)) (covers_S m) hU h_range_prime
        let B := single_covered_map X 𝒰 hcover hfinite_intersections s γ1 (covers_S m) hU h_range1
        have h_final : A = eqToHom hx' ≫ B ≫ eqToHom hy'.symm := by
          let e_x : _ ≅ _ := eqToIso hx'
          let e_y : _ ≅ _ := eqToIso hy'
          have h_main2' : e_x.inv ≫ A ≫ e_y.hom = B := h_main
          exact VanKampen.iso_sandwich_rewrite e_x e_y A B h_main2'
        exact h_final
      have h_split4 : objs' (Fin.castSucc (Fin.succ m)) = mid := by
        dsimp only [objs', mid, pts']
        have h1 : ¬ (Fin.castSucc (Fin.succ m)).val ≤ m.val := by simp [Fin.castSucc, Fin.succ] <;> omega
        have h2 : (Fin.castSucc (Fin.succ m)).val = m.val + 1 := by simp [Fin.castSucc, Fin.succ] <;> omega
        have h_ts : ts' (Fin.castSucc (Fin.succ m)) = t := by
          dsimp only [ts']
          rw [dif_neg h1, dif_pos h2] <;> rfl
        rw [h_ts] <;> rfl
      have h_split5 : objs' (Fin.succ (Fin.succ m)) = objs_S (Fin.succ m) := by
        dsimp only [objs', objs_S, pts', pts_S]
        have h1 : ¬ (Fin.succ (Fin.succ m)).val ≤ m.val := by simp [Fin.succ] <;> omega
        have h2 : ¬ (Fin.succ (Fin.succ m)).val = m.val + 1 := by simp [Fin.succ] <;> omega
        have h_ts : ts' (Fin.succ (Fin.succ m)) = ts_S (Fin.succ m) := by
          dsimp only [ts']
          rw [dif_neg h1, dif_neg h2] <;> simp [Fin.succ] <;> omega
        rw [h_ts] <;> rfl
      have h_split6 : homs' (Fin.succ m) = eqToHom h_split4 ≫ g ≫ eqToHom h_split5.symm := by
        dsimp only [homs', g]
        have h_covers : covers' (Fin.succ m) = covers_S m := by
          dsimp only [covers']
          have h1 : (Fin.succ m).val = m.val + 1 := by simp [Fin.succ] <;> omega
          rw [dif_neg (by simp [Fin.succ] <;> omega), dif_neg (by simp [Fin.succ] <;> omega), dif_pos h1] <;> rfl
        have h_path1 : ts' (Fin.castSucc (Fin.succ m)) = t := by
          dsimp only [ts']
          have h1 : ¬ (Fin.castSucc (Fin.succ m)).val ≤ m.val := by simp [Fin.castSucc, Fin.succ] <;> omega
          have h2 : (Fin.castSucc (Fin.succ m)).val = m.val + 1 := by simp [Fin.castSucc, Fin.succ] <;> omega
          rw [dif_neg h1, dif_pos h2] <;> rfl
        have h_path2 : ts' (Fin.succ (Fin.succ m)) = ts_S (Fin.succ m) := by
          dsimp only [ts']
          have h1 : ¬ (Fin.succ (Fin.succ m)).val ≤ m.val := by simp [Fin.succ] <;> omega
          have h2 : ¬ (Fin.succ (Fin.succ m)).val = m.val + 1 := by simp [Fin.succ] <;> omega
          rw [dif_neg h1, dif_neg h2] <;> simp [Fin.succ] <;> omega
        -- Extract endpoint equalities
        have hx : pts' (Fin.castSucc (Fin.succ m)) = γ t := by
          dsimp only [pts']
          rw [h_path1] <;> rfl
        have hy : pts' (Fin.succ (Fin.succ m)) = pts_S (Fin.succ m) := by
          dsimp only [pts', pts_S]
          rw [h_path2] <;> rfl
        -- Paths are equal pointwise
        have hfun : ∀ t_val, γs' (Fin.succ m) t_val = γ2 t_val := by
          intro t_val
          dsimp only [γs', γ2]
          have h_eq1 : ts' (Fin.castSucc (Fin.succ m)) = t := h_path1
          have h_eq2 : ts' (Fin.succ (Fin.succ m)) = ts_S (Fin.succ m) := h_path2
          have h_left : (γ.subpath (ts' (Fin.castSucc (Fin.succ m))) (ts' (Fin.succ (Fin.succ m)))) t_val =
              γ (Set.Icc.convexComb (ts' (Fin.castSucc (Fin.succ m))) (ts' (Fin.succ (Fin.succ m))) t_val) := by rfl
          have h_right : (γ.subpath t (ts_S (Fin.succ m))) t_val =
              γ (Set.Icc.convexComb t (ts_S (Fin.succ m)) t_val) := by rfl
          rw [h_left, h_right]
          rw [h_eq1, h_eq2]
        -- Get hcover_mem for the cover
        have hU : covers_S m ∈ 𝒰 := hcover_mem_S m
        -- We need h_ranges' (Fin.succ m) with the rewritten cover
        have h_range_prime : Set.range (γs' (Fin.succ m)) ⊆ (covers_S m : Set X) := by
          rw [←h_covers]
          exact h_ranges' (Fin.succ m)
        -- Apply single_covered_map_congr
        have h_main : eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hx).symm ≫
            single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.succ m)) (covers_S m) hU h_range_prime ≫
            eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hy) =
            single_covered_map X 𝒰 hcover hfinite_intersections s γ2 (covers_S m) hU h_range2 := by
          exact single_covered_map_congr X 𝒰 hcover hfinite_intersections s
            (γs' (Fin.succ m)) γ2 hx hy hfun (covers_S m) hU h_range_prime h_range2
        -- The h_split4 and h_split5 are exactly the congr_arg equalities
        have h_eq1 : h_split4 = congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hx := by
          apply Subsingleton.elim
        have h_eq2 : h_split5 = congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hy := by
          apply Subsingleton.elim
        rw [h_eq1, h_eq2]
        -- Now we need to relate single_covered_map with covers' (Fin.succ m) vs covers_S m
        have h_covers_eq : covers' (Fin.succ m) = covers_S m := h_covers
        have hU' : covers' (Fin.succ m) ∈ 𝒰 := hcover_mem' (Fin.succ m)
        have h_eq_map : single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.succ m)) (covers' (Fin.succ m)) hU' (h_ranges' (Fin.succ m)) =
                        single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.succ m)) (covers_S m) hU h_range_prime := by
          have h : ∀ (U V : Opens X) (hUV : U = V) (hU : U ∈ 𝒰) (hV : V ∈ 𝒰)
              (hR1 : Set.range (γs' (Fin.succ m)) ⊆ (U : Set X))
              (hR2 : Set.range (γs' (Fin.succ m)) ⊆ (V : Set X)),
              single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.succ m)) U hU hR1 =
              single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.succ m)) V hV hR2 := by
            intro U V hUV hU hV hR1 hR2
            cases hUV
            exact single_covered_map_indep_of_h_range X 𝒰 hcover hfinite_intersections s (γs' (Fin.succ m)) U hU hR1 hR2
          exact h (covers' (Fin.succ m)) (covers_S m) h_covers_eq hU' hU (h_ranges' (Fin.succ m)) h_range_prime
        rw [h_eq_map]
        let hx' := congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hx
        let hy' := congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) hy
        let e_x : _ ≅ _ := eqToIso hx'
        let e_y : _ ≅ _ := eqToIso hy'
        let A := single_covered_map X 𝒰 hcover hfinite_intersections s (γs' (Fin.succ m)) (covers_S m) hU h_range_prime
        let B := single_covered_map X 𝒰 hcover hfinite_intersections s γ2 (covers_S m) hU h_range2
        have h_main2' : e_x.inv ≫ A ≫ e_y.hom = B := h_main
        exact VanKampen.iso_sandwich_rewrite e_x e_y A B h_main2'
      have h_after : ∀ (j : Fin n), j.val > m.val →
          let i : Fin (n + 1) := Fin.succ j
          ∃ (h1 : objs' (Fin.castSucc i) = objs_S (Fin.castSucc j))
            (h2 : objs' (Fin.succ i) = objs_S (Fin.succ j)),
          eqToHom h1.symm ≫ homs' i ≫ eqToHom h2 = homs_S j := by
        intro j h_j_gt
        let i : Fin (n + 1) := Fin.succ j
        have h_i_gt : i.val > m.val + 1 := by
          dsimp only [i]
          simp [Fin.succ] <;> omega
        have h1 : ¬ (Fin.castSucc i).val ≤ m.val := by simp [Fin.castSucc] <;> omega
        have h2 : ¬ (Fin.castSucc i).val = m.val + 1 := by simp [Fin.castSucc] <;> omega
        have h_c1 : ¬ i.val < m.val := by simp [i, Fin.succ] <;> omega
        have h_c2 : ¬ i.val = m.val := by simp [i, Fin.succ] <;> omega
        have h_c3 : ¬ i.val = m.val + 1 := by simp [i, Fin.succ] <;> omega
        have h_covers : covers' i = covers_S j := by
          dsimp only [covers', i]
          rw [dif_neg h_c1, dif_neg h_c2, dif_neg h_c3]
          <;> apply congr_arg covers_S
          <;> apply Fin.ext
          <;> simp [Fin.succ] <;> omega
        have h_ts1 : ts' (Fin.castSucc i) = ts_S (Fin.castSucc j) := by
          dsimp only [ts']
          have h_eq_val : (Fin.castSucc i).val - 1 = (Fin.castSucc j).val := by
            simp [Fin.castSucc, Fin.succ, i] <;> omega
          rw [dif_neg h1, dif_neg h2]
          <;> apply congr_arg ts_S
          <;> apply Fin.ext
          <;> exact h_eq_val
        have h5 : ¬ (Fin.succ i).val ≤ m.val := by simp [Fin.succ, i] <;> omega
        have h6 : ¬ (Fin.succ i).val = m.val + 1 := by simp [Fin.succ, i] <;> omega
        have h_ts2 : ts' (Fin.succ i) = ts_S (Fin.succ j) := by
          dsimp only [ts']
          have h_eq_val2 : (Fin.succ i).val - 1 = (Fin.succ j).val := by
            simp [Fin.succ, i] <;> omega
          rw [dif_neg h5, dif_neg h6]
          <;> apply congr_arg ts_S
          <;> apply Fin.ext
          <;> exact h_eq_val2
        have h_pts1 : pts' (Fin.castSucc i) = pts_S (Fin.castSucc j) := by
          dsimp only [pts', pts_S]
          rw [h_ts1] <;> rfl
        have h1_obj : objs' (Fin.castSucc i) = objs_S (Fin.castSucc j) := by
          dsimp only [objs', objs_S]
          rw [h_pts1] <;> rfl
        have h_pts2 : pts' (Fin.succ i) = pts_S (Fin.succ j) := by
          dsimp only [pts', pts_S]
          rw [h_ts2] <;> rfl
        have h2_obj : objs' (Fin.succ i) = objs_S (Fin.succ j) := by
          dsimp only [objs', objs_S]
          rw [h_pts2] <;> rfl
        refine' ⟨h1_obj, h2_obj, _⟩
        -- Paths are equal pointwise
        have hfun : ∀ t_val, γs' i t_val = γs_S j t_val := by
          intro t_val
          dsimp only [γs', γs_S]
          have h_eq1 : ts' (Fin.castSucc i) = ts_S (Fin.castSucc j) := h_ts1
          have h_eq2 : ts' (Fin.succ i) = ts_S (Fin.succ j) := h_ts2
          simp [Path.subpath, h_eq1, h_eq2]
          <;> rfl
        -- Get hcover_mem for the cover
        have hU : covers_S j ∈ 𝒰 := hcover_mem_S j
        -- We need h_ranges' i with the rewritten cover
        have h_range1 : Set.range (γs' i) ⊆ (covers_S j : Set X) := by
          rw [←h_covers]
          exact h_ranges' i
        -- Apply single_covered_map_congr
        have h_main : eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts1).symm ≫
            single_covered_map X 𝒰 hcover hfinite_intersections s (γs' i) (covers_S j) hU h_range1 ≫
            eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts2) =
            single_covered_map X 𝒰 hcover hfinite_intersections s (γs_S j) (covers_S j) hU (h_ranges_S j) := by
          exact single_covered_map_congr X 𝒰 hcover hfinite_intersections s
            (γs' i) (γs_S j) h_pts1 h_pts2 hfun (covers_S j) hU h_range1 (h_ranges_S j)
        -- The h1_obj and h2_obj are exactly the congr_arg equalities
        have h_eq1 : h1_obj = congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts1 := by
          apply Subsingleton.elim
        have h_eq2 : h2_obj = congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts2 := by
          apply Subsingleton.elim
        rw [h_eq1, h_eq2]
        -- Now we need to relate single_covered_map with covers' i vs covers_S j
        have h_covers_eq : covers' i = covers_S j := h_covers
        have hU' : covers' i ∈ 𝒰 := hcover_mem' i
        have h_eq_map : single_covered_map X 𝒰 hcover hfinite_intersections s (γs' i) (covers' i) hU' (h_ranges' i) =
                        single_covered_map X 𝒰 hcover hfinite_intersections s (γs' i) (covers_S j) hU h_range1 := by
          have h : ∀ (U V : Opens X) (hUV : U = V) (hU : U ∈ 𝒰) (hV : V ∈ 𝒰)
              (hR1 : Set.range (γs' i) ⊆ (U : Set X))
              (hR2 : Set.range (γs' i) ⊆ (V : Set X)),
              single_covered_map X 𝒰 hcover hfinite_intersections s (γs' i) U hU hR1 =
              single_covered_map X 𝒰 hcover hfinite_intersections s (γs' i) V hV hR2 := by
            intro U V hUV hU hV hR1 hR2
            cases hUV
            exact single_covered_map_indep_of_h_range X 𝒰 hcover hfinite_intersections s (γs' i) U hU hR1 hR2
          exact h (covers' i) (covers_S j) h_covers_eq hU' hU (h_ranges' i) h_range1
        dsimp only [homs']
        rw [h_eq_map]
        exact h_main
      have h_main : eqToHom h0.symm ≫ comp_list (n + 1) objs' homs' ≫ eqToHom h_last =
          comp_list n objs_S homs_S :=
        comp_list_split_explicit_proof m objs_S homs_S f g h_eq objs' homs' h_before h_split1 h_split2 h_split3 h_split4 h_split5 h_split6 h_after h0 h_last
      let eq0_S : objs_S 0 = desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk x) := by
        dsimp only [objs_S, pts_S]
        have h_pts0 : (γ (ts_S 0)) = x := by
          rw [h_ts0_eq]
          exact γ.source
        rw [h_pts0] <;> rfl
      let eq_last_S : objs_S (Fin.last n) = desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk y) := by
        dsimp only [objs_S, pts_S]
        have h_pts_last : (γ (ts_S (Fin.last n))) = y := by
          rw [h_ts1_eq]
          exact γ.target
        rw [h_pts_last] <;> rfl
      let eq0_S' : objs' 0 = desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk x) := by
        dsimp only [objs', pts']
        have h_ts0 : ts' 0 = (0 : I) := by
          have h1 : ts' 0 = ts_S (0 : Fin (n + 1)) := by
            dsimp only [ts']
            have h : (0 : Fin (n + 2)).val ≤ m.val := by simp <;> omega
            rw [dif_pos h]
            <;> congr <;> apply Fin.ext <;> simp
          rw [h1]
          exact h_ts0_eq
        have h_pts0 : (γ (ts' 0)) = x := by
          rw [h_ts0]
          exact γ.source
        rw [h_pts0] <;> rfl
      let eq_last_S' : objs' (Fin.last (n + 1)) = desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk y) := by
        dsimp only [objs', pts']
        have h_ts1 : ts' (Fin.last (n + 1)) = (1 : I) := by
          dsimp only [ts']
          let i := Fin.last (n + 1)
          have h1 : ¬ i.val ≤ m.val := by
            simp [i, Fin.last] <;> omega
          have h2 : ¬ i.val = m.val + 1 := by
            simp [i, Fin.last] <;> omega
          have h_fin_eq : (⟨i.val - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := by
            apply Fin.ext
            simp [i, Fin.last]
            <;> omega
          rw [dif_neg h1, dif_neg h2]
          rw [h_fin_eq]
          exact h_ts1_eq
        have h_pts_last : (γ (ts' (Fin.last (n + 1)))) = y := by
          rw [h_ts1]
          exact γ.target
        rw [h_pts_last] <;> rfl
      have h_eq0 : eq0_S' = h0.trans eq0_S := by
        exact Subsingleton.elim eq0_S' (h0.trans eq0_S)
      have h_eq_last : eq_last_S' = h_last.trans eq_last_S := by
        exact Subsingleton.elim eq_last_S' (h_last.trans eq_last_S)
      have h_step1 : eqToHom eq0_S'.symm ≫ comp_list (n + 1) objs' homs' ≫ eqToHom eq_last_S' =
          eqToHom (h0.trans eq0_S).symm ≫ comp_list (n + 1) objs' homs' ≫ eqToHom (h_last.trans eq_last_S) := by
        rw [h_eq0, h_eq_last]
      have h_step2 : eqToHom (h0.trans eq0_S).symm ≫ comp_list (n + 1) objs' homs' ≫ eqToHom (h_last.trans eq_last_S) =
          eqToHom eq0_S.symm ≫ (eqToHom h0.symm ≫ comp_list (n + 1) objs' homs' ≫ eqToHom h_last) ≫ eqToHom eq_last_S := by
        simp [eqToHom_trans, Category.assoc] <;> rfl
      have h_step3 : eqToHom eq0_S.symm ≫ (eqToHom h0.symm ≫ comp_list (n + 1) objs' homs' ≫ eqToHom h_last) ≫ eqToHom eq_last_S =
          eqToHom eq0_S.symm ≫ comp_list n objs_S homs_S ≫ eqToHom eq_last_S := by
        have h_assoc : eqToHom eq0_S.symm ≫ (eqToHom h0.symm ≫ comp_list (n + 1) objs' homs' ≫ eqToHom h_last) ≫ eqToHom eq_last_S =
            (eqToHom eq0_S.symm ≫ (eqToHom h0.symm ≫ comp_list (n + 1) objs' homs' ≫ eqToHom h_last)) ≫ eqToHom eq_last_S := by
          simp [Category.assoc] <;> rfl
        rw [h_assoc]
        have h_rewrite : eqToHom eq0_S.symm ≫ (eqToHom h0.symm ≫ comp_list (n + 1) objs' homs' ≫ eqToHom h_last) =
            eqToHom eq0_S.symm ≫ comp_list n objs_S homs_S := by
          rw [h_main]
        rw [h_rewrite]
        <;> simp [Category.assoc] <;> rfl
      rw [h_step1, h_step2, h_step3]
    -- Combine everything
    rw [h_eq_S, h_eq_S']
    exact h_core

/-- Helper: adding any point to an adapted subdivision gives another adapted subdivision.
    This is just insert_is_adapted from CommonRefinement.lean. -/
lemma adapted_subdivision_add_point
    {x y : X} {γ : Path x y} {S : Finset I} {t : I}
    (hS : IsAdaptedSubdivision 𝒰 γ S) :
    IsAdaptedSubdivision 𝒰 γ (S ∪ {t}) :=
  insert_is_adapted (𝒰 := 𝒰) hS

/-- Refinement invariance: if S ⊆ S' are both adapted subdivisions,
    then they give the same morphism.

    Proof: by induction on |S' \ S|. Each step adds one point and uses refines_one. -/
theorem my_map_from_adapted_subdivision_refines_clean
    {x y : X} {γ : Path x y} {S S' : Finset I}
    (hS : IsAdaptedSubdivision 𝒰 γ S)
    (hS' : IsAdaptedSubdivision 𝒰 γ S')
    (h_sub : S ⊆ S') :
    my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS =
    my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS' := by
  classical
  -- We prove by induction on k = |S' \ S|
  have h_main : ∀ (k : ℕ), ∀ (S₁ S₂ : Finset I),
    S₁ ⊆ S₂ → S₂ ⊆ S' → (S₂ \ S₁).card = k →
    (hS₁ : IsAdaptedSubdivision 𝒰 γ S₁) →
    (hS₂ : IsAdaptedSubdivision 𝒰 γ S₂) →
    my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS₁ =
    my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS₂ := by
    intro k
    induction k with
    | zero =>
      intro S₁ S₂ h_sub1 h_sub2 h_card hS₁ hS₂
      -- Base case: (S₂ \ S₁).card = 0, so S₂ \ S₁ is empty, so S₂ ⊆ S₁
      have h_S2_sub_S1 : S₂ ⊆ S₁ := by
        simpa [Finset.card_eq_zero] using h_card
      have h_S2_eq_S1 : S₂ = S₁ := by
        apply Finset.Subset.antisymm h_S2_sub_S1 h_sub1
      subst h_S2_eq_S1
      <;> rfl
    | succ k ih =>
      intro S₁ S₂ h_sub1 h_sub2 h_card hS₁ hS₂
      -- Inductive step: (S₂ \ S₁).card = k + 1
      have h_nonempty : (S₂ \ S₁).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h
        rw [h] at h_card
        simp at h_card <;> omega
      let t : I := Classical.choose h_nonempty
      have ht_in_diff : t ∈ S₂ \ S₁ := Classical.choose_spec h_nonempty
      have ht_in_S2 : t ∈ S₂ := Finset.mem_sdiff.mp ht_in_diff |>.1
      have ht_notin_S1 : t ∉ S₁ := Finset.mem_sdiff.mp ht_in_diff |>.2
      let S_mid := S₁ ∪ {t}
      have h_sub_S1_Smid : S₁ ⊆ S_mid := by simp [S_mid]
      have h_sub_Smid_S2 : S_mid ⊆ S₂ := by
        intro x hx
        simp only [S_mid, Finset.mem_union, Finset.mem_singleton] at hx
        rcases hx with (hx | rfl)
        · exact h_sub1 hx
        · exact ht_in_S2
      have hS_mid : IsAdaptedSubdivision 𝒰 γ S_mid :=
        adapted_subdivision_add_point X 𝒰 hcover hfinite_intersections s hS₁
      -- By refines_one, map(S₁) = map(S_mid)
      have h_step1 : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS₁ =
          my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS_mid :=
        my_map_from_adapted_subdivision_refines_one_clean X 𝒰 hcover hfinite_intersections s hS₁ hS_mid
      -- Now (S₂ \ S_mid).card = k
      have h_card2 : (S₂ \ S_mid).card = k := by
        have h1 : S₂ \ S₁ = (S₂ \ S_mid) ∪ (S_mid \ S₁) := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_union]
          constructor
          · -- Forward direction
            rintro ⟨h_in_S2, h_notin_S1⟩
            by_cases h_in_Smid : x ∈ S_mid
            · -- x ∈ S_mid
              exact Or.inr ⟨h_in_Smid, h_notin_S1⟩
            · -- x ∉ S_mid
              exact Or.inl ⟨h_in_S2, h_in_Smid⟩
          · -- Backward direction
            rintro (⟨h_in_S2, h_notin_Smid⟩ | ⟨h_in_Smid, h_notin_S1⟩)
            · -- Case 1: x ∈ S₂ \ S_mid
              have h_notin_S1 : x ∉ S₁ := by
                intro h
                exact h_notin_Smid (h_sub_S1_Smid h)
              exact ⟨h_in_S2, h_notin_S1⟩
            · -- Case 2: x ∈ S_mid \ S₁
              have h_in_S2 : x ∈ S₂ := h_sub_Smid_S2 h_in_Smid
              exact ⟨h_in_S2, h_notin_S1⟩
        rw [h1] at h_card
        have h_disj : Disjoint (S₂ \ S_mid) (S_mid \ S₁) := by
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          have h_notin : x ∉ S_mid := Finset.mem_sdiff.mp hx1 |>.2
          have h_in : x ∈ S_mid := Finset.mem_sdiff.mp hx2 |>.1
          exact h_notin h_in
        have h_card1 : (S_mid \ S₁).card = 1 := by
          simp [S_mid, ht_notin_S1] <;> omega
        rw [Finset.card_union_of_disjoint h_disj] at h_card
        rw [h_card1] at h_card
        <;> omega
      -- By induction hypothesis, map(S_mid) = map(S₂)
      have h_step2 : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS_mid =
          my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS₂ := by
        exact ih S_mid S₂ h_sub_Smid_S2 h_sub2 h_card2 hS_mid hS₂
      rw [h_step1, h_step2]
  have h_card_eq : (S' \ S).card = (S' \ S).card := rfl
  exact h_main (S' \ S).card S S' h_sub (by rfl) h_card_eq hS hS'

/-- Helper: the union of two adapted subdivisions is also an adapted subdivision.
    This is just union_is_adapted from CommonRefinement.lean. -/
lemma adapted_subdivision_union
    {x y : X} {γ : Path x y} {S S' : Finset I}
    (hS : IsAdaptedSubdivision 𝒰 γ S)
    (hS' : IsAdaptedSubdivision 𝒰 γ S') :
    IsAdaptedSubdivision 𝒰 γ (S ∪ S') :=
  union_is_adapted hfinite_intersections hS hS'

/-- Independence of choice of adapted subdivision.
    This is the key lemma: any two adapted subdivisions give the same morphism.

    Proof: take their union S ∪ S', which is also an adapted subdivision.
    Then both S and S' refine S ∪ S', so by refines both equal the map for S ∪ S'.
    Hence they are equal to each other. -/
theorem my_map_from_adapted_subdivision_independent_clean
    {x y : X} {γ : Path x y} {S S' : Finset I}
    (hS : IsAdaptedSubdivision 𝒰 γ S)
    (hS' : IsAdaptedSubdivision 𝒰 γ S') :
    my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS =
    my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS' := by
  classical
  let S_union := S ∪ S'
  have hS_union : IsAdaptedSubdivision 𝒰 γ S_union :=
    adapted_subdivision_union X 𝒰 hcover hfinite_intersections s hS hS'
  have h1 : S ⊆ S_union := by simp [S_union]
  have h2 : S' ⊆ S_union := by simp [S_union]
  have h_eq1 : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS =
      my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS_union :=
    my_map_from_adapted_subdivision_refines_clean X 𝒰 hcover hfinite_intersections s hS hS_union h1
  have h_eq2 : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS' =
      my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS_union :=
    my_map_from_adapted_subdivision_refines_clean X 𝒰 hcover hfinite_intersections s hS' hS_union h2
  rw [h_eq1, h_eq2]

end

end
