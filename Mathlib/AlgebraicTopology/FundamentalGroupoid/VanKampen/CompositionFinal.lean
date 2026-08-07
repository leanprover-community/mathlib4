module

public import Mathlib
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.CanonicalCocone
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.UniversalProperty
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.CleanMapFromAdapted
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.ComposeMorphisms

@[expose] public section

open TopologicalSpace CategoryTheory Limits

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

include hcover hfinite_intersections

/-- Scale a point in I to the first half [0, 1/2] -/
def scale_first_half (t : I) : I :=
  ⟨(t : ℝ) / 2, by
    have h₁ : 0 ≤ (t : ℝ) / 2 := by linarith [t.prop.1]
    have h₂ : (t : ℝ) / 2 ≤ 1 := by linarith [t.prop.2]
    exact ⟨h₁, h₂⟩⟩

/-- Scale a point in I to the second half [1/2, 1] -/
def scale_second_half (t : I) : I :=
  ⟨1 / 2 + (t : ℝ) / 2, by
    have h₁ : 0 ≤ 1 / 2 + (t : ℝ) / 2 := by linarith [t.prop.1]
    have h₂ : 1 / 2 + (t : ℝ) / 2 ≤ 1 := by linarith [t.prop.2]
    exact ⟨h₁, h₂⟩⟩

/-- Helper: Strict monotonicity of scaling functions -/
lemma scale_first_half_strict : StrictMono (scale_first_half : I → I) := by
  intro a b h
  have h' : (a : ℝ) < (b : ℝ) := by exact_mod_cast h
  have h'' : ((a : ℝ) / 2) < ((b : ℝ) / 2) := by linarith
  exact_mod_cast h''

lemma scale_second_half_strict : StrictMono (scale_second_half : I → I) := by
  intro a b h
  have h' : (a : ℝ) < (b : ℝ) := by exact_mod_cast h
  have h'' : (1 / 2 + (a : ℝ) / 2) < (1 / 2 + (b : ℝ) / 2) := by linarith
  exact_mod_cast h''

lemma scale_first_half_le_half (t : I) : (scale_first_half t : ℝ) ≤ 1 / 2 := by
  simp [scale_first_half] <;> linarith [t.prop.2]

lemma scale_second_half_ge_half (t : I) : (scale_second_half t : ℝ) ≥ 1 / 2 := by
  simp [scale_second_half] <;> linarith [t.prop.1]

/-- Given an adapted subdivision, extract canonical decomposition -/
lemma exists_canonical_decomposition' {x y : X} {γ : Path x y} {S : Finset I}
    (hS : IsAdaptedSubdivision 𝒰 γ S) :
    ∃ (n : ℕ) (ts : Fin (n + 1) → I) (h_ts_strict : StrictMono ts)
      (h_ts_image : Finset.image ts Finset.univ = S)
      (covers : Fin n → Opens X) (hcover_mem : ∀ i, covers i ∈ 𝒰)
      (h_range : ∀ i, ∀ (t : I), ts (Fin.castSucc i) ≤ t → t ≤ ts (Fin.succ i) → γ t ∈ (covers i : Set X)),
      my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS =
      my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS n ts h_ts_strict h_ts_image covers hcover_mem h_range := by
  classical
  have h0_in : (0 : I) ∈ S := hS.1
  have h1_in : (1 : I) ∈ S := hS.2.1
  have hS_nonempty : S.Nonempty := ⟨0, h0_in⟩
  let k : ℕ := S.card
  have hk_pos : 0 < k := Finset.card_pos.mpr hS_nonempty
  let e : Fin k ↪o I := S.orderEmbOfFin rfl
  have h_e_mem : ∀ (i : Fin k), e i ∈ S := Finset.orderEmbOfFin_mem S rfl
  have h_e_strict_mono : StrictMono e := OrderEmbedding.strictMono e
  have h_image : Finset.image e Finset.univ = S := Finset.image_orderEmbOfFin_univ S rfl
  let n : ℕ := k - 1
  have hk_eq : k = n + 1 := by omega
  let ts (i : Fin (n + 1)) : I := e ⟨i.val, by rw [hk_eq] <;> exact i.is_lt⟩
  have h_ts_strict : StrictMono ts := by
    intro i j h
    exact h_e_strict_mono (by simpa [ts] using h)
  have h_ts_image : Finset.image ts Finset.univ = S := by
    have h1 : Finset.image ts Finset.univ = Finset.image e Finset.univ := by
      ext x
      simp only [ts, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨⟨i.val, by rw [hk_eq] <;> exact i.is_lt⟩, rfl⟩
      · rintro ⟨j, rfl⟩
        have h_j_lt : j.val < n + 1 := by rw [←hk_eq]; exact j.is_lt
        let i : Fin (n + 1) := ⟨j.val, h_j_lt⟩
        exact ⟨i, by simp [i] <;> rfl⟩
    rw [h1, h_image]
  let choose_data (i : Fin n) :
    ∃ (U : Opens X), U ∈ 𝒰 ∧ ∀ (t : I), ts (Fin.castSucc i) ≤ t → t ≤ ts (Fin.succ i) → γ t ∈ (U : Set X) := by
    let s₁ := ts (Fin.castSucc i)
    let s₂ := ts (Fin.succ i)
    have h_s1_in : s₁ ∈ S := h_e_mem _
    have h_s2_in : s₂ ∈ S := h_e_mem _
    have h_lt : s₁ < s₂ := h_e_strict_mono (by simp [Fin.castSucc, Fin.succ] <;> omega)
    have h_no_between : ∀ (t : I), t ∈ S → s₁ < t → t < s₂ → False := by
      intro t ht h1 h2
      have h_exists : ∃ (j : Fin k), e j = t := by
        have h : t ∈ Finset.image e Finset.univ := by rw [h_image] <;> exact ht
        rcases Finset.mem_image.mp h with ⟨j, _, rfl⟩
        exact ⟨j, rfl⟩
      rcases h_exists with ⟨j, hj⟩
      have h_j_gt : (Fin.castSucc i).val < j.val := by
        have h4 : ts (Fin.castSucc i) < e j := by rw [hj] <;> exact h1
        have h5 : e ⟨(Fin.castSucc i).val, by rw [hk_eq] <;> exact (Fin.castSucc i).is_lt⟩ = ts (Fin.castSucc i) := by rfl
        rw [←h5] at h4
        exact h_e_strict_mono.lt_iff_lt.mp h4
      have h_j_lt : j.val < (Fin.succ i).val := by
        have h4 : e j < ts (Fin.succ i) := by rw [hj] <;> exact h2
        have h5 : e ⟨(Fin.succ i).val, by rw [hk_eq] <;> exact (Fin.succ i).is_lt⟩ = ts (Fin.succ i) := by rfl
        rw [←h5] at h4
        exact h_e_strict_mono.lt_iff_lt.mp h4
      simp [Fin.castSucc, Fin.succ] at h_j_gt h_j_lt <;> omega
    exact hS.2.2 s₁ s₂ h_s1_in h_s2_in h_lt h_no_between
  choose U hU using choose_data
  let covers (i : Fin n) : Opens X := U i
  let hcover_mem (i : Fin n) : covers i ∈ 𝒰 := (hU i).1
  let h_range (i : Fin n) : ∀ (t : I), ts (Fin.castSucc i) ≤ t → t ≤ ts (Fin.succ i) → γ t ∈ (covers i : Set X) := (hU i).2
  have h_eq : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS =
      my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS n ts h_ts_strict h_ts_image covers hcover_mem h_range :=
    my_map_from_adapted_subdivision_universal X 𝒰 hcover hfinite_intersections s hS ts h_ts_strict h_ts_image covers hcover_mem h_range
  exact ⟨n, ts, h_ts_strict, h_ts_image, covers, hcover_mem, h_range, h_eq⟩

/-- Main composition lemma -/
theorem my_map_from_adapted_subdivision_comp_cauchy {x y z : X}
    (γ₁ : Path x y) (γ₂ : Path y z)
    {S₁ : Finset I} (hS₁ : IsAdaptedSubdivision 𝒰 γ₁ S₁)
    {S₂ : Finset I} (hS₂ : IsAdaptedSubdivision 𝒰 γ₂ S₂) :
    ∃ (S : Finset I) (hS : IsAdaptedSubdivision 𝒰 (γ₁.trans γ₂) S),
      my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS =
      my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS₁ ≫
      my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS₂ := by
  classical
  -- Step 1: Get canonical decompositions
  rcases exists_canonical_decomposition' X 𝒰 hcover hfinite_intersections s hS₁ with
    ⟨n₁, ts₁, h_ts₁_strict, h_ts₁_image, covers₁, hcover₁_mem, h_range₁, h_eq₁⟩
  rcases exists_canonical_decomposition' X 𝒰 hcover hfinite_intersections s hS₂ with
    ⟨n₂, ts₂, h_ts₂_strict, h_ts₂_image, covers₂, hcover₂_mem, h_range₂, h_eq₂⟩

  let n := n₁ + n₂

  -- Step 2: Helper facts about endpoints
  have h_ts1_last : ts₁ (Fin.last n₁) = (1 : I) := by
    have h1_in : (1 : I) ∈ S₁ := hS₁.2.1
    have h1_in_image : (1 : I) ∈ Finset.image ts₁ Finset.univ := by rw [h_ts₁_image] <;> exact h1_in
    let i : Fin (n₁ + 1) := Classical.choose (Finset.mem_image.mp h1_in_image)
    let hi : ts₁ i = (1 : I) := (Classical.choose_spec (Finset.mem_image.mp h1_in_image)).2
    have h_i_eq_last : i = Fin.last n₁ := by
      apply Fin.eq_last_of_not_lt
      intro h
      have h_tsk_lt_ts1 : ts₁ i < ts₁ (Fin.last n₁) := h_ts₁_strict h
      rw [hi] at h_tsk_lt_ts1
      have h' : (1 : ℝ) < (ts₁ (Fin.last n₁) : ℝ) := by exact_mod_cast h_tsk_lt_ts1
      have h'' : (ts₁ (Fin.last n₁) : ℝ) ≤ 1 := (ts₁ (Fin.last n₁)).prop.2
      linarith
    rw [h_i_eq_last] at hi
    exact hi
  have h_ts2_zero : ts₂ 0 = (0 : I) := by
    have h0_in : (0 : I) ∈ S₂ := hS₂.1
    have h0_in_image : (0 : I) ∈ Finset.image ts₂ Finset.univ := by rw [h_ts₂_image] <;> exact h0_in
    let i : Fin (n₂ + 1) := Classical.choose (Finset.mem_image.mp h0_in_image)
    let hi : ts₂ i = (0 : I) := (Classical.choose_spec (Finset.mem_image.mp h0_in_image)).2
    have h_i_eq_0 : i = 0 := by
      by_contra h
      have h_i_pos : 0 < i := Fin.pos_iff_ne_zero.mpr h
      have h_ts0_lt_tsi : ts₂ 0 < ts₂ i := h_ts₂_strict h_i_pos
      rw [hi] at h_ts0_lt_tsi
      have h_nonneg : (0 : ℝ) ≤ (ts₂ 0 : ℝ) := (ts₂ 0).prop.1
      have h_cont : (ts₂ 0 : ℝ) < (0 : ℝ) := by exact_mod_cast h_ts0_lt_tsi
      linarith
    rw [h_i_eq_0] at hi
    exact hi
  have h_ts1_zero : ts₁ 0 = (0 : I) := by
    have h0_in : (0 : I) ∈ S₁ := hS₁.1
    have h0_in_image : (0 : I) ∈ Finset.image ts₁ Finset.univ := by rw [h_ts₁_image] <;> exact h0_in
    let i : Fin (n₁ + 1) := Classical.choose (Finset.mem_image.mp h0_in_image)
    let hi : ts₁ i = (0 : I) := (Classical.choose_spec (Finset.mem_image.mp h0_in_image)).2
    have h_i_eq_0 : i = 0 := by
      by_contra h
      have h_i_pos : 0 < i := Fin.pos_iff_ne_zero.mpr h
      have h_ts0_lt_tsi : ts₁ 0 < ts₁ i := h_ts₁_strict h_i_pos
      rw [hi] at h_ts0_lt_tsi
      have h_nonneg : (0 : ℝ) ≤ (ts₁ 0 : ℝ) := (ts₁ 0).prop.1
      have h_cont : (ts₁ 0 : ℝ) < (0 : ℝ) := by exact_mod_cast h_ts0_lt_tsi
      linarith
    rw [h_i_eq_0] at hi
    exact hi
  have h_ts2_last : ts₂ (Fin.last n₂) = (1 : I) := by
    have h1_in : (1 : I) ∈ S₂ := hS₂.2.1
    have h1_in_image : (1 : I) ∈ Finset.image ts₂ Finset.univ := by rw [h_ts₂_image] <;> exact h1_in
    let i : Fin (n₂ + 1) := Classical.choose (Finset.mem_image.mp h1_in_image)
    let hi : ts₂ i = (1 : I) := (Classical.choose_spec (Finset.mem_image.mp h1_in_image)).2
    have h_i_eq_last : i = Fin.last n₂ := by
      apply Fin.eq_last_of_not_lt
      intro h
      have h_tsk_lt_ts1 : ts₂ i < ts₂ (Fin.last n₂) := h_ts₂_strict h
      rw [hi] at h_tsk_lt_ts1
      have h' : (1 : ℝ) < (ts₂ (Fin.last n₂) : ℝ) := by exact_mod_cast h_tsk_lt_ts1
      have h'' : (ts₂ (Fin.last n₂) : ℝ) ≤ 1 := (ts₂ (Fin.last n₂)).prop.2
      linarith
    rw [h_i_eq_last] at hi
    exact hi

  -- Step 3: Define concatenated subdivision
  let ts_concat (i : Fin (n + 1)) : I :=
    if h : i.val ≤ n₁ then
      scale_first_half (ts₁ ⟨i.val, by omega⟩)
    else
      scale_second_half (ts₂ ⟨i.val - n₁, by omega⟩)
  let covers_concat (i : Fin n) : Opens X :=
    if h : i.val < n₁ then
      covers₁ ⟨i.val, by omega⟩
    else
      covers₂ ⟨i.val - n₁, by omega⟩

  -- All remaining subproofs are left as future work - this is the skeleton
  have h_ts_concat_strict : StrictMono ts_concat := by
    intro i j h
    have h_val : i.val < j.val := h
    by_cases h_i : i.val ≤ n₁
    · -- i ≤ n₁
      by_cases h_j : j.val ≤ n₁
      · -- both ≤ n₁
        let i' : Fin (n₁ + 1) := ⟨i.val, by omega⟩
        let j' : Fin (n₁ + 1) := ⟨j.val, by omega⟩
        have h_ij' : i' < j' := by exact_mod_cast h_val
        have h_ts_lt : ts₁ i' < ts₁ j' := h_ts₁_strict h_ij'
        have h_ts_lt_val : (ts₁ i' : ℝ) < (ts₁ j' : ℝ) := by exact_mod_cast h_ts_lt
        have h1 : ts_concat i = scale_first_half (ts₁ i') := by
          simp only [ts_concat, h_i] <;> rfl
        have h2 : ts_concat j = scale_first_half (ts₁ j') := by
          simp only [ts_concat, h_j] <;> rfl
        rw [h1, h2]
        apply Subtype.mk_lt_mk.mpr
        <;> linarith
      · -- i ≤ n₁, j > n₁
        have h_j_gt_n1 : ¬ j.val ≤ n₁ := by omega
        have h_j_minus_n1_pos : 0 < j.val - n₁ := by omega
        let k : Fin (n₂ + 1) := ⟨j.val - n₁, by omega⟩
        have h_k_pos : 0 < k := by
          simp [k, Fin.pos_iff_ne_zero] <;> omega
        have h_lt0 : ts₂ 0 < ts₂ k := h_ts₂_strict h_k_pos
        have h0_val : (ts₂ 0 : ℝ) = 0 := by
          have h_eq : ts₂ 0 = (0 : I) := h_ts2_zero
          rw [h_eq]
          <;> simp
        have h_k_val_pos : (0 : ℝ) < (ts₂ k : ℝ) := by
          have h : (ts₂ 0 : ℝ) < (ts₂ k : ℝ) := by exact_mod_cast h_lt0
          rw [h0_val] at h
          exact h
        let tsi : I := ts_concat i
        let tsj : I := ts_concat j
        have h_tsi_eq : tsi = scale_first_half (ts₁ ⟨i.val, by omega⟩) := by
          simp only [ts_concat, h_i, tsi] <;> rfl
        have h_tsj_eq : tsj = scale_second_half (ts₂ k) := by
          simp only [ts_concat, h_j_gt_n1, tsj] <;> rfl
        have h1_val : (tsi : ℝ) ≤ 1 / 2 := by
          rw [h_tsi_eq]
          have h4 : ((scale_first_half (ts₁ ⟨i.val, by omega⟩) : I) : ℝ) = (ts₁ ⟨i.val, by omega⟩ : ℝ) / 2 := by
            simp [scale_first_half] <;> rfl
          rw [h4]
          have h5 : (ts₁ ⟨i.val, by omega⟩ : ℝ) ≤ 1 := (ts₁ ⟨i.val, by omega⟩).prop.2
          linarith
        have h2_val : (1 / 2 : ℝ) < (tsj : ℝ) := by
          rw [h_tsj_eq]
          have h3 : ((scale_second_half (ts₂ k) : I) : ℝ) = 1 / 2 + (ts₂ k : ℝ) / 2 := by
            simp [scale_second_half] <;> rfl
          rw [h3]
          linarith [h_k_val_pos]
        have h_goal_val : (tsi : ℝ) < (tsj : ℝ) := by linarith
        exact Subtype.mk_lt_mk.mpr h_goal_val
    · -- i > n₁, so j > n₁ too
      have h_i' : ¬i.val ≤ n₁ := by tauto
      have h_j' : ¬j.val ≤ n₁ := by omega
      let i' : Fin (n₂ + 1) := ⟨i.val - n₁, by omega⟩
      let j' : Fin (n₂ + 1) := ⟨j.val - n₁, by omega⟩
      have h_ij' : i' < j' := by exact_mod_cast (show i.val - n₁ < j.val - n₁ by omega)
      have h_ts_lt : ts₂ i' < ts₂ j' := h_ts₂_strict h_ij'
      have h_ts_lt_val : (ts₂ i' : ℝ) < (ts₂ j' : ℝ) := by exact_mod_cast h_ts_lt
      have h1 : ts_concat i = scale_second_half (ts₂ i') := by
        simp only [ts_concat, h_i'] <;> rfl
      have h2 : ts_concat j = scale_second_half (ts₂ j') := by
        simp only [ts_concat, h_j'] <;> rfl
      rw [h1, h2]
      apply Subtype.mk_lt_mk.mpr
      <;> linarith
  have hcover_concat_mem : ∀ i : Fin n, covers_concat i ∈ 𝒰 := by
    intro i
    dsimp only [covers_concat]
    by_cases h : i.val < n₁
    · rw [dif_pos h]
      exact hcover₁_mem ⟨i.val, by omega⟩
    · rw [dif_neg h]
      exact hcover₂_mem ⟨i.val - n₁, by omega⟩
  have h_range_concat : ∀ (i : Fin n), ∀ (t : I),
      ts_concat (Fin.castSucc i) ≤ t → t ≤ ts_concat (Fin.succ i) → (γ₁.trans γ₂) t ∈ (covers_concat i : Set X) := by
    intro i t h1 h2
    by_cases h : i.val < n₁
    · -- Case 1: i.val < n₁, use first path
      let i' : Fin n₁ := ⟨i.val, h⟩
      have h_cover : covers_concat i = covers₁ i' := by
        dsimp only [covers_concat]
        rw [dif_pos h] <;> rfl
      have h_cast_lt : (Fin.castSucc i).val < n₁ := by
        simpa [Fin.castSucc] using h
      have h_succ_le : (Fin.succ i).val ≤ n₁ := by
        simp [Fin.succ] <;> omega
      have h_ts1 : ts_concat (Fin.castSucc i) = scale_first_half (ts₁ (Fin.castSucc i')) := by
        dsimp only [ts_concat]
        have h_le : (Fin.castSucc i).val ≤ n₁ := by linarith
        rw [dif_pos h_le] <;> rfl
      have h_ts2 : ts_concat (Fin.succ i) = scale_first_half (ts₁ (Fin.succ i')) := by
        dsimp only [ts_concat]
        rw [dif_pos h_succ_le] <;> rfl
      have h_ts2_val_le_half : (ts_concat (Fin.succ i) : ℝ) ≤ 1 / 2 := by
        rw [h_ts2]
        simp [scale_first_half] <;> have h' := (ts₁ (Fin.succ i')).prop.2 <;> linarith
      have h_t_le_half : (t : ℝ) ≤ 1 / 2 := by
        have h' : (t : ℝ) ≤ (ts_concat (Fin.succ i) : ℝ) := by exact_mod_cast h2
        exact le_trans h' h_ts2_val_le_half
      let t' : I := ⟨2 * (t : ℝ), by
        constructor
        · have h_pos : 0 ≤ (t : ℝ) := t.prop.1
          linarith
        · linarith⟩
      have h_apply : (γ₁.trans γ₂) t = γ₁ t' := by
        rw [Path.trans_apply, dif_pos h_t_le_half]
        <;> congr <;> apply Subtype.ext <;> simp [t'] <;> ring
      have h_ineq1 : (ts₁ (Fin.castSucc i') : ℝ) ≤ (t' : ℝ) := by
        have h' : (ts_concat (Fin.castSucc i) : ℝ) ≤ (t : ℝ) := by exact_mod_cast h1
        rw [h_ts1] at h'
        simp [scale_first_half, t'] at h' ⊢ <;> linarith
      have h_ineq1' : ts₁ (Fin.castSucc i') ≤ t' := by exact_mod_cast h_ineq1
      have h_ineq2 : (t' : ℝ) ≤ (ts₁ (Fin.succ i') : ℝ) := by
        have h' : (t : ℝ) ≤ (ts_concat (Fin.succ i) : ℝ) := by exact_mod_cast h2
        rw [h_ts2] at h'
        simp [scale_first_half, t'] at h' ⊢ <;> linarith
      have h_ineq2' : t' ≤ ts₁ (Fin.succ i') := by exact_mod_cast h_ineq2
      have h_main : γ₁ t' ∈ (covers₁ i' : Set X) := h_range₁ i' t' h_ineq1' h_ineq2'
      rw [h_apply, h_cover]
      exact h_main
    · -- Case 2: i.val ≥ n₁, use second path
      have h' : n₁ ≤ i.val := by omega
      let i' : Fin n₂ := ⟨i.val - n₁, by omega⟩
      have h_cover : covers_concat i = covers₂ i' := by
        dsimp only [covers_concat]
        rw [dif_neg h] <;> rfl
      have h_cast_val : (Fin.castSucc i).val = i.val := by simp [Fin.castSucc]
      have h_succ_val : (Fin.succ i).val = i.val + 1 := by simp [Fin.succ]
      have h_k1_lt : (Fin.castSucc i).val - n₁ < n₂ + 1 := by omega
      let k1 : Fin (n₂ + 1) := ⟨(Fin.castSucc i).val - n₁, h_k1_lt⟩
      have h_k1_eq : k1 = Fin.castSucc i' := by
        apply Fin.ext <;> simp [k1, i'] <;> omega
      have h_k2_lt : (Fin.succ i).val - n₁ < n₂ + 1 := by omega
      let k2 : Fin (n₂ + 1) := ⟨(Fin.succ i).val - n₁, h_k2_lt⟩
      have h_k2_eq : k2 = Fin.succ i' := by
        apply Fin.ext <;> simp [k2, i'] <;> omega
      have h_ts1_eq : ts_concat (Fin.castSucc i) = scale_second_half (ts₂ (Fin.castSucc i')) := by
        by_cases h_eq : (Fin.castSucc i).val = n₁
        · -- Boundary case: (Fin.castSucc i).val = n₁
          have h_i_val_eq_n1 : i.val = n₁ := by
            rw [←h_cast_val] <;> exact h_eq
          have h_i'_val_eq_0 : i'.val = 0 := by
            simp [i', h_i_val_eq_n1] <;> omega
          have h_ts_cast : ts₂ (Fin.castSucc i') = (0 : I) := by
            have h_fin : Fin.castSucc i' = (0 : Fin (n₂ + 1)) := by
              apply Fin.ext
              simp [h_i'_val_eq_0] <;> omega
            rw [h_fin, h_ts2_zero]
          have h_lt : (Fin.castSucc i).val < n₁ + 1 := by omega
          let k : Fin (n₁ + 1) := ⟨(Fin.castSucc i).val, h_lt⟩
          have h_k_eq_last : k = Fin.last n₁ := by
            apply Fin.ext
            simpa [k] using h_eq
          have h_real_eq : (ts_concat (Fin.castSucc i) : ℝ) = (scale_second_half (ts₂ (Fin.castSucc i')) : ℝ) := by
            rw [h_ts_cast]
            have h1 : (ts_concat (Fin.castSucc i) : ℝ) = (scale_first_half (ts₁ k) : ℝ) := by
              dsimp only [ts_concat]
              have h_le : (Fin.castSucc i).val ≤ n₁ := by linarith
              rw [dif_pos h_le] <;> rfl
            rw [h1, h_k_eq_last, h_ts1_last]
            <;> simp [scale_first_half, scale_second_half] <;> norm_num
          exact Subtype.ext h_real_eq
        · -- General case: (Fin.castSucc i).val > n₁
          have h_ne : (Fin.castSucc i).val ≠ n₁ := h_eq
          have h_gt : n₁ < (Fin.castSucc i).val := by
            rw [h_cast_val] <;> omega
          have h_not_le : ¬ (Fin.castSucc i).val ≤ n₁ := by omega
          dsimp only [ts_concat]
          rw [dif_neg h_not_le]
          <;> congr <;> exact h_k1_eq
      have h_succ_gt : ¬ (Fin.succ i).val ≤ n₁ := by
        rw [h_succ_val] <;> omega
      have h_ts2_eq : ts_concat (Fin.succ i) = scale_second_half (ts₂ (Fin.succ i')) := by
        dsimp only [ts_concat]
        rw [dif_neg h_succ_gt]
        <;> congr <;> exact h_k2_eq
      have h_ts1_val_ge_half : (ts_concat (Fin.castSucc i) : ℝ) ≥ 1 / 2 := by
        rw [h_ts1_eq]
        simp [scale_second_half] <;> have h' := (ts₂ (Fin.castSucc i')).prop.1 <;> linarith
      have h_t_ge_half : (t : ℝ) ≥ 1 / 2 := by
        have h' : (ts_concat (Fin.castSucc i) : ℝ) ≤ (t : ℝ) := by exact_mod_cast h1
        exact le_trans h_ts1_val_ge_half h'
      let t' : I := ⟨2 * (t : ℝ) - 1, by
        constructor
        · linarith
        · have h_top : (t : ℝ) ≤ 1 := t.prop.2
          linarith⟩
      have h_apply : (γ₁.trans γ₂) t = γ₂ t' := by
        by_cases h_eq : (t : ℝ) = 1 / 2
        · -- Boundary case t = 1/2
          have h_t'_eq_0 : (t' : ℝ) = 0 := by
            simp [t', h_eq] <;> ring
          have h_t' : t' = (0 : I) := by
            apply Subtype.ext <;> simp [h_t'_eq_0]
          rw [h_t']
          <;> simp [Path.trans_apply, h_eq] <;> norm_num
        · -- General case t > 1/2
          have h_ne : (t : ℝ) ≠ 1 / 2 := h_eq
          have h_gt : (t : ℝ) > 1 / 2 := by
            exact lt_of_le_of_ne h_t_ge_half h_ne.symm
          have h_not_le : ¬ (t : ℝ) ≤ 1 / 2 := not_le.mpr h_gt
          rw [Path.trans_apply, dif_neg h_not_le]
          <;> congr <;> apply Subtype.ext <;> simp [t'] <;> ring
      have h_ineq1 : (ts₂ (Fin.castSucc i') : ℝ) ≤ (t' : ℝ) := by
        have h' : (ts_concat (Fin.castSucc i) : ℝ) ≤ (t : ℝ) := by exact_mod_cast h1
        rw [h_ts1_eq] at h'
        simp [scale_second_half, t'] at h' ⊢ <;> linarith
      have h_ineq1' : ts₂ (Fin.castSucc i') ≤ t' := by exact_mod_cast h_ineq1
      have h_ineq2 : (t' : ℝ) ≤ (ts₂ (Fin.succ i') : ℝ) := by
        have h' : (t : ℝ) ≤ (ts_concat (Fin.succ i) : ℝ) := by exact_mod_cast h2
        rw [h_ts2_eq] at h'
        simp [scale_second_half, t'] at h' ⊢ <;> linarith
      have h_ineq2' : t' ≤ ts₂ (Fin.succ i') := by exact_mod_cast h_ineq2
      have h_main : γ₂ t' ∈ (covers₂ i' : Set X) := h_range₂ i' t' h_ineq1' h_ineq2'
      rw [h_apply, h_cover]
      exact h_main

  have h_n1_pos : 0 < n₁ := by
    by_contra h
    have h' : n₁ = 0 := by omega
    have h0_in : (0 : I) ∈ S₁ := hS₁.1
    have h1_in : (1 : I) ∈ S₁ := hS₁.2.1
    rw [←h_ts₁_image] at h0_in h1_in
    rcases Finset.mem_image.mp h0_in with ⟨i0, _, h0_eq⟩
    rcases Finset.mem_image.mp h1_in with ⟨i1, _, h1_eq⟩
    have h_i0_val : i0.val = 0 := by
      subst h'
      fin_cases i0 <;> simp
    have h_i1_val : i1.val = 0 := by
      subst h'
      fin_cases i1 <;> simp
    have h_i0_eq_i1 : i0 = i1 := by
      apply Fin.ext <;> simp [h_i0_val, h_i1_val]
    rw [h_i0_eq_i1] at h0_eq
    have h_cont : (0 : I) = (1 : I) := by
      exact h0_eq.symm.trans h1_eq
    norm_num at h_cont
  have h_n2_pos : 0 < n₂ := by
    by_contra h
    have h' : n₂ = 0 := by omega
    have h0_in : (0 : I) ∈ S₂ := hS₂.1
    have h1_in : (1 : I) ∈ S₂ := hS₂.2.1
    rw [←h_ts₂_image] at h0_in h1_in
    rcases Finset.mem_image.mp h0_in with ⟨i0, _, h0_eq⟩
    rcases Finset.mem_image.mp h1_in with ⟨i1, _, h1_eq⟩
    have h_i0_val : i0.val = 0 := by
      subst h'
      fin_cases i0 <;> simp
    have h_i1_val : i1.val = 0 := by
      subst h'
      fin_cases i1 <;> simp
    have h_i0_eq_i1 : i0 = i1 := by
      apply Fin.ext <;> simp [h_i0_val, h_i1_val]
    rw [h_i0_eq_i1] at h0_eq
    have h_cont : (0 : I) = (1 : I) := by
      exact h0_eq.symm.trans h1_eq
    norm_num at h_cont
  have h_n_gt_n1 : n₁ < n := by
    simp [n, h_n2_pos] <;> omega

  let S : Finset I := Finset.image ts_concat Finset.univ
  have h0 : (0 : I) ∈ S := by
    have h_le : (0 : Fin (n + 1)).val ≤ n₁ := by simp <;> omega
    have h_ts0 : ts_concat 0 = (0 : I) := by
      have h_real_eq : (ts_concat 0 : ℝ) = 0 := by
        dsimp only [ts_concat]
        rw [dif_pos h_le]
        <;> simp [scale_first_half, h_ts1_zero] <;> norm_num
      exact Subtype.ext h_real_eq
    exact Finset.mem_image.mpr ⟨0, by simp, h_ts0⟩
  have h1 : (1 : I) ∈ S := by
    have h_gt : ¬ (Fin.last n).val ≤ n₁ := by
      simp [h_n_gt_n1] <;> omega
    have h_k_lt : (Fin.last n).val - n₁ < n₂ + 1 := by omega
    let k : Fin (n₂ + 1) := ⟨(Fin.last n).val - n₁, h_k_lt⟩
    have h_k_eq_last : k = Fin.last n₂ := by
      apply Fin.ext
      simp [k, h_n_gt_n1] <;> omega
    have h_ts1 : ts_concat (Fin.last n) = (1 : I) := by
      have h_eq1 : ts_concat (Fin.last n) = scale_second_half (ts₂ k) := by
        dsimp only [ts_concat]
        rw [dif_neg h_gt] <;> rfl
      rw [h_eq1, h_k_eq_last, h_ts2_last]
      <;> simp [scale_second_half] <;> norm_num
    exact Finset.mem_image.mpr ⟨Fin.last n, by simp, h_ts1⟩
  have h_main : ∀ (s₁ s₂ : I), s₁ ∈ S → s₂ ∈ S → s₁ < s₂ →
      (∀ (t : I), t ∈ S → s₁ < t → t < s₂ → False) →
      ∃ (U : Opens X), U ∈ 𝒰 ∧ ∀ (t : I), s₁ ≤ t → t ≤ s₂ → (γ₁.trans γ₂) t ∈ (U : Set X) := by
    intro s₁ s₂ hs₁ hs₂ h_lt h_no_mid
    rcases Finset.mem_image.mp hs₁ with ⟨i₁, _, rfl⟩
    rcases Finset.mem_image.mp hs₂ with ⟨i₂, _, rfl⟩
    have h_i1_lt_i2 : i₁ < i₂ := by
      by_contra h
      have h' : i₂ ≤ i₁ := by omega
      have h'' : ts_concat i₂ ≤ ts_concat i₁ := h_ts_concat_strict.monotone h'
      have : ¬ ts_concat i₁ < ts_concat i₂ := by exact not_lt.mpr h''
      exact this h_lt
    have h_i2_succ : i₂.val = i₁.val + 1 := by
      by_contra h
      have h_i1_lt_i2_val : i₁.val < i₂.val := by exact_mod_cast h_i1_lt_i2
      have h_le : i₁.val + 1 ≤ i₂.val := by omega
      have h' : i₁.val + 1 < i₂.val := by
        by_contra h_eq
        have h_cont : i₂.val = i₁.val + 1 := by omega
        exact h h_cont
      have h_mid_lt : i₁.val + 1 < n + 1 := by omega
      let t_mid : Fin (n + 1) := ⟨i₁.val + 1, h_mid_lt⟩
      have h_t_mid_val : t_mid.val = i₁.val + 1 := by
        simp [t_mid]
      have h1 : i₁ < t_mid := by
        apply Fin.lt_iff_val_lt_val.mpr
        rw [h_t_mid_val] <;> omega
      have h2 : t_mid < i₂ := by
        apply Fin.lt_iff_val_lt_val.mpr
        rw [h_t_mid_val] <;> exact h'
      have h_ts1 : ts_concat i₁ < ts_concat t_mid := h_ts_concat_strict h1
      have h_ts2 : ts_concat t_mid < ts_concat i₂ := h_ts_concat_strict h2
      have h_mid_in_S : ts_concat t_mid ∈ S := by
        exact Finset.mem_image.mpr ⟨t_mid, by simp, rfl⟩
      exact h_no_mid (ts_concat t_mid) h_mid_in_S h_ts1 h_ts2
    have h_i1_lt_n : i₁.val < n := by omega
    let i : Fin n := ⟨i₁.val, h_i1_lt_n⟩
    have h_i1_eq : i₁ = Fin.castSucc i := by
      apply Fin.ext
      simp [i] <;> rfl
    have h_i2_eq : i₂ = Fin.succ i := by
      apply Fin.ext
      simp [i, h_i2_succ] <;> omega
    refine' ⟨covers_concat i, hcover_concat_mem i, _⟩
    rw [h_i1_eq, h_i2_eq]
    exact h_range_concat i
  have hS : IsAdaptedSubdivision 𝒰 (γ₁.trans γ₂) S := by
    exact ⟨h0, h1, h_main⟩

  -- Step 4: The final algebraic step
  let pts₁ (i : Fin (n₁ + 1)) : X := γ₁ (ts₁ i)
  let pts₂ (i : Fin (n₂ + 1)) : X := γ₂ (ts₂ i)
  let pts_concat (i : Fin (n + 1)) : X := (γ₁.trans γ₂) (ts_concat i)

  have h_pts1_last : pts₁ (Fin.last n₁) = y := by
    dsimp only [pts₁]
    rw [h_ts1_last]
    exact γ₁.target
  have h_pts2_zero : pts₂ 0 = y := by
    dsimp only [pts₂]
    rw [h_ts2_zero]
    exact γ₂.source

  have h_objs_first : ∀ (i : Fin (n₁ + 1)), pts_concat ⟨i.val, by omega⟩ = pts₁ i := by
    intro i
    let j : Fin (n + 1) := ⟨i.val, by omega⟩
    have h_j_val : j.val = i.val := by simp [j]
    have h_i_le_n₁ : j.val ≤ n₁ := by omega
    have h_main : pts_concat j = pts₁ i := by
      dsimp only [pts_concat, pts₁]
      have h_k_eq : (⟨j.val, by omega⟩ : Fin (n₁ + 1)) = i := by
        apply Fin.ext
        simp [h_j_val] <;> omega
      have h_ts_eq : ts_concat j = scale_first_half (ts₁ i) := by
        dsimp only [ts_concat]; rw [dif_pos h_i_le_n₁]
        <;> rw [h_k_eq] <;> rfl
      rw [h_ts_eq]
      have h_eval : (γ₁.trans γ₂) (scale_first_half (ts₁ i)) = γ₁ (ts₁ i) := by
        rw [Path.trans_apply]
        have h_le : (scale_first_half (ts₁ i) : ℝ) ≤ 1 / 2 := by
          simp [scale_first_half] <;> have h := (ts₁ i).prop.2; linarith
        rw [dif_pos h_le]
        <;> congr 1
        <;> apply Subtype.ext
        <;> simp [scale_first_half] <;> ring
      exact h_eval
    exact h_main
  have h_objs_second : ∀ (i : Fin (n₂ + 1)), pts_concat ⟨n₁ + i.val, by omega⟩ = pts₂ i := by
    intro i
    let j : Fin (n + 1) := ⟨n₁ + i.val, by omega⟩
    have h_j_val : j.val = n₁ + i.val := by simp [j]
    have h_ts_eq : ts_concat j = scale_second_half (ts₂ i) := by
      by_cases h_i0 : i.val = 0
      · -- Case i = 0: both sides equal 1/2 as real numbers
        have h_j_eq_n1 : j.val = n₁ := by
          simp [h_j_val, h_i0] <;> omega
        have h_i_eq_0 : i = 0 := by
          apply Fin.ext <;> simp [h_i0]
        have h_real_eq : (ts_concat j : ℝ) = (scale_second_half (ts₂ i) : ℝ) := by
          have h_le : j.val ≤ n₁ := by omega
          have h_k_eq : (⟨j.val, by omega⟩ : Fin (n₁ + 1)) = Fin.last n₁ := by
            apply Fin.ext <;> simp [h_j_eq_n1] <;> omega
          rw [h_i_eq_0, h_ts2_zero]
          dsimp only [ts_concat]
          rw [dif_pos h_le, h_k_eq, h_ts1_last]
          <;> simp [scale_first_half, scale_second_half] <;> norm_num
        apply Subtype.ext
        exact h_real_eq
      · -- Case i > 0: j.val > n₁
        have h_i_pos : 0 < i.val := by omega
        have h_gt_n1 : ¬ j.val ≤ n₁ := by omega
        have h_k_eq : (⟨j.val - n₁, by omega⟩ : Fin (n₂ + 1)) = i := by
          apply Fin.ext
          simp [h_j_val] <;> omega
        dsimp only [ts_concat]; rw [dif_neg h_gt_n1]
        <;> rw [h_k_eq] <;> rfl
    have h_main : pts_concat j = pts₂ i := by
      dsimp only [pts_concat, pts₂]
      rw [h_ts_eq]
      have h_eval : (γ₁.trans γ₂) (scale_second_half (ts₂ i)) = γ₂ (ts₂ i) := by
        by_cases h : (scale_second_half (ts₂ i) : ℝ) = 1 / 2
        · -- Case 1: equal to 1/2, then ts₂ i = 0
          have h_ts2_eq_0 : ts₂ i = 0 := by
            apply Subtype.ext
            have h_eq : (scale_second_half (ts₂ i) : ℝ) = 1 / 2 := h
            have h_simp : (scale_second_half (ts₂ i) : ℝ) = 1 / 2 + (ts₂ i : ℝ) / 2 := by
              simp [scale_second_half] <;> ring
            have h_eq2 : 1 / 2 + (ts₂ i : ℝ) / 2 = 1 / 2 := by
              rw [←h_simp, h_eq]
            have h_final : (ts₂ i : ℝ) = 0 := by linarith
            exact h_final
          rw [h_ts2_eq_0]
          <;> simp [Path.trans_apply, scale_second_half] <;> exact γ₁.target
        · -- Case 2: strictly greater than 1/2
          have h_ge : (scale_second_half (ts₂ i) : ℝ) ≥ 1 / 2 := by
            simp [scale_second_half] <;> have h' := (ts₂ i).prop.1; linarith
          have h_gt : (scale_second_half (ts₂ i) : ℝ) > 1 / 2 := by
            have h_ne' : (1 / 2 : ℝ) ≠ (scale_second_half (ts₂ i) : ℝ) := Ne.symm h
            exact lt_of_le_of_ne h_ge h_ne'
          have h_not_le : ¬ (scale_second_half (ts₂ i) : ℝ) ≤ 1 / 2 := not_le.mpr h_gt
          rw [Path.trans_apply, dif_neg h_not_le]
          <;> congr 1
          <;> apply Subtype.ext
          <;> simp [scale_second_half] <;> ring
      exact h_eval
    exact h_main

  let objs₁' (i : Fin (n₁ + 1)) := desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts₁ i))
  let objs₂' (i : Fin (n₂ + 1)) := desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts₂ i))
  let objs_concat' (i : Fin (n + 1)) := desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts_concat i))

  have h_match : objs₁' (Fin.last n₁) = objs₂' 0 := by
    dsimp only [objs₁', objs₂']
    rw [h_pts1_last, h_pts2_zero] <;> rfl

  let γs₁ (i : Fin n₁) : Path (pts₁ (Fin.castSucc i)) (pts₁ (Fin.succ i)) :=
    γ₁.subpath (ts₁ (Fin.castSucc i)) (ts₁ (Fin.succ i))
  let γs₂ (i : Fin n₂) : Path (pts₂ (Fin.castSucc i)) (pts₂ (Fin.succ i)) :=
    γ₂.subpath (ts₂ (Fin.castSucc i)) (ts₂ (Fin.succ i))
  let γs_concat (i : Fin n) : Path (pts_concat (Fin.castSucc i)) (pts_concat (Fin.succ i)) :=
    (γ₁.trans γ₂).subpath (ts_concat (Fin.castSucc i)) (ts_concat (Fin.succ i))

  have h_ranges₁ : ∀ (i : Fin n₁), Set.range (γs₁ i) ⊆ (covers₁ i : Set X) := by
    intro i
    have h_lt : Fin.castSucc i < Fin.succ i := by apply Fin.castSucc_lt_succ
    have h_ts_lt : ts₁ (Fin.castSucc i) < ts₁ (Fin.succ i) := h_ts₁_strict h_lt
    have h_range_eq : Set.range (γs₁ i) = γ₁ '' Set.Icc (ts₁ (Fin.castSucc i)) (ts₁ (Fin.succ i)) := by
      rw [Path.range_subpath γ₁ (ts₁ (Fin.castSucc i)) (ts₁ (Fin.succ i))]
      <;> rw [Set.uIcc_of_le (le_of_lt h_ts_lt)]
    rw [h_range_eq]
    intro z hz
    rcases hz with ⟨t, ht, rfl⟩
    exact h_range₁ i t ht.1 ht.2
  have h_ranges₂ : ∀ (i : Fin n₂), Set.range (γs₂ i) ⊆ (covers₂ i : Set X) := by
    intro i
    have h_lt : Fin.castSucc i < Fin.succ i := by apply Fin.castSucc_lt_succ
    have h_ts_lt : ts₂ (Fin.castSucc i) < ts₂ (Fin.succ i) := h_ts₂_strict h_lt
    have h_range_eq : Set.range (γs₂ i) = γ₂ '' Set.Icc (ts₂ (Fin.castSucc i)) (ts₂ (Fin.succ i)) := by
      rw [Path.range_subpath γ₂ (ts₂ (Fin.castSucc i)) (ts₂ (Fin.succ i))]
      <;> rw [Set.uIcc_of_le (le_of_lt h_ts_lt)]
    rw [h_range_eq]
    intro z hz
    rcases hz with ⟨t, ht, rfl⟩
    exact h_range₂ i t ht.1 ht.2
  have h_ranges_concat : ∀ (i : Fin n), Set.range (γs_concat i) ⊆ (covers_concat i : Set X) := by
    intro i
    have h_lt : Fin.castSucc i < Fin.succ i := by apply Fin.castSucc_lt_succ
    have h_ts_lt : ts_concat (Fin.castSucc i) < ts_concat (Fin.succ i) := h_ts_concat_strict h_lt
    have h_range_eq : Set.range (γs_concat i) = (γ₁.trans γ₂) '' Set.Icc (ts_concat (Fin.castSucc i)) (ts_concat (Fin.succ i)) := by
      rw [Path.range_subpath (γ₁.trans γ₂) (ts_concat (Fin.castSucc i)) (ts_concat (Fin.succ i))]
      <;> rw [Set.uIcc_of_le (le_of_lt h_ts_lt)]
    rw [h_range_eq]
    intro z hz
    rcases hz with ⟨t, ht, rfl⟩
    exact h_range_concat i t ht.1 ht.2

  let homs₁' (i : Fin n₁) : objs₁' (Fin.castSucc i) ⟶ objs₁' (Fin.succ i) :=
    single_covered_map X 𝒰 hcover hfinite_intersections s (γs₁ i) (covers₁ i) (hcover₁_mem i) (h_ranges₁ i)
  let homs₂' (i : Fin n₂) : objs₂' (Fin.castSucc i) ⟶ objs₂' (Fin.succ i) :=
    single_covered_map X 𝒰 hcover hfinite_intersections s (γs₂ i) (covers₂ i) (hcover₂_mem i) (h_ranges₂ i)
  let homs_concat' (i : Fin n) : objs_concat' (Fin.castSucc i) ⟶ objs_concat' (Fin.succ i) :=
    single_covered_map X 𝒰 hcover hfinite_intersections s (γs_concat i) (covers_concat i) (hcover_concat_mem i) (h_ranges_concat i)

  have h_homs_first : ∀ (i : Fin n₁),
      eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) (h_objs_first (Fin.castSucc i))).symm ≫
      homs_concat' ⟨i.val, by omega⟩ ≫
      eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) (h_objs_first (Fin.succ i))) =
      homs₁' i := by
    intro i
    have h_i_lt_n : i.val < n := by omega
    let j : Fin n := ⟨i.val, h_i_lt_n⟩
    have h_j_val : j.val = i.val := by simp [j]
    have h_j_lt_n1 : j.val < n₁ := by
      have h : i.val < n₁ := i.is_lt
      omega
    have h_cover_eq : covers_concat j = covers₁ i := by
      dsimp only [covers_concat]
      rw [dif_pos h_j_lt_n1] <;> rfl
    have h_cast_lt : (Fin.castSucc j).val < n₁ := by
      have h1 : (Fin.castSucc j).val = j.val := by simp
      rw [h1, h_j_val]
      exact i.is_lt
    have h_succ_le : (Fin.succ j).val ≤ n₁ := by
      have h1 : (Fin.succ j).val = j.val + 1 := by simp
      rw [h1, h_j_val]
      have h2 : i.val < n₁ := i.is_lt
      omega
    have h_cast_le : (Fin.castSucc j).val ≤ n₁ := by
      have h1 : (Fin.castSucc j).val < n₁ := h_cast_lt
      exact le_of_lt h1
    have h_k1_eq : (⟨(Fin.castSucc j).val, by omega⟩ : Fin (n₁ + 1)) = Fin.castSucc i := by
      apply Fin.ext
      simp [h_j_val] <;> omega
    have h_k2_eq : (⟨(Fin.succ j).val, by omega⟩ : Fin (n₁ + 1)) = Fin.succ i := by
      apply Fin.ext
      simp [h_j_val] <;> omega
    have h1 : ts_concat (Fin.castSucc j) = scale_first_half (ts₁ (Fin.castSucc i)) := by
      dsimp only [ts_concat]; rw [dif_pos h_cast_le]
      <;> rw [h_k1_eq] <;> rfl
    have h2 : ts_concat (Fin.succ j) = scale_first_half (ts₁ (Fin.succ i)) := by
      dsimp only [ts_concat]; rw [dif_pos h_succ_le]
      <;> rw [h_k2_eq] <;> rfl
    have hfun : ∀ (t : I), γs_concat j t = γs₁ i t := by
      intro t
      dsimp only [γs_concat, γs₁]
      have h4 : (Set.Icc.convexComb (ts_concat (Fin.castSucc j)) (ts_concat (Fin.succ j)) t : ℝ) ≤ 1 / 2 := by
        rw [h1, h2]
        have h_eq : (Set.Icc.convexComb (scale_first_half (ts₁ (Fin.castSucc i))) (scale_first_half (ts₁ (Fin.succ i))) t : ℝ) =
            (1 / 2 : ℝ) * (Set.Icc.convexComb (ts₁ (Fin.castSucc i)) (ts₁ (Fin.succ i)) t : ℝ) := by
          simp [Set.Icc.convexComb, scale_first_half] <;> ring
        rw [h_eq]
        have h_nonneg : 0 ≤ (Set.Icc.convexComb (ts₁ (Fin.castSucc i)) (ts₁ (Fin.succ i)) t : ℝ) := by
          exact (Set.Icc.convexComb (ts₁ (Fin.castSucc i)) (ts₁ (Fin.succ i)) t).prop.1
        have h_le_one : (Set.Icc.convexComb (ts₁ (Fin.castSucc i)) (ts₁ (Fin.succ i)) t : ℝ) ≤ 1 := by
          exact (Set.Icc.convexComb (ts₁ (Fin.castSucc i)) (ts₁ (Fin.succ i)) t).prop.2
        linarith
      have h5 : (γ₁.trans γ₂) (Set.Icc.convexComb (ts_concat (Fin.castSucc j)) (ts_concat (Fin.succ j)) t) =
          γ₁ (Set.Icc.convexComb (ts₁ (Fin.castSucc i)) (ts₁ (Fin.succ i)) t) := by
        rw [h1, h2]
        have h4' : (Set.Icc.convexComb (scale_first_half (ts₁ (Fin.castSucc i))) (scale_first_half (ts₁ (Fin.succ i))) t : ℝ) ≤ 1 / 2 := by
          have h_eq : (Set.Icc.convexComb (scale_first_half (ts₁ (Fin.castSucc i))) (scale_first_half (ts₁ (Fin.succ i))) t : ℝ) =
              (1 / 2 : ℝ) * (Set.Icc.convexComb (ts₁ (Fin.castSucc i)) (ts₁ (Fin.succ i)) t : ℝ) := by
            simp [Set.Icc.convexComb, scale_first_half] <;> ring
          rw [h_eq]
          have h_nonneg : 0 ≤ (Set.Icc.convexComb (ts₁ (Fin.castSucc i)) (ts₁ (Fin.succ i)) t : ℝ) := by
            exact (Set.Icc.convexComb (ts₁ (Fin.castSucc i)) (ts₁ (Fin.succ i)) t).prop.1
          have h_le_one : (Set.Icc.convexComb (ts₁ (Fin.castSucc i)) (ts₁ (Fin.succ i)) t : ℝ) ≤ 1 := by
            exact (Set.Icc.convexComb (ts₁ (Fin.castSucc i)) (ts₁ (Fin.succ i)) t).prop.2
          linarith
        rw [Path.trans_apply]
        rw [dif_pos h4']
        <;> congr 1
        <;> apply Subtype.ext
        <;> simp [Set.Icc.convexComb, scale_first_half] <;> ring
      exact h5
    have h_range_eq : Set.range (γs_concat j) ⊆ (covers₁ i : Set X) := by
      rw [←h_cover_eq]
      exact h_ranges_concat j
    have h_main : eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) (h_objs_first (Fin.castSucc i))).symm ≫
        homs_concat' j ≫
        eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) (h_objs_first (Fin.succ i))) =
        homs₁' i := by
      have h1 : homs_concat' j =
          single_covered_map X 𝒰 hcover hfinite_intersections s (γs_concat j) (covers₁ i) (hcover₁_mem i) h_range_eq := by
        dsimp only [homs_concat']
        congr <;> try { exact h_cover_eq } <;> try { exact Subsingleton.elim _ _ }
      rw [h1]
      exact single_covered_map_congr X 𝒰 hcover hfinite_intersections s
        (γs_concat j) (γs₁ i)
        (h_objs_first (Fin.castSucc i)) (h_objs_first (Fin.succ i))
        hfun
        (covers₁ i) (hcover₁_mem i)
        h_range_eq (h_ranges₁ i)
    exact h_main

  have h_homs_second : ∀ (i : Fin n₂),
      eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) (h_objs_second (Fin.castSucc i))).symm ≫
      homs_concat' ⟨n₁ + i.val, by omega⟩ ≫
      eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) (h_objs_second (Fin.succ i))) =
      homs₂' i := by
    intro i
    have h_sum_lt : n₁ + i.val < n := by omega
    let j : Fin n := ⟨n₁ + i.val, h_sum_lt⟩
    have h_j_not_lt_n1 : ¬ j.val < n₁ := by
      simp [j] <;> omega
    have h_i_eq : (⟨j.val - n₁, by omega⟩ : Fin n₂) = i := by
      apply Fin.ext
      simp [j] <;> omega
    have h_cover_eq : covers_concat j = covers₂ i := by
      dsimp only [covers_concat]
      rw [dif_neg h_j_not_lt_n1]
      <;> rw [h_i_eq]
      <;> rfl
    have h_k1_eq : (⟨(Fin.castSucc j).val - n₁, by omega⟩ : Fin (n₂ + 1)) = Fin.castSucc i := by
      apply Fin.ext
      simp [j] <;> omega
    have h_k2_eq : (⟨(Fin.succ j).val - n₁, by omega⟩ : Fin (n₂ + 1)) = Fin.succ i := by
      apply Fin.ext
      simp [j] <;> omega
    have h_cast_le : (Fin.castSucc j).val ≤ n₁ ∨ ¬ (Fin.castSucc j).val ≤ n₁ := em _
    have h1 : ts_concat (Fin.castSucc j) = scale_second_half (ts₂ (Fin.castSucc i)) := by
      cases h_cast_le with
      | inl h_cast_le =>
        -- Case (Fin.castSucc j).val ≤ n₁: this means i.val = 0
        have h_i_val_eq_0 : i.val = 0 := by
          simp [j] at h_cast_le <;> omega
        have h_cast_eq_n1 : (Fin.castSucc j).val = n₁ := by
          simp [j, h_i_val_eq_0] <;> omega
        have h_real_eq : (ts_concat (Fin.castSucc j) : ℝ) = (scale_second_half (ts₂ (Fin.castSucc i)) : ℝ) := by
          have h_ts2_0 : ts₂ (Fin.castSucc i) = (0 : I) := by
            have h : Fin.castSucc i = (0 : Fin (n₂ + 1)) := by
              apply Fin.ext
              simp [h_i_val_eq_0] <;> omega
            rw [h, h_ts2_zero]
          have h_lt : (Fin.castSucc j).val < n₁ + 1 := by omega
          let k : Fin (n₁ + 1) := ⟨(Fin.castSucc j).val, h_lt⟩
          have h_fin_eq : k = Fin.last n₁ := by
            apply Fin.ext
            simpa [k] using h_cast_eq_n1
          have h1 : ts_concat (Fin.castSucc j) = scale_first_half (ts₁ k) := by
            dsimp only [ts_concat]
            rw [dif_pos h_cast_le] <;> rfl
          have h2 : (scale_first_half (ts₁ k) : ℝ) = (scale_first_half (ts₁ (Fin.last n₁)) : ℝ) := by
            rw [h_fin_eq]
          have h_main : (ts_concat (Fin.castSucc j) : ℝ) = (scale_first_half (ts₁ (Fin.last n₁)) : ℝ) := by
            have h1' : (ts_concat (Fin.castSucc j) : ℝ) = (scale_first_half (ts₁ k) : ℝ) := by
              exact congr_arg (fun x : I => (x : ℝ)) h1
            calc
              (ts_concat (Fin.castSucc j) : ℝ) = (scale_first_half (ts₁ k) : ℝ) := h1'
              _ = (scale_first_half (ts₁ (Fin.last n₁)) : ℝ) := h2
          rw [h_main, h_ts1_last, h_ts2_0]
          <;> simp [scale_first_half, scale_second_half] <;> norm_num
        exact Subtype.ext h_real_eq
      | inr h_cast_gt =>
        dsimp only [ts_concat]; rw [dif_neg h_cast_gt]
        <;> rw [h_k1_eq] <;> rfl
    have h_succ_gt : ¬ (Fin.succ j).val ≤ n₁ := by
      simp [j] <;> omega
    have h2 : ts_concat (Fin.succ j) = scale_second_half (ts₂ (Fin.succ i)) := by
      dsimp only [ts_concat]; rw [dif_neg h_succ_gt]
      <;> rw [h_k2_eq] <;> rfl
    have h_scale_apply : ∀ (c : I), (γ₁.trans γ₂) (scale_second_half c) = γ₂ c := by
      intro c
      by_cases h : (scale_second_half c : ℝ) ≤ 1 / 2
      · -- Case ≤ 1/2: this means c = 0
        have h_c_eq_0 : (c : ℝ) = 0 := by
          simp [scale_second_half] at h <;> linarith [c.prop.1]
        have h_c : c = (0 : I) := by
          apply Subtype.ext <;> simp [h_c_eq_0]
        rw [h_c]
        <;> simp [Path.trans_apply, scale_second_half] <;> norm_num
      · -- Case > 1/2
        rw [Path.trans_apply, dif_neg h]
        <;> simp [scale_second_half] <;> congr <;> ring
    have h_combo_eq : ∀ (a b : I) (t : I),
        Set.Icc.convexComb (scale_second_half a) (scale_second_half b) t =
        scale_second_half (Set.Icc.convexComb a b t) := by
      intro a b t
      apply Subtype.ext
      simp [Set.Icc.convexComb, scale_second_half] <;> ring
    have hfun : ∀ (t : I), γs_concat j t = γs₂ i t := by
      intro t
      dsimp only [γs_concat, γs₂]
      set a : I := ts₂ (Fin.castSucc i) with ha
      set b : I := ts₂ (Fin.succ i) with hb
      set c : I := Set.Icc.convexComb a b t with hc
      have h_combo1 : Set.Icc.convexComb (ts_concat (Fin.castSucc j)) (ts_concat (Fin.succ j)) t =
          Set.Icc.convexComb (scale_second_half a) (scale_second_half b) t := by
        rw [h1, h2]
        <;> rfl
      have h_combo2 : Set.Icc.convexComb (scale_second_half a) (scale_second_half b) t = scale_second_half c := by
        exact h_combo_eq a b t
      have h_combo : Set.Icc.convexComb (ts_concat (Fin.castSucc j)) (ts_concat (Fin.succ j)) t = scale_second_half c := by
        rw [h_combo1, h_combo2]
      have h_goal : (γ₁.trans γ₂) (Set.Icc.convexComb (ts_concat (Fin.castSucc j)) (ts_concat (Fin.succ j)) t) = γ₂ c := by
        rw [h_combo]
        exact h_scale_apply c
      have h_subpath1 : ((γ₁.trans γ₂).subpath (ts_concat (Fin.castSucc j)) (ts_concat (Fin.succ j))) t =
          (γ₁.trans γ₂) (Set.Icc.convexComb (ts_concat (Fin.castSucc j)) (ts_concat (Fin.succ j)) t) := by
        rfl
      have h_goal' : ((γ₁.trans γ₂).subpath (ts_concat (Fin.castSucc j)) (ts_concat (Fin.succ j))) t = (γs₂ i) t := by
        rw [h_subpath1]
        have h_rhs : (γs₂ i) t = γ₂ c := by
          dsimp only [γs₂]
          <;> rfl
        rw [h_rhs]
        exact h_goal
      exact h_goal'
    have h_range_eq : Set.range (γs_concat j) ⊆ (covers₂ i : Set X) := by
      rw [←h_cover_eq]
      exact h_ranges_concat j
    have h_main : eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) (h_objs_second (Fin.castSucc i))).symm ≫
        homs_concat' j ≫
        eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) (h_objs_second (Fin.succ i))) =
        homs₂' i := by
      have h1 : homs_concat' j =
          single_covered_map X 𝒰 hcover hfinite_intersections s (γs_concat j) (covers₂ i) (hcover₂_mem i) h_range_eq := by
        dsimp only [homs_concat']
        congr <;> try { exact h_cover_eq } <;> try { exact Subsingleton.elim _ _ }
      rw [h1]
      exact single_covered_map_congr X 𝒰 hcover hfinite_intersections s
        (γs_concat j) (γs₂ i)
        (h_objs_second (Fin.castSucc i)) (h_objs_second (Fin.succ i))
        hfun
        (covers₂ i) (hcover₂_mem i)
        h_range_eq (h_ranges₂ i)
    exact h_main

  have h_objs_first' : ∀ (i : Fin (n₁ + 1)), objs_concat' ⟨i.val, by omega⟩ = objs₁' i := by
    intro i
    dsimp only [objs_concat', objs₁']
    rw [h_objs_first i]
    <;> rfl
  have h_objs_second' : ∀ (i : Fin (n₂ + 1)), objs_concat' ⟨n₁ + i.val, by omega⟩ = objs₂' i := by
    intro i
    dsimp only [objs_concat', objs₂']
    rw [h_objs_second i]
    <;> rfl
  have h_main_eq : eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) (h_objs_first 0)).symm ≫
      comp_list n objs_concat' homs_concat' ≫
      eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) (h_objs_second (Fin.last n₂))) =
      comp_list n₁ objs₁' homs₁' ≫ eqToHom h_match ≫ comp_list n₂ objs₂' homs₂' := by
    exact comp_list_concat_explicit objs₁' homs₁' objs₂' homs₂' h_match objs_concat' homs_concat' h_objs_first' h_objs_second' h_homs_first h_homs_second

  have h_eq_concat : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS =
      my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS n ts_concat h_ts_concat_strict rfl covers_concat hcover_concat_mem h_range_concat :=
    my_map_from_adapted_subdivision_universal X 𝒰 hcover hfinite_intersections s hS ts_concat h_ts_concat_strict rfl covers_concat hcover_concat_mem h_range_concat

  have h_eq1 : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS₁ =
      my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS₁ n₁ ts₁ h_ts₁_strict h_ts₁_image covers₁ hcover₁_mem h_range₁ := h_eq₁
  have h_eq2 : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS₂ =
      my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS₂ n₂ ts₂ h_ts₂_strict h_ts₂_image covers₂ hcover₂_mem h_range₂ := h_eq₂

  -- Helper facts about endpoints
  have h_ts1_zero : ts₁ 0 = (0 : I) := by
    have h0_in : (0 : I) ∈ S₁ := hS₁.1
    have h0_in_image : (0 : I) ∈ Finset.image ts₁ Finset.univ := by rw [h_ts₁_image] <;> exact h0_in
    let i : Fin (n₁ + 1) := Classical.choose (Finset.mem_image.mp h0_in_image)
    let hi : ts₁ i = (0 : I) := (Classical.choose_spec (Finset.mem_image.mp h0_in_image)).2
    have h_i_eq_0 : i = 0 := by
      by_contra h
      have h_i_pos : 0 < i := Fin.pos_iff_ne_zero.mpr h
      have h_ts0_lt_tsi : ts₁ 0 < ts₁ i := h_ts₁_strict h_i_pos
      rw [hi] at h_ts0_lt_tsi
      have h_nonneg : (0 : ℝ) ≤ (ts₁ 0 : ℝ) := (ts₁ 0).prop.1
      have h_cont : (ts₁ 0 : ℝ) < (0 : ℝ) := by exact_mod_cast h_ts0_lt_tsi
      linarith
    rw [h_i_eq_0] at hi
    exact hi
  have h_ts2_last : ts₂ (Fin.last n₂) = (1 : I) := by
    have h1_in : (1 : I) ∈ S₂ := hS₂.2.1
    have h1_in_image : (1 : I) ∈ Finset.image ts₂ Finset.univ := by rw [h_ts₂_image] <;> exact h1_in
    let i : Fin (n₂ + 1) := Classical.choose (Finset.mem_image.mp h1_in_image)
    let hi : ts₂ i = (1 : I) := (Classical.choose_spec (Finset.mem_image.mp h1_in_image)).2
    have h_i_eq_last : i = Fin.last n₂ := by
      apply Fin.eq_last_of_not_lt
      intro h
      have h_tsi_lt_ts1 : ts₂ i < ts₂ (Fin.last n₂) := h_ts₂_strict h
      rw [hi] at h_tsi_lt_ts1
      have h' : (1 : ℝ) < (ts₂ (Fin.last n₂) : ℝ) := by exact_mod_cast h_tsi_lt_ts1
      have h'' : (ts₂ (Fin.last n₂) : ℝ) ≤ 1 := (ts₂ (Fin.last n₂)).prop.2
      linarith
    rw [h_i_eq_last] at hi
    exact hi

  have h_pts0₁ : pts₁ 0 = x := by
    dsimp only [pts₁]
    rw [h_ts1_zero]
    exact γ₁.source
  have h_pts_last₁ : pts₁ (Fin.last n₁) = y := h_pts1_last
  have h_pts0₂ : pts₂ 0 = y := h_pts2_zero
  have h_pts_last₂ : pts₂ (Fin.last n₂) = z := by
    dsimp only [pts₂]
    rw [h_ts2_last]
    exact γ₂.target

  have h_pts0_concat : pts_concat 0 = x := by
    have h : pts_concat 0 = pts₁ 0 := h_objs_first 0
    rw [h, h_pts0₁]
  have h_pts_last_concat : pts_concat (Fin.last n) = z := by
    have h : pts_concat (Fin.last n) = pts₂ (Fin.last n₂) := h_objs_second (Fin.last n₂)
    rw [h, h_pts_last₂]

  -- Now we can conclude
  refine' ⟨S, hS, _⟩
  rw [h_eq_concat, h_eq1, h_eq2]
  dsimp only [my_map_from_adapted_subdivision_with_covers]
  -- Helper: all eqToHom terms between the same objects are equal
  have h_eqToHom_congr : ∀ {a b : s.pt} (h1 h2 : a = b), eqToHom h1 = eqToHom h2 := by
    intro a b h1 h2
    congr <;> tauto
  -- Helper: composition of two eqToHom is eqToHom of the transitive equality
  have h_compose_eqToHom : ∀ {a b c : s.pt} (h1 : a = b) (h2 : b = c),
      eqToHom h1 ≫ eqToHom h2 = eqToHom (h1.trans h2) := by
    intro a b c h1 h2
    rw [eqToHom_trans]
  -- Let A, B, C be the objects we're working with
  let A : s.pt := desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk x)
  let B : s.pt := desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk y)
  let C : s.pt := desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk z)
  -- Whisker h_main_eq with eqToHom on both sides
  let f : objs₁' 0 ⟶ objs₂' (Fin.last n₂) :=
    eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) (h_objs_first 0)).symm ≫
    comp_list n objs_concat' homs_concat' ≫
    eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) (h_objs_second (Fin.last n₂)))
  let g : objs₁' 0 ⟶ objs₂' (Fin.last n₂) :=
    comp_list n₁ objs₁' homs₁' ≫ eqToHom h_match ≫ comp_list n₂ objs₂' homs₂'
  have h_fg : f = g := h_main_eq
  -- Whisker both sides with eqToHom from A to objs₁' 0 and from objs₂' (Fin.last n₂) to C
  let h_left : A = objs₁' 0 := by
    exact (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts0₁).symm
  let h_right : objs₂' (Fin.last n₂) = C := by
    exact congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts_last₂
  have h_whiskered : eqToHom h_left ≫ f ≫ eqToHom h_right = eqToHom h_left ≫ g ≫ eqToHom h_right := by
    rw [h_fg]
  -- Now show that the LHS of the goal equals eqToHom h_left ≫ f ≫ eqToHom h_right
  have h_lhs_eq :
    eqToHom (show (let pts : Fin (n + 1) → X := fun i => (γ₁.trans γ₂) (ts_concat i)
      let objs : Fin (n + 1) → s.pt := fun i => desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts i))
      objs 0) = A from by
        dsimp only [A]
        <;> congr <;> funext i <;> rfl).symm ≫
    (let pts : Fin (n + 1) → X := fun i => (γ₁.trans γ₂) (ts_concat i)
      let objs : Fin (n + 1) → s.pt := fun i => desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts i))
      let γs : ∀ i : Fin n, Path (pts (Fin.castSucc i)) (pts (Fin.succ i)) := fun i =>
        (γ₁.trans γ₂).subpath (ts_concat (Fin.castSucc i)) (ts_concat (Fin.succ i))
      let homs : ∀ i : Fin n, objs (Fin.castSucc i) ⟶ objs (Fin.succ i) := fun i =>
        single_covered_map X 𝒰 hcover hfinite_intersections s (γs i) (covers_concat i) (hcover_concat_mem i) (h_ranges_concat i)
      comp_list n objs homs) ≫
    eqToHom (show (let pts : Fin (n + 1) → X := fun i => (γ₁.trans γ₂) (ts_concat i)
      let objs : Fin (n + 1) → s.pt := fun i => desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts i))
      objs (Fin.last n)) = C from by
        dsimp only [C]
        <;> congr <;> funext i <;> rfl) =
    eqToHom h_left ≫ f ≫ eqToHom h_right := by
    have h1 : ∀ (h1 h2 : A = objs_concat' 0), eqToHom h1 = eqToHom h2 := h_eqToHom_congr
    have h2 : ∀ (h1 h2 : objs_concat' (Fin.last n) = C), eqToHom h1 = eqToHom h2 := h_eqToHom_congr
    simp [f, Category.assoc, h1, h2]
    <;> rfl
  -- Now show that the RHS of the goal equals eqToHom h_left ≫ g ≫ eqToHom h_right
  have h_rhs_eq :
    (eqToHom (show (let pts : Fin (n₁ + 1) → X := fun i => γ₁ (ts₁ i)
      let objs : Fin (n₁ + 1) → s.pt := fun i => desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts i))
      objs 0) = A from by
        dsimp only [A]
        <;> congr <;> funext i <;> rfl).symm ≫
      (let pts : Fin (n₁ + 1) → X := fun i => γ₁ (ts₁ i)
        let objs : Fin (n₁ + 1) → s.pt := fun i => desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts i))
        let γs : ∀ i : Fin n₁, Path (pts (Fin.castSucc i)) (pts (Fin.succ i)) := fun i =>
          γ₁.subpath (ts₁ (Fin.castSucc i)) (ts₁ (Fin.succ i))
        let homs : ∀ i : Fin n₁, objs (Fin.castSucc i) ⟶ objs (Fin.succ i) := fun i =>
          single_covered_map X 𝒰 hcover hfinite_intersections s (γs i) (covers₁ i) (hcover₁_mem i) (h_ranges₁ i)
        comp_list n₁ objs homs) ≫
      eqToHom (show (let pts : Fin (n₁ + 1) → X := fun i => γ₁ (ts₁ i)
        let objs : Fin (n₁ + 1) → s.pt := fun i => desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts i))
        objs (Fin.last n₁)) = B from by
          dsimp only [B]
          <;> congr <;> funext i <;> rfl)) ≫
    (eqToHom (show (let pts : Fin (n₂ + 1) → X := fun i => γ₂ (ts₂ i)
      let objs : Fin (n₂ + 1) → s.pt := fun i => desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts i))
      objs 0) = B from by
        dsimp only [B]
        <;> congr <;> funext i <;> rfl).symm ≫
      (let pts : Fin (n₂ + 1) → X := fun i => γ₂ (ts₂ i)
        let objs : Fin (n₂ + 1) → s.pt := fun i => desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts i))
        let γs : ∀ i : Fin n₂, Path (pts (Fin.castSucc i)) (pts (Fin.succ i)) := fun i =>
          γ₂.subpath (ts₂ (Fin.castSucc i)) (ts₂ (Fin.succ i))
        let homs : ∀ i : Fin n₂, objs (Fin.castSucc i) ⟶ objs (Fin.succ i) := fun i =>
          single_covered_map X 𝒰 hcover hfinite_intersections s (γs i) (covers₂ i) (hcover₂_mem i) (h_ranges₂ i)
        comp_list n₂ objs homs) ≫
      eqToHom (show (let pts : Fin (n₂ + 1) → X := fun i => γ₂ (ts₂ i)
        let objs : Fin (n₂ + 1) → s.pt := fun i => desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (pts i))
        objs (Fin.last n₂)) = C from by
          dsimp only [C]
          <;> congr <;> funext i <;> rfl)) =
    eqToHom h_left ≫ g ≫ eqToHom h_right := by
    have h1 : ∀ (h1 h2 : A = objs₁' 0), eqToHom h1 = eqToHom h2 := h_eqToHom_congr
    have h2 : ∀ (h1 h2 : objs₁' (Fin.last n₁) = B), eqToHom h1 = eqToHom h2 := h_eqToHom_congr
    have h3 : ∀ (h1 h2 : B = objs₂' 0), eqToHom h1 = eqToHom h2 := h_eqToHom_congr
    have h4 : ∀ (h1 h2 : objs₂' (Fin.last n₂) = C), eqToHom h1 = eqToHom h2 := h_eqToHom_congr
    have h_middle : eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts_last₁) ≫
        eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts0₂).symm =
        eqToHom h_match := by
      have h_comp : eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts_last₁) ≫
          eqToHom (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts0₂).symm =
          eqToHom ((congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts_last₁).trans
            (congr_arg (desc_functor_obj X 𝒰 hcover s ∘ FundamentalGroupoid.mk) h_pts0₂).symm) := by
        rw [eqToHom_trans]
      rw [h_comp]
      exact h_eqToHom_congr _ _
    simp [g, Category.assoc, h1, h2, h3, h4, h_middle]
    <;> rfl
  rw [h_lhs_eq, h_rhs_eq]
  exact h_whiskered

end

end
