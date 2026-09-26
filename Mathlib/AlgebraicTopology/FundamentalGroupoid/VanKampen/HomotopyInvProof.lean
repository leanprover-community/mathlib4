module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.CleanDescent
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.ConsecutiveRows
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.RectangleHomotopy
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.RectangleBoundaryHomotopy
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.SingleCoveredConstPath

@[expose] public section

set_option maxHeartbeats 500000

open TopologicalSpace CategoryTheory Limits

open scoped unitInterval

noncomputable section

universe u

variable (X : Type u) [TopologicalSpace X]
variable (𝒰 : Set (Opens X))
variable (hcover : ∀ x : X, ∃ U : Opens X, U ∈ 𝒰 ∧ x ∈ U)
variable (hpath_connected : ∀ U : Opens X, U ∈ 𝒰 → IsPathConnected (U : Set X))
variable (hfinite_intersections :
  ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)

variable (s : Cocone
    (((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
      Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor))

include hcover hfinite_intersections

include hcover hfinite_intersections

theorem consecutive_rows_equal_my_desc_map_aux {x y : X} {γ₁ γ₂ : Path x y}
    (H : Path.Homotopy γ₁ γ₂) {n : ℕ} (hn_pos : 0 < n)
    (pcH : PartwiseCoveredHomotopy 𝒰 H n n) (j : Fin n) :
    my_desc_map X 𝒰 hcover hfinite_intersections s
      (H.eval ⟨(j.val : ℝ) / (n : ℝ), by
        have h₁ : 0 ≤ (j.val : ℝ) / (n : ℝ) := by positivity
        have h₂ : (j.val : ℝ) / (n : ℝ) ≤ 1 := by
          have h₃ : j.val < n := j.is_lt
          have h₄ : (j.val : ℝ) ≤ (n : ℝ) := by exact_mod_cast h₃.le
          have h₅ : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
          exact (div_le_one h₅).mpr h₄
        exact ⟨h₁, h₂⟩⟩) =
    my_desc_map X 𝒰 hcover hfinite_intersections s
      (H.eval ⟨((j.val : ℝ) + 1) / (n : ℝ), by
        have h₁ : 0 ≤ ((j.val : ℝ) + 1) / (n : ℝ) := by positivity
        have h₂ : ((j.val : ℝ) + 1) / (n : ℝ) ≤ 1 := by
          have h₃ : j.val < n := j.is_lt
          have h₄ : (j.val : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr h₃
          have h₅ : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
          exact (div_le_one h₅).mpr h₄
        exact ⟨h₁, h₂⟩⟩) := by
  classical
  -- Grid points in path direction
  let t_i (i : Fin (n + 1)) : I := ⟨(i.val : ℝ) / (n : ℝ), by
    have h₁ : 0 ≤ (i.val : ℝ) / (n : ℝ) := by positivity
    have h₂ : (i.val : ℝ) / (n : ℝ) ≤ 1 := by
      have h₃ : i.val ≤ n := Nat.lt_succ_iff.mp i.is_lt
      have h₄ : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
      exact (div_le_one h₄).mpr (by exact_mod_cast h₃)
    exact ⟨h₁, h₂⟩⟩
  -- Grid points in homotopy direction (row j and row j+1)
  let s_j : I := ⟨(j.val : ℝ) / (n : ℝ), by
    have h₁ : 0 ≤ (j.val : ℝ) / (n : ℝ) := by positivity
    have h₂ : (j.val : ℝ) / (n : ℝ) ≤ 1 := by
      have h₃ : j.val < n := j.is_lt
      have h₄ : (j.val : ℝ) ≤ (n : ℝ) := by exact_mod_cast h₃.le
      have h₅ : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
      exact (div_le_one h₅).mpr h₄
    exact ⟨h₁, h₂⟩⟩
  let s_j1 : I := ⟨((j.val : ℝ) + 1) / (n : ℝ), by
    have h₁ : 0 ≤ ((j.val : ℝ) + 1) / (n : ℝ) := by positivity
    have h₂ : ((j.val : ℝ) + 1) / (n : ℝ) ≤ 1 := by
      have h₃ : j.val < n := j.is_lt
      have h₄ : (j.val : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr h₃
      have h₅ : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
      exact (div_le_one h₅).mpr h₄
    exact ⟨h₁, h₂⟩⟩
  -- Covering sets for each column (in row j)
  let covers (i : Fin n) : Opens X := pcH.covers j i
  have hcover_mem (i : Fin n) : covers i ∈ 𝒰 := pcH.hcover_mem j i
  -- Bottom row paths (row j)
  let γ_bottom (i : Fin n) : Path (H.eval s_j (t_i (Fin.castSucc i))) (H.eval s_j (t_i (Fin.succ i))) :=
    (H.eval s_j).subpath (t_i (Fin.castSucc i)) (t_i (Fin.succ i))
  -- Top row paths (row j+1)
  let γ_top (i : Fin n) : Path (H.eval s_j1 (t_i (Fin.castSucc i))) (H.eval s_j1 (t_i (Fin.succ i))) :=
    (H.eval s_j1).subpath (t_i (Fin.castSucc i)) (t_i (Fin.succ i))
  -- Strict monotonicity of t_i
  have h_ti_strict_mono : StrictMono t_i := by
    intro i k h
    apply Subtype.mk_lt_mk.mpr
    have h₅ : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
    have h₆ : (i.val : ℝ) < (k.val : ℝ) := by exact_mod_cast h
    gcongr
  have h_ti_le (i : Fin n) : t_i (Fin.castSucc i) ≤ t_i (Fin.succ i) :=
    le_of_lt (h_ti_strict_mono (by simp [Fin.castSucc_lt_succ]))
  -- Bottom range: γ_bottom i is contained in covers i
  have h_bottom_range (i : Fin n) : Set.range (γ_bottom i) ⊆ (covers i : Set X) := by
    have h_lt : t_i (Fin.castSucc i) < t_i (Fin.succ i) := h_ti_strict_mono (by simp [Fin.castSucc_lt_succ])
    have h_range_eq : Set.range (γ_bottom i) = (H.eval s_j) '' Set.Icc (t_i (Fin.castSucc i)) (t_i (Fin.succ i)) := by
      rw [Path.range_subpath (H.eval s_j) (t_i (Fin.castSucc i)) (t_i (Fin.succ i))]
      <;> rw [Set.uIcc_of_le (le_of_lt h_lt)]
    rw [h_range_eq]
    intro z hz
    rcases hz with ⟨t, ht, rfl⟩
    have h1 : (j : ℝ) / (n : ℝ) ≤ (s_j : ℝ) := by rfl
    have h2 : (s_j : ℝ) ≤ ((j : ℝ) + 1) / (n : ℝ) := by
      have h_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
      have h_j_le : (j : ℝ) ≤ (j : ℝ) + 1 := by linarith
      exact div_le_div_of_nonneg_right h_j_le (by positivity)
    have h3 : (i : ℝ) / (n : ℝ) ≤ (t : ℝ) := by
      simpa [t_i] using (show (t_i (Fin.castSucc i) : ℝ) ≤ (t : ℝ) from ht.1)
    have h4 : (t : ℝ) ≤ ((i : ℝ) + 1) / (n : ℝ) := by
      simpa [t_i] using (show (t : ℝ) ≤ (t_i (Fin.succ i) : ℝ) from ht.2)
    exact pcH.h_rectangles j i (s_j, t) h1 h2 h3 h4
  -- Top range: γ_top i is contained in covers i
  have h_top_range (i : Fin n) : Set.range (γ_top i) ⊆ (covers i : Set X) := by
    have h_lt : t_i (Fin.castSucc i) < t_i (Fin.succ i) := h_ti_strict_mono (by simp [Fin.castSucc_lt_succ])
    have h_range_eq : Set.range (γ_top i) = (H.eval s_j1) '' Set.Icc (t_i (Fin.castSucc i)) (t_i (Fin.succ i)) := by
      rw [Path.range_subpath (H.eval s_j1) (t_i (Fin.castSucc i)) (t_i (Fin.succ i))]
      <;> rw [Set.uIcc_of_le (le_of_lt h_lt)]
    rw [h_range_eq]
    intro z hz
    rcases hz with ⟨t, ht, rfl⟩
    have h1 : (j : ℝ) / (n : ℝ) ≤ (s_j1 : ℝ) := by
      have h_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
      have h_j_le : (j : ℝ) ≤ (j : ℝ) + 1 := by linarith
      exact div_le_div_of_nonneg_right h_j_le (by positivity)
    have h2 : (s_j1 : ℝ) ≤ ((j : ℝ) + 1) / (n : ℝ) := by rfl
    have h3 : (i : ℝ) / (n : ℝ) ≤ (t : ℝ) := by
      simpa [t_i] using (show (t_i (Fin.castSucc i) : ℝ) ≤ (t : ℝ) from ht.1)
    have h4 : (t : ℝ) ≤ ((i : ℝ) + 1) / (n : ℝ) := by
      simpa [t_i] using (show (t : ℝ) ≤ (t_i (Fin.succ i) : ℝ) from ht.2)
    exact pcH.h_rectangles j i (s_j1, t) h1 h2 h3 h4
  -- Vertical paths at each grid point
  let s_lerp (t : I) : I := ⟨(s_j : ℝ) + (t : ℝ) * ((s_j1 : ℝ) - (s_j : ℝ)), by
    have h_sj_nonneg : 0 ≤ (s_j : ℝ) := s_j.prop.1
    have h_sj_le : (s_j : ℝ) ≤ (s_j1 : ℝ) := by
      have h_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
      have h_j_le : (j : ℝ) ≤ (j : ℝ) + 1 := by linarith
      exact div_le_div_of_nonneg_right h_j_le (by positivity)
    have h_diff_nonneg : 0 ≤ (s_j1 : ℝ) - (s_j : ℝ) := by linarith
    have h_t_nonneg : 0 ≤ (t : ℝ) := t.prop.1
    have h1 : 0 ≤ (s_j : ℝ) + (t : ℝ) * ((s_j1 : ℝ) - (s_j : ℝ)) := by
      have h : 0 ≤ (t : ℝ) * ((s_j1 : ℝ) - (s_j : ℝ)) := mul_nonneg h_t_nonneg h_diff_nonneg
      linarith
    have h_t_le_one : (t : ℝ) ≤ 1 := t.prop.2
    have h_sj1_le_one : (s_j1 : ℝ) ≤ 1 := s_j1.prop.2
    have h2 : (s_j : ℝ) + (t : ℝ) * ((s_j1 : ℝ) - (s_j : ℝ)) ≤ 1 := by
      have h3 : (t : ℝ) * ((s_j1 : ℝ) - (s_j : ℝ)) ≤ (s_j1 : ℝ) - (s_j : ℝ) := by
        exact mul_le_of_le_one_left h_diff_nonneg h_t_le_one
      linarith
    exact ⟨h1, h2⟩⟩
  have h_s_lerp0 : s_lerp 0 = s_j := by
    apply Subtype.ext
    simp [s_lerp] <;> ring
  have h_s_lerp1 : s_lerp 1 = s_j1 := by
    apply Subtype.ext
    simp [s_lerp] <;> ring
  let γ_vert (k : Fin (n + 1)) : Path (H.eval s_j (t_i k)) (H.eval s_j1 (t_i k)) :=
    let f : C(I, X) := ⟨fun t : I => H.eval (s_lerp t) (t_i k), by continuity⟩
    have h_src : f 0 = H.eval s_j (t_i k) := by
      have h : f 0 = H.eval (s_lerp 0) (t_i k) := by rfl
      rw [h, h_s_lerp0]
    have h_tgt : f 1 = H.eval s_j1 (t_i k) := by
      have h : f 1 = H.eval (s_lerp 1) (t_i k) := by rfl
      rw [h, h_s_lerp1]
    ⟨f, h_src, h_tgt⟩
  -- Helper: s_lerp t is always between s_j and s_j1
  have h_s_lerp_between (t : I) : (s_j : ℝ) ≤ (s_lerp t : ℝ) ∧ (s_lerp t : ℝ) ≤ (s_j1 : ℝ) := by
    have h_sj_le : (s_j : ℝ) ≤ (s_j1 : ℝ) := by
      have h_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
      have h_j_le : (j : ℝ) ≤ (j : ℝ) + 1 := by linarith
      exact div_le_div_of_nonneg_right h_j_le (by positivity)
    have h_diff_nonneg : 0 ≤ (s_j1 : ℝ) - (s_j : ℝ) := by linarith
    have h_t_nonneg : 0 ≤ (t : ℝ) := t.prop.1
    have h_t_le_one : (t : ℝ) ≤ 1 := t.prop.2
    constructor
    · -- s_j ≤ s_lerp t
      have h : 0 ≤ (t : ℝ) * ((s_j1 : ℝ) - (s_j : ℝ)) := mul_nonneg h_t_nonneg h_diff_nonneg
      linarith
    · -- s_lerp t ≤ s_j1
      have h : (t : ℝ) * ((s_j1 : ℝ) - (s_j : ℝ)) ≤ (s_j1 : ℝ) - (s_j : ℝ) :=
        mul_le_of_le_one_left h_diff_nonneg h_t_le_one
      linarith
  -- Vertical range: γ_vert (Fin.castSucc i) is contained in covers i
  have h_vert_range (i : Fin n) : Set.range (γ_vert (Fin.castSucc i)) ⊆ (covers i : Set X) := by
    intro z hz
    rcases hz with ⟨t, rfl⟩
    have h_between := h_s_lerp_between t
    have h1 : (j : ℝ) / (n : ℝ) ≤ (s_lerp t : ℝ) := by
      have h_eq : (s_j : ℝ) = (j : ℝ) / (n : ℝ) := by rfl
      rw [h_eq] at h_between
      exact h_between.1
    have h2 : (s_lerp t : ℝ) ≤ ((j : ℝ) + 1) / (n : ℝ) := by
      have h_eq : (s_j1 : ℝ) = ((j : ℝ) + 1) / (n : ℝ) := by rfl
      rw [h_eq] at h_between
      exact h_between.2
    have h3 : (i : ℝ) / (n : ℝ) ≤ (t_i (Fin.castSucc i) : ℝ) := by rfl
    have h4 : (t_i (Fin.castSucc i) : ℝ) ≤ ((i : ℝ) + 1) / (n : ℝ) := by
      have h_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
      have h_i_le : (i : ℝ) ≤ (i : ℝ) + 1 := by linarith
      exact div_le_div_of_nonneg_right h_i_le (by positivity)
    exact pcH.h_rectangles j i (s_lerp t, t_i (Fin.castSucc i)) h1 h2 h3 h4
  -- Right edge range: γ_vert (Fin.succ i) is contained in covers i
  have h_right_range (i : Fin n) : Set.range (γ_vert (Fin.succ i)) ⊆ (covers i : Set X) := by
    intro z hz
    rcases hz with ⟨t, rfl⟩
    have h_between := h_s_lerp_between t
    have h1 : (j : ℝ) / (n : ℝ) ≤ (s_lerp t : ℝ) := by
      have h_eq : (s_j : ℝ) = (j : ℝ) / (n : ℝ) := by rfl
      rw [h_eq] at h_between
      exact h_between.1
    have h2 : (s_lerp t : ℝ) ≤ ((j : ℝ) + 1) / (n : ℝ) := by
      have h_eq : (s_j1 : ℝ) = ((j : ℝ) + 1) / (n : ℝ) := by rfl
      rw [h_eq] at h_between
      exact h_between.2
    have h3 : (i : ℝ) / (n : ℝ) ≤ (t_i (Fin.succ i) : ℝ) := by
      have h_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
      have h_i_val : (i : ℝ) ≤ (i : ℝ) + 1 := by linarith
      have h : (i : ℝ) / (n : ℝ) ≤ ((i : ℝ) + 1) / (n : ℝ) := by
        exact div_le_div_of_nonneg_right h_i_val (by positivity)
      have h_eq : (t_i (Fin.succ i) : ℝ) = ((i : ℝ) + 1) / (n : ℝ) := by
        simp [t_i, Fin.val_succ] <;> ring
      rw [h_eq]
      exact h
    have h4 : (t_i (Fin.succ i) : ℝ) ≤ ((i : ℝ) + 1) / (n : ℝ) := by
      have h_eq : (t_i (Fin.succ i) : ℝ) = ((i : ℝ) + 1) / (n : ℝ) := by
        simp [t_i, Fin.val_succ] <;> ring
      rw [h_eq]
    exact pcH.h_rectangles j i (s_lerp t, t_i (Fin.succ i)) h1 h2 h3 h4
  -- Horizontal interpolation for each column
  let t_lerp (i : Fin n) (t : I) : I := ⟨(t_i (Fin.castSucc i) : ℝ) + (t : ℝ) * ((t_i (Fin.succ i) : ℝ) - (t_i (Fin.castSucc i) : ℝ)), by
    have h_ti_le : (t_i (Fin.castSucc i) : ℝ) ≤ (t_i (Fin.succ i) : ℝ) :=
      le_of_lt (h_ti_strict_mono (by simp [Fin.castSucc_lt_succ]))
    have h_diff_nonneg : 0 ≤ (t_i (Fin.succ i) : ℝ) - (t_i (Fin.castSucc i) : ℝ) := by linarith
    have h_t_nonneg : 0 ≤ (t : ℝ) := t.prop.1
    have h1 : 0 ≤ (t_i (Fin.castSucc i) : ℝ) + (t : ℝ) * ((t_i (Fin.succ i) : ℝ) - (t_i (Fin.castSucc i) : ℝ)) := by
      have h_ti_nonneg : 0 ≤ (t_i (Fin.castSucc i) : ℝ) := (t_i (Fin.castSucc i)).prop.1
      have h : 0 ≤ (t : ℝ) * ((t_i (Fin.succ i) : ℝ) - (t_i (Fin.castSucc i) : ℝ)) := mul_nonneg h_t_nonneg h_diff_nonneg
      linarith
    have h_t_le_one : (t : ℝ) ≤ 1 := t.prop.2
    have h_ti1_le_one : (t_i (Fin.succ i) : ℝ) ≤ 1 := (t_i (Fin.succ i)).prop.2
    have h2 : (t_i (Fin.castSucc i) : ℝ) + (t : ℝ) * ((t_i (Fin.succ i) : ℝ) - (t_i (Fin.castSucc i) : ℝ)) ≤ 1 := by
      have h3 : (t : ℝ) * ((t_i (Fin.succ i) : ℝ) - (t_i (Fin.castSucc i) : ℝ)) ≤ (t_i (Fin.succ i) : ℝ) - (t_i (Fin.castSucc i) : ℝ) :=
        mul_le_of_le_one_left h_diff_nonneg h_t_le_one
      linarith
    exact ⟨h1, h2⟩⟩
  have h_t_lerp0 (i : Fin n) : t_lerp i 0 = t_i (Fin.castSucc i) := by
    apply Subtype.ext
    simp [t_lerp] <;> ring
  have h_t_lerp1 (i : Fin n) : t_lerp i 1 = t_i (Fin.succ i) := by
    apply Subtype.ext
    simp [t_lerp] <;> ring
  -- Helper: t_lerp i t is always between t_i (Fin.castSucc i) and t_i (Fin.succ i)
  have h_t_lerp_between (i : Fin n) (t : I) :
      (t_i (Fin.castSucc i) : ℝ) ≤ (t_lerp i t : ℝ) ∧ (t_lerp i t : ℝ) ≤ (t_i (Fin.succ i) : ℝ) := by
    have h_ti_le : (t_i (Fin.castSucc i) : ℝ) ≤ (t_i (Fin.succ i) : ℝ) :=
      le_of_lt (h_ti_strict_mono (by simp [Fin.castSucc_lt_succ]))
    have h_diff_nonneg : 0 ≤ (t_i (Fin.succ i) : ℝ) - (t_i (Fin.castSucc i) : ℝ) := by linarith
    have h_t_nonneg : 0 ≤ (t : ℝ) := t.prop.1
    have h_t_le_one : (t : ℝ) ≤ 1 := t.prop.2
    constructor
    · have h : 0 ≤ (t : ℝ) * ((t_i (Fin.succ i) : ℝ) - (t_i (Fin.castSucc i) : ℝ)) := mul_nonneg h_t_nonneg h_diff_nonneg
      linarith
    · have h : (t : ℝ) * ((t_i (Fin.succ i) : ℝ) - (t_i (Fin.castSucc i) : ℝ)) ≤ (t_i (Fin.succ i) : ℝ) - (t_i (Fin.castSucc i) : ℝ) :=
        mul_le_of_le_one_left h_diff_nonneg h_t_le_one
      linarith
  -- Rectangle homotopy for each column using RectangleHomotopy
  have h_rect_both (i : Fin n) :
    ∃ (H_rect : Path.Homotopy ((γ_bottom i).trans (γ_vert (Fin.succ i)))
        ((γ_vert (Fin.castSucc i)).trans (γ_top i))),
      ∀ (p : I × I), H_rect p ∈ (covers i : Set X) := by
    let G : C(I × I, X) := ⟨fun p : I × I => H.eval (s_lerp p.1) (t_lerp i p.2), by continuity⟩
    have hG00 : G (0, 0) = H.eval s_j (t_i (Fin.castSucc i)) := by
      simp [G, h_s_lerp0, h_t_lerp0 i] <;> rfl
    have hG01 : G (0, 1) = H.eval s_j (t_i (Fin.succ i)) := by
      simp [G, h_s_lerp0, h_t_lerp1 i] <;> rfl
    have hG10 : G (1, 0) = H.eval s_j1 (t_i (Fin.castSucc i)) := by
      simp [G, h_s_lerp1, h_t_lerp0 i] <;> rfl
    have hG11 : G (1, 1) = H.eval s_j1 (t_i (Fin.succ i)) := by
      simp [G, h_s_lerp1, h_t_lerp1 i] <;> rfl
    let gb : Path (G (0, 0)) (G (0, 1)) := (γ_bottom i).cast hG00 hG01
    let gr : Path (G (0, 1)) (G (1, 1)) := (γ_vert (Fin.succ i)).cast hG01 hG11
    let gl : Path (G (0, 0)) (G (1, 0)) := (γ_vert (Fin.castSucc i)).cast hG00 hG10
    let gt : Path (G (1, 0)) (G (1, 1)) := (γ_top i).cast hG10 hG11
    have hgb : ∀ (t : I), gb t = G (0, t) := by
      intro t
      have h1 : gb t = γ_bottom i t := by rfl
      rw [h1]
      have h2 : γ_bottom i t = H.eval s_j (Set.Icc.convexComb (t_i (Fin.castSucc i)) (t_i (Fin.succ i)) t) := by rfl
      rw [h2]
      have h_eq : Set.Icc.convexComb (t_i (Fin.castSucc i)) (t_i (Fin.succ i)) t = t_lerp i t := by
        apply Subtype.ext
        simp [Set.Icc.coe_convexComb, t_lerp] <;> ring
      rw [h_eq]
      have h3 : G (0, t) = H.eval (s_lerp 0) (t_lerp i t) := by rfl
      rw [h3, h_s_lerp0] <;> rfl
    have hgr : ∀ (s : I), gr s = G (s, 1) := by
      intro s
      have h1 : gr s = γ_vert (Fin.succ i) s := by rfl
      rw [h1]
      have h2 : γ_vert (Fin.succ i) s = H.eval (s_lerp s) (t_i (Fin.succ i)) := by rfl
      rw [h2]
      have h3 : G (s, 1) = H.eval (s_lerp s) (t_lerp i 1) := by rfl
      rw [h3, h_t_lerp1 i] <;> rfl
    have hgl : ∀ (s : I), gl s = G (s, 0) := by
      intro s
      have h1 : gl s = γ_vert (Fin.castSucc i) s := by rfl
      rw [h1]
      have h2 : γ_vert (Fin.castSucc i) s = H.eval (s_lerp s) (t_i (Fin.castSucc i)) := by rfl
      rw [h2]
      have h3 : G (s, 0) = H.eval (s_lerp s) (t_lerp i 0) := by rfl
      rw [h3, h_t_lerp0 i] <;> rfl
    have hgt : ∀ (t : I), gt t = G (1, t) := by
      intro t
      have h1 : gt t = γ_top i t := by rfl
      rw [h1]
      have h2 : γ_top i t = H.eval s_j1 (Set.Icc.convexComb (t_i (Fin.castSucc i)) (t_i (Fin.succ i)) t) := by rfl
      rw [h2]
      have h_eq : Set.Icc.convexComb (t_i (Fin.castSucc i)) (t_i (Fin.succ i)) t = t_lerp i t := by
        apply Subtype.ext
        simp [Set.Icc.coe_convexComb, t_lerp] <;> ring
      rw [h_eq]
      have h3 : G (1, t) = H.eval (s_lerp 1) (t_lerp i t) := by rfl
      rw [h3, h_s_lerp1] <;> rfl
    have hG_in : ∀ (p : I × I), G p ∈ (covers i : Set X) := by
      intro p
      have h_s_between := h_s_lerp_between p.1
      have h_t_between := h_t_lerp_between i p.2
      have h1 : (j : ℝ) / (n : ℝ) ≤ (s_lerp p.1 : ℝ) := by
        have h_eq : (s_j : ℝ) = (j : ℝ) / (n : ℝ) := by rfl
        rw [h_eq] at h_s_between; exact h_s_between.1
      have h2 : (s_lerp p.1 : ℝ) ≤ ((j : ℝ) + 1) / (n : ℝ) := by
        have h_eq : (s_j1 : ℝ) = ((j : ℝ) + 1) / (n : ℝ) := by rfl
        rw [h_eq] at h_s_between; exact h_s_between.2
      have h3 : (i : ℝ) / (n : ℝ) ≤ (t_lerp i p.2 : ℝ) := by
        have h_eq : (t_i (Fin.castSucc i) : ℝ) = (i : ℝ) / (n : ℝ) := by
          simp [t_i, Fin.castSucc] <;> rfl
        rw [h_eq] at h_t_between; exact h_t_between.1
      have h4 : (t_lerp i p.2 : ℝ) ≤ ((i : ℝ) + 1) / (n : ℝ) := by
        have h_eq : (t_i (Fin.succ i) : ℝ) = ((i : ℝ) + 1) / (n : ℝ) := by
          simp [t_i, Fin.val_succ] <;> ring
        rw [h_eq] at h_t_between; exact h_t_between.2
      exact pcH.h_rectangles j i (s_lerp p.1, t_lerp i p.2) h1 h2 h3 h4
    have h_main := RectangleHomotopy.rectangle_boundary_homotopy_edges G gb gr gl gt hgb hgr hgl hgt (covers i : Set X) hG_in
    rcases h_main with ⟨H_rect, hH_rect_range⟩
    let H_rect_cast : Path.Homotopy
        ((gb.trans gr).cast hG00.symm hG11.symm)
        ((gl.trans gt).cast hG00.symm hG11.symm) :=
      H_rect.pathCast hG00.symm hG11.symm
    have hH_rect_cast_range : ∀ (p : I × I), H_rect_cast p ∈ (covers i : Set X) := by
      intro p
      have h_eq : H_rect_cast p = H_rect p := by rfl
      rw [h_eq]
      exact hH_rect_range p
    have h_mid : H.eval s_j (t_i (Fin.succ i)) = G (0, 1) := hG01.symm
    have h_mid2 : H.eval s_j1 (t_i (Fin.castSucc i)) = G (1, 0) := hG10.symm
    have h_eq0 : (gb.trans gr).cast hG00.symm hG11.symm = (γ_bottom i).trans (γ_vert (Fin.succ i)) := by
      rw [Path.cast_trans gb gr hG00.symm h_mid hG11.symm]
      have hgb2 : gb.cast hG00.symm h_mid = γ_bottom i := by
        apply Path.ext
        funext t
        have h : (gb.cast hG00.symm h_mid) t = gb t := by rfl
        rw [h] <;> rfl
      have hgr2 : gr.cast h_mid hG11.symm = γ_vert (Fin.succ i) := by
        apply Path.ext
        funext t
        have h : (gr.cast h_mid hG11.symm) t = gr t := by rfl
        rw [h] <;> rfl
      rw [hgb2, hgr2]
    have h_eq1 : (gl.trans gt).cast hG00.symm hG11.symm = (γ_vert (Fin.castSucc i)).trans (γ_top i) := by
      rw [Path.cast_trans gl gt hG00.symm h_mid2 hG11.symm]
      have hgl2 : gl.cast hG00.symm h_mid2 = γ_vert (Fin.castSucc i) := by
        apply Path.ext
        funext t
        have h : (gl.cast hG00.symm h_mid2) t = gl t := by rfl
        rw [h] <;> rfl
      have hgt2 : gt.cast h_mid2 hG11.symm = γ_top i := by
        apply Path.ext
        funext t
        have h : (gt.cast h_mid2 hG11.symm) t = gt t := by rfl
        rw [h] <;> rfl
      rw [hgl2, hgt2]
    let H_rect' : Path.Homotopy ((γ_bottom i).trans (γ_vert (Fin.succ i)))
        ((γ_vert (Fin.castSucc i)).trans (γ_top i)) :=
      Path.Homotopy.cast H_rect_cast h_eq0 h_eq1
    have hH_rect'_range : ∀ (p : I × I), H_rect' p ∈ (covers i : Set X) := by
      intro p
      have h_eq : H_rect' p = H_rect_cast p := by rfl
      rw [h_eq]
      exact hH_rect_cast_range p
    exact ⟨H_rect', hH_rect'_range⟩
  let h_rect_homotopy (i : Fin n) :
    Path.Homotopy ((γ_bottom i).trans (γ_vert (Fin.succ i)))
      ((γ_vert (Fin.castSucc i)).trans (γ_top i)) :=
    (h_rect_both i).choose
  have h_rect_homotopy_range (i : Fin n) :
    ∀ (p : I × I), (h_rect_homotopy i) p ∈ (covers i : Set X) := by
    exact (h_rect_both i).choose_spec
  -- Apply rectangle_identity_clean to each column
  have h_rect_comm (i : Fin n) :
    single_covered_map X 𝒰 hcover hfinite_intersections s (γ_bottom i) (covers i) (hcover_mem i) (h_bottom_range i) ≫
    single_covered_map X 𝒰 hcover hfinite_intersections s (γ_vert (Fin.succ i)) (covers i) (hcover_mem i) (h_right_range i) =
    single_covered_map X 𝒰 hcover hfinite_intersections s (γ_vert (Fin.castSucc i)) (covers i) (hcover_mem i) (h_vert_range i) ≫
    single_covered_map X 𝒰 hcover hfinite_intersections s (γ_top i) (covers i) (hcover_mem i) (h_top_range i) :=
    rectangle_identity_clean X 𝒰 hcover hfinite_intersections s (covers i) (hcover_mem i)
      (γ_bottom i) (h_bottom_range i)
      (γ_vert (Fin.succ i)) (h_right_range i)
      (γ_vert (Fin.castSucc i)) (h_vert_range i)
      (γ_top i) (h_top_range i)
      (h_rect_homotopy i) (h_rect_homotopy_range i)
  -- Objects in the cocone point for bottom and top rows
  let p_objs (i : Fin (n + 1)) : s.pt :=
    desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (H.eval s_j (t_i i)))
  let q_objs (i : Fin (n + 1)) : s.pt :=
    desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk (H.eval s_j1 (t_i i)))
  -- Bottom and top morphisms (single_covered_map for each segment)
  let f_bottom (i : Fin n) : p_objs (Fin.castSucc i) ⟶ p_objs (Fin.succ i) :=
    single_covered_map X 𝒰 hcover hfinite_intersections s (γ_bottom i) (covers i) (hcover_mem i) (h_bottom_range i)
  let f_top (i : Fin n) : q_objs (Fin.castSucc i) ⟶ q_objs (Fin.succ i) :=
    single_covered_map X 𝒰 hcover hfinite_intersections s (γ_top i) (covers i) (hcover_mem i) (h_top_range i)
  -- Vertical morphisms
  let f_vert (k : Fin (n + 1)) : p_objs k ⟶ q_objs k :=
    my_desc_map X 𝒰 hcover hfinite_intersections s (γ_vert k)
  -- Commuting squares for the chain lemma
  have h_square (i : Fin n) :
    f_bottom i ≫ f_vert (Fin.succ i) = f_vert (Fin.castSucc i) ≫ f_top i := by
    let f_vert_left := single_covered_map X 𝒰 hcover hfinite_intersections s (γ_vert (Fin.castSucc i)) (covers i) (hcover_mem i) (h_vert_range i)
    let f_vert_right := single_covered_map X 𝒰 hcover hfinite_intersections s (γ_vert (Fin.succ i)) (covers i) (hcover_mem i) (h_right_range i)
    have h_main : f_bottom i ≫ f_vert_right = f_vert_left ≫ f_top i := h_rect_comm i
    have h1 : f_vert (Fin.castSucc i) = f_vert_left := by
      exact?
    have h2 : f_vert (Fin.succ i) = f_vert_right := by
      exact?
    rw [h2, h1]
    exact h_main
  -- Apply the chain lemma
  have h_chain : comp_list n p_objs f_bottom ≫ f_vert (Fin.last n) =
      f_vert 0 ≫ comp_list n q_objs f_top :=
    comp_list_chain_commute p_objs q_objs f_bottom f_top f_vert h_square
  -- The first vertical edge is a constant path at x
  -- The last vertical edge is a constant path at y
  -- So f_vert 0 and f_vert (Fin.last n) are "identities" (eqToHom of the endpoint equality)
  -- Connect to my_desc_map via the universal property and conclude
  let S_bot : Finset I := Finset.image t_i Finset.univ
  have h_ti0 : t_i 0 = (0 : I) := by
    apply Subtype.ext
    have h : (t_i 0).val = 0 := by
      dsimp only [t_i]
      simpa using zero_div (n : ℝ)
    have h' : ((0 : I) : ℝ) = 0 := by norm_cast
    rw [h']
    exact h
  have h_ti1 : t_i (Fin.last n) = (1 : I) := by
    apply Subtype.ext
    have h_last_val : (Fin.last n).val = n := by simp [Fin.last] <;> omega
    have h_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
    have h : (t_i (Fin.last n)).val = 1 := by
      dsimp only [t_i]
      rw [h_last_val]
      have h_pos' : (n : ℝ) ≠ 0 := by exact_mod_cast hn_pos.ne'
      exact div_self h_pos'
    have h' : ((1 : I) : ℝ) = 1 := by norm_cast
    rw [h']
    exact h
  have h0_in_S_bot : (0 : I) ∈ S_bot := by
    dsimp only [S_bot]
    rw [←h_ti0]
    exact Finset.mem_image.mpr ⟨0, by simp, rfl⟩
  have h1_in_S_bot : (1 : I) ∈ S_bot := by
    dsimp only [S_bot]
    rw [←h_ti1]
    exact Finset.mem_image.mpr ⟨Fin.last n, by simp, rfl⟩
  have h_range_bot' : ∀ (i : Fin n) (t : I), t_i (Fin.castSucc i) ≤ t → t ≤ t_i (Fin.succ i) → (H.eval s_j) t ∈ (covers i : Set X) := by
    intro i t h1 h2
    have h_in_range : (H.eval s_j) t ∈ Set.range (γ_bottom i) := by
      have h_lt : t_i (Fin.castSucc i) < t_i (Fin.succ i) := h_ti_strict_mono (by simp [Fin.castSucc_lt_succ])
      have h_range_eq : Set.range (γ_bottom i) = (H.eval s_j) '' Set.Icc (t_i (Fin.castSucc i)) (t_i (Fin.succ i)) := by
        rw [Path.range_subpath (H.eval s_j) (t_i (Fin.castSucc i)) (t_i (Fin.succ i))]
        <;> rw [Set.uIcc_of_le (le_of_lt h_lt)]
      rw [h_range_eq]
      exact ⟨t, ⟨h1, h2⟩, rfl⟩
    exact h_bottom_range i h_in_range
  have hS_bot : IsAdaptedSubdivision 𝒰 (H.eval s_j) S_bot := by
    constructor
    · exact h0_in_S_bot
    · constructor
      · exact h1_in_S_bot
      · intro s₁ s₂ hs₁ hs₂ h_lt h_no_between
        have h_exists : ∃ (i : Fin n), s₁ = t_i (Fin.castSucc i) ∧ s₂ = t_i (Fin.succ i) := by
          rcases Finset.mem_image.mp hs₁ with ⟨k, _, rfl⟩
          rcases Finset.mem_image.mp hs₂ with ⟨l, _, rfl⟩
          have h_k_lt_l : k < l := by
            by_contra h
            have h' : l ≤ k := le_of_not_gt h
            have h'' : t_i l ≤ t_i k := h_ti_strict_mono.monotone h'
            exact lt_irrefl _ (lt_of_le_of_lt h'' h_lt)
          have h_l_val_succ : l.val = k.val + 1 := by
            by_contra h
            have h_k_lt_l_val : k.val < l.val := by exact_mod_cast h_k_lt_l
            have h_succ_lt : k.val + 1 < l.val := by omega
            have h_m_lt_n1 : k.val + 1 < n + 1 := by omega
            let m : Fin (n + 1) := ⟨k.val + 1, h_m_lt_n1⟩
            have h_k_lt_m : k < m := by
              apply Fin.lt_iff_val_lt_val.mpr
              simp [m] <;> omega
            have h_m_lt_l : m < l := by
              apply Fin.lt_iff_val_lt_val.mpr
              simp [m, h_succ_lt] <;> omega
            have h_between1 : t_i k < t_i m := h_ti_strict_mono h_k_lt_m
            have h_between2 : t_i m < t_i l := h_ti_strict_mono h_m_lt_l
            have h_mem : t_i m ∈ Finset.image t_i Finset.univ := by
              exact Finset.mem_image.mpr ⟨m, Finset.mem_univ _, rfl⟩
            exact h_no_between (t_i m) h_mem h_between1 h_between2
          have h_k_lt_n : k.val < n := by omega
          let i : Fin n := ⟨k.val, h_k_lt_n⟩
          have h_k_eq : k = Fin.castSucc i := by
            apply Fin.ext
            simp [i]
          have h_l_eq : l = Fin.succ i := by
            apply Fin.ext
            simp [i, h_l_val_succ, Fin.val_succ]
            <;> omega
          refine' ⟨i, _⟩
          constructor
          · rw [h_k_eq]
          · rw [h_l_eq]
        rcases h_exists with ⟨i, rfl, rfl⟩
        refine' ⟨covers i, hcover_mem i, _⟩
        exact h_range_bot' i
  have h_desc_bot : my_desc_map X 𝒰 hcover hfinite_intersections s (H.eval s_j) =
      my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS_bot :=
    my_desc_map_well_defined X 𝒰 hcover hfinite_intersections s (H.eval s_j)
      (Classical.choose (exists_adapted_subdivision X 𝒰 hcover (H.eval s_j))) S_bot
      (Classical.choose_spec (exists_adapted_subdivision X 𝒰 hcover (H.eval s_j))) hS_bot
  have h_univ_bot : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS_bot =
      my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS_bot n t_i h_ti_strict_mono rfl covers hcover_mem h_range_bot' := by
    exact my_map_from_adapted_subdivision_universal X 𝒰 hcover hfinite_intersections s hS_bot t_i h_ti_strict_mono rfl covers hcover_mem h_range_bot'
  -- Step 1: Prove γ_vert 0 is constant (at x) and γ_vert (Fin.last n) is constant (at y)
  have h_eval0 : ∀ (s : I), H.eval s 0 = x := by
    intro s
    exact (H.eval s).source
  have h_eval1 : ∀ (s : I), H.eval s 1 = y := by
    intro s
    exact (H.eval s).target
  have h_vert0_const : ∀ (t : I), (γ_vert 0) t = H.eval s_j (t_i 0) := by
    intro t
    have h1 : (γ_vert 0) t = H.eval (s_lerp t) (t_i 0) := by rfl
    have h2 : H.eval (s_lerp t) (t_i 0) = x := by
      rw [h_ti0]
      exact h_eval0 (s_lerp t)
    have h3 : H.eval s_j (t_i 0) = x := by
      rw [h_ti0]
      exact h_eval0 s_j
    rw [h1, h2, h3]
  have h_vert_last_const : ∀ (t : I), (γ_vert (Fin.last n)) t = H.eval s_j (t_i (Fin.last n)) := by
    intro t
    have h1 : (γ_vert (Fin.last n)) t = H.eval (s_lerp t) (t_i (Fin.last n)) := by rfl
    have h2 : H.eval (s_lerp t) (t_i (Fin.last n)) = y := by
      rw [h_ti1]
      exact h_eval1 (s_lerp t)
    have h3 : H.eval s_j (t_i (Fin.last n)) = y := by
      rw [h_ti1]
      exact h_eval1 s_j
    rw [h1, h2, h3]
  -- Step 2: Prove f_vert 0 and f_vert (Fin.last n) are eqToHom
  have h_eq0 : p_objs 0 = q_objs 0 := by
    dsimp only [p_objs, q_objs]
    have h1 : H.eval s_j (t_i 0) = H.eval s_j1 (t_i 0) := by
      rw [h_ti0]
      <;> exact (h_eval0 s_j).trans (h_eval0 s_j1).symm
    rw [h1]
  have h_eq_last : p_objs (Fin.last n) = q_objs (Fin.last n) := by
    dsimp only [p_objs, q_objs]
    have h1 : H.eval s_j (t_i (Fin.last n)) = H.eval s_j1 (t_i (Fin.last n)) := by
      rw [h_ti1]
      <;> exact (h_eval1 s_j).trans (h_eval1 s_j1).symm
    rw [h1]
  have h_fvert0 : f_vert 0 = eqToHom h_eq0 := by
    have h1 : f_vert 0 = my_desc_map X 𝒰 hcover hfinite_intersections s (γ_vert 0) := by rfl
    rw [h1]
    rcases hcover x with ⟨U, hU_mem, hxU⟩
    have h_range0 : Set.range (γ_vert 0) ⊆ (U : Set X) := by
      intro z hz
      rcases hz with ⟨t, rfl⟩
      have h2 : (γ_vert 0) t = x := by
        have h3 : (γ_vert 0) t = H.eval s_j (t_i 0) := h_vert0_const t
        rw [h3, h_ti0]; exact h_eval0 s_j
      rw [h2]; exact hxU
    rw [my_desc_map_single_covered X 𝒰 hcover hfinite_intersections s (γ_vert 0) U hU_mem h_range0]
    let x1 := H.eval s_j (t_i 0)
    let x2 := H.eval s_j1 (t_i 0)
    have h_endpoints_eq : x1 = x2 := by
      dsimp only [x1, x2]
      rw [h_ti0]
      <;> exact (h_eval0 s_j).trans (h_eval0 s_j1).symm
    have h_const : ∀ (t : I), (γ_vert 0) t = x1 := h_vert0_const
    exact single_covered_map_const_path X 𝒰 hcover hfinite_intersections s (γ_vert 0) h_endpoints_eq U hU_mem h_range0 h_const
  have h_fvert_last : f_vert (Fin.last n) = eqToHom h_eq_last := by
    have h1 : f_vert (Fin.last n) = my_desc_map X 𝒰 hcover hfinite_intersections s (γ_vert (Fin.last n)) := by rfl
    rw [h1]
    rcases hcover y with ⟨U, hU_mem, hyU⟩
    have h_range_last : Set.range (γ_vert (Fin.last n)) ⊆ (U : Set X) := by
      intro z hz
      rcases hz with ⟨t, rfl⟩
      have h2 : (γ_vert (Fin.last n)) t = y := by
        have h3 : (γ_vert (Fin.last n)) t = H.eval s_j (t_i (Fin.last n)) := h_vert_last_const t
        rw [h3, h_ti1]
        exact h_eval1 s_j
      rw [h2]
      exact hyU
    rw [my_desc_map_single_covered X 𝒰 hcover hfinite_intersections s (γ_vert (Fin.last n)) U hU_mem h_range_last]
    let y1 := H.eval s_j (t_i (Fin.last n))
    let y2 := H.eval s_j1 (t_i (Fin.last n))
    have h_endpoints_eq : y1 = y2 := by
      dsimp only [y1, y2]
      rw [h_ti1]
      <;> exact (h_eval1 s_j).trans (h_eval1 s_j1).symm
    have h_const : ∀ (t : I), (γ_vert (Fin.last n)) t = y1 := h_vert_last_const
    exact single_covered_map_const_path X 𝒰 hcover hfinite_intersections s (γ_vert (Fin.last n)) h_endpoints_eq U hU_mem h_range_last h_const
  -- Step 3: Set up the top row
  let S_top : Finset I := Finset.image t_i Finset.univ
  have h_range_top' : ∀ (i : Fin n) (t : I), t_i (Fin.castSucc i) ≤ t → t ≤ t_i (Fin.succ i) → (H.eval s_j1) t ∈ (covers i : Set X) := by
    intro i t h1 h2
    have h_in_range : (H.eval s_j1) t ∈ Set.range (γ_top i) := by
      have h_lt : t_i (Fin.castSucc i) < t_i (Fin.succ i) := h_ti_strict_mono (by simp [Fin.castSucc_lt_succ])
      have h_range_eq : Set.range (γ_top i) = (H.eval s_j1) '' Set.Icc (t_i (Fin.castSucc i)) (t_i (Fin.succ i)) := by
        rw [Path.range_subpath (H.eval s_j1) (t_i (Fin.castSucc i)) (t_i (Fin.succ i))]
        <;> rw [Set.uIcc_of_le (le_of_lt h_lt)]
      rw [h_range_eq]
      exact ⟨t, ⟨h1, h2⟩, rfl⟩
    exact h_top_range i h_in_range
  have hS_top : IsAdaptedSubdivision 𝒰 (H.eval s_j1) S_top := by
    constructor
    · exact h0_in_S_bot
    · constructor
      · exact h1_in_S_bot
      · intro s₁ s₂ hs₁ hs₂ h_lt h_no_between
        have h_exists : ∃ (i : Fin n), s₁ = t_i (Fin.castSucc i) ∧ s₂ = t_i (Fin.succ i) := by
          rcases Finset.mem_image.mp hs₁ with ⟨k, _, rfl⟩
          rcases Finset.mem_image.mp hs₂ with ⟨l, _, rfl⟩
          have h_k_lt_l : k < l := by
            by_contra h
            have h' : l ≤ k := le_of_not_gt h
            have h'' : t_i l ≤ t_i k := h_ti_strict_mono.monotone h'
            exact lt_irrefl _ (lt_of_le_of_lt h'' h_lt)
          have h_l_val_succ : l.val = k.val + 1 := by
            by_contra h
            have h_k_lt_l_val : k.val < l.val := by exact_mod_cast h_k_lt_l
            have h_succ_lt : k.val + 1 < l.val := by omega
            have h_m_lt_n1 : k.val + 1 < n + 1 := by omega
            let m : Fin (n + 1) := ⟨k.val + 1, h_m_lt_n1⟩
            have h_k_lt_m : k < m := by
              apply Fin.lt_iff_val_lt_val.mpr
              simp [m] <;> omega
            have h_m_lt_l : m < l := by
              apply Fin.lt_iff_val_lt_val.mpr
              simp [m, h_succ_lt] <;> omega
            have h_between1 : t_i k < t_i m := h_ti_strict_mono h_k_lt_m
            have h_between2 : t_i m < t_i l := h_ti_strict_mono h_m_lt_l
            have h_mem : t_i m ∈ Finset.image t_i Finset.univ := by
              exact Finset.mem_image.mpr ⟨m, Finset.mem_univ _, rfl⟩
            exact h_no_between (t_i m) h_mem h_between1 h_between2
          have h_k_lt_n : k.val < n := by omega
          let i : Fin n := ⟨k.val, h_k_lt_n⟩
          have h_k_eq : k = Fin.castSucc i := by
            apply Fin.ext
            simp [i]
          have h_l_eq : l = Fin.succ i := by
            apply Fin.ext
            simp [i, h_l_val_succ, Fin.val_succ] <;> omega
          refine' ⟨i, _⟩
          constructor
          · rw [h_k_eq]
          · rw [h_l_eq]
        rcases h_exists with ⟨i, rfl, rfl⟩
        refine' ⟨covers i, hcover_mem i, _⟩
        exact h_range_top' i
  have h_desc_top : my_desc_map X 𝒰 hcover hfinite_intersections s (H.eval s_j1) =
      my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS_top :=
    my_desc_map_well_defined X 𝒰 hcover hfinite_intersections s (H.eval s_j1)
      (Classical.choose (exists_adapted_subdivision X 𝒰 hcover (H.eval s_j1))) S_top
      (Classical.choose_spec (exists_adapted_subdivision X 𝒰 hcover (H.eval s_j1))) hS_top
  have h_univ_top : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS_top =
      my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS_top n t_i h_ti_strict_mono rfl covers hcover_mem h_range_top' := by
    exact my_map_from_adapted_subdivision_universal X 𝒰 hcover hfinite_intersections s hS_top t_i h_ti_strict_mono rfl covers hcover_mem h_range_top'
  -- Step 4: Unfold definitions and use chain lemma
  have h_chain2 : comp_list n p_objs f_bottom ≫ eqToHom h_eq_last =
      eqToHom h_eq0 ≫ comp_list n q_objs f_top := by
    rw [h_fvert_last, h_fvert0] at h_chain
    exact h_chain
  -- Step 5: Conclude
  let mk_x_obj := desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk x)
  let mk_y_obj := desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk y)
  have h_bot_eq0 : p_objs 0 = mk_x_obj := by
    dsimp only [p_objs, mk_x_obj]
    have h : (H.eval s_j) (t_i 0) = x := by
      rw [h_ti0]
      exact (H.eval s_j).source
    rw [h]
    <;> rfl
  have h_bot_eq_last : p_objs (Fin.last n) = mk_y_obj := by
    dsimp only [p_objs, mk_y_obj]
    have h : (H.eval s_j) (t_i (Fin.last n)) = y := by
      rw [h_ti1]
      exact (H.eval s_j).target
    rw [h]
    <;> rfl
  have h_top_eq0 : q_objs 0 = mk_x_obj := by
    dsimp only [q_objs, mk_x_obj]
    have h : (H.eval s_j1) (t_i 0) = x := by
      rw [h_ti0]
      exact (H.eval s_j1).source
    rw [h]
    <;> rfl
  have h_top_eq_last : q_objs (Fin.last n) = mk_y_obj := by
    dsimp only [q_objs, mk_y_obj]
    have h : (H.eval s_j1) (t_i (Fin.last n)) = y := by
      rw [h_ti1]
      exact (H.eval s_j1).target
    rw [h]
    <;> rfl
  have h_eq0' : eqToHom h_bot_eq0.symm ≫ eqToHom h_eq0 = eqToHom h_top_eq0.symm := by
    have h2 : eqToHom h_bot_eq0.symm ≫ eqToHom h_eq0 = eqToHom (h_bot_eq0.symm.trans h_eq0) := by
      rw [eqToHom_trans]
    rw [h2]
    <;> congr
  have h_eq_last' : eqToHom h_eq_last.symm ≫ eqToHom h_bot_eq_last = eqToHom h_top_eq_last := by
    have h2 : eqToHom h_eq_last.symm ≫ eqToHom h_bot_eq_last = eqToHom ((h_eq_last.symm).trans h_bot_eq_last) := by
      rw [eqToHom_trans]
    rw [h2]
    <;> congr
  have h_main_bot : my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS_bot n t_i h_ti_strict_mono rfl covers hcover_mem h_range_bot' =
      eqToHom h_bot_eq0.symm ≫ comp_list n p_objs f_bottom ≫ eqToHom h_bot_eq_last := by
    simp [my_map_from_adapted_subdivision_with_covers, h_bot_eq0, h_bot_eq_last]
    <;> rfl
  have h_main_top : my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS_top n t_i h_ti_strict_mono rfl covers hcover_mem h_range_top' =
      eqToHom h_top_eq0.symm ≫ comp_list n q_objs f_top ≫ eqToHom h_top_eq_last := by
    simp [my_map_from_adapted_subdivision_with_covers, h_top_eq0, h_top_eq_last]
    <;> rfl
  have h_last_decomp : eqToHom h_bot_eq_last = eqToHom h_eq_last ≫ eqToHom h_top_eq_last := by
    rw [←eqToHom_trans]
    <;> congr
    <;> exact Eq.trans h_eq_last h_top_eq_last
  have h_final : eqToHom h_bot_eq0.symm ≫ comp_list n p_objs f_bottom ≫ eqToHom h_bot_eq_last =
      eqToHom h_top_eq0.symm ≫ comp_list n q_objs f_top ≫ eqToHom h_top_eq_last := by
    have h1 : eqToHom h_bot_eq0.symm ≫ comp_list n p_objs f_bottom ≫ eqToHom h_bot_eq_last =
        eqToHom h_bot_eq0.symm ≫ comp_list n p_objs f_bottom ≫ (eqToHom h_eq_last ≫ eqToHom h_top_eq_last) := by
      rw [h_last_decomp]
    rw [h1]
    have h2 : eqToHom h_bot_eq0.symm ≫ comp_list n p_objs f_bottom ≫ (eqToHom h_eq_last ≫ eqToHom h_top_eq_last) =
        eqToHom h_bot_eq0.symm ≫ (comp_list n p_objs f_bottom ≫ eqToHom h_eq_last) ≫ eqToHom h_top_eq_last := by
      simp [Category.assoc]
      <;> rfl
    rw [h2]
    have h3 : eqToHom h_bot_eq0.symm ≫ (comp_list n p_objs f_bottom ≫ eqToHom h_eq_last) ≫ eqToHom h_top_eq_last =
        eqToHom h_bot_eq0.symm ≫ (eqToHom h_eq0 ≫ comp_list n q_objs f_top) ≫ eqToHom h_top_eq_last := by
      rw [h_chain2]
    rw [h3]
    have h4 : eqToHom h_bot_eq0.symm ≫ (eqToHom h_eq0 ≫ comp_list n q_objs f_top) ≫ eqToHom h_top_eq_last =
        (eqToHom h_bot_eq0.symm ≫ eqToHom h_eq0) ≫ comp_list n q_objs f_top ≫ eqToHom h_top_eq_last := by
      simp [Category.assoc]
      <;> rfl
    rw [h4]
    have h5 : (eqToHom h_bot_eq0.symm ≫ eqToHom h_eq0) ≫ comp_list n q_objs f_top ≫ eqToHom h_top_eq_last =
        eqToHom h_top_eq0.symm ≫ comp_list n q_objs f_top ≫ eqToHom h_top_eq_last := by
      rw [h_eq0']
    exact h5
  have h_both : my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS_bot n t_i h_ti_strict_mono rfl covers hcover_mem h_range_bot' =
      my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS_top n t_i h_ti_strict_mono rfl covers hcover_mem h_range_top' := by
    rw [h_main_bot, h_main_top, h_final]
  rw [h_desc_bot, h_desc_top, h_univ_bot, h_univ_top]
  exact h_both


/-- Homotopy invariance of my_desc_map: homotopic paths have the same descent map. -/
theorem my_desc_map_homotopy_invariant_aux
    {x y : X} {γ₁ γ₂ : Path x y}
    (h : Path.Homotopic γ₁ γ₂) :
    my_desc_map X 𝒰 hcover hfinite_intersections s γ₁ =
    my_desc_map X 𝒰 hcover hfinite_intersections s γ₂ := by
  rcases h with ⟨H⟩
  have h_main := exists_partwise_covered_homotopy 𝒰 hcover H
  rcases h_main with ⟨n, hn_pos, ⟨pcH⟩⟩
  let t_of_idx (k : Fin (n + 1)) : I := ⟨(k.val : ℝ) / (n : ℝ), by
    have h₁ : 0 ≤ (k.val : ℝ) / (n : ℝ) := by positivity
    have h₂ : (k.val : ℝ) / (n : ℝ) ≤ 1 := by
      have h₃ : k.val < n + 1 := k.is_lt
      have h₄ : (k.val : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.lt_succ_iff.mp h₃)
      have h₅ : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
      exact (div_le_one h₅).mpr h₄
    exact ⟨h₁, h₂⟩⟩
  let row (k : Fin (n + 1)) : Path x y := H.eval (t_of_idx k)
  have h_ind : ∀ (k : Fin (n + 1)),
      my_desc_map X 𝒰 hcover hfinite_intersections s (row 0) =
      my_desc_map X 𝒰 hcover hfinite_intersections s (row k) := by
    intro k
    induction k using Fin.induction with
    | zero =>
      simp [row]
    | succ k ih =>
      let j : Fin n := k
      let t_j : I := ⟨(j.val : ℝ) / (n : ℝ), by
        have h₁ : 0 ≤ (j.val : ℝ) / (n : ℝ) := by positivity
        have h₂ : (j.val : ℝ) / (n : ℝ) ≤ 1 := by
          have h₃ : j.val < n := j.is_lt
          have h₄ : (j.val : ℝ) ≤ (n : ℝ) := by exact_mod_cast h₃.le
          have h₅ : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
          exact (div_le_one h₅).mpr h₄
        exact ⟨h₁, h₂⟩⟩
      let t_j1 : I := ⟨((j.val : ℝ) + 1) / (n : ℝ), by
        have h₁ : 0 ≤ ((j.val : ℝ) + 1) / (n : ℝ) := by positivity
        have h₂ : ((j.val : ℝ) + 1) / (n : ℝ) ≤ 1 := by
          have h₃ : j.val < n := j.is_lt
          have h₄ : (j.val : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr h₃)
          have h₅ : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
          exact (div_le_one h₅).mpr h₄
        exact ⟨h₁, h₂⟩⟩
      have h_tj_eq : t_of_idx (Fin.castSucc k) = t_j := by
        apply Subtype.ext
        simp [t_of_idx, t_j, Fin.castSucc] <;> ring
      have h_tj1_eq : t_of_idx (Fin.succ k) = t_j1 := by
        apply Subtype.ext
        simp [t_of_idx, t_j1, Fin.val_succ] <;> ring
      have h_row_j : row (Fin.castSucc k) = H.eval t_j := by
        simpa [row] using congr_arg (fun t : I => H.eval t) h_tj_eq
      have h_row_j1 : row (Fin.succ k) = H.eval t_j1 := by
        simpa [row] using congr_arg (fun t : I => H.eval t) h_tj1_eq
      have h_step_main : my_desc_map X 𝒰 hcover hfinite_intersections s (H.eval t_j) =
          my_desc_map X 𝒰 hcover hfinite_intersections s (H.eval t_j1) :=
        consecutive_rows_equal_my_desc_map_aux X 𝒰 hcover hfinite_intersections s H hn_pos pcH j
      have h_step : my_desc_map X 𝒰 hcover hfinite_intersections s (row (Fin.castSucc k)) =
          my_desc_map X 𝒰 hcover hfinite_intersections s (row (Fin.succ k)) := by
        rw [h_row_j, h_row_j1]
        exact h_step_main
      calc
        my_desc_map X 𝒰 hcover hfinite_intersections s (row 0)
          = my_desc_map X 𝒰 hcover hfinite_intersections s (row (Fin.castSucc k)) := ih
        _ = my_desc_map X 𝒰 hcover hfinite_intersections s (row (Fin.succ k)) := h_step
  have h0 := h_ind (Fin.last n)
  have h_row0 : row 0 = γ₁ := by
    have h_eq : t_of_idx 0 = (0 : I) := by
      apply Subtype.ext
      simp [t_of_idx] <;> field_simp <;> ring
    simpa [row] using congr_arg (fun t : I => H.eval t) h_eq ▸ H.eval_zero
  have h_rown : row (Fin.last n) = γ₂ := by
    have h_n_ne_zero : n ≠ 0 := hn_pos.ne'
    have h_n_pos' : (n : ℝ) ≠ 0 := by exact_mod_cast h_n_ne_zero
    have h_val_eq : ((Fin.last n).val : ℝ) = (n : ℝ) := by
      exact_mod_cast (by simp [Fin.last])
    have h_div_eq : ((Fin.last n).val : ℝ) / (n : ℝ) = 1 := by
      rw [h_val_eq]
      field_simp [h_n_pos'] <;> ring
    have h_eq : t_of_idx (Fin.last n) = (1 : I) := by
      apply Subtype.ext
      exact h_div_eq
    simpa [row] using congr_arg (fun t : I => H.eval t) h_eq ▸ H.eval_one
  rw [h_row0, h_rown] at h0
  exact h0

end

end
