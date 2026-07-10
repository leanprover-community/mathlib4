module

public import Mathlib
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.CleanDescent
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.ConsecutiveRows
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.RectangleBoundaryHomotopy
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.HomotopyInvHelpers

@[expose] public section

set_option maxHeartbeats 500000

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

/-
  NOTE: This file is a backup/alternative proof approach.
  The main proof lives in CleanDescent.lean.
  This theorem is work-in-progress and not used by the main proof.
-/
#check (my_desc_map X 𝒰 hcover hfinite_intersections s)  -- keep variables used

/-
theorem consecutive_rows_equal_my_desc_map_clean {x y : X} {γ₁ γ₂ : Path x y}
    (H : Path.Homotopy γ₁ γ₂) {n : ℕ} (hn_pos : 0 < n)
    (pcH : PartwiseCoveredHomotopy 𝒰 H n n) (j : Fin n) :
    my_desc_map X 𝒰 hcover hfinite_intersections s (H.eval ⟨(j.val : ℝ) / (n : ℝ), by
      have h₁ : 0 ≤ (j.val : ℝ) / (n : ℝ) := by positivity
      have h₂ : (j.val : ℝ) / (n : ℝ) ≤ 1 := by
        have h₃ : j.val < n := j.is_lt
        have h₄ : (j.val : ℝ) ≤ (n : ℝ) := by exact_mod_cast h₃.le
        have h₅ : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
        exact (div_le_one h₅).mpr h₄
      exact ⟨h₁, h₂⟩⟩) =
    my_desc_map X 𝒰 hcover hfinite_intersections s (H.eval ⟨((j.val : ℝ) + 1) / (n : ℝ), by
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
  -- Row positions
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
  -- Covering sets for each column
  let covers (i : Fin n) : Opens X := pcH.covers j i
  have hcover_mem (i : Fin n) : covers i ∈ 𝒰 := pcH.hcover_mem j i
  -- Strict monotonicity of t_i
  have h_ti_strict_mono : StrictMono t_i := by
    intro i k h
    apply Subtype.mk_lt_mk.mpr
    have h₅ : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
    have h₆ : (i.val : ℝ) < (k.val : ℝ) := by exact_mod_cast h
    gcongr
  have ha_le_b : (s_j : ℝ) ≤ (s_j1 : ℝ) := by
    have h_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
    have h_j_le : (j : ℝ) ≤ (j : ℝ) + 1 := by linarith
    exact div_le_div_of_nonneg_right h_j_le (by positivity)
  -- Bottom row paths (row j)
  let γ_bottom (i : Fin n) : Path (H.eval s_j (t_i (Fin.castSucc i))) (H.eval s_j (t_i (Fin.succ i))) :=
    (H.eval s_j).subpath (t_i (Fin.castSucc i)) (t_i (Fin.succ i))
  -- Top row paths (row j+1)
  let γ_top (i : Fin n) : Path (H.eval s_j1 (t_i (Fin.castSucc i))) (H.eval s_j1 (t_i (Fin.succ i))) :=
    (H.eval s_j1).subpath (t_i (Fin.castSucc i)) (t_i (Fin.succ i))
  -- Vertical paths at each grid point
  let s_lerp (t : I) : I := ⟨(s_j : ℝ) + (t : ℝ) * ((s_j1 : ℝ) - (s_j : ℝ)), by
    have h_sj_nonneg : 0 ≤ (s_j : ℝ) := s_j.prop.1
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
    apply Subtype.ext; simp [s_lerp] <;> ring
  have h_s_lerp1 : s_lerp 1 = s_j1 := by
    apply Subtype.ext; simp [s_lerp] <;> ring
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
    have h_diff_nonneg : 0 ≤ (s_j1 : ℝ) - (s_j : ℝ) := by linarith
    have h_t_nonneg : 0 ≤ (t : ℝ) := t.prop.1
    have h_t_le_one : (t : ℝ) ≤ 1 := t.prop.2
    constructor
    · have h : 0 ≤ (t : ℝ) * ((s_j1 : ℝ) - (s_j : ℝ)) := mul_nonneg h_t_nonneg h_diff_nonneg
      linarith
    · have h : (t : ℝ) * ((s_j1 : ℝ) - (s_j : ℝ)) ≤ (s_j1 : ℝ) - (s_j : ℝ) :=
        mul_le_of_le_one_left h_diff_nonneg h_t_le_one
      linarith
  -- Range proofs
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
  have h_vert_range (i : Fin n) : Set.range (γ_vert (Fin.castSucc i)) ⊆ (covers i : Set X) := by
    intro z hz
    rcases hz with ⟨t, rfl⟩
    have h_between := h_s_lerp_between t
    have h1 : (j : ℝ) / (n : ℝ) ≤ (s_lerp t : ℝ) := by
      have h_eq : (s_j : ℝ) = (j : ℝ) / (n : ℝ) := by rfl
      rw [h_eq] at h_between; exact h_between.1
    have h2 : (s_lerp t : ℝ) ≤ ((j : ℝ) + 1) / (n : ℝ) := by
      have h_eq : (s_j1 : ℝ) = ((j : ℝ) + 1) / (n : ℝ) := by rfl
      rw [h_eq] at h_between; exact h_between.2
    have h3 : (i : ℝ) / (n : ℝ) ≤ (t_i (Fin.castSucc i) : ℝ) := by rfl
    have h4 : (t_i (Fin.castSucc i) : ℝ) ≤ ((i : ℝ) + 1) / (n : ℝ) := by
      have h_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
      have h_i_le : (i : ℝ) ≤ (i : ℝ) + 1 := by linarith
      exact div_le_div_of_nonneg_right h_i_le (by positivity)
    exact pcH.h_rectangles j i (s_lerp t, t_i (Fin.castSucc i)) h1 h2 h3 h4
  have h_right_range (i : Fin n) : Set.range (γ_vert (Fin.succ i)) ⊆ (covers i : Set X) := by
    intro z hz
    rcases hz with ⟨t, rfl⟩
    have h_between := h_s_lerp_between t
    have h1 : (j : ℝ) / (n : ℝ) ≤ (s_lerp t : ℝ) := by
      have h_eq : (s_j : ℝ) = (j : ℝ) / (n : ℝ) := by rfl
      rw [h_eq] at h_between; exact h_between.1
    have h2 : (s_lerp t : ℝ) ≤ ((j : ℝ) + 1) / (n : ℝ) := by
      have h_eq : (s_j1 : ℝ) = ((j : ℝ) + 1) / (n : ℝ) := by rfl
      rw [h_eq] at h_between; exact h_between.2
    have h3 : (i : ℝ) / (n : ℝ) ≤ (t_i (Fin.succ i) : ℝ) := by
      have h_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
      have h_i_val : (i : ℝ) ≤ (i : ℝ) + 1 := by linarith
      have h : (i : ℝ) / (n : ℝ) ≤ ((i : ℝ) + 1) / (n : ℝ) := by
        exact div_le_div_of_nonneg_right h_i_val (by positivity)
      have h_eq : (t_i (Fin.succ i) : ℝ) = ((i : ℝ) + 1) / (n : ℝ) := by
        simp [t_i, Fin.val_succ] <;> ring
      rw [h_eq]; exact h
    have h4 : (t_i (Fin.succ i) : ℝ) ≤ ((i : ℝ) + 1) / (n : ℝ) := by
      have h_eq : (t_i (Fin.succ i) : ℝ) = ((i : ℝ) + 1) / (n : ℝ) := by
        simp [t_i, Fin.val_succ] <;> ring
      rw [h_eq]
    exact pcH.h_rectangles j i (s_lerp t, t_i (Fin.succ i)) h1 h2 h3 h4
  -- Rectangle homotopy for each column
  have h_rect_both (i : Fin n) :
    ∃ (H_rect : Path.Homotopy ((γ_bottom i).trans (γ_vert (Fin.succ i)))
        ((γ_vert (Fin.castSucc i)).trans (γ_top i))),
      ∀ (p : I × I), H_rect p ∈ (covers i : Set X) := by
    let H_cont : C(I × I, X) := ⟨fun p => H p, H.continuous⟩
    let a := s_j
    let b := s_j1
    let c := t_i (Fin.castSucc i)
    let d := t_i (Fin.succ i)
    have hc_le_d : (c : ℝ) ≤ (d : ℝ) :=
      le_of_lt (h_ti_strict_mono (by simp [Fin.castSucc_lt_succ]))
    have hU : ∀ (p : I × I), (a : ℝ) ≤ (p.1 : ℝ) → (p.1 : ℝ) ≤ (b : ℝ) →
        (c : ℝ) ≤ (p.2 : ℝ) → (p.2 : ℝ) ≤ (d : ℝ) → H_cont p ∈ (covers i : Set X) := by
      intro p h1 h2 h3 h4
      have h1' : (j : ℝ) / (n : ℝ) ≤ (p.1 : ℝ) := by
        have h_eq : (a : ℝ) = (j : ℝ) / (n : ℝ) := by rfl
        rw [h_eq] at h1; exact h1
      have h2' : (p.1 : ℝ) ≤ ((j : ℝ) + 1) / (n : ℝ) := by
        have h_eq : (b : ℝ) = ((j : ℝ) + 1) / (n : ℝ) := by rfl
        rw [h_eq] at h2; exact h2
      have h3' : (i : ℝ) / (n : ℝ) ≤ (p.2 : ℝ) := by
        have h_eq : (c : ℝ) = (i : ℝ) / (n : ℝ) := by rfl
        rw [h_eq] at h3; exact h3
      have h4' : (p.2 : ℝ) ≤ ((i : ℝ) + 1) / (n : ℝ) := by
        have h_eq : (d : ℝ) = ((i : ℝ) + 1) / (n : ℝ) := by
          simp [d, t_i, Fin.val_succ] <;> ring
        rw [h_eq] at h4; exact h4
      exact pcH.h_rectangles j i p h1' h2' h3' h4'
    have h_main := RectangleBoundaryHomotopy.exists_rectangle_boundary_homotopy_in_U
      H_cont a b c d ha_le_b hc_le_d (covers i : Set X) hU
    rcases h_main with ⟨H_rect, hH_rect_range⟩
    -- Prove equalities between rectangle edges and our paths
    have h_eq_bot : RectangleBoundaryHomotopy.bottom_edge H_cont a b c ha_le_b = γ_vert (Fin.castSucc i) := by
      apply Path.ext; funext s; rfl
    have h_eq_right : RectangleBoundaryHomotopy.right_edge H_cont b c d hc_le_d = γ_top i := by
      apply Path.ext
      funext t
      dsimp only [γ_top]
      have h_lerp_eq : RectangleBoundaryHomotopy.lerp_I c d hc_le_d t = Set.Icc.convexComb c d t := by
        apply Subtype.ext
        simp [RectangleBoundaryHomotopy.lerp_I, Set.Icc.coe_convexComb] <;> ring
      have h1 : (RectangleBoundaryHomotopy.right_edge H_cont b c d hc_le_d) t =
          H.eval b (RectangleBoundaryHomotopy.lerp_I c d hc_le_d t) := by rfl
      have h2 : ((H.eval s_j1).subpath (t_i (Fin.castSucc i)) (t_i (Fin.succ i))) t =
          H.eval s_j1 (Set.Icc.convexComb (t_i (Fin.castSucc i)) (t_i (Fin.succ i)) t) := by
        exact?
      have h_b_eq : b = s_j1 := by rfl
      have h_c_eq : c = t_i (Fin.castSucc i) := by rfl
      have h_d_eq : d = t_i (Fin.succ i) := by rfl
      calc
        (RectangleBoundaryHomotopy.right_edge H_cont b c d hc_le_d) t
          = H.eval b (RectangleBoundaryHomotopy.lerp_I c d hc_le_d t) := h1
        _ = H.eval s_j1 (RectangleBoundaryHomotopy.lerp_I c d hc_le_d t) := by rw [h_b_eq]
        _ = H.eval s_j1 (Set.Icc.convexComb c d t) := by rw [h_lerp_eq]
        _ = H.eval s_j1 (Set.Icc.convexComb (t_i (Fin.castSucc i)) (t_i (Fin.succ i)) t) := by
          rw [h_c_eq, h_d_eq]
        _ = ((H.eval s_j1).subpath (t_i (Fin.castSucc i)) (t_i (Fin.succ i))) t := h2.symm
    have h_eq_left : RectangleBoundaryHomotopy.left_edge H_cont a c d hc_le_d = γ_bottom i := by
      apply Path.ext
      funext t
      dsimp only [γ_bottom]
      have h_lerp_eq : RectangleBoundaryHomotopy.lerp_I c d hc_le_d t = Set.Icc.convexComb c d t := by
        apply Subtype.ext
        simp [RectangleBoundaryHomotopy.lerp_I, Set.Icc.coe_convexComb] <;> ring
      have h1 : (RectangleBoundaryHomotopy.left_edge H_cont a c d hc_le_d) t =
          H.eval a (RectangleBoundaryHomotopy.lerp_I c d hc_le_d t) := by rfl
      have h2 : ((H.eval s_j).subpath (t_i (Fin.castSucc i)) (t_i (Fin.succ i))) t =
          H.eval s_j (Set.Icc.convexComb (t_i (Fin.castSucc i)) (t_i (Fin.succ i)) t) := by
        exact?
      have h_a_eq : a = s_j := by rfl
      have h_c_eq : c = t_i (Fin.castSucc i) := by rfl
      have h_d_eq : d = t_i (Fin.succ i) := by rfl
      calc
        (RectangleBoundaryHomotopy.left_edge H_cont a c d hc_le_d) t
          = H.eval a (RectangleBoundaryHomotopy.lerp_I c d hc_le_d t) := h1
        _ = H.eval s_j (RectangleBoundaryHomotopy.lerp_I c d hc_le_d t) := by rw [h_a_eq]
        _ = H.eval s_j (Set.Icc.convexComb c d t) := by rw [h_lerp_eq]
        _ = H.eval s_j (Set.Icc.convexComb (t_i (Fin.castSucc i)) (t_i (Fin.succ i)) t) := by
          rw [h_c_eq, h_d_eq]
        _ = ((H.eval s_j).subpath (t_i (Fin.castSucc i)) (t_i (Fin.succ i))) t := h2.symm
    have h_eq_top : RectangleBoundaryHomotopy.top_edge H_cont a b d ha_le_b = γ_vert (Fin.succ i) := by
      apply Path.ext; funext s; rfl
    let γ_a := (RectangleBoundaryHomotopy.bottom_edge H_cont a b c ha_le_b).trans
        (RectangleBoundaryHomotopy.right_edge H_cont b c d hc_le_d)
    let γ_b := (RectangleBoundaryHomotopy.left_edge H_cont a c d hc_le_d).trans
        (RectangleBoundaryHomotopy.top_edge H_cont a b d ha_le_b)
    let γ_a' := (γ_vert (Fin.castSucc i)).trans (γ_top i)
    let γ_b' := (γ_bottom i).trans (γ_vert (Fin.succ i))
    have h1 : γ_a = γ_a' := by
      dsimp only [γ_a, γ_a']
      rw [h_eq_bot, h_eq_right]
      <;> rfl
    have h2 : γ_b = γ_b' := by
      dsimp only [γ_b, γ_b']
      let γ_left := RectangleBoundaryHomotopy.left_edge H_cont a c d hc_le_d
      let γ_top_edge := RectangleBoundaryHomotopy.top_edge H_cont a b d ha_le_b
      have h_step1 : γ_left.trans γ_top_edge = γ_left.trans (γ_vert (Fin.succ i)) := by
        exact congr_arg (fun γ : Path _ _ => γ_left.trans γ) h_eq_top
      have h_step2 : γ_left.trans (γ_vert (Fin.succ i)) = (γ_bottom i).trans (γ_vert (Fin.succ i)) := by
        exact congr_arg (fun γ : Path _ _ => γ.trans (γ_vert (Fin.succ i))) h_eq_left
      exact h_step1.trans h_step2
    -- Generalized statement: homotopy with range property transports across path equalities
    have h_transport : ∀ (γ1 γ2 γ1' γ2' : Path (H.eval s_j (t_i (Fin.castSucc i))) (H.eval s_j1 (t_i (Fin.succ i))))
        (h1' : γ1 = γ1') (h2' : γ2 = γ2')
        (H : Path.Homotopy γ1 γ2) (hH : ∀ p, H p ∈ (covers i : Set X)),
      ∃ (H' : Path.Homotopy γ1' γ2'), ∀ p, H' p ∈ (covers i : Set X) := by
      intro γ1 γ2 γ1' γ2' h1' h2' H hH
      induction h1'
      induction h2'
      exact ⟨H, hH⟩
    have h_result : ∃ (H' : Path.Homotopy γ_a' γ_b'), ∀ p, H' p ∈ (covers i : Set X) :=
      h_transport γ_a γ_b γ_a' γ_b' h1 h2 H_rect hH_rect_range
    -- Now take symm and prove range is preserved
    rcases h_result with ⟨H_rect', hH_rect'_range⟩
    have h_symm_range : ∀ (p : I × I), H_rect'.symm p ∈ (covers i : Set X) := by
      intro p
      have h_main : ∀ (q : Path.Homotopy γ_a' γ_b'),
          (∀ (x : I × I), q x ∈ (covers i : Set X)) → ∀ (x : I × I), q.symm x ∈ (covers i : Set X) := by
        intro q hq x
        exact?
      exact h_main H_rect' hH_rect'_range p
    refine' ⟨H_rect'.symm, h_symm_range⟩
  let h_rect_homotopy (i : Fin n) :
    Path.Homotopy ((γ_bottom i).trans (γ_vert (Fin.succ i)))
      ((γ_vert (Fin.castSucc i)).trans (γ_top i)) :=
    (h_rect_both i).choose
  have h_rect_homotopy_range (i : Fin n) :
    ∀ (p : I × I), (h_rect_homotopy i) p ∈ (covers i : Set X) :=
    (h_rect_both i).choose_spec
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
      dsimp only [f_vert, f_vert_left]
      exact my_desc_map_single_covered X 𝒰 hcover hfinite_intersections s (γ_vert (Fin.castSucc i)) (covers i) (hcover_mem i) (h_vert_range i)
    have h2 : f_vert (Fin.succ i) = f_vert_right := by
      dsimp only [f_vert, f_vert_right]
      exact my_desc_map_single_covered X 𝒰 hcover hfinite_intersections s (γ_vert (Fin.succ i)) (covers i) (hcover_mem i) (h_right_range i)
    rw [h2, h1]
    exact h_main
  -- Apply the chain lemma
  have h_chain : comp_list n p_objs f_bottom ≫ f_vert (Fin.last n) =
      f_vert 0 ≫ comp_list n q_objs f_top :=
    comp_list_chain_commute p_objs q_objs f_bottom f_top f_vert h_square
  -- Step 1: Prove γ_vert 0 is constant (at x) and γ_vert (Fin.last n) is constant (at y)
  have h_eval0 : ∀ (s : I), H.eval s 0 = x := by
    intro s; exact (H.eval s).source
  have h_eval1 : ∀ (s : I), H.eval s 1 = y := by
    intro s; exact (H.eval s).target
  have h_ti0 : t_i 0 = (0 : I) := by
    apply Subtype.ext
    have h : (t_i 0).val = 0 := by
      dsimp only [t_i]; simpa using zero_div (n : ℝ)
    have h' : ((0 : I) : ℝ) = 0 := by norm_cast
    rw [h']; exact h
  have h_ti1 : t_i (Fin.last n) = (1 : I) := by
    apply Subtype.ext
    have h_last_val : (Fin.last n).val = n := by simp [Fin.last] <;> omega
    have h_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
    have h : (t_i (Fin.last n)).val = 1 := by
      dsimp only [t_i]; rw [h_last_val]
      have h_pos' : (n : ℝ) ≠ 0 := by exact_mod_cast hn_pos.ne'
      exact div_self h_pos'
    have h' : ((1 : I) : ℝ) = 1 := by norm_cast
    rw [h']; exact h
  have h_vert0_const : ∀ (t : I), (γ_vert 0) t = H.eval s_j (t_i 0) := by
    intro t
    have h1 : (γ_vert 0) t = H.eval (s_lerp t) (t_i 0) := by rfl
    have h2 : H.eval (s_lerp t) (t_i 0) = x := by
      rw [h_ti0]; exact h_eval0 (s_lerp t)
    have h3 : H.eval s_j (t_i 0) = x := by
      rw [h_ti0]; exact h_eval0 s_j
    rw [h1, h2, h3]
  have h_vert_last_const : ∀ (t : I), (γ_vert (Fin.last n)) t = H.eval s_j (t_i (Fin.last n)) := by
    intro t
    have h1 : (γ_vert (Fin.last n)) t = H.eval (s_lerp t) (t_i (Fin.last n)) := by rfl
    have h2 : H.eval (s_lerp t) (t_i (Fin.last n)) = y := by
      rw [h_ti1]; exact h_eval1 (s_lerp t)
    have h3 : H.eval s_j (t_i (Fin.last n)) = y := by
      rw [h_ti1]; exact h_eval1 s_j
    rw [h1, h2, h3]
  have h_eq0 : p_objs 0 = q_objs 0 := by
    dsimp only [p_objs, q_objs]
    have h1 : H.eval s_j (t_i 0) = H.eval s_j1 (t_i 0) := by
      rw [h_ti0] <;> exact (h_eval0 s_j).trans (h_eval0 s_j1).symm
    rw [h1]
  have h_eq_last : p_objs (Fin.last n) = q_objs (Fin.last n) := by
    dsimp only [p_objs, q_objs]
    have h1 : H.eval s_j (t_i (Fin.last n)) = H.eval s_j1 (t_i (Fin.last n)) := by
      rw [h_ti1] <;> exact (h_eval1 s_j).trans (h_eval1 s_j1).symm
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
    dsimp only [single_covered_map]
    let U_set : Set X := (U : Set X)
    have hx1 : H.eval s_j (t_i 0) ∈ U := by
      have h2 : H.eval s_j (t_i 0) = x := by rw [h_ti0]; exact h_eval0 s_j
      rw [h2]; exact hxU
    have hx2 : H.eval s_j1 (t_i 0) ∈ U := by
      have h2 : H.eval s_j1 (t_i 0) = x := by rw [h_ti0]; exact h_eval0 s_j1
      rw [h2]; exact hxU
    let γ_lift : Path (⟨H.eval s_j (t_i 0), hx1⟩ : U_set) (⟨H.eval s_j1 (t_i 0), hx2⟩ : U_set) :=
      (Path.lift_to_subtype (γ_vert 0) hx1 hx2 h_range0).choose
    let hγ_lift : ∀ (t : I), (γ_lift t : X) = (γ_vert 0) t :=
      (Path.lift_to_subtype (γ_vert 0) hx1 hx2 h_range0).choose_spec
    have h_pointwise : ∀ (t : I), (γ_lift t : X) = x := by
      intro t
      have h1 : (γ_lift t : X) = (γ_vert 0) t := hγ_lift t
      have h2 : (γ_vert 0) t = x := by
        have h3 : (γ_vert 0) t = H.eval s_j (t_i 0) := h_vert0_const t
        rw [h3, h_ti0]; exact h_eval0 s_j
      rw [h1, h2]
    have h_lift_const : ∀ (t : I), γ_lift t = γ_lift 0 := by
      intro t
      apply Subtype.ext
      have h_t : (γ_lift t : X) = x := h_pointwise t
      have h_0 : (γ_lift 0 : X) = x := h_pointwise 0
      exact h_t.trans h_0.symm
    -- γ_lift is constant, so its homotopy class is the identity
    have h_end_eq : γ_lift 1 = γ_lift 0 := h_lift_const 1
    have h_const_homotopy : Path.Homotopic γ_lift
        ((Path.refl (γ_lift 0)).cast rfl h_end_eq.symm) := by
      refine' ⟨{
        toFun := fun (p : I × I) => γ_lift p.2,
        map_zero_left' := by
          funext t
          exact h_lift_const t,
        map_one_left' := by
          funext t
          exact h_lift_const t,
        map_zero_right' := by simp,
        map_one_right' := by
          simp [h_end_eq]
      }⟩
    have h_class_eq : Path.Homotopic.Quotient.mk γ_lift =
        Path.Homotopic.Quotient.mk ((Path.refl (γ_lift 0)).cast rfl h_end_eq.symm) := by
      exact Quotient.sound h_const_homotopy
    -- Therefore the functor maps it to the identity
    have h_f'_id : (s.ι.app ⟨U, hU_mem⟩).map (Path.Homotopic.Quotient.mk γ_lift) =
        eqToHom (congr_arg ((s.ι.app ⟨U, hU_mem⟩).obj ∘ FundamentalGroupoid.mk) h_end_eq.symm) := by
      rw [h_class_eq]
      <;> simp
    -- Unfold single_covered_map and use this fact
    have h_main_goal : f_vert 0 = eqToHom h_eq0 := by
      dsimp only [f_vert, single_covered_map]
      rw [my_desc_map_single_covered X 𝒰 hcover hfinite_intersections s (γ_vert 0) U hU_mem h_range0]
      rw [h_f'_id]
      <;> simp [h_eq0]
      <;> aesop
    exact h_main_goal
  have h_fvert_last : f_vert (Fin.last n) = eqToHom h_eq_last := by
    have h1 : f_vert (Fin.last n) = my_desc_map X 𝒰 hcover hfinite_intersections s (γ_vert (Fin.last n)) := by rfl
    rw [h1]
    rcases hcover y with ⟨U, hU_mem, hyU⟩
    have h_range_last : Set.range (γ_vert (Fin.last n)) ⊆ (U : Set X) := by
      intro z hz
      rcases hz with ⟨t, rfl⟩
      have h2 : (γ_vert (Fin.last n)) t = y := by
        have h3 : (γ_vert (Fin.last n)) t = H.eval s_j (t_i (Fin.last n)) := h_vert_last_const t
        rw [h3, h_ti1]; exact h_eval1 s_j
      rw [h2]; exact hyU
    rw [my_desc_map_single_covered X 𝒰 hcover hfinite_intersections s (γ_vert (Fin.last n)) U hU_mem h_range_last]
    dsimp only [single_covered_map]
    let U_set : Set X := (U : Set X)
    have hy1 : H.eval s_j (t_i (Fin.last n)) ∈ U := by
      have h2 : H.eval s_j (t_i (Fin.last n)) = y := by rw [h_ti1]; exact h_eval1 s_j
      rw [h2]; exact hyU
    have hy2 : H.eval s_j1 (t_i (Fin.last n)) ∈ U := by
      have h2 : H.eval s_j1 (t_i (Fin.last n)) = y := by rw [h_ti1]; exact h_eval1 s_j1
      rw [h2]; exact hyU
    let γ_lift : Path (⟨H.eval s_j (t_i (Fin.last n)), hy1⟩ : U_set) (⟨H.eval s_j1 (t_i (Fin.last n)), hy2⟩ : U_set) :=
      (Path.lift_to_subtype (γ_vert (Fin.last n)) hy1 hy2 h_range_last).choose
    let hγ_lift : ∀ (t : I), (γ_lift t : X) = (γ_vert (Fin.last n)) t :=
      (Path.lift_to_subtype (γ_vert (Fin.last n)) hy1 hy2 h_range_last).choose_spec
    have h_pointwise : ∀ (t : I), (γ_lift t : X) = y := by
      intro t
      have h1 : (γ_lift t : X) = (γ_vert (Fin.last n)) t := hγ_lift t
      have h2 : (γ_vert (Fin.last n)) t = y := by
        have h3 : (γ_vert (Fin.last n)) t = H.eval s_j (t_i (Fin.last n)) := h_vert_last_const t
        rw [h3, h_ti1]; exact h_eval1 s_j
      rw [h1, h2]
    have h_lift_const : ∀ (t : I), γ_lift t = γ_lift 0 := by
      intro t
      apply Subtype.ext
      have h_t : (γ_lift t : X) = y := h_pointwise t
      have h_0 : (γ_lift 0 : X) = y := h_pointwise 0
      exact h_t.trans h_0.symm
    -- γ_lift is constant, so its homotopy class is the identity
    have h_end_eq : γ_lift 1 = γ_lift 0 := h_lift_const 1
    have h_const_homotopy : Path.Homotopic γ_lift
        ((Path.refl (γ_lift 0)).cast rfl h_end_eq.symm) := by
      refine' ⟨{
        toFun := fun (p : I × I) => γ_lift p.2,
        map_zero_left' := by
          funext t
          exact h_lift_const t,
        map_one_left' := by
          funext t
          exact h_lift_const t,
        map_zero_right' := by simp,
        map_one_right' := by
          simp [h_end_eq]
      }⟩
    have h_class_eq : Path.Homotopic.Quotient.mk γ_lift =
        Path.Homotopic.Quotient.mk ((Path.refl (γ_lift 0)).cast rfl h_end_eq.symm) := by
      exact Quotient.sound h_const_homotopy
    -- Therefore the functor maps it to the identity
    have h_f'_id : (s.ι.app ⟨U, hU_mem⟩).map (Path.Homotopic.Quotient.mk γ_lift) =
        eqToHom (congr_arg ((s.ι.app ⟨U, hU_mem⟩).obj ∘ FundamentalGroupoid.mk) h_end_eq.symm) := by
      rw [h_class_eq]
      <;> simp
    -- Unfold single_covered_map and use this fact
    have h_main_goal : f_vert (Fin.last n) = eqToHom h_eq_last := by
      dsimp only [f_vert, single_covered_map]
      rw [my_desc_map_single_covered X 𝒰 hcover hfinite_intersections s (γ_vert (Fin.last n)) U hU_mem h_range_last]
      rw [h_f'_id]
      <;> simp [h_eq_last]
      <;> aesop
    exact h_main_goal
  -- Step 2: Rewrite chain lemma with eqToHom
  have h_chain2 : comp_list n p_objs f_bottom ≫ eqToHom h_eq_last =
      eqToHom h_eq0 ≫ comp_list n q_objs f_top := by
    rw [h_fvert_last, h_fvert0] at h_chain
    exact h_chain
  -- Step 3: Set up adapted subdivisions for bottom and top rows
  let S_bot : Finset I := Finset.image t_i Finset.univ
  let S_top : Finset I := Finset.image t_i Finset.univ
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
            apply Fin.ext; simp [i]
          have h_l_eq : l = Fin.succ i := by
            apply Fin.ext
            simp [i, h_l_val_succ, Fin.val_succ] <;> omega
          refine' ⟨i, _⟩
          constructor
          · rw [h_k_eq]
          · rw [h_l_eq]
        rcases h_exists with ⟨i, rfl, rfl⟩
        refine' ⟨covers i, hcover_mem i, _⟩
        exact h_range_bot' i
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
            apply Fin.ext; simp [i]
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
  have h_desc_bot : my_desc_map X 𝒰 hcover hfinite_intersections s (H.eval s_j) =
      my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS_bot :=
    my_desc_map_well_defined X 𝒰 hcover hfinite_intersections s (H.eval s_j)
      (Classical.choose (exists_adapted_subdivision X 𝒰 hcover (H.eval s_j))) S_bot
      (Classical.choose_spec (exists_adapted_subdivision X 𝒰 hcover (H.eval s_j))) hS_bot
  have h_desc_top : my_desc_map X 𝒰 hcover hfinite_intersections s (H.eval s_j1) =
      my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS_top :=
    my_desc_map_well_defined X 𝒰 hcover hfinite_intersections s (H.eval s_j1)
      (Classical.choose (exists_adapted_subdivision X 𝒰 hcover (H.eval s_j1))) S_top
      (Classical.choose_spec (exists_adapted_subdivision X 𝒰 hcover (H.eval s_j1))) hS_top
  have h_univ_bot : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS_bot =
      my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS_bot n t_i h_ti_strict_mono rfl covers hcover_mem h_range_bot' := by
    exact my_map_from_adapted_subdivision_universal X 𝒰 hcover hfinite_intersections s hS_bot t_i h_ti_strict_mono rfl covers hcover_mem h_range_bot'
  have h_univ_top : my_map_from_adapted_subdivision X 𝒰 hcover hfinite_intersections s hS_top =
      my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS_top n t_i h_ti_strict_mono rfl covers hcover_mem h_range_top' := by
    exact my_map_from_adapted_subdivision_universal X 𝒰 hcover hfinite_intersections s hS_top t_i h_ti_strict_mono rfl covers hcover_mem h_range_top'
  -- Step 4: Conclude
  let mk_x_obj := desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk x)
  let mk_y_obj := desc_functor_obj X 𝒰 hcover s (FundamentalGroupoid.mk y)
  have h_bot_eq0 : p_objs 0 = mk_x_obj := by
    dsimp only [p_objs, mk_x_obj]
    have h : (H.eval s_j) 0 = x := by
      have h1 : (H.eval s_j) 0 = x := h_eval0 s_j
      exact h1
    rw [h_ti0, h] <;> rfl
  have h_bot_eq_last : p_objs (Fin.last n) = mk_y_obj := by
    dsimp only [p_objs, mk_y_obj]
    have h : (H.eval s_j) 1 = y := by
      have h1 : (H.eval s_j) 1 = y := h_eval1 s_j
      exact h1
    rw [h_ti1, h] <;> rfl
  have h_top_eq0 : q_objs 0 = mk_x_obj := by
    dsimp only [q_objs, mk_x_obj]
    have h : (H.eval s_j1) 0 = x := by
      have h1 : (H.eval s_j1) 0 = x := h_eval0 s_j1
      exact h1
    rw [h_ti0, h] <;> rfl
  have h_top_eq_last : q_objs (Fin.last n) = mk_y_obj := by
    dsimp only [q_objs, mk_y_obj]
    have h : (H.eval s_j1) 1 = y := by
      have h1 : (H.eval s_j1) 1 = y := h_eval1 s_j1
      exact h1
    rw [h_ti1, h] <;> rfl
  have h_eq0_trans : h_bot_eq0.symm.trans h_eq0 = h_top_eq0.symm := by
    dsimp only [h_bot_eq0, h_eq0, h_top_eq0]
    <;> rfl
  have h_eq0' : eqToHom h_bot_eq0.symm ≫ eqToHom h_eq0 = eqToHom h_top_eq0.symm := by
    have h2 : eqToHom h_bot_eq0.symm ≫ eqToHom h_eq0 = eqToHom (h_bot_eq0.symm.trans h_eq0) := by
      exact eqToHom_trans (Eq.symm h_bot_eq0) h_eq0
    rw [h2, h_eq0_trans]
  have h_eq_last_trans : (h_eq_last.symm).trans h_bot_eq_last = h_top_eq_last := by
    dsimp only [h_eq_last, h_bot_eq_last, h_top_eq_last]
    <;> rfl
  have h_eq_last' : eqToHom h_eq_last.symm ≫ eqToHom h_bot_eq_last = eqToHom h_top_eq_last := by
    have h2 : eqToHom h_eq_last.symm ≫ eqToHom h_bot_eq_last = eqToHom ((h_eq_last.symm).trans h_bot_eq_last) := by
      exact eqToHom_trans (Eq.symm h_eq_last) h_bot_eq_last
    rw [h2, h_eq_last_trans]
  have h_main_bot : my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS_bot n t_i h_ti_strict_mono rfl covers hcover_mem h_range_bot' =
      eqToHom h_bot_eq0.symm ≫ comp_list n p_objs f_bottom ≫ eqToHom h_bot_eq_last := by
    simp [my_map_from_adapted_subdivision_with_covers, h_bot_eq0, h_bot_eq_last] <;> rfl
  have h_main_top : my_map_from_adapted_subdivision_with_covers X 𝒰 hcover hfinite_intersections s hS_top n t_i h_ti_strict_mono rfl covers hcover_mem h_range_top' =
      eqToHom h_top_eq0.symm ≫ comp_list n q_objs f_top ≫ eqToHom h_top_eq_last := by
    simp [my_map_from_adapted_subdivision_with_covers, h_top_eq0, h_top_eq_last] <;> rfl
  have h_last_decomp : eqToHom h_bot_eq_last = eqToHom h_eq_last ≫ eqToHom h_top_eq_last := by
    rw [←eqToHom_trans] <;> congr <;> exact Eq.trans h_eq_last h_top_eq_last
  have h_final : eqToHom h_bot_eq0.symm ≫ comp_list n p_objs f_bottom ≫ eqToHom h_bot_eq_last =
      eqToHom h_top_eq0.symm ≫ comp_list n q_objs f_top ≫ eqToHom h_top_eq_last := by
    have h1 : eqToHom h_bot_eq0.symm ≫ comp_list n p_objs f_bottom ≫ eqToHom h_bot_eq_last =
        eqToHom h_bot_eq0.symm ≫ comp_list n p_objs f_bottom ≫ (eqToHom h_eq_last ≫ eqToHom h_top_eq_last) := by
      rw [h_last_decomp]
    rw [h1]
    have h2 : eqToHom h_bot_eq0.symm ≫ comp_list n p_objs f_bottom ≫ (eqToHom h_eq_last ≫ eqToHom h_top_eq_last) =
        eqToHom h_bot_eq0.symm ≫ (comp_list n p_objs f_bottom ≫ eqToHom h_eq_last) ≫ eqToHom h_top_eq_last := by
      simp [Category.assoc] <;> rfl
    rw [h2]
    have h3 : eqToHom h_bot_eq0.symm ≫ (comp_list n p_objs f_bottom ≫ eqToHom h_eq_last) ≫ eqToHom h_top_eq_last =
        eqToHom h_bot_eq0.symm ≫ (eqToHom h_eq0 ≫ comp_list n q_objs f_top) ≫ eqToHom h_top_eq_last := by
      rw [h_chain2]
    rw [h3]
    have h4 : eqToHom h_bot_eq0.symm ≫ (eqToHom h_eq0 ≫ comp_list n q_objs f_top) ≫ eqToHom h_top_eq_last =
        (eqToHom h_bot_eq0.symm ≫ eqToHom h_eq0) ≫ comp_list n q_objs f_top ≫ eqToHom h_top_eq_last := by
      simp [Category.assoc] <;> rfl
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
-/

end

end
