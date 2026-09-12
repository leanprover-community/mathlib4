module

public import Mathlib
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.PathHelpers
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.RectangleHomotopy

@[expose] public section

set_option maxHeartbeats 500000

open TopologicalSpace

open scoped unitInterval

universe u

variable {X : Type u} [TopologicalSpace X]

namespace RectangleBoundaryHomotopy

/-- Linear interpolation from a to b, where s : I is the parameter. -/
def lerp_I (a b : I) (ha_le_b : (a : ℝ) ≤ (b : ℝ)) (s : I) : I :=
  ⟨(a : ℝ) + (s : ℝ) * ((b : ℝ) - (a : ℝ)), by
    have h_diff_nonneg : 0 ≤ (b : ℝ) - (a : ℝ) := by exact sub_nonneg.mpr ha_le_b
    have h1 : 0 ≤ (a : ℝ) + (s : ℝ) * ((b : ℝ) - (a : ℝ)) := by
      have h_s_nonneg : 0 ≤ (s : ℝ) := s.prop.1
      nlinarith [a.prop.1]
    have h2 : (a : ℝ) + (s : ℝ) * ((b : ℝ) - (a : ℝ)) ≤ 1 := by
      have h_s_le_one : (s : ℝ) ≤ 1 := s.prop.2
      nlinarith [b.prop.2]
    exact ⟨h1, h2⟩⟩

@[simp] lemma lerp_I_zero (a b : I) (ha_le_b : (a : ℝ) ≤ (b : ℝ)) :
    lerp_I a b ha_le_b 0 = a := by
  apply Subtype.ext
  simp [lerp_I] <;> ring

@[simp] lemma lerp_I_one (a b : I) (ha_le_b : (a : ℝ) ≤ (b : ℝ)) :
    lerp_I a b ha_le_b 1 = b := by
  apply Subtype.ext
  simp [lerp_I] <;> ring

lemma continuous_lerp_I (a b : I) (ha_le_b : (a : ℝ) ≤ (b : ℝ)) :
    Continuous (lerp_I a b ha_le_b) := by
  apply Continuous.subtype_mk
  continuity

/-- The bottom edge of the rectangle [a,b] × [c,d]: from H(a,c) to H(b,c). -/
def bottom_edge (H : C(I × I, X)) (a b c : I) (ha_le_b : (a : ℝ) ≤ (b : ℝ)) :
    Path (H (a, c)) (H (b, c)) :=
  let s_lerp := lerp_I a b ha_le_b
  have h1 : Continuous s_lerp := continuous_lerp_I a b ha_le_b
  have h2 : Continuous (fun (_ : I) => c) := continuous_const
  have h_cont : Continuous (fun s : I => (s_lerp s, c)) :=
    Continuous.prodMk h1 h2
  let f : C(I, I × I) := ⟨fun s : I => (s_lerp s, c), h_cont⟩
  let cmap : C(I, X) := H.comp f
  ⟨cmap, by simp [s_lerp, f, cmap], by simp [s_lerp, f, cmap]⟩

/-- The right edge of the rectangle [a,b] × [c,d]: from H(b,c) to H(b,d). -/
def right_edge (H : C(I × I, X)) (b c d : I) (hc_le_d : (c : ℝ) ≤ (d : ℝ)) :
    Path (H (b, c)) (H (b, d)) :=
  let t_lerp := lerp_I c d hc_le_d
  have h1 : Continuous (fun (_ : I) => b) := continuous_const
  have h2 : Continuous t_lerp := continuous_lerp_I c d hc_le_d
  have h_cont : Continuous (fun t : I => (b, t_lerp t)) :=
    Continuous.prodMk h1 h2
  let f : C(I, I × I) := ⟨fun t : I => (b, t_lerp t), h_cont⟩
  let cmap : C(I, X) := H.comp f
  ⟨cmap, by simp [t_lerp, f, cmap], by simp [t_lerp, f, cmap]⟩

/-- The left edge of the rectangle [a,b] × [c,d]: from H(a,c) to H(a,d). -/
def left_edge (H : C(I × I, X)) (a c d : I) (hc_le_d : (c : ℝ) ≤ (d : ℝ)) :
    Path (H (a, c)) (H (a, d)) :=
  let t_lerp := lerp_I c d hc_le_d
  have h1 : Continuous (fun (_ : I) => a) := continuous_const
  have h2 : Continuous t_lerp := continuous_lerp_I c d hc_le_d
  have h_cont : Continuous (fun t : I => (a, t_lerp t)) :=
    Continuous.prodMk h1 h2
  let f : C(I, I × I) := ⟨fun t : I => (a, t_lerp t), h_cont⟩
  let cmap : C(I, X) := H.comp f
  ⟨cmap, by simp [t_lerp, f, cmap], by simp [t_lerp, f, cmap]⟩

/-- The top edge of the rectangle [a,b] × [c,d]: from H(a,d) to H(b,d). -/
def top_edge (H : C(I × I, X)) (a b d : I) (ha_le_b : (a : ℝ) ≤ (b : ℝ)) :
    Path (H (a, d)) (H (b, d)) :=
  let s_lerp := lerp_I a b ha_le_b
  have h1 : Continuous s_lerp := continuous_lerp_I a b ha_le_b
  have h2 : Continuous (fun (_ : I) => d) := continuous_const
  have h_cont : Continuous (fun s : I => (s_lerp s, d)) :=
    Continuous.prodMk h1 h2
  let f : C(I, I × I) := ⟨fun s : I => (s_lerp s, d), h_cont⟩
  let cmap : C(I, X) := H.comp f
  ⟨cmap, by simp [s_lerp, f, cmap], by simp [s_lerp, f, cmap]⟩

lemma exists_rectangle_boundary_homotopy_in_U
    (H : C(I × I, X))
    (a b c d : I)
    (ha_le_b : (a : ℝ) ≤ (b : ℝ))
    (hc_le_d : (c : ℝ) ≤ (d : ℝ))
    (U : Set X)
    (hU : ∀ (p : I × I), (a : ℝ) ≤ (p.1 : ℝ) → (p.1 : ℝ) ≤ (b : ℝ) →
      (c : ℝ) ≤ (p.2 : ℝ) → (p.2 : ℝ) ≤ (d : ℝ) → H p ∈ U) :
    ∃ (H_rect : Path.Homotopy
        ((bottom_edge H a b c ha_le_b).trans (right_edge H b c d hc_le_d))
        ((left_edge H a c d hc_le_d).trans (top_edge H a b d ha_le_b))),
      ∀ (p : I × I), H_rect p ∈ U := by
  let s_lerp := lerp_I a b ha_le_b
  let t_lerp := lerp_I c d hc_le_d
  have h_s_cont : Continuous s_lerp := continuous_lerp_I a b ha_le_b
  have h_t_cont : Continuous t_lerp := continuous_lerp_I c d hc_le_d
  have h_f_cont : Continuous (fun p : I × I => (s_lerp p.1, t_lerp p.2)) :=
    Continuous.prodMk (h_s_cont.comp continuous_fst) (h_t_cont.comp continuous_snd)
  let f : C(I × I, I × I) := ⟨fun p : I × I => (s_lerp p.1, t_lerp p.2), h_f_cont⟩
  let G := H.comp f
  have hG_in_U : ∀ (q : I × I), G q ∈ U := by
    intro q
    have h1 : G q = H (f q) := by rfl
    rw [h1]
    have h_s_between : (a : ℝ) ≤ (s_lerp q.1 : ℝ) ∧ (s_lerp q.1 : ℝ) ≤ (b : ℝ) := by
      have h_val : (s_lerp q.1 : ℝ) = (a : ℝ) + (q.1 : ℝ) * ((b : ℝ) - (a : ℝ)) := by rfl
      rw [h_val]
      have h_diff_nonneg : 0 ≤ (b : ℝ) - (a : ℝ) := by exact sub_nonneg.mpr ha_le_b
      have h_s_nonneg : 0 ≤ (q.1 : ℝ) := q.1.prop.1
      have h_s_le_one : (q.1 : ℝ) ≤ 1 := q.1.prop.2
      have h1 : 0 ≤ (q.1 : ℝ) * ((b : ℝ) - (a : ℝ)) := mul_nonneg h_s_nonneg h_diff_nonneg
      have h2 : (q.1 : ℝ) * ((b : ℝ) - (a : ℝ)) ≤ (b : ℝ) - (a : ℝ) := by
        have h : (q.1 : ℝ) * ((b : ℝ) - (a : ℝ)) ≤ 1 * ((b : ℝ) - (a : ℝ)) := by
          gcongr
        simpa using h
      constructor
      · linarith
      · linarith
    have h_t_between : (c : ℝ) ≤ (t_lerp q.2 : ℝ) ∧ (t_lerp q.2 : ℝ) ≤ (d : ℝ) := by
      have h_val : (t_lerp q.2 : ℝ) = (c : ℝ) + (q.2 : ℝ) * ((d : ℝ) - (c : ℝ)) := by rfl
      rw [h_val]
      have h_diff_nonneg : 0 ≤ (d : ℝ) - (c : ℝ) := by exact sub_nonneg.mpr hc_le_d
      have h_t_nonneg : 0 ≤ (q.2 : ℝ) := q.2.prop.1
      have h_t_le_one : (q.2 : ℝ) ≤ 1 := q.2.prop.2
      have h1 : 0 ≤ (q.2 : ℝ) * ((d : ℝ) - (c : ℝ)) := mul_nonneg h_t_nonneg h_diff_nonneg
      have h2 : (q.2 : ℝ) * ((d : ℝ) - (c : ℝ)) ≤ (d : ℝ) - (c : ℝ) := by
        have h : (q.2 : ℝ) * ((d : ℝ) - (c : ℝ)) ≤ 1 * ((d : ℝ) - (c : ℝ)) := by
          gcongr
        simpa using h
      constructor
      · linarith
      · linarith
    exact hU (f q) h_s_between.1 h_s_between.2 h_t_between.1 h_t_between.2
  let bottom_cmap := G.comp ⟨fun t : I => (0, t), by continuity⟩
  let right_cmap := G.comp ⟨fun s : I => (s, 1), by continuity⟩
  let left_cmap := G.comp ⟨fun s : I => (s, 0), by continuity⟩
  let top_cmap := G.comp ⟨fun t : I => (1, t), by continuity⟩
  let γ_bottom : Path (G (0, 0)) (G (0, 1)) := ⟨bottom_cmap, by rfl, by rfl⟩
  let γ_right : Path (G (0, 1)) (G (1, 1)) := ⟨right_cmap, by rfl, by rfl⟩
  let γ_left : Path (G (0, 0)) (G (1, 0)) := ⟨left_cmap, by rfl, by rfl⟩
  let γ_top : Path (G (1, 0)) (G (1, 1)) := ⟨top_cmap, by rfl, by rfl⟩
  have h_bottom : ∀ (t : I), γ_bottom t = G (0, t) := by intro t; rfl
  have h_right : ∀ (s : I), γ_right s = G (s, 1) := by intro s; rfl
  have h_left : ∀ (s : I), γ_left s = G (s, 0) := by intro s; rfl
  have h_top : ∀ (t : I), γ_top t = G (1, t) := by intro t; rfl
  have h_main : ∃ (H_rect : Path.Homotopy (γ_bottom.trans γ_right) (γ_left.trans γ_top)),
      ∀ (p : I × I), H_rect p ∈ U :=
    RectangleHomotopy.rectangle_boundary_homotopy_edges G γ_bottom γ_right γ_left γ_top
      h_bottom h_right h_left h_top U hG_in_U
  rcases h_main with ⟨H_rect, hH_rect_U⟩
  have h0 : H (a, c) = G (0, 0) := by
    have h_s : s_lerp 0 = a := lerp_I_zero a b ha_le_b
    have h_t : t_lerp 0 = c := lerp_I_zero c d hc_le_d
    have h : G (0, 0) = H (s_lerp 0, t_lerp 0) := by rfl
    rw [h, h_s, h_t] <;> rfl
  have h1 : H (b, d) = G (1, 1) := by
    have h_s : s_lerp 1 = b := lerp_I_one a b ha_le_b
    have h_t : t_lerp 1 = d := lerp_I_one c d hc_le_d
    have h : G (1, 1) = H (s_lerp 1, t_lerp 1) := by rfl
    rw [h, h_s, h_t] <;> rfl
  have h_mid1 : H (b, c) = G (1, 0) := by
    have h_s : s_lerp 1 = b := lerp_I_one a b ha_le_b
    have h_t : t_lerp 0 = c := lerp_I_zero c d hc_le_d
    have h : G (1, 0) = H (s_lerp 1, t_lerp 0) := by rfl
    rw [h, h_s, h_t] <;> rfl
  have h_mid2 : H (a, d) = G (0, 1) := by
    have h_s : s_lerp 0 = a := lerp_I_zero a b ha_le_b
    have h_t : t_lerp 1 = d := lerp_I_one c d hc_le_d
    have h : G (0, 1) = H (s_lerp 0, t_lerp 1) := by rfl
    rw [h, h_s, h_t] <;> rfl
  have h_left_eq1 : γ_left.cast h0 h_mid1 = bottom_edge H a b c ha_le_b := by
    have h : ∀ (s : I), (γ_left.cast h0 h_mid1) s = (bottom_edge H a b c ha_le_b) s := by
      intro s
      have h1 : (γ_left.cast h0 h_mid1) s = γ_left s := by rfl
      rw [h1]
      have h2 : γ_left s = G (s, 0) := by rfl
      rw [h2]
      have h3 : G (s, 0) = H (s_lerp s, t_lerp 0) := by rfl
      rw [h3]
      have h4 : t_lerp 0 = c := lerp_I_zero c d hc_le_d
      rw [h4] <;> rfl
    have h' : ⇑(γ_left.cast h0 h_mid1) = ⇑(bottom_edge H a b c ha_le_b) := by
      funext s; exact h s
    exact Path.ext h'
  have h_left_eq2 : γ_top.cast h_mid1 h1 = right_edge H b c d hc_le_d := by
    have h : ∀ (t : I), (γ_top.cast h_mid1 h1) t = (right_edge H b c d hc_le_d) t := by
      intro t
      have h1 : (γ_top.cast h_mid1 h1) t = γ_top t := by rfl
      rw [h1]
      have h2 : γ_top t = G (1, t) := by rfl
      rw [h2]
      have h3 : G (1, t) = H (s_lerp 1, t_lerp t) := by rfl
      rw [h3]
      have h4 : s_lerp 1 = b := lerp_I_one a b ha_le_b
      rw [h4] <;> rfl
    have h' : ⇑(γ_top.cast h_mid1 h1) = ⇑(right_edge H b c d hc_le_d) := by
      funext t; exact h t
    exact Path.ext h'
  have h_left_eq' : (γ_left.trans γ_top).cast h0 h1 =
      (bottom_edge H a b c ha_le_b).trans (right_edge H b c d hc_le_d) := by
    rw [Path.cast_trans γ_left γ_top h0 h_mid1 h1]
    rw [h_left_eq1, h_left_eq2]
  have h_bottom_eq1 : γ_bottom.cast h0 h_mid2 = left_edge H a c d hc_le_d := by
    have h : ∀ (t : I), (γ_bottom.cast h0 h_mid2) t = (left_edge H a c d hc_le_d) t := by
      intro t
      have h1 : (γ_bottom.cast h0 h_mid2) t = γ_bottom t := by rfl
      rw [h1]
      have h2 : γ_bottom t = G (0, t) := by rfl
      rw [h2]
      have h3 : G (0, t) = H (s_lerp 0, t_lerp t) := by rfl
      rw [h3]
      have h4 : s_lerp 0 = a := lerp_I_zero a b ha_le_b
      rw [h4] <;> rfl
    have h' : ⇑(γ_bottom.cast h0 h_mid2) = ⇑(left_edge H a c d hc_le_d) := by
      funext t; exact h t
    exact Path.ext h'
  have h_bottom_eq2 : γ_right.cast h_mid2 h1 = top_edge H a b d ha_le_b := by
    have h : ∀ (s : I), (γ_right.cast h_mid2 h1) s = (top_edge H a b d ha_le_b) s := by
      intro s
      have h1 : (γ_right.cast h_mid2 h1) s = γ_right s := by rfl
      rw [h1]
      have h2 : γ_right s = G (s, 1) := by rfl
      rw [h2]
      have h3 : G (s, 1) = H (s_lerp s, t_lerp 1) := by rfl
      rw [h3]
      have h4 : t_lerp 1 = d := lerp_I_one c d hc_le_d
      rw [h4] <;> rfl
    have h' : ⇑(γ_right.cast h_mid2 h1) = ⇑(top_edge H a b d ha_le_b) := by
      funext s; exact h s
    exact Path.ext h'
  have h_bottom_eq' : (γ_bottom.trans γ_right).cast h0 h1 =
      (left_edge H a c d hc_le_d).trans (top_edge H a b d ha_le_b) := by
    rw [Path.cast_trans γ_bottom γ_right h0 h_mid2 h1]
    rw [h_bottom_eq1, h_bottom_eq2]
  -- Take symm first, then cast
  let H_rect_symm : Path.Homotopy (γ_left.trans γ_top) (γ_bottom.trans γ_right) := H_rect.symm
  have hH_rect_symm_U : ∀ (p : I × I), H_rect_symm p ∈ U := by
    intro p
    have h_main : ∀ (q : Path.Homotopy (γ_bottom.trans γ_right) (γ_left.trans γ_top)),
        (∀ (x : I × I), q x ∈ U) → ∀ (x : I × I), q.symm x ∈ U := by
      intro q hq x
      exact?
    exact h_main H_rect hH_rect_U p
  let H_rect_symm' : Path.Homotopy ((γ_left.trans γ_top).cast h0 h1) ((γ_bottom.trans γ_right).cast h0 h1) :=
    H_rect_symm.pathCast h0 h1
  have hH_rect_symm'_U : ∀ (p : I × I), H_rect_symm' p ∈ U := by
    intro p
    have h : H_rect_symm' p = H_rect_symm p := by rfl
    rw [h]
    exact hH_rect_symm_U p
  let H_final : Path.Homotopy
      ((bottom_edge H a b c ha_le_b).trans (right_edge H b c d hc_le_d))
      ((left_edge H a c d hc_le_d).trans (top_edge H a b d ha_le_b)) :=
    H_rect_symm'.cast h_left_eq' h_bottom_eq'
  have h_final_range : ∀ (p : I × I), H_final p ∈ U := by
    intro p
    have h : H_final p = H_rect_symm' p := by rfl
    rw [h]
    exact hH_rect_symm'_U p
  exact ⟨H_final, h_final_range⟩

end RectangleBoundaryHomotopy

end
