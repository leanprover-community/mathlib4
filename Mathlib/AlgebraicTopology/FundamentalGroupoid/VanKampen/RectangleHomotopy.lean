module

public import Mathlib

@[expose] public section

open TopologicalSpace

open scoped unitInterval

universe u

noncomputable section

variable {X : Type u} [TopologicalSpace X]

namespace RectangleHomotopy

/-- The identity path in I, from 0 to 1. -/
def id_path_I : Path (0 : I) (1 : I) where
  toFun := fun t : I => t
  continuous_toFun := continuous_id
  source' := by simp
  target' := by simp

/-- First component homotopy: refl;id → id;refl -/
def h1 : Path.Homotopy
    ((Path.refl (0 : I)).trans id_path_I)
    (id_path_I.trans (Path.refl (1 : I))) :=
  Path.Homotopy.trans (Path.Homotopy.reflTrans id_path_I)
    (Path.Homotopy.symm (Path.Homotopy.transRefl id_path_I))

/-- Second component homotopy: id;refl → refl;id -/
def h2 : Path.Homotopy
    (id_path_I.trans (Path.refl (1 : I)))
    ((Path.refl (0 : I)).trans id_path_I) :=
  Path.Homotopy.trans (Path.Homotopy.transRefl id_path_I)
    (Path.Homotopy.symm (Path.Homotopy.reflTrans id_path_I))

/-- The two boundary paths in I × I. -/
def p1 : Path ((0 : I), (0 : I)) ((1 : I), (1 : I)) :=
  Path.prod ((Path.refl (0 : I)).trans id_path_I) (id_path_I.trans (Path.refl (1 : I)))

def p2 : Path ((0 : I), (0 : I)) ((1 : I), (1 : I)) :=
  Path.prod (id_path_I.trans (Path.refl (1 : I))) ((Path.refl (0 : I)).trans id_path_I)

/-- The standard square homotopy in I × I. -/
def square_homotopy : Path.Homotopy p1 p2 :=
  Path.Homotopic.prodHomotopy h1 h2

/-- Given a continuous map G : I × I → X, we get a homotopy between
    the two boundary paths by mapping the square homotopy along G. -/
def rectangle_boundary_homotopy (G : C(I × I, X)) :
    Path.Homotopy (p1.map G.continuous) (p2.map G.continuous) :=
  square_homotopy.map G

/-- The rectangle boundary homotopy stays within the image of G. -/
lemma rectangle_boundary_homotopy_range (G : C(I × I, X)) (U : Set X)
    (hG : ∀ (p : I × I), G p ∈ U) :
    ∀ (p : I × I), (rectangle_boundary_homotopy G) p ∈ U := by
  intro p
  have h_eq : (rectangle_boundary_homotopy G) p = G (square_homotopy p) := by
    rfl
  rw [h_eq]
  exact hG (square_homotopy p)

/-- Given edge paths matching the boundary of G, we get a homotopy between
    bottom.trans right and left.trans top, staying within U. -/
theorem rectangle_boundary_homotopy_edges
    (G : C(I × I, X))
    (γ_bottom : Path (G (0, 0)) (G (0, 1)))
    (γ_right : Path (G (0, 1)) (G (1, 1)))
    (γ_left : Path (G (0, 0)) (G (1, 0)))
    (γ_top : Path (G (1, 0)) (G (1, 1)))
    (h_bottom : ∀ (t : I), γ_bottom t = G (0, t))
    (h_right : ∀ (s : I), γ_right s = G (s, 1))
    (h_left : ∀ (s : I), γ_left s = G (s, 0))
    (h_top : ∀ (t : I), γ_top t = G (1, t))
    (U : Set X)
    (hG : ∀ (p : I × I), G p ∈ U) :
    ∃ (H_rect : Path.Homotopy (γ_bottom.trans γ_right) (γ_left.trans γ_top)),
      ∀ (p : I × I), H_rect p ∈ U := by
  let H_raw := rectangle_boundary_homotopy G
  have h_range_raw : ∀ (p : I × I), H_raw p ∈ U :=
    rectangle_boundary_homotopy_range G U hG
  have h_eq1 : (p1.map G.continuous) = γ_bottom.trans γ_right := by
    have h_main : ∀ (t : I), (p1.map G.continuous) t = (γ_bottom.trans γ_right) t := by
      intro t
      have h_lhs : (p1.map G.continuous) t = G (p1 t) := by rfl
      rw [h_lhs]
      let p1_fst := (Path.refl (0 : I)).trans id_path_I
      let p1_snd := id_path_I.trans (Path.refl (1 : I))
      have h_p1_def : p1 = Path.prod p1_fst p1_snd := by rfl
      have h_p1t : p1 t = (p1_fst t, p1_snd t) := by
        rw [h_p1_def]
        exact congrFun (Path.prod_coe p1_fst p1_snd) t
      rw [h_p1t]
      by_cases h : (t : ℝ) ≤ 1 / 2
      · -- Case t ≤ 1/2: first part of p1 is bottom edge (s stays at 0, t goes from 0 to 1)
        have h2t : 0 ≤ 2 * (t : ℝ) ∧ 2 * (t : ℝ) ≤ 1 := by
          constructor <;> linarith [t.prop.1, t.prop.2]
        let t2 : I := ⟨2 * (t : ℝ), h2t.1, h2t.2⟩
        have ht2 : (t2 : ℝ) = 2 * (t : ℝ) := by rfl
        have h_fst : p1_fst t = (0 : I) := by
          dsimp only [p1_fst]
          rw [Path.trans_apply, dif_pos h]
          <;> simp [id_path_I]
          <;> rfl
        have h_snd : p1_snd t = t2 := by
          dsimp only [p1_snd]
          rw [Path.trans_apply, dif_pos h]
          <;> exact Subtype.ext ht2
        have h_goal1 : G (p1_fst t, p1_snd t) = G (0, t2) := by
          rw [h_fst, h_snd]
        rw [h_goal1]
        have h_rhs : (γ_bottom.trans γ_right) t = γ_bottom t2 := by
          rw [Path.trans_apply, dif_pos h]
          <;> congr <;> exact Subtype.ext ht2
        rw [h_rhs, h_bottom t2]
        <;> rfl
      · -- Case t > 1/2: second part of p1 is right edge (s goes from 0 to 1, t stays at 1)
        have h' : 1 / 2 ≤ (t : ℝ) := by linarith
        have h2t1 : 0 ≤ 2 * (t : ℝ) - 1 ∧ 2 * (t : ℝ) - 1 ≤ 1 := by
          constructor <;> linarith [t.prop.1, t.prop.2]
        let t2 : I := ⟨2 * (t : ℝ) - 1, h2t1.1, h2t1.2⟩
        have ht2 : (t2 : ℝ) = 2 * (t : ℝ) - 1 := by rfl
        have h_fst : p1_fst t = t2 := by
          dsimp only [p1_fst]
          rw [Path.trans_apply, dif_neg h]
          <;> exact Subtype.ext ht2
        have h_snd : p1_snd t = (1 : I) := by
          dsimp only [p1_snd]
          rw [Path.trans_apply, dif_neg h]
          <;> simp [id_path_I]
          <;> rfl
        have h_goal1 : G (p1_fst t, p1_snd t) = G (t2, 1) := by
          rw [h_fst, h_snd]
        rw [h_goal1]
        have h_rhs : (γ_bottom.trans γ_right) t = γ_right t2 := by
          rw [Path.trans_apply, dif_neg h]
          <;> congr <;> exact Subtype.ext ht2
        rw [h_rhs, h_right t2]
        <;> rfl
    have h_fun : (fun t : I => (p1.map G.continuous) t) = (fun t : I => (γ_bottom.trans γ_right) t) := by
      funext t
      exact h_main t
    exact Path.ext h_fun
  have h_eq2 : (p2.map G.continuous) = γ_left.trans γ_top := by
    have h_main : ∀ (t : I), (p2.map G.continuous) t = (γ_left.trans γ_top) t := by
      intro t
      have h_lhs : (p2.map G.continuous) t = G (p2 t) := by rfl
      rw [h_lhs]
      let p2_fst := id_path_I.trans (Path.refl (1 : I))
      let p2_snd := (Path.refl (0 : I)).trans id_path_I
      have h_p2_def : p2 = Path.prod p2_fst p2_snd := by rfl
      have h_p2t : p2 t = (p2_fst t, p2_snd t) := by
        rw [h_p2_def]
        exact congrFun (Path.prod_coe p2_fst p2_snd) t
      rw [h_p2t]
      by_cases h : (t : ℝ) ≤ 1 / 2
      · -- Case t ≤ 1/2: first part of p2 is left edge (s goes from 0 to 1, t stays at 0)
        have h2t : 0 ≤ 2 * (t : ℝ) ∧ 2 * (t : ℝ) ≤ 1 := by
          constructor <;> linarith [t.prop.1, t.prop.2]
        let t2 : I := ⟨2 * (t : ℝ), h2t.1, h2t.2⟩
        have ht2 : (t2 : ℝ) = 2 * (t : ℝ) := by rfl
        have h_fst : p2_fst t = t2 := by
          dsimp only [p2_fst]
          rw [Path.trans_apply, dif_pos h]
          <;> exact Subtype.ext ht2
        have h_snd : p2_snd t = (0 : I) := by
          dsimp only [p2_snd]
          rw [Path.trans_apply, dif_pos h]
          <;> simp [id_path_I]
          <;> rfl
        have h_goal1 : G (p2_fst t, p2_snd t) = G (t2, 0) := by
          rw [h_fst, h_snd]
        rw [h_goal1]
        have h_rhs : (γ_left.trans γ_top) t = γ_left t2 := by
          rw [Path.trans_apply, dif_pos h]
          <;> congr <;> exact Subtype.ext ht2
        rw [h_rhs, h_left t2]
        <;> rfl
      · -- Case t > 1/2: second part of p2 is top edge (s stays at 1, t goes from 0 to 1)
        have h' : 1 / 2 ≤ (t : ℝ) := by linarith
        have h2t1 : 0 ≤ 2 * (t : ℝ) - 1 ∧ 2 * (t : ℝ) - 1 ≤ 1 := by
          constructor <;> linarith [t.prop.1, t.prop.2]
        let t2 : I := ⟨2 * (t : ℝ) - 1, h2t1.1, h2t1.2⟩
        have ht2 : (t2 : ℝ) = 2 * (t : ℝ) - 1 := by rfl
        have h_fst : p2_fst t = (1 : I) := by
          dsimp only [p2_fst]
          rw [Path.trans_apply, dif_neg h]
          <;> simp [id_path_I]
          <;> rfl
        have h_snd : p2_snd t = t2 := by
          dsimp only [p2_snd]
          rw [Path.trans_apply, dif_neg h]
          <;> exact Subtype.ext ht2
        have h_goal1 : G (p2_fst t, p2_snd t) = G (1, t2) := by
          rw [h_fst, h_snd]
        rw [h_goal1]
        have h_rhs : (γ_left.trans γ_top) t = γ_top t2 := by
          rw [Path.trans_apply]
          rw [dif_neg h]
          <;> congr <;> exact Subtype.ext ht2
        rw [h_rhs, h_top t2]
        <;> rfl
    have h_fun : (fun t : I => (p2.map G.continuous) t) = (fun t : I => (γ_left.trans γ_top) t) := by
      funext t
      exact h_main t
    exact Path.ext h_fun
  let H_rect : Path.Homotopy (γ_bottom.trans γ_right) (γ_left.trans γ_top) :=
    (H_raw.cast h_eq1 h_eq2)
  have h_range : ∀ (p : I × I), H_rect p ∈ U := by
    intro p
    have h_eq : H_rect p = H_raw p := by rfl
    rw [h_eq]
    exact h_range_raw p
  exact ⟨H_rect, h_range⟩

end RectangleHomotopy

end

end
