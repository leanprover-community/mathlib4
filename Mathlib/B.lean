import Mathlib

-- Comment this to get a working version
import Mathlib.A

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "Triangle" => Fin 3 → ℝ²
local notation "Segment" => Fin 2 → ℝ²

-- This code replaces "import FormalBook.A" and makes the last simp work.

open foo

namespace bar

lemma linear_combination_det_last {n : ℕ} {x y : ℝ²} {P : Fin n → ℝ²} {α : Fin n → ℝ}
    (hα : ∑ i, α i = 1) :
  det (fun | 0 => x | 1 => y | 2 => (∑ i, α i • P i)) =
  ∑ i, (α i * det (fun | 0 => x | 1 => y | 2 => (P i))) := by sorry

end bar

example (n : ℕ) (x y : ℝ²) (P : Fin n → ℝ²) (α : Fin n → ℝ) (hα : ∑ i, α i = 1) :
    foo.linear_combination_det_last (n := n) (x := x) (y := y) (P := P) (α := α) hα =
    bar.linear_combination_det_last hα := rfl

lemma linear_combination_det_first {n : ℕ} {y z : ℝ²} {P : Fin n → ℝ²} {α : Fin n → ℝ}
    (hα : ∑ i, α i = 1) :
  det (fun | 0 => (∑ i, α i • P i) | 1 => y | 2 => z) =
  ∑ i, (α i * det (fun | 0 => (P i) | 1 => y | 2 => z)) := by sorry

lemma linear_combination_det_middle {n : ℕ} {x z : ℝ²} {P : Fin n → ℝ²} {α : Fin n → ℝ}
    (hα : ∑ i, α i = 1) :
  det (fun | 0 => x | 1 => (∑ i, α i • P i) | 2 => z) =
  ∑ i, (α i * det (fun | 0 => x | 1 => (P i) | 2 => z)) := by sorry

 lemma det_zero_perm {T : Triangle} (hT  : det T = 0) :
    ∀ i j k, det (fun | 0 => T i | 1 => T j | 2 => T k) = 0 := by sorry

lemma det_0_triangle_imp_triv {T : Triangle} (hT : det T = 0) :
    ∀ x y z, x ∈ closed_hull T → y ∈ closed_hull T → z ∈ closed_hull T →
      det (fun | 0 => x | 1 => y | 2 => z) = 0 := by
  intro x y z ⟨_, ⟨_, hαx⟩ , hx⟩ ⟨_, ⟨_, hαy⟩ , hy⟩ ⟨_, ⟨_, hαz⟩ , hz⟩
  rw [←hx, ← hy, ←hz, linear_combination_det_first hαx]
  simp [linear_combination_det_middle hαy]
  simp [foo.linear_combination_det_last hαz] -- this simp breaks
  -- simp [bar.linear_combination_det_last hαz] -- this simp works
  simp [det_zero_perm hT, mul_zero]





#print foo.linear_combination_det_last
/-
theorem foo.linear_combination_det_last : ∀ {n : ℕ} {x y : ℝ²} {P : Fin n → ℝ²} {α : Fin n → ℝ},
  ∑ i : Fin n, α i = 1 →
    (det fun x_1 ↦
        match x_1 with
        | 0 => x
        | 1 => y
        | 2 => ∑ i : Fin n, α i • P i) =
      ∑ i : Fin n,
        α i *
          det fun x_1 ↦
            match x_1 with
            | 0 => x
            | 1 => y
            | 2 => P i :=
fun {n} {x y} {P} {α} hα ↦ sorry
-/
#print bar.linear_combination_det_last
/-
theorem bar.linear_combination_det_last : ∀ {n : ℕ} {x y : ℝ²} {P : Fin n → ℝ²} {α : Fin n → ℝ},
  ∑ i : Fin n, α i = 1 →
    (det fun x_1 ↦
        match x_1 with
        | 0 => x
        | 1 => y
        | 2 => ∑ i : Fin n, α i • P i) =
      ∑ i : Fin n,
        α i *
          det fun x_1 ↦
            match x_1 with
            | 0 => x
            | 1 => y
            | 2 => P i :=
fun {n} {x y} {P} {α} hα ↦ sorry
-/

