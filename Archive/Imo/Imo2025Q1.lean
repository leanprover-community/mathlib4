/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers (Problem statement), Yizheng Zhu (Solution)
-/
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

/-!
# IMO 2025 Q1

A line in the plane is called sunny if it is not parallel to any of the x-axis, the y-axis,
and the line x + y = 0.

Let n ⩾ 3 be a given integer. Determine all nonnegative integers k such that there exist n distinct
lines in the plane satisfying both of the following:

• for all positive integers a and b with a + b ⩽ n + 1, the point (a, b) is on at least one of the
lines; and

• exactly k of the n lines are sunny.

The answer is 0, 1, and 3.

For existence, it is easy to construct solutions k = 0, 1, 3 for n = 3,
and for n > 3, add diagonal lines x + y = j + 1 for 3 < j ≤ n based on the n = 3 solutions.

To show any such k must be in {0, 1, 3}, we firstly show that it is true with n = 3, and
then for n > 3, we show that one of the edge lines x = 1, y = 1, x + y = n + 1 must be in the
given set of lines, which reduces the problem to n - 1.

The key lemma is that if none of the edge lines x = 1, y = 1, x + y = n + 1 are in the given
set of lines, then all the n points on the same edge must be on different lines.
-/


open scoped Affine Finset
open Module

namespace Imo2025Q1

/-- The `x`-axis, as an affine subspace. -/
noncomputable def xAxis : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) where
  carrier := {p | p 1 = 0}
  smul_vsub_vadd_mem c p₁ p₂ p₃ hp₁ hp₂ hp₃ := by simp_all

/-- The `y`-axis, as an affine subspace. -/
noncomputable def yAxis : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) where
  carrier := {p | p 0 = 0}
  smul_vsub_vadd_mem c p₁ p₂ p₃ hp₁ hp₂ hp₃ := by simp_all

/- The line `x+y=0`, as an affine subspace. -/
noncomputable def linexy0 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) where
  carrier := {p | p 0 + p 1 = 0}
  smul_vsub_vadd_mem c p₁ p₂ p₃ hp₁ hp₂ hp₃ := by
    simp only [Fin.isValue, vsub_eq_sub, vadd_eq_add, Set.mem_setOf_eq, PiLp.add_apply,
      PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    suffices c * (p₁ 0 + p₁ 1 - (p₂ 0 + p₂ 1)) + (p₃ 0 + p₃ 1) = 0 by
      rw [← this]
      ring
    simp_all

/-- The condition on lines in the problem. -/
def Sunny (s : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) : Prop :=
   ¬ s ∥ xAxis ∧ ¬ s ∥ yAxis ∧ ¬ s ∥ linexy0

/-- The answer to be determined. -/
def answer : (Set.Ici 3) → Set ℕ := fun _ => {0, 1, 3}

section LineOnPlane

/-- The 2-dimensional plane -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Affine subspaces of the plane (i.e. ∅, point, line, plane) -/
abbrev AffSubOfPlane := AffineSubspace ℝ Plane

/-- Two vectors are equal iff their x and y coordinates are equal. -/
lemma vec_eq (x₁ x₂ y₁ y₂ : ℝ) : !₂[x₁, y₁] = !₂[x₂, y₂] ↔ (x₁ = x₂ ∧ y₁ = y₂) :=
  ⟨fun h ↦ by apply_fun (fun w ↦ (w.ofLp 0, w.ofLp 1)) at h; simpa using h, by simp +contextual⟩

/-- Get the x coordinate of a vector. -/
lemma vec_repr_x (x y : ℝ) : !₂[x, y] 0 = x := by simp
/-- Get the y coordinate of a vector. -/
lemma vec_repr_y (x y : ℝ) : !₂[x, y] 1 = y := by simp

/-- Represent a vector as a pair of real numbers -/
lemma vec_repr (x : Plane) : x = !₂[x 0, x 1] := FinVec.etaExpand_eq _ |>.symm

/-- Multiply a vector by a scalar. -/
lemma vec_mul (k x y : ℝ) : k • !₂[x, y] = !₂[k * x, k * y] := FinVec.etaExpand_eq _ |>.symm

/-- Compute the difference of two vectors -/
lemma vec_sub (x₁ y₁ x₂ y₂ : ℝ) : !₂[x₁, y₁] - !₂[x₂, y₂] = !₂[x₁ - x₂, y₁ - y₂] :=
  FinVec.etaExpand_eq _ |>.symm

/-- The "line" `ax + by + c = 0`. ("line" means except for the degenerate case `a = 0 ∧ b = 0`)
Note: We don't enforce `a ≠ 0 ∨ b ≠ 0`. -/
noncomputable def line (a b c : ℝ) : AffSubOfPlane where
  carrier := {p | a * p 0 + b * p 1 + c = 0}
  smul_vsub_vadd_mem r p₁ p₂ p₃ hp₁ hp₂ hp₃ := by
    simp only [Fin.isValue, vsub_eq_sub, vadd_eq_add, Set.mem_setOf_eq, PiLp.add_apply,
      PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    grind

/-- Check if a point `(x, y)` belongs to the line `a * x + b * y + c = 0`. -/
lemma point_on_line (x y a b c : ℝ) : !₂[x, y] ∈ line a b c ↔ a * x + b * y + c = 0 := by
  simp [line, ← SetLike.mem_coe, SetLike.coe]

/-- The line `a * x + b * y + c = 0` is nonempty when `a` and `b` are not both zero -/
lemma line_nonempty (a b c : ℝ) (h : a ≠ 0 ∨ b ≠ 0) :
    (SetLike.coe (line a b c)).Nonempty := by
  simp only [Set.Nonempty, SetLike.mem_coe]
  obtain ha | hb := h
  · use !₂[-c / a, 0]
    rw [point_on_line]
    field_simp; ring
  · use !₂[0, -c / b]
    rw [point_on_line]
    field_simp; ring

/-- `(-b, a)` is the direction of the line `a * x + b * y + c = 0`
when `a` and `b` are not both zero -/
lemma line_direction (a b c : ℝ) (h : a ≠ 0 ∨ b ≠ 0) (w : Plane) :
    w ∈ AffineSubspace.direction (line a b c) ↔ ∃ (k : ℝ), k • !₂[-b, a] = w := by
  have hv_nonempty := line_nonempty a b c h
  constructor
  · intro hw
    obtain ⟨w₁, hw₁, w₂, hw₂, hw₁₂⟩ :=
      (AffineSubspace.mem_direction_iff_eq_vsub hv_nonempty _).mp hw
    rw [vec_repr w₁, point_on_line] at hw₁
    rw [vec_repr w₂, point_on_line] at hw₂
    simp only [vsub_eq_sub] at hw₁₂
    obtain ha | hb := h
    · use (w₁ 1 - w₂ 1) / a
      · rw [hw₁₂]
        nth_rw 2 [vec_repr w₁, vec_repr w₂]
        rw [vec_mul, vec_sub, vec_eq]
        constructor <;> (field_simp; try linarith)
    · use (w₂ 0 - w₁ 0) / b
      · rw [hw₁₂]
        nth_rw 2 [vec_repr w₁, vec_repr w₂]
        rw [vec_mul, vec_sub, vec_eq]
        constructor <;> (field_simp; try linarith)
  · intro ⟨k, hkw⟩
    rw [AffineSubspace.mem_direction_iff_eq_vsub hv_nonempty]
    simp only [Set.Nonempty, SetLike.mem_coe] at hv_nonempty
    obtain ⟨v₁, hv₁⟩ := hv_nonempty
    use v₁
    refine ⟨hv₁, v₁ - w, ?_, by simp⟩
    rw [vec_repr v₁, point_on_line] at hv₁
    rw [vec_repr v₁, ← hkw, vec_mul, vec_sub, point_on_line]
    ring_nf; exact hv₁

/-- The rank of the line `a * x + b * y + c = 0` is `1` when `a` and `b` are not both zero -/
lemma line_rank (a b c : ℝ) (h : a ≠ 0 ∨ b ≠ 0) : finrank ℝ (line a b c).direction = 1 := by
  have hv_mem : !₂[-b, a] ∈ AffineSubspace.direction (line a b c) := by
    rw [line_direction (h := h)]
    use 1; simp
  rw [finrank_eq_one_iff']
  refine ⟨⟨!₂[-b, a], hv_mem⟩, by simp; tauto, ?_⟩
  simp only [SetLike.mk_smul_mk, Subtype.forall, Subtype.mk.injEq]
  exact fun w ↦ (line_direction a b c h w).mp

/-- The coeffecients of a line a * x + b * y + c = 0 -/
structure LineCoeffs where
  a : ℝ
  b : ℝ
  c : ℝ

/-- Build a line from a `LineCoeffs` -/
noncomputable def line' (coeff : LineCoeffs) := line coeff.a coeff.b coeff.c

def edgeCoeffs (n : ℕ) (d : Fin 3) : LineCoeffs := match d with
| 0 => ⟨1, 0, -1⟩
| 1 => ⟨0, 1, -1⟩
| 2 => ⟨1, 1, -(n + 1)⟩

/-- The three lines on the edges of the triangular integer grid, each side having n points:
`x - 1 = 0`; `y - 1 = 0`; `x + y - (n + 1) = 0`.
These lines are named `edgeLine n 0`, `edgeLine n 1`, `edgeLine n 2`, resp. -/
noncomputable def edgeLine (n : ℕ) (d : Fin 3) := line' (edgeCoeffs n d)

/-- The y axis is the line `x = 0`. -/
lemma y_ax_line : line 1 0 0 = yAxis := by simp [line, yAxis]

/-- The x axis is the line `y = 0` -/
lemma x_ax_line : line 0 1 0 = xAxis := by simp [line, xAxis]

/-- The line `x + y = 0` -/
lemma xy0_line : line 1 1 0 = linexy0 := by simp [line, linexy0]

/-- Preparation lemma for checking if two lines are parallel -/
lemma line_para' (a b a' b' : ℝ) (h' : a' ≠ 0 ∨ b' ≠ 0)
    (hab : a * b' = a' * b) (w : Plane) :
    (∃ (k : ℝ), k • !₂[-b, a] = w) → (∃ (k : ℝ), k • !₂[-b', a'] = w) := by
  intro ⟨k, hk₁⟩
  rw [vec_mul, vec_repr w, vec_eq] at hk₁
  obtain ha | hb := h'
  · use k * a / a'
    rw [vec_mul, vec_repr w, vec_eq]
    grind
  · use k * b / b'
    rw [vec_mul, vec_repr w, vec_eq]
    grind

/-- Two non-degenerate lines `a * x + b * y + c = 0` and `a' * x + b' * y + c = 0`
are parallel iff `a * b' = a' * b`. -/
lemma line_para (a b c a' b' c' : ℝ) (h : a ≠ 0 ∨ b ≠ 0) (h' : a' ≠ 0 ∨ b' ≠ 0) :
    line a b c ∥ line a' b' c' ↔ a * b' = a' * b := by
  rw [AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot]
  constructor
  · intro ⟨hp, hb⟩
    let w := !₂[-b, a]
    have : w ∈ AffineSubspace.direction (line a b c) := by
      rw [line_direction a b c h w]
      use 1
      simp [w]
    rw [hp, line_direction a' b' c' h' w] at this
    grind [vec_mul, vec_eq]
  · intro hab
    constructor
    · ext w
      rw [line_direction a b c h w, line_direction a' b' c' h' w]
      exact ⟨line_para' a b a' b' h' hab w, line_para' a' b' a b h hab.symm w⟩
    · have := line_nonempty a b c h
      have := line_nonempty a' b' c' h'
      simp_all [Set.nonempty_iff_ne_empty, ← AffineSubspace.coe_eq_bot_iff]

/-- If the line `a * x + b * y + c` is parallel to `L`,
and both lines go through `(x₁, y₁)`, `(x₂, y₂)`,
then `a * (x₂ - x₁) + b * (y₂ - y₁) = 0`. -/
lemma line_para_two_points (a b c : ℝ) (h : a ≠ 0 ∨ b ≠ 0) (L : AffSubOfPlane) (x₁ y₁ x₂ y₂ : ℝ) :
    line a b c ∥ L → !₂[x₁, y₁] ∈ L → !₂[x₂, y₂] ∈ L → a * (x₂ - x₁) + b * (y₂ - y₁) = 0 := by
  by_cases hxy : x₁ = x₂ ∧ y₁ = y₂
  · simp [show x₂ - x₁ = 0 by simp [hxy], show y₂ - y₁ = 0 by simp [hxy]]
  · rw [AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot]
    intro ⟨hp, _⟩ h₁ h₂
    let w := !₂[x₂ - x₁, y₂ - y₁]
    have : w ∈ AffineSubspace.direction L := by
      rw [AffineSubspace.mem_direction_iff_eq_vsub _]
      · use !₂[x₂, y₂]; simp only [h₂, vsub_eq_sub, true_and]
        use !₂[x₁, y₁]; simp only [h₁, true_and]
        simp [w, vec_sub]
      · simp only [Set.Nonempty, SetLike.mem_coe]; use !₂[x₁, y₁]
    rw [← hp, line_direction (h := by tauto)] at this
    grind [vec_mul, vec_eq]

/-- If the linex `a * x + b * y + c = 0` and `a' * x + b' * y + c = 0` are equal,
then `a * b' = a' * b ∧ a * c' = a' * c ∧ b * c' = b' * c`. -/
lemma line_eq_check (a b c a' b' c' : ℝ) (h : a ≠ 0 ∨ b ≠ 0) (h' : a' ≠ 0 ∨ b' ≠ 0)
    (heq : line a b c = line a' b' c') :
    a * b' = a' * b ∧ a * c' = a' * c ∧ b * c' = b' * c := by
  have hab : a * b' = a' * b := by rw [← line_para a b c a' b' c' h h', heq]
  rw [AffineSubspace.ext_iff, Set.ext_iff] at heq
  refine ⟨hab, ?_⟩
  by_cases ha : a = 0
  · specialize heq !₂[0, -c / b]
    grind [AffineSubspace.mem_coe, AffineSubspace.mem_coe, point_on_line, point_on_line]
  · constructor
    · specialize heq !₂[-c / a, 0]
      grind [AffineSubspace.mem_coe, AffineSubspace.mem_coe, point_on_line, point_on_line]
    · by_cases hb : b = 0
      · grind
      · specialize heq !₂[0, -c / b]
        grind [AffineSubspace.mem_coe, AffineSubspace.mem_coe, point_on_line, point_on_line]

/-- Preparation lemma for `get_line_eq`. -/
lemma line_contains (L L' : AffSubOfPlane) (hL : finrank ℝ L.direction = 1) (a b : Plane)
    (hab : a ≠ b) (ha : a ∈ L) (hb : b ∈ L) (ha' : a ∈ L') (hb' : b ∈ L') : L ≤ L' := by
  rw [AffineSubspace.le_def']
  intro x hx
  obtain ⟨v, _, hv⟩ := finrank_eq_one_iff'.mp hL
  have L_nonempty : (SetLike.coe L).Nonempty := by simp only [Set.Nonempty, SetLike.mem_coe]; use a
  obtain ⟨k, hk⟩ :=
    hv ⟨a -ᵥ b, by rw [AffineSubspace.mem_direction_iff_eq_vsub L_nonempty]; use a; simp [ha, hb]⟩
  obtain ⟨q, hq⟩ :=
    hv ⟨x -ᵥ a, by rw [AffineSubspace.mem_direction_iff_eq_vsub L_nonempty]; use x; simp [hx, ha]⟩
  apply_fun (·.val) at hk; simp only [SetLike.val_smul, vsub_eq_sub] at hk
  apply_fun (·.val) at hq; simp only [SetLike.val_smul, vsub_eq_sub] at hq
  have hk₀ : k ≠ 0 := by
    intro hkC; simp only [hkC, zero_smul] at hk
    grind
  have x_a_expr : x - a = (q / k) • (a - b) := by rw [← hk, ← hq, ← mul_smul]; congr 1; field_simp
  have := L'.smul_vsub_vadd_mem (q / k) (p₁ := a) (p₂ := b) (p₃ := a) ha' hb' ha'
  simpa [← x_a_expr] using this

/-- If both of the two non-degenerate lines `L` and `L'` go through two different points
`a` and `b`, then `L = L'`. -/
lemma get_line_eq
    (L L' : AffSubOfPlane) (hL : finrank ℝ L.direction = 1) (hL' : finrank ℝ L'.direction = 1)
    (a b : Plane) (hab : a ≠ b)
    (ha : a ∈ L) (hb : b ∈ L) (ha' : a ∈ L') (hb' : b ∈ L') : L = L' := by
  have h₁ := line_contains L L' hL a b hab ha hb ha' hb'
  have h₂ := line_contains L' L hL' a b hab ha' hb' ha hb
  rw [AffineSubspace.le_def] at *
  rw [AffineSubspace.ext_iff]
  exact Set.Subset.antisymm h₁ h₂

end LineOnPlane

/-- The decidable predicate `Sunny`. -/
noncomputable def sunnyPred : DecidablePred Sunny := Classical.decPred _
/-- The decidable equality predicate `L = L'` for `(L L' : AffSubOfPlane)`. -/
noncomputable def eqAffSubOfPlane : DecidableEq AffSubOfPlane := Classical.decEq _

/-- Check if the line `a * x + b * y + c = 0` is sunny or not. -/
lemma sunny_slope (a b c : ℝ) (h : a ≠ 0 ∨ b ≠ 0) :
    Sunny (line a b c) ↔ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b := by
  dsimp only [Sunny]
  rw [← x_ax_line, ← y_ax_line, ← xy0_line, line_para, line_para, line_para]
  · grind
  all_goals (first | assumption | simp)

/-- The integer grid consisting of (a, b), where a, b are positive integers and a + b ≤ n + 1. -/
def grid (n : ℕ) : Set Plane :=
  {x : Plane | ∃ (a b : ℕ), x 0 = a ∧ x 1 = b ∧ 0 < a ∧ 0 < b ∧ a + b ≤ (n : ℕ) + 1}

/-- Check if (a, b) is in `grid n` for natural numbers a, b. -/
lemma point_in_grid (n : ℕ) (a b : ℕ) :
    !₂[(a : ℝ), (b : ℝ)] ∈ grid n ↔ 0 < a ∧ 0 < b ∧ a + b ≤ n + 1 := by simp [grid]

/-- The configuration of a finise set of lines going through a set of points in the plane. -/
structure coverConfig where
  /-- The finite set of lines that go through a set of points -/
  lines : Finset AffSubOfPlane
  /-- The set of points in the plane to be covered -/
  g : Set Plane
  /-- The number of lines -/
  n : ℕ
  /-- The number of sunny lines -/
  nS : ℕ
  /-- Line number correctness -/
  lines_count : #lines = n
  /-- Every line has rank 1 -/
  lines_rank : ∀ l ∈ lines, finrank ℝ l.direction = 1
  /-- every point in `g` is covered by a line in `lines` -/
  lines_cover : ∀ x ∈ g, ∃ l ∈ lines, x ∈ l
  /-- Sunny line number correctness -/
  sunny_count : have := sunnyPred; #{l ∈ lines | Sunny l} = nS

lemma coverConfig.nS_leq_n (C : coverConfig) : C.nS ≤ C.n := by
  simp [← C.sunny_count, ← C.lines_count, Finset.card_filter_le]

/-- `shiftSet v g` is the result of shifting every point in `g` by the vector `v`. -/
def shiftSet (v : Plane) (g : Set Plane) : Set Plane :=
  Set.image (AffineEquiv.constVAdd ℝ Plane v) g

def gridShift (d : Fin 3) : Plane := match d with
  | 0 => !₂[-1, 0]
  | 1 => !₂[0, -1]
  | 2 => !₂[0, 0]

/-- After removing an edge from `grid (n + 1)` and appropriate shifting,
the resulting set is `grid n`.
Remove `edgeLine (n + 1) 0` (i.e. left edge) -> shift by `(-1, 0)`.
Remove `edgeLine (n + 1) 1` (i.e. bottom edge) -> shift by `(0, -1)`.
Remove `edgeLine (n + 1) 2` (i.e. diagonal edge) -> shift by `(0, 0)` (i.e. no shift). -/
lemma grid_shift (n : ℕ) (d : Fin 3) :
    shiftSet (gridShift d) (grid (n + 1) \ (edgeLine (n + 1) d)) = grid n := by
  ext x
  simp only [shiftSet, AffineEquiv.constVAdd_apply, vadd_eq_add, Set.image_add_left, grid,
    Fin.isValue, exists_and_left, Set.preimage_diff, Set.preimage_setOf_eq, PiLp.add_apply,
    PiLp.neg_apply, Set.mem_diff, Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
  constructor
  · intro ⟨⟨a, ha, b, hb, ha₀, hb₀, hab⟩, h₂⟩
    simp only [edgeLine, line'] at h₂
    fin_cases d
    all_goals
      simp only [line, Fin.isValue, edgeCoeffs, one_mul, zero_mul, add_zero, gridShift, ←
        SetLike.mem_coe, SetLike.coe, Set.mem_setOf_eq, PiLp.add_apply, PiLp.neg_apply,
        PiLp.toLp_apply, Matrix.cons_val_zero, neg_neg, add_neg_cancel_comm, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, zero_add] at h₂
      simp only [gridShift, Fin.isValue, PiLp.toLp_apply, Matrix.cons_val_zero, neg_neg, neg_zero,
        zero_add] at ha
      simp only [gridShift, Fin.isValue, PiLp.toLp_apply, Matrix.cons_val_one, neg_neg,
        Matrix.cons_val_fin_one, neg_zero, zero_add] at hb
    · have : a ≠ 1 := by intro hC; simp only [hC, Fin.isValue, Nat.cast_one,
        add_eq_left] at ha; contradiction
      refine ⟨a - 1, ?_, b, ?_⟩
      · rw [show a = a - 1 + 1 by omega] at ha
        grind
      · constructor <;> (try (first | assumption | omega))
    · have : b ≠ 1 := by intro hC; simp only [hC, Fin.isValue, Nat.cast_one,
      add_eq_left] at hb; rw [hb] at h₂; simp at h₂
      refine ⟨a, ha, b - 1, ?_, ?_⟩
      · rw [show b = b - 1 + 1 by omega] at hb
        grind
      · constructor <;> (try (first | assumption | omega))
    · have : a + b ≠ n + 2 := by
        intro hC; rw [ha, hb] at h₂; norm_cast at h₂; omega
      refine ⟨a, ha, b, hb, ?_⟩
      constructor <;> (try (first | assumption | omega))
  · intro ⟨a, ha, b, hb, ha₀, hb₀, hab⟩
    fin_cases d
    · constructor
      · use 1 + a
        simp only [gridShift, Fin.isValue, PiLp.toLp_apply, Matrix.cons_val_zero, neg_neg, ha,
          Nat.cast_add, Nat.cast_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, neg_zero,
          zero_add, add_pos_iff, zero_lt_one, ha₀, or_self, true_and]
        use b
        simp only [Fin.isValue, hb, hb₀, true_and]
        omega
      · simp only [edgeLine, line', line, Fin.isValue, edgeCoeffs, one_mul, zero_mul, add_zero,
          gridShift, ← SetLike.mem_coe, SetLike.coe, Set.mem_setOf_eq, PiLp.add_apply,
          PiLp.neg_apply, PiLp.toLp_apply, Matrix.cons_val_zero, neg_neg, add_neg_cancel_comm]
        intro hC; rw [hC] at ha; norm_cast at ha; omega
    · constructor
      · use a
        simp only [gridShift, Fin.isValue, PiLp.toLp_apply, Matrix.cons_val_zero, neg_zero, ha,
          zero_add, Matrix.cons_val_one, Matrix.cons_val_fin_one, neg_neg, true_and]
        use 1 + b
        simp only [Fin.isValue, hb, Nat.cast_add, Nat.cast_one, add_pos_iff, zero_lt_one,
          hb₀, or_self, true_and]
        omega
      · simp only [edgeLine, line', line, Fin.isValue, edgeCoeffs, zero_mul, one_mul, zero_add,
          gridShift, ← SetLike.mem_coe, SetLike.coe, Set.mem_setOf_eq, PiLp.add_apply,
          PiLp.neg_apply, PiLp.toLp_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one, neg_neg,
          add_neg_cancel_comm]
        intro hC; rw [hC] at hb; norm_cast at hb; omega
    · constructor
      · use a
        simp only [gridShift, Fin.isValue, PiLp.toLp_apply, Matrix.cons_val_zero, neg_zero, ha,
          zero_add, Matrix.cons_val_one, Matrix.cons_val_fin_one, true_and]
        use b
        simp only [Fin.isValue, hb, hb₀, true_and]
        omega
      · simp only [edgeLine, line', line, Fin.isValue, edgeCoeffs, Nat.cast_add, Nat.cast_one,
        neg_add_rev, one_mul, gridShift, ← SetLike.mem_coe, SetLike.coe, Set.mem_setOf_eq,
        PiLp.add_apply, PiLp.neg_apply, PiLp.toLp_apply, Matrix.cons_val_zero, neg_zero, zero_add,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
        intro hC; rw [ha, hb] at hC; norm_cast at hC; omega

/-- After removing the diagonal edge from `grid (n + 1)` , the resulting set is `grid n`. -/
lemma grid_remove_diag (n : ℕ) : grid (n + 1) \ (edgeLine (n + 1) 2) = grid n := by
  rw [← grid_shift n 2, gridShift]
  set g := grid (n + 1) \ ↑(edgeLine (n + 1) 2)
  simp only [shiftSet, AffineEquiv.constVAdd_apply, vadd_eq_add, Set.image_add_left]
  ext x; simp only [Set.mem_preimage]
  rw [show -!₂[0, 0] + x = x by simp]

/-- `shiftLineMap v L` shifts the line L by the vector `v`. -/
def shiftLineMap (v : Plane) (L : AffSubOfPlane) : AffSubOfPlane :=
  AffineSubspace.map (AffineEquiv.constVAdd ℝ Plane v) L

/-- The preparation lemma on composing two line-shifts. -/
lemma affine_trans (e : Plane ≃ᵃ[ℝ] Plane) (e' : Plane ≃ᵃ[ℝ] Plane) :
    (AffineEquiv.trans e e').toAffineMap = e'.toAffineMap.comp e.toAffineMap := by simp

/-- `shiftLineMap v` is the injective map `AffSubOfPlane ↪ AffSubOfPlane`
that shifts by the vector `v`. -/
def shiftLine (v : Plane) : AffSubOfPlane ↪ AffSubOfPlane := ⟨
  shiftLineMap v,
  by
    dsimp only [Function.Injective]; intro L₁ L₂ h
    apply_fun (shiftLineMap (-v)) at h
    dsimp only [shiftLineMap] at h
    rw [AffineSubspace.map_map, AffineSubspace.map_map,
      ← affine_trans, ← AffineEquiv.constVAdd_add] at h
    simpa using h
⟩

/-- The shift of a line is parallel to the original line. -/
lemma shift_para (v : Plane) (L : AffSubOfPlane) :  L ∥ shiftLine v L := by
  dsimp only [shiftLine, Function.Embedding.coeFn_mk, shiftLineMap, AffineSubspace.Parallel]; use v

/-- `shiftLines v lines` is the collection of `shiftLine v L` for `L ∈ lines`. -/
def shiftLines (v : Plane) (lines : Finset AffSubOfPlane) : Finset AffSubOfPlane :=
  Finset.map (shiftLine v) lines

/-- `shiftLine (-v)` is the inverse of `shiftLine v`. -/
lemma shift_line_inv (v : Plane) (L : AffSubOfPlane) : (shiftLine (-v)) ((shiftLine v) L) = L := by
  simp [shiftLine, Function.Embedding.coeFn_mk, shiftLineMap, AffineSubspace.map_map,
    ← affine_trans, ← AffineEquiv.constVAdd_add]

/-- If `L` is sunny, then so is its shift. -/
lemma shift_sunny (v : Plane) (L : AffSubOfPlane) : Sunny L → Sunny (shiftLine v L) := by
  rw [Sunny, Sunny]
  have (L' : AffSubOfPlane) : L ∥ L' ↔ shiftLine v L ∥ L' :=
    ⟨fun h ↦ AffineSubspace.Parallel.trans (shift_para _ _).symm h,
      fun h ↦ AffineSubspace.Parallel.trans (shift_para _ _) h⟩
  rw [← this, ← this, ← this]
  tauto

/-- Shift a `coverConfig` by the vector `v`. -/
def coverConfig.shift (C : coverConfig) (v : Plane) : coverConfig where
  lines := shiftLines v C.lines
  g := shiftSet v C.g
  n := C.n
  nS := C.nS
  lines_count := by simp [shiftLines, C.lines_count]
  lines_rank := by
    simp only [shiftLines, Finset.mem_map, forall_exists_index, and_imp,forall_apply_eq_imp_iff₂]
    intro l hl
    exact (shift_para v l).direction_eq ▸ C.lines_rank l hl
  lines_cover := by
    simp only [shiftLines, Finset.mem_map, exists_exists_and_eq_and]
    intro x hx
    simp only [shiftSet, AffineEquiv.constVAdd_apply, vadd_eq_add, Set.image_add_left,
      Set.mem_preimage] at hx
    obtain ⟨l, _, _⟩ := C.lines_cover (-v + x) hx
    refine ⟨l, by assumption, ?_⟩
    simp only [shiftLine, Function.Embedding.coeFn_mk, shiftLineMap, AffineSubspace.mem_map,
      AffineEquiv.coe_toAffineMap, AffineEquiv.constVAdd_apply, vadd_eq_add]
    exact ⟨-v + x, by assumption, by simp⟩
  sunny_count := by
    intro
    simp only [shiftLines, ← C.sunny_count]
    symm
    have := eqAffSubOfPlane
    apply Finset.card_bij'
      (fun L ↦ (fun _ ↦ shiftLine v L)) (fun L' ↦ (fun _ ↦ shiftLine (-v) L'))
    · intro L hL
      simp only [Finset.mem_filter] at hL
      simp only [Finset.mem_filter, Finset.mem_map']
      exact ⟨by tauto, by apply shift_sunny; tauto⟩
    · intro L' hL'; simp only [Finset.mem_filter, Finset.mem_map] at hL'
      obtain ⟨⟨L, _, hL₂⟩, hS'⟩ := hL'
      simp only [Finset.mem_filter, hS', shift_sunny, and_true]
      rwa [← hL₂, shift_line_inv]
    · intros; rw [shift_line_inv]
    · intros; nth_rw 1 [show v = -(-v) by simp]; rw [shift_line_inv]

/-- Remove a line `L` from a `coverConfig`. -/
noncomputable def coverConfig.removeLine (C : coverConfig) (L : AffSubOfPlane) (hL : L ∈ C.lines)
(hS : ¬Sunny L) : coverConfig where
  lines := have := eqAffSubOfPlane; C.lines.erase L
  g := C.g \ L
  n := C.n - 1
  nS := C.nS
  lines_count := by simp [C.lines_count, hL]
  lines_rank := fun L' hL' ↦ C.lines_rank L'
    (by simp only [Finset.mem_erase, ne_eq] at hL'; tauto)
  lines_cover := by
    intro x hx
    simp only [Set.mem_diff, SetLike.mem_coe] at hx
    obtain ⟨L', hL'⟩ := C.lines_cover x (by tauto)
    use L'; simp only [Finset.mem_erase, ne_eq, hL', and_true]
    intro hC
    rw [hC] at hL'
    tauto
  sunny_count := by
    rw [← C.sunny_count]
    congr 1
    ext L'; simp only [Finset.mem_filter, Finset.mem_erase, ne_eq, and_congr_left_iff,
      and_iff_right_iff_imp]
    intro hS' hL' hC
    rw [hC] at hS'
    contradiction

/-- A `coverConfig` with the additional requirement that the set of points to be covered is
`grid n` -/
structure coverGridConfig extends coverConfig where
  /-- A proof of the fact that the set of points to be covered is `grid n` -/
  g_is_grid : g = grid n

/-- The three edge lines of a the grid point to be covered in a `coverGridConfig` -/
noncomputable def coverGridConfig.edgeLine (C : coverGridConfig) :=
  Imo2025Q1.edgeLine C.n

/-- If a `coverGridConfig` contains a line on the edge, remove the edge and shift it to a smaller
`coverGridConfig` -/
noncomputable def reduce (C : coverGridConfig) (d : Fin 3) (hd : C.edgeLine d ∈ C.lines) :
    coverGridConfig where
  tocoverConfig :=
    (C.tocoverConfig.removeLine (C.edgeLine d) hd edge_not_sunny).shift (gridShift d)
  g_is_grid := by
    simp only [coverConfig.shift, coverConfig.removeLine]
    have : C.n > 0 := by simp [← C.lines_count]; use C.edgeLine d
    have : C.n = C.n - 1 + 1 := by omega
    convert grid_shift (C.n - 1) d
    · rw [C.g_is_grid, ← this]
    · rw [coverGridConfig.edgeLine, ← this]
  where edge_not_sunny := by {
    rw [coverGridConfig.edgeLine, edgeLine, line', sunny_slope] <;>
    fin_cases d <;> simp [edgeCoeffs]}

/-- Applying `coverGridConfig.reduce` decrements `n` by `1` and doesn't change `nS`. -/
lemma coverGridConfig.reduce_count (C : coverGridConfig) (d : Fin 3) (hd : C.edgeLine d ∈ C.lines) :
    (reduce C d hd).n = C.n - 1 ∧ (reduce C d hd).nS = C.nS := by
  simp [reduce, coverConfig.shift, coverConfig.removeLine]

/-- Given reals numbers `M > 0` and `a, b, c ∈ (0, M)`, the points
`(1, a + 1)`, `(b + 1, 1)`, `(c + 1, M - c + 1)` are not colinear. -/
lemma not_colinear (L : AffSubOfPlane) (M a b c : ℝ) :
    finrank ℝ L.direction = 1 → M > 0 → 0 < a → a < M → 0 < b → b < M → 0 < c → c < M →
    !₂[1, a + 1] ∈ L → !₂[b + 1, 1] ∈ L → !₂[c + 1, M - c + 1] ∈ L → False := by
  intro hL hM ha₀ haM hb₀ hbM hc₀ hcM hpa hpb hpc
  have : L = line a b (-a - b - a * b) := by
    apply get_line_eq (a := !₂[1, a + 1]) (b := !₂[b + 1, 1]) <;> (try assumption)
    · apply line_rank; left; positivity
    · intro hC; rw [vec_eq] at hC; have hC := hC.left; simp only [right_eq_add] at hC; linarith
    · rw [point_on_line]; ring
    · rw [point_on_line]; ring
  rw [this, point_on_line] at hpc
  by_cases hab : b ≤ a
  · have : (0 : ℝ) > 0 := by
      calc
      _ = (a - b) * c + b * (M - a) := by linarith
      _ > (a - b) * c + b * (a - a) := by gcongr
      _ = (a - b) * c := by simp
      _ ≥ (b - b) * c := by gcongr
      _ = 0 := by simp
    linarith
  · have : a < b := by rwa [← not_le]
    have : (0 : ℝ) > 0 := by
      calc
      _ = (b - a) * (M - c) + a * (M - b) := by linarith
      _ > (b - a) * (M - c) + a * (b - b) := by gcongr
      _ = (b - a) * (M - c) := by simp
      _ ≥ (a - a) * (M - c) := by gcongr; linarith
      _ = 0 := by simp
    linarith

/-- Given natural numbers `M > 0` and `a, b, c ∈ (0, M)`, the points
`(1, a + 1)`, `(b + 1, 1)`, `(c + 1, M - c + 1)` are not colinear. -/
lemma not_colinear_nat (L : AffSubOfPlane) (M a b c : ℕ) :
    finrank ℝ L.direction = 1 → M > 0 → 0 < a → a < M → 0 < b → b < M → 0 < c → c < M →
    (!₂[1, (a + 1 : ℕ)] : Plane) ∈ L →
    (!₂[(b + 1 : ℕ), 1] : Plane) ∈ L →
    (!₂[(c + 1 : ℕ), (M - c + 1 : ℕ)] : Plane) ∈ L →
    False := by
  intros
  have: M ≥ c := by omega
  convert not_colinear L M a b c _ _ _ _ _ _ _ _ _ _ _ <;> norm_cast

/-- If `n : ℕ` and `n > 1`, if `n' : ℕ` and `n' = n - 1`, then `(n' : ℝ) + (1 : ℝ) = (n : ℝ)`. -/
lemma n_minus_plus (n : ℕ) (hn : n > 1) : (n - 1 : ℕ) + (1 : ℝ) = n := by norm_cast; omega

/-- If `L` goes through `(x₁, y₁)` and `(x₂, y₂)`, and `x₁ ≠ x₂`, `y₁ ≠ y₂`, `x₂ - x₁ ≠ y₁ - y₂`,
then `L` is sunny. -/
lemma line_sunny_two_points (L : AffSubOfPlane) (x₁ y₁ x₂ y₂ : ℝ)
    (h₁ : !₂[x₁, y₁] ∈ L) (h₂ : !₂[x₂, y₂] ∈ L)
    (hx : x₁ ≠ x₂) (hy : y₁ ≠ y₂) (hxy : x₂ - x₁ ≠ y₁ - y₂) : Sunny L := by
  rw [Sunny]
  refine ⟨x_ax_line ▸ ?_, y_ax_line ▸ ?_, xy0_line ▸ ?_⟩ <;> (intro hp; symm at hp)
  · have := line_para_two_points 0 1 0 (by simp) L x₁ y₁ x₂ y₂ hp h₁ h₂
    have : y₁ = y₂ := by linarith
    contradiction
  · have := line_para_two_points 1 0 0 (by simp) L x₁ y₁ x₂ y₂ hp h₁ h₂
    have : x₁ = x₂ := by linarith
    contradiction
  · have := line_para_two_points 1 1 0 (by simp) L x₁ y₁ x₂ y₂ hp h₁ h₂
    have : x₂ - x₁ = y₁ - y₂ := by linarith
    contradiction

section FindLines

/-- `coverGridConfig.findLine` chooses a line in `lines` that goes through `x` -/
noncomputable def coverGridConfig.findLine (C : coverGridConfig) (x : Plane) (hx : x ∈ C.g) :=
  Classical.choose (C.lines_cover x hx)

/-- `coverGridConfig.findLine` chooses a line in `lines` that goes through `x` -/
lemma coverGridConfig.find_line_correct (C : coverGridConfig) (x : Plane) (hx : x ∈ C.g) :
    C.findLine x hx ∈ C.lines ∧ x ∈ C.findLine x hx := by
  have := Classical.choose_spec (C.lines_cover x hx)
  simpa [coverGridConfig.findLine]

/-- If `findLine` finds the same line that goes through different points `x` and `y`,
and if the non-degenerate line `a * x + b * y + c = 0` passes through `x` and `y`,
then `a * x + b * y + c = 0` is in `lines`. -/
lemma coverGridConfig.find_same_line (C : coverGridConfig) (x y : Plane)
    (hx : x ∈ C.g) (hy : y ∈ C.g) (a b c : ℝ) (hxy : x ≠ y)
    (hEq : C.findLine x hx = C.findLine y hy)
    (hab : a ≠ 0 ∨ b ≠ 0)
    (hxL : x ∈ line a b c) (hyL : y ∈ line a b c) :
    line a b c ∈ C.lines := by
  let L := C.findLine x hx
  have hL : L ∈ C.lines := by dsimp only [L]; simp [find_line_correct]
  suffices L = line a b c by rwa [← this]
  apply get_line_eq (a := x) (b := y) <;> (try assumption)
  · exact C.lines_rank L hL
  · apply line_rank; assumption
  · dsimp only [L]; simp [find_line_correct]
  · dsimp only [L]; rw [hEq]; simp [find_line_correct]

/-- The points on the three edges of a `coverGridConfig` -/
def coverGridConfig.edgePoint (C : coverGridConfig) (d : Fin 3) (k : Fin C.n) : Plane :=
  match d with
  | 0 => !₂[(1 : ℕ), (k.val + 1 : ℕ)]   -- left edge
  | 1 => !₂[(k.val + 1 : ℕ), (1 : ℕ)]   -- bottom edge
  | 2 => !₂[(k.val + 1 : ℕ), (C.n - k.val : ℕ)]   -- diagonal edge

/-- The points on the three edges of a `coverGridConfig` are in its grid. -/
lemma coverGridConfig.edge_point_in_grid (C : coverGridConfig) (d : Fin 3) (i : Fin C.n) :
    C.edgePoint d i ∈ C.g := by
  rw [C.g_is_grid]
  dsimp only [edgePoint]
  fin_cases d <;> (simp only [point_in_grid]; omega)

/-- The points on the three edges of a `coverGridConfig` are on their edge lines. -/
lemma coverGridConfig.edge_point_on_line (C : coverGridConfig) (d : Fin 3) (i : Fin C.n) :
    C.edgePoint d i ∈ C.edgeLine d := by
  fin_cases d <;>
  (simp only [edgeLine, Imo2025Q1.edgeLine, line', edgeCoeffs, edgePoint, point_on_line])
  · simp
  · simp
  · ring_nf; simp

/-- `coverGridConfig.findLineEdge` chooses a line in `lines` that goes through `C.edgePoint d i`
using the function `coverGridConfig.findLine`. -/
noncomputable def coverGridConfig.findLineEdge (C : coverGridConfig) (d : Fin 3) (i : Fin C.n) :=
  C.findLine (C.edgePoint d i) (C.edge_point_in_grid d i)

/-- `coverGridConfig.findLineEdge` chooses a line in `lines` that goes through `C.edgePoint d i` -/
lemma coverGridConfig.find_line_edge_correct (C : coverGridConfig) (d : Fin 3) (i : Fin C.n) :
    C.findLineEdge d i ∈ C.lines ∧ C.edgePoint d i ∈ C.findLineEdge d i := by
  rw [findLineEdge]
  exact C.find_line_correct _ _

/-- A `coverGridConfig` with the additional requirements that `n > 1` and `lines` doesn't contain
an edge. Note: we need `n > 1` to have three corners in the grid. -/
structure coverGridNoEdgeConfig extends coverGridConfig where
  /-- A proof of the fact that  `lines` doesn't contain an edge -/
  hE : ∀ (e : Fin 3), edgeLine n e ∉ lines
  /-- A proof of the fact that `n > 1`, to have three corners in the grid -/
  hn : n > 1

/-- If `lines` does not contain an edge line of `grid n`, then on every edge, the lines chosen by
`findLineEdge` are distinct. -/
lemma coverGridNoEdgeConfig.cover_no_edge_line_inj (C : coverGridNoEdgeConfig) (d : Fin 3) :
    Function.Injective (C.findLineEdge d) := by
  dsimp only [Function.Injective]
  intro i j hij
  by_contra hC
  suffices edgeLine C.n d ∈ C.lines by have := C.hE d; contradiction
  let x := C.edgePoint d i
  let y := C.edgePoint d j
  apply C.find_same_line
    (C.edgePoint d i) (C.edgePoint d j) (C.edge_point_in_grid d i) (C.edge_point_in_grid d j)
  · dsimp only [coverGridConfig.edgePoint]; fin_cases d <;> try (
      simp only
      intro hC'; rw [vec_eq] at hC'; obtain ⟨hC'₁, hC'₂⟩ := hC'
      norm_cast at hC'₁ hC'₂
      omega )
  · assumption
  · dsimp [edgeCoeffs]; fin_cases d <;> simp
  · apply coverGridConfig.edge_point_on_line
  · apply coverGridConfig.edge_point_on_line

/-- If `lines` does not contain an edge line of `grid n`, then for every edge, every line in
`lines` must be chosen by a point on that edge. -/
lemma coverGridNoEdgeConfig.cover_no_edge_line_surj (C : coverGridNoEdgeConfig) (d : Fin 3) :
    Finset.map ⟨C.findLineEdge d, C.cover_no_edge_line_inj d⟩ Finset.univ = C.lines := by
  set R := Finset.map ⟨C.findLineEdge d, C.cover_no_edge_line_inj d⟩ Finset.univ
  have : #R = C.n := by simp [R]
  have : R ⊆ C.lines := by
    intro x hx
    simp only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and,
      R] at hx
    obtain ⟨i, hi⟩ := hx
    simp [← hi, C.find_line_edge_correct]
  apply Finset.eq_of_subset_of_card_le <;> try (first | assumption | omega)
  have := C.lines_count
  omega

def edgeEndpointCornerId (d : Fin 3) (r : Fin 2) : Fin 3 := match d, r with
  | 0, 0 => 0   -- edge 0 left corner is 0
  | 0, 1 => 1   -- edge 0 right corner is 1
  | 1, 0 => 0   -- edge 1 left corner is 0
  | 1, 1 => 2   -- edge 1 right corner is 2
  | 2, 0 => 1   -- edge 2 left corner is 1
  | 2, 1 => 2   -- edge 2 right corner is 2

def coverGridNoEdgeConfig.edgeEndpointIndex (C : coverGridNoEdgeConfig) (r : Fin 2) : Fin C.n :=
  match r with
    | 0 => ⟨0, by have := C.hn; omega⟩        -- left endpoint has index 0
    | 1 => ⟨C.n - 1, by have := C.hn; omega⟩  -- right endpoint has index C.n - 1

/-- The points on the three corners of `grid n` -/
def coverGridNoEdgeConfig.cornerPoint (C : coverGridNoEdgeConfig) (c : Fin 3) : Plane :=
  match c with
  | 0 => C.edgePoint 0 (C.edgeEndpointIndex 0)    -- lower left corner
  | 1 => C.edgePoint 0 (C.edgeEndpointIndex 1)    -- upper corner
  | 2 => C.edgePoint 1 (C.edgeEndpointIndex 1)    -- right corner

/-- Every corner of `grid n` belongs to two edgle lines. -/
lemma coverGridNoEdgeConfig.corner_point_on_edge (C : coverGridNoEdgeConfig)
  (d : Fin 3) (r : Fin 2) :
    C.cornerPoint (edgeEndpointCornerId d r) = C.edgePoint d (C.edgeEndpointIndex r) := by
  dsimp only [cornerPoint, edgeEndpointCornerId, coverGridNoEdgeConfig.edgeEndpointIndex,
    coverGridConfig.edgePoint]
  have := n_minus_plus C.n C.hn
  have : 1 = (C.n : ℝ) - (C.n - 1 : ℕ) := by
    rw [← n_minus_plus C.n C.hn]; ring
  fin_cases d <;> fin_cases r <;> (simp only; repeat rw [vec_eq]; simpa)

/-- `coverGridNoEdgeConfig.findLineCorner C c` chooses a line in `lines` that goes through
`C.cornerPoint c` using the function `findLine`. -/
noncomputable def coverGridNoEdgeConfig.findLineCorner (C : coverGridNoEdgeConfig)
  (c : Fin 3) := match c with
    | 0 => C.findLineEdge 0 (C.edgeEndpointIndex 0)
    | 1 => C.findLineEdge 0 (C.edgeEndpointIndex 1)
    | 2 => C.findLineEdge 1 (C.edgeEndpointIndex 1)

/-- `coverGridNoEdgeConfig.findLineCorner C c` chooses a line in `lines` that goes through
`C.cornerPoint c`. -/
lemma coverGridNoEdgeConfig.find_line_corner_correct (C : coverGridNoEdgeConfig)
  (c : Fin 3) :
    C.findLineCorner c ∈ C.lines ∧ C.cornerPoint c ∈ C.findLineCorner c := by
  fin_cases c <;>
    (dsimp only [findLineCorner, cornerPoint]; exact C.find_line_edge_correct  _ _)

/-- The line chosen by `findLineCorner` at each of the three corners equals to the line
chosen by `findLineEdge` at corresponding points on two edge lines. -/
lemma coverGridNoEdgeConfig.find_line_corner_eq_edge (C : coverGridNoEdgeConfig)
  (d : Fin 3) (r : Fin 2) :
    C.findLineCorner (edgeEndpointCornerId d r) = C.findLineEdge d (C.edgeEndpointIndex r) := by
  simp only [coverGridConfig.findLineEdge, edgeEndpointCornerId,
    coverGridNoEdgeConfig.findLineCorner]
  fin_cases r <;> (simp only; fin_cases d) <;> (simp only; congr 1)
  all_goals
    rw [← C.corner_point_on_edge _ _, ← C.corner_point_on_edge _ _]
    congr 1

/-- The three points chosen by `findLineCorner` are distinct. -/
lemma coverGridNoEdgeConfig.cover_no_edge_corner_distinct (C : coverGridNoEdgeConfig) :
    C.findLineCorner 0 ≠ C.findLineCorner 1 ∧
    C.findLineCorner 0 ≠ C.findLineCorner 2 ∧
    C.findLineCorner 1 ≠ C.findLineCorner 2 := by
  suffices
      C.findLineCorner (edgeEndpointCornerId 0 0) ≠ C.findLineCorner (edgeEndpointCornerId 0 1) ∧
      C.findLineCorner (edgeEndpointCornerId 1 0) ≠ C.findLineCorner (edgeEndpointCornerId 1 1) ∧
      C.findLineCorner (edgeEndpointCornerId 2 0) ≠ C.findLineCorner (edgeEndpointCornerId 2 1) by
    congr
  have := C.find_line_corner_eq_edge
  have := C.hn
  repeat' constructor
  all_goals
    rw [C.find_line_corner_eq_edge, C.find_line_corner_eq_edge]
    intro hC
    apply C.cover_no_edge_line_inj at hC
    rw [edgeEndpointIndex, edgeEndpointIndex] at hC
    apply_fun (·.val) at hC; simp only at hC
    omega

/-- `findLineCorner` is injective. -/
lemma coverGridNoEdgeConfig.cover_no_edge_corner_inj (C : coverGridNoEdgeConfig) :
    Function.Injective C.findLineCorner := by
  have := C.cover_no_edge_corner_distinct
  intro i j hij
  fin_cases i <;> fin_cases j <;> tauto

/-- The image set of `findLineCorner`. -/
noncomputable def coverGridNoEdgeConfig.corner_set (C : coverGridNoEdgeConfig) :
    Finset AffSubOfPlane :=
  Finset.map ⟨C.findLineCorner, C.cover_no_edge_corner_inj⟩ Finset.univ

/-- The members of the `corner_set`, i.e., The image set of `findLineCorner` -/
lemma coverGridNoEdgeConfig.corner_set_members (C : coverGridNoEdgeConfig) (d : Fin 3) :
    C.findLineCorner d ∈ C.corner_set := by
  simp [coverGridNoEdgeConfig.corner_set]

/-- The cardinality of the `corner_set`, i.e., The image set of `findLineCorner` -/
lemma coverGridNoEdgeConfig.corner_set_card (C : coverGridNoEdgeConfig) :
    #C.corner_set = 3 := by
  simp [coverGridNoEdgeConfig.corner_set]

/-- `corner_set` (i.e., The image set of `findLineCorner`) is a subset of `lines` -/
lemma coverGridNoEdgeConfig.corner_set_subset_lines (C : coverGridNoEdgeConfig) :
    C.corner_set ⊆ C.lines := by
  intro L
  simp only [corner_set, Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and,
    forall_exists_index]
  intro i hi
  rw [← hi]
  exact (C.find_line_corner_correct _).left

/-- If a `coverGridNoEdgeConfig` has `n = 3`, then `nS = 3`. -/
lemma coverGridNoEdgeConfig.cover_no_edge_3_lines (C : coverGridNoEdgeConfig)
    (hn3 : C.n = 3) : C.nS = 3 := by
  have Leq : C.corner_set = C.lines := by
    refine Finset.eq_of_subset_of_card_le C.corner_set_subset_lines ?_
    rw [C.lines_count, hn3, C.corner_set_card]
  let line_edge_middle_to_corner (d : Fin 3) : Fin 3 := match d with
    | 0 => 2
    | 1 => 1
    | 2 => 0
  have line_edge_middle (d : Fin 3) :
      C.findLineEdge d ⟨1, by omega⟩ = C.findLineCorner (line_edge_middle_to_corner d) := by
    have : C.findLineEdge d ⟨1, by omega⟩ ∈ C.corner_set :=
      Leq ▸ (C.find_line_edge_correct _ _).left
    simp only [coverGridNoEdgeConfig.corner_set, Finset.mem_map, Finset.mem_univ,
      Function.Embedding.coeFn_mk, true_and] at this
    obtain ⟨i, hi⟩ := this
    have middle_neq_endpoints (r : Fin 2) :
        C.findLineEdge d ⟨1, by omega⟩ ≠ C.findLineCorner (edgeEndpointCornerId d r) := by
      rw [C.find_line_corner_eq_edge]
      intro hC
      have := C.cover_no_edge_line_inj d hC
      fin_cases r <;> simp [coverGridNoEdgeConfig.edgeEndpointIndex] at this
      omega
    have := middle_neq_endpoints 0
    have := middle_neq_endpoints 1
    clear middle_neq_endpoints
    fin_cases d <;> fin_cases i <;> simp_all [line_edge_middle_to_corner, edgeEndpointCornerId]
  have : !₂[1, 1] ∈ C.findLineCorner 0 ∧ !₂[2, 2] ∈ C.findLineCorner 0 ∧
      !₂[1, 3] ∈ C.findLineCorner 1 ∧ !₂[2, 1] ∈ C.findLineCorner 1 ∧
      !₂[1, 2] ∈ C.findLineCorner 2 ∧ !₂[3, 1] ∈ C.findLineCorner 2 := by
    rw [
      show !₂[1, 1] = C.cornerPoint 0 by
        simp [coverGridNoEdgeConfig.cornerPoint, coverGridConfig.edgePoint],
      show !₂[2, 2] = C.edgePoint 2 ⟨1, by omega⟩ by simp [coverGridConfig.edgePoint, hn3],
      show !₂[1, 3] = C.cornerPoint 1 by
        simp [coverGridNoEdgeConfig.cornerPoint, coverGridConfig.edgePoint,
          coverGridNoEdgeConfig.edgeEndpointIndex, hn3],
      show !₂[2, 1] = C.edgePoint 1 ⟨1, by omega⟩ by simp [coverGridConfig.edgePoint],
      show !₂[1, 2] = C.edgePoint 0 ⟨1, by omega⟩ by simp [coverGridConfig.edgePoint],
      show !₂[3, 1] = C.cornerPoint 2 by
        simp [coverGridNoEdgeConfig.cornerPoint, coverGridConfig.edgePoint,
          coverGridNoEdgeConfig.edgeEndpointIndex, hn3]]
    repeat' constructor <;> try exact (C.find_line_corner_correct _).right
    all_goals
      convert (C.find_line_edge_correct _ ⟨1, by omega⟩).right
      rw [line_edge_middle]
  rw [← C.sunny_count, ← Leq, ← hn3, ← C.lines_count, ← Leq]
  congr 1
  ext L
  simp only [corner_set, Finset.mem_filter, Finset.mem_map, Finset.mem_univ,
    Function.Embedding.coeFn_mk, true_and, and_iff_left_iff_imp]
  intro ⟨i, hi⟩
  fin_cases i <;> rw [← hi]; try simp only
  · apply line_sunny_two_points _ 1 1 2 2 <;> try (first | tauto | norm_num)
  · apply line_sunny_two_points _ 1 3 2 1 <;> try (first | tauto | norm_num)
  · apply line_sunny_two_points _ 3 1 1 2 <;> try (first | tauto | norm_num)

/-- It is impossible to have a `coverGridNoEdgeConfig` with `n ≥ 4`. -/
lemma coverGridNoEdgeConfig.cover_no_edge_4_impossible (C : coverGridNoEdgeConfig)
    (hn4 : C.n ≥ 4) : False := by
  have := eqAffSubOfPlane
  have : #(C.lines \ C.corner_set) ≥ 1 := by
    calc
    _ = #C.lines - #(C.corner_set) := Finset.card_sdiff_of_subset C.corner_set_subset_lines
    _ ≥ C.n - 3 := by rw [C.lines_count, C.corner_set_card]
    _ ≥ 1 := by omega
  simp only [ge_iff_le, Finset.one_le_card] at this
  obtain ⟨L', hL'⟩ := Finset.Nonempty.exists_mem this
  simp only [Finset.mem_sdiff] at hL'
  have hL'₀ (d : Fin 3) : ∃ i, (C.findLineEdge d i = L' ∧
      i ≠ C.edgeEndpointIndex 0 ∧ i ≠ C.edgeEndpointIndex 1) := by
    rw [← C.cover_no_edge_line_surj d, Finset.mem_map] at hL'
    obtain ⟨⟨i, hi₁⟩, hi₂⟩ := hL'; simp only [Finset.mem_univ, Function.Embedding.coeFn_mk,
      true_and] at hi₁
    refine ⟨i, by assumption, ?_, ?_⟩
    all_goals
      by_contra hC
      have : L' ∈ C.corner_set := by
        rw [← hi₁, hC, ← C.find_line_corner_eq_edge d _]
        exact C.corner_set_members _
      tauto
  rw [coverGridNoEdgeConfig.edgeEndpointIndex, coverGridNoEdgeConfig.edgeEndpointIndex] at hL'₀
  choose iFunc hiFunc₁ hiFunc₂ hiFunc₃ using hL'₀
  have not_left_endpoint (d : Fin 3): (iFunc d).val > 0 := by
    by_contra
    have hC : (iFunc d).val = 0 := by omega
    have := hiFunc₂ d
    simp [← hC] at this
  have not_right_endpoint (d : Fin 3): (iFunc d).val < C.n - 1 := by
    by_contra
    have hC : (iFunc d).val = C.n - 1 := by omega
    have := hiFunc₃ d
    simp [← hC] at this
  have hi₀: (!₂[1, ((iFunc 0).val + 1 : ℕ)] : Plane) ∈ L' := by
    rw [← hiFunc₁ 0]
    convert (C.find_line_edge_correct 0 (iFunc 0)).right
    dsimp only [coverGridConfig.edgePoint]
    rw [vec_eq]; simp
  have hi₁: (!₂[((iFunc 1).val + 1 : ℕ), 1] : Plane) ∈ L' := by
    rw [← hiFunc₁ 1]
    convert (C.find_line_edge_correct 1 (iFunc 1)).right
    dsimp only [coverGridConfig.edgePoint]
    rw [vec_eq]; simp
  have hi₂: (!₂[((iFunc 2).val + 1 : ℕ), (C.n - 1 - (iFunc 2).val + 1 : ℕ)] : Plane) ∈ L' := by
    rw [← hiFunc₁ 2]
    convert (C.find_line_edge_correct 2 (iFunc 2)).right
    dsimp only [coverGridConfig.edgePoint]
    rw [vec_eq]
    exact ⟨rfl, by norm_cast; omega⟩
  have := C.lines_rank
  apply not_colinear_nat L' (C.n - 1) (iFunc 0) (iFunc 1) (iFunc 2)
  any_goals
    first | assumption | exact not_left_endpoint _ | exact not_right_endpoint _
  · apply this; exact hL'.left
  · omega

end FindLines


/-- A `coverGridNoEdgeConfig` must satisfy `n = 3 ∧ nS = 3`. -/
lemma coverGridNoEdgeConfig.cover_edge (C : coverGridNoEdgeConfig) : C.n = 3 ∧ C.nS = 3 := by
  have : C.n ≥ 3 := by
    calc
    _ = #C.lines := C.lines_count.symm
    _ ≥ #C.corner_set := Finset.card_le_card C.corner_set_subset_lines
    _ = 3 := C.corner_set_card
  by_cases C.n = 3
  · have := C.cover_no_edge_3_lines; tauto
  · have : C.n ≥ 4 := by omega
    have := C.cover_no_edge_4_impossible
    tauto

/-- A `coverGridNoEdgeConfig` must satisfy `nS ≤ n` and `nS ∈ {0, 1, 3}`.
Proved by induction on `n` of the above fact for all `coverGridNoEdgeConfig`. -/
lemma coverGridConfig.any_cover (C : coverGridConfig) :
    (C.nS ≤ C.n ∧ (C.nS = 0 ∨ C.nS = 1 ∨ C.nS = 3)) := by
  suffices ∀ (n : ℕ), (n = C.n → (C.nS ≤ C.n ∧ (C.nS = 0 ∨ C.nS = 1 ∨ C.nS = 3))) from this C.n rfl
  intro n
  induction n generalizing C with
  | zero =>
    have := C.nS_leq_n
    intros
    omega
  | succ n ih =>
    have := C.nS_leq_n
    intro h
    by_cases n = 0
    · omega
    · by_cases hE : ∃ e, C.edgeLine e ∈ C.lines
      · obtain ⟨d, hd⟩ := hE
        have := C.reduce_count d hd
        have := ih (reduce C d hd)
        omega
      · push_neg at hE
        let C' : coverGridNoEdgeConfig := {C with hE := hE, hn := by omega}
        have := C'.cover_edge
        have : C'.n = C.n := by rfl
        have : C'.nS = C.nS := by rfl
        omega

/-- A `coverGridConfig` with the additional requirements every line in `lines` goes through at
least one point in `g`. This is used to inductively construct covers of `grid n` with exactly
`0`, `1`, or `3` sunny lines. -/
structure strongCoverGridConfig extends coverGridConfig where
  lines_used : ∀ l ∈ lines, ∃ x ∈ g, x ∈ l

/-- A `strongCoverGridConfig` with `n = 0` and `nS = 0` -/
def zeroSunny : strongCoverGridConfig where
  lines := ∅
  g := ∅
  n := 0
  nS := 0
  lines_count := by simp
  lines_rank := by simp
  lines_cover := by simp
  sunny_count := by simp
  g_is_grid := by
    simp only [grid]; ext w
    simp only [Set.mem_empty_iff_false, Fin.isValue, zero_add,
      exists_and_left, Set.mem_setOf_eq, false_iff, not_exists, not_and, not_le]
    intros
    omega
  lines_used := by simp

/-- A `strongCoverGridConfig` with `n = 1` and `nS = 1` -/
noncomputable def oneSunny : strongCoverGridConfig where
  lines := {line (-1) 1 0}
  g := grid 1
  n := 1
  nS := 1
  lines_count := by simp
  lines_rank := by simp only [Finset.mem_singleton, forall_eq]; apply line_rank; simp
  lines_cover := by
    dsimp only [grid, Fin.isValue, Nat.reduceAdd, Set.mem_setOf_eq]
    intro x ⟨a, b, ha, hb, ha₀, hb₀, hab⟩
    have : a = 1 ∧ b = 1 := by omega
    simp [line, ← SetLike.mem_coe, SetLike.coe, ha, hb, this]
  sunny_count := by
    have : Sunny (line (-1) 1 0) := by
      rw [sunny_slope] <;>
        simp only [ne_eq, neg_eq_zero, one_ne_zero, not_false_eq_true, or_self, true_and]
      norm_num
    calc
    _ = #{line (-1) 1 0} := by
      congr 1; ext l
      simp only [Finset.mem_filter, Finset.mem_singleton, and_iff_left_iff_imp]
      intro hl; rwa [hl]
    _ = 1 := by simp
  g_is_grid := by rfl
  lines_used := by
    simp only [Finset.mem_singleton, forall_eq]
    use !₂[1, 1]; constructor
    · simp only [grid, Fin.isValue, Nat.reduceAdd, exists_and_left, Set.mem_setOf_eq,
      PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      use 1; norm_cast; simp
    · simp [line, ← SetLike.mem_coe, SetLike.coe]

/-- The `LineCoeffs` of a 3 sunny solution -/
def threeSunnyLineCoeffs : Fin 3 → LineCoeffs
  | 0 => ⟨-1, 1, 0⟩
  | 1 => ⟨2, 1, -5⟩
  | 2 => ⟨1, 2, -5⟩

/-- The lines of a 3 sunny solution -/
noncomputable def threeSunnyLine (d : Fin 3) := line' (threeSunnyLineCoeffs d)

/-- The lines of a 3 sunny solution are distinct. -/
lemma threeSunnyLineInj : Function.Injective threeSunnyLine := by
  intro d e h
  fin_cases d
  all_goals fin_cases e
  any_goals rfl
  all_goals
    simp only [threeSunnyLine, line', threeSunnyLineCoeffs] at h
    apply line_eq_check at h <;> norm_num
    norm_num at h

/-- The set of lines of a 3 sunny solution -/
noncomputable def threeSunnyLines :=
  Finset.map ⟨threeSunnyLine, threeSunnyLineInj⟩ Finset.univ

/-- The members of the set of lines of a 3 sunny solution -/
lemma threeSunnyLinesMem (L : AffSubOfPlane) : L ∈ threeSunnyLines ↔
    (L = threeSunnyLine 0) ∨ (L = threeSunnyLine 1) ∨ (L = threeSunnyLine 2) := by
  simp only [threeSunnyLines, Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk,
    true_and, Fin.isValue]
  constructor
  · intro ⟨d, hd⟩; fin_cases d <;> (simp only at hd; tauto)
  · rintro (h | h | h) <;> (rw [h]; simp)

/-- The points in `grid 3` -/
lemma grid3Points (x : Plane) : x ∈ grid 3 ↔
    (x = !₂[1, 1] ∨ x = !₂[1, 2] ∨ x = !₂[1, 3] ∨
     x = !₂[2, 1] ∨ x = !₂[2, 2] ∨ x = !₂[3, 1]) := by
  simp only [grid, Fin.isValue, Nat.reduceAdd, exists_and_left, Set.mem_setOf_eq]
  constructor
  · intro ⟨a, ha, b, hb, ha₀, hb₀, hab⟩
    rw [vec_repr x, ha, hb, vec_eq, vec_eq, vec_eq, vec_eq, vec_eq, vec_eq]
    norm_cast
    omega
  · intro hx
    rw [vec_repr x, vec_eq, vec_eq, vec_eq, vec_eq, vec_eq, vec_eq] at hx
    obtain hx | hx | hx | hx | hx | hx := hx
    all_goals
      rw [hx.left, hx.right]
      norm_cast
      simp

/-- A `strongCoverGridConfig` with `n = 3` and `nS = 3` -/
noncomputable def threeSunny : strongCoverGridConfig where
  lines := threeSunnyLines
  g := grid 3
  n := 3
  nS := 3
  lines_count := by simp [threeSunnyLines]
  lines_rank := by
    simp only [threeSunnyLines, Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk,
      true_and, forall_exists_index, forall_apply_eq_imp_iff]
    intro d
    fin_cases d
    all_goals
      simp only [threeSunnyLine, line', threeSunnyLineCoeffs]
      apply line_rank; simp
  lines_cover := by
    simp only [grid3Points, threeSunnyLinesMem]
    rintro x (hx | hx | hx | hx | hx | hx)
    all_goals
      dsimp only [threeSunnyLine, line', threeSunnyLineCoeffs]
      rw [hx]
      simp [point_on_line]
      try norm_num
  sunny_count := by
    have hS (d : Fin 3): Sunny (threeSunnyLine d) := by
      dsimp only [threeSunnyLine, line', threeSunnyLineCoeffs]
      rw [sunny_slope] <;> fin_cases d <;> (simp only; try norm_num)
    calc
    _ = #threeSunnyLines := by
      congr 1; ext l
      simp only [threeSunnyLines, Finset.mem_filter, Finset.mem_map, Finset.mem_univ,
        Function.Embedding.coeFn_mk, true_and, and_iff_left_iff_imp, forall_exists_index]
      exact fun d hd ↦ hd ▸ hS d
    _ = 3 := by simp [threeSunnyLines]
  g_is_grid := rfl
  lines_used := by
    simp only [grid3Points, threeSunnyLinesMem, threeSunnyLine, line', threeSunnyLineCoeffs]
    rintro L (hL | hL | hL)
    all_goals
      rw [hL]
      simp [point_on_line]
      try norm_num

/-- Add a diagonal line `x + y = n + 2` to a `countAndStrongCover` -/
noncomputable def strongCoverGridConfig.extend (C : strongCoverGridConfig) :
    strongCoverGridConfig where
  lines := Finset.cons (edgeLine (C.n + 1) 2) C.lines hNew
  g := grid (C.n + 1)
  n := C.n + 1
  nS := C.nS
  lines_count := by simp [C.lines_count]
  lines_rank := by
    intro l hl
    simp only [Fin.isValue, Finset.mem_cons] at hl
    obtain hl | hl := hl
    · rw [hl, edgeLine, line', edgeCoeffs]; apply line_rank; simp
    · exact C.lines_rank l hl
  lines_cover := by
    intro x hx
    by_cases hE : x ∈ edgeLine (C.n + 1) 2
    · use edgeLine (C.n + 1) 2; simp [hE]
    · have : x ∈ C.g := by rw [C.g_is_grid, ← grid_remove_diag]; simp [hx, hE]
      obtain ⟨L, hL₁, hL₂⟩ := C.lines_cover x this
      use L; simp [hL₁, hL₂]
  sunny_count := by
    rw [← C.sunny_count]; congr 1
    ext L
    simp only [Fin.isValue, Finset.mem_filter, Finset.mem_cons,
    and_congr_left_iff, or_iff_right_iff_imp]
    intro hLS hLd
    rw [hLd, edgeLine, line', edgeCoeffs, sunny_slope (h := by simp)] at hLS
    replace hLS := hLS.right.right; contradiction
  g_is_grid := rfl
  lines_used := by
    intro L hL
    by_cases hE : L = edgeLine (C.n + 1) 2
    · refine ⟨!₂[1, C.n + 1], ?_, ?_⟩
      · use 1; simp only [Fin.isValue, PiLp.toLp_apply, Matrix.cons_val_zero, Nat.cast_one,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_lt_one, true_and]
        use C.n + 1; simp only [Nat.cast_add, Nat.cast_one, lt_add_iff_pos_left, add_pos_iff,
          zero_lt_one, or_true, true_and]
        omega
      · rw [hE, edgeLine, line', edgeCoeffs, point_on_line]
        ring_nf
        rw [show (1 + C.n : ℕ) = 1 + (C.n : ℝ) by norm_cast]
        ring
    · have : L ∈ C.lines := by apply Finset.mem_of_mem_cons_of_ne hL; exact hE
      obtain ⟨x, hx₁, hx₂⟩ := C.lines_used L this
      use x; simp only [hx₂, and_true]
      have := grid_remove_diag C.n
      rw [← C.g_is_grid] at this
      rw [← this, Set.mem_diff] at hx₁
      tauto
  where hNew : edgeLine (C.n + 1) 2 ∉ C.lines := by {
    intro hC
    obtain ⟨x, hx₁, hx₂⟩ := C.lines_used (edgeLine (C.n + 1) 2) hC
    simp only [C.g_is_grid, grid, Fin.isValue, exists_and_left, Set.mem_setOf_eq] at hx₁
    obtain ⟨a, ha, b, hb, ha₀, hb₀, hab⟩ := hx₁
    have : (a : ℝ) + b ≤ (C.n + 1 : ℕ) := by norm_cast
    rw [vec_repr x, edgeLine, line', point_on_line, edgeCoeffs, ha, hb] at hx₂
    linarith}

/-- It is possible to have a `strongCoverGridConfig`, whenever `nS ≤ n` and
`nS = 0 ∨ nS = 1 ∨ nS = 3` -/
lemma existsStrongCover (n nS : ℕ) :
    nS ≤ n → (nS = 0 ∨ nS = 1 ∨ nS = 3) →
    ∃ (C : strongCoverGridConfig), C.n = n ∧ C.nS = nS := by
  induction n with
  | zero =>
    intro h hS
    use zeroSunny
    simp only [zeroSunny, true_and]
    omega
  | succ n ih =>
    intro h hS
    by_cases hE : nS ≤ n
    · have ⟨C, hL⟩ := ih hE hS
      use C.extend
      simpa [strongCoverGridConfig.extend]
    · have : nS = n + 1 := by omega
      rw [← this]
      obtain hS | hS | hS := hS
      · rw [hS]; use zeroSunny; simp [zeroSunny]
      · rw [hS]; use oneSunny; simp [oneSunny]
      · rw [hS]; use threeSunny; simp [threeSunny]

/-- The final theorem: answer is {0, 1, 3}. -/
theorem result (n : Set.Ici 3) :
    {k | ∃ lines : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))),
      have := sunnyPred;
      #lines = n ∧ (∀ l ∈ lines, finrank ℝ l.direction = 1) ∧
      (∀ a b : ℕ, 0 < a → 0 < b → a + b ≤ (n : ℕ) + 1 → ∃ l ∈ lines, !₂[(a : ℝ), b] ∈ l) ∧
      #{l ∈ lines | Sunny l} = k} = answer n := by
  dsimp only [Lean.Elab.WF.paramLet, answer]
  ext nS
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro ⟨lines, h₁, h₂, h₃, h₄⟩
    let C : coverGridConfig := {
      lines := lines
      g := grid n
      n := n
      nS := nS
      lines_count := h₁
      lines_rank := h₂
      lines_cover := by
        intro x hx
        simp only [grid, Fin.isValue, exists_and_left, Set.mem_setOf_eq] at hx
        obtain ⟨a, ha, b, hb, ha₀, hb₀, hab⟩ := hx
        specialize h₃ a b ha₀ hb₀ hab
        rw [← ha, ← hb, show !₂[x 0, x 1] = x by ext i; fin_cases i <;> simp] at h₃
        exact h₃
      sunny_count := h₄
      g_is_grid := rfl
      }
    have := C.any_cover
    tauto
  · intro hS
    have : n.val ≥ 3 := n.property
    have : nS ≤ n.val := by omega
    obtain ⟨C, h⟩ := existsStrongCover n nS this hS
    use C.lines
    simp only [C.lines_count, h, C.sunny_count, and_true, true_and]
    refine ⟨fun L hL ↦ C.lines_rank L hL, fun a b ha₀ hb₀ hab ↦ ?_⟩
    convert C.lines_cover !₂[(a : ℝ), (b : ℝ)] _
    rw [C.g_is_grid, point_in_grid]
    omega

end Imo2025Q1
