/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers (Problem statement), Yizheng Zhu (Solution)
-/
import Mathlib

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

namespace IMO2025P1

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
lemma vec_eq (x1 x2 y1 y2 : ℝ) : !₂[x1, y1] = !₂[x2, y2] ↔ (x1 = x2 ∧ y1 = y2) := by
  constructor
  · intro h
    apply_fun (fun w ↦ (w.ofLp 0, w.ofLp 1)) at h
    simpa using h
  · simp (config := { contextual := true })

/-- Get the x coordinate of a vector. -/
lemma vec_repr_x (x y : ℝ) : !₂[x, y] 0 = x := by simp
/-- Get the y coordinate of a vector. -/
lemma vec_repr_y (x y : ℝ) : !₂[x, y] 1 = y := by simp

/-- Represent a vector as a pair of real numbers -/
lemma vec_repr (x : Plane) : x = !₂[x 0, x 1] := by
  ext i; fin_cases i <;> simp

/-- Multiply a vector by a scalar. -/
lemma vec_mul (k x y : ℝ) : k • !₂[x, y] = !₂[k * x, k * y] := by
  ext i; fin_cases i <;> simp

/-- Compute the difference of two vectors -/
lemma vec_sub (x1 y1 x2 y2 : ℝ) : !₂[x1, y1] - !₂[x2, y2] = !₂[x1 - x2, y1 - y2] := by
  ext i; fin_cases i <;> simp

/-- The "line" `ax + by + c = 0`. ("line" means except for the degenerate case `a = 0 ∧ b = 0`)
Note: We don't enforce `a ≠ 0 ∨ b ≠ 0`. -/
noncomputable def line (a b c : ℝ) : AffSubOfPlane where
  carrier := {p | a * p 0 + b * p 1 + c = 0}
  smul_vsub_vadd_mem r p₁ p₂ p₃ hp₁ hp₂ hp₃ := by
    simp only [Fin.isValue, vsub_eq_sub, vadd_eq_add, Set.mem_setOf_eq, PiLp.add_apply,
      PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    simp_all only [Fin.isValue, Set.mem_setOf_eq]
    calc
    _ = r * (a * p₁ 0 + b * p₁ 1 + c) -
        r * (a * p₂ 0 + b * p₂ 1 + c) +
        (a * p₃ 0 + b * p₃ 1 + c) := by ring
    _ = 0 := by rw [hp₁, hp₂, hp₃]; ring

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
lemma line_direction (a b c : ℝ) (h : a ≠ 0 ∨ b ≠ 0) (w : Plane):
    w ∈ AffineSubspace.direction (line a b c) ↔ ∃ (k : ℝ), k • !₂[-b, a] = w := by
  have hv_nonempty := line_nonempty a b c h
  constructor
  · intro hw
    rw [AffineSubspace.mem_direction_iff_eq_vsub hv_nonempty] at hw
    obtain ⟨w1, hw1, w2, hw2, hw12⟩ := hw
    rw [vec_repr w1, point_on_line] at hw1
    rw [vec_repr w2, point_on_line] at hw2
    simp only [vsub_eq_sub] at hw12
    obtain ha | hb := h
    · use (w1 1 - w2 1) / a
      · rw [hw12]
        nth_rw 2 [vec_repr w1, vec_repr w2]
        rw [vec_mul, vec_sub, vec_eq]
        constructor
        · field_simp; linarith
        · field_simp
    · use (w2 0 - w1 0) / b
      · rw [hw12]
        nth_rw 2 [vec_repr w1, vec_repr w2]
        rw [vec_mul, vec_sub, vec_eq]
        constructor
        · field_simp; linarith
        · field_simp; linarith
  · intro ⟨k, hkw⟩
    rw [AffineSubspace.mem_direction_iff_eq_vsub hv_nonempty]
    simp only [Set.Nonempty, SetLike.mem_coe] at hv_nonempty
    obtain ⟨v1, hv1⟩ := hv_nonempty
    use v1
    constructor
    · exact hv1
    · use v1 - w; constructor
      · rw [vec_repr v1, point_on_line] at hv1
        rw [vec_repr v1, ← hkw, vec_mul, vec_sub, point_on_line]
        ring_nf; exact hv1
      · simp

/-- The rank of the line `a * x + b * y + c = 0` is `1` when `a` and `b` are not both zero -/
lemma line_rank (a b c : ℝ) (h : a ≠ 0 ∨ b ≠ 0) : finrank ℝ (line a b c).direction = 1 := by
  have hv_mem : !₂[-b, a] ∈ AffineSubspace.direction (line a b c) := by
    rw [line_direction]
    · use 1; rw [vec_mul, vec_eq]; simp
    · exact h
  rw [finrank_eq_one_iff']
  use ⟨!₂[-b, a], hv_mem⟩
  constructor
  · simp; tauto
  · simp only [SetLike.mk_smul_mk, Subtype.forall, Subtype.mk.injEq]
    intro w; exact (line_direction a b c h w).mp

def aEdge (d : Fin 3) : ℝ := match d with
| 0 => 1
| 1 => 0
| 2 => 1
def bEdge (d : Fin 3) : ℝ := match d with
| 0 => 0
| 1 => 1
| 2 => 1
def cEdge (n : ℕ) (d : Fin 3) : ℝ := match d with
| 0 => -1
| 1 => -1
| 2 => -(n + 1)

/-- The three lines on the edges of the triangular integer grid, each side having n points:
`x - 1 = 0`; `y - 1 = 0`; `x + y - (n + 1) = 0`.
These lines are named `edgeLine n 0`, `edgeLine n 1`, `edgeLine n 2`, resp. -/
noncomputable def edgeLine (n : ℕ) (d : Fin 3) :=
  line (aEdge d) (bEdge d) (cEdge n d)

/-- The y axis is the line `x = 0`. -/
lemma y_ax_line : line 1 0 0 = yAxis := by
  simp [line, yAxis]

/-- The x axis is the line `y = 0` -/
lemma x_ax_line : line 0 1 0 = xAxis := by
  simp [line, xAxis]

/-- The line `x + y = 0` -/
lemma xy0_line : line 1 1 0 = linexy0 := by
  simp [line, linexy0]

/-- Preparation lemma for checking if two lines are parallel -/
lemma line_para' (a b a' b': ℝ) (h' : a' ≠ 0 ∨ b' ≠ 0)
    (hab : a * b' = a' * b) (w : Plane) :
    (∃ (k : ℝ), k • !₂[-b, a] = w) → (∃ (k : ℝ), k • !₂[-b', a'] = w) := by
  intro ⟨k, hk1⟩
  rw [vec_mul, vec_repr w, vec_eq] at hk1
  obtain ⟨hk1, hk2⟩ := hk1
  obtain ha | hb := h'
  · use k * a / a'
    rw [vec_mul, vec_repr w, vec_eq]
    constructor <;> field_simp
    · rw [←hk1, mul_assoc, hab]; ring
    · rw [←hk2, ]
  · use k * b / b'
    rw [vec_mul, vec_repr w, vec_eq]
    constructor <;> field_simp
    · rw [←hk1]; ring
    · rw [←hk2, mul_assoc _ a _, hab]; ring

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
    rw [hp] at this
    rw [line_direction a' b' c' h' w] at this
    dsimp only [w] at this
    obtain ⟨k, hk⟩ := this
    rw [vec_mul, vec_eq] at hk
    obtain ⟨hk1, hk2⟩ := hk
    replace hk1 : k * b' = b := by linarith
    rw [← hk1, ← hk2]; ring
  · intro hab
    constructor
    · ext w
      rw [line_direction a b c h w, line_direction a' b' c' h' w]
      constructor
      · exact line_para' a b a' b' h' hab w
      · exact line_para' a' b' a b h hab.symm w
    · rw [← AffineSubspace.coe_eq_bot_iff, ← AffineSubspace.coe_eq_bot_iff]
      have : SetLike.coe (line a b c) ≠ ∅ := by
        rw [← Set.nonempty_iff_ne_empty]
        exact line_nonempty a b c h
      have : SetLike.coe (line a' b' c') ≠ ∅ := by
        rw [← Set.nonempty_iff_ne_empty]
        exact line_nonempty a' b' c' h'
      tauto

/-- If the line `a * x + b * y + c` is parallel to `L`,
and both lines go through `(x1, y1)`, `(x2, y2)`,
then `a * (x2 - x1) + b * (y2 - y1) = 0`. -/
lemma line_para_two_points (a b c : ℝ) (h : a ≠ 0 ∨ b ≠ 0) (L : AffSubOfPlane) (x1 y1 x2 y2 : ℝ) :
    line a b c ∥ L → !₂[x1, y1] ∈ L → !₂[x2, y2] ∈ L → a * (x2 - x1) + b * (y2 - y1) = 0 := by
  by_cases hxy : x1 = x2 ∧ y1 = y2
  · rw [show x2 - x1 = 0 by simp [hxy], show y2 - y1 = 0 by simp [hxy]]
    simp
  · rw [AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot]
    intro ⟨hp, _⟩ h1 h2
    let w := !₂[x2 - x1, y2 - y1]
    have : w ∈ AffineSubspace.direction L := by
      rw [AffineSubspace.mem_direction_iff_eq_vsub _]
      · use !₂[x2, y2]; simp only [h2, vsub_eq_sub, true_and]
        use !₂[x1, y1]; simp only [h1, true_and]
        dsimp only [w]; rw [vec_sub, vec_eq]; simp
      · simp only [Set.Nonempty, SetLike.mem_coe]; use !₂[x1, y1]
    rw [← hp, line_direction] at this
    · dsimp only [w] at this
      obtain ⟨k, hk⟩ := this
      rw [vec_mul, vec_eq] at hk
      rw [← hk.left, ← hk.right]; ring
    · tauto

/-- If the linex `a * x + b * y + c = 0` and `a' * x + b' * y + c = 0` are equal,
then `a * b' = a' * b ∧ a * c' = a' * c ∧ b * c' = b' * c`. -/
lemma line_eq_check (a b c a' b' c' : ℝ) (h : a ≠ 0 ∨ b ≠ 0) (h' : a' ≠ 0 ∨ b' ≠ 0)
    (heq : line a b c = line a' b' c') :
    a * b' = a' * b ∧ a * c' = a' * c ∧ b * c' = b' * c := by
  have hab : a * b' = a' * b := by rw [← line_para a b c a' b' c' h h', heq]
  rw [AffineSubspace.ext_iff, Set.ext_iff] at heq
  constructor
  · exact hab
  · by_cases ha : a = 0
    · have hb : b ≠ 0 := by tauto
      have ha' : a' = 0 := by rw [ha] at hab; simp only [zero_mul, zero_eq_mul] at hab; tauto
      simp only [ha, zero_mul, ha', true_and]
      specialize heq !₂[0, -c / b]
      rw [AffineSubspace.mem_coe, AffineSubspace.mem_coe, point_on_line, point_on_line] at heq
      have : a * 0 + b * (-c / b) + c = 0 := by field_simp; ring
      replace heq := (heq.mp) this; simp only [mul_zero, zero_add] at heq
      calc
      _ = b * (-(b' * (-c / b))) := by congr 1; linarith
      _ = b' * c := by field_simp
    · constructor
      · specialize heq !₂[-c / a, 0]
        rw [AffineSubspace.mem_coe, AffineSubspace.mem_coe, point_on_line, point_on_line] at heq
        have : a * (-c / a) + b * 0 + c = 0 := by field_simp; ring
        replace heq := (heq.mp) this; simp only [mul_zero, add_zero] at heq
        calc
        _ = a * (-(a' * (-c / a))) := by congr 1; linarith
        _ = a' * c := by field_simp
      · by_cases hb : b = 0
        · have hb' : b' = 0 := by rw [hb] at hab; simp only [mul_zero, mul_eq_zero] at hab; tauto
          simp [hb, hb']
        · specialize heq !₂[0, -c / b]
          rw [AffineSubspace.mem_coe, AffineSubspace.mem_coe, point_on_line, point_on_line] at heq
          have : a * 0 + b * (-c / b) + c = 0 := by field_simp; ring
          replace heq := (heq.mp) this; simp only [mul_zero, zero_add] at heq
          calc
          _ = b * (-(b' * (-c / b))) := by congr 1; linarith
          _ = b' * c := by field_simp

/-- Preparation lemma for `get_line_eq`. -/
lemma line_contains (L L' : AffSubOfPlane) (hL : finrank ℝ L.direction = 1) (a b : Plane) :
    (a ≠ b → a ∈ L → b ∈ L → a ∈ L' → b ∈ L' → L ≤ L') := by
  intro hab ha hb ha' hb'
  rw [AffineSubspace.le_def']
  intro x hx
  rw [finrank_eq_one_iff'] at hL
  obtain ⟨v, hv0, hv⟩ := hL
  have L_nonempty : (SetLike.coe L).Nonempty := by simp only [Set.Nonempty, SetLike.mem_coe]; use a
  obtain ⟨k, hk⟩ :=
    hv ⟨a -ᵥ b, by rw [AffineSubspace.mem_direction_iff_eq_vsub L_nonempty]; use a; simp [ha, hb]⟩
  obtain ⟨q, hq⟩ :=
    hv ⟨x -ᵥ a, by rw [AffineSubspace.mem_direction_iff_eq_vsub L_nonempty]; use x; simp [hx, ha]⟩
  apply_fun (·.val) at hk; simp only [SetLike.val_smul, vsub_eq_sub] at hk
  apply_fun (·.val) at hq; simp only [SetLike.val_smul, vsub_eq_sub] at hq
  have hk0 : k ≠ 0 := by
    intro hkC; simp only [hkC, zero_smul] at hk
    have : a = b := by rw [← sub_eq_zero]; exact hk.symm
    contradiction
  have x_a_expr : x - a = (q / k) • (a - b) := by rw [← hk, ← hq, ← mul_smul]; congr 1; field_simp
  have := L'.smul_vsub_vadd_mem (q / k) (p₁ := a) (p₂ := b) (p₃ := a) ha' hb' ha'
  simpa [← x_a_expr] using this

/-- If both of the two non-degenerate lines `L` and `L'` go through two different points
`a` and `b`, then `L = L'`. -/
lemma get_line_eq
    (L L' : AffSubOfPlane) (hL : finrank ℝ L.direction = 1) (hL' : finrank ℝ L'.direction = 1)
    (a b : Plane) (hab : a ≠ b)
    (ha : a ∈ L) (hb : b ∈ L) (ha' : a ∈ L') (hb' : b ∈ L') : L = L' := by
  have h1 := line_contains L L' hL a b hab ha hb ha' hb'
  have h2 := line_contains L' L hL' a b hab ha' hb' ha hb
  rw [AffineSubspace.le_def] at *
  rw [AffineSubspace.ext_iff]
  exact Set.Subset.antisymm h1 h2

end LineOnPlane

/-- The decidable predicate `Sunny`. -/
noncomputable def sunnyPred : DecidablePred Sunny := Classical.decPred _
/-- The decidable equality predicate `L = L'` for `(L L' : AffSubOfPlane)`. -/
noncomputable def eqAffSubOfPlane : DecidableEq AffSubOfPlane := Classical.decEq _

/-- Check if the line `a * x + b * y + c = 0` is sunny or not. -/
lemma sunny_slope (a b c : ℝ) (h : a ≠ 0 ∨ b ≠ 0) :
    Sunny (line a b c) ↔ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b := by
  dsimp only [Sunny]
  rw [← x_ax_line, ← y_ax_line, ← xy0_line]
  rw [line_para, line_para, line_para]
  · simp only [mul_one, zero_mul, mul_zero, one_mul, ne_eq, and_congr_right_iff,
      and_congr_left_iff]
    tauto
  all_goals (first | assumption | simp)

/-- The integer grid consisting of (a, b), where a, b are positive integers and a + b ≤ n + 1. -/
def grid (n : ℕ) : Set Plane :=
  {x : Plane | ∃ (a b : ℕ), x 0 = a ∧ x 1 = b ∧ 0 < a ∧ 0 < b ∧ a + b ≤ (n : ℕ) + 1}

/-- Check if (a, b) is in `grid n` for natural numbers a, b. -/
lemma point_in_grid (n : ℕ) (a b : ℕ) :
    !₂[(a : ℝ), (b : ℝ)] ∈ grid n ↔ 0 < a ∧ 0 < b ∧ a + b ≤ n + 1 := by simp [grid]

/-- `countAndCover lines g n nS` means:
`lines` has `n` lines, every point in `g` is covered by a line in `lines`,
and the number of sunny lines in `lines` is `nS`. -/
def countAndCover (lines : Finset AffSubOfPlane) (g : Set Plane) (n nS : ℕ) :=
  have := sunnyPred;
  #lines = n ∧ (∀ l ∈ lines, finrank ℝ l.direction = 1) ∧
  (∀ x ∈ g, ∃ l ∈ lines, x ∈ l) ∧ #{l ∈ lines | Sunny l} = nS

/-- `shiftSet v g` is the result of shifting every point in `g` by the vector `v`. -/
def shiftSet (v : Plane) (g : Set Plane) : Set Plane :=
  Set.image (AffineEquiv.constVAdd ℝ Plane v) g

def gridShiftX (d : Fin 3) := match d with
  | 0 => -1
  | 1 => 0
  | 2 => 0
def gridShiftY (d : Fin 3) := match d with
  | 0 => 0
  | 1 => -1
  | 2 => 0

/-- After removing an edge from `grid (n + 1)` and appropriate shifting,
the resulting set is `grid n`.
Remove `edgeLine (n + 1) 0` (i.e. left edge) -> shift by `(-1, 0)`.
Remove `edgeLine (n + 1) 1` (i.e. bottom edge) -> shift by `(0, -1)`.
Remove `edgeLine (n + 1) 2` (i.e. diagonal edge) -> shift by `(0, 0)` (i.e. no shift). -/
lemma grid_shift (n : ℕ) (d : Fin 3):
    shiftSet !₂[gridShiftX d, gridShiftY d] (grid (n + 1) \ (edgeLine (n + 1) d)) = grid n := by
  ext x
  simp only [shiftSet, AffineEquiv.constVAdd_apply, vadd_eq_add, Set.image_add_left, grid,
    Fin.isValue, exists_and_left, Set.preimage_diff, Set.preimage_setOf_eq, PiLp.add_apply,
    PiLp.neg_apply, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Set.mem_diff, Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
  constructor
  · intro ⟨⟨a, ha, b, hb, ha0, hb0, hab⟩, h2⟩
    simp only [edgeLine, line, Fin.isValue, ← SetLike.mem_coe, SetLike.coe, Set.mem_setOf_eq,
      PiLp.add_apply, PiLp.neg_apply, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at h2
    fin_cases d
    · simp only [aEdge, gridShiftX, Int.reduceNeg, Int.cast_neg, Int.cast_one, neg_neg,
        Fin.isValue, one_mul, bEdge, gridShiftY, zero_mul,
        add_zero, cEdge, add_neg_cancel_comm] at h2
      simp only [gridShiftX, Int.reduceNeg, Int.cast_neg, Int.cast_one, neg_neg, Fin.isValue] at ha
      simp only [gridShiftY, Int.cast_zero, neg_zero, Fin.isValue, zero_add] at hb
      have : a ≠ 1 := by intro hC; rw [hC] at ha; simp only [Fin.isValue, Nat.cast_one,
        add_eq_left] at ha; contradiction
      use a - 1
      constructor
      · field_simp
        apply_fun (·-1) at ha
        simpa using ha
      · use b
        constructor <;> (try (first | assumption | omega))
    · simp only [aEdge, gridShiftX, Int.cast_zero, neg_zero, Fin.isValue, zero_add, zero_mul,
        bEdge, gridShiftY, one_mul, cEdge] at h2
      simp only [gridShiftX, Int.cast_zero, neg_zero, Fin.isValue, zero_add] at ha
      simp only [gridShiftY, Int.reduceNeg, Int.cast_neg, Int.cast_one, neg_neg, Fin.isValue] at hb
      have : b ≠ 1 := by intro hC; rw [hC] at hb; simp only [Fin.isValue, Nat.cast_one,
        add_eq_left] at hb; rw [hb] at h2; simp at h2
      use a
      constructor
      · exact ha
      · use b - 1
        constructor
        · field_simp
          apply_fun (·-1) at hb
          simpa using hb
        · constructor <;> (try (first | assumption | omega))
    · simp only [aEdge, gridShiftX, Int.cast_zero, neg_zero, Fin.isValue, zero_add, one_mul, bEdge,
        gridShiftY, cEdge, neg_add_rev] at h2
      simp only [gridShiftX, Int.cast_zero, neg_zero, Fin.isValue, zero_add] at ha
      simp only [gridShiftY, Int.cast_zero, neg_zero, Fin.isValue, zero_add] at hb
      have : a + b ≠ n + 2 := by
        intro hC; rw [ha, hb] at h2; norm_cast at h2; omega
      use a
      constructor
      · exact ha
      · use b; constructor
        · exact hb
        · constructor <;> (try (first | assumption | omega))
  · intro ⟨a, ha, b, hb, ha0, hb0, hab⟩
    fin_cases d
    · constructor
      · use 1 + a
        simp only [gridShiftX, Int.reduceNeg, Int.cast_neg, Int.cast_one, neg_neg,
          Fin.isValue, ha, Nat.cast_add, Nat.cast_one, gridShiftY, Int.cast_zero, neg_zero,
          zero_add, add_pos_iff, zero_lt_one, ha0, or_self, true_and]
        use b
        simp only [Fin.isValue, hb, hb0, true_and]
        omega
      · simp only [edgeLine, line, Fin.isValue, aEdge, one_mul, bEdge, zero_mul, add_zero, cEdge,
          gridShiftX, Int.reduceNeg, Int.cast_neg, Int.cast_one, Fin.zero_eta, ← SetLike.mem_coe,
          SetLike.coe, Set.mem_setOf_eq, PiLp.add_apply, PiLp.neg_apply, PiLp.toLp_apply,
          Matrix.cons_val_zero, neg_neg, add_neg_cancel_comm]
        intro hC; rw [hC] at ha; norm_cast at ha; omega
    · constructor
      · use a
        simp only [gridShiftX, Int.cast_zero, neg_zero, Fin.isValue, ha, zero_add,
          gridShiftY, Int.reduceNeg, Int.cast_neg, Int.cast_one, neg_neg, true_and]
        use 1 + b
        simp only [Fin.isValue, hb, Nat.cast_add, Nat.cast_one, add_pos_iff, zero_lt_one,
          hb0, or_self, true_and]
        omega
      · simp only [edgeLine, line, Fin.isValue, aEdge, zero_mul, bEdge, one_mul, zero_add, cEdge,
          Fin.mk_one, gridShiftY, Int.reduceNeg, Int.cast_neg, Int.cast_one, ← SetLike.mem_coe,
          SetLike.coe, Set.mem_setOf_eq, PiLp.add_apply, PiLp.neg_apply, PiLp.toLp_apply,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, neg_neg, add_neg_cancel_comm]
        intro hC; rw [hC] at hb; norm_cast at hb; omega
    · constructor
      · use a
        simp only [gridShiftX, Int.cast_zero, neg_zero, Fin.isValue, ha, zero_add,
          gridShiftY, true_and]
        use b
        simp only [Fin.isValue, hb, hb0, true_and]
        omega
      · simp only [edgeLine, line, Fin.isValue, aEdge, one_mul, bEdge, cEdge, Nat.cast_add,
          Nat.cast_one, neg_add_rev, gridShiftX, Int.cast_zero, gridShiftY, ← SetLike.mem_coe,
          SetLike.coe, Set.mem_setOf_eq, PiLp.add_apply, PiLp.neg_apply, PiLp.toLp_apply,
          Matrix.cons_val_zero, neg_zero, zero_add, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        intro hC; rw [ha, hb] at hC; norm_cast at hC; omega

/-- After removing the diagonal edge from `grid (n + 1)` , the resulting set is `grid n`. -/
lemma grid_remove_diag (n : ℕ) : grid (n + 1) \ (edgeLine (n + 1) 2) = grid n := by
  rw [← grid_shift n 2, gridShiftX, gridShiftY]
  set g := grid (n + 1) \ ↑(edgeLine (n + 1) 2)
  simp only [shiftSet, Int.cast_zero, AffineEquiv.constVAdd_apply, vadd_eq_add, Set.image_add_left]
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
    dsimp only [Function.Injective]; intro L1 L2 h
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
  dsimp only [shiftLine, Function.Embedding.coeFn_mk, shiftLineMap]
  rw [AffineSubspace.map_map, ←affine_trans, ←AffineEquiv.constVAdd_add]
  simp

/-- If `L` is sunny, then so is its shift. -/
lemma shift_sunny (v : Plane) (L : AffSubOfPlane) : Sunny L → Sunny (shiftLine v L) := by
  rw [Sunny, Sunny]
  have (L' : AffSubOfPlane) : L ∥ L' ↔ shiftLine v L ∥ L' := by
    constructor
    · intro h
      apply AffineSubspace.Parallel.trans _ h
      symm; apply shift_para
    · intro h
      apply AffineSubspace.Parallel.trans _ h
      apply shift_para
  rw [← this, ← this, ← this]
  tauto

/-- If `countAndCover lines g n nS`, then the same `countAndCover` property holds after
shifting `lines` and `g` by the same vector. -/
lemma shift_count_and_cover (lines : Finset AffSubOfPlane) (g : Set Plane) (n nS : ℕ) (v : Plane) :
    countAndCover lines g n nS → countAndCover (shiftLines v lines) (shiftSet v g) n nS := by
  dsimp only [countAndCover]
  intro ⟨h1, h2, h3, h4⟩
  simp only [shiftLines, Finset.card_map, Finset.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, exists_exists_and_eq_and]
  constructor
  · exact h1
  · constructor
    · intro l hl; specialize h2 l hl
      rw [← AffineSubspace.Parallel.direction_eq (shift_para v l)]
      exact h2
    · constructor
      · intro x hx
        simp only [shiftSet, AffineEquiv.constVAdd_apply, vadd_eq_add, Set.image_add_left,
          Set.mem_preimage] at hx
        obtain ⟨l, hl1, hl2⟩ := h3 (-v + x) hx
        use l; constructor
        · assumption
        · simp only [shiftLine, Function.Embedding.coeFn_mk, shiftLineMap, AffineSubspace.mem_map,
            AffineEquiv.coe_toAffineMap, AffineEquiv.constVAdd_apply, vadd_eq_add]
          use -v + x; constructor
          · assumption
          · simp
      · rw [← h4]
        symm
        have := sunnyPred
        have := eqAffSubOfPlane
        apply Finset.card_bij'
          (fun L ↦ (fun _ ↦ shiftLine v L)) (fun L' ↦ (fun _ ↦ shiftLine (-v) L'))
        · intro L hL
          simp only [Finset.mem_filter] at hL
          simp only [Finset.mem_filter, Finset.mem_map']
          constructor
          · tauto
          · apply shift_sunny; tauto
        · intro L' hL'; simp only [Finset.mem_filter, Finset.mem_map] at hL'
          obtain ⟨⟨L, hL1, hL2⟩, hS'⟩ := hL'
          simp only [Finset.mem_filter, hS', shift_sunny, and_true]
          rw [← hL2, shift_line_inv]; assumption
        · intros; rw [shift_line_inv]
        · intros; nth_rw 1 [show v = -(-v) by simp]; rw [shift_line_inv]

/-- Preparation lemma for `reduce_count_and_cover`.
After removing a non-sunny line `L` from `lines`, the same `countAndCover` property holds
with `lines \ {L}` and `g \ L`. -/
lemma reduce_count_and_cover' (lines : Finset AffSubOfPlane) (L : AffSubOfPlane) (hL : L ∈ lines)
    (g : Set Plane) (n nS : ℕ) :
    have := sunnyPred
    have := eqAffSubOfPlane
    countAndCover lines g (n + 1) nS → ¬Sunny L →
    countAndCover (lines.erase L) (g \ L) n nS := by
  dsimp only [countAndCover, Lean.Elab.WF.paramLet]
  intro ⟨h1, h2, h3, h4⟩ hS
  constructor
  · simp [h1, hL]
  · constructor
    · intro L' hL'
      exact h2 L' (by simp only [Finset.mem_erase, ne_eq] at hL'; tauto)
    · constructor
      · intro x hx
        simp only [Set.mem_diff, SetLike.mem_coe] at hx
        obtain ⟨L', hL'⟩ := h3 x (by tauto)
        use L'; simp only [Finset.mem_erase, ne_eq, hL', and_true]
        intro hC
        rw [hC] at hL'
        tauto
      · rw [← h4]
        congr 1
        ext L'; simp only [Finset.mem_filter, Finset.mem_erase, ne_eq, and_congr_left_iff,
          and_iff_right_iff_imp]
        intro hS' hL' hC
        rw [hC] at hS'
        contradiction

/-- If `countAndCover _ (grid (n + 1)) (n + 1) nS` holds for a set of lines that contains
an edge of `grid (n + 1)`, then `countAndCover _ (grid n) n nS` holds for a set of lines. -/
lemma reduce_count_and_cover (lines : Finset AffSubOfPlane) (n nS : ℕ) :
    countAndCover lines (grid (n + 1)) (n + 1) nS →
    (∃ d, edgeLine (n + 1) d ∈ lines) →
    ∃ lines' : Finset AffSubOfPlane, countAndCover lines' (grid n) n nS := by
  have := eqAffSubOfPlane
  intro h ⟨d, hL⟩
  have : ¬Sunny (edgeLine (n + 1) d) := by
    rw [edgeLine, sunny_slope] <;> fin_cases d <;> simp [aEdge, bEdge]
  apply reduce_count_and_cover' lines (edgeLine (n + 1) d) hL at h
  specialize h this
  apply shift_count_and_cover (v := !₂[gridShiftX d, gridShiftY d]) at h
  use shiftLines !₂[gridShiftX d, gridShiftY d] (lines.erase (edgeLine (n + 1) d))
  convert h
  rw [← grid_shift n d]

/-- Given reals numbers `M > 0` and `a, b, c ∈ (0, M)`, the points
`(1, a + 1)`, `(b + 1, 1)`, `(c + 1, M - c + 1)` are not colinear. -/
lemma not_colinear (L : AffSubOfPlane) (M a b c: ℝ) :
    finrank ℝ L.direction = 1 → M > 0 → 0 < a → a < M → 0 < b → b < M → 0 < c → c < M →
    !₂[1, a + 1] ∈ L → !₂[b + 1, 1] ∈ L → !₂[c + 1, M - c + 1] ∈ L → False := by
  intro hL hM ha0 haM hb0 hbM hc0 hcM hpa hpb hpc
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
lemma not_colinear_nat (L : AffSubOfPlane) (M a b c: ℕ) :
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

/-- If `L` goes through `(x1, y1)` and `(x2, y2)`, and `x1 ≠ x2`, `y1 ≠ y2`, `x2 - x1 ≠ y1 - y2`,
then `L` is sunny. -/
lemma line_sunny_two_points (L : AffSubOfPlane) (x1 y1 x2 y2 : ℝ)
    (h1 : !₂[x1, y1] ∈ L) (h2 : !₂[x2, y2] ∈ L)
    (hx : x1 ≠ x2) (hy : y1 ≠ y2) (hxy : x2 - x1 ≠ y1 - y2) : Sunny L := by
  rw [Sunny]
  constructor
  · rw [← x_ax_line]
    intro hp
    symm at hp
    have := line_para_two_points 0 1 0 (by simp) L x1 y1 x2 y2 hp h1 h2
    have : y1 = y2 := by linarith
    contradiction
  · constructor
    · rw [← y_ax_line]
      intro hp
      symm at hp
      have := line_para_two_points 1 0 0 (by simp) L x1 y1 x2 y2 hp h1 h2
      have : x1 = x2 := by linarith
      contradiction
    · rw [← xy0_line]
      intro hp
      symm at hp
      have := line_para_two_points 1 1 0 (by simp) L x1 y1 x2 y2 hp h1 h2
      have : x2 - x1 = y1 - y2 := by linarith
      contradiction

section FindLines
variable (lines : Finset AffSubOfPlane)
variable (n nS : ℕ)
variable (x y : Plane)
variable (h : countAndCover lines (grid n) n nS)
variable (hx : x ∈ grid n)
variable (hy : y ∈ grid n)

/-- `findLine lines n nS x h hx` chooses a line in `lines` that goes through `x` -/
noncomputable def findLine :=
  Classical.choose (h.right.right.left x hx)

/-- `findLine lines n nS x h hx` chooses a line in `lines` that goes through `x` -/
lemma find_line_correct :
    findLine lines n nS x h hx ∈ lines ∧ x ∈ findLine lines n nS x h hx := by
  have := Classical.choose_spec (h.right.right.left x hx)
  simpa [findLine]

/-- If `findLine` finds the same line that goes through different points `x` and `y`,
and if the non-degenerate line `a * x + b * y + c = 0` passes through `x` and `y`,
then `a * x + b * y + c = 0` is in `lines`. -/
lemma find_same_line (a b c : ℝ)
    (hxy : x ≠ y)
    (hEq : findLine lines n nS x h hx = findLine lines n nS y h hy)
    (hab : a ≠ 0 ∨ b ≠ 0)
    (hxL : x ∈ line a b c)
    (hyL : y ∈ line a b c) :
    line a b c ∈ lines := by
  let L := findLine lines n nS x h hx
  have hL : L ∈ lines := by dsimp only [L]; simp [find_line_correct]
  suffices L = line a b c by rwa [← this]
  apply get_line_eq (a := x) (b := y) <;> (try assumption)
  · dsimp only [countAndCover] at h
    exact h.right.left L hL
  · apply line_rank; assumption
  · dsimp only [L]; simp [find_line_correct]
  · dsimp only [L]; rw [hEq]; simp [find_line_correct]

/-- The points on the three edges of `grid n` -/
def edgePoint (d : Fin 3) (k : Fin n) : Plane :=
  match d with
  | 0 => !₂[(1 : ℕ), (k.val + 1 : ℕ)]   -- left edge
  | 1 => !₂[(k.val + 1 : ℕ), (1 : ℕ)]   -- bottom edge
  | 2 => !₂[(k.val + 1 : ℕ), (n - k.val : ℕ)]   -- diagonal edge

lemma edge_point_in_grid (d : Fin 3) (i : Fin n): edgePoint n d i ∈ grid n := by
  dsimp only [edgePoint]
  fin_cases d <;> (simp only; rw [point_in_grid]; omega)

lemma edge_point_on_line (d : Fin 3) (i : Fin n) :
    edgePoint n d i ∈ edgeLine n d := by
  fin_cases d <;> (simp only [edgeLine, aEdge, bEdge, cEdge, edgePoint, point_on_line])
  · simp
  · simp
  · ring_nf; simp

/-- `findLineEdge lines n nS h d i` chooses a line in `lines` that goes through `edgePoint n d i`
using the function `findLine`. -/
noncomputable def findLineEdge (d : Fin 3) (i : Fin n) :=
  findLine lines n nS (edgePoint n d i) h (edge_point_in_grid n d i)

/-- `findLineEdge lines n nS h d i` chooses a line in `lines` that goes through `edgePoint n d i` -/
lemma find_line_edge_correct (d : Fin 3) (i : Fin n) :
    findLineEdge lines n nS h d i ∈ lines ∧ edgePoint n d i ∈ findLineEdge lines n nS h d i := by
  rw [findLineEdge]
  exact find_line_correct lines n nS (edgePoint n d i) h (edge_point_in_grid n d i)

/-- If `countAndCover lines (grid n) n nS)` and `lines` does not contain an edge line of `grid n`,
then on every edge, the lines chosen by `findLineEdge` are distinct. -/
lemma cover_no_edge_line_inj (hE : ∀ (e : Fin 3), edgeLine n e ∉ lines) (d : Fin 3) :
    Function.Injective (findLineEdge lines n nS h d) := by
  dsimp only [Function.Injective]
  intro i j hij
  by_contra hC
  suffices edgeLine n d ∈ lines by specialize hE d; contradiction
  dsimp [edgeLine]
  let x := edgePoint n d i
  let y := edgePoint n d j
  apply find_same_line lines n nS
    (edgePoint n d i) (edgePoint n d j) h (edge_point_in_grid n d i) (edge_point_in_grid n d j)
  · dsimp only [edgePoint]; fin_cases d <;> try (
      simp only
      intro hC'; rw [vec_eq] at hC'; obtain ⟨hC'1, hC'2⟩ := hC'
      norm_cast at hC'1; norm_cast at hC'2
      omega )
  · assumption
  · dsimp [aEdge, bEdge]; fin_cases d <;> simp
  · rw [← edgeLine]; apply edge_point_on_line
  · rw [← edgeLine]; apply edge_point_on_line

/-- If `countAndCover lines (grid n) n nS)` and `lines` does not contain an edge line of `grid n`,
then for every edge, every line in `lines` must be chosen by a point on that edge. -/
lemma cover_no_edge_line_surj (hE : ∀ (e : Fin 3), edgeLine n e ∉ lines) (d : Fin 3) :
    Finset.map
      ⟨findLineEdge lines n nS h d,
      cover_no_edge_line_inj lines n nS h hE d⟩
      Finset.univ = lines := by
  set R := Finset.map
    ⟨findLineEdge lines n nS h d,
    cover_no_edge_line_inj lines n nS h hE d⟩
    Finset.univ
  have : #R = n := by simp [R]
  have : R ⊆ lines := by
    intro x hx
    simp only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and,
      R] at hx
    obtain ⟨i, hi⟩ := hx;
    rw [← hi]
    simp [find_line_edge_correct]
  apply Finset.eq_of_subset_of_card_le <;> try (first | assumption | omega)
  have := h.left
  omega

/-- The points on the three corners of `grid n` -/
def cornerPoint (hn : n > 1) (c : Fin 3) : Plane := match c with
  | 0 => edgePoint n 0 ⟨0, by omega⟩    -- lower left corner
  | 1 => edgePoint n 0 ⟨n - 1, by omega⟩    -- upper corner
  | 2 => edgePoint n 1 ⟨n - 1, by omega⟩    -- right corner

/-- Every corner of `grid n` belongs to two edgle lines. -/
lemma corner_point_on_edge (hn : n > 1) :
    cornerPoint n hn 0 = edgePoint n 0 ⟨0, by omega⟩ ∧
    cornerPoint n hn 0 = edgePoint n 1 ⟨0, by omega⟩ ∧
    cornerPoint n hn 1 = edgePoint n 0 ⟨n - 1, by omega⟩ ∧
    cornerPoint n hn 1 = edgePoint n 2 ⟨0, by omega⟩ ∧
    cornerPoint n hn 2 = edgePoint n 2 ⟨n - 1, by omega⟩ ∧
    cornerPoint n hn 2 = edgePoint n 1 ⟨n - 1, by omega⟩
    := by
  dsimp only [cornerPoint, edgePoint]
  repeat rw [vec_eq]
  have : (n - 1 : ℕ) + (1 : ℝ) = n ∧ 1 = (n : ℝ) - (n - 1 : ℕ) := by
    simp only [n_minus_plus n hn, true_and]
    rw [← n_minus_plus n hn]; ring
  all_goals simpa

/-- `findLineCorner lines n nS h hn c` chooses a line in `lines` that goes through
`cornerPoint n hn c` using the function `findLine`. -/
noncomputable def findLineCorner (hn : n > 1) (c : Fin 3) := match c with
  | 0 => findLineEdge lines n nS h 0 ⟨0, by omega⟩
  | 1 => findLineEdge lines n nS h 0 ⟨n - 1, by omega⟩
  | 2 => findLineEdge lines n nS h 1 ⟨n - 1, by omega⟩

/-- `findLineCorner lines n nS h hn c` chooses a line in `lines` that goes through
`cornerPoint n hn c`. -/
lemma find_line_corner_correct (hn : n > 1) (c : Fin 3) :
    findLineCorner lines n nS h hn c ∈ lines ∧
    cornerPoint n hn c ∈ findLineCorner lines n nS h hn c := by
  fin_cases c <;>
    (dsimp only [findLineCorner, cornerPoint]; exact find_line_edge_correct lines n nS h _ _)

/-- The line chosen by `findLineCorner` at each of the three corners equals to the line
chosen by `findLineEdge` at corresponding points on two edge lines. -/
lemma find_line_corner_eq_edge (hn : n > 1) :
    findLineCorner lines n nS h hn 0 = findLineEdge lines n nS h 0 ⟨0, by omega⟩ ∧
    findLineCorner lines n nS h hn 0 = findLineEdge lines n nS h 1 ⟨0, by omega⟩ ∧
    findLineCorner lines n nS h hn 1 = findLineEdge lines n nS h 0 ⟨n - 1, by omega⟩ ∧
    findLineCorner lines n nS h hn 1 = findLineEdge lines n nS h 2 ⟨0, by omega⟩ ∧
    findLineCorner lines n nS h hn 2 = findLineEdge lines n nS h 1 ⟨n - 1, by omega⟩ ∧
    findLineCorner lines n nS h hn 2 = findLineEdge lines n nS h 2 ⟨n - 1, by omega⟩ := by
  simp only [findLineCorner]; simp only [Fin.isValue, true_and]
  simp only [findLineEdge]
  constructor
  · congr
  · constructor
    · congr; rw [edgePoint, edgePoint]; rw [vec_eq]
      simp only [Nat.cast_one, zero_add, Nat.cast_add, tsub_zero, true_and]
      exact n_minus_plus n hn
    · congr; rw [edgePoint, edgePoint]; rw [vec_eq]
      simp only [Nat.cast_add, Nat.cast_one, tsub_le_iff_right, le_add_iff_nonneg_right, zero_le,
        Nat.cast_sub, true_and]
      rw [← n_minus_plus n hn]; ring

/-- If `countAndCover lines (grid n) n nS)` and `lines` does not contain an edge line of `grid n`,
then the three points chosen by  `findLineCorner` are distinct. -/
lemma cover_no_edge_corner_inj (hE : ∀ (e : Fin 3), edgeLine n e ∉ lines) (hn : n > 1) :
    findLineCorner lines n nS h hn 0 ≠ findLineCorner lines n nS h hn 1 ∧
    findLineCorner lines n nS h hn 0 ≠ findLineCorner lines n nS h hn 2 ∧
    findLineCorner lines n nS h hn 1 ≠ findLineCorner lines n nS h hn 2 := by
  have line_corner_eq_edge := find_line_corner_eq_edge lines n nS h hn
  simp only [findLineCorner]
  constructor
  · intro hC; apply cover_no_edge_line_inj (hE := hE) at hC; simp only [Fin.mk.injEq] at hC; omega
  · constructor
    · rw [show findLineEdge lines n nS h 0 ⟨0, by omega⟩ =
        findLineEdge lines n nS h 1 ⟨0, by omega⟩ by tauto]
      have := cover_no_edge_line_inj lines n nS h hE 1
      simp only [Function.Injective] at this
      intro hC
      have := @this ⟨0, by omega⟩ ⟨n - 1, by omega⟩ hC
      simp only [Fin.mk.injEq] at this
      omega
    · rw [show findLineEdge lines n nS h 0 ⟨n - 1, by omega⟩ =
        findLineEdge lines n nS h 2 ⟨0, by omega⟩ by tauto]
      rw [show findLineEdge lines n nS h 1 ⟨n - 1, by omega⟩ =
        findLineEdge lines n nS h 2 ⟨n - 1, by omega⟩ by tauto]
      have := cover_no_edge_line_inj lines n nS h hE 2
      simp only [Function.Injective] at this
      intro hC
      have := @this ⟨0, by omega⟩ ⟨n - 1, by omega⟩ hC
      simp only [Fin.mk.injEq] at this
      omega

/-- If `countAndCover lines (grid n) n nS)`, `n = 3` and `lines` does not contain an edge line of
`grid n`, then `nS = 3`. -/
lemma cover_no_edge_3_lines
    (h : countAndCover lines (grid n) n nS)
    (hE : ∀ (e : Fin 3), edgeLine n e ∉ lines)
    (hn : n > 1) (hn3 : n = 3):
    nS = 3 := by
  have ⟨h1, h2, h3, h4⟩ := h
  let La := findLineCorner lines n nS h hn 0
  let Lb := findLineCorner lines n nS h hn 1
  let Lc := findLineCorner lines n nS h hn 2
  have hLa := find_line_corner_correct lines n nS h hn 0
  have hLb := find_line_corner_correct lines n nS h hn 1
  have hLc := find_line_corner_correct lines n nS h hn 2
  have := eqAffSubOfPlane
  have Leq: {La, Lb, Lc} = lines := by
    have Lsubset: {La, Lb, Lc} ⊆ lines := by
      intro L; simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (hL | hL | hL) <;> (rw [hL]; tauto)
    have Lcard: #{La, Lb, Lc} = 3 := by
      rw [Finset.card_eq_three]
      use La, Lb, Lc
      have corner_inj := cover_no_edge_corner_inj lines n nS h hE hn
      tauto
    apply Finset.eq_of_subset_of_card_le
    · exact Lsubset
    · rw [h1, hn3, Lcard]
  have lineMember : ∀ L, (L ∈ lines → L = La ∨ L = Lb ∨ L = Lc) := by
    intro L hL
    rw [← Leq] at hL
    simp only [Finset.mem_insert, Finset.mem_singleton] at hL
    exact hL
  have : !₂[1, 1] ∈ La ∧ !₂[2, 2] ∈ La ∧
      !₂[1, 3] ∈ Lb ∧ !₂[2, 1] ∈ Lb ∧
      !₂[1, 2] ∈ Lc ∧ !₂[3, 1] ∈ Lc := by
    have edge_correct := find_line_edge_correct lines n nS h
    have line_inj := cover_no_edge_line_inj lines n nS h hE
    have line_corner_eq_edge := find_line_corner_eq_edge lines n nS h hn
    have corner_inj := cover_no_edge_corner_inj lines n nS h hE hn
    repeat' constructor
    · rw [show !₂[1, 1] = cornerPoint n hn 0 by simp [cornerPoint, edgePoint]]; tauto
    · rw [show !₂[2, 2] = edgePoint n 2 ⟨1, by omega⟩ by simp [edgePoint, hn3]]
      convert (edge_correct 2 ⟨1, by omega⟩).right
      set L := findLineEdge lines n nS h 2 ⟨1, by omega⟩
      have : L = La ∨ L = Lb ∨ L = Lc := by
        apply lineMember L
        simp [L, edge_correct 2 ⟨1, by omega⟩]
      have : L ≠ Lb := by
        intro hC
        dsimp only [Fin.isValue, L] at hC
        rw [show Lb = findLineEdge lines n nS h 2 ⟨0, by omega⟩ by tauto] at hC
        have := line_inj 2 hC
        simp at this
      have : L ≠ Lc := by
        intro hC
        dsimp only [Fin.isValue, L] at hC
        rw [show Lc = findLineEdge lines n nS h 2 ⟨n - 1, by omega⟩ by tauto] at hC
        have := line_inj 2 hC
        simp only [Fin.mk.injEq] at this
        omega
      tauto
    · rw [show !₂[1, 3] = cornerPoint n hn 1 by simp [cornerPoint, edgePoint, hn3]]; tauto
    · rw [show !₂[2, 1] = edgePoint n 1 ⟨1, by omega⟩ by simp [edgePoint]]
      convert (edge_correct 1 ⟨1, by omega⟩).right
      set L := findLineEdge lines n nS h 1 ⟨1, by omega⟩
      have : L = La ∨ L = Lb ∨ L = Lc := by
        apply lineMember L
        simp [L, edge_correct 1 ⟨1, by omega⟩]
      have : L ≠ La := by
        intro hC
        dsimp only [Fin.isValue, L] at hC
        rw [show La = findLineEdge lines n nS h 1 ⟨0, by omega⟩ by tauto] at hC
        have := line_inj 1 hC
        simp at this
      have : L ≠ Lc := by
        intro hC
        dsimp only [Fin.isValue, L] at hC
        rw [show Lc = findLineEdge lines n nS h 1 ⟨n - 1, by omega⟩ by tauto] at hC
        have := line_inj 1 hC
        simp only [Fin.mk.injEq] at this
        omega
      tauto
    · rw [show !₂[1, 2] = edgePoint n 0 ⟨1, by omega⟩ by simp [edgePoint]]
      convert (edge_correct 0 ⟨1, by omega⟩).right
      set L := findLineEdge lines n nS h 0 ⟨1, by omega⟩
      have : L = La ∨ L = Lb ∨ L = Lc := by
        apply lineMember L
        simp [L, edge_correct 0 ⟨1, by omega⟩]
      have : L ≠ La := by
        intro hC
        dsimp only [Fin.isValue, L] at hC
        rw [show La = findLineEdge lines n nS h 0 ⟨0, by omega⟩ by tauto] at hC
        have := line_inj 0 hC
        simp at this
      have : L ≠ Lb := by
        intro hC
        dsimp only [Fin.isValue, L] at hC
        rw [show Lb = findLineEdge lines n nS h 0 ⟨n - 1, by omega⟩ by tauto] at hC
        have := line_inj 0 hC
        simp only [Fin.mk.injEq] at this
        omega
      tauto
    · rw [show !₂[3, 1] = cornerPoint n hn 2 by simp [cornerPoint, edgePoint, hn3]]; tauto
  have hSa: Sunny La := by apply line_sunny_two_points La 1 1 2 2 <;> try (first | tauto | norm_num)
  have hSb: Sunny Lb := by apply line_sunny_two_points Lb 1 3 2 1 <;> try (first | tauto | norm_num)
  have hSc: Sunny Lc := by apply line_sunny_two_points Lc 3 1 1 2 <;> try (first | tauto | norm_num)
  rw [← h4, ← Leq, ← hn3, ← h1, ← Leq]
  simp only
  congr 1
  ext L
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, and_iff_left_iff_imp]
  rintro (hL | hL | hL) <;> (rw [hL]; assumption)

/-- It is impossible to have `countAndCover lines (grid n) n nS)`, `n ≥ 4` and `lines` does not
contain an edge line of `grid n`. -/
lemma cover_no_edge_4_impossible
    (h : countAndCover lines (grid n) n nS)
    (hE : ∀ (e : Fin 3), edgeLine n e ∉ lines)
    (hn : n > 1) (hn4 : n ≥ 4): False := by
  have := eqAffSubOfPlane
  have ⟨h1, h2, h3, h4⟩ := h
  have edge_correct := find_line_edge_correct lines n nS h
  have line_surj := cover_no_edge_line_surj lines n nS h hE
  have hLa := find_line_corner_correct lines n nS h hn 0
  have hLb := find_line_corner_correct lines n nS h hn 1
  have hLc := find_line_corner_correct lines n nS h hn 2
  have line_corner_eq_edge := find_line_corner_eq_edge lines n nS h hn
  have corner_inj := cover_no_edge_corner_inj lines n nS h hE hn
  set La := findLineCorner lines n nS h hn 0
  set Lb := findLineCorner lines n nS h hn 1
  set Lc := findLineCorner lines n nS h hn 2
  have : #(((lines.erase La).erase Lb).erase Lc) ≥ 1 := by
    rw [Finset.card_erase_of_mem, Finset.card_erase_of_mem, Finset.card_erase_of_mem]
    · omega
    · tauto
    · simp only [Finset.mem_erase, ne_eq]; tauto
    · simp only [Finset.mem_erase, ne_eq]; tauto
  simp only [ge_iff_le, Finset.one_le_card] at this
  obtain ⟨Ld, hLd⟩ := Finset.Nonempty.exists_mem this
  simp only [Finset.mem_erase, ne_eq] at hLd
  obtain ⟨hLdLc, hLdLb, hLdLa, hLdLine⟩ := hLd
  have hLd : ∀ (d : Fin 3), ∃ i, findLineEdge lines n nS h d i = Ld := by
    intro d
    rw [← line_surj d] at hLdLine
    rw [Finset.mem_map] at hLdLine
    obtain ⟨i, hi1, hi2⟩ := hLdLine
    use i; exact hi2
  -- i is the index of the point on edge 0 (i.e. left edge) that lies on Ld
  obtain ⟨i, hi⟩ := hLd 0
  have : i.val > 0 := by
    by_contra
    have hC : i.val = 0 := by omega
    have : Ld = La := by
      rw [← hi, show La = findLineEdge lines n nS h 0 ⟨0, by omega⟩ by tauto]
      congr 1; rw [Fin.ext_iff]; exact hC
    contradiction
  have : i.val < n - 1 := by
    by_contra
    have hC : i.val = n - 1 := by omega
    have : Ld = Lb := by
      rw [← hi, show Lb = findLineEdge lines n nS h 0 ⟨n - 1, by omega⟩ by tauto]
      congr 1; rw [Fin.ext_iff]; exact hC
    contradiction
  have hi': (!₂[1, (i.val + 1 : ℕ)] : Plane) ∈ Ld := by
    rw [← hi]
    convert (edge_correct 0 i).right
    dsimp only [edgePoint]
    rw [vec_eq]; simp
  -- j is the index of the point on edge 1 (i.e. bottom edge) that lies on Ld
  obtain ⟨j, hj⟩ := hLd 1
  have : j.val > 0 := by
    by_contra
    have hC : j.val = 0 := by omega
    have : Ld = La := by
      rw [← hj, show La = findLineEdge lines n nS h 1 ⟨0, by omega⟩ by tauto]
      congr 1; rw [Fin.ext_iff]; exact hC
    contradiction
  have : j.val < n - 1 := by
    by_contra
    have hC : j.val = n - 1 := by omega
    have : Ld = Lc := by
      rw [← hj, show Lc = findLineEdge lines n nS h 1 ⟨n - 1, by omega⟩ by tauto]
      congr 1; rw [Fin.ext_iff]; exact hC
    contradiction
  have hj': (!₂[(j.val + 1 : ℕ), 1] : Plane) ∈ Ld := by
    rw [← hj]
    convert (edge_correct 1 j).right
    dsimp only [edgePoint]
    rw [vec_eq]; simp
  -- k is the index of the point on edge 2 (i.e. diagonal edge) that lies on Ld
  obtain ⟨k, hk⟩ := hLd 2
  have : k.val > 0 := by
    by_contra
    have hC : k.val = 0 := by omega
    have : Ld = Lb := by
      rw [← hk, show Lb = findLineEdge lines n nS h 2 ⟨0, by omega⟩ by tauto]
      congr 1; rw [Fin.ext_iff]; exact hC
    contradiction
  have : k.val < n - 1 := by
    by_contra
    have hC : k.val = n - 1 := by omega
    have : Ld = Lc := by
      rw [← hk, show Lc = findLineEdge lines n nS h 2 ⟨n - 1, by omega⟩ by tauto]
      congr 1; rw [Fin.ext_iff]; exact hC
    contradiction
  have hk': (!₂[(k.val + 1 : ℕ), (n - 1 - k.val + 1: ℕ)] : Plane) ∈ Ld := by
    rw [← hk]
    convert (edge_correct 2 k).right
    dsimp only [edgePoint]
    rw [vec_eq]; constructor
    · rfl
    · norm_cast; omega
  -- (1, i + 1), (j + 1, 1), (k + 1, n - k) are not colinear
  apply not_colinear_nat Ld (n - 1) i j k <;> try assumption
  · apply h2; exact hLdLine
  · omega

end FindLines

/-- If `countAndCover lines (grid n) n nS)` and `lines` does not contain an edge line of
`grid n`, then `n = 3 ∧ nS = 3`. -/
lemma cover_edge (lines : Finset AffSubOfPlane) (n nS : ℕ)
    (hn : n > 1)
    (h : countAndCover lines (grid n) n nS)
    (hE : ∀ (e : Fin 3), edgeLine n e ∉ lines) :
    (n = 3 ∧ nS = 3) := by
  have := eqAffSubOfPlane
  have ⟨h1, h2, h3, h4⟩ := h
  have hLa := find_line_corner_correct lines n nS h hn 0
  have hLb := find_line_corner_correct lines n nS h hn 1
  have hLc := find_line_corner_correct lines n nS h hn 2
  have corner_inj := cover_no_edge_corner_inj lines n nS h hE hn
  set La := findLineCorner lines n nS h hn 0
  set Lb := findLineCorner lines n nS h hn 1
  set Lc := findLineCorner lines n nS h hn 2
  by_cases n = 2
  · have : 2 < #lines := by
      rw [Finset.two_lt_card_iff]
      use La, Lb, Lc; tauto
    omega
  · by_cases hn3 : n = 3
    · have := cover_no_edge_3_lines lines n nS h hE hn hn3
      tauto
    · exfalso
      apply cover_no_edge_4_impossible lines n nS h hE hn
      omega

/-- If `countAndCover lines (grid n) n nS)`, then `nS ≤ n` and `nS ∈ {0, 1, 3}`.
Proved by induction on `n` of the above fact for all `lines`. -/
lemma any_cover (lines : Finset AffSubOfPlane) (n nS : ℕ) :
    countAndCover lines (grid n) n nS → (nS ≤ n ∧ (nS = 0 ∨ nS = 1 ∨ nS = 3)) := by
  have := sunnyPred
  revert lines
  induction n with
  | zero =>
    intro lines h; dsimp only [countAndCover] at h; obtain ⟨h1, h2, h3, h4⟩ := h
    simp only [Finset.card_eq_zero] at h1; rw [h1] at h4
    simp only [Finset.filter_empty, Finset.card_empty] at h4; simp [h4]
  | succ n ih =>
    intro lines h
    obtain (hn | hn | hn | hn) : n = 0 ∨ n = 1 ∨ n = 2 ∨ n ≥ 3 := by omega
    · dsimp only [countAndCover] at h; obtain ⟨h1, h2, h3, h4⟩ := h
      have : nS ≤ n + 1 := by rw [← h4, ← h1]; exact @Finset.card_filter_le _ lines Sunny sunnyPred
      omega
    · have := cover_edge lines (n + 1) nS (by omega) h
      have : ∃ d, edgeLine (n + 1) d ∈ lines := by
        by_contra hC; push_neg at hC
        specialize this hC
        omega
      have ⟨lines', h'⟩ := reduce_count_and_cover lines n nS h this
      have := ih lines' h'
      omega
    · have := cover_edge lines (n + 1) nS (by omega) h
      obtain (this | hnS3) : (∃ d, edgeLine (n + 1) d ∈ lines) ∨ nS = 3 := by
        by_contra hC; push_neg at hC
        specialize this hC.left
        omega
      · have ⟨lines', h'⟩ := reduce_count_and_cover lines n nS h this
        have := ih lines' h'
        omega
      · omega
    · have := cover_edge lines (n + 1) nS (by omega) h
      have : (∃ d, edgeLine (n + 1) d ∈ lines) := by
        by_contra hC; push_neg at hC
        specialize this hC
        omega
      have ⟨lines', h'⟩ := reduce_count_and_cover lines n nS h this
      have := ih lines' h'
      omega

/-- `countAndStrongCover lines g n nS` means:
`countAndCover lines g n nS` (i.e. `lines` has `n` lines,
every point in `g` is covered by a line in `lines`,
and the number of sunny lines in `lines` is `nS`)
and every line in `lines` goes through at least one point in `g`.
This is used to inductively construct strong covers of `grid n`
with exactly `0`, `1`, or `3` sunny lines. -/
def countAndStrongCover (lines : Finset AffSubOfPlane) (g : Set Plane) (n nS : ℕ) :=
  countAndCover lines g n nS ∧ ∀ l ∈ lines, ∃ x ∈ g, x ∈ l

/-- It is possible to have `countAndStrongCover lines (grid 0) 0 0)`. -/
lemma zero_sunny :
    ∃ lines : Finset AffSubOfPlane, countAndStrongCover lines (grid 0) 0 0 := by
  use ∅
  simp only [countAndStrongCover, countAndCover, Finset.card_empty, Finset.notMem_empty,
    IsEmpty.forall_iff, implies_true, false_and, exists_const, imp_false, Finset.filter_empty,
    and_true, true_and]
  intro x hx
  dsimp only [grid, Fin.isValue, Nat.reduceAdd, Set.mem_setOf_eq] at hx
  omega

/-- It is possible to have `countAndStrongCover lines (grid 1) 1 1)`. -/
lemma one_sunny :
    ∃ lines : Finset AffSubOfPlane, countAndStrongCover lines (grid 1) 1 1 := by
  let line1 := line (-1) 1 0
  let lines1 : Finset AffSubOfPlane := {line1}
  use lines1
  dsimp only [countAndStrongCover, countAndCover, lines1]
  constructor
  · simp only [Finset.card_singleton, Finset.mem_singleton, forall_eq, exists_eq_left, true_and]
    constructor
    · dsimp only [line1]; apply line_rank; simp
    · constructor
      · dsimp only [grid, Fin.isValue, Nat.reduceAdd, Set.mem_setOf_eq]
        intro x ⟨a, b, ha, hb, ha0, hb0, hab⟩
        have : a = 1 ∧ b = 1 := by omega
        simp [line1, line, ← SetLike.mem_coe, SetLike.coe, ha, hb, this]
      · have := sunnyPred;
        have : Sunny line1 := by
          dsimp only [line1]
          rw [sunny_slope] <;>
            simp only [ne_eq, neg_eq_zero, one_ne_zero, not_false_eq_true, or_self, true_and]
          norm_num
        calc
        _ = #{line1} := by
          congr 1; ext l
          simp only [Finset.mem_filter, Finset.mem_singleton, and_iff_left_iff_imp]
          intro hl; rwa [hl]
        _ = 1 := by simp
  · simp only [Finset.mem_singleton, forall_eq]
    use !₂[1, 1]; constructor
    · simp only [grid, Fin.isValue, Nat.reduceAdd, exists_and_left, Set.mem_setOf_eq,
      PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      use 1; norm_cast; simp
    · simp [line1, line,  ← SetLike.mem_coe, SetLike.coe]

/-- It is possible to have `countAndStrongCover lines (grid 3) 3 3)`. -/
lemma three_sunny :
    ∃ lines : Finset AffSubOfPlane, countAndStrongCover lines (grid 3) 3 3 := by
  let line1 := line (-1) 1 0
  let line2 := line 2 1 (-5)
  let line3 := line 1 2 (-5)
  have h12 : line1 ≠ line2 := by
    dsimp only [ne_eq, line1, line2]; intro h; apply line_eq_check at h <;> norm_num; norm_num at h
  have h13 : line1 ≠ line3 := by
    dsimp only [ne_eq, line1, line3]; intro h; apply line_eq_check at h <;> norm_num; norm_num at h
  have h23 : line2 ≠ line3 := by
    dsimp only [ne_eq, line2, line3]; intro h; apply line_eq_check at h <;> norm_num; norm_num at h
  let lines1 : Finset AffSubOfPlane :=
    Finset.cons line1 (Finset.cons line2 {line3} (by simp [h23])) (by simp [h12, h13])
  use lines1
  dsimp only [countAndStrongCover, countAndCover, lines1]
  constructor
  · simp only [Finset.card_cons, Finset.card_singleton, Nat.reduceAdd, Finset.mem_cons,
      Finset.mem_singleton, forall_eq_or_imp, forall_eq, exists_eq_or_imp, exists_eq_left, true_and]
    constructor
    · constructor
      · dsimp only [line1]; apply line_rank; simp
      · constructor <;> (dsimp only [line1, line2, line3]; apply line_rank; simp)
    · constructor
      · dsimp only [grid, Fin.isValue, Nat.reduceAdd, Set.mem_setOf_eq]; intro x hx;
        obtain ⟨a, b, ha, hb, ha0, hb0, hab⟩ := hx
        have : (a = 1 ∧ b = 1) ∨
          (a = 1 ∧ b = 2) ∨
          (a = 1 ∧ b = 3) ∨
          (a = 2 ∧ b = 1) ∨
          (a = 2 ∧ b = 2) ∨
          (a = 3 ∧ b = 1) := by omega
        obtain this | this | this | this | this | this := this <;> (
          dsimp only [line1, line2, line3];
          rw [vec_repr x, point_on_line, point_on_line, point_on_line,
            ha, hb, this.left, this.right];
          try norm_num )
      · have hS1: Sunny line1 := by dsimp only [line1]; rw [sunny_slope]; simp only [ne_eq,
          neg_eq_zero, one_ne_zero, not_false_eq_true, true_and]; norm_num; norm_num
        have hS2: Sunny line2 := by dsimp only [line2]; rw [sunny_slope] <;> simp
        have hS3: Sunny line3 := by dsimp only [line3]; rw [sunny_slope] <;> simp
        calc
        _ = #lines1 := by
          congr 1; ext l
          simp only [Finset.mem_filter, Finset.mem_cons, Finset.mem_singleton,
            and_iff_left_iff_imp, lines1]
          rintro (hl | hl | hl) <;> (rw [hl]; assumption)
        _ = 3 := by simp [lines1]
  · simp only [Finset.mem_cons, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    constructor
    · use !₂[1, 1]; constructor
      · simp only [grid, Fin.isValue, Nat.reduceAdd, exists_and_left, Set.mem_setOf_eq,
          PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        use 1; norm_cast; simp
      · simp [line1, point_on_line]
    · constructor
      · use !₂[1, 3]; constructor
        · simp only [grid, Fin.isValue, Nat.reduceAdd, exists_and_left, Set.mem_setOf_eq,
            PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
          use 1; norm_cast; simp
        · simp only [point_on_line, mul_one, one_mul, line2]
          norm_num
      · use !₂[3, 1]; constructor
        · simp only [grid, Fin.isValue, Nat.reduceAdd, exists_and_left, Set.mem_setOf_eq,
            PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
          use 3; norm_cast; simp
        · simp only [point_on_line, one_mul, mul_one, line3]
          norm_num

/-- If it is possible to have `countAndStrongCover _ (grid n) n nS)`, then it is possible to have
`countAndStrongCover _ (grid (n + 1)) (n + 1) nS)` -/
lemma extendCountAndStrongCover (lines : Finset AffSubOfPlane) (n nS : ℕ)
    (h : countAndStrongCover lines (grid n) n nS) :
    ∃ (lines' : Finset AffSubOfPlane), countAndStrongCover lines' (grid (n + 1)) (n + 1) nS := by
  dsimp only [countAndStrongCover, countAndCover]
  have ⟨⟨h1, h2, h3, h4⟩, h5⟩ := h
  have hNew : edgeLine (n + 1) 2 ∉ lines := by
    intro hC
    obtain ⟨x, hx1, hx2⟩ := h5 (edgeLine (n + 1) 2) hC
    simp only [grid, Fin.isValue, exists_and_left, Set.mem_setOf_eq] at hx1
    obtain ⟨a, ha, b, hb, ha0, hb0, hab⟩ := hx1
    have : (a : ℝ) + b ≤ (n + 1 : ℕ) := by norm_cast
    rw [vec_repr x, edgeLine, point_on_line, aEdge, bEdge, cEdge] at hx2
    rw [ha, hb] at hx2
    linarith
  use Finset.cons (edgeLine (n + 1) 2) lines hNew
  constructor
  · constructor
    · simp [h1]
    · constructor
      · intro l hl
        simp only [Fin.isValue, Finset.mem_cons] at hl
        obtain hl | hl := hl
        · rw [hl, edgeLine, aEdge, bEdge]; apply line_rank; simp
        · exact h2 l hl
      · constructor
        · intro x hx
          by_cases hE : x ∈ edgeLine (n + 1) 2
          · use edgeLine (n + 1) 2; simp [hE]
          · have : x ∈ grid n := by rw [← grid_remove_diag]; simp [hx, hE]
            obtain ⟨L, hL1, hL2⟩ := h3 x this
            use L; simp [hL1, hL2]
        · rw [← h4]; congr 1
          ext L
          simp only [Fin.isValue, Finset.mem_filter, Finset.mem_cons,
          and_congr_left_iff, or_iff_right_iff_imp]
          intro hLS hLd
          rw [hLd, edgeLine, aEdge, bEdge, sunny_slope] at hLS
          · replace hLS := hLS.right.right; contradiction
          · simp
  · intro L hL
    by_cases hE : L = edgeLine (n + 1) 2
    · use !₂[1, n + 1]
      constructor
      · use 1; simp only [Fin.isValue, PiLp.toLp_apply, Matrix.cons_val_zero, Nat.cast_one,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_lt_one, true_and]
        use n + 1; simp only [Nat.cast_add, Nat.cast_one, lt_add_iff_pos_left, add_pos_iff,
          zero_lt_one, or_true, true_and]
        omega
      · rw [hE, edgeLine, aEdge, bEdge, cEdge, point_on_line]
        ring_nf
        rw [show (1 + n : ℕ) = 1 + (n : ℝ) by norm_cast]
        ring
    · have : L ∈ lines := by apply Finset.mem_of_mem_cons_of_ne hL; exact hE
      obtain ⟨x, hx1, hx2⟩ := h5 L this
      use x; simp only [hx2, and_true]
      have := grid_remove_diag n
      rw [← this] at hx1
      rw [Set.mem_diff] at hx1
      tauto

/-- It is possible to have `countAndStrongCover _ (grid n) n nS)`, whenever `nS ≤ n` and
`nS = 0 ∨ nS = 1 ∨ nS = 3` -/
lemma existsStrongCover (n nS : ℕ) :
    nS ≤ n → (nS = 0 ∨ nS = 1 ∨ nS = 3) →
    ∃ (lines : Finset AffSubOfPlane), countAndStrongCover lines (grid n) n nS := by
  induction n with
  | zero =>
    intro h hS
    use ∅
    have : grid 0 = ∅ := by
      ext
      simp only [grid, Fin.isValue, zero_add, exists_and_left, Set.mem_setOf_eq,
        Set.mem_empty_iff_false, iff_false, not_exists, not_and, not_le]
      intro a ha b hb ha0 hb0
      omega
    rw [this]
    simp only [countAndStrongCover, countAndCover, Finset.card_empty, Finset.notMem_empty,
      IsEmpty.forall_iff, implies_true, Set.mem_empty_iff_false, false_and, exists_const,
      Finset.filter_empty, true_and, and_true]
    omega
  | succ n ih =>
    intro h hS
    by_cases hE : nS ≤ n
    · have ⟨lines, hL⟩ := ih hE hS
      exact extendCountAndStrongCover lines n nS hL
    · have : nS = n + 1 := by omega
      rw [← this]
      obtain hS | hS | hS := hS
      · rw [hS]; exact zero_sunny
      · rw [hS]; exact one_sunny
      · rw [hS]; exact three_sunny

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
  · intro ⟨lines, h1, h2, h3, h4⟩
    have : countAndCover lines (grid n) n nS := by
      simp only [countAndCover, h1, h4, and_true, true_and]
      constructor
      · exact h2
      · intro x hx
        simp only [grid, Fin.isValue, exists_and_left, Set.mem_setOf_eq] at hx
        obtain ⟨a, ha, b, hb, ha0, hb0, hab⟩ := hx
        specialize h3 a b ha0 hb0 hab
        rw [← ha, ← hb, show !₂[x 0, x 1] = x by ext i; fin_cases i <;> simp] at h3
        exact h3
    have := any_cover lines n nS this
    tauto
  · intro hS
    have : n.val ≥ 3 := by exact n.property
    have : nS ≤ n.val := by omega
    obtain ⟨lines, h⟩ := existsStrongCover n nS this hS
    use lines
    dsimp only [countAndStrongCover, countAndCover] at h
    obtain ⟨⟨h1, h2, h3, h4⟩, _⟩ := h
    simp only [h1, h4, and_true, true_and]
    constructor
    · intro L hL; exact h2 L hL
    · intro a b ha0 hb0 hab
      convert h3 !₂[(a : ℝ), (b : ℝ)] _
      simp only [grid, Fin.isValue, exists_and_left, Set.mem_setOf_eq, PiLp.toLp_apply,
        Matrix.cons_val_zero, Nat.cast_inj, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        exists_eq_left']
      tauto

end IMO2025P1
