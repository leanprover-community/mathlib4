/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Data.Real.Sqrt
-- import Mathlib.Topology.Instances.Real
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Group.AddTorsor

/-!
# Useful lemmas about real numbers

We prove some useful lemmas toward the homeomorphism in `OnePointHomemorph`.

## Main results

* `pos_or_neg` : nonzero vector being positive or negative.

## Tags

calculus
-/


/-- absolute value ≤ inverse. -/
lemma abs_le_inv {a x : ℝ} (ha : a > 0) (G₀ : ¬x = 0)
    (hx : |x| ≤ a⁻¹) : x⁻¹ ≤ -a ∨ a ≤ x⁻¹ := by
  apply le_abs'.mp; rw [abs_inv, le_inv_comm₀]; repeat tauto
  rw [abs_pos]; exact G₀

/-- Symmetrize. -/
lemma symmetrize
    (P : ℝ → Prop)
    {a₀ : ℝ} (ha₀ : ∀ b ≤ a₀, P b)
    {a₁ : ℝ} (ha₁ : ∀ b, a₁ ≤ b → P b) :
    ∀ (b : ℝ), b ≤ -(max |a₀| |a₁|) ∨ (max |a₀| |a₁|) ≤ b → P b := by
    intro b hb
    let a : ℝ := max |a₀| |a₁|
    cases hb with
    |inl hl =>
      apply ha₀
      calc b ≤ -a := hl
        (-a) ≤ a₀ := by
            rw [neg_le]
            calc -a₀ ≤ |a₀| := neg_le_abs a₀
                 |a₀| ≤ a    := le_max_left |a₀| |a₁|
    |inr hr =>
      apply ha₁
      calc _ ≤  |a₁| := le_abs_self a₁
           _ ≤ a     := le_max_right |a₀| |a₁|
           _ ≤ _     := hr



/-- Geometry positive. -/
lemma geometryPos {n : ℕ} {k : Fin n}
    {y v : Fin n → ℝ}
    (hv : dist y v < y k)
    (hy : 0 < y k) : 0 < v k := by
  by_contra H
  have g₀ : dist 0 (v k) = 0 - v k := by apply abs_eq_self.mpr;linarith
  have g₁ : dist (y k) 0 = y k - 0:= by apply abs_eq_self.mpr;linarith
  have g₂ : dist (y k) (v k) = y k - v k := by apply abs_eq_self.mpr;linarith
  have h₀: dist (y k) 0 + dist 0 (v k) = dist (v k) (y k) := by
    rw [g₀,g₁,dist_comm,g₂];ring

  have h₂: dist (v k) (y k) < (y k)      := calc
                              _ ≤ dist v y := by apply dist_le_pi_dist -- the key!
                              _ < _            := by rw [dist_comm]; exact hv
  simp only [sub_zero] at g₁
  nth_rewrite 2 [← g₁] at h₂
  rw [← h₀, dist_comm] at h₂
  linarith

/-- Geometry positive. -/
lemma geometry_pos {n : ℕ} {k : Fin n}
    {P : (Fin n → ℝ) → Prop} {y v : { v : Fin n → ℝ // P v }}
    (hv : dist y.1 v.1 < y.1 k) (hy : 0 < y.1 k) : 0 < v.1 k := geometryPos hv hy

/-- Geometry negative. -/
lemma geometry_neg {n : ℕ} {k : Fin n}
    {P : (Fin n → ℝ) → Prop} {y v : { v : Fin n → ℝ // P v }}
    (hy : y.1 k < 0)
    (hv : dist y.1 v.1 < - y.1 k) : v.1 k < 0 := by
  have R := @geometryPos n k (-y.1) (-v.1)
    (by simp only [dist_neg_neg, Pi.neg_apply]; tauto)
    (by simp only [Pi.neg_apply,
      Left.neg_pos_iff]; tauto)
  simp only [Pi.neg_apply, Left.neg_pos_iff] at R
  exact R



/-- Open geometry positive. -/
lemma open_geometry_pos {n : ℕ} {k : Fin n} {P : (Fin n → ℝ) → Prop} :
    IsOpen fun y : {v : Fin n → ℝ // P v} ↦ 0 < y.1 k := by
  rw [isOpen_iff_ball_subset]
  intro y hy
  use {(u,v) | dist u v < y.1 k}
  constructor
  · rw [Metric.mem_uniformity_dist]
    use y.1 k; simp_all only [ne_eq, gt_iff_lt, Set.mem_setOf_eq, implies_true, and_true]; tauto
  · intro v hv; exact geometry_pos hv hy

/-- Open geometry negative. -/
lemma open_geometry_neg {n : ℕ} {k : Fin n} {P : (Fin n → ℝ) → Prop} :
    IsOpen fun y : {v : Fin n → ℝ // P v} ↦ y.1 k < 0 := by
  rw [isOpen_iff_ball_subset]
  intro y hy
  use {(u,v) | dist u v < - y.1 k}
  constructor
  · rw [Metric.mem_uniformity_dist]
    use -y.1 k; simp_all only [ne_eq, gt_iff_lt, Left.neg_pos_iff, Set.mem_setOf_eq, implies_true,
      and_true]; tauto
  · intro v hv; exact geometry_neg hy hv


/-- Less than /2. -/
lemma lt_div_two (y : ℝ) : y < y / 2 ↔ y < 0 := by constructor; repeat (intro;linarith)

/-- Open nonzero. -/
lemma open_nonzero {n : ℕ} {k : Fin n} {P : (Fin n → ℝ) → Prop}
    {x : { v : Fin n → ℝ // P v}}
    (H₁ : ¬x.1 k = 0) : ∃ t, (∀ y ∈ t, ¬y.1 k = 0) ∧ IsOpen t ∧ x ∈ t := by
  use {y | y.1 k ∈ Set.Ioo ((y.1 k) / 2) (2*(y.1 k))
          ∨ y.1 k ∈ Set.Ioo (2*(y.1 k)) ((y.1 k) / 2)}
  simp only [ne_eq, Fin.isValue, Set.mem_Ioo, half_lt_self_iff, Set.mem_setOf_eq, Subtype.forall]
  constructor
  · intro _ _ haa; cases haa <;> linarith
  · constructor
    · apply IsOpen.union
      · apply IsOpen.inter
        · exact open_geometry_pos
        · simp_rw [two_mul]; simp only [lt_add_iff_pos_right]; exact open_geometry_pos
      · apply IsOpen.inter
        · simp_rw [two_mul]; simp only [add_lt_iff_neg_left]; exact open_geometry_neg
        · simp_rw [lt_div_two]; exact open_geometry_neg
    · have : x.1 k < 0 ∨ x.1 k > 0 := lt_or_gt_of_ne H₁
      cases this
      · right; constructor <;> linarith
      · left;  constructor <;> linarith

/-- Distance cone. -/
theorem distConePosPos {n : ℕ} {i j : Fin n} {a : Fin n → ℝ} (h₀ : a j = 0) (h₁ : a i > 0)
    {s : ℝ} (hs : s ≥ 0) :
    (a i / (s+1) > 0) ∧ ∀ y, dist y a ≤ (a i / (s+1)) → y j > 0 → s ≤ y i / y j := by
  constructor
  · exact div_pos h₁ (add_pos_of_nonneg_of_pos hs Real.zero_lt_one)
  · intro y hay  hy₀
    rw [le_div_iff₀ hy₀]
    have g₁ : dist (y j) (a j) ≤ dist y a := dist_le_pi_dist y a j
    have g₄ : - (y i) + (a i) ≤ dist (y i) (a i) := by
      rw [dist_comm,add_comm];apply le_abs_self
    have g₅ : dist y a * (s+1) ≤ a i / (s+1) * (s+1):= by
      apply mul_le_mul_of_nonneg hay
      linarith;exact dist_nonneg;linarith
    have g₇ : dist y a * (s+1) ≤ a i := by
      field_simp at g₅; exact g₅
    simp_all only [gt_iff_lt, ge_iff_le, dist_zero_right, Real.norm_eq_abs, neg_add_le_iff_le_add]
    calc
    s * y j ≤ s * dist y a     := mul_le_mul_of_nonneg_left (by linarith[le_abs_self (y j)]) hs
    _       ≤ a i - (dist y a) := by linarith[dist_le_pi_dist y a j]
    _       ≤ y i              := by linarith[dist_le_pi_dist y a i]


/-- Multiply a designated coordinate by -1. -/
def flipPos {n : ℕ} (j : Fin n) (y : Fin n → ℝ) (k : Fin n) : ℝ :=
    ite (j = k) (- y k) (y k)

/-- Distance cone. -/
theorem distConePosNeg {n : ℕ} {i j : Fin n} {a : Fin n → ℝ} (h₀ : a j = 0) (h₁ : a i > 0)
    {s : ℝ} (hs : s ≥ 0) :
    (a i / (s+1) > 0) ∧ ∀ y, dist y a ≤ (a i / (s+1)) → y j < 0 → y i / y j ≤  -s := by
  let Q₀ := distConePosPos h₀ h₁ hs
  constructor
  · tauto
  · intro y hy hy'
    have : dist (flipPos j y) a = dist y a := by
      repeat rw [dist_pi_def]
      congr
      ext z
      unfold flipPos
      simp only [coe_nndist]
      by_cases H : j = z
      · subst H
        simp only [↓reduceIte]
        rw [h₀]
        simp
      · rw [if_neg H]
    have Q := Q₀.2 (flipPos j y) (by rw [this]; exact hy) (by
      unfold flipPos
      simp only [↓reduceIte, gt_iff_lt, Left.neg_pos_iff]
      tauto
    )
    unfold flipPos at *
    simp only [↓reduceIte] at Q
    simp_all only [ge_iff_le]
    have : j ≠ i := by aesop
    rw [if_neg this] at Q
    linarith

/-- Distance cone. -/
theorem distConeNegPos {n : ℕ} {i j : Fin n} {a : Fin n → ℝ} (h₀ : a j = 0) (h₁ : a i <  0)
    {s : ℝ} (hs : s ≥ 0) :
    (- a i / (s+1) > 0) ∧ ∀ y, dist y a ≤ (- a i / (s+1)) → y j > 0 → y i / y j ≤  - s := by
  constructor
  · have g₁ : s + 1 > 0 := by linarith
    aesop
  · intro y hy hy'
    have := (@distConePosNeg n i j (-a) (by simp_all) (by simp_all) s hs).2 (-y)
      (by simp_all) (by simp_all)
    simp_all

/-- Distance cone. -/
theorem distConeNegNeg {n : ℕ} {i j : Fin n} {a : Fin n → ℝ} (h₀ : a j = 0) (h₁ : a i <  0)
    {s : ℝ} (hs : s ≥ 0) :
    (- a i / (s+1) > 0) ∧ ∀ y, dist y a ≤ (- a i / (s+1)) → y j < 0 → y i / y j ≥ s := by
  constructor
  · have g₁ : s + 1 > 0 := by linarith
    aesop
  · intro y hy hy'
    have := (@distConePosPos n i j (-a) (by simp_all) (by simp_all) s hs).2 (-y)
      (by simp_all) (by simp_all)
    simp_all


/-- Distance cone. -/
theorem dist_cone_pos {n : ℕ} {i j : Fin n} {a : Fin n → ℝ} (h₀ : a j = 0) (h₁ : a i > 0)
    {s : ℝ} (hs : s ≥ 0) :
    ∃ δ > 0, ∀ y, dist y a ≤ δ →
      (y j < 0 → y i / y j ≤  -s)
      ∧ (y j > 0 → y i / y j ≥  s) := by
  use a i / (s+1)
  constructor
  · exact (distConePosPos h₀ h₁ hs).1
  · intro y hy;
    constructor
    · exact (distConePosNeg h₀ h₁ hs).2 y hy
    · exact (distConePosPos h₀ h₁ hs).2 y hy

/-- Distance cone. -/
theorem dist_cone_neg {n : ℕ} {i j : Fin n} {a : Fin n → ℝ} (h₀ : a j = 0) (h₁ : a i < 0)
    {s : ℝ} (hs : s ≥ 0) :
    ∃ δ > 0, ∀ y, dist y a ≤ δ →
      (y j > 0 → y i / y j ≤  -s)
      ∧ (y j < 0 → y i / y j ≥  s) := by
  use - a i / (s+1)
  constructor
  · exact (distConeNegPos h₀ h₁ hs).1
  · intro y hy;
    constructor
    · exact (distConeNegPos h₀ h₁ hs).2 y hy
    · exact (distConeNegNeg h₀ h₁ hs).2 y hy

/-- Distance cone. -/
lemma posOrNeg {n : ℕ} {a : { v : Fin n → ℝ // v ≠ 0 }} :
    ∃ j : Fin n, a.1 j > 0 ∨ a.1 j < 0 := by
  by_contra H
  push_neg at H
  have (j) : a.1 j = 0 := by linarith[H j]
  have : a.1 = 0 := by
    ext z
    aesop
  exact a.2 this

/-- Only for `Fin 2`. -/
lemma pos_or_neg {a : { v : Fin 2 → ℝ // v ≠ 0 }} (H : a.1 1 = 0) : a.1 0 > 0 ∨ a.1 0 < 0 := by
  by_contra H
  push_neg at H
  have : a.1 0 = 0 := by linarith
  have : a.1 = 0 := by
    ext z
    fin_cases z <;> (simp only [ne_eq, Fin.zero_eta, Fin.isValue, Pi.zero_apply]; tauto)
  exact a.2 this

-- used : -- abs_le_inv, open_nonzero, symmetrize, dist_cone_pos, dist_cone_neg, pos_or_neg
