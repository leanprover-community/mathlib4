/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.Instances.Real
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


/-- -/
lemma abs_le_inv {a x : ℝ} (ha : a > 0) (G₀ : ¬x = 0)
    (hx : |x| ≤ a⁻¹) : x⁻¹ ≤ -a ∨ a ≤ x⁻¹ := by
  apply le_abs'.mp; rw [abs_inv, le_inv_comm₀]; repeat tauto
  rw [abs_pos]; exact G₀


/-- -/
lemma close_enough {x l y : ℝ} (hlu : l < x) (hy' : 2 * |x - y| ≤ |x - l|) : l < y := by
  nth_rewrite 2 [abs_eq_self.mpr] at hy'
  repeat linarith[le_abs_self (x - y)]

/-- -/
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

/-- -/
lemma geometry_pos
    {y v : { v : Fin 2 → ℝ // ¬v = 0 }}
    (hv : dist y.1 v.1 < y.1 1)
    (hy : 0 < y.1 1) : 0 < v.1 1 := by
  by_contra H
  have g₀ : dist 0 (v.1 1) = 0 - v.1 1 := by apply abs_eq_self.mpr;linarith
  have g₁ : dist (y.1 1) 0 = y.1 1 - 0:= by apply abs_eq_self.mpr;linarith
  have g₂ : dist (y.1 1) (v.1 1) = y.1 1 - v.1 1 := by apply abs_eq_self.mpr;linarith
  have h₀: dist (y.1 1) 0 + dist 0 (v.1 1) = dist (v.1 1) (y.1 1) := by
    rw [g₀,g₁,dist_comm,g₂];ring

  have h₂: dist (v.1 1) (y.1 1) < (y.1 1)      := calc
                              _ ≤ dist v.1 y.1 := by apply dist_le_pi_dist -- the key!
                              _ < _            := by rw [dist_comm]; exact hv
  simp only [sub_zero] at g₁
  nth_rewrite 2 [← g₁] at h₂
  rw [← h₀, dist_comm] at h₂
  linarith

/-- -/
lemma geometry_neg
    {y v : { v : Fin 2 → ℝ // ¬v = 0 }}
    (hy : y.1 1 < 0)
    (hv : dist y.1 v.1 < - y.1 1) : v.1 1 < 0 := by
  have Q := @geometry_pos
    ⟨-y.1,by
      simp only [neg_eq_zero]
      intro hc
      rw [hc] at hy
      simp_all⟩
    ⟨-v.1,by
      simp only [neg_eq_zero]
      exact v.2⟩
    (by simp only [dist_neg_neg, Fin.isValue, Pi.neg_apply]; tauto)
    (by simp only [Fin.isValue, Pi.neg_apply, Left.neg_pos_iff];tauto)
  simp only [Fin.isValue, Pi.neg_apply, Left.neg_pos_iff] at Q
  tauto

/-- -/
lemma open_geometry_pos :
    IsOpen fun y : {v : Fin 2 → ℝ // v ≠ 0} ↦ 0 < y.1 1 := by
  rw [isOpen_iff_ball_subset]
  intro y hy
  use {(u,v) | dist u v < y.1 1}
  constructor
  · rw [Metric.mem_uniformity_dist]
    use y.1 1; simp_all only [ne_eq, gt_iff_lt, Set.mem_setOf_eq, implies_true, and_true]; tauto
  · intro v hv; exact geometry_pos hv hy

/-- -/
lemma open_geometry_neg :
    IsOpen fun y : {v : Fin 2 → ℝ // v ≠ 0} ↦ y.1 1 < 0 := by
  rw [isOpen_iff_ball_subset]
  intro y hy
  use {(u,v) | dist u v < - y.1 1}
  constructor
  · rw [Metric.mem_uniformity_dist]
    use -y.1 1; simp_all only [ne_eq, gt_iff_lt, Left.neg_pos_iff, Set.mem_setOf_eq, implies_true,
      and_true]; tauto
  · intro v hv; exact geometry_neg hy hv

/-- -/
lemma same_set₀ : fun y : {v : Fin 2 → ℝ // v ≠ 0} ↦ y.1 1 < 2 * y.1 1 = fun y ↦ 0 < y.1 1 := by
  ext y; constructor; repeat (intro;linarith)

/-- -/
lemma same_set₁ : fun y : {v : Fin 2 → ℝ // v ≠ 0} ↦ y.1 1 > 2 * y.1 1 = fun y ↦ 0 > y.1 1 := by
  ext y; constructor; repeat (intro;linarith)

/-- -/
lemma same_set₂ : fun y : {v : Fin 2 → ℝ // v ≠ 0} ↦ y.1 1 < (y.1 1) / 2 = fun y ↦ 0 > y.1 1 := by
  ext y; constructor; repeat (intro;linarith)

/-- -/
lemma open_nonzero
    {x : { v : Fin 2 → ℝ // v ≠ 0 }}
    (H₁ : ¬x.1 1 = 0) : ∃ t, (∀ y ∈ t, ¬y.1 1 = 0) ∧ IsOpen t ∧ x ∈ t := by
  use {y | y.1 1 ∈ Set.Ioo ((y.1 1) / 2) (2*(y.1 1))
          ∨ y.1 1 ∈ Set.Ioo (2*(y.1 1)) ((y.1 1) / 2)}
  simp only [ne_eq, Fin.isValue, Set.mem_Ioo, half_lt_self_iff, Set.mem_setOf_eq, Subtype.forall]
  constructor
  · intro _ _ haa; cases haa; repeat linarith
  · constructor
    · apply IsOpen.union
      · apply IsOpen.inter
        · exact open_geometry_pos
        · rw [same_set₀]; exact open_geometry_pos
      · apply IsOpen.inter
        · rw [same_set₁]; exact open_geometry_neg
        · rw [same_set₂]; exact open_geometry_neg
    · have : x.1 1 < 0 ∨ x.1 1 > 0 := lt_or_gt_of_ne H₁
      cases this
      · right; constructor; repeat linarith
      · left;  constructor; repeat linarith

/-- -/
theorem dist_cone_pos_pos {a : Fin 2 → ℝ} (h₀ : a 1 = 0) (h₁ : a 0 > 0) {s : ℝ} (hs : s ≥ 0) :
    (a 0 / (s+1) > 0) ∧ ∀ y, dist y a ≤ (a 0 / (s+1)) → y 1 > 0 → s ≤ y 0 / y 1 := by
  constructor
  · exact div_pos h₁ (add_pos_of_nonneg_of_pos hs Real.zero_lt_one)
  · intro y hay  hy₀
    rw [le_div_iff₀ hy₀]
    have g₁ : dist (y 1) (a 1) ≤ dist y a := dist_le_pi_dist y a 1
    have g₄ : - (y 0) + (a 0) ≤ dist (y 0) (a 0) := by
      rw [dist_comm,add_comm];apply le_abs_self
    have g₅ : dist y a * (s+1) ≤ a 0 / (s+1) * (s+1):= by
      apply mul_le_mul_of_nonneg hay
      linarith;exact dist_nonneg;linarith
    have g₇ : dist y a * (s+1) ≤ a 0 := by
      field_simp at g₅; exact g₅
    simp_all only [gt_iff_lt, ge_iff_le, dist_zero_right, Real.norm_eq_abs, neg_add_le_iff_le_add]
    calc
    s * y 1 ≤ s * dist y a     := mul_le_mul_of_nonneg_left (by linarith[le_abs_self (y 1)]) hs
    _       ≤ a 0 - (dist y a) := by linarith[dist_le_pi_dist y a 1]
    _       ≤ y 0              := by linarith[dist_le_pi_dist y a 0]

/-- -/
theorem dist_cone_pos_neg {a : Fin 2 → ℝ} (h₀ : a 1 = 0) (h₁ : a 0 > 0) {s : ℝ} (hs : s ≥ 0) :
    (a 0 / (s+1) > 0) ∧ ∀ y, dist y a ≤ (a 0 / (s+1)) → y 1 < 0 → y 0 / y 1 ≤  -s := by
  let Q₀ := dist_cone_pos_pos h₀ h₁ hs
  constructor
  · tauto
  · intro y hy hy'
    have : dist ![y 0, -y 1] a = dist y a := by
      repeat rw [dist_pi_def]
      congr
      ext z
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, coe_nndist]
      cases (Nat.le_one_iff_eq_zero_or_eq_one.mp (Fin.is_le z)) with
      | inl h =>
        have : z = 0 := by apply Fin.eq_of_val_eq; simp_all
        rw [this];tauto
      | inr h =>
        have : z = 1 := by apply Fin.eq_of_val_eq; simp_all
        rw [this];simp only [Fin.isValue, Matrix.cons_val_one, Matrix.head_cons];rw [h₀];simp;
    have Q := Q₀.2 (![y 0,- y 1]) (by rw [this]; exact hy) (by simp only [Fin.isValue,
      Matrix.cons_val_one, Matrix.head_cons, gt_iff_lt, Left.neg_pos_iff];tauto)
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at Q
    linarith

/-- -/
theorem dist_cone_neg_pos {a : Fin 2 → ℝ} (h₀ : a 1 = 0) (h₁ : a 0 <  0)
    {s : ℝ} (hs : s ≥ 0) :
    (- a 0 / (s+1) > 0) ∧ ∀ y, dist y a ≤ (- a 0 / (s+1)) → y 1 > 0 → y 0 / y 1 ≤  - s := by
  have Q := @dist_cone_pos_neg ![-a 0,a 1] h₀ (by
  simp only [Fin.isValue, Matrix.cons_val_zero,
    gt_iff_lt, Left.neg_pos_iff];exact h₁) s hs
  rw [h₀] at Q
  have hn : ![-a 0, 0] = -a := by
    ext z;simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Pi.neg_apply]
    have : z.1 = 0 ∨ z.1 = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp (Fin.is_le z)
    cases this with
    | inl h =>
      have : z = 0 := by apply Fin.eq_of_val_eq; simp_all
      rw [this];simp
    | inr h =>
      have : z = 1 := by apply Fin.eq_of_val_eq; simp_all
      rw [this]
      simp only [Fin.isValue, Matrix.cons_val_one, Matrix.head_cons, zero_eq_neg]; exact h₀
  constructor
  · exact Q.1
  · intro y hay hy
    have Q₂ := Q.2
    have W := @Q₂ (-y) (by
      simp only [Fin.isValue, Matrix.cons_val_zero]; rw [hn, dist_neg_neg]
      exact hay) (by simp only [Fin.isValue, Pi.neg_apply, Left.neg_neg_iff];tauto)
    simp only [Fin.isValue, Pi.neg_apply, neg_div_neg_eq] at W
    exact W

/-- -/
theorem dist_cone_neg_neg {a : Fin 2 → ℝ} (h₀ : a 1 = 0) (h₁ : a 0 <  0) {s : ℝ} (hs : s ≥ 0) :
    (- a 0 / (s+1) > 0) ∧ ∀ y, dist y a ≤ (- a 0 / (s+1)) → y 1 < 0 → y 0 / y 1 ≥ s := by
  have Q := @dist_cone_pos_pos ![-a 0,a 1] (by tauto) (by
    simp only [Fin.isValue,
    Matrix.cons_val_zero, gt_iff_lt, Left.neg_pos_iff];tauto) s hs

  have Q₂ := Q.2
  constructor
  · have Q₁ := Q.1;tauto
  · intro y hay hy;

    have W := @Q₂ (-y) (by
      have : ![-a 0, a 1] = -a := by
        ext z
        have : z.1 = 0 ∨ z.1 = 1 := by
          refine Nat.le_one_iff_eq_zero_or_eq_one.mp ?_
          exact Fin.is_le z
        cases this with
        | inl h =>
          have : z = 0 := by apply Fin.eq_of_val_eq; simp_all
          rw [this];tauto
        | inr h =>
          have : z = 1 := by apply Fin.eq_of_val_eq; simp_all
          rw [this]
          simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_one,
            Matrix.head_cons, Pi.neg_apply]
          rw [h₀]
          simp
      rw [this]
      have : dist (-y) (-a) = dist y a := by exact dist_neg_neg y a
      rw [this]
      tauto
    ) (by simp only [Fin.isValue, Pi.neg_apply, gt_iff_lt, Left.neg_pos_iff];tauto)
    simp only [Fin.isValue, Pi.neg_apply, neg_div_neg_eq] at W
    tauto

/-- -/
theorem dist_cone_pos {a : Fin 2 → ℝ} (h₀ : a 1 = 0) (h₁ : a 0 > 0) {s : ℝ} (hs : s ≥ 0) :
    ∃ δ > 0, ∀ y, dist y a ≤ δ →
      (y 1 < 0 → y 0 / y 1 ≤  -s)
      ∧ (y 1 > 0 → y 0 / y 1 ≥  s) := by
  use a 0 / (s+1)
  constructor
  · exact (dist_cone_pos_pos h₀ h₁ hs).1
  · intro y hy;
    constructor
    · exact (dist_cone_pos_neg h₀ h₁ hs).2 y hy
    · exact (dist_cone_pos_pos h₀ h₁ hs).2 y hy

/-- -/
theorem dist_cone_neg {a : Fin 2 → ℝ} (h₀ : a 1 = 0) (h₁ : a 0 < 0) {s : ℝ} (hs : s ≥ 0) :
    ∃ δ > 0, ∀ y, dist y a ≤ δ →
      (y 1 > 0 → y 0 / y 1 ≤  -s)
      ∧ (y 1 < 0 → y 0 / y 1 ≥  s) := by
  use - a 0 / (s+1)
  constructor
  · exact (dist_cone_neg_pos h₀ h₁ hs).1
  · intro y hy;
    constructor
    · exact (dist_cone_neg_pos h₀ h₁ hs).2 y hy
    · exact (dist_cone_neg_neg h₀ h₁ hs).2 y hy

/-- -/
lemma pos_or_neg {a : { v : Fin 2 → ℝ // v ≠ 0 }} (H : a.1 1 = 0) : a.1 0 > 0 ∨ a.1 0 < 0 := by
  by_contra H
  push_neg at H
  have : a.1 0 = 0 := by linarith
  have : a.1 = 0 := by
    ext z
    have : z.1 = 0 ∨ z.1 = 1 := by
      refine Nat.le_one_iff_eq_zero_or_eq_one.mp ?_
      exact Fin.is_le z
    cases this with
    | inl h =>
      have : z = 0 := by apply Fin.eq_of_val_eq; tauto
      rw [this];tauto
    | inr h =>
      have : z = 1 := by apply Fin.eq_of_val_eq; tauto
      rw [this];tauto
  apply a.2;tauto
