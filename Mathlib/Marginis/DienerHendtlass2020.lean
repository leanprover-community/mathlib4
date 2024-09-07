import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Basic
import Mathlib.Algebra.Group.Basic

import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/--

In the paper 'Differentiating Convex Functions Constructively'
by Hannes Diener and Matthew Hendtlass, the increase in
'the approximate derivatives of f ' for convex functions
f : [0, 1] → ℝ is proved in Lemma 3. Here we formalize the proof.

Note that the proof provided in the paper does not account
for the case when y = x'. Because of this (and for effieciency)
the proof was changed, but we attempt to keep the spirit of the
proof.

Also note that the formalization uses `f : ℝ → ℝ` instead of
f : ↑(Set.Icc 0 1) → ℝ because the ConvexOn in Mathlib would
require that 'AddCommMonoid ↑(Set.Icc 0 1)'.

-/


lemma Neighbors {x y z : ℝ} (f : ℝ → ℝ) (Con : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f)
    (hx : (x : ℝ) ∈ Set.Icc 0 1)(hz : (z : ℝ) ∈ Set.Icc 0 1) (ha1 : x < y)
    (ha2 : y < z) : (f y - f x) / (y - x) ≤ (f z - f y) / (z - y) := by
  have hzy : 0 < z - y := sub_pos.mpr ha2
  have hzx : 0 < z - x := sub_pos.mpr (gt_trans ha2 ha1)
  let t := (z - y) / (z - x)
  have h0_lt_t : 0 < t := div_pos hzy hzx
  have h0_le_t : 0 ≤ t := le_of_lt h0_lt_t
  have ht_lt_1 : t < 1 := (div_lt_one hzx).mpr (sub_lt_sub_left ha1 z)
  have htugh : 0 < 1 - t := sub_pos.mpr ht_lt_1
  have hduh : t + (1 - t) = 1 := by simp
  unfold ConvexOn at Con

  have Conf : f (t * x + (1 - t) * z) ≤ t * (f x) + (1 - t) * (f z) :=
    Con.2 hx hz h0_le_t (le_of_lt htugh) hduh
  have hzx_on_zx : 1 = (z - x) / (z - x) := Eq.symm (div_self (Ne.symm (ne_of_lt hzx)))

  have r1 : 1 - t = (y - x) / (z - x) := by
    rw [hzx_on_zx]
    ring_nf

  have hyt : y = t * x + (1 - t) * z := by
    calc
    y = y * 1 := by simp
    _  = y * ((z - x) / (z - x)) := by rw [hzx_on_zx]
    _  = t * x + ((y - x) / (z - x)) * z := by ring_nf
    _  = t * x + (1 - t) * z := by rw [←r1]

  rw [←hyt] at Conf
  have hzmy : z - y = t * (z - x) := by
    rw [div_mul_eq_mul_div (z - y) (z - x) (z - x),
      mul_div_assoc (z - y) (z - x) (z - x), ←hzx_on_zx]
    simp
  have hymx : y - x = (1 - t) * (z - x) := by
    rw [r1, div_mul_eq_mul_div (y - x) (z - x) (z - x),
      mul_div_assoc (y - x) (z - x) (z - x), ←hzx_on_zx]
    simp
  rw [hzmy, hymx, div_mul_eq_div_div, div_mul_eq_div_div]
  apply (div_le_div_right hzx).mpr

  apply (div_le_iff' htugh).mpr
  rw [←mul_div_assoc]


  apply (le_div_iff' h0_lt_t).mpr
  rw[mul_sub_left_distrib, mul_sub_left_distrib, mul_sub_right_distrib,
    mul_sub_right_distrib, ← sub_add]
  simp
  linarith


/-
  apply abcdef (f z) (t * f z) (f y) (t * f y) (t * f x) (t * f y)
  by_contra h
  push_neg at h
  have nConf : ¬f y ≤ t * f x + (1 - t) * f z := by
    have hm : t * f x + (1 - t) * f z < f y := by
      calc
      t * f x + (1 - t) * f z = f z - t * f z + t * f y + t * f x - t * f y := by ring_nf
      _                       < f y := h
    exact not_le_of_gt hm
  exact nConf Conf
 -/
lemma Lemma_3 {x y x' y' : ℝ} (f : ℝ → ℝ) (Con : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f)
    (hx : (x : ℝ) ∈ Set.Icc 0 1) (hy : (y : ℝ) ∈ Set.Icc 0 1)
    (hx' : (x' : ℝ) ∈ Set.Icc 0 1) (hy' : (y' : ℝ) ∈ Set.Icc 0 1)
    (ha1 : x < y) (ha2 : y ≤ x') (ha3 : x' < y') :
    (f y - f x) / (y - x) ≤ (f y' - f x') / (y' - x') := by
  have ha4 : y = x' ∨ y < x' := Decidable.eq_or_lt_of_le ha2
  cases ha4 with
  | inl equal =>
    subst y
    exact Neighbors f Con hx hy' ha1 ha3
  | inr less_than =>
    by_contra a
    push_neg at a
    have h := LT.lt.lt_or_lt a ((f x' - f y) / (x' - y))
    cases h with
    | inl hl =>
      have hln := not_le_of_gt hl
      have nhln : (f x' - f y) / (x' - y) ≤ (f y' - f x') / (y' - x') :=
        Neighbors f Con hy hy' less_than ha3
      exact hln nhln
    | inr hr =>
      have hrn := not_le_of_gt hr
      have nhrn : (f y - f x) / (y - x) ≤ (f x' - f y) / (x' - y) :=
        Neighbors f Con hx hx' ha1 less_than
      exact hrn nhrn
