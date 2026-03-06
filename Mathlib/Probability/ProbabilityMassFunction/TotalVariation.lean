/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Data.ENNReal.AbsDiff
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Total variation distance for probability mass functions

This file defines total variation distance on probability mass functions and provides a
`MetricSpace` instance for `PMF α`.

We follow the Mathlib convention of providing both an `ℝ≥0∞`-valued version (`PMF.etvDist`)
and an `ℝ`-valued version (`PMF.tvDist`), connected by `tvDist = etvDist.toReal`.

We also prove the **data processing inequality**: post-processing by a deterministic map or a
Markov kernel cannot increase total variation distance.

## Main definitions

- `PMF.etvDist p q`: the extended total variation distance, valued in `ℝ≥0∞`
- `PMF.tvDist p q`: the total variation distance, valued in `ℝ`
- `PMF.instMetricSpace`: the `MetricSpace` instance on `PMF α` via total variation distance

## Main results

- `PMF.etvDist_le_one`: total variation distance is at most 1
- `PMF.etvDist_eq_zero_iff`: distance is zero iff the PMFs are equal
- `PMF.etvDist_map_le`: data processing inequality for deterministic maps
- `PMF.etvDist_bind_right_le`: data processing inequality for Markov kernels
- `PMF.etvDist_option_punit`: closed form for distributions on `Option PUnit`

## Tags

probability mass function, total variation distance, statistical distance, data processing
inequality, metric space
-/

noncomputable section

open ENNReal

namespace ENNReal

/-- Truncated subtraction distributes over `tsum` as an inequality. -/
lemma tsum_tsub_le_tsum_tsub {α : Type*} (a b : α → ℝ≥0∞) :
    ∑' x, a x - ∑' x, b x ≤ ∑' x, (a x - b x) := by
  rw [tsub_le_iff_right]
  calc ∑' x, a x ≤ ∑' x, ((a x - b x) + b x) :=
        ENNReal.tsum_le_tsum fun x => le_tsub_add
    _ = ∑' x, (a x - b x) + ∑' x, b x := ENNReal.tsum_add

/-- `ENNReal.absDiff` is subadditive over infinite sums. -/
lemma absDiff_tsum_le {α : Type*} (a b : α → ℝ≥0∞) :
    ENNReal.absDiff (∑' x, a x) (∑' x, b x) ≤
      ∑' x, ENNReal.absDiff (a x) (b x) := by
  unfold ENNReal.absDiff
  calc (∑' x, a x - ∑' x, b x) + (∑' x, b x - ∑' x, a x)
      ≤ ∑' x, (a x - b x) + ∑' x, (b x - a x) :=
        add_le_add (tsum_tsub_le_tsum_tsub a b)
          (tsum_tsub_le_tsum_tsub b a)
    _ = ∑' x, ((a x - b x) + (b x - a x)) := ENNReal.tsum_add.symm

/-- Fiber decomposition for `ℝ≥0∞`-valued sums: summing over fibers then over the
base is the same as summing over the total space. -/
lemma tsum_fiber {α β : Type*} [DecidableEq β] (f : α → β)
    (g : α → ℝ≥0∞) :
    ∑' y, ∑' x, (if f x = y then g x else 0) = ∑' x, g x := by
  rw [ENNReal.tsum_comm]
  congr 1; ext x
  simp only [eq_comm (a := f x)]
  exact tsum_ite_eq (f x) (fun _ ↦ g x) (SummationFilter.unconditional β)

end ENNReal

namespace PMF

variable {α : Type*}

/-- Extended total variation distance on PMFs, valued in `ℝ≥0∞`.
Defined as `(1/2) ∑ x, absDiff (p x) (q x)`. -/
protected noncomputable def etvDist (p q : PMF α) : ℝ≥0∞ :=
  (∑' x, ENNReal.absDiff (p x) (q x)) / 2

/-- Total variation distance on PMFs, valued in `ℝ`. -/
protected noncomputable def tvDist (p q : PMF α) : ℝ :=
  (p.etvDist q).toReal

/-- `PMF.tvDist` is the `toReal` of `PMF.etvDist`. -/
lemma tvDist_def (p q : PMF α) : p.tvDist q = (p.etvDist q).toReal :=
  rfl

@[simp]
lemma etvDist_self (p : PMF α) : p.etvDist p = 0 := by
  simp [PMF.etvDist]

/-- `PMF.etvDist` is symmetric. -/
lemma etvDist_comm (p q : PMF α) : p.etvDist q = q.etvDist p := by
  simp only [PMF.etvDist, ENNReal.absDiff_comm]

/-- Triangle inequality for `PMF.etvDist`. -/
lemma etvDist_triangle (p q r : PMF α) :
    p.etvDist r ≤ p.etvDist q + q.etvDist r := by
  simp only [PMF.etvDist, ENNReal.div_add_div_same]
  exact ENNReal.div_le_div_right
    (calc ∑' x, ENNReal.absDiff (p x) (r x)
        ≤ ∑' x, (ENNReal.absDiff (p x) (q x)
            + ENNReal.absDiff (q x) (r x)) :=
          ENNReal.tsum_le_tsum fun x =>
            ENNReal.absDiff_triangle (p x) (q x) (r x)
      _ = ∑' x, ENNReal.absDiff (p x) (q x)
            + ∑' x, ENNReal.absDiff (q x) (r x) :=
          ENNReal.tsum_add) _

/-- Total variation distance is at most 1. -/
lemma etvDist_le_one (p q : PMF α) : p.etvDist q ≤ 1 := by
  calc p.etvDist q
      = (∑' x, ENNReal.absDiff (p x) (q x)) / 2 := rfl
    _ ≤ (∑' x, (p x + q x)) / 2 :=
        ENNReal.div_le_div_right
          (ENNReal.tsum_le_tsum fun x =>
            ENNReal.absDiff_le_add (p x) (q x)) _
    _ = (∑' x, p x + ∑' x, q x) / 2 := by
        rw [ENNReal.tsum_add]
    _ = (1 + 1) / 2 := by rw [p.tsum_coe, q.tsum_coe]
    _ = 2 / 2 := by norm_num
    _ = 1 := ENNReal.div_self two_ne_zero ofNat_ne_top

/-- `PMF.etvDist` is always finite. -/
lemma etvDist_ne_top (p q : PMF α) : p.etvDist q ≠ ⊤ :=
  ne_top_of_le_ne_top one_ne_top (etvDist_le_one p q)

@[simp]
lemma etvDist_eq_zero_iff {p q : PMF α} :
    p.etvDist q = 0 ↔ p = q := by
  simp only [PMF.etvDist, ENNReal.div_eq_zero_iff,
    ofNat_ne_top, or_false]
  rw [ENNReal.tsum_eq_zero]
  exact ⟨fun h => PMF.ext fun x =>
    (ENNReal.absDiff_eq_zero.mp (h x)),
    fun h => by subst h; simp⟩

@[simp]
lemma tvDist_self (p : PMF α) : p.tvDist p = 0 := by
  simp [PMF.tvDist]

/-- `PMF.tvDist` is symmetric. -/
lemma tvDist_comm (p q : PMF α) : p.tvDist q = q.tvDist p := by
  simp only [PMF.tvDist, etvDist_comm]

/-- `PMF.tvDist` is nonnegative. -/
lemma tvDist_nonneg (p q : PMF α) : 0 ≤ p.tvDist q :=
  ENNReal.toReal_nonneg

/-- Triangle inequality for `PMF.tvDist`. -/
lemma tvDist_triangle (p q r : PMF α) :
    p.tvDist r ≤ p.tvDist q + q.tvDist r := by
  rw [PMF.tvDist, PMF.tvDist, PMF.tvDist,
    ← ENNReal.toReal_add (etvDist_ne_top p q)
      (etvDist_ne_top q r)]
  exact ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr
      ⟨etvDist_ne_top p q, etvDist_ne_top q r⟩)
    (etvDist_triangle p q r)

/-- Total variation distance is at most 1. -/
lemma tvDist_le_one (p q : PMF α) : p.tvDist q ≤ 1 := by
  rw [PMF.tvDist, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono one_ne_top (etvDist_le_one p q)

@[simp]
lemma tvDist_eq_zero_iff {p q : PMF α} :
    p.tvDist q = 0 ↔ p = q := by
  rw [PMF.tvDist, ENNReal.toReal_eq_zero_iff,
    etvDist_eq_zero_iff]
  simp [etvDist_ne_top]

section DataProcessing

universe u₀

variable {α' : Type u₀} {β : Type u₀}

/-- Expansion of `Functor.map` for `PMF` in terms of indicator sums. -/
lemma map_apply_eq [DecidableEq β] (f : α' → β) (p : PMF α')
    (y : β) :
    (f <$> p) y = ∑' x, if f x = y then p x else 0 := by
  simp only [Functor.map, PMF.bind_apply]
  congr 1; ext x; split <;> simp_all [eq_comm]

/-- **Data processing inequality** for deterministic maps: post-processing by a function
cannot increase total variation distance. -/
lemma etvDist_map_le (f : α' → β)
    (p q : PMF α') :
    (f <$> p).etvDist (f <$> q) ≤ p.etvDist q := by
  classical
  simp only [PMF.etvDist]
  apply ENNReal.div_le_div_right
  calc ∑' y, ENNReal.absDiff ((f <$> p) y) ((f <$> q) y)
      = ∑' y, ENNReal.absDiff
          (∑' x, if f x = y then p x else 0)
          (∑' x, if f x = y then q x else 0) := by
          congr 1; ext y; rw [map_apply_eq, map_apply_eq]
    _ ≤ ∑' y, ∑' x, ENNReal.absDiff
          (if f x = y then p x else 0)
          (if f x = y then q x else 0) :=
          ENNReal.tsum_le_tsum fun y =>
            ENNReal.absDiff_tsum_le _ _
    _ = ∑' y, ∑' x, if f x = y
          then ENNReal.absDiff (p x) (q x) else 0 := by
          congr 1; ext y; congr 1; ext x
          split <;> simp
    _ = ∑' x, ENNReal.absDiff (p x) (q x) :=
          ENNReal.tsum_fiber f _

/-- Data processing inequality for `PMF.tvDist` under deterministic maps. -/
lemma tvDist_map_le (f : α' → β)
    (p q : PMF α') :
    (f <$> p).tvDist (f <$> q) ≤ p.tvDist q := by
  classical
  simp only [PMF.tvDist]
  exact ENNReal.toReal_mono (etvDist_ne_top p q)
    (etvDist_map_le f p q)

/-- **Data processing inequality** for Markov kernels: post-processing by a stochastic
kernel cannot increase total variation distance. -/
lemma etvDist_bind_right_le (f : α' → PMF β)
    (p q : PMF α') :
    (p.bind f).etvDist (q.bind f) ≤ p.etvDist q := by
  simp only [PMF.etvDist, PMF.bind_apply]
  apply ENNReal.div_le_div_right
  calc ∑' y, ENNReal.absDiff
        (∑' x, p x * (f x) y) (∑' x, q x * (f x) y)
      ≤ ∑' y, ∑' x, ENNReal.absDiff
          (p x * (f x) y) (q x * (f x) y) :=
        ENNReal.tsum_le_tsum fun y =>
          ENNReal.absDiff_tsum_le _ _
    _ ≤ ∑' y, ∑' x, ENNReal.absDiff (p x) (q x)
          * (f x) y :=
        ENNReal.tsum_le_tsum fun y =>
          ENNReal.tsum_le_tsum fun x =>
            ENNReal.absDiff_mul_right_le _ _ _
    _ = ∑' x, ∑' y, ENNReal.absDiff (p x) (q x)
          * (f x) y := ENNReal.tsum_comm
    _ = ∑' x, ENNReal.absDiff (p x) (q x)
          * ∑' y, (f x) y := by
        congr 1; ext x; rw [ENNReal.tsum_mul_left]
    _ = ∑' x, ENNReal.absDiff (p x) (q x) := by
        congr 1; ext x; rw [(f x).tsum_coe, mul_one]

/-- Data processing inequality for `PMF.tvDist` under Markov kernels. -/
lemma tvDist_bind_right_le (f : α' → PMF β)
    (p q : PMF α') :
    (p.bind f).tvDist (q.bind f) ≤ p.tvDist q := by
  simp only [PMF.tvDist]
  exact ENNReal.toReal_mono (etvDist_ne_top p q)
    (etvDist_bind_right_le f p q)

end DataProcessing

/-- The `MetricSpace` instance on `PMF α` induced by total variation distance. -/
noncomputable instance instMetricSpace : MetricSpace (PMF α) where
  dist := PMF.tvDist
  edist := PMF.etvDist
  dist_self := PMF.tvDist_self
  dist_comm := PMF.tvDist_comm
  dist_triangle := PMF.tvDist_triangle
  eq_of_dist_eq_zero h := tvDist_eq_zero_iff.mp h
  edist_dist p q :=
    (ENNReal.ofReal_toReal (etvDist_ne_top p q)).symm

@[simp]
lemma dist_eq_tvDist (p q : PMF α) :
    dist p q = p.tvDist q := rfl

@[simp]
lemma edist_eq_etvDist (p q : PMF α) :
    edist p q = p.etvDist q := rfl

section OptionPUnit

variable (p q : PMF (Option PUnit))

private lemma pmf_none_eq (p : PMF (Option PUnit)) :
    p none = 1 - p (some ()) := by
  have h := p.tsum_coe
  rw [tsum_fintype, Fintype.sum_option, Fintype.sum_unique]
    at h
  exact (ENNReal.sub_eq_of_eq_add (PMF.apply_ne_top p _)
    h.symm).symm

/-- Closed form for `etvDist` on binary distributions `PMF (Option PUnit)`. -/
lemma etvDist_option_punit :
    p.etvDist q =
      ENNReal.absDiff (p (some ())) (q (some ())) := by
  simp only [PMF.etvDist]
  rw [tsum_fintype, Fintype.sum_option, Fintype.sum_unique]
  rw [pmf_none_eq p, pmf_none_eq q,
    ENNReal.absDiff_tsub_tsub (PMF.coe_le_one p _)
      (PMF.coe_le_one q _) one_ne_top]
  rw [show ENNReal.absDiff (p (some ())) (q (some ()))
      + ENNReal.absDiff (p (some ())) (q (some ()))
      = 2 * ENNReal.absDiff (p (some ())) (q (some ()))
    from by ring, mul_div_assoc]
  simp [ENNReal.mul_div_cancel two_ne_zero ofNat_ne_top]

/-- Closed form for `tvDist` on binary distributions `PMF (Option PUnit)`. -/
lemma tvDist_option_punit :
    p.tvDist q =
      |(p (some ())).toReal - (q (some ())).toReal| := by
  simp only [PMF.tvDist, etvDist_option_punit]
  exact ENNReal.absDiff_toReal
    (ne_top_of_le_ne_top one_ne_top (PMF.coe_le_one p _))
    (ne_top_of_le_ne_top one_ne_top (PMF.coe_le_one q _))

end OptionPUnit

end PMF
