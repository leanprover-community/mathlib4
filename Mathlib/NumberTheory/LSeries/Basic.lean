/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Michael Stoll
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.PSeries
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Ring.Real

/-!
# L-series

Given a sequence `f: ℕ → ℂ`, we define the corresponding L-series.

## Main Definitions

* `LSeries.term f s n` is the `n`th term of the L-series of the sequence `f` at `s : ℂ`.
  We define it to be zero when `n = 0`.

* `LSeries f` is the L-series with a given sequence `f` as its coefficients. This is not the
  analytic continuation (which does not necessarily exist), just the sum of the infinite series if
  it exists and zero otherwise.

* `LSeriesSummable f s` indicates that the L-series of `f` converges at `s : ℂ`.

* `LSeriesHasSum f s a` expresses that the L-series of `f` converges (absolutely) at `s : ℂ` to
  `a : ℂ`.

## Main Results

* `LSeriesSummable_of_isBigO_rpow`: the `LSeries` of a sequence `f` such that `f = O(n^(x-1))`
  converges at `s` when `x < s.re`.

* `LSeriesSummable.isBigO_rpow`: if the `LSeries` of `f` is summable at `s`, then `f = O(n^(re s))`.

## Notation

We introduce `L` as notation for `LSeries` and `↗f` as notation for `fun n : ℕ ↦ (f n : ℂ)`,
both scoped to `LSeries.notation`. The latter makes it convenient to use arithmetic functions
or Dirichlet characters (or anything that coerces to a function `N → R`, where `ℕ` coerces
to `N` and `R` coerces to `ℂ`) as arguments to `LSeries` etc.

## Reference

For some background on the design decisions made when implementing L-series in Mathlib
(and applications motivating the development), see the paper
[Formalizing zeta and L-functions in Lean](https://arxiv.org/abs/2503.00959)
by David Loeffler and Michael Stoll.

## Tags

L-series
-/

@[expose] public section

open Complex

/-!
### The terms of an L-series

We define the `n`th term evaluated at a complex number `s` of the L-series associated
to a sequence `f : ℕ → ℂ`, `LSeries.term f s n`, and provide some basic API.

We set `LSeries.term f s 0 = 0`, and for positive `n`, `LSeries.term f s n = f n / n ^ s`.
-/

namespace LSeries

/-- The `n`th term of the L-series of `f` evaluated at `s`. We set it to zero when `n = 0`. -/
noncomputable
def term (f : ℕ → ℂ) (s : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else f n / n ^ s

lemma term_def (f : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    term f s n = if n = 0 then 0 else f n / n ^ s :=
  rfl

/-- An alternate spelling of `term_def` for the case `f 0 = 0`. -/
lemma term_def₀ {f : ℕ → ℂ} (hf : f 0 = 0) (s : ℂ) (n : ℕ) :
    LSeries.term f s n = f n * (n : ℂ) ^ (-s) := by
  rw [LSeries.term]
  split_ifs with h <;> simp [h, hf, cpow_neg, div_eq_inv_mul, mul_comm]

@[simp]
lemma term_zero (f : ℕ → ℂ) (s : ℂ) : term f s 0 = 0 := rfl

-- We put `hn` first for convenience, so that we can write `rw [LSeries.term_of_ne_zero hn]` etc.
@[simp]
lemma term_of_ne_zero {n : ℕ} (hn : n ≠ 0) (f : ℕ → ℂ) (s : ℂ) :
    term f s n = f n / n ^ s :=
  if_neg hn

/--
If `s ≠ 0`, then the `if .. then .. else` construction in `LSeries.term` isn't needed, since
`0 ^ s = 0`.
-/
lemma term_of_ne_zero' {s : ℂ} (hs : s ≠ 0) (f : ℕ → ℂ) (n : ℕ) :
    term f s n = f n / n ^ s := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [term_zero, Nat.cast_zero, zero_cpow hs, div_zero]
  · rw [term_of_ne_zero hn]

lemma term_congr {f g : ℕ → ℂ} (h : ∀ {n}, n ≠ 0 → f n = g n) (s : ℂ) (n : ℕ) :
    term f s n = term g s n := by
  rcases eq_or_ne n 0 with hn | hn <;> simp [hn, h]

lemma pow_mul_term_eq (f : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    (n + 1) ^ s * term f s (n + 1) = f (n + 1) := by
  simp [term, natCast_add_one_cpow_ne_zero n _, mul_div_assoc']

lemma norm_term_eq (f : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    ‖term f s n‖ = if n = 0 then 0 else ‖f n‖ / n ^ s.re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp [hn, norm_natCast_cpow_of_pos <| Nat.pos_of_ne_zero hn]

lemma norm_term_le {f g : ℕ → ℂ} (s : ℂ) {n : ℕ} (h : ‖f n‖ ≤ ‖g n‖) :
    ‖term f s n‖ ≤ ‖term g s n‖ := by
  simp only [norm_term_eq]
  split
  · rfl
  · gcongr

lemma norm_term_le_of_re_le_re (f : ℕ → ℂ) {s s' : ℂ} (h : s.re ≤ s'.re) (n : ℕ) :
    ‖term f s' n‖ ≤ ‖term f s n‖ := by
  simp only [norm_term_eq]
  split
  · next => rfl
  · next hn => gcongr; exact Nat.one_le_cast.mpr <| Nat.one_le_iff_ne_zero.mpr hn

section positivity

open scoped ComplexOrder

lemma term_nonneg {a : ℕ → ℂ} {n : ℕ} (h : 0 ≤ a n) (x : ℝ) : 0 ≤ term a x n := by
  rw [term_def]
  split_ifs with hn
  exacts [le_rfl, mul_nonneg h (inv_natCast_cpow_ofReal_pos hn x).le]

lemma term_pos {a : ℕ → ℂ} {n : ℕ} (hn : n ≠ 0) (h : 0 < a n) (x : ℝ) : 0 < term a x n := by
  simpa only [term_of_ne_zero hn] using mul_pos h <| inv_natCast_cpow_ofReal_pos hn x

end positivity

end LSeries

/-!
### Definition of the L-series and related statements

We define `LSeries f s` of `f : ℕ → ℂ` as the sum over `LSeries.term f s`.
We also provide predicates `LSeriesSummable f s` stating that `LSeries f s` is summable
and `LSeriesHasSum f s a` stating that the L-series of `f` is summable at `s` and converges
to `a : ℂ`.
-/

open LSeries

/-- The value of the L-series of the sequence `f` at the point `s`
if it converges absolutely there, and `0` otherwise. -/
noncomputable
def LSeries (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑' n, term f s n

/-- Congruence for `LSeries` with the evaluation variable `s`. -/
lemma LSeries_congr {f g : ℕ → ℂ} (h : ∀ {n}, n ≠ 0 → f n = g n) (s : ℂ) :
    LSeries f s = LSeries g s :=
  tsum_congr <| term_congr h s

/-- `LSeriesSummable f s` indicates that the L-series of `f` converges absolutely at `s`. -/
def LSeriesSummable (f : ℕ → ℂ) (s : ℂ) : Prop :=
  Summable (term f s)

lemma LSeriesSummable_congr {f g : ℕ → ℂ} (s : ℂ) (h : ∀ {n}, n ≠ 0 → f n = g n) :
    LSeriesSummable f s ↔ LSeriesSummable g s :=
  summable_congr <| term_congr h s

open Filter in
/-- If `f` and `g` agree on large `n : ℕ` and the `LSeries` of `f` converges at `s`,
then so does that of `g`. -/
lemma LSeriesSummable.congr' {f g : ℕ → ℂ} (s : ℂ) (h : f =ᶠ[atTop] g) (hf : LSeriesSummable f s) :
    LSeriesSummable g s := by
  rw [← Nat.cofinite_eq_atTop] at h
  refine (summable_norm_iff.mpr hf).of_norm_bounded_eventually ?_
  have : term f s =ᶠ[cofinite] term g s := by
    rw [eventuallyEq_iff_exists_mem] at h ⊢
    obtain ⟨S, hS, hS'⟩ := h
    refine ⟨S \ {0}, diff_mem hS <| (Set.finite_singleton 0).compl_mem_cofinite, fun n hn ↦ ?_⟩
    rw [Set.mem_diff, Set.mem_singleton_iff] at hn
    simp [hn.2, hS' hn.1]
  exact this.symm.mono fun n hn ↦ by simp [hn]

open Filter in
/-- If `f` and `g` agree on large `n : ℕ`, then the `LSeries` of `f` converges at `s`
if and only if that of `g` does. -/
lemma LSeriesSummable_congr' {f g : ℕ → ℂ} (s : ℂ) (h : f =ᶠ[atTop] g) :
    LSeriesSummable f s ↔ LSeriesSummable g s :=
  ⟨fun H ↦ H.congr' s h, fun H ↦ H.congr' s h.symm⟩

theorem LSeries.eq_zero_of_not_LSeriesSummable (f : ℕ → ℂ) (s : ℂ) :
    ¬ LSeriesSummable f s → LSeries f s = 0 :=
  tsum_eq_zero_of_not_summable

@[simp]
theorem LSeriesSummable_zero {s : ℂ} : LSeriesSummable 0 s := by
  simp [LSeriesSummable, funext (term_def 0 s), summable_zero]

/-- This states that the L-series of the sequence `f` converges absolutely at `s` and that
the value there is `a`. -/
def LSeriesHasSum (f : ℕ → ℂ) (s a : ℂ) : Prop :=
  HasSum (term f s) a

lemma LSeriesHasSum.LSeriesSummable {f : ℕ → ℂ} {s a : ℂ}
    (h : LSeriesHasSum f s a) : LSeriesSummable f s :=
  h.summable

lemma LSeriesHasSum.LSeries_eq {f : ℕ → ℂ} {s a : ℂ}
    (h : LSeriesHasSum f s a) : LSeries f s = a :=
  h.tsum_eq

lemma LSeriesSummable.LSeriesHasSum {f : ℕ → ℂ} {s : ℂ} (h : LSeriesSummable f s) :
    LSeriesHasSum f s (LSeries f s) :=
  h.hasSum

lemma LSeriesHasSum_iff {f : ℕ → ℂ} {s a : ℂ} :
    LSeriesHasSum f s a ↔ LSeriesSummable f s ∧ LSeries f s = a :=
  ⟨fun H ↦ ⟨H.LSeriesSummable, H.LSeries_eq⟩, fun ⟨H₁, H₂⟩ ↦ H₂ ▸ H₁.LSeriesHasSum⟩

lemma LSeriesHasSum_congr {f g : ℕ → ℂ} (s a : ℂ) (h : ∀ {n}, n ≠ 0 → f n = g n) :
    LSeriesHasSum f s a ↔ LSeriesHasSum g s a := by
  simp [LSeriesHasSum_iff, LSeriesSummable_congr s h, LSeries_congr h s]

lemma LSeriesSummable.of_re_le_re {f : ℕ → ℂ} {s s' : ℂ} (h : s.re ≤ s'.re)
    (hf : LSeriesSummable f s) : LSeriesSummable f s' := by
  rw [LSeriesSummable, ← summable_norm_iff] at hf ⊢
  exact hf.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_term_le_of_re_le_re f h)

theorem LSeriesSummable_iff_of_re_eq_re {f : ℕ → ℂ} {s s' : ℂ} (h : s.re = s'.re) :
    LSeriesSummable f s ↔ LSeriesSummable f s' :=
  ⟨fun H ↦ H.of_re_le_re h.le, fun H ↦ H.of_re_le_re h.symm.le⟩

/-- The indicator function of `{1} ⊆ ℕ` with values in `ℂ`. -/
def LSeries.delta (n : ℕ) : ℂ :=
  if n = 1 then 1 else 0

/-!
### Notation
-/

@[inherit_doc]
scoped[LSeries.notation] notation "L" => LSeries

/-- We introduce notation `↗f` for `f` interpreted as a function `ℕ → ℂ`.

Let `R` be a ring with a coercion to `ℂ`. Then we can write `↗χ` when `χ : DirichletCharacter R`
or `↗f` when `f : ArithmeticFunction R` or simply `f : N → R` with a coercion from `ℕ` to `N`
as an argument to `LSeries`, `LSeriesHasSum`, `LSeriesSummable` etc. -/
scoped[LSeries.notation] notation:max "↗" f:max => fun n : ℕ ↦ (f n : ℂ)

@[inherit_doc]
scoped[LSeries.notation] notation "δ" => delta

/-!
### LSeries of 0 and δ
-/

@[simp]
lemma LSeries_zero : LSeries 0 = 0 := by
  ext
  simp [LSeries, LSeries.term]

section delta

open scoped LSeries.notation

namespace LSeries

open Nat Complex

lemma term_delta (s : ℂ) (n : ℕ) : term δ s n = if n = 1 then 1 else 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rcases eq_or_ne n 1 with hn' | hn' <;>
    simp [hn, hn', delta]

lemma mul_delta_eq_smul_delta {f : ℕ → ℂ} : f * δ = f 1 • δ := by
  ext n
  by_cases hn : n = 1 <;>
  simp [hn, delta]

lemma mul_delta {f : ℕ → ℂ} (h : f 1 = 1) : f * δ = δ := by
  rw [mul_delta_eq_smul_delta, h, one_smul]

lemma delta_mul_eq_smul_delta {f : ℕ → ℂ} : δ * f = f 1 • δ :=
  mul_comm δ f ▸ mul_delta_eq_smul_delta

lemma delta_mul {f : ℕ → ℂ} (h : f 1 = 1) : δ * f = δ :=
  mul_comm δ f ▸ mul_delta h

end LSeries

/-- The L-series of `δ` is the constant function `1`. -/
lemma LSeries_delta : LSeries δ = 1 := by
  ext
  simp [LSeries, LSeries.term_delta]

end delta


/-!
### Criteria for and consequences of summability of L-series

We relate summability of L-series with bounds on the coefficients in terms of powers of `n`.
-/

/-- If the `LSeries` of `f` is summable at `s`, then `f n` is bounded in absolute value
by a constant times `n^(re s)`. -/
lemma LSeriesSummable.le_const_mul_rpow {f : ℕ → ℂ} {s : ℂ} (h : LSeriesSummable f s) :
    ∃ C, ∀ n ≠ 0, ‖f n‖ ≤ C * n ^ s.re := by
  replace h := h.norm
  use tsum fun n ↦ ‖term f s n‖
  by_contra! ⟨n, hn₀, hn⟩
  have := h.le_tsum n fun _ _ ↦ norm_nonneg _
  rw [norm_term_eq, if_neg hn₀,
    div_le_iff₀ <| Real.rpow_pos_of_pos (Nat.cast_pos.mpr <| Nat.pos_of_ne_zero hn₀) _] at this
  exact (this.trans_lt hn).false.elim

open Filter in
/-- If the `LSeries` of `f` is summable at `s`, then `f = O(n^(re s))`. -/
lemma LSeriesSummable.isBigO_rpow {f : ℕ → ℂ} {s : ℂ} (h : LSeriesSummable f s) :
    f =O[atTop] fun n ↦ (n : ℝ) ^ s.re := by
  obtain ⟨C, hC⟩ := h.le_const_mul_rpow
  refine Asymptotics.IsBigO.of_bound C <| eventually_atTop.mpr ⟨1, fun n hn ↦ ?_⟩
  convert hC n (Nat.pos_iff_ne_zero.mp hn) using 2
  rw [Real.norm_eq_abs, Real.abs_rpow_of_nonneg n.cast_nonneg, abs_of_nonneg n.cast_nonneg]

/-- If `f n` is bounded in absolute value by a constant times `n^(x-1)` and `re s > x`,
then the `LSeries` of `f` is summable at `s`. -/
lemma LSeriesSummable_of_le_const_mul_rpow {f : ℕ → ℂ} {x : ℝ} {s : ℂ} (hs : x < s.re)
    (h : ∃ C, ∀ n ≠ 0, ‖f n‖ ≤ C * n ^ (x - 1)) :
    LSeriesSummable f s := by
  obtain ⟨C, hC⟩ := h
  have hC₀ : 0 ≤ C := (norm_nonneg <| f 1).trans <| by simpa using hC 1 one_ne_zero
  have hsum : Summable fun n : ℕ ↦ ‖(C : ℂ) / n ^ (s + (1 - x))‖ := by
    simp_rw [div_eq_mul_inv, norm_mul, ← cpow_neg]
    have hsx : -s.re + x - 1 < -1 := by linarith only [hs]
    refine Summable.mul_left _ <|
      Summable.of_norm_bounded_eventually_nat (g := fun n ↦ (n : ℝ) ^ (-s.re + x - 1)) ?_ ?_
    · simpa
    · simp only [norm_norm, Filter.eventually_atTop]
      refine ⟨1, fun n hn ↦ le_of_eq ?_⟩
      simp only [norm_natCast_cpow_of_pos hn, add_re, sub_re, neg_re, ofReal_re, one_re]
      ring_nf
  refine Summable.of_norm <| hsum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
  rcases n.eq_zero_or_pos with rfl | hn
  · simpa only [term_zero, norm_zero] using norm_nonneg _
  have hn' : 0 < (n : ℝ) ^ s.re := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
  simp_rw [term_of_ne_zero hn.ne', norm_div, norm_natCast_cpow_of_pos hn, div_le_iff₀ hn',
    norm_real, Real.norm_of_nonneg hC₀, div_eq_mul_inv, mul_assoc,
    ← Real.rpow_neg <| Nat.cast_nonneg _, ← Real.rpow_add <| Nat.cast_pos.mpr hn]
  simpa using hC n <| Nat.pos_iff_ne_zero.mp hn

open Filter Finset Real Nat in
/-- If `f = O(n^(x-1))` and `re s > x`, then the `LSeries` of `f` is summable at `s`. -/
lemma LSeriesSummable_of_isBigO_rpow {f : ℕ → ℂ} {x : ℝ} {s : ℂ} (hs : x < s.re)
    (h : f =O[atTop] fun n ↦ (n : ℝ) ^ (x - 1)) :
    LSeriesSummable f s := by
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp h
  obtain ⟨m, hm⟩ := eventually_atTop.mp hC
  let C' := max C (max' (insert 0 (image (fun n : ℕ ↦ ‖f n‖ / (n : ℝ) ^ (x - 1)) (range m)))
    (insert_nonempty 0 _))
  have hC'₀ : 0 ≤ C' := (le_max' _ _ (mem_insert.mpr (Or.inl rfl))).trans <| le_max_right ..
  have hCC' : C ≤ C' := le_max_left ..
  refine LSeriesSummable_of_le_const_mul_rpow hs ⟨C', fun n hn₀ ↦ ?_⟩
  rcases le_or_gt m n with hn | hn
  · refine (hm n hn).trans ?_
    have hn₀ : (0 : ℝ) ≤ n := cast_nonneg _
    gcongr
    rw [Real.norm_eq_abs, abs_rpow_of_nonneg hn₀, abs_of_nonneg hn₀]
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn₀
    refine (div_le_iff₀ <| rpow_pos_of_pos (cast_pos.mpr hn') _).mp ?_
    refine (le_max' _ _ <| mem_insert_of_mem ?_).trans <| le_max_right ..
    exact mem_image.mpr ⟨n, mem_range.mpr hn, rfl⟩

/-- If `f` is bounded, then its `LSeries` is summable at `s` when `re s > 1`. -/
theorem LSeriesSummable_of_bounded_of_one_lt_re {f : ℕ → ℂ} {m : ℝ}
    (h : ∀ n ≠ 0, ‖f n‖ ≤ m) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable f s :=
  LSeriesSummable_of_le_const_mul_rpow hs ⟨m, fun n hn ↦ by simp [h n hn]⟩

/-- If `f` is bounded, then its `LSeries` is summable at `s : ℝ` when `s > 1`. -/
theorem LSeriesSummable_of_bounded_of_one_lt_real {f : ℕ → ℂ} {m : ℝ}
    (h : ∀ n ≠ 0, ‖f n‖ ≤ m) {s : ℝ} (hs : 1 < s) :
    LSeriesSummable f s :=
  LSeriesSummable_of_bounded_of_one_lt_re h <| by simp [hs]
