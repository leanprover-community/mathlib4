/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.NumberTheory.LSeries.Basic

/-!
# Linearity of the L-series of `f` as a function of `f`

We show that the `LSeries` of `f : ℕ → ℂ` is a linear function of `f` (assuming convergence
of both L-series when adding two functions).
-/

/-!
### Addition
-/

open LSeries

lemma LSeries.term_add (f g : ℕ → ℂ) (s : ℂ) : term (f + g) s = term f s + term g s := by
  ext ⟨- | n⟩
  · simp only [term_zero, Pi.add_apply, add_zero]
  · simp only [term_of_ne_zero (Nat.succ_ne_zero _), Pi.add_apply, add_div]

lemma LSeries.term_add_apply (f g : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    term (f + g) s n = term f s n + term g s n := by
  rw [term_add, Pi.add_apply]

lemma LSeriesHasSum.add {f g : ℕ → ℂ} {s a b : ℂ} (hf : LSeriesHasSum f s a)
    (hg : LSeriesHasSum g s b) :
    LSeriesHasSum (f + g) s (a + b) := by
  simpa only [LSeriesHasSum, term_add] using HasSum.add hf hg

lemma LSeriesSummable.add {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s)
    (hg : LSeriesSummable g s) :
    LSeriesSummable (f + g) s := by
  simpa only [LSeriesSummable, ← term_add_apply] using Summable.add hf hg

@[simp]
lemma LSeries_add {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s) (hg : LSeriesSummable g s) :
    LSeries (f + g) s = LSeries f s + LSeries g s := by
  simpa only [LSeries, term_add, Pi.add_apply] using tsum_add hf hg

/-!
### Negation
-/

lemma LSeries.term_neg (f : ℕ → ℂ) (s : ℂ) : term (-f) s = -term f s := by
  ext ⟨- | n⟩
  · simp only [term_zero, Pi.neg_apply, neg_zero]
  · simp only [term_of_ne_zero (Nat.succ_ne_zero _), Pi.neg_apply, Nat.cast_succ, neg_div]

lemma LSeries.term_neg_apply (f : ℕ → ℂ) (s : ℂ) (n : ℕ) : term (-f) s n = -term f s n := by
  rw [term_neg, Pi.neg_apply]

lemma LSeriesHasSum.neg {f : ℕ → ℂ} {s a : ℂ} (hf : LSeriesHasSum f s a) :
    LSeriesHasSum (-f) s (-a) := by
  simpa only [LSeriesHasSum, term_neg] using HasSum.neg hf

lemma LSeriesSummable.neg {f : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s) :
    LSeriesSummable (-f) s := by
  simpa only [LSeriesSummable, term_neg] using Summable.neg hf

@[simp]
lemma LSeriesSummable.neg_iff {f : ℕ → ℂ} {s : ℂ} :
    LSeriesSummable (-f) s ↔ LSeriesSummable f s :=
  ⟨fun H ↦ neg_neg f ▸ H.neg, .neg⟩

@[simp]
lemma LSeries_neg (f : ℕ → ℂ) (s : ℂ) : LSeries (-f) s = -LSeries f s := by
  simp only [LSeries, term_neg_apply, tsum_neg]

/-!
### Subtraction
-/

lemma LSeries.term_sub (f g : ℕ → ℂ) (s : ℂ) : term (f - g) s = term f s - term g s := by
  simp_rw [sub_eq_add_neg, term_add, term_neg]

lemma LSeries.term_sub_apply (f g : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    term (f - g) s n = term f s n - term g s n := by
  rw [term_sub, Pi.sub_apply]

lemma LSeriesHasSum.sub {f g : ℕ → ℂ} {s a b : ℂ} (hf : LSeriesHasSum f s a)
    (hg : LSeriesHasSum g s b) :
    LSeriesHasSum (f - g) s (a - b) := by
  simpa only [LSeriesHasSum, term_sub] using HasSum.sub hf hg

lemma LSeriesSummable.sub {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s)
    (hg : LSeriesSummable g s) :
    LSeriesSummable (f - g) s := by
  simpa only [LSeriesSummable, ← term_sub_apply] using Summable.sub hf hg

@[simp]
lemma LSeries_sub {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s) (hg : LSeriesSummable g s) :
    LSeries (f - g) s = LSeries f s - LSeries g s := by
  simpa only [LSeries, term_sub, Pi.sub_apply] using tsum_sub hf hg

/-!
### Scalar multiplication
-/

lemma LSeries.term_smul (f : ℕ → ℂ) (c s : ℂ) : term (c • f) s = c • term f s := by
  ext ⟨- | n⟩
  · simp only [term_zero, Pi.smul_apply, smul_eq_mul, mul_zero]
  · simp only [term_of_ne_zero (Nat.succ_ne_zero _), Pi.smul_apply, smul_eq_mul, Nat.cast_succ,
      mul_div_assoc]

lemma LSeries.term_smul_apply (f : ℕ → ℂ) (c s : ℂ) (n : ℕ) :
    term (c • f) s n = c * term f s n := by
  rw [term_smul, Pi.smul_apply, smul_eq_mul]

lemma LSeriesHasSum.smul {f : ℕ → ℂ} (c : ℂ) {s a : ℂ} (hf : LSeriesHasSum f s a) :
    LSeriesHasSum (c • f) s (c * a) := by
  simpa only [LSeriesHasSum, term_smul, smul_eq_mul] using hf.const_smul c

lemma LSeriesSummable.smul {f : ℕ → ℂ} (c : ℂ) {s : ℂ} (hf : LSeriesSummable f s) :
    LSeriesSummable (c • f) s := by
  simpa only [LSeriesSummable, term_smul, smul_eq_mul] using hf.const_smul c

lemma LSeriesSummable.of_smul {f : ℕ → ℂ} {c s : ℂ} (hc : c ≠ 0) (hf : LSeriesSummable (c • f) s) :
    LSeriesSummable f s := by
  simpa only [ne_eq, hc, not_false_eq_true, inv_smul_smul₀] using hf.smul (c⁻¹)

lemma LSeriesSummable.smul_iff {f : ℕ → ℂ} {c s : ℂ} (hc : c ≠ 0) :
    LSeriesSummable (c • f) s ↔ LSeriesSummable f s :=
  ⟨of_smul hc, smul c⟩

@[simp]
lemma LSeries_smul (f : ℕ → ℂ) (c s : ℂ) : LSeries (c • f) s = c * LSeries f s := by
  simp only [LSeries, term_smul_apply, tsum_mul_left]

/-!
### Sums
-/

section sum

variable {ι : Type*} (f : ι → ℕ → ℂ) (S : Finset ι) (s : ℂ)

@[simp]
lemma LSeries.term_sum_apply (n : ℕ) :
    term (∑ i ∈ S, f i) s n  = ∑ i ∈ S, term (f i) s n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [term_zero, Finset.sum_const_zero]
  · simp only [ne_eq, hn, not_false_eq_true, term_of_ne_zero, Finset.sum_apply, Finset.sum_div]

lemma LSeries.term_sum : term (∑ i ∈ S, f i) s  = ∑ i ∈ S, term (f i) s :=
  funext fun _ ↦ by rw [Finset.sum_apply]; exact term_sum_apply f S s _

variable {f S s}

lemma LSeriesHasSum.sum {a : ι → ℂ} (hf : ∀ i ∈ S, LSeriesHasSum (f i) s (a i)) :
    LSeriesHasSum (∑ i ∈ S, f i) s (∑ i ∈ S, a i) := by
  simpa only [LSeriesHasSum, term_sum, Finset.sum_fn S fun i ↦ term (f i) s] using hasSum_sum hf

lemma LSeriesSummable.sum (hf : ∀ i ∈ S, LSeriesSummable (f i) s) :
    LSeriesSummable (∑ i ∈ S, f i) s := by
  simpa only [LSeriesSummable, ← term_sum_apply] using summable_sum hf

@[simp]
lemma LSeries_sum (hf : ∀ i ∈ S, LSeriesSummable (f i) s) :
    LSeries (∑ i ∈ S, f i) s = ∑ i ∈ S, LSeries (f i) s := by
  simpa only [LSeries, term_sum, Finset.sum_apply] using tsum_sum hf

end sum
