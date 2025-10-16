/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Algebra.BigOperators.Field
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
  ext ⟨- | n⟩ <;>
  simp [add_div]

lemma LSeries.term_add_apply (f g : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    term (f + g) s n = term f s n + term g s n := by
  simp [term_add]

lemma LSeriesHasSum.add {f g : ℕ → ℂ} {s a b : ℂ} (hf : LSeriesHasSum f s a)
    (hg : LSeriesHasSum g s b) :
    LSeriesHasSum (f + g) s (a + b) := by
  simpa [LSeriesHasSum, term_add] using HasSum.add hf hg

lemma LSeriesSummable.add {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s)
    (hg : LSeriesSummable g s) :
    LSeriesSummable (f + g) s := by
  simpa [LSeriesSummable, ← term_add_apply] using Summable.add hf hg

@[simp]
lemma LSeries_add {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s) (hg : LSeriesSummable g s) :
    LSeries (f + g) s = LSeries f s + LSeries g s := by
  simpa [LSeries, term_add] using hf.tsum_add hg

/-!
### Negation
-/

lemma LSeries.term_neg (f : ℕ → ℂ) (s : ℂ) : term (-f) s = -term f s := by
  ext ⟨- | n⟩ <;>
  simp [neg_div]

lemma LSeries.term_neg_apply (f : ℕ → ℂ) (s : ℂ) (n : ℕ) : term (-f) s n = -term f s n := by
  simp [term_neg]

lemma LSeriesHasSum.neg {f : ℕ → ℂ} {s a : ℂ} (hf : LSeriesHasSum f s a) :
    LSeriesHasSum (-f) s (-a) := by
  simpa [LSeriesHasSum, term_neg] using HasSum.neg hf

lemma LSeriesSummable.neg {f : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s) :
    LSeriesSummable (-f) s := by
  simpa [LSeriesSummable, term_neg] using Summable.neg hf

@[simp]
lemma LSeriesSummable.neg_iff {f : ℕ → ℂ} {s : ℂ} :
    LSeriesSummable (-f) s ↔ LSeriesSummable f s :=
  ⟨fun H ↦ neg_neg f ▸ H.neg, .neg⟩

@[simp]
lemma LSeries_neg (f : ℕ → ℂ) (s : ℂ) : LSeries (-f) s = -LSeries f s := by
  simp [LSeries, term_neg_apply, tsum_neg]

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
  simpa [LSeriesHasSum, term_sub] using HasSum.sub hf hg

lemma LSeriesSummable.sub {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s)
    (hg : LSeriesSummable g s) :
    LSeriesSummable (f - g) s := by
  simpa [LSeriesSummable, ← term_sub_apply] using Summable.sub hf hg

@[simp]
lemma LSeries_sub {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s) (hg : LSeriesSummable g s) :
    LSeries (f - g) s = LSeries f s - LSeries g s := by
  simpa [LSeries, term_sub] using hf.tsum_sub hg

/-!
### Scalar multiplication
-/

lemma LSeries.term_smul (f : ℕ → ℂ) (c s : ℂ) : term (c • f) s = c • term f s := by
  ext ⟨- | n⟩ <;>
  simp [mul_div_assoc]

lemma LSeries.term_smul_apply (f : ℕ → ℂ) (c s : ℂ) (n : ℕ) :
    term (c • f) s n = c * term f s n := by
  simp [term_smul]

lemma LSeriesHasSum.smul {f : ℕ → ℂ} (c : ℂ) {s a : ℂ} (hf : LSeriesHasSum f s a) :
    LSeriesHasSum (c • f) s (c * a) := by
  simpa [LSeriesHasSum, term_smul] using hf.const_smul c

lemma LSeriesSummable.smul {f : ℕ → ℂ} (c : ℂ) {s : ℂ} (hf : LSeriesSummable f s) :
    LSeriesSummable (c • f) s := by
  simpa [LSeriesSummable, term_smul] using hf.const_smul c

lemma LSeriesSummable.of_smul {f : ℕ → ℂ} {c s : ℂ} (hc : c ≠ 0) (hf : LSeriesSummable (c • f) s) :
    LSeriesSummable f s := by
  simpa [hc] using hf.smul (c⁻¹)

lemma LSeriesSummable.smul_iff {f : ℕ → ℂ} {c s : ℂ} (hc : c ≠ 0) :
    LSeriesSummable (c • f) s ↔ LSeriesSummable f s :=
  ⟨of_smul hc, smul c⟩

@[simp]
lemma LSeries_smul (f : ℕ → ℂ) (c s : ℂ) : LSeries (c • f) s = c * LSeries f s := by
  simp [LSeries, term_smul_apply, tsum_mul_left]

/-!
### Sums
-/

section sum

variable {ι : Type*} (f : ι → ℕ → ℂ) (S : Finset ι) (s : ℂ)

@[simp]
lemma LSeries.term_sum_apply (n : ℕ) :
    term (∑ i ∈ S, f i) s n = ∑ i ∈ S, term (f i) s n := by
  rcases eq_or_ne n 0 with hn | hn <;>
  simp [hn, Finset.sum_div]

lemma LSeries.term_sum : term (∑ i ∈ S, f i) s = ∑ i ∈ S, term (f i) s :=
  funext fun _ ↦ by simp

variable {f S s}

lemma LSeriesHasSum.sum {a : ι → ℂ} (hf : ∀ i ∈ S, LSeriesHasSum (f i) s (a i)) :
    LSeriesHasSum (∑ i ∈ S, f i) s (∑ i ∈ S, a i) := by
  simpa [LSeriesHasSum, term_sum, Finset.sum_fn S fun i ↦ term (f i) s] using hasSum_sum hf

lemma LSeriesSummable.sum (hf : ∀ i ∈ S, LSeriesSummable (f i) s) :
    LSeriesSummable (∑ i ∈ S, f i) s := by
  simpa [LSeriesSummable, ← term_sum_apply] using summable_sum hf

@[simp]
lemma LSeries_sum (hf : ∀ i ∈ S, LSeriesSummable (f i) s) :
    LSeries (∑ i ∈ S, f i) s = ∑ i ∈ S, LSeries (f i) s := by
  simpa [LSeries, term_sum] using Summable.tsum_finsetSum hf

end sum
