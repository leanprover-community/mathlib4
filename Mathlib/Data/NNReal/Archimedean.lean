/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Real.Archimedean

/-!
# Nonnegative real numbers

In this file we define `NNReal` (notation: `ℝ≥0`) to be the type of non-negative real numbers,
a.k.a. the interval `[0, ∞)`. We also define the following operations and structures on `ℝ≥0`:

* the order on `ℝ≥0` is the restriction of the order on `ℝ`; these relations define a conditionally
  complete linear order with a bottom element, `ConditionallyCompleteLinearOrderBot`;

* `a + b` and `a * b` are the restrictions of addition and multiplication of real numbers to `ℝ≥0`;
  these operations together with `0 = ⟨0, _⟩` and `1 = ⟨1, _⟩` turn `ℝ≥0` into a conditionally
  complete linear ordered archimedean commutative semifield; we have no typeclass for this in
  `mathlib` yet, so we define the following instances instead:

  - `LinearOrderedSemiring ℝ≥0`;
  - `OrderedCommSemiring ℝ≥0`;
  - `CanonicallyOrderedAdd ℝ≥0`;
  - `LinearOrderedCommGroupWithZero ℝ≥0`;
  - `CanonicallyLinearOrderedAddCommMonoid ℝ≥0`;
  - `Archimedean ℝ≥0`;
  - `ConditionallyCompleteLinearOrderBot ℝ≥0`.

  These instances are derived from corresponding instances about the type `{x : α // 0 ≤ x}` in an
  appropriate ordered field/ring/group/monoid `α`, see `Mathlib.Algebra.Order.Nonneg.OrderedRing`.

* `Real.toNNReal x` is defined as `⟨max x 0, _⟩`, i.e. `↑(Real.toNNReal x) = x` when `0 ≤ x` and
  `↑(Real.toNNReal x) = 0` otherwise.

We also define an instance `CanLift ℝ ℝ≥0`. This instance can be used by the `lift` tactic to
replace `x : ℝ` and `hx : 0 ≤ x` in the proof context with `x : ℝ≥0` while replacing all occurrences
of `x` with `↑x`. This tactic also works for a function `f : α → ℝ` with a hypothesis
`hf : ∀ x, 0 ≤ f x`.

## Notations

This file defines `ℝ≥0` as a localized notation for `NNReal`.
-/

assert_not_exists Star

open Function NNReal

namespace NNReal

instance instArchimedean : Archimedean ℝ≥0 := Nonneg.instArchimedean
instance instMulArchimedean : MulArchimedean ℝ≥0 := Nonneg.instMulArchimedean
variable {ι : Type*} {f : ι → ℝ}

noncomputable instance : ConditionallyCompleteLinearOrderBot ℝ≥0 :=
  Nonneg.conditionallyCompleteLinearOrderBot (0 : ℝ)

@[norm_cast]
theorem coe_sSup (s : Set ℝ≥0) : (↑(sSup s) : ℝ) = sSup (((↑) : ℝ≥0 → ℝ) '' s) := by
  rcases Set.eq_empty_or_nonempty s with rfl|hs
  · simp
  by_cases H : BddAbove s
  · have A : sSup (Subtype.val '' s) ∈ Set.Ici 0 := by
      apply Real.sSup_nonneg
      rintro - ⟨y, -, rfl⟩
      exact y.2
    exact (@subset_sSup_of_within ℝ (Set.Ici (0 : ℝ)) _ _ (_) s hs H A).symm
  · simp only [csSup_of_not_bddAbove H, csSup_empty, bot_eq_zero', NNReal.coe_zero]
    apply (Real.sSup_of_not_bddAbove ?_).symm
    contrapose! H
    exact bddAbove_coe.1 H

@[simp, norm_cast]
theorem coe_iSup {ι : Sort*} (s : ι → ℝ≥0) : (↑(⨆ i, s i) : ℝ) = ⨆ i, ↑(s i) := by
  rw [iSup, iSup, coe_sSup, ← Set.range_comp]; rfl

@[norm_cast]
theorem coe_sInf (s : Set ℝ≥0) : (↑(sInf s) : ℝ) = sInf (((↑) : ℝ≥0 → ℝ) '' s) := by
  rcases Set.eq_empty_or_nonempty s with rfl|hs
  · simp only [Set.image_empty, Real.sInf_empty, coe_eq_zero]
    exact @subset_sInf_emptyset ℝ (Set.Ici (0 : ℝ)) _ _ (_)
  have A : sInf (Subtype.val '' s) ∈ Set.Ici 0 := by
    apply Real.sInf_nonneg
    rintro - ⟨y, -, rfl⟩
    exact y.2
  exact (@subset_sInf_of_within ℝ (Set.Ici (0 : ℝ)) _ _ (_) s hs (OrderBot.bddBelow s) A).symm

@[simp]
theorem sInf_empty : sInf (∅ : Set ℝ≥0) = 0 := by
  rw [← coe_eq_zero, coe_sInf, Set.image_empty, Real.sInf_empty]

@[norm_cast]
theorem coe_iInf {ι : Sort*} (s : ι → ℝ≥0) : (↑(⨅ i, s i) : ℝ) = ⨅ i, ↑(s i) := by
  rw [iInf, iInf, coe_sInf, ← Set.range_comp]; rfl

theorem lt_iff_exists_rat_btwn (a b : ℝ≥0) :
    a < b ↔ ∃ q : ℚ, 0 ≤ q ∧ a < Real.toNNReal q ∧ Real.toNNReal q < b :=
  Iff.intro
    (fun h : (↑a : ℝ) < (↑b : ℝ) =>
      let ⟨q, haq, hqb⟩ := exists_rat_btwn h
      have : 0 ≤ (q : ℝ) := le_trans a.2 <| le_of_lt haq
      ⟨q, Rat.cast_nonneg.1 this, by
        simp [Real.coe_toNNReal _ this, NNReal.coe_lt_coe.symm, haq, hqb]⟩)
    fun ⟨_, _, haq, hqb⟩ => lt_trans haq hqb


end NNReal

open NNReal

namespace Real

section ToNNReal

end ToNNReal

end Real

open Real

namespace NNReal

section Pow

nonrec theorem exists_pow_lt_of_lt_one {a b : ℝ≥0} (ha : 0 < a) (hb : b < 1) :
    ∃ n : ℕ, b ^ n < a := by
  simpa only [← coe_pow, NNReal.coe_lt_coe] using
    exists_pow_lt_of_lt_one (NNReal.coe_pos.2 ha) (NNReal.coe_lt_coe.2 hb)

nonrec theorem exists_mem_Ico_zpow {x : ℝ≥0} {y : ℝ≥0} (hx : x ≠ 0) (hy : 1 < y) :
    ∃ n : ℤ, x ∈ Set.Ico (y ^ n) (y ^ (n + 1)) :=
  exists_mem_Ico_zpow (α := ℝ) hx.bot_lt hy

nonrec theorem exists_mem_Ioc_zpow {x : ℝ≥0} {y : ℝ≥0} (hx : x ≠ 0) (hy : 1 < y) :
    ∃ n : ℤ, x ∈ Set.Ioc (y ^ n) (y ^ (n + 1)) :=
  exists_mem_Ioc_zpow (α := ℝ) hx.bot_lt hy

end Pow

section Inv

lemma exists_nat_pos_inv_lt {b : ℝ≥0} (hb : 0 < b) :
    ∃ (n : ℕ), 0 < n ∧ (n : ℝ≥0)⁻¹ < b :=
  b.toReal.exists_nat_pos_inv_lt hb

end Inv

section Csupr

open Set

variable {ι : Sort*} {f : ι → ℝ≥0}

nonrec theorem sSup_of_not_bddAbove {s : Set ℝ≥0} (hs : ¬BddAbove s) : SupSet.sSup s = 0 := by
  rw [← bddAbove_coe] at hs
  rw [← coe_inj, coe_sSup, NNReal.coe_zero]
  exact sSup_of_not_bddAbove hs

theorem iSup_of_not_bddAbove (hf : ¬BddAbove (range f)) : ⨆ i, f i = 0 :=
  sSup_of_not_bddAbove hf

theorem iSup_empty [IsEmpty ι] (f : ι → ℝ≥0) : ⨆ i, f i = 0 := ciSup_of_empty f

theorem iInf_empty [IsEmpty ι] (f : ι → ℝ≥0) : ⨅ i, f i = 0 := by
  rw [_root_.iInf_of_isEmpty, sInf_empty]

@[simp] lemma iSup_eq_zero (hf : BddAbove (range f)) : ⨆ i, f i = 0 ↔ ∀ i, f i = 0 := by
  cases isEmpty_or_nonempty ι
  · simp
  · simp [← bot_eq_zero', ← le_bot_iff, ciSup_le_iff hf]

@[simp]
theorem iInf_const_zero {α : Sort*} : ⨅ _ : α, (0 : ℝ≥0) = 0 := by
  rw [← coe_inj, coe_iInf]
  exact Real.iInf_const_zero

end Csupr

end NNReal

section StrictMono

open NNReal

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- If `Γ₀ˣ` is nontrivial and `f : Γ₀ →*₀ ℝ≥0` is strictly monotone, then for any positive
  `r : ℝ≥0`, there exists `d : Γ₀ˣ` with `f d < r`. -/
theorem NNReal.exists_lt_of_strictMono [h : Nontrivial Γ₀ˣ] {f : Γ₀ →*₀ ℝ≥0} (hf : StrictMono f)
    {r : ℝ≥0} (hr : 0 < r) : ∃ d : Γ₀ˣ, f d < r := by
  obtain ⟨g, hg1⟩ := (nontrivial_iff_exists_ne (1 : Γ₀ˣ)).mp h
  set u : Γ₀ˣ := if g < 1 then g else g⁻¹ with hu
  have hfu : f u < 1 := by
    rw [hu]
    split_ifs with hu1
    · rw [← map_one f]; exact hf hu1
    · have hfg0 : f g ≠ 0 :=
        fun h0 ↦ (Units.ne_zero g) ((map_eq_zero f).mp h0)
      have hg1' : 1 < g := lt_of_le_of_ne (not_lt.mp hu1) hg1.symm
      rw [Units.val_inv_eq_inv_val, map_inv₀, inv_lt_one_iff hfg0, ← map_one f]
      exact hf hg1'
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr hfu
  use u ^ n
  rwa [Units.val_pow_eq_pow_val, map_pow]

/-- If `Γ₀ˣ` is nontrivial and `f : Γ₀ →*₀ ℝ≥0` is strictly monotone, then for any positive
  real `r`, there exists `d : Γ₀ˣ` with `f d < r`. -/
theorem Real.exists_lt_of_strictMono [h : Nontrivial Γ₀ˣ] {f : Γ₀ →*₀ ℝ≥0} (hf : StrictMono f)
    {r : ℝ} (hr : 0 < r) : ∃ d : Γ₀ˣ, (f d : ℝ) < r := by
  set s : NNReal := ⟨r, le_of_lt hr⟩
  have hs : 0 < s := hr
  exact NNReal.exists_lt_of_strictMono hf hs

end StrictMono
