/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.Valued.LocallyCompact


/-!

# Adic expansions of elements of rings of integers of nonarchimedean fields.

We show that every element of a ring of integers of a nonarchimedean field can be uniquely
determined as an expansion in terms of a fixed uniformizer.

## Main definitions

* `AdicExpansion.Digits`: a preimage of the residue field which is used in the expansion.
* `AdicExpansion`: the expansion itself, implemented as a type synonym of functions from `ℕ`.

## TODO
* `AdicExpansion.evalAt`: the evaluation of the expansion at a given point.
* Show that the induced metric space has the same topology regardless of uniformizer chosen.
* `AdicExpansion.appr`: the expansion for a given element of the ring of integers, when over a
  complete discrete valuation ring.

-/

variable {K R : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CommRing R]

open scoped Valued NormedField

namespace AdicExpansion

variable [IsLocalRing R]

section Digits

variable (R) in
/-- The digits used in an adic expansion, requiring that they are in bijection with the
residue field. Zero is required to be a digit to ensure uniqueness of the expansion. -/
structure Digits where
  /-- The underlying preimage of the residue field. -/
  (carrier : Set R)
  (zero : 0 ∈ carrier)
  (bij : Set.BijOn (IsLocalRing.residue R) carrier (Set.univ))

instance : SetLike (Digits R) R := ⟨Digits.carrier, by rintro ⟨⟩ ⟨⟩; simp⟩

noncomputable
instance (digits : Digits R) : Zero digits := ⟨0, digits.zero⟩

instance (digits : Digits R) : Nonempty digits := ⟨0⟩

@[simp, norm_cast]
lemma Digits.coe_zero (digits : Digits R) : ((0 : digits) : R) = 0 := rfl

lemma Digits.ext_iff {digits : Digits R} {x y : digits} : x = y ↔ (x : R) = y := by
  simp

@[simp]
lemma Digits.isUnit_iff {digits : Digits R} {x : digits} :
    IsUnit (x : R) ↔ x ≠ 0 := by
  rw [iff_not_comm]
  constructor <;> intro h
  · simp [h]
  rw [Digits.ext_iff, Digits.coe_zero]
  exact digits.bij.injOn x.prop digits.zero (by simpa using h)

lemma Digits.not_isUnit_dvd_iff {digits : Digits R} {ϖ : R} (hϖ : ¬ IsUnit ϖ) {x : digits} :
    ϖ ∣ x ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  rw [← not_not (a := x = 0), ← ne_eq, ← isUnit_iff]
  exact not_isUnit_of_not_isUnit_dvd hϖ h

lemma Digits.coe_sub_eq_iff {digits : Digits R} {x y : digits} :
    (x : R) - y = 0 ↔ x = y := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  rw [Digits.ext_iff, ← sub_eq_zero, h]

lemma Digits.not_isUnit_dvd_sub_iff {digits : Digits R} {ϖ : R} (hϖ : ¬ IsUnit ϖ)
    {x y : digits} :
    ϖ ∣ x - y ↔ x = y := by
  constructor
  · rintro ⟨c, hc⟩
    apply_fun IsLocalRing.residue R at hc
    ext
    refine digits.bij.injOn x.prop y.prop ?_
    rw [← sub_eq_zero, ← map_sub, hc, (IsLocalRing.residue_eq_zero_iff _).mpr]
    simp [hϖ]
  · intro h
    simp [h]

end Digits

end AdicExpansion

open AdicExpansion

/-- A formal expansion of an element in the local ring, at the digits specified. Meant to
be evaluated using `AdicExpansion.evalAtUpto` and related definitions. -/
def AdicExpansion [IsLocalRing R] (d : Digits R) := ℕ → d

namespace AdicExpansion

variable [IsLocalRing R] {D : Digits R}

protected lemma ext_iff {f g : AdicExpansion D} :
    f = g ↔ ∀ n, f n = g n :=
  funext_iff

@[ext]
protected lemma ext {f g : AdicExpansion D} (h : ∀ n, f n = g n) : f = g :=
  funext h

noncomputable
instance : Zero (AdicExpansion D) := inferInstanceAs (Zero (ℕ → D))

@[simp]
lemma zero_apply (n : ℕ) : (0 : AdicExpansion D) n = 0 := rfl

/-- Evaluation of an `AdicExpansion` up to the indicated power, using the provided "base". -/
noncomputable
def evalAtUpto (ϖ : R) (f : AdicExpansion D) (n : ℕ) : R :=
  ∑ i ∈ Finset.range n, f i * ϖ ^ i

@[simp]
lemma evalAtUpto_zero (ϖ : R) (f : AdicExpansion D) :
    evalAtUpto ϖ f 0 = 0 := by
  simp only [evalAtUpto, Finset.sum_range_zero, zero_mul]

@[simp]
lemma evalAtUpto_one (ϖ : R) (f : AdicExpansion D) :
    evalAtUpto ϖ f 1 = f 0 := by
  simp [evalAtUpto]

lemma evalAtUpto_add_one (ϖ : R) (f : AdicExpansion D) (n : ℕ) :
    evalAtUpto ϖ f (n + 1) = evalAtUpto ϖ f n + f n * ϖ ^ n := by
  simp only [evalAtUpto, Finset.sum_range_succ]

@[simp]
lemma zero_evalAtUpto (ϖ : R) (n : ℕ) :
    evalAtUpto ϖ (0 : ℕ → D) n = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [evalAtUpto_add_one, ih]

@[simp]
lemma evalAtUpto_at_zero (f : AdicExpansion D) (n : ℕ) :
    evalAtUpto 0 f (n + 1) = f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [evalAtUpto_add_one, ih]
    simp

lemma congr_of_eqOn (ϖ : R) {f g : AdicExpansion D} {n : ℕ}
    (h : ∀ i < n, f i = g i) :
    evalAtUpto ϖ f n = evalAtUpto ϖ g n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [evalAtUpto_add_one]
    rw [ih (fun i hi ↦ h i (Nat.lt_succ_of_lt hi)), h _ (by simp)]

lemma mul_evalAtUpto_of_add_one (ϖ : R) (f : AdicExpansion D) (n : ℕ) :
    ϖ * evalAtUpto ϖ (f ∘ (· + 1)) n = evalAtUpto ϖ f (n + 1) - f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [evalAtUpto_add_one, Function.comp_apply, mul_add, ih]
    ring

lemma evalAtUpto_add_one' (ϖ : R) (f : AdicExpansion D) (n : ℕ) :
    evalAtUpto ϖ f (n + 1) = f 0 + ϖ * evalAtUpto ϖ (f ∘ (· + 1)) n := by
  rw [mul_evalAtUpto_of_add_one]
  ring

lemma dvd_evalAtUpto_iff_apply_zero {ϖ : R} (hϖ : ¬ IsUnit ϖ)
    {f : AdicExpansion D} {n : ℕ} :
    ϖ ∣ evalAtUpto ϖ f (n + 1) ↔ f 0 = 0 := by
  constructor
  · intro h
    induction n with
    | zero => simpa using not_isUnit_of_not_isUnit_dvd hϖ h
    | succ n ih =>
      obtain ⟨c, h⟩ := h
      rw [evalAtUpto_add_one, eq_comm, ← sub_eq_iff_eq_add, pow_succ', mul_left_comm,
        ← mul_sub] at h
      exact ih ⟨_, h.symm⟩
  · intro h
    refine ⟨evalAtUpto ϖ (f ∘ (· + 1)) n, ?_⟩
    simp [mul_evalAtUpto_of_add_one, h]

lemma evalAtUpto_eq_zero_iff [IsDomain R] {ϖ : R} (hϖ : ¬ IsUnit ϖ) (hn : ϖ ≠ 0)
    {f : AdicExpansion D} {n : ℕ} :
    evalAtUpto ϖ f (n + 1) = 0 ↔ ∀ i < n + 1, f i = 0 := by
  constructor
  · intro h
    induction n generalizing f with
    | zero => simpa [Digits.ext_iff] using h
    | succ n ih =>
      have h' := h
      rw [evalAtUpto_add_one, add_eq_zero_iff_eq_neg, ← neg_mul, mul_comm] at h'
      replace h' : ϖ ^ (n + 1) ∣ evalAtUpto ϖ f (n + 1) := by
        rw [h']
        exact ⟨_, rfl⟩
      replace h' : ϖ ∣ evalAtUpto ϖ f (n + 1) := dvd_trans (dvd_pow_self _ (by simp)) h'
      rw [dvd_evalAtUpto_iff_apply_zero hϖ, Digits.ext_iff, Digits.coe_zero] at h'
      rw [← sub_zero (evalAtUpto _ _ _), ← h', ← mul_evalAtUpto_of_add_one, h'] at h
      simp only [mul_eq_zero, hn, false_or] at h
      specialize ih h
      simp only [Function.comp_apply, Digits.ext_iff, Digits.coe_zero] at ih
      rintro (_|i) hi
      · simp [Digits.ext_iff, h']
      · simpa [Digits.ext_iff] using ih i (by linarith)
  · intro h
    rw [← zero_evalAtUpto (D := D) ϖ (n + 1)]
    refine congr_of_eqOn ϖ ?_
    simpa using h

lemma pow_not_dvd_evalAtUpto [IsDomain R] {ϖ : R} (hϖ : ¬ IsUnit ϖ) (hn : ϖ ≠ 0)
    (f : AdicExpansion D)
    (n : ℕ) (h : ∃ i < n + 1, f i ≠ 0) :
    ¬ϖ ^ (n + 1) ∣ evalAtUpto ϖ f (n + 1) := by
  contrapose! h
  rw [← evalAtUpto_eq_zero_iff hϖ hn]
  induction n generalizing f with
  | zero =>
    simp only [zero_add, pow_one, evalAtUpto_one] at h
    simpa [Digits.ext_iff] using not_isUnit_of_not_isUnit_dvd hϖ h
  | succ n ih =>
    rw [evalAtUpto_add_one, pow_succ] at h
    obtain ⟨c, h⟩ := h
    rw [mul_comm, eq_comm, ← sub_eq_iff_eq_add, mul_assoc, ← mul_sub] at h
    specialize ih _ ⟨_, h.symm⟩
    simp only [ih, mul_eq_zero, ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false,
      not_false_eq_true, pow_eq_zero_iff, hn, false_or, sub_eq_zero] at h
    replace h : f (n + 1) = 0 := by simpa using not_isUnit_of_not_isUnit_dvd hϖ ⟨_, h.symm⟩
    rw [evalAtUpto_add_one, ih, h, Digits.coe_zero]
    simp [hn]

lemma evalAtUpto_injOn [IsDomain R]
    {ϖ : R} (hϖ : ¬ IsUnit ϖ) (hϖ0 : ϖ ≠ 0) (n : ℕ) (z : D) :
    Set.InjOn (evalAtUpto ϖ · n) {f : AdicExpansion D | ∀ i ≥ n, f i = z} := by
  induction n generalizing z with
  | zero =>
    intro f hf g hg _
    simp only [ge_iff_le, zero_le, forall_const, Set.mem_setOf_eq] at hf hg
    ext
    simp [hf, hg]
  | succ n ih =>
    intro f hf g hg h
    simp only [ge_iff_le, Set.mem_setOf_eq] at hf hg h
    apply_fun (· - (f 0 : R)) at h
    apply_fun (· - (g 0 : R)) at h
    rw [← mul_evalAtUpto_of_add_one, sub_sub, add_comm (f 0 : R), ← sub_sub,
      ← mul_evalAtUpto_of_add_one, sub_eq_sub_iff_sub_eq_sub, ← mul_sub] at h
    have h0 : g 0 = f 0 := by simp [← Digits.not_isUnit_dvd_sub_iff hϖ, ← h]
    simp only [h0, sub_self, mul_eq_zero, hϖ0, false_or, sub_eq_zero] at h
    specialize ih z (fun i hi ↦ hf (i + 1) (by simpa using hi))
      (fun i hi ↦ hg (i + 1) (by simpa using hi)) h
    ext (_|n)
    · simp [h0]
    · simp [congr_fun ih n]

section CompleteSpace

open Filter Topology

variable {D : Digits 𝒪[K]}

local notation "O" => 𝒪[K]

/-- In a complete ring of integers of a nonarchimedean normed field, an adic expansion can
be summed entirely, as a limit of the partial sums. -/
noncomputable
def evalAt (ϖ : O) (f : AdicExpansion D) : O :=
  ∑' n, f n * ϖ ^ n

@[simp]
lemma evalAt_zero (ϖ : O) :
    evalAt ϖ (0 : AdicExpansion D) = 0 := by
  simp [evalAt]

lemma cauchySeq_evalAtUpto {ϖ : O} (hϖ : ¬ IsUnit ϖ) (f : AdicExpansion D) :
    CauchySeq (evalAtUpto ϖ f ·) := by
  refine NonarchimedeanAddGroup.cauchySeq_of_tendsto_sub_nhds_zero ?_
  simp only [evalAtUpto_add_one, add_sub_cancel_left]
  have := tendsto_norm.comp (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (x := ϖ) ?_)
  · simp only [norm_zero] at this
    refine squeeze_zero_norm ?_ this
    intro n
    dsimp
    refine (norm_mul_le _ _).trans ?_
    exact mul_le_of_le_one_left (norm_nonneg _) (Valued.integer.norm_le_one _)
  · rw [Valued.integer.isUnit_iff_norm_eq_one] at hϖ
    exact lt_of_le_of_ne (Valued.integer.norm_le_one _) hϖ

lemma Digits.norm_eq_one_iff {x : D} :
    ‖(x : O)‖ = 1 ↔ x ≠ 0 := by
  rw [← Valued.integer.isUnit_iff_norm_eq_one, Digits.isUnit_iff]

@[simp]
lemma Digits.norm_coe_eq_one_iff {x : D} :
    ‖((x : O) : K)‖ = 1 ↔ x ≠ 0 := by
  simp [← Digits.norm_eq_one_iff]

lemma norm_evalAtUpto {ϖ : O} (hϖ : ¬ IsUnit ϖ) (f : AdicExpansion D) (n : ℕ)
    [DecidablePred fun i : ℕ ↦ i < n + 1 ∧ f i ≠ 0]
    (h : ∃ i < n + 1, f i ≠ 0) :
    ‖evalAtUpto ϖ f (n + 1)‖ = ‖ϖ‖ ^ (Nat.find h) := by
  rcases eq_or_ne ϖ 0 with rfl|hϖ0
  · simp
    by_cases H : Nat.find h = 0
    · rw [H]
      rw [Nat.find_eq_zero] at H
      simpa using H.right
    · rw [zero_pow_eq_zero.mpr H]
      rw [← ne_eq, ← Nat.pos_iff_ne_zero, Nat.lt_find_iff] at H
      push_neg at H
      simp [H _ le_rfl]
  induction n generalizing f with
  | zero =>
    rw [(Nat.find_eq_zero h).mpr] <;>
    simpa using h
  | succ n ih =>
    rw [evalAtUpto_add_one]
    generalize hk : Nat.find h = k
    rw [Nat.find_eq_iff] at hk
    simp_rw [Nat.lt_succ_iff] at h hk
    classical
    by_cases H : ∃ i < n + 1, f i ≠ 0
    · specialize ih _ H
      have hn : ‖ϖ‖ ^ (n + 1) < ‖ϖ‖ ^ Nat.find H := by
        refine pow_lt_pow_right_of_lt_one₀ ?_ ?_ ?_
        · simp [hϖ0]
        · exact lt_of_le_of_ne (Valued.integer.norm_le_one ϖ)
            (mt Valued.integer.isUnit_iff_norm_eq_one.mpr hϖ)
        · exact (Nat.find_spec H).left
      have hf : ‖↑(f (n + 1)) * ϖ ^ (n + 1)‖ < ‖evalAtUpto ϖ f (n + 1)‖ := by
        rw [ih]
        refine (norm_mul_le _ _).trans_lt ?_
        rw [mul_comm]
        exact mul_lt_of_lt_of_le_one_of_nonneg (by simpa using hn)
          (Valued.integer.norm_le_one _) (norm_nonneg _)
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm, max_eq_left hf.le, ih]
      · congr
        rw [Nat.find_eq_iff]
        push_neg at hk ⊢
        rcases hk.left.left.eq_or_lt with rfl|hk'
        · obtain ⟨i, hi, hi'⟩ := H
          exact absurd (hk.right i hi hi.le) hi'
        · exact ⟨⟨hk', hk.left.right⟩, fun m hm hm' ↦ hk.right m hm hm'.le⟩
      · exact hf.ne'
    · push_neg at H
      rw [(evalAtUpto_eq_zero_iff hϖ hϖ0).mpr H]
      rcases hk.left.left.eq_or_lt with rfl|hk'
      · simp [Digits.norm_coe_eq_one_iff.mpr hk.left.right]
      · exact absurd (H _ hk') hk.left.right

variable [CompleteSpace 𝒪[K]] {D : Digits 𝒪[K]}

lemma summable_evalAt {ϖ : O} (hϖ : ¬ IsUnit ϖ) (f : ℕ → O) :
    Summable (fun n ↦ f n * ϖ ^ n) := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [Nat.cofinite_eq_atTop]
  have := tendsto_norm.comp (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (x := ϖ) ?_)
  · simp only [norm_zero] at this
    refine squeeze_zero_norm ?_ this
    intro n
    dsimp
    refine (norm_mul_le _ _).trans ?_
    exact mul_le_of_le_one_left (norm_nonneg _) (Valued.integer.norm_le_one _)
  · rw [Valued.integer.isUnit_iff_norm_eq_one] at hϖ
    exact lt_of_le_of_ne (Valued.integer.norm_le_one _) hϖ

lemma tendsto_evalAtUpto_nhds_evalAt {ϖ : O} (hϖ : ¬ IsUnit ϖ) (f : AdicExpansion D) :
    Tendsto (evalAtUpto ϖ f ·) atTop (𝓝 (evalAt ϖ f)) := by
  simpa [evalAt, evalAtUpto] using (summable_evalAt hϖ ((↑) ∘ f)).tendsto_sum_tsum_nat

lemma norm_evalAt {ϖ : O} (hϖ : ¬ IsUnit ϖ) (f : AdicExpansion D) :
    ‖evalAt ϖ f‖ = ⨆ n, ‖f n * ϖ ^ n‖ := by
  classical
  rcases eq_or_ne f 0 with rfl|H
  · simp
  simp only [ne_eq, AdicExpansion.ext_iff, zero_apply, not_forall] at H
  trans ‖ϖ‖ ^ (Nat.find H)
  · apply tendsto_nhds_unique (tendsto_norm.comp (tendsto_evalAtUpto_nhds_evalAt hϖ f))
    rw [NormedAddCommGroup.tendsto_atTop]
    intro ε hε
    refine ⟨Nat.find H + 1, fun n hn ↦ hε.trans_le' ?_⟩
    simp only [Function.comp_apply, Real.norm_eq_abs, abs_nonpos_iff, sub_eq_zero]
    rcases n with (_|n)
    · simp at hn
    rw [Nat.succ_le_iff] at hn
    have : ∃ i < n + 1, f i ≠ 0 := ⟨Nat.find H, hn, Nat.find_spec H⟩
    rw [norm_evalAtUpto hϖ f n this]
    congr 1
    rw [Nat.find_eq_iff]
    refine ⟨⟨hn, Nat.find_spec H⟩, fun m hm ↦ ?_⟩
    push_neg
    intro
    simpa using Nat.find_min H hm
  rw [eq_comm]
  apply ciSup_eq_of_forall_le_of_forall_lt_exists_gt
  · intro i
    by_cases h : f i = 0
    · simp [h]
    · simp only [AddSubgroupClass.coe_norm, Subring.coe_mul, SubmonoidClass.coe_pow, norm_mul,
      Digits.norm_coe_eq_one_iff.mpr h, norm_pow, one_mul, ne_eq]
      refine pow_le_pow_of_le_one (norm_nonneg _) (Valued.integer.norm_le_one _) ?_
      rw [Nat.find_le_iff]
      exact ⟨_, le_rfl, h⟩
  · intro ε hε
    refine ⟨Nat.find H, hε.trans_le ?_⟩
    simp [Digits.norm_coe_eq_one_iff.mpr (Nat.find_spec H)]

lemma evalAt_eq_zero_iff {ϖ : O} (hϖ : ¬ IsUnit ϖ) {f : AdicExpansion D} :
    evalAt ϖ f = 0 ↔ (ϖ = 0 ∧ f 0 = 0) ∨ f = 0 := by
  constructor
  · intro h
    apply_fun (‖·‖) at h
    rw [norm_evalAt hϖ, norm_zero] at h
    rcases eq_or_ne f 0 with rfl|hf
    · simp
    rw [Function.ne_iff] at hf
    obtain ⟨i, hi⟩ := hf
    simp only [AdicExpansion.ext_iff, Pi.zero_apply, Digits.ext_iff, Digits.coe_zero, ne_eq,
      zero_apply] at hi
    have hb : BddAbove (Set.range fun n ↦ ‖f n * ϖ ^ n‖) := by
      refine ⟨1, ?_⟩
      rw [mem_upperBounds]
      simp [- norm_mul, - AddSubgroupClass.coe_norm, Valued.integer.norm_le_one]
    have := h.le
    rw [ciSup_le_iff hb] at this
    specialize this i
    replace this := le_antisymm this (norm_nonneg _)
    simp only [AddSubgroupClass.coe_norm, Subring.coe_mul, SubmonoidClass.coe_pow, norm_mul,
      norm_pow, mul_eq_zero, norm_eq_zero, ZeroMemClass.coe_eq_zero, hi, pow_eq_zero_iff', ne_eq,
      false_or] at this
    refine Or.inl ⟨this.left, ?_⟩
    simpa [Digits.ext_iff] using le_antisymm ((le_ciSup hb 0).trans h.le) (norm_nonneg _)
  · rintro (h|h) <;>
    simp [evalAt, h, tsum_eq_zero_add (summable_evalAt (not_isUnit_zero) (fun n ↦ (f n : O)))]

lemma quotient_mk_evalAt_eq_quotient_mk_evalAtUpto {ϖ : O}
    (n : ℕ) (f : AdicExpansion D) :
    Ideal.Quotient.mk (Ideal.span {ϖ ^ n}) (evalAt ϖ f) =
    Ideal.Quotient.mk (Ideal.span {ϖ ^ n}) (evalAtUpto ϖ f n) := by
  by_cases hu : IsUnit ϖ
  · rw [Ideal.span_singleton_eq_top.mpr (hu.pow n)]
    exact Subsingleton.elim _ _
  rw [evalAt, ← sum_add_tsum_nat_add n (summable_evalAt hu _), ← evalAtUpto]
  simp_rw [pow_add ϖ _ n, ← mul_assoc, (summable_evalAt hu _).tsum_mul_right (a := ϖ ^ n),
    RingHom.map_add, RingHom.map_mul]
  simp

lemma injective_evalAt {ϖ : O} (hϖ : Irreducible ϖ) :
    Function.Injective (evalAt (D := D) ϖ) := by
  intro f g h
  contrapose! h
  intro H
  rw [Function.ne_iff] at h
  classical
  let k := Nat.find h
  have hkm : ∀ m < k, f m = g m := fun m hm ↦ by simpa using Nat.find_min h hm
  have hk := Nat.find_spec h
  apply_fun Ideal.Quotient.mk (Ideal.span {ϖ ^ (k + 1)}) at H
  rw [quotient_mk_evalAt_eq_quotient_mk_evalAtUpto,
    quotient_mk_evalAt_eq_quotient_mk_evalAtUpto, evalAtUpto_add_one, evalAtUpto_add_one,
    congr_of_eqOn _ hkm, RingHom.map_add, RingHom.map_add, add_right_inj, ← sub_eq_zero,
    ← RingHom.map_sub, ← sub_mul, Ideal.Quotient.eq_zero_iff_dvd] at H
  suffices ϖ ∣ f k - g k by
    rw [Digits.not_isUnit_dvd_sub_iff hϖ.not_unit] at this
    exact absurd this hk
  rw [pow_dvd_iff_le_emultiplicity, emultiplicity_mul hϖ.prime,
    emultiplicity_pow_self hϖ.ne_zero hϖ.not_unit, Nat.cast_add, Nat.cast_one, add_comm,
    (ENat.addLECancellable_of_ne_top (ENat.coe_ne_top _)).add_le_add_iff_right] at H
  exact dvd_of_emultiplicity_pos (H.trans_lt' zero_lt_one)

end CompleteSpace

end AdicExpansion
