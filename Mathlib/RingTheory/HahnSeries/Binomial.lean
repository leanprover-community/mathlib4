/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Scott Carnahan
-/
import Mathlib.RingTheory.HahnSeries.Summable
--import Mathlib.RingTheory.Binomial

#align_import ring_theory.hahn_series from "leanprover-community/mathlib"@"a484a7d0eade4e1268f4fb402859b6686037f965"

/-!
# Hahn Series
If `Γ` is ordered and `R` has zero, then `HahnSeries Γ R` consists of formal series over `Γ` with
coefficients in `R`, whose supports are partially well-ordered. With further structure on `R` and
`Γ`, we can add further structure on `HahnSeries Γ R`.  We introduce valuations and binomial
expansions.

## Main Definitions
  * `HahnSeries.addVal Γ R` defines an `AddValuation` on `HahnSeries Γ R` when `Γ` is linearly
    ordered.

## Main results

  *

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/

set_option linter.uppercaseLean3 false

open Finset Function

open scoped Classical
open BigOperators Pointwise

noncomputable section

variable {Γ : Type*} {R : Type*}

namespace HahnSeries

/-! We consider integral powers of binomials with invertible leading term.  Also, we consider more
binomial ring powers of binomials with leading term 1, when the coefficient ring is an algebra over
the binomial ring in question.  Question: how to approach switching to consider locality in vertex
algebras?  -/

section OneSubSingle

variable [LinearOrderedCancelAddCommMonoid Γ] [CommRing R]

theorem isUnit_one_sub_single {g : Γ} (hg : 0 < g) (r : R) : IsUnit (1 - single g r) := by
  refine isUnit_of_mul_eq_one _ _ (SummableFamily.one_sub_self_mul_hsum_powers ?_)
  by_cases hr : r = 0;
  · simp_all only [map_zero, orderTop_zero, WithTop.zero_lt_top]
  · simp_all only [orderTop_single hr, WithTop.coe_pos]

theorem supp_one_sub_single {g : Γ} (r : R) :
    (1 - single g r).support ⊆ {0, g} := by
  refine support_add_subset.trans ?_
  simp_all only [support_neg, Set.union_subset_iff]
  constructor
  · by_cases h : Nontrivial R
    · rw [support_one]
      exact Set.singleton_subset_iff.mpr (Set.mem_insert 0 {g})
    · rw [not_nontrivial_iff_subsingleton, subsingleton_iff] at h
      exact Set.compl_subset_compl.mp fun ⦃a⦄ _ a_2 ↦ a_2 (h (coeff 1 a) 0)
  · exact support_single_subset.trans (Set.subset_insert 0 {g})

theorem coeff_mul_one_sub_single {x : HahnSeries Γ R} {g g' : Γ} {r : R} :
    (x * (1 - single g r)).coeff (g + g') = x.coeff (g + g') - r * x.coeff g' := by
  rw [mul_one_sub, sub_coeff, sub_right_inj, add_comm, mul_single_coeff_add, mul_comm]

theorem support_one_sub_single_npow' {g : Γ} {r : R} {n : ℕ} :
    ((1 - single g r) ^ n).support ⊆ AddSubmonoid.closure {0, g} :=
  (support_pow_subset_closure (1 - (single g) r) n).trans
    (AddSubmonoid.closure_mono (supp_one_sub_single r))

theorem _root_.AddSubmonoid.closure_insert_zero {Γ} [AddZeroClass Γ] {g : Γ} :
  AddSubmonoid.closure ({0, g} : Set Γ) ≤ AddSubmonoid.closure ({g} : Set Γ) :=
    AddSubmonoid.closure_le.mpr <| Set.insert_subset_iff.mpr
    { left := AddSubmonoid.zero_mem _, right := AddSubmonoid.subset_closure }
--#find_home AddSubmonoid.closure_insert_zero --[Mathlib.LinearAlgebra.Span]

theorem support_one_sub_single_npow (g : Γ) (r : R) {n : ℕ} :
    ((1 - single g r) ^ n).support ⊆ AddSubmonoid.closure {g} :=
  support_one_sub_single_npow'.trans AddSubmonoid.closure_insert_zero

theorem _root_.AddSubmonoid.neg_not_in_closure {Γ} [OrderedAddCommMonoid Γ] {g g' : Γ} (hg : 0 ≤ g)
    (hg' : g' < 0) : ¬ g' ∈ AddSubmonoid.closure {g} := by
  rw [AddSubmonoid.mem_closure_singleton, not_exists]
  intro k hk
  have hgk : 0 ≤ k • g :=
    nsmul_nonneg hg k
  rw [hk] at hgk
  exact (lt_self_iff_false 0).mp (lt_of_le_of_lt hgk hg')
--#find_home AddSubmonoid.neg_not_in_closure --[Mathlib.GroupTheory.Submonoid.Membership]

theorem coeff_one_sub_single_pow_of_neg {g g' : Γ} (hg : 0 ≤ g) (hg' : g' < 0) {r : R} {n : ℕ} :
    ((1 - single g r) ^ n).coeff g' = 0 := by
  by_contra h
  rw [← ne_eq, ← mem_support] at h
  apply (AddSubmonoid.neg_not_in_closure hg hg')
    (Set.mem_of_subset_of_mem (support_one_sub_single_npow g r) h)

theorem coeff_one_sub_single_pow_of_add_eq_zero {g g' : Γ} (hg : 0 < g) (hgg' : g + g' = 0) {r : R}
    {n : ℕ} : ((1 - single g r) ^ n).coeff g' = 0 := by
  have hg' : g' < 0 := by
    rw [← hgg']
    exact (lt_add_iff_pos_left g').mpr hg
  exact coeff_one_sub_single_pow_of_neg (le_of_lt hg) hg'

theorem coeff_single_mul_of_no_add {x : HahnSeries Γ R} {a b : Γ} {r : R} (hab : ¬∃c, c + a = b) :
    (x * single a r).coeff b = 0 := by
  rw [mul_coeff]
  trans ∑ ij : Γ × Γ in ∅, x.coeff ij.fst * (single a r).coeff ij.snd
  · apply sum_congr _ fun _ _ => rfl
    ext ⟨a1, a2⟩
    simp_all [mem_addAntidiagonal, single_coeff]
  · exact rfl
--#find_home! coeff_single_mul_of_no_add --[Mathlib.RingTheory.HahnSeries.Multiplication]

theorem coeff_zero_one_sub_single_npow {g : Γ} (hg : 0 < g) {r : R} {n : ℕ} :
    ((1 - single g r) ^ n).coeff 0 = 1 := by
  by_cases hr : r = 0; · rw [hr, single_eq_zero, sub_zero, one_pow, one_coeff, if_pos rfl]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    by_cases hg' : ∃ g' : Γ, g + g' = 0
    · rw [← hg'.choose_spec, coeff_mul_one_sub_single, hg'.choose_spec, ih, sub_eq_self,
        coeff_one_sub_single_pow_of_add_eq_zero hg hg'.choose_spec, mul_zero]
    · rw [mul_one_sub, sub_coeff, ih, sub_eq_self, coeff_single_mul_of_no_add]
      simp_all [add_comm]

theorem coeff_one_sub_single_npow {g : Γ} (hg : 0 < g) (r : R) {k n : ℕ}:
    ((1 - single g r) ^ n).coeff (k • g) = (-1) ^ k • (Nat.choose n k) • (r ^ k) := by
  induction' n with n ihn generalizing k
  · simp only [Nat.zero_eq, zero_smul, Int.reduceNeg, pow_zero, Nat.choose_zero_right, one_smul]
    induction' k with k
    · simp
    · simp only [Nat.zero_eq, pow_zero, one_coeff, Int.reduceNeg, Nat.choose_zero_succ, zero_smul,
      smul_zero, ite_eq_right_iff]
      have hkg : ¬ Nat.succ k • g = 0 :=
        ne_comm.mp <| ne_of_lt <| (nsmul_pos_iff (Nat.succ_ne_zero k)).mpr hg
      simp_all only [Nat.zero_eq, pow_zero, one_coeff, nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow,
        Int.cast_neg, Int.cast_one, IsEmpty.forall_iff]
  · induction' k with k
    · simp only [Nat.zero_eq, zero_smul, Int.reduceNeg, pow_zero, Nat.choose_zero_right, one_smul]
      exact coeff_zero_one_sub_single_npow hg
    · have hkg : Nat.succ k • g = g + k • g := by
        rw [← Nat.add_one, add_smul, one_smul, add_comm _ g]
      rw [pow_succ, hkg, coeff_mul_one_sub_single, ← hkg, ihn, ihn, Nat.choose_succ_succ,
        sub_eq_add_neg, neg_mul_eq_mul_neg, pow_succ', pow_succ']
      simp
      ring_nf

/-!
theorem coeff_one_sub_single_neg_pow {g : Γ} (hg : 0 < g) {r : R} {n : ℤ} : ∀(k : ℕ),
    ((IsUnit.unit (isUnit_one_sub_single hg r)) ^ n).val.coeff (k • g) =
      (-r) ^ k • Ring.choose n k := by
  refine Int.induction_on n ?_ ?_ ?_
  · exact fun k => by
      by_cases hk : k = 0
      · rw [hk, Ring.choose_zero_right, zero_smul, zpow_zero, pow_zero]
        norm_cast
        simp
      · rw [Ring.choose_zero_pos ℤ k (Nat.pos_iff_ne_zero.mpr hk), zpow_zero]
        norm_cast
        rw [smul_zero]
        have hkg : 0 < k • g := (nsmul_pos_iff hk).mpr hg
        have hkg' : ¬ k • g = 0 := fun h => by simp_all
        rw [one_coeff, if_neg hkg']
  · intro n h k
    rw [zpow_add_one, Units.val_mul, IsUnit.unit_spec]
    by_cases hk : k = 0
    · rw [coeff_mul_one_sub_single, h, hk, coeff_one_sub_single_pow_of_neg hg
        (show 0 • g - g < 0 by simp [hg])]
      simp
    · sorry
  · sorry
-/

end OneSubSingle

section SingleAddSingle

variable [LinearOrderedAddCommGroup Γ] [CommRing R]

theorem single_add_single_coeff {g g' : Γ} (hgg' : g < g') {a b : R} :
    (single g a + single g' b).coeff g = a := by
  simp_all [ne_of_lt hgg']

theorem single_add_single_coeff_ne {g g' : Γ} (hgg' : g < g') {a b : R} (ha : a ≠ 0) :
    single g a + single g' b ≠ 0 :=
  ne_zero_of_coeff_ne_zero (ne_of_eq_of_ne (single_add_single_coeff hgg') ha)

theorem single_add_single_support {g g' : Γ} {a b : R} :
    (single g a + single g' b).support ⊆ {g} ∪ {g'} := by
  refine support_add_subset.trans ?_
  simp_all only [Set.union_singleton, Set.union_subset_iff]
  refine { left := fun _ hk => Set.mem_insert_of_mem g' (support_single_subset hk), right := ?_ }
  rw [Set.pair_comm]
  exact fun k hk => Equiv.Set.union.proof_1 k <| Set.mem_insert_of_mem g (support_single_subset hk)

theorem orderTop_binomial {g g' : Γ} (hgg' : g < g') {a b : R} (ha : a ≠ 0) :
    (single g a + single g' b).orderTop = g := by
  rw [← orderTop_single ha]
  exact orderTop_add_eq (lt_of_eq_of_lt (orderTop_single ha)
    (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hgg') orderTop_single_le))

theorem leadingCoeff_binomial {g g' : Γ} (hgg' : g < g') {a b : R} (ha : a ≠ 0) :
    (single g a + single g' b).leadingCoeff = a := by
  rw [leadingCoeff, orderTop_binomial hgg' ha, coeffTop_eq, single_add_single_coeff hgg']

theorem isUnit_binomial {g g' : Γ} (hgg' : g < g') (a : Units R) (b : R) :
    IsUnit (single g a.val + single g' b) := by
  refine isUnit_of_isUnit_leadingCoeff (R := R) ?_
  by_cases ha : a.val = 0
  · have hz : (0 : R) = 1 :=
      isUnit_zero_iff.mp (Eq.mpr (congrArg (fun h ↦ IsUnit h) ha.symm) (Units.isUnit a))
    rw [← one_mul (leadingCoeff _), ← hz, zero_mul, hz, isUnit_iff_dvd_one]
  · rw [leadingCoeff_binomial hgg' ha]
    exact Units.isUnit a

end SingleAddSingle
