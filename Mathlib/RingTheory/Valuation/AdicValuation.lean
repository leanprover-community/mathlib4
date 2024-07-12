/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.Valuation.PrimeMultiplicity
import Mathlib.Algebra.Order.Group.WithTop
import Mathlib.RingTheory.Localization.NumDen
import Mathlib.Algebra.Squarefree.Basic

/-!
# p-adic valuation over a fraction ring over a unique factorization domain.
-/

variable {F K : Type*} [CommRing F] [IsDomain F] [UniqueFactorizationMonoid F] [Field K]
  [Algebra F K] [IsFractionRing F K]
  [DecidableRel fun (a b : F) => a ∣ b]
  (p : F) [Fact (Prime p)]

open IsFractionRing algebraMap PartENat

noncomputable def adicValuation : AddValuation K (WithTop ℤ) :=
  (multiplicity.addValuation (Fact.out : Prime p)).map toWithTopInt (by simp) toWithTopInt_monotone
  |>.extendToLocalization (S := nonZeroDivisors F) (by
    intro v hv
    apply Set.mem_compl
    intro nh
    simp only [SetLike.mem_coe, Valuation.mem_supp_iff] at nh
    change toWithTopInt _ = ⊤ at nh
    simp only [toWithTopInt_eq_top_iff] at nh
    conv at nh =>
      lhs
      apply multiplicity.addValuation_apply
    suffices multiplicity.Finite p v by
      rw [multiplicity.finite_iff_dom, nh] at this
      exact this
    apply multiplicity.finite_prime_left
    exact Fact.out
    exact nonZeroDivisors.ne_zero hv
  ) K

lemma adicValuation_coe_eq_multiplicity (a : F) :
    adicValuation p (a : K) = toWithTopInt (multiplicity p a) := by
  unfold adicValuation
  conv =>
    lhs
    apply Valuation.extendToLocalization_apply_map_apply (Γ := (Multiplicative (WithTop ℤ)ᵒᵈ))
  rfl

lemma adicValuation_coe_nonneg (a : F) :
    0 ≤ adicValuation p (a : K) := by
  rw [adicValuation_coe_eq_multiplicity]
  apply toWithTopInt_nonneg

lemma adicValuation_coe_eq_zero_iff (a : F) :
    adicValuation p (a : K) = 0 ↔ ¬p ∣ a := by
  rw [adicValuation_coe_eq_multiplicity, toWithTopInt_eq_zero_iff]
  exact multiplicity.multiplicity_eq_zero

lemma adicValuation_coe_pos_iff (a : F) :
    0 < adicValuation p (a : K) ↔ p ∣ a := by
  rw [← not_iff_not, ← adicValuation_coe_eq_zero_iff (K := K)]
  simp only [not_lt, le_iff_eq_or_lt, or_iff_left_iff_imp]
  have := adicValuation_coe_nonneg p a (K := K)
  intro h
  exact (this.trans_lt h).false.elim

instance (priority := 100) {α : Type*} [LinearOrderedAddCommGroupWithTop α] : SubtractionMonoid α where
  neg_neg := sorry
  neg_add_rev := sorry
  neg_eq_of_add := sorry

lemma injective_add_ne_top {R : Type*} [LinearOrderedAddCommGroupWithTop R]
    (b : R) (h : b ≠ ⊤) :
    Function.Injective (fun x ↦ x + b) := by sorry

lemma StrictMono.add_ne_top {R : Type*} [LinearOrderedAddCommGroupWithTop R]
    (b : R) (h : b ≠ ⊤) :
    StrictMono (fun x ↦ x + b) := by sorry

lemma sub_pos' (R : Type*) [LinearOrderedAddCommGroupWithTop R] (a b : R) :
    0 < a - b ↔ b < a ∨ b = ⊤ := by sorry

open algebraMap in
@[simp]
lemma NoZeroSMulDivisors.coe_eq_zero (R : Type*) (A : Type*) [CommRing R] [Ring A] [Nontrivial A]
    [Algebra R A] [NoZeroSMulDivisors R A] (x : R) : (x : A) = 0 ↔ x = 0 := by
  constructor
  · intro h
    replace h : algebraMap R A x = algebraMap R A 0 := by convert h; simp
    exact NoZeroSMulDivisors.algebraMap_injective R A h
  · intro h
    simp [h]

lemma adicValuation_nonpos_iff (a : K) :
    adicValuation p a ≤ 0 ↔ ¬p ∣ num F a := by
  constructor
  · intro h nh
    rw [← mk'_num_den' F a, AddValuation.map_div] at h
    have : adicValuation p (algebraMap F K (den F a : F)) = 0 := by
      rw [adicValuation_coe_eq_zero_iff]
      have := IsFractionRing.num_den_reduced F a
      have nu : ¬IsUnit p := Prime.not_unit Fact.out
      exact fun a ↦ nu (this nh a)
    rw [this, sub_zero] at h
    rw [← adicValuation_coe_pos_iff (K := K)] at nh
    exact (nh.trans_le h).false
  · contrapose!
    intro h
    rw [← adicValuation_coe_pos_iff (K := K)]
    rw [← mk'_num_den' F a, AddValuation.map_div, sub_pos'] at h
    rcases h with h | h
    · apply lt_of_le_of_lt _ h
      apply adicValuation_coe_nonneg
    · simp [nonZeroDivisors.coe_ne_zero] at h

lemma adicValuation_nonneg_iff (a : K) :
    0 ≤ adicValuation p a ↔ ¬p ∣ den F a := by
  by_cases ha : a = 0
  · simp [ha]
    intro h
    exact Prime.not_unit Fact.out <| isUnit_of_dvd_unit h isUnit_den_zero
  convert adicValuation_nonpos_iff p a⁻¹ using 1
  · simp only [AddValuation.map_inv]
    cases x : adicValuation p a
    · simp [ha] at x
    simp only [WithTop.coe_nonneg, ← WithTop.LinearOrderedAddCommGroup.coe_neg, WithTop.coe_le_zero,
      Left.neg_nonpos_iff]
  · apply Iff.not
    apply Associated.dvd_iff_dvd_right
    exact IsFractionRing.associated_den_num_inv a ha
