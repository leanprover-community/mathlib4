import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Cyclotomic.Rat

theorem isPrimitiveRoot_of_mem_rootsOfUnity {M : Type*} [CommMonoid M] {ζ : Mˣ} {n : ℕ} [NeZero n]
    (hζ : ζ ∈ rootsOfUnity n M) :
    ∃ d : ℕ, d ≠ 0 ∧ d ∣ n ∧ IsPrimitiveRoot ζ d :=
  ⟨orderOf ζ, (IsOfFinOrder.orderOf_pos ⟨n, NeZero.pos n,
    (isPeriodicPt_mul_iff_pow_eq_one ζ).mpr hζ⟩).ne', orderOf_dvd_of_pow_eq_one hζ,
    IsPrimitiveRoot.orderOf ζ⟩

open Algebra

open scoped IntermediateField

theorem IsPrimitiveRoot.prime_dvd_of_dvd_norm_sub_one {n : ℕ} [NeZero n] (hn : 2 ≤ n) {K : Type*}
    [Field K] [NumberField K] {ζ : K} {p : ℕ} [hF : Fact (Nat.Prime p)] (hζ : IsPrimitiveRoot ζ n)
    (hp : (p : ℤ) ∣ norm ℤ (hζ.toInteger - 1)) :
    p ∣ n := by
  obtain ⟨μ, hC, hμ, h⟩ :
      ∃ μ : ℚ⟮ζ⟯, ∃ (_ : IsCyclotomicExtension {n} ℚ ℚ⟮ζ⟯), ∃ (hμ : IsPrimitiveRoot μ n),
      norm ℤ (hζ.toInteger - 1) = norm ℤ (hμ.toInteger - 1) ^ Module.finrank ℚ⟮ζ⟯ K := by
    refine ⟨IntermediateField.AdjoinSimple.gen ℚ ζ,
      intermediateField_adjoin_isCyclotomicExtension hζ, coe_submonoidClass_iff.mp hζ, ?_⟩
    have : NumberField ℚ⟮ζ⟯ := of_intermediateField _
    rw [norm_eq_iff ℤ (Sₘ := K) (Rₘ := ℚ) rfl.le, map_sub, map_one, RingOfIntegers.map_mk,
      show  ζ - 1 = algebraMap ℚ⟮ζ⟯ K (IntermediateField.AdjoinSimple.gen ℚ ζ - 1) by rfl,
      ← norm_norm (S := ℚ⟮ζ⟯), Algebra.norm_algebraMap, map_pow, map_pow, ← norm_localization ℤ
      (nonZeroDivisors ℤ) (Sₘ :=  ℚ⟮ζ⟯), map_sub (algebraMap _ _), RingOfIntegers.map_mk, map_one]
  rw [h] at hp
  rsuffices ⟨q, hq, t, s, ht₁, ht₂, hs⟩ :
      ∃ q, ∃ (_ : q.Prime), ∃ t s, t ≠ 0 ∧ n = q ^ t ∧ (p : ℤ) ∣ (q : ℤ) ^ s := by
    obtain hn | hn := lt_or_eq_of_le hn
    · by_cases h : ∃ q, ∃ (_ : q.Prime), ∃ t, q ^ t = n
      · obtain ⟨q, hq, t, hn'⟩ := h
        have : Fact (Nat.Prime q) := ⟨hq⟩
        cases t with
        | zero => simp [← hn'] at hn
        | succ r =>
          rw [← hn'] at hC hμ
          refine ⟨q, hq, r + 1, Module.finrank (ℚ⟮ζ⟯) K, r.add_one_ne_zero, hn'.symm, ?_⟩
          by_cases hq' : q = 2
          · cases r with
            | zero =>
                rw [← hn', hq', zero_add, pow_one] at hn
                exact ((lt_irrefl _) hn).elim
            | succ k =>
                rw [hq'] at hC hμ ⊢
                rwa [hμ.norm_toInteger_sub_one_of_eq_two_pow] at hp
          · rwa [hμ.norm_toInteger_sub_one_of_prime_ne_two hq'] at hp
      · rw [IsPrimitiveRoot.norm_toInteger_sub_one_eq_one hμ hn, one_pow,
          Int.natCast_dvd_ofNat, Nat.dvd_one] at hp
        · exact (Nat.Prime.ne_one hF.out hp).elim
        · simp [ne_eq, not_forall, _root_.not_imp, not_not] at h
          exact fun {p} a k ↦ h p a k
    · rw [← hn] at hμ hC ⊢
      refine ⟨2, Nat.prime_two, 1, Module.finrank ℚ K, one_ne_zero, by rw [pow_one], ?_⟩
      rwa [hμ.norm_toInteger_sub_one_of_eq_two, ← pow_mul, Module.finrank_mul_finrank,
        neg_eq_neg_one_mul, mul_pow, IsUnit.dvd_mul_left
        ((isUnit_pow_iff Module.finrank_pos.ne').mpr isUnit_neg_one)] at hp
  · have : p = q := by
      rw [← Int.natCast_pow, Int.natCast_dvd_natCast] at hs
      exact (Nat.prime_dvd_prime_iff_eq hF.out hq).mp (hF.out.dvd_of_dvd_pow hs)
    rw [ht₂, this]
    exact dvd_pow_self _ ht₁
