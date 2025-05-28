import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.RamificationInertia.Basic

theorem Ideal.absNorm_eq_pow_inertiaDeg' {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Module.Free ℤ R] [Module.Finite ℤ R] {p : ℕ} (P : Ideal R) [P.LiesOver (span {(p : ℤ)})]
    (hp : Nat.Prime p) :
    absNorm P = p ^ (span {(p : ℤ)}).inertiaDeg P := by
  exact absNorm_eq_pow_inertiaDeg P (p := p) (Nat.prime_iff_prime_int.mp hp)

theorem Nat.coprime_iff {a b : ℕ} :
    a.Coprime b ↔ ∃ u v : ℤ, u * a + v * b = 1 := by
  refine ⟨?_, ?_⟩
  · intro h
    refine ⟨a.gcdA b, a.gcdB b, ?_⟩
    rw [mul_comm _ (a : ℤ), mul_comm _ (b : ℤ), ← Nat.gcd_eq_gcd_ab, h, Nat.cast_one]
  · intro ⟨u, v, h⟩
    exact Int.gcd_eq_one_iff.mpr fun _ ha hb ↦ h ▸ Dvd.dvd.linear_comb ha hb u v

@[simp] theorem Nat.one_lt_pow_iff' {a : ℕ} (ha : 1 < a) : ∀ {n}, 1 < a ^ n ↔ 1 ≤ n
 | 0 => by simp
 | n + 1 => by simp [ha]

@[simp] protected theorem Nat.pow_le_one_iff' {a n : ℕ} (ha : 1 < a) : a ^ n ≤ 1 ↔ n = 0 := by
  simp [← Nat.not_lt, one_lt_pow_iff' ha]

theorem Nat.pow_sub_one_dvd_pow_sub_one_iff {a n m : ℕ} (ha : 2 ≤ a) :
    a ^ n - 1 ∣ a ^ m - 1 ↔ n ∣ m := by
  rw [dvd_iff_mod_eq_zero, pow_sub_one_mod_pow_sub_one, Nat.sub_eq_zero_iff_le,
    Nat.pow_le_one_iff' ha, dvd_iff_mod_eq_zero]

theorem ZMod.natCast_eq_natCast_iff_dvd_sub (a b : ℕ) (c : ℕ) :
    (a : ZMod c) = ↑b ↔ (c : ℤ) ∣ b - a := by
  rw [← Int.cast_natCast a, ← Int.cast_natCast b, ← intCast_eq_intCast_iff_dvd_sub]

theorem isPrimitiveRoot_of_mem_rootsOfUnity {M : Type*} [CommMonoid M] {ζ : Mˣ} {n : ℕ} [NeZero n]
    (hζ : ζ ∈ rootsOfUnity n M) :
    ∃ d : ℕ, d ≠ 0 ∧ d ∣ n ∧ IsPrimitiveRoot ζ d := by
  refine ⟨orderOf ζ, (IsOfFinOrder.orderOf_pos ⟨n, NeZero.pos n,
    (isPeriodicPt_mul_iff_pow_eq_one ζ).mpr hζ⟩).ne', orderOf_dvd_of_pow_eq_one hζ,
    IsPrimitiveRoot.orderOf ζ⟩

open NumberField IsPrimitiveRoot

theorem IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension {F K : Type*} [Field F]
    [Field K] [Algebra F K] [Algebra.IsIntegral F K] {n : ℕ} [NeZero n] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) :
    IsCyclotomicExtension {n} F (IntermediateField.adjoin F {ζ}) := by
  change IsCyclotomicExtension {n} F (IntermediateField.adjoin F {ζ}).toSubalgebra
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_integral (Algebra.IsIntegral.isIntegral ζ)]
  exact hζ.adjoin_isCyclotomicExtension F

variable {K : Type*} [Field K] [NumberField K] {ζ : (𝓞 K)}

open IntermediateField

-- See the results in `Mathlib.NumberTheory.Cyclotomic.Rat`
theorem reduc {n : ℕ} [NeZero n] (hζ : IsPrimitiveRoot ζ n):
    ∃ μ : ℚ⟮(ζ : K)⟯, ∃ (_ : IsCyclotomicExtension {n} ℚ ℚ⟮(ζ : K)⟯),
      IsPrimitiveRoot μ n ∧ (ζ : K) - 1 = algebraMap ℚ⟮(ζ : K)⟯ K (μ - 1) := by
  refine ⟨IntermediateField.AdjoinSimple.gen ℚ (ζ : K), ?_, ?_, rfl⟩
  · exact (hζ.map_of_injective
      (RingOfIntegers.coe_injective)).intermediateField_adjoin_isCyclotomicExtension
  · exact coe_submonoidClass_iff.mp <| hζ.map_of_injective (RingOfIntegers.coe_injective)

theorem IsPrimitiveRoot.norm_int_sub_one_eq_one {n : ℕ} [NeZero n] (hζ : IsPrimitiveRoot ζ n)
    (h₁ : 2 < n) (h₂ : ∀ {p : ℕ}, Nat.Prime p → ∀ (k : ℕ), p ^ k ≠ n) :
    Algebra.norm ℤ (ζ - 1) = 1 := by
  simp only [← Rat.intCast_inj, Algebra.coe_norm_int, map_sub, map_one, Int.cast_one]
  obtain ⟨μ, _, hμ, h⟩ := reduc hζ
  rw [h, ← Algebra.norm_norm (S := ℚ⟮(ζ : K)⟯), Algebra.norm_algebraMap, map_pow,
    sub_one_norm_eq_eval_cyclotomic hμ h₁ (Polynomial.cyclotomic.irreducible_rat (NeZero.pos _)),
    Polynomial.eval_one_cyclotomic_not_prime_pow h₂, Int.cast_one, one_pow]

theorem IsPrimitiveRoot.norm_int_sub_one_ne_two {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ} (hp : p ≠ 2)
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    Algebra.norm ℤ (ζ - 1) =  p ^ Module.finrank (ℚ⟮(ζ : K)⟯) K := by
  simp only [← Rat.intCast_inj, Algebra.coe_norm_int, map_sub, map_one, Int.cast_one]
  obtain ⟨μ, hF, hμ, h⟩ := reduc hζ
  rw [h, ← Algebra.norm_norm (S := ℚ⟮(ζ : K)⟯), Algebra.norm_algebraMap, map_pow,
    hμ.norm_sub_one_of_prime_ne_two (Polynomial.cyclotomic.irreducible_rat (NeZero.pos _)) hp,
    Int.cast_pow, Int.cast_natCast]

theorem IsPrimitiveRoot.norm_int_sub_one_two {k : ℕ} (hk : 2 ≤ k)
    (hζ : IsPrimitiveRoot ζ (2 ^ k)) :
    Algebra.norm ℤ (ζ - 1) =  2 ^ Module.finrank (ℚ⟮(ζ : K)⟯) K := by
  simp only [← Rat.intCast_inj, Algebra.coe_norm_int, map_sub, map_one, Int.cast_one]
  obtain ⟨μ, hF, hμ, h⟩ := reduc hζ
  rw [h, ← Algebra.norm_norm (S := ℚ⟮(ζ : K)⟯), Algebra.norm_algebraMap, map_pow,
    hμ.norm_sub_one_two hk (Polynomial.cyclotomic.irreducible_rat (Nat.two_pow_pos k)),
    Int.cast_pow, Int.cast_ofNat]

theorem IsPrimitiveRoot.prime_dvd_of_dvd_norm_sub_one {n : ℕ} (hn : 2 ≤ n) {p : ℕ}
    [hF : Fact (Nat.Prime p)] (hζ : IsPrimitiveRoot ζ n) (hp : ↑p ∣ Algebra.norm ℤ (ζ - 1)) :
    p ∣ n := by
  have : NeZero n := NeZero.of_gt hn
  suffices ∃ q, ∃ (_ : Nat.Prime q), ∃ t s, t ≠ 0 ∧
    (n : ℕ) = q ^ t ∧ (p : ℤ) ∣ (q : ℤ) ^ s by
    obtain ⟨q, hq, t, s, ht₁, ht₂, hs⟩ := this
    rw [← Int.natCast_pow] at hs
    rw [Int.natCast_dvd_natCast] at hs
    have := hF.out.dvd_of_dvd_pow hs
    rw [Nat.prime_dvd_prime_iff_eq hF.out hq] at this
    rw [this, ht₂]
    exact dvd_pow_self _ ht₁
  obtain hn | hn := lt_or_eq_of_le hn
  · by_cases h :  ∀ {q : ℕ}, Nat.Prime q → ∀ (k : ℕ), q ^ k ≠ n
    · rw [hζ.norm_int_sub_one_eq_one hn h, Int.natCast_dvd_ofNat, Nat.dvd_one] at hp
      exact (Nat.Prime.ne_one hF.out hp).elim
    · simp only [ne_eq, not_forall, Classical.not_imp, Decidable.not_not] at h
      obtain ⟨q, hq, t, hn'⟩ := h
      cases t with
      | zero =>
          rw [← hn', pow_zero] at hn
          linarith
      | succ r =>
          refine ⟨q, hq, r + 1, Module.finrank (ℚ⟮(ζ : K)⟯) K, r.add_one_ne_zero, hn'.symm, ?_⟩
          by_cases hq' : q = 2
          · have hr : 2 ≤ r + 1 := by
              contrapose! hn
              rw [Nat.add_lt_iff_lt_sub_right, Nat.succ_sub_one, Nat.lt_one_iff] at hn
              rw [hq', hn, zero_add, pow_one, eq_comm] at hn'
              exact le_of_eq hn'
            rw [← hn', hq'] at hζ
            rw [hζ.norm_int_sub_one_two hr] at hp
            rwa [hq', Nat.cast_ofNat]
          · have : Fact (Nat.Prime q) := { out := hq }
            rw [← hn'] at hζ
            rwa [hζ.norm_int_sub_one_ne_two hq'] at hp
  · rw [← hn] at hζ
    replace hζ : ζ = - 1 := by exact IsPrimitiveRoot.eq_neg_one_of_two_right hζ
    rw [hζ, show (-1 : 𝓞 K) - 1 = algebraMap ℤ (𝓞 K) (- 2 : ℤ) by simp; norm_num] at hp
    rw [Algebra.norm_algebraMap_of_basis (RingOfIntegers.basis K)] at hp
    rw [neg_eq_neg_one_mul, mul_pow] at hp
    simp only [Int.reduceNeg, ne_eq, Fintype.card_ne_zero, not_false_eq_true, isUnit_pow_iff,
      IsUnit.neg_iff, isUnit_one, IsUnit.dvd_mul_left] at hp
    exact ⟨2, Nat.prime_two, 1, _, one_ne_zero, by rw [hn, pow_one], hp⟩
