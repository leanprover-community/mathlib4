import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.Cyclotomic.Rat
import Mathlib

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

open IntermediateField Polynomial

theorem IsPrimitiveRoot.norm_toInteger_sub_one_eq_one {n : ℕ} {K : Type*} [Field K] {ζ : K}
    [CharZero K] [IsCyclotomicExtension {n} ℚ K] (hζ : IsPrimitiveRoot ζ n) (h₁ : 2 < n)
    (h₂ : ∀ {p : ℕ}, Nat.Prime p → ∀ (k : ℕ), p ^ k ≠ n) :
    have : NeZero n := NeZero.of_gt h₁
    Algebra.norm ℤ (hζ.toInteger - 1) = 1 := by
  have : NumberField K := IsCyclotomicExtension.numberField {n} ℚ K
  have : NeZero n := NeZero.of_gt h₁
  dsimp only
  rw [Algebra.norm_eq_iff ℤ (Sₘ := K) (Rₘ := ℚ) rfl.le, map_sub, map_one, map_one,
    RingOfIntegers.map_mk, sub_one_norm_eq_eval_cyclotomic hζ h₁
    (cyclotomic.irreducible_rat (NeZero.pos _)), eval_one_cyclotomic_not_prime_pow h₂, Int.cast_one]

theorem IsPrimitiveRoot.norm_toInteger_sub_one_of_eq_two_pow {k : ℕ}  {K : Type*} [Field K]
    {ζ : K} [CharZero K] [IsCyclotomicExtension {2 ^ (k + 2)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (2 ^ (k + 2))) :
    (Algebra.norm ℤ) (hζ.toInteger - 1) = 2 := by
  have : NumberField K := IsCyclotomicExtension.numberField {2 ^ (k + 2)} ℚ K
  rw [Algebra.norm_eq_iff ℤ (Sₘ := K) (Rₘ := ℚ) rfl.le, map_sub, map_one, eq_intCast,
    Int.cast_ofNat, RingOfIntegers.map_mk, hζ.norm_sub_one_two (Nat.le_add_left 2 k)
    (Polynomial.cyclotomic.irreducible_rat (Nat.two_pow_pos _))]

theorem IsPrimitiveRoot.norm_toInteger_sub_one_of_eq_two {K : Type*} [Field K]
    {ζ : K} [CharZero K] [IsCyclotomicExtension {2} ℚ K] (hζ : IsPrimitiveRoot ζ 2) :
    (Algebra.norm ℤ) (hζ.toInteger - 1) = (-2) ^ Module.finrank ℚ K := by
  have : NumberField K := IsCyclotomicExtension.numberField {2} ℚ K
  rw [Algebra.norm_eq_iff ℤ (Sₘ := K) (Rₘ := ℚ) rfl.le, map_sub, map_one, map_pow, eq_intCast,
    Int.cast_neg,  Int.cast_ofNat, RingOfIntegers.map_mk, hζ.eq_neg_one_of_two_right,
    show - 1 - 1 = algebraMap ℚ K (-2) by norm_num, Algebra.norm_algebraMap]

open Algebra

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






#exit

def Algebra.adjoinSimple.gen (R : Type*) {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (a : A) : Algebra.adjoin R {a} := ⟨a, self_mem_adjoin_singleton R a⟩


theorem Algebra.norm_eq_norm_adjoin' (A : Type*) [CommRing A] [IsDomain A] {B : Type*} [CommRing B]
    [IsDomain B] [Algebra A B] [Module.Finite A B] [Module.Free A B] {x : B} :
    (norm A) x =
      (norm A) (Algebra.adjoinSimple.gen A x) ^ Module.finrank A (Algebra.adjoin A {x}) := by
  have : Function.Injective ((algebraMap A (FractionRing A))) := sorry
  rw [← this.eq_iff]
  let _ : Algebra (FractionRing A) (FractionRing B) := sorry
  have : IsScalarTower A (FractionRing A) (FractionRing B) := sorry
  have : IsLocalization (algebraMapSubmonoid B (nonZeroDivisors A)) (FractionRing B) := sorry
  have : Algebra.IsSeparable (FractionRing A) (FractionRing B) := sorry
  have : FiniteDimensional (FractionRing A) (FractionRing B) := sorry

  have r₁ := Algebra.norm_localization A (S := B) (Rₘ := FractionRing A) (Sₘ := FractionRing B)
    (M := nonZeroDivisors A) (a := x)

  rw [← r₁]
  rw [Algebra.norm_eq_norm_adjoin]

  have : IsLocalization (algebraMapSubmonoid ((adjoin A {x})) (nonZeroDivisors A))
    (FractionRing ↥(adjoin A {x})) := sorry
  let _ : Algebra (FractionRing A) (FractionRing ↥(adjoin A {x})) := sorry
  have : IsScalarTower A (FractionRing A) (FractionRing ↥(adjoin A {x})) := sorry
  have : Module.Free A ↥(adjoin A {x}) := sorry
  have : Module.Finite A ↥(adjoin A {x}) := sorry

  have r₂ := Algebra.norm_localization A (S := Algebra.adjoin A {x})
    (Rₘ := FractionRing A) (Sₘ := (FractionRing (Algebra.adjoin A {x})))
    (M := nonZeroDivisors A) (adjoinSimple.gen A x)

  rw [map_pow, ← r₂]


#exit

  rw [this]
  rw [Algebra.norm_eq_norm_adjoin]
  have : IsLocalization (algebraMapSubmonoid ((adjoin A {x})) (nonZeroDivisors A))
    (FractionRing ↥(adjoin A {x})) := sorry
  let _ : Algebra (FractionRing A) (FractionRing ↥(adjoin A {x})) := sorry
  have : IsScalarTower A (FractionRing A) (FractionRing ↥(adjoin A {x})) := sorry
  have : Module.Free A (adjoin A {x}) := sorry
  have :  Module.Finite A (adjoin A {x}) := sorry
  have : IsDomain (adjoin A {x}) := sorry
  have := Algebra.norm_eq_iff A (S := Algebra.adjoin A {x}) (Rₘ := FractionRing A)
    (Sₘ := FractionRing (Algebra.adjoin A {x}))
    (M := nonZeroDivisors A) (a := le_rfl

  sorry



#exit

-- See the results in `Mathlib.NumberTheory.Cyclotomic.Rat`
theorem reduc {n : ℕ} [NeZero n] (hζ : IsPrimitiveRoot ζ n):
    ∃ μ : ℚ⟮(ζ : K)⟯, ∃ (_ : IsCyclotomicExtension {n} ℚ ℚ⟮(ζ : K)⟯),
      IsPrimitiveRoot μ n ∧ ζ - 1 = algebraMap ℚ⟮ζ⟯ K (μ - 1) :=
--      hζ.toInteger - 1 = RingOfIntegers.mapRingHom (algebraMap ℚ⟮ζ⟯ K) (hμ.toInteger - 1) :=
  ⟨IntermediateField.AdjoinSimple.gen ℚ (ζ : K),
    intermediateField_adjoin_isCyclotomicExtension hζ, coe_submonoidClass_iff.mp hζ, rfl⟩

theorem IsPrimitiveRoot.norm_toInteger_sub_one_eq_one {n : ℕ} [NeZero n] (hζ : IsPrimitiveRoot ζ n)
    (h₁ : 2 < n) (h₂ : ∀ {p : ℕ}, Nat.Prime p → ∀ (k : ℕ), p ^ k ≠ n) :
    Algebra.norm ℤ (hζ.toInteger - 1) = 1 := by
  obtain ⟨μ, _, hμ, h⟩ := reduc hζ
  rw [Algebra.norm_eq_iff ℤ (Sₘ := K) (Rₘ := ℚ) rfl.le, map_sub, map_one, map_one,
    RingOfIntegers.map_mk, h, ← Algebra.norm_norm (S := ℚ⟮(ζ : K)⟯), Algebra.norm_algebraMap,
    map_pow, sub_one_norm_eq_eval_cyclotomic hμ h₁ (cyclotomic.irreducible_rat (NeZero.pos _)),
    eval_one_cyclotomic_not_prime_pow h₂, Int.cast_one, one_pow]

theorem IsPrimitiveRoot.norm_toInteger_sub_one_of_prime_ne_two'' {p : ℕ} [Fact (Nat.Prime p)]
    {k : ℕ} (hp : p ≠ 2) (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    Algebra.norm ℤ (hζ.toInteger - 1) =  p ^ Module.finrank (ℚ⟮(ζ : K)⟯) K := by
  obtain ⟨μ, hF, hμ, h⟩ := reduc hζ
  rw [Algebra.norm_eq_iff ℤ (Sₘ := K) (Rₘ := ℚ) rfl.le, map_sub, map_one, map_pow, map_natCast]
  rw [RingOfIntegers.map_mk, h, ← Algebra.norm_norm (S := ℚ⟮(ζ : K)⟯), Algebra.norm_algebraMap,
  map_pow]
  rw [hμ.norm_sub_one_of_prime_ne_two (Polynomial.cyclotomic.irreducible_rat (NeZero.pos _)) hp]

theorem IsPrimitiveRoot.norm_toInteger_sub_one_of_prime_two_ge_two {k : ℕ} (hk : 2 ≤ k)
    (hζ : IsPrimitiveRoot ζ (2 ^ k)) :
    Algebra.norm ℤ (hζ.toInteger - 1) =  2 ^ Module.finrank (ℚ⟮(ζ : K)⟯) K := by
  obtain ⟨μ, hF, hμ, h⟩ := reduc hζ
  rw [Algebra.norm_eq_iff ℤ (Sₘ := K) (Rₘ := ℚ) rfl.le, map_sub, map_one, map_pow, eq_intCast,
    Int.cast_ofNat]
  rw [RingOfIntegers.map_mk, h, ← Algebra.norm_norm (S := ℚ⟮(ζ : K)⟯), Algebra.norm_algebraMap,
  map_pow]
  rw [hμ.norm_sub_one_two hk (Polynomial.cyclotomic.irreducible_rat (Nat.two_pow_pos k))]

theorem IsPrimitiveRoot.prime_dvd_of_dvd_norm_sub_one {n : ℕ} [NeZero n] (hn : 2 ≤ n) {p : ℕ}
    [hF : Fact (Nat.Prime p)] (hζ : IsPrimitiveRoot ζ n)
    (hp : ↑p ∣ Algebra.norm ℤ (hζ.toInteger - 1)) :
    p ∣ n := by
  have : NeZero n := NeZero.of_gt hn
  rsuffices ⟨q, hq, t, s, ht₁, ht₂, hs⟩ :
      ∃ q, ∃ (_ : q.Prime), ∃ t s, t ≠ 0 ∧ n = q ^ t ∧ (p : ℤ) ∣ (q : ℤ) ^ s := by
    obtain hn | hn := lt_or_eq_of_le hn
    · by_cases h : ∀ {q : ℕ}, Nat.Prime q → ∀ (k : ℕ), q ^ k ≠ n
      · rw [hζ.norm_toInteger_sub_one_eq_one hn h, Int.natCast_dvd_ofNat, Nat.dvd_one] at hp
        exact (Nat.Prime.ne_one hF.out hp).elim
      ·
        sorry
    ·
      sorry

  rw [← Int.natCast_pow, Int.natCast_dvd_natCast] at hs
  have := hF.out.dvd_of_dvd_pow hs
  rw [Nat.prime_dvd_prime_iff_eq hF.out hq] at this
  rw [this, ht₂]
  exact dvd_pow_self _ ht₁

#exit

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
