import Mathlib

theorem Ideal.eq_of_dvd_of_isPrime {A : Type*} [CommRing A] [IsDedekindDomain A] {I J : Ideal A}
    [hIP : I.IsPrime] [hJP : J.IsPrime] (hJ : J ≠ ⊥) (h : I ∣ J) : I = J := by
  by_cases hI : I = ⊥
  · rw [hI, Ideal.dvd_iff_le, le_bot_iff] at h
    rw [h, hI]
  exact (prime_dvd_prime_iff_eq (prime_of_isPrime hI hIP) (prime_of_isPrime hJ hJP)).mp h

section ExpChar

variable (p : ℕ)

local notation3 "𝒑" => (Ideal.span {(p : ℤ)})

attribute [local instance] Ideal.Quotient.field

instance [hp : Fact (Nat.Prime p)] : CharP (ℤ ⧸ 𝒑) p := by
  refine CharP.quotient ℤ p ?_
  rw [mem_nonunits_iff, isUnit_iff_dvd_one, Int.natCast_dvd_ofNat]
  exact Nat.Prime.not_dvd_one hp.out

theorem Int.ideal_span_ne_bot [NeZero p] : 𝒑 ≠ ⊥ := by
  rw [ne_eq, Ideal.span_singleton_eq_bot]
  exact NeZero.ne _

instance [NeZero p] : Finite (ℤ ⧸ 𝒑) := by
  refine Ideal.finiteQuotientOfFreeOfNeBot 𝒑 ?_
  exact Int.ideal_span_ne_bot _

theorem Int.card_ideal_quot : Nat.card (ℤ ⧸ 𝒑) = p := by
  simp [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]

end ExpChar

@[simp]
theorem rootsOfUnity_pow_eq_one {M : Type*} [CommMonoid M] (k : ℕ) (ζ : rootsOfUnity k M) :
    ζ ^ k = 1 := by
  rw [Subtype.ext_iff, Subgroup.coe_pow, Subgroup.coe_one, ← mem_rootsOfUnity]
  exact ζ.prop

open Ideal in
theorem Int.mem_ideal_of_liesOver_span {R : Type*} [Ring R] (d : ℤ) (I : Ideal R)
    [h : I.LiesOver (span {d})] : (d : R) ∈ I := by
  simp [Int.cast_mem_ideal_iff, ← (liesOver_iff _ _).mp h]

@[simp]
theorem MulChar.one_apply_zero {R : Type*} [Nontrivial R] [CommMonoidWithZero R] {R' : Type*}
    [CommMonoidWithZero R'] : (1 : MulChar R R') 0 = 0 := dif_neg not_isUnit_zero

theorem gaussSum_one {R : Type*} [CommRing R] [Fintype R] [DecidableEq R] {R' : Type*}
    [CommRing R'] : gaussSum (1 : MulChar R R') (1 : AddChar R R') = (Fintype.card Rˣ) := by
  classical
  simp [gaussSum, MulChar.sum_one_eq_card_units]

theorem gaussSum_one_left {R : Type*} [Field R] [Fintype R] {R' : Type*} [CommRing R'] [IsDomain R']
    (ψ : AddChar R R') : gaussSum 1 ψ = if ψ = 0 then (Fintype.card R : R') - 1 else -1 := by
  classical
  rw [gaussSum, ← Finset.univ.add_sum_erase _ (Finset.mem_univ 0), MulChar.one_apply_zero,
    zero_mul, zero_add]
  have : ∀ x ∈ Finset.univ.erase (0 : R), (1 : MulChar R R') x = 1 := by
    intro x hx
    exact MulChar.one_apply <| isUnit_iff_ne_zero.mpr <| Finset.ne_of_mem_erase hx
  simp_rw +contextual [this, one_mul]
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ 0), AddChar.map_zero_eq_one, AddChar.sum_eq_ite,
    ite_sub, zero_sub]

theorem gaussSum_one_right {R : Type*} [CommRing R] [Fintype R] {R' : Type*} [CommRing R']
    [IsDomain R'] {χ : MulChar R R'} (hχ : χ ≠ 1) : gaussSum χ 1 = 0 := by
  simpa [gaussSum] using MulChar.sum_eq_zero_of_ne_one hχ

theorem Nat.eq_or_eq_of_totient_eq_totient {a b : ℕ} (h : a ∣ b) (h' : a.totient = b.totient) :
    a = b ∨ 2 * a = b := by
  by_cases ha : a = 0
  · rw [ha, totient_zero, eq_comm, totient_eq_zero] at h'
    simp [ha, h']
  by_cases hb : b = 0
  · rw [hb, totient_zero, totient_eq_zero] at h'
    exact False.elim (ha h')
  obtain ⟨c, rfl⟩ := h
  suffices a.Coprime c by
    rw [totient_mul this, eq_comm, mul_eq_left (totient_eq_zero.not.mpr ha),
      totient_eq_one_iff] at h'
    obtain rfl | rfl := h'
    · simp
    · simp [mul_comm]
  refine coprime_of_dvd fun p hp hap ↦ ?_
  rintro ⟨d, rfl⟩
  suffices a.totient < (p * a * d).totient by
    rw [← mul_assoc, mul_comm a] at h'
    exact h'.not_lt this
  rw [mul_comm p]
  refine lt_of_lt_of_le ?_ (Nat.le_of_dvd ?_ (totient_dvd_of_dvd ⟨d, rfl⟩))
  · rw [mul_comm, totient_mul_of_prime_of_dvd hp hap, Nat.lt_mul_iff_one_lt_left]
    · exact hp.one_lt
    · exact totient_pos.mpr <| pos_of_ne_zero ha
  · exact totient_pos.mpr <| zero_lt_of_ne_zero (by rwa [mul_assoc])

theorem Nat.eq_of_totient_eq_totient {a b : ℕ} (h : a ∣ b) (ha : Even a)
    (h' : a.totient = b.totient) : a = b := by
  by_cases ha' : a = 0
  · rw [ha', totient_zero, eq_comm, totient_eq_zero] at h'
    rw [h', ha']
  refine (eq_or_eq_of_totient_eq_totient h h').resolve_right fun h ↦ ?_
  rw [← h, totient_mul_of_prime_of_dvd (prime_two) (even_iff_two_dvd.mp ha), eq_comm,
    mul_eq_right (totient_eq_zero.not.mpr ha')] at h'
  cutsat

theorem ZMod.orderOf_mod_self_pow_sub_one {n k : ℕ} (hn : 1 < n) (hk : 0 < k) :
    orderOf (n : ZMod (n ^ k - 1)) = k := by
  have : NeZero n := NeZero.of_gt hn
  refine (orderOf_eq_iff hk).mpr ⟨?_, fun m hm₁ hm₂ ↦ ?_⟩
  · rw [← Nat.cast_npow, ← sub_eq_zero, ← Nat.cast_one (R := ZMod (n ^ k - 1)),
      ← Nat.cast_sub NeZero.one_le]
    exact ZMod.natCast_self _
  · rw [ne_eq, ← Nat.cast_npow, ← sub_eq_zero, ← Nat.cast_one (R := ZMod (n ^ k - 1)),
      ← Nat.cast_sub NeZero.one_le, ZMod.natCast_eq_zero_iff]
    refine (Nat.le_of_dvd ?_).mt (not_le.mpr ?_)
    · exact Nat.zero_lt_sub_of_lt <| Nat.one_lt_pow hm₂.ne' hn
    · exact Nat.sub_lt_sub_iff_right NeZero.one_le (c := 1).mpr <| Nat.pow_lt_pow_right hn hm₁

theorem mem_torsion_iff_isPrimitiveRoot {G : Type*} [CommGroup G] {ζ : G} :
    ζ ∈ CommGroup.torsion G ↔ (∃ k, k ≠ 0 ∧ IsPrimitiveRoot ζ k) := by
  rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  refine ⟨fun ⟨n, hn₁, hn₂⟩ ↦ ?_, fun ⟨k, hk₁, hk₂⟩ ↦ ?_⟩
  · exact ⟨orderOf ζ, orderOf_ne_zero_iff.mpr ⟨n, hn₁, (isPeriodicPt_mul_iff_pow_eq_one _).mpr hn₂⟩,
      IsPrimitiveRoot.orderOf ζ⟩
  · exact ⟨k, Nat.zero_lt_of_ne_zero hk₁, hk₂.pow_eq_one⟩

theorem mem_torsion_of_isPrimitiveRoot (k : ℕ) [NeZero k] {G : Type*} [CommGroup G]
    {ζ : G} (hζ : IsPrimitiveRoot ζ k) :
    ζ ∈ CommGroup.torsion G :=
  mem_torsion_iff_isPrimitiveRoot.mpr ⟨k, NeZero.ne _, hζ⟩

@[simp]
lemma RingHom.rangeRestrict_injective_iff {R S : Type*} [Ring R] [Ring S] {f : R →+* S} :
    Function.Injective f.rangeRestrict ↔ Function.Injective f := by
  convert Set.injective_codRestrict _

@[to_additive]
theorem MonoidAlgebra.single_sub {R M : Type*} [Ring R] (a : M) (b₁ b₂ : R) :
    single a (b₁ - b₂) = single a b₁ - single a b₂ :=
  Finsupp.single_sub _ _ _

@[to_additive (attr := simp)]
theorem MonoidAlgebra.fintype_sum_single {k G : Type*} [Fintype G] [Semiring k]
    (f : MonoidAlgebra k G) : ∑ g : G, single g (f g) = f := by
  classical
  rw [← sum_single f, Finsupp.sum_fintype]
  · conv_lhs =>
      enter [2, g, 2]
      rw [Finset.sum_apply']
      simp [single_apply]
  · intro _
    simp

theorem IsCyclotomicExtension.union_of_isPrimitiveRoot (S : Set ℕ) (A B : Type*) [CommRing A]
    [CommRing B] [Algebra A B] [hB : IsCyclotomicExtension S A B] {n : ℕ} {r : B}
    (hr : IsPrimitiveRoot r n) :
    IsCyclotomicExtension (S ∪ {n}) A B := by
  by_cases hn : n = 0
  · rwa [hn, eq_self_sdiff_zero, Set.union_diff_right, ← eq_self_sdiff_zero]
  rw [iff_adjoin_eq_top]
  refine ⟨fun m hm₁ hm₂ ↦ ?_, le_antisymm (by aesop) ?_⟩
  · obtain hm₁ | rfl := hm₁
    · exact exists_isPrimitiveRoot A B hm₁ hm₂
    · use r
  · rw [← ((iff_adjoin_eq_top _ _ _).mp hB).2]
    exact Algebra.adjoin_mono (by aesop)

-- lifted from #29517

lemma IsPrimitiveRoot.div_of_dvd {M : Type*} [CommMonoid M] {ζ : M} {n m : ℕ} [NeZero n]
    (hζ : IsPrimitiveRoot ζ n) (h : m ∣ n) :
    IsPrimitiveRoot (ζ ^ (n / m)) m := by
  have hm0 : 0 < m := by
    rw [Nat.pos_iff_ne_zero]
    rintro rfl
    simp only [zero_dvd_iff] at h
    exact NeZero.out h
  obtain ⟨k, rfl⟩ := id h
  have hk0 : 0 < k := by
    rw [Nat.pos_iff_ne_zero]
    rintro rfl
    simp_all
  simpa [hm0, hk0] using hζ.pow_of_dvd hk0.ne' (dvd_mul_left _ _)

-- These should be generalized

open NumberField in
theorem NumberField.Units.rootsOfUnity_eq_rootsOfUnity (K : Type*) [Field K] [NumberField K]
    (n : ℕ) [NeZero n] :
    rootsOfUnity n (𝓞 K) = rootsOfUnity (n.gcd (torsionOrder K)) (𝓞 K) := by
  ext ζ
  rw [mem_rootsOfUnity, mem_rootsOfUnity]
  refine ⟨fun h ↦ pow_gcd_eq_one ζ h ?_, fun h ↦ ?_⟩
  · have : ζ ∈ torsion K := by
      rw [torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
      exact ⟨n, NeZero.pos n, h⟩
    rwa [← rootsOfUnity_eq_torsion] at this
  · obtain ⟨d, hd⟩ := Nat.gcd_dvd_left n (torsionOrder K)
    rw [hd, pow_mul, h, one_pow]

open NumberField in
theorem NumberField.Units.card_rootsOfUnity (K : Type*) [Field K] [NumberField K]
    (n : ℕ) [NeZero n] (hn : n ∣ torsionOrder K) :
    Fintype.card (rootsOfUnity n (𝓞 K)) = n := by
  obtain ⟨g, hg⟩ : ∃ g : 𝓞 K, IsPrimitiveRoot g (torsionOrder K) := by
    rw [← card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot]
    simp_rw [rootsOfUnity_eq_torsion, torsionOrder]
  exact IsPrimitiveRoot.card_rootsOfUnity (hg.div_of_dvd hn)
