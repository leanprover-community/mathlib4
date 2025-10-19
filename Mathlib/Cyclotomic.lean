import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.Misc

open Polynomial in
theorem Polynomial.cyclotomic_eq_minpoly' {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    [CharZero R] {μ : R} (h : IsPrimitiveRoot μ n) (hpos : 0 < n) :
    cyclotomic n ℤ = minpoly ℤ μ := by
  have h' : IsPrimitiveRoot (algebraMap R (FractionRing R) μ) n :=
    h.map_of_injective <| FaithfulSMul.algebraMap_injective R _
  apply map_injective (algebraMap ℤ ℚ) <| RingHom.injective_int _
  rw [← @minpoly.isIntegrallyClosed_eq_field_fractions ℤ R _ _ _ _ ℚ (FractionRing R) _ _
    _ _ _ _ _ _ ?_ _ _ _ μ (h.isIntegral hpos), ← cyclotomic_eq_minpoly_rat h' hpos, map_cyclotomic]
  -- We need to do that because of the `zsmul` diamond, see the discussion
  -- "Instance diamond in `OreLocalization`" on Zulip
  convert AddCommGroup.intIsScalarTower (R := ℚ) (M := FractionRing R) using 1
  ext n x
  exact OreLocalization.zsmul_eq_zsmul n x

namespace IsCyclotomicExtension.Rat

open Ideal NumberField

section PrimePow

variable (p k : ℕ) [hp : Fact (Nat.Prime p)] {K : Type*} [Field K] [NumberField K]
  [hK : IsCyclotomicExtension {p ^ (k + 1)} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))

instance isPrime_span_zeta_sub_one : IsPrime (span {hζ.toInteger - 1}) := by
  rw [Ideal.span_singleton_prime]
  · exact hζ.zeta_sub_one_prime
  · exact Prime.ne_zero hζ.zeta_sub_one_prime

theorem associated_norm_zeta_sub_one : Associated (Algebra.norm ℤ (hζ.toInteger - 1)) (p : ℤ) := by
  by_cases h : p = 2
  · cases k with
  | zero =>
    rw [h, zero_add, pow_one] at hK hζ
    rw [hζ.norm_toInteger_sub_one_of_eq_two, h, Int.ofNat_two, Associated.neg_left_iff]
  | succ n =>
    rw [h, add_assoc, show 1 + 1 = 2 by rfl] at hK hζ
    rw [hζ.norm_toInteger_sub_one_of_eq_two_pow, h, Int.ofNat_two]
  · rw [hζ.norm_toInteger_sub_one_of_prime_ne_two h]

theorem absNorm_span_zeta_sub_one : absNorm (span {hζ.toInteger - 1}) = p := by
  simpa using congr_arg absNorm <|
    span_singleton_eq_span_singleton.mpr <| associated_norm_zeta_sub_one p k hζ

theorem p_mem_span_zeta_sub_one : (p : 𝓞 K) ∈ span {hζ.toInteger - 1} := by
  convert Ideal.absNorm_mem _
  exact (absNorm_span_zeta_sub_one ..).symm

theorem span_zeta_sub_one_ne_bot : span {hζ.toInteger - 1} ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨p, p_mem_span_zeta_sub_one p k hζ, NeZero.natCast_ne p (𝓞 K)⟩

local notation3 "𝒑" => (Ideal.span {(p : ℤ)})

theorem liesOver_span_zeta_sub_one : (span {hζ.toInteger - 1}).LiesOver 𝒑 := by
  rw [liesOver_iff]
  refine Ideal.IsMaximal.eq_of_le (Int.ideal_span_isMaximal_of_prime p) IsPrime.ne_top' ?_
  rw [span_singleton_le_iff_mem, mem_comap, algebraMap_int_eq, map_natCast]
  exact p_mem_span_zeta_sub_one p k hζ

theorem inertiaDeg_span_zeta_sub_one : inertiaDeg 𝒑 (span {hζ.toInteger - 1}) = 1 := by
  have := liesOver_span_zeta_sub_one p k hζ
  rw [← Nat.pow_right_inj hp.out.one_lt, pow_one, ← absNorm_eq_pow_inertiaDeg' _ hp.out,
    absNorm_span_zeta_sub_one]

attribute [local instance] FractionRing.liftAlgebra in
theorem map_eq_span_zeta_sub_one_pow :
    (map (algebraMap ℤ (𝓞 K)) 𝒑) = span {hζ.toInteger - 1} ^ Module.finrank ℚ K := by
  have : IsGalois ℚ K := isGalois {p ^ (k + 1)} ℚ K
  have : IsGalois (FractionRing ℤ) (FractionRing (𝓞 K)) := by
    refine IsGalois.of_equiv_equiv (f := (FractionRing.algEquiv ℤ ℚ).toRingEquiv.symm)
      (g := (FractionRing.algEquiv (𝓞 K) K).toRingEquiv.symm) <|
        RingHom.ext fun x ↦ IsFractionRing.algEquiv_commutes (FractionRing.algEquiv ℤ ℚ).symm
          (FractionRing.algEquiv (𝓞 K) K).symm _
  rw [map_span, Set.image_singleton, span_singleton_eq_span_singleton.mpr
    ((associated_norm_zeta_sub_one p k hζ).symm.map (algebraMap ℤ (𝓞 K))),
    ← Algebra.intNorm_eq_norm, Algebra.algebraMap_intNorm_of_isGalois, ← prod_span_singleton]
  conv_lhs =>
    enter [2, σ]
    rw [span_singleton_eq_span_singleton.mpr
      (hζ.toInteger_isPrimitiveRoot.associated_sub_one_map_sub_one σ).symm]
  rw [Finset.prod_const, Finset.card_univ, ← Fintype.card_congr (galRestrict ℤ ℚ K (𝓞 K)).toEquiv,
    ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]

theorem ramificationIdx_span_zeta_sub_one :
    ramificationIdx (algebraMap ℤ (𝓞 K)) 𝒑 (span {hζ.toInteger - 1}) = p ^ k * (p - 1) := by
  have := liesOver_span_zeta_sub_one p k hζ
  have h := isPrime_span_zeta_sub_one p k hζ
  rw [← Nat.totient_prime_pow_succ hp.out, ← finrank _ K,
    IsDedekindDomain.ramificationIdx_eq_multiplicity _ h, map_eq_span_zeta_sub_one_pow p k hζ,
    multiplicity_pow_self (span_zeta_sub_one_ne_bot p k hζ) (isUnit_iff.not.mpr h.ne_top)]
  exact map_ne_bot_of_ne_bot <| by simpa using hp.out.ne_zero

variable (K)

include hK in
theorem ncard_primesOver_of_prime_pow :
    (primesOver 𝒑 (𝓞 K)).ncard = 1 := by
  have : IsGalois ℚ K := isGalois {p ^ (k + 1)} ℚ K
  have : 𝒑 ≠ ⊥ := by simpa using hp.out.ne_zero
  have h_main := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn this (𝓞 K) ℚ K
  have hζ := hK.zeta_spec
  have := liesOver_span_zeta_sub_one p k hζ
  rwa [ramificationIdxIn_eq_ramificationIdx 𝒑 (span {hζ.toInteger - 1}) ℚ K,
    inertiaDegIn_eq_inertiaDeg 𝒑 (span {hζ.toInteger - 1}) ℚ K, inertiaDeg_span_zeta_sub_one,
    ramificationIdx_span_zeta_sub_one, mul_one, ← Nat.totient_prime_pow_succ hp.out,
    ← finrank _ K, Nat.mul_eq_right] at h_main
  exact Module.finrank_pos.ne'

theorem eq_span_zeta_sub_one_of_liesOver (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] :
    P = span {hζ.toInteger - 1} := by
  have : P ∈ primesOver 𝒑 (𝓞 K) := ⟨hP₁, hP₂⟩
  have : span {hζ.toInteger - 1} ∈ primesOver 𝒑 (𝓞 K) :=
    ⟨isPrime_span_zeta_sub_one p k hζ, liesOver_span_zeta_sub_one p k hζ⟩
  have := ncard_primesOver_of_prime_pow p k K
  aesop

include hK in
theorem inertiaDeg_eq_of_prime_pow (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] :
    inertiaDeg 𝒑 P = 1 := by
  rw [eq_span_zeta_sub_one_of_liesOver p k K hK.zeta_spec P, inertiaDeg_span_zeta_sub_one]

include hK in
theorem ramificationIdx_eq_of_prime_pow (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] :
    ramificationIdx (algebraMap ℤ (𝓞 K)) 𝒑 P = p ^ k * (p - 1) := by
  rw [eq_span_zeta_sub_one_of_liesOver p k K hK.zeta_spec P, ramificationIdx_span_zeta_sub_one]

end PrimePow

section notDVD

variable (m : ℕ) [NeZero m] {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
  (p : ℕ) [hp : Fact (p.Prime)] (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]

local notation3 "𝒑" => (Ideal.span {(p : ℤ)})

open NumberField RingOfIntegers Ideal

theorem inertiaDeg_of_not_dvd (hm : ¬ p ∣ m) :
    inertiaDeg 𝒑 P = orderOf (p : ZMod m) := by
  replace hm : p.Coprime m := not_not.mp <| (Nat.Prime.dvd_iff_not_coprime hp.out).not.mp hm
  let ζ := (zeta_spec m ℚ K).toInteger
  have h₁ : ¬ p ∣ exponent ζ := by
    rw [exponent_eq_one_iff.mpr <| adjoin_singleton_eq_top m K (zeta_spec m ℚ K)]
    exact hp.out.not_dvd_one
  have h₂ := (primesOverSpanEquivMonicFactorsMod h₁ ⟨P, ⟨inferInstance, inferInstance⟩⟩).2
  have h₃ := inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' h₁ h₂
  simp only [Subtype.coe_eta, Equiv.symm_apply_apply] at h₃
  rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff
    (Polynomial.map_monic_ne_zero (minpoly.monic ζ.isIntegral))] at h₂
  rw [h₃, Polynomial.natDegree_of_dvd_cyclotomic_of_irreducible (by simp) hm (f := 1) _ h₂.1]
  · simpa using (orderOf_injective _ Units.coeHom_injective (ZMod.unitOfCoprime p hm)).symm
  · refine dvd_trans h₂.2.2 ?_
    rw [← Polynomial.map_cyclotomic_int, ← Polynomial.cyclotomic_eq_minpoly' _ (NeZero.pos m)]
    exact (zeta_spec m ℚ K).toInteger_isPrimitiveRoot


#exit

  rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff] at h
  · rw [Polynomial.natDegree_of_dvd_cyclotomic_of_irreducible (p := p) (f := 1)]
    · simp
      exact (orderOf_injective _ Units.coeHom_injective (ZMod.unitOfCoprime p hm)).symm
    · simp
    · simpa
    · have := h.2.2
      refine dvd_trans this ?_
      rw [← Polynomial.map_cyclotomic_int]
      rw [← Polynomial.cyclotomic_eq_minpoly' m (𝓞 K) _ (NeZero.pos _)]
      exact IsPrimitiveRoot.toInteger_isPrimitiveRoot _
    · exact h.1
  · exact Polynomial.map_monic_ne_zero (minpoly.monic ζ.isIntegral)

theorem ramificationIdx_of_not_dvd (hm : ¬ p ∣ m) :
    ramificationIdx (algebraMap ℤ (𝓞 K)) 𝒑 P = 1 := by
  sorry

end notDVD

section general

variable (n : ℕ) [NeZero n] {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
  (p : ℕ) [hp : Fact (p.Prime)] (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]

local notation3 "𝒑" => (Ideal.span {(p : ℤ)})

example {k m : ℕ} (hn : n = p ^ k * m) (hm : ¬ p ∣ m) :
    inertiaDeg 𝒑 P = orderOf (p : ZMod m) ∧
      ramificationIdx (algebraMap ℤ (𝓞 K)) 𝒑 P = p ^ k * (p - 1) := by

  sorry



end general

end IsCyclotomicExtension.Rat





theorem IsCyclotomicExtension_single_iff_single_two_mul_of_odd (n : ℕ) (hn : Odd n)
    (A B : Type*) [CommRing A] [CommRing B] [Nontrivial B] [NoZeroDivisors B] [Algebra A B]
    (hB : ringChar B ≠ 2) :
    IsCyclotomicExtension {n} A B ↔ IsCyclotomicExtension {2 * n} A B := by
  have : NeZero n := by
    refine ⟨?_⟩
    exact Nat.ne_of_odd_add hn
  have h : orderOf (-1 : B) = 2 := by
    rw [orderOf_neg_one, if_neg hB]
  rw [IsCyclotomicExtension.iff_singleton, IsCyclotomicExtension.iff_singleton]
  congr! 1
  · refine ⟨?_, ?_⟩
    · intro ⟨ζ, hζ⟩
      refine ⟨-ζ, ?_⟩
      convert IsPrimitiveRoot.orderOf (-ζ)
      rw [neg_eq_neg_one_mul, (Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime]
      · rw [h, hζ.eq_orderOf]
      · rw [h, ← hζ.eq_orderOf]
        exact Nat.coprime_two_left.mpr hn
    · intro ⟨ζ, hζ⟩
      exact ⟨ζ ^ 2, hζ.pow (NeZero.pos _) rfl⟩
  · suffices Algebra.adjoin A {b : B | b ^ n = 1} = Algebra.adjoin A {b : B | b ^ (2 * n) = 1} by
      rw [SetLike.ext_iff] at this
      exact forall_congr' this
    apply le_antisymm
    · apply Algebra.adjoin_mono
      intro b hb
      rw [Set.mem_setOf_eq, mul_comm, pow_mul, hb, one_pow]
    · apply Algebra.adjoin_le
      intro b hb
      rw [Set.mem_setOf_eq, mul_comm, pow_mul, sq_eq_one_iff] at hb
      obtain hb | hb := hb
      · apply Algebra.subset_adjoin
        exact hb
      · simp only [SetLike.mem_coe]
        rw [show b = - - b by exact Eq.symm (InvolutiveNeg.neg_neg b)]
        apply Subalgebra.neg_mem
        apply Algebra.subset_adjoin
        rw [Set.mem_setOf_eq, neg_pow, Odd.neg_one_pow hn, neg_mul, one_mul, hb, neg_neg]



-- Golf `IsCyclotomicExtension.of_union_of_dvd` using this
theorem IsCyclotomicExtension.exists_prim_root_of_dvd {n : ℕ} [NeZero n] {S : Set ℕ} (A B : Type*)
    [CommRing A] [CommRing B] [Algebra A B] (h : ∃ s ∈ S, s ≠ 0 ∧ n ∣ s)
    [H : IsCyclotomicExtension S A B] :
    ∃ (r : B), IsPrimitiveRoot r n := by
  obtain ⟨m, hm, hm', ⟨x, rfl⟩⟩ := h
  obtain ⟨ζ, hζ⟩ := H.exists_isPrimitiveRoot hm hm'
  refine ⟨ζ ^ x, ?_⟩
  have h_xnz : x ≠ 0 := Nat.ne_zero_of_mul_ne_zero_right hm'
  have := hζ.pow_of_dvd h_xnz (dvd_mul_left x n)
  rwa [mul_div_cancel_right₀ _ h_xnz] at this

open NumberField Units

theorem NumberField.Units.mem_torsion' (K : Type*) [Field K] [NumberField K]
    {x : (𝓞 K)ˣ} :
    x ∈ torsion K ↔ IsOfFinOrder x := CommGroup.mem_torsion _ _

theorem NumberField.dvd_torsionOrder_of_isPrimitiveRoot {n : ℕ} [NeZero n] {K : Type*} [Field K]
    [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    n ∣ torsionOrder K := by
  rw [torsionOrder, Fintype.card_eq_nat_card]
  replace hζ := (hζ.toInteger_isPrimitiveRoot).isUnit_unit (NeZero.ne n)
  have hζ' := CommGroup.mem_torsion_of_isPrimitiveRoot n hζ
  convert orderOf_dvd_natCard (⟨_, hζ'⟩ : torsion K)
  rw [Subgroup.orderOf_mk]
  exact hζ.eq_orderOf

theorem NumberField.Units.torsionOrder_eq_of_isCyclotomicExtension (n : ℕ) [NeZero n] {K : Type*}
    [Field K] [NumberField K] [hK : IsCyclotomicExtension {n} ℚ K] :
    torsionOrder K = if Even n then n else 2 * n := by
  have hζ := hK.zeta_spec
  obtain ⟨μ, hμ⟩ : ∃ μ : torsion K, orderOf μ = torsionOrder K := by
    rw [torsionOrder, Fintype.card_eq_nat_card]
    exact IsCyclic.exists_ofOrder_eq_natCard
  rw [← IsPrimitiveRoot.iff_orderOf, ← IsPrimitiveRoot.coe_submonoidClass_iff,
    ← IsPrimitiveRoot.coe_units_iff] at hμ
  replace hμ := hμ.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  have h := IsPrimitiveRoot.pow_mul_pow_lcm hζ hμ (NeZero.ne _) (torsionOrder_ne_zero K)
  have : NeZero (n.lcm (torsionOrder K)) :=
    NeZero.of_pos <| Nat.lcm_pos_iff.mpr ⟨NeZero.pos n, torsionOrder_pos K⟩
  have : IsCyclotomicExtension {n.lcm (torsionOrder K)} ℚ K := by
    have := hK.union_of_isPrimitiveRoot _ _ _ h
    rwa [Set.union_comm, ← IsCyclotomicExtension.iff_union_of_dvd] at this
    exact ⟨n.lcm (torsionOrder K), by simp, NeZero.ne _, Nat.dvd_lcm_left _ _⟩
  have hmain := (IsCyclotomicExtension.Rat.finrank n K).symm.trans <|
    (IsCyclotomicExtension.Rat.finrank (n.lcm (torsionOrder K)) K)
  obtain hn | hn := Nat.even_or_odd n
  · rw [if_pos hn]
    apply dvd_antisymm
    · have := Nat.eq_of_totient_eq_totient (Nat.dvd_lcm_left _ _) hn hmain
      rwa [eq_comm, Nat.lcm_eq_left_iff_dvd] at this
    · exact NumberField.dvd_torsionOrder_of_isPrimitiveRoot hζ
  · rw [if_neg (Nat.not_even_iff_odd.mpr hn)]
    have := (Nat.eq_or_eq_of_totient_eq_totient (Nat.dvd_lcm_left _ _) hmain).resolve_left ?_
    · rw [this, eq_comm, Nat.lcm_eq_right_iff_dvd]
      exact NumberField.dvd_torsionOrder_of_isPrimitiveRoot hζ
    · rw [eq_comm, Nat.lcm_eq_left_iff_dvd]
      intro h
      exact Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hn h) (even_torsionOrder K)

open Ideal

variable (p k : ℕ) [hp : Fact (Nat.Prime p)] {K : Type*} [Field K] [NumberField K]
    [hK : IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))

example (e : ℕ) (he : (hζ.toInteger - 1) ^ e ∣ p ∧ ¬ (hζ.toInteger - 1) ^ (e + 1) ∣ p) :
    e = p ^ k * (p - 1) := by
  obtain ⟨x, hx⟩ := he.1
  have h_main := congr_arg (Int.natAbs ·) <| congr_arg (Algebra.norm ℤ ·) hx
  dsimp at h_main
  have : Algebra.norm ℤ (p : 𝓞 K) = p ^ Module.finrank ℚ K := sorry
  rw [this] at h_main
  by_cases hodd : p = 2
  · sorry
  rw [map_mul, map_pow, hζ.norm_toInteger_sub_one_of_prime_ne_two hodd] at h_main
  have hx' : ¬ ↑p ∣ Algebra.norm ℤ x := by
    by_contra!



    sorry
  have := congr_arg (Nat.factorization · p) h_main
  dsimp at this
  simp [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_cast, Nat.factorization_pow,
    Finsupp.coe_smul, Nat.factorization_mul sorry sorry,
    Pi.smul_apply, _root_.smul_eq_mul, Nat.Prime.factorization_self hp.out] at this
  rw [Nat.factorization_eq_zero_of_not_dvd, add_zero] at this
  rw [← this, IsCyclotomicExtension.Rat.finrank (p ^ (k + 1))]
  rw [Nat.totient_prime_pow, Nat.add_sub_cancel_right]
  exact hp.out
  exact Nat.zero_lt_succ k
  rwa [← Int.natCast_dvd]

example (p k : ℕ) [hp : Fact (Nat.Prime p)] (hodd : p ≠ 2) {K : Type*} [Field K] [NumberField K]
    [hK : IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [P.LiesOver (span {(p : ℤ)})] :
    ramificationIdx (algebraMap ℤ (𝓞 K)) (span {(p : ℤ)}) P = p ^ k * (p - 1) := by
  let hζ := IsCyclotomicExtension.zeta_spec (p ^ (k + 1)) ℚ K
  have t₀ := hζ.zeta_sub_one_prime
  have t₁ := hζ.norm_toInteger_sub_one_of_prime_ne_two hodd
  have : P = span {hζ.toInteger - 1} := sorry
  rw [this]

  have t₂ : FiniteMultiplicity (hζ.toInteger - 1) (algebraMap ℤ (𝓞 K) p) := by
    apply?
  have := t₂.multiplicity_eq_iff.mp rfl
  obtain ⟨x, hx⟩ := this.1
  have := congr_arg (Algebra.norm ℚ ·) <| congr_arg (algebraMap (𝓞 K) K ·) hx
  set e := multiplicity (hζ.toInteger - 1) (algebraMap ℤ (𝓞 K) p)
  dsimp only at this

  rw [← Algebra.coe_norm_int] at this
  rw? at this
  rw [map_mul, map_pow, t₁] at this

  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity]
  simp [algebraMap_int_eq, map_span, eq_intCast, Set.image_singleton, Int.cast_natCast]
  rw [FiniteMultiplicity.multiplicity_eq_iff]
  simp_rw [span_singleton_pow, dvd_iff_le, Ideal.span_singleton_le_span_singleton]

  obtain ⟨x, hx⟩ := IsPrimitiveRoot.toInteger_sub_one_dvd_prime hζ

  apply Ideal.ramificationIdx_spec
  · simp [algebraMap_int_eq, map_span, eq_intCast, Set.image_singleton, Int.cast_natCast,
      span_singleton_pow, span_singleton_le_span_singleton]


    sorry
  · sorry
