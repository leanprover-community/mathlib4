import Mathlib.NumberTheory.Cyclotomic.Rat
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.Misc

open Polynomial in
theorem Polynomial.cyclotomic_eq_minpoly' (n : ℕ) (R : Type*) [CommRing R] [IsDomain R]
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

open NumberField RingOfIntegers in
theorem IsCyclotomicExtension.Rat.inertiaDeg_of_coprime (m : ℕ) [NeZero m] {K : Type*}
    [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K] (p : ℕ) [hp : Fact (p.Prime)]
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] (hm : p.Coprime m) :
    (Ideal.span {(p : ℤ)}).inertiaDeg P = orderOf (p : ZMod m) := by
  let ζ := (IsCyclotomicExtension.zeta_spec m ℚ K).toInteger
  have h₁ : exponent ζ = 1 := by
    rw [exponent_eq_one_iff]
    exact IsCyclotomicExtension.Rat.adjoin_singleton_eq_top m K _
  have h₂ : ¬ p ∣ exponent ζ := by
    rw [h₁]
    exact hp.out.not_dvd_one
  let hQ := Ideal.primesOverSpanEquivMonicFactorsMod h₂ ⟨P, ⟨inferInstance, inferInstance⟩⟩
  have := Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' h₂ hQ.2
  simp only [Subtype.coe_eta, Equiv.symm_apply_apply, hQ] at this
  rw [this]
  have h := hQ.2
  rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff] at h
  · rw [foo (p := p) (f := 1)]
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
    · exact h.2.1
  · exact Polynomial.map_monic_ne_zero (minpoly.monic ζ.isIntegral)

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
