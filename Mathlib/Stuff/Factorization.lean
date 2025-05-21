import Mathlib


variable {K : Type*} [Field K] [Fintype K] {p f n : ℕ}
  (hK : Fintype.card K = p ^ f) (hn : (p ^ f).Coprime n)

open Polynomial ZMod AdjoinRoot FiniteField Multiset

lemma stupid (p : ℕ) {P : ℤ[X]} {q1 q2 : (ZMod p)[X]} (h : ∃ A Q1 Q2 : ℤ[X],
      Q1.map (Int.castRingHom (ZMod p)) = q1 ∧
      Q2.map (Int.castRingHom (ZMod p)) = q2 ∧
      P + p*A = Q1 * Q2) :
    P.map (Int.castRingHom (ZMod p)) = q1 * q2 := by
  obtain ⟨A, Q1, Q2, h1, h2, h3⟩ := h
  apply_fun Polynomial.map (Int.castRingHom (ZMod p)) at h3
  simp only [Polynomial.map_add, Polynomial.map_mul, h1, h2] at h3
  suffices Polynomial.map (Int.castRingHom (ZMod p)) p = 0 by
    rwa [this, zero_mul, add_zero] at h3
  simp

include hK

lemma f_ne_zero : f ≠ 0 := fun h0 ↦ not_subsingleton K <|
    Fintype.card_le_one_iff_subsingleton.mp <| by simpa [h0] using hK.le

variable [hp : Fact p.Prime]

lemma char : CharP K p :=
  have hf : f ≠ 0 := fun h0 ↦ not_subsingleton K <|
    Fintype.card_le_one_iff_subsingleton.mp <| by simpa [h0] using hK.le
  (CharP.charP_iff_prime_eq_zero hp.out).mpr (by simpa [hf, hK] using cast_card_eq_zero K)

theorem foo {P : K[X]} (hP : P ∣ cyclotomic n K) (hPirr : Irreducible P) (hPmo : P.Monic) :
    P.natDegree = orderOf (unitOfCoprime _ hn) := by
  have : Fact (Irreducible P) := ⟨hPirr⟩
  have := hPmo.finite_adjoinRoot
  have : Finite (AdjoinRoot P) := Module.finite_of_finite K
  have hζ : IsPrimitiveRoot (root P) n := by
    have : NeZero (n : AdjoinRoot P) := by
      suffices NeZero (n : K) by
        simpa using NeZero.of_injective (algebraMap K (AdjoinRoot P)).injective
      have := char hK
      exact ⟨fun h0 ↦ Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨p, hp.out, dvd_pow_self p (f_ne_zero hK), (CharP.cast_eq_zero_iff K p n).mp h0⟩ hn⟩
    simpa [← isRoot_cyclotomic_iff] using (isRoot_root P).dvd
      (by simpa using map_dvd (algebraMap K (AdjoinRoot P)) hP)
  let pB := powerBasis hPirr.ne_zero
  rw [← powerBasis_dim hPirr.ne_zero, ← pB.finrank, ← orderOf_frobeniusAlgEquivOfAlgebraic]
  have hζ' := isOfFinOrder_iff_pow_eq_one.mpr
      ⟨n, pos_of_ne_zero (fun h0 ↦ by simp [h0, hp.out.ne_one, (f_ne_zero hK)] at hn),
      hζ.pow_eq_one⟩
  refine dvd_antisymm
    (orderOf_dvd_iff_pow_eq_one.mpr <| AlgEquiv.coe_algHom_injective <| pB.algHom_ext ?_)
    (orderOf_dvd_iff_pow_eq_one.mpr <| Units.ext ?_)
  · simp only [AlgHom.coe_coe, AlgEquiv.coe_pow, AlgEquiv.one_apply,
      coe_frobeniusAlgEquivOfAlgebraic, pow_iterate, hK]
    nth_rewrite 2 [← pow_one pB.gen]
    rw [powerBasis_gen hPirr.ne_zero, hζ'.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf, ← eq_iff_modEq_nat]
    simpa using Units.eq_iff.mpr <| pow_orderOf_eq_one (unitOfCoprime _ hn)
  · let φ := frobeniusAlgEquivOfAlgebraic K (AdjoinRoot P)
    have : (φ ^ orderOf φ) (root P) = root P := by simp [pow_orderOf_eq_one φ]
    simp only [AlgEquiv.coe_pow, φ, coe_frobeniusAlgEquivOfAlgebraic, pow_iterate, hK] at this
    rw [Units.val_one, ← Nat.cast_one, Units.val_pow_eq_pow_val, coe_unitOfCoprime,
      ← Nat.cast_pow, eq_iff_modEq_nat, hζ.eq_orderOf, ← hζ'.pow_eq_pow_iff_modEq, this, pow_one]

theorem bar {P : K[X]} (hP : P ∣ cyclotomic n K) (hPirr : Irreducible P) :
    P.natDegree = orderOf (unitOfCoprime _ hn) := by
  obtain ⟨A, hA⟩ := hP
  have hQ : P * C P.leadingCoeff⁻¹ ∣ cyclotomic n K := by
    refine ⟨A * C P.leadingCoeff, ?_⟩
    calc
      _ = P * A := hA
      _ = P * (C P.leadingCoeff⁻¹ * C P.leadingCoeff) * A := by
        field_simp [← C_mul, leadingCoeff_ne_zero.mpr hPirr.ne_zero]
      _ = _ := by ring
  simpa [← natDegree_mul_leadingCoeff_self_inv P] using foo hK hn hQ
    (irreducible_mul_leadingCoeff_inv.mpr hPirr) (monic_mul_leadingCoeff_inv hPirr.ne_zero)

open UniqueFactorizationMonoid in
theorem baz {P : K[X]} (hP : P ∣ cyclotomic n K)
    (hPdeg : P.natDegree = orderOf (unitOfCoprime _ hn)) : Irreducible P := by
  classical
  have hP0 : P ≠ 0 := ne_zero_of_dvd_ne_zero (cyclotomic_ne_zero n K) hP
  obtain ⟨Q, HQ⟩ := exists_mem_normalizedFactors hP0 <| not_isUnit_of_natDegree_pos _ <|
    pos_of_ne_zero <| fun h ↦ orderOf_eq_zero_iff.mp (h ▸ hPdeg.symm) <| isOfFinOrder_of_finite ..
  refine (associated_of_dvd_of_natDegree_le (dvd_of_mem_normalizedFactors HQ) hP0 ?_).irreducible
    (irreducible_of_normalized_factor Q HQ)
  rw [hPdeg, ← bar hK hn ?_ (irreducible_of_normalized_factor Q HQ)]
  exact dvd_of_mem_normalizedFactors <| mem_of_le
    ((dvd_iff_normalizedFactors_le_normalizedFactors hP0 (cyclotomic_ne_zero n K)).mp hP) HQ

open UniqueFactorizationMonoid Nat

variable [DecidableEq K]

theorem boh {P : K[X]} (hP : P ∈ normalizedFactors (cyclotomic n K)) :
    P.natDegree = orderOf (unitOfCoprime _ hn) :=
  bar hK _ (dvd_of_mem_normalizedFactors hP) (irreducible_of_normalized_factor P hP)

theorem blah : (normalizedFactors (cyclotomic n K)).toFinset.card =
    φ n / orderOf (unitOfCoprime _ hn) := by
  have h := prod_normalizedFactors (cyclotomic_ne_zero n K)
  have : ∀ P ∈ normalizedFactors (cyclotomic n K), P.natDegree = orderOf (unitOfCoprime _ hn) :=
    fun P hP ↦ boh hK hn hP
  have H := natDegree_eq_of_degree_eq <| degree_eq_degree_of_associated h
  rw [natDegree_cyclotomic, natDegree_multiset_prod _ (zero_not_mem_normalizedFactors _),
    map_congr rfl this] at H
  simp only [map_const', sum_replicate, smul_eq_mul] at H
  rw [← H, mul_div_left _ (orderOf_pos _), toFinset_card_of_nodup]
  refine nodup_iff_count_le_one.mpr (fun P ↦ ?_)
  by_contra! H
  have : Squarefree (cyclotomic n K) := by
    have := char hK
    refine ((X_pow_sub_one_separable_iff.mpr (fun Hn ↦ ?_)).of_dvd
      (cyclotomic.dvd_X_pow_sub_one n K)).squarefree
    refine hp.out.coprime_iff_not_dvd.mp ((Nat.coprime_pow_left_iff
      (pos_of_ne_zero <| f_ne_zero hK) _ _).mp hn) ((CharP.cast_eq_zero_iff K p _).mp Hn)
  have hP : P ∈ normalizedFactors (cyclotomic n K) := count_pos.mp (by omega)
  refine (prime_of_normalized_factor _ hP).not_unit (this P ?_)
  have : {P, P} ≤ normalizedFactors (cyclotomic n K) := by
    refine le_iff_count.mpr (fun Q ↦ ?_)
    by_cases hQ : Q = P
    · simp only [hQ, insert_eq_cons, count_cons_self, nodup_singleton, mem_singleton,
      count_eq_one_of_mem, reduceAdd]
      omega
    · simp [hQ]
  have := prod_dvd_prod_of_le this
  simp only [insert_eq_cons, prod_cons, prod_singleton] at this
  exact this.trans h.dvd
