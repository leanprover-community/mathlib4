import Mathlib.Sandbox

noncomputable section

open NumberField Polynomial Ideal KummerDedekind RingOfIntegers UniqueFactorizationMonoid

variable {K : Type*} [Field K]

namespace RingOfIntegers

def exponent (θ : 𝓞 K) : ℕ := absNorm (under ℤ (conductor ℤ θ))

theorem exponent_eq_one_iff {θ : 𝓞 K} :
    exponent θ = 1 ↔ Algebra.adjoin ℤ {θ} = ⊤ := by
  rw [exponent, absNorm_eq_one_iff, comap_eq_top_iff, conductor_eq_top_iff_adjoin_eq_top]

variable {θ : 𝓞 K} {p : ℕ}

theorem not_dvd_exponent_iff [h : Fact (Nat.Prime p)] :
    ¬ p ∣ exponent θ ↔ comap (algebraMap ℤ (𝓞 K)) (conductor ℤ θ) ⊔ span {(p : ℤ)} = ⊤ := by
  rw [sup_comm, IsCoatom.sup_eq_top_iff, ← under_def, ← Ideal.dvd_iff_le,
    Int.ideal_eq_span_absNorm_self (under ℤ (conductor ℤ θ)),
    span_singleton_dvd_span_singleton_iff_dvd, Int.natCast_dvd_natCast, exponent]
  refine isMaximal_def.mp <| Int.ideal_span_isMaximal_of_prime p

variable [h : Fact (Nat.Prime p)] [NumberField K]

def ZModXQuotSpanEquivQuotSpan (hp : ¬ p ∣ exponent θ) :
    (ZMod p)[X] ⧸ span {map (Int.castRingHom (ZMod p)) (minpoly ℤ θ)} ≃+*
      𝓞 K ⧸ span {(p : 𝓞 K)} :=
  (quotientEquivAlgOfEq ℤ (by simp [map_span, Polynomial.map_map])).toRingEquiv.trans
    ((quotientEquiv _ _ (mapEquiv (Int.quotientSpanNatEquivZMod p)) rfl).symm.trans
      ((quotMapEquivQuotQuotMap (not_dvd_exponent_iff.mp hp) θ.isIntegral).symm.trans
        (quotientEquivAlgOfEq ℤ (by simp [map_span])).toRingEquiv))

theorem ZModXQuotSpanEquivQuotSpan_mk_apply (hp : ¬ p ∣ exponent θ) (Q : ℤ [X]) :
  (ZModXQuotSpanEquivQuotSpan hp)
    (Ideal.Quotient.mk (span {map (Int.castRingHom (ZMod p)) (minpoly ℤ θ)})
      (map (Int.castRingHom (ZMod p)) Q)) = Ideal.Quotient.mk (span {(p : 𝓞 K)}) (aeval θ Q) := by
  unfold ZModXQuotSpanEquivQuotSpan
  have : RingHom.comp ((Int.quotientSpanNatEquivZMod p).symm) (Int.castRingHom (ZMod p)) =
    Ideal.Quotient.mk (span {(p : ℤ)}) := by ext; simp
  simp only [AlgEquiv.toRingEquiv_eq_coe, algebraMap_int_eq, RingEquiv.trans_apply,
    AlgEquiv.coe_ringEquiv, quotientEquivAlgOfEq_mk, quotientEquiv_symm_apply, quotientMap_mk,
    RingHom.coe_coe, mapEquiv_symm_apply, Polynomial.map_map, this]
  exact congr_arg (quotientEquivAlgOfEq ℤ (by simp [map_span])) <|
    quotMapEquivQuotQuotMap_symm_apply (not_dvd_exponent_iff.mp hp) θ.isIntegral Q

def _root_.Polynomial.monicFactorsMod (a : ℕ) (A : ℤ[X]) : Set ((ZMod a)[X]) :=
  {Q : (ZMod a)[X] | Irreducible Q ∧ Q.Monic ∧ Q ∣ map (Int.castRingHom (ZMod a)) A}


attribute [local instance] Ideal.Quotient.field Int.ideal_span_isMaximal_of_prime

open UniqueFactorizationMonoid in
def Ideal.primesOverSpanEquivMonicFactorsMod (hp : ¬ p ∣ exponent θ) :
    primesOver (span {(p : ℤ)}) (𝓞 K) ≃ monicFactorsMod p (minpoly ℤ θ) := by
  have h : span {(p : ℤ)} ≠ ⊥ := by
    rw [ne_eq, span_singleton_eq_bot]
    exact NeZero.natCast_ne p ℤ
  refine (Equiv.trans (Equiv.setCongr ?_) (KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
    (I := span {(p : ℤ)})
    (Int.ideal_span_isMaximal_of_prime p) ?_ ?_ θ.isIntegral)).trans ?_
  · apply Ideal.primesOver_eq_normalizedFactors _ _ h
  · exact h
  · exact not_dvd_exponent_iff.mp hp
  · sorry

#exit
    rw [dvd_iff_le, map_le_iff_le_comap, IsCoatom.le_iff_eq, eq_comm]
    · rw [← isMaximal_def]
      exact Int.ideal_span_isMaximal_of_prime p
    · exact IsPrime.ne_top'



  · simpa using NeZero.ne p
  · exact not_dvd_exponent_iff.mp hp
  · sorry

#exit

example :
  {L | L ∈ normalizedFactors (span {Polynomial.map (Int.castRingHom (ZMod p)) (minpoly ℤ θ)})} ≃
    ↑(monicFactorsMod p (minpoly ℤ θ)) :=
  have h : map (Int.castRingHom (ZMod p)) (minpoly ℤ θ) ≠ 0 :=
    map_monic_ne_zero (minpoly.monic θ.isIntegral)
  have : {d | d ∈ normalizedFactors (map (Int.castRingHom (ZMod p)) (minpoly ℤ θ))} =
      monicFactorsMod p (minpoly ℤ θ) := by
    ext Q
    by_cases hQ : Q = 0
    · simp [hQ, zero_notMem_normalizedFactors, monicFactorsMod, not_monic_zero]
    · rw [monicFactorsMod, Set.mem_setOf_eq, Set.mem_setOf_eq, mem_normalizedFactors_iff' h,
        normalize_eq_self_iff_monic hQ]
  (normalizedFactorsEquivSpanNormalizedFactors h).symm.trans (Equiv.setCongr this)

omit [NumberField K] in
def Ideal.primesOverSpanEquivMonicFactorsModAux :
    (monicFactorsMod p (minpoly ℤ θ)) ≃
      {I | I ∈ normalizedFactors (span {map (Int.castRingHom (ZMod p)) (minpoly ℤ θ)})} :=
  have h : map (Int.castRingHom (ZMod p)) (minpoly ℤ θ) ≠ 0 :=
      map_monic_ne_zero (minpoly.monic θ.isIntegral)
  have : monicFactorsMod p (minpoly ℤ θ) =
      {d | d ∈ normalizedFactors (map (Int.castRingHom (ZMod p)) (minpoly ℤ θ))} := by
    ext Q
    by_cases hQ : Q = 0
    · simp [hQ, zero_notMem_normalizedFactors, monicFactorsMod, not_monic_zero]
    · rw [monicFactorsMod, Set.mem_setOf_eq, Set.mem_setOf_eq, mem_normalizedFactors_iff' h,
        normalize_eq_self_iff_monic hQ]
  (Equiv.setCongr this).trans (normalizedFactorsEquivSpanNormalizedFactors h)

omit [NumberField K] in
@[simp]
theorem Ideal.primesOverSpanEquivMonicFactorsModAux_apply {Q : (ZMod p)[X]}
    (hQ : Q ∈ monicFactorsMod p (minpoly ℤ θ)) :
    (Ideal.primesOverSpanEquivMonicFactorsModAux ⟨Q, hQ⟩ : Ideal (ZMod p)[X]) =
      Ideal.span {Q} := rfl

def Ideal.primesOverSpanEquivMonicFactorsMod (hp : ¬ p ∣ exponent θ) :
    primesOver (span {(p : ℤ)}) (𝓞 K) ≃ monicFactorsMod p (minpoly ℤ θ) := by
  refine Equiv.trans (Equiv.setCongr ?_)
    ((normalizedFactorsEquivOfQuotEquiv (ZModXQuotSpanEquivQuotSpan hp) ?_ ?_).symm.trans
      Ideal.primesOverSpanEquivMonicFactorsModAux.symm)
  · sorry
  · sorry
  · sorry
    -- have h : map (Int.castRingHom (ZMod p)) (minpoly ℤ θ) ≠ 0 :=
    --   map_monic_ne_zero (minpoly.monic θ.isIntegral)
    -- have : {d | d ∈ normalizedFactors (map (Int.castRingHom (ZMod p)) (minpoly ℤ θ))} =
    --   monicFactorsMod p (minpoly ℤ θ) := by
    --   ext Q
    --   by_cases hQ : Q = 0
    --   · simp [hQ, zero_notMem_normalizedFactors, monicFactorsMod, not_monic_zero]
    --   · rw [monicFactorsMod, Set.mem_setOf_eq, Set.mem_setOf_eq, mem_normalizedFactors_iff' h,
    --       normalize_eq_self_iff_monic hQ]
    -- exact (normalizedFactorsEquivSpanNormalizedFactors h).symm.trans (Equiv.setCongr this)

theorem Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span
    (hp : ¬ p ∣ exponent θ) {Q : ℤ[X]}
    (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod p (minpoly ℤ θ)) :
    ((primesOverSpanEquivMonicFactorsMod hp).symm
      ⟨Q.map (Int.castRingHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) =
        span {(p : (𝓞 K)), aeval θ Q} := by
  unfold Ideal.primesOverSpanEquivMonicFactorsMod
  simp only [Set.coe_setOf, Equiv.symm_trans_apply, Equiv.symm_symm]
  erw [Equiv.setCongr_symm_apply]
  simp only [Set.mem_setOf_eq]
  erw [normalizedFactorsEquivOfQuotEquiv_apply (ZModXQuotSpanEquivQuotSpan hp)]
--  simp [idealFactorsEquivOfQuotEquiv]
  have := primesOverSpanEquivMonicFactorsModAux_apply hQ
  erw [this]
  rw [map_span]
  rw [Set.image_singleton]

  -- simp only [Set.coe_setOf, Equiv.symm_trans_apply, Equiv.symm_symm]
  -- erw [Equiv.setCongr_symm_apply]
  -- simp only [Set.mem_setOf_eq]
  -- erw [Equiv.setCongr_symm_apply]
  -- simp only [Set.mem_setOf_eq]
  -- rw [normalizedFactorsEquivOfQuotEquiv]
  -- simp only [Set.coe_setOf, Set.mem_setOf_eq, Equiv.coe_fn_mk]
  -- simp_rw [normalizedFactorsEquivSpanNormalizedFactors]
  -- simp





  sorry





#exit

theorem mainEquiv_apply (hp : ¬ p ∣ exponent θ) (Q : ℤ[X]) :
    mainEquiv hp (map (Int.castRingHom (ZMod p)) Q) = aeval θ Q := sorry

variable (p) in
-- Is it better than `normalizedFactors (map (Int.castRingHom (ZMod p)) A)`?
abbrev monicFactorsMod (A : ℤ[X]) : Set ((ZMod p)[X]) :=
  {Q : (ZMod p)[X] | Irreducible Q ∧ Q.Monic ∧ Q ∣ map (Int.castRingHom (ZMod p)) A}



theorem Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span
    (hp : ¬ p ∣ exponent θ) {Q : ℤ[X]}
    (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod p (minpoly ℤ θ)) :
    ((primesOverSpanEquivMonicFactorsMod hp).symm
      ⟨Q.map (Int.castRingHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) =
        span {(p : (𝓞 K)), aeval θ Q} := by
  sorry

theorem Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply (hp : ¬ p ∣ exponent θ)
    {Q : ℤ[X]} (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod p (minpoly ℤ θ)) :
    inertiaDeg (span {(p : ℤ)}) ((primesOverSpanEquivMonicFactorsMod hp).symm
      ⟨Q.map (Int.castRingHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) =
        natDegree (Q.map (Int.castRingHom (ZMod p))) := by
  sorry

theorem Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply (hp : ¬ p ∣ exponent θ)
    {Q : ℤ[X]} (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod p (minpoly ℤ θ)) :
    ramificationIdx (algebraMap ℤ (𝓞 K)) (span {(p : ℤ)})
      ((primesOverSpanEquivMonicFactorsMod hp).symm
        ⟨Q.map (Int.castRingHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) =
          emultiplicity (Q.map (Int.castRingHom (ZMod p)))
            ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) := by
  sorry
