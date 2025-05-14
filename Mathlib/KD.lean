import Mathlib.Sandbox

noncomputable section

open Polynomial NumberField Ideal KummerDedekind RingOfIntegers UniqueFactorizationMonoid

variable {K : Type*} [Field K] {θ : 𝓞 K} {p : ℕ} [h : Fact (Nat.Prime p)]

namespace RingOfIntegers

def exponent (θ : 𝓞 K) : ℕ := absNorm (under ℤ (conductor ℤ θ))

theorem exponent_eq_one_iff {θ : 𝓞 K} :
    exponent θ = 1 ↔ Algebra.adjoin ℤ {θ} = ⊤ := by
  rw [exponent, absNorm_eq_one_iff, comap_eq_top_iff, conductor_eq_top_iff_adjoin_eq_top]

theorem not_dvd_exponent_iff :
    ¬ p ∣ exponent θ ↔ comap (algebraMap ℤ (𝓞 K)) (conductor ℤ θ) ⊔ span {(p : ℤ)} = ⊤ := by
  rw [sup_comm, IsCoatom.sup_eq_top_iff, ← under_def, ← Ideal.dvd_iff_le,
    Int.ideal_eq_span_absNorm_self (under ℤ (conductor ℤ θ)),
    span_singleton_dvd_span_singleton_iff_dvd, Int.natCast_dvd_natCast, exponent]
  refine isMaximal_def.mp <| Int.ideal_span_isMaximal_of_prime p

example [NumberField K] (x : 𝓞 K) :
    exponent θ * x ∈ Algebra.adjoin ℤ {θ} := by
  have : (exponent θ : 𝓞 K) ∈ conductor ℤ θ := by
    have : (exponent θ : ℤ) ∈ under ℤ (conductor ℤ θ) := Ideal.absNorm_mem _
    rw [under_def] at this
    simpa only [algebraMap_int_eq, mem_comap, map_natCast]
  exact this x

theorem mem_conductor_iff_exponent_dvd [NumberField K] {d : ℕ} :
    (d : 𝓞 K) ∈ conductor ℤ θ ↔ (exponent θ : ℤ) ∣ d := by
  rw [← Int.cast_natCast, ← eq_intCast (algebraMap ℤ (𝓞 K)), ← Ideal.mem_comap, ← under_def]
  rw [Int.ideal_eq_span_absNorm_self (under ℤ (conductor ℤ θ))]
  rw [Ideal.mem_span_singleton]
  rfl

variable (θ)

theorem exponent_eq_sInf [NumberField K] :
    exponent θ = sInf {d : ℕ | 0 < d ∧ (d : 𝓞 K) ∈ conductor ℤ θ} := by
  rw [exponent, Int.absNorm_under_eq_sInf]

variable {θ} [NumberField K]

def ZModXQuotSpanEquivQuotSpan (hp : ¬ p ∣ exponent θ) :
    (ZMod p)[X] ⧸ span {map (Int.castRingHom (ZMod p)) (minpoly ℤ θ)} ≃+*
      𝓞 K ⧸ span {(p : 𝓞 K)} :=
  (quotientEquivAlgOfEq ℤ (by simp [Ideal.map_span, Polynomial.map_map])).toRingEquiv.trans
    ((quotientEquiv _ _ (mapEquiv (Int.quotientSpanNatEquivZMod p)) rfl).symm.trans
      ((quotMapEquivQuotQuotMap (not_dvd_exponent_iff.mp hp) θ.isIntegral).symm.trans
        (quotientEquivAlgOfEq ℤ (by simp [map_span])).toRingEquiv))

theorem ZModXQuotSpanEquivQuotSpan_mk_apply (hp : ¬ p ∣ exponent θ) (Q : ℤ[X]) :
  (ZModXQuotSpanEquivQuotSpan hp)
    (Ideal.Quotient.mk (span {map (Int.castRingHom (ZMod p)) (minpoly ℤ θ)})
      (map (Int.castRingHom (ZMod p)) Q)) = Ideal.Quotient.mk (span {(p : 𝓞 K)}) (aeval θ Q) := by
  unfold ZModXQuotSpanEquivQuotSpan
  simp only [AlgEquiv.toRingEquiv_eq_coe, algebraMap_int_eq, RingEquiv.trans_apply,
    AlgEquiv.coe_ringEquiv, quotientEquivAlgOfEq_mk, quotientEquiv_symm_apply, quotientMap_mk,
    RingHom.coe_coe, mapEquiv_symm_apply, Polynomial.map_map,
    Int.quotientSpanNatEquivZMod_comp_castRingHom_eq]
  exact congr_arg (quotientEquivAlgOfEq ℤ (by simp [map_span])) <|
    quotMapEquivQuotQuotMap_symm_apply (not_dvd_exponent_iff.mp hp) θ.isIntegral Q

def _root_.Polynomial.monicFactorsMod (a : ℕ) (A : ℤ[X]) : Set ((ZMod a)[X]) :=
  {Q : (ZMod a)[X] | Irreducible Q ∧ Q.Monic ∧ Q ∣ map (Int.castRingHom (ZMod a)) A}

theorem _root_.Polynomial.zero_notMem_monicFactorsMod (a : ℕ) [Fact (1 < a)] (A : ℤ[X]) :
    0 ∉ monicFactorsMod a A := by
  intro h
  rw [monicFactorsMod, Set.mem_setOf_eq] at h
  exact Polynomial.not_monic_zero h.2.1

variable (p) in
open UniqueFactorizationMonoid in
theorem _root_.Polynomial.monicFactorsMod_eq_normalizedFactors {A : ℤ[X]}
    (hA : map (Int.castRingHom (ZMod p)) A ≠ 0) :
    monicFactorsMod p A = {Q | Q ∈ normalizedFactors (map (Int.castRingHom (ZMod p)) A)} := by
  ext Q
  by_cases hQ : Q = 0
  · simp [hQ, zero_notMem_normalizedFactors, zero_notMem_monicFactorsMod]
  · rw [monicFactorsMod, Set.mem_setOf_eq, Set.mem_setOf_eq, mem_normalizedFactors_iff' hA,
      normalize_eq_self_iff_monic hQ]

def ZModXQuotSpanEquivQuotSpanPair (hp : ¬ p ∣ exponent θ)
    {Q : ℤ[X]} (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod p (minpoly ℤ θ)) :
    (ZMod p)[X] ⧸ span {Polynomial.map (Int.castRingHom (ZMod p)) Q} ≃+*
      𝓞 K ⧸ span {(p : 𝓞 K), (aeval θ) Q} :=
  have h_eq₁ : span {map (Int.castRingHom (ZMod p)) Q} =
      span {map (Int.castRingHom (ZMod p)) (minpoly ℤ θ)} ⊔
        span {map (Int.castRingHom (ZMod p)) Q} := by
    rw [← span_insert, span_pair_comm, span_pair_eq_span_singleton_of_dvd hQ.2.2]
  have h_eq₂ : span {↑p} ⊔ span {(aeval θ) Q} = span {↑p, (aeval θ) Q} := by
    rw [span_insert]
  ((Ideal.quotEquivOfEq h_eq₁).trans (DoubleQuot.quotQuotEquivQuotSup _ _).symm).trans <|
    (Ideal.quotientEquiv
      (Ideal.map (Ideal.Quotient.mk _) (span {(Polynomial.map (Int.castRingHom (ZMod p)) Q)}))
      (Ideal.map (Ideal.Quotient.mk _) (span {aeval θ Q})) (ZModXQuotSpanEquivQuotSpan hp) (by
        simp [Ideal.map_map, map_span, ZModXQuotSpanEquivQuotSpan_mk_apply])).trans <|
    (DoubleQuot.quotQuotEquivQuotSup _ _).trans (Ideal.quotEquivOfEq h_eq₂)

end RingOfIntegers

namespace NumberField

attribute [local instance] Int.ideal_span_isMaximal_of_prime Ideal.Quotient.field

-- change name
open scoped Classical in
def Ideal.primesOverSpanEquivMonicFactorsModAux (A : ℤ[X]) :
    {Q | Q ∈ normalizedFactors (map (Ideal.Quotient.mk (span {(p : ℤ)})) A)} ≃
    {Q | Q ∈ normalizedFactors (map (Int.castRingHom (ZMod p)) A)} :=
  (normalizedFactorsEquiv (e := (mapEquiv (Int.quotientSpanNatEquivZMod p)).toMulEquiv)
    (by simp) (map (Ideal.Quotient.mk (span {(p : ℤ)})) A)).trans
      (Equiv.setCongr (by simp [Polynomial.map_map]))

open scoped Classical in
theorem Ideal.primesOverSpanEquivMonicFactorsModAux_apply (A : ℤ[X]) {Q : (ℤ ⧸ span {(p : ℤ)})[X]}
    (hQ : Q ∈ {Q | Q ∈ normalizedFactors (map (Ideal.Quotient.mk (span {(p : ℤ)})) A)}) :
    (Ideal.primesOverSpanEquivMonicFactorsModAux A ⟨Q, hQ⟩ : (ZMod p)[X]) =
      Polynomial.map (Int.quotientSpanNatEquivZMod p) Q := rfl

theorem Ideal.primesOverSpanEquivMonicFactorsModAux_symm_apply (A : ℤ[X]) {Q : (ZMod p)[X]}
    (hQ : Q ∈ {Q | Q ∈ normalizedFactors (map (Int.castRingHom (ZMod p)) A)}) :
    ((Ideal.primesOverSpanEquivMonicFactorsModAux A).symm ⟨Q, hQ⟩ : (ℤ ⧸ span {(p : ℤ)})[X]) =
      Polynomial.map ((Int.quotientSpanNatEquivZMod p).symm) Q := rfl

-- change name
open scoped Classical in
theorem map_Int.quotientSpanNatEquivZMod_symm_mem_of_mem {A : ℤ[X]}
    (hA : Polynomial.map (Int.castRingHom (ZMod p)) A ≠ 0) {Q : (ZMod p)[X]}
    (hQ : Q ∈ monicFactorsMod p A) :
    Polynomial.map ((Int.quotientSpanNatEquivZMod p).symm) Q ∈
      {d | d ∈ normalizedFactors (map (Ideal.Quotient.mk (span {(p : ℤ)})) A)} := by
  rw [← Ideal.primesOverSpanEquivMonicFactorsModAux_symm_apply]
  refine Subtype.coe_prop ((Ideal.primesOverSpanEquivMonicFactorsModAux _).symm ⟨Q, ?_⟩)
  rwa [← monicFactorsMod_eq_normalizedFactors p hA]

variable [NumberField K]

open scoped Classical UniqueFactorizationMonoid in
def Ideal.primesOverSpanEquivMonicFactorsMod (hp : ¬ p ∣ exponent θ) :
    primesOver (span {(p : ℤ)}) (𝓞 K) ≃ monicFactorsMod p (minpoly ℤ θ) :=
  have h : span {(p : ℤ)} ≠ ⊥ := by simp [NeZero.ne p]
  ((Equiv.setCongr (primesOver_eq_normalizedFactors _ _ h)).trans
    (KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
    (Int.ideal_span_isMaximal_of_prime p) h (not_dvd_exponent_iff.mp hp) θ.isIntegral)).trans <|
      (Ideal.primesOverSpanEquivMonicFactorsModAux _).trans <|
        Equiv.setCongr (monicFactorsMod_eq_normalizedFactors p
            (map_monic_ne_zero (minpoly.monic θ.isIntegral))).symm

theorem Ideal.eq_primesOverSpanEquivMonicFactorsMod_symm_of_primesOver (hp : ¬ p ∣ exponent θ)
    {P : Ideal (𝓞 K)} (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K)) :
    ∃ (Q : (ZMod p)[X]), ∃ (hQ : Q ∈ monicFactorsMod p (minpoly ℤ θ)),
      P = (primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q, hQ⟩ :=
  ⟨primesOverSpanEquivMonicFactorsMod hp ⟨P, hP⟩, Subtype.coe_prop _, by simp⟩

theorem Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_aux (hp : ¬ p ∣ exponent θ)
    {Q : (ZMod p)[X]} (hQ : Q ∈ monicFactorsMod p (minpoly ℤ θ)) :
    ((Ideal.primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q, hQ⟩ : Ideal (𝓞 K)) =
      (KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
        inferInstance (by simp [NeZero.ne p]) (not_dvd_exponent_iff.mp hp) θ.isIntegral).symm
        ⟨Q.map (Int.quotientSpanNatEquivZMod p).symm,
          map_Int.quotientSpanNatEquivZMod_symm_mem_of_mem
            (map_monic_ne_zero (minpoly.monic θ.isIntegral)) hQ⟩ := rfl

theorem Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span
    (hp : ¬ p ∣ exponent θ) {Q : ℤ[X]}
    (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod p (minpoly ℤ θ)) :
    ((primesOverSpanEquivMonicFactorsMod hp).symm
      ⟨Q.map (Int.castRingHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) =
        span {(p : (𝓞 K)), aeval θ Q} := by
  simp only [primesOverSpanEquivMonicFactorsMod_symm_apply_aux, Polynomial.map_map,
    Int.quotientSpanNatEquivZMod_comp_castRingHom_eq]
  rw [KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk_symm_apply_eq_span]
  rw [span_union, span_eq, map_span, Set.image_singleton, map_natCast, ← span_insert]

theorem Ideal.liesOver_primesOverSpanEquivMonicFactorsMod_symm (hp : ¬ ↑p ∣ exponent θ) {Q : ℤ[X]}
    (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod p (minpoly ℤ θ)) :
    LiesOver (span {(p : (𝓞 K)), aeval θ Q}) (span {(p : ℤ)}) := by
  rw [← Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span hp hQ]
  exact ((primesOverSpanEquivMonicFactorsMod hp).symm ⟨_, hQ⟩).prop.2

theorem Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply (hp : ¬ p ∣ exponent θ)
    {Q : ℤ[X]} (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod p (minpoly ℤ θ)) :
    inertiaDeg (span {(p : ℤ)}) ((primesOverSpanEquivMonicFactorsMod hp).symm
      ⟨Q.map (Int.castRingHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) =
        natDegree (Q.map (Int.castRingHom (ZMod p))) := by
  -- Register this instance for `inertiaDeg_algebraMap` below
  have := liesOver_primesOverSpanEquivMonicFactorsMod_symm hp hQ
  have hQ' : Polynomial.map (Int.castRingHom (ZMod p)) Q ≠ 0 := by
    contrapose! hQ
    rw [hQ]
    exact zero_notMem_monicFactorsMod p (minpoly ℤ θ)
  rw [primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span, inertiaDeg_algebraMap,
    ← finrank_quotient_span_eq_natDegree hQ']
  refine Algebra.finrank_eq_of_equiv_equiv (Int.quotientSpanNatEquivZMod p) ?_ ?_
  · exact (ZModXQuotSpanEquivQuotSpanPair hp hQ).symm
  · ext; simp

theorem Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' (hp : ¬ p ∣ exponent θ)
    {Q : (ZMod p)[X]} (hQ : Q ∈ monicFactorsMod p (minpoly ℤ θ)) :
    inertiaDeg (span {(p : ℤ)})
      ((primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q, hQ⟩ : Ideal (𝓞 K)) =
        natDegree Q := by
  obtain ⟨S, rfl⟩ := (map_surjective _ (ZMod.ringHom_surjective (Int.castRingHom (ZMod p)))) Q
  rw [inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply]

theorem Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply (hp : ¬ p ∣ exponent θ)
    {Q : ℤ[X]} (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod p (minpoly ℤ θ)) :
    ramificationIdx (algebraMap ℤ (𝓞 K)) (span {(p : ℤ)})
      ((primesOverSpanEquivMonicFactorsMod hp).symm
        ⟨Q.map (Int.castRingHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) =
          multiplicity (Q.map (Int.castRingHom (ZMod p)))
            ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) := by
  rw [Ideal.ramificationIdx_eq_multiplicity (RingHom.injective_int _) (by simp [NeZero.ne p])
    inferInstance]
  · apply multiplicity_eq_of_emultiplicity_eq
    simp only [primesOverSpanEquivMonicFactorsMod_symm_apply_aux, Set.mem_setOf_eq, Set.coe_setOf,
      Polynomial.map_map, Int.quotientSpanNatEquivZMod_comp_castRingHom_eq]
    rw [← emultiplicity_map_eq (mapEquiv (Int.quotientSpanNatEquivZMod p).symm)]
    simp_rw [mapEquiv_apply, Polynomial.map_map, Int.quotientSpanNatEquivZMod_comp_castRingHom_eq]
    rw [KummerDedekind.emultiplicity_factors_map_eq_emultiplicity inferInstance
      (by simp [NeZero.ne p]) (not_dvd_exponent_iff.mp hp) θ.isIntegral]
    erw [Equiv.apply_symm_apply] -- Don't know how to easily remove this erw
  · apply Ideal.ne_bot_of_liesOver_of_ne_bot' (p := span {(p : ℤ)}) (by simp [NeZero.ne p])

theorem Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply' (hp : ¬ p ∣ exponent θ)
    {Q : (ZMod p)[X]} (hQ : Q ∈ monicFactorsMod p (minpoly ℤ θ)) :
    ramificationIdx (algebraMap ℤ (𝓞 K)) (span {(p : ℤ)})
      ((primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q, hQ⟩ : Ideal (𝓞 K)) =
        multiplicity Q ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) := by
  obtain ⟨S, rfl⟩ := (map_surjective _ (ZMod.ringHom_surjective (Int.castRingHom (ZMod p)))) Q
  rw [ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply]

end NumberField

section Application

end Application
