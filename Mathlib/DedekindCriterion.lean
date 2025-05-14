import Mathlib
import Mathlib.Sandbox



noncomputable section
open NumberField Polynomial Ideal KummerDedekind

variable {K : Type*} [Field K] [NumberField K]

variable (θ : 𝓞 K)

def index : ℕ := absNorm (under ℤ (conductor ℤ θ))
-- AddSubgroup.index (Algebra.adjoin ℤ {θ}).toSubring.toAddSubgroup

variable (p : ℕ+) [h : Fact (Nat.Prime p)]

-- Thats basically normalizedFactors (map (Int.castRingHom (ZMod p)) A)
abbrev monicFactorsMod (A : ℤ[X]) : Set ((ZMod p)[X]) :=
  {Q : (ZMod p)[X] | Irreducible Q ∧ Q.Monic ∧ Q ∣ map (Int.castRingHom (ZMod p)) A}

attribute [local instance] Ideal.Quotient.field Int.ideal_span_isMaximal_of_prime

variable {p θ}

omit [NumberField K] in
theorem max_comap_conductor_span_eq_top (hp : ¬ ↑p ∣ index θ) :
    comap (algebraMap ℤ (𝓞 K)) (conductor ℤ θ) ⊔ span {(p : ℤ)} = ⊤ := by
  have h := Int.ideal_span_isMaximal_of_prime p
  rw [isMaximal_def] at h
  apply h.2
  rw [← under_def]
  rw [right_lt_sup]
  rw [← Ideal.dvd_iff_le]
  rw [Int.ideal_eq_span_absNorm_self (under ℤ (conductor ℤ θ))]
  rw [span_singleton_dvd_span_singleton_iff_dvd]
  rwa [Int.natCast_dvd_natCast]

omit [NumberField K] in
theorem not_dvd_index_iff :
    ¬ ↑p ∣ index θ ↔ comap (algebraMap ℤ (𝓞 K)) (conductor ℤ θ) ⊔ span {(p : ℤ)} = ⊤ := by
  rw [sup_comm, IsCoatom.sup_eq_top_iff, ← under_def, ← Ideal.dvd_iff_le,
    Int.ideal_eq_span_absNorm_self (under ℤ (conductor ℤ θ)),
    span_singleton_dvd_span_singleton_iff_dvd, Int.natCast_dvd_natCast, index]
  exact isMaximal_def.mp <| Int.ideal_span_isMaximal_of_prime p

variable (p) in
omit h in
theorem equiv₁_aux (A : Type*) [Semiring A] [Algebra ℤ A] :
    Ideal.map (algebraMap ℤ A) (span {↑↑p}) = span {(p : A)} := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

def equiv (hp : ¬ ↑p ∣ index θ) :
    (ZMod p)[X] ⧸ span {map (Int.castRingHom (ZMod p)) (minpoly ℤ θ)} ≃+*
      𝓞 K ⧸ span {(p : 𝓞 K)} :=
  have : Ideal.map ((mapEquiv (Int.quotientSpanNatEquivZMod p)))
      (span {Polynomial.map (Ideal.Quotient.mk (span {↑↑p})) (minpoly ℤ θ)}) =
        span {map (Int.castRingHom (ZMod p)) (minpoly ℤ θ)} := by
    simp_rw [map_span, mapEquiv_apply, Set.image_singleton, Polynomial.map_map]
    have : RingHom.comp (Int.quotientSpanNatEquivZMod ↑p) (Ideal.Quotient.mk (span {(p : ℤ)}))=
      Int.castRingHom (ZMod ↑p) := by ext; simp
    rw [this]
  (quotientEquivAlgOfEq ℤ sorry).toRingEquiv.trans
    ((quotientEquiv _ _ (mapEquiv (Int.quotientSpanNatEquivZMod p)) rfl).symm.trans
      ((quotMapEquivQuotQuotMap (not_dvd_index_iff.mp hp) θ.isIntegral).symm.trans
        (quotientEquivAlgOfEq ℤ (equiv₁_aux p (𝓞 K))).toRingEquiv))
--      (f₁.symm.trans f₂).symm)
  -- RingEquiv.trans (quotientEquivAlgOfEq ℤ sorry).toRingEquiv
  --   ((f₁.symm.trans f₂).trans
  --   (quotientEquiv _ _ (mapEquiv (Int.quotientSpanNatEquivZMod p)) rfl)).symm
  -- RingEquiv.trans (quotientEquivAlgOfEq ℤ sorry).toRingEquiv
  --   (((quotientEquivAlgOfEq ℤ (equiv₁_aux p (𝓞 K))).toRingEquiv.symm.trans
  --   (quotMapEquivQuotQuotMap (not_dvd_index_iff.mp hp) θ.isIntegral)).trans
  --   (quotientEquiv _ _ (mapEquiv (Int.quotientSpanNatEquivZMod p)) rfl)).symm
--  rw [← this, map_coe]

theorem equiv_apply (hp : ¬ ↑p ∣ index θ) (Q : ℤ[X]) :
    equiv hp (map (Int.castRingHom (ZMod p)) Q) = aeval θ Q := by
  unfold equiv
  dsimp only
  simp only [AlgEquiv.toRingEquiv_eq_coe, algebraMap_int_eq, RingEquiv.trans_apply,
    AlgEquiv.coe_ringEquiv, quotientEquivAlgOfEq_mk, quotientEquiv_symm_apply, quotientMap_mk,
    RingHom.coe_coe, mapEquiv_symm_apply]
  rw [Polynomial.map_map]
  have : RingHom.comp ((Int.quotientSpanNatEquivZMod p).symm) (Int.castRingHom (ZMod p)) =
    Ideal.Quotient.mk (span {(p : ℤ)}) := by ext; simp
  rw [this]

  have := quotMapEquivQuotQuotMap_symm_apply (not_dvd_index_iff.mp hp) θ.isIntegral Q
  erw [this]
  rfl









omit [NumberField K] in
def equiv₁ (hp : ¬ ↑p ∣ index θ) : (Algebra.adjoin ℤ {θ}) ⧸ span {(p : Algebra.adjoin ℤ {θ})}
    ≃+* 𝓞 K ⧸ span {(p : 𝓞 K)} :=
  (quotientEquivAlgOfEq ℤ (equiv₁_aux p (Algebra.adjoin ℤ {θ})).symm).toRingEquiv.trans
    ((quotAdjoinEquivQuotMap
      (not_dvd_index_iff.mp hp) (FaithfulSMul.algebraMap_injective _ _)).trans
        (quotientEquivAlgOfEq ℤ (equiv₁_aux p (𝓞 K))).toRingEquiv)

omit [NumberField K] in
@[simp]
theorem equiv₁_apply_mk (hp : ¬ ↑p ∣ index θ) (x : Algebra.adjoin ℤ {θ}) :
    equiv₁ hp x = x := rfl -- ((Ideal.Quotient.mk (span {(p : Algebra.adjoin ℤ {θ})})) x) =
--      (Ideal.Quotient.mk (span {(p : 𝓞 K)})) ↑x := rfl

variable (p θ) in
def equiv₂ : (ZMod p)[X] ⧸ span {map (Int.castRingHom (ZMod p)) (minpoly ℤ θ)}
    ≃+* (Algebra.adjoin ℤ {θ}) ⧸ span {(p : Algebra.adjoin ℤ {θ})} :=
  have : RingHom.comp ((Int.quotientSpanNatEquivZMod p).symm) (Int.castRingHom (ZMod p)) =
      Ideal.Quotient.mk (span {(p : ℤ)}) := by ext; simp
  ((quotientEquiv _ _ (mapEquiv (Int.quotientSpanNatEquivZMod p).symm) rfl).trans
    ((quotientEquivAlgOfEq ℤ (by simp [map_span, Polynomial.map_map, this])).toRingEquiv.trans
      ((AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (span {(p : ℤ)})
          (minpoly ℤ θ)).symm.trans
        (quotientEquivAlgOfEq ℤ (by simp [map_span])).toRingEquiv))).trans
          (quotientEquiv _ _ (minpoly.equivAdjoin θ.isIntegral).toRingEquiv.symm rfl).symm

@[simp]
theorem equiv₂_apply_mk (Q : ℤ[X]) :
    equiv₂ θ p (map (Int.castRingHom (ZMod p)) Q) =
      (⟨aeval θ Q, aeval_mem_adjoin_singleton ℤ θ⟩ : Algebra.adjoin ℤ {θ}) := by
  dsimp [equiv₂]
  have : RingHom.comp ((Int.quotientSpanNatEquivZMod p).symm) (Int.castRingHom (ZMod p)) =
      Ideal.Quotient.mk (span {(p : ℤ)}) := by ext; simp
  rw [Polynomial.map_map, this, AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot_symm_mk_mk,
    quotientEquivAlgOfEq_mk, quotientMap_mk, RingHom.coe_coe, minpoly.equivAdjoin_apply]
  have : AdjoinRoot.mk (minpoly ℤ θ) Q = QuotientAddGroup.mk Q := rfl
  rw [this, QuotientAddGroup.lift_mk]
  congr
  simp only [algebraMap_int_eq, AddMonoidHom.coe_coe, coe_eval₂RingHom]
  refine Subtype.ext (RingOfIntegers.ext ?_)
  simp only [IsFractionRing.coe_inj]
  change (algebraMap (Algebra.adjoin ℤ {θ}) (𝓞 K)) _ = _
  simp only [ringHom_eval₂_intCastRingHom]
  rfl

def equiv (hp : ¬ ↑p ∣ index θ) :
    (ZMod p)[X] ⧸ span {map (Int.castRingHom (ZMod p)) (minpoly ℤ θ)} ≃+* 𝓞 K ⧸ span {(p : 𝓞 K)} :=
  (equiv₂ θ p).trans (equiv₁ hp)

example (hp : ¬ ↑p ∣ index θ) (Q : ℤ[X]) :
    equiv hp (map (Int.castRingHom (ZMod p)) Q) = aeval θ Q := by
  simp [equiv]

















open UniqueFactorizationMonoid in
theorem Ideal.primesOverSpanEquivMonicFactorsMod_aux₁ :
    ((span {(p : ℤ)}).primesOver (𝓞 K)) =
      {J : Ideal (𝓞 K)| J ∈ normalizedFactors (map (algebraMap ℤ (𝓞 K)) (span {↑↑p}))} := by
  classical
  ext J
  rw [primesOver, Set.mem_setOf_eq, Set.mem_setOf_eq, mem_normalizedFactors_iff', liesOver_iff]
  · by_cases hJ : J = ⊥
    · simp_rw [hJ, under_bot, span_singleton_eq_bot, Int.natCast_eq_zero, PNat.ne_zero,
        and_false, ← Submodule.zero_eq_bot, not_irreducible_zero, false_and]
    · simp_rw [under_def, irreducible_iff_prime, prime_iff_isPrime hJ, normalize_eq, true_and,
        and_congr_right_iff]
      intro hJ'
      rw [dvd_iff_le, map_le_iff_le_comap, IsCoatom.le_iff_eq, eq_comm]
      · rw [← isMaximal_def]
        exact Int.ideal_span_isMaximal_of_prime p
      · exact IsPrime.ne_top'
  · exact map_ne_bot_of_ne_bot (by simp)

open UniqueFactorizationMonoid in
open scoped Classical in
def Ideal.primesOverSpanEquivMonicFactorsModAux :
    monicFactorsMod p (minpoly ℤ θ) ≃
      {d : (ℤ ⧸ span {(p : ℤ)})[X] //
        d ∈ normalizedFactors (Polynomial.map (Quotient.mk (span {(p : ℤ)})) (minpoly ℤ θ))} :=
  Equiv.subtypeEquiv (mapEquiv (Int.quotientSpanNatEquivZMod p)).symm fun f ↦ by
    rw [Set.mem_setOf_eq]
    by_cases hf : f = 0
    · simp_rw [hf, not_monic_zero, false_and, and_false, RingEquiv.coe_toEquiv, map_zero,
        UniqueFactorizationMonoid.zero_not_mem_normalizedFactors]
    · rw [mem_normalizedFactors_iff' (map_monic_ne_zero <| minpoly.monic θ.isIntegral),
        RingEquiv.coe_toEquiv, MulEquiv.irreducible_iff, RingEquiv_dvd_iff, RingEquiv.symm_symm,
        mapEquiv_symm_apply, mapEquiv_apply, Polynomial.map_map,
        normalize_eq_self_iff_monic (map_ne_zero hf), monic_map_iff]
      rfl

omit [NumberField K] in
theorem Ideal.primesOverSpanEquivMonicFactorsModAux_apply {Q : (ZMod p)[X]}
    (hQ : Q ∈ monicFactorsMod p (minpoly ℤ θ)) :
    primesOverSpanEquivMonicFactorsModAux ⟨Q, hQ⟩ =
      (mapEquiv (Int.quotientSpanNatEquivZMod p).symm) Q := rfl

open UniqueFactorizationMonoid in
def Ideal.primesOverSpanEquivMonicFactorsMod (hp : ¬ ↑p ∣ index θ) :
    primesOver (span {(p : ℤ)}) (𝓞 K) ≃ monicFactorsMod p (minpoly ℤ θ) := by
  classical
  refine (Equiv.trans ?_ (KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
    inferInstance (by simp) (max_comap_conductor_span_eq_top hp) θ.isIntegral)).trans ?_
  · exact Equiv.setCongr primesOverSpanEquivMonicFactorsMod_aux₁
  · exact Ideal.primesOverSpanEquivMonicFactorsModAux.symm

open UniqueFactorizationMonoid in
theorem Ideal.primesOverSpanEquivMonicFactorsMod_apply (hp : ¬ ↑p ∣ index θ) {P : Ideal (𝓞 K)}
    (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K)) :
    (primesOverSpanEquivMonicFactorsMod hp ⟨P, hP⟩ : (ZMod p) [X]) =
      (mapEquiv (Int.quotientSpanNatEquivZMod p))
        (KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
          inferInstance (by simp) (max_comap_conductor_span_eq_top hp) θ.isIntegral
          ⟨P, by rwa [← primesOverSpanEquivMonicFactorsMod_aux₁]⟩) := rfl

open UniqueFactorizationMonoid in
theorem Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply (hp : ¬ ↑p ∣ index θ) {Q : (ZMod p)[X]}
    (hQ : Q ∈ monicFactorsMod p (minpoly ℤ θ)) :
    ((primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q, hQ⟩ : Ideal (𝓞 K)) =
      (KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
        inferInstance (by simp?) (max_comap_conductor_span_eq_top hp) θ.isIntegral).symm
        ⟨Q.map (Int.quotientSpanNatEquivZMod p).symm, by
          rw [Set.mem_setOf, ← mapEquiv_apply, ← primesOverSpanEquivMonicFactorsModAux_apply hQ]
          exact Subtype.prop _⟩ := rfl

theorem Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span (hp : ¬ ↑p ∣ index θ) {Q : ℤ[X]}
    (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod p (minpoly ℤ θ)) :
    ((primesOverSpanEquivMonicFactorsMod hp).symm
      ⟨Q.map (Int.castRingHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) =
        span {(p : (𝓞 K)), aeval θ Q} := by
  have : RingHom.comp ((Int.quotientSpanNatEquivZMod p).symm) (Int.castRingHom (ZMod p)) =
      Ideal.Quotient.mk (span {(p : ℤ)}) := by
    ext; simp
  simp only [primesOverSpanEquivMonicFactorsMod_symm_apply, Polynomial.map_map, this]
  rw [KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk_symm_apply_eq_span]
  rw [span_union, span_eq, map_span, Set.image_singleton, map_natCast, ← span_insert]

theorem Ideal.liesOver_primesOverSpanEquivMonicFactorsMod_symm (hp : ¬ ↑p ∣ index θ) {Q : ℤ[X]}
    (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod p (minpoly ℤ θ)) :
    LiesOver (span {(p : (𝓞 K)), aeval θ Q}) (span {(p : ℤ)}) := sorry

example : ℤ[X] ⧸ span {C (p : ℤ)} ≃+* (ZMod ↑p)[X] := by
  let e := polynomialQuotientEquivQuotientPolynomial (span {(p : ℤ)})
  sorry
  -- let f := mapRingHom (Int.castRingHom (ZMod p))
  -- have hf : Function.Surjective f :=
  --   map_surjective (Int.castRingHom (ZMod p)) (ZMod.ringHom_surjective  _)
  -- have : span {C (p : ℤ)} = RingHom.ker f := by
  --   sorry
  -- rw [this]
  -- exact RingHom.quotientKerEquivOfSurjective hf

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem Ideal.finrank_eq_finrank_of_mem_liesOver (hp : ¬ ↑p ∣ index θ) {Q : ℤ[X]}
    (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod p (minpoly ℤ θ)) :
  have := liesOver_primesOverSpanEquivMonicFactorsMod_symm hp hQ
  Module.finrank (ℤ ⧸ span {(p : ℤ)}) (𝓞 K ⧸ span {(p : 𝓞 K), aeval θ Q}) =
    Module.finrank (ZMod p) ((ZMod p)[X] ⧸ span {Q.map (Int.castRingHom (ZMod p))}) := by
  have := liesOver_primesOverSpanEquivMonicFactorsMod_symm hp hQ
  have := Algebra.finrank_eq_of_equiv_equiv (R := ℤ ⧸ span {(p : ℤ)})
    (S :=  (𝓞 K ⧸ span {↑↑p, (aeval θ) Q})) (R' := ZMod p)
    (S' := ((ZMod p)[X] ⧸ span {Q.map (Int.castRingHom (ZMod p))}))
    (Int.quotientSpanNatEquivZMod p) ?_ ?_
  · exact this
  · rw [span_insert]
    refine RingEquiv.trans (DoubleQuot.quotQuotEquivQuotSup _ _).symm ?_
    refine RingEquiv.symm ?_
    let k := quotAdjoinEquivQuotMap (R := ℤ) (S := 𝓞 K) (x := θ) (I := span {(p : ℤ)}) sorry sorry
    rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_natCast,
      map_natCast] at k
    let s := (minpoly.equivAdjoin (R := ℤ) (x := θ) sorry).toRingEquiv.symm
    let t := AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (R := ℤ) (span {(p : ℤ)})
      (minpoly ℤ θ)
    rw [Ideal.map_span, Set.image_singleton, map_natCast] at t
    let J := (map (Quotient.mk (span {↑↑p})) (span {(aeval θ) Q}))
    let I := Ideal.map ↑k.symm J
    let A := quotientEquiv J _ k.symm rfl
    refine RingEquiv.trans ?_ (quotientEquiv _ _ k.symm rfl).symm
    let s' := quotientEquiv (span {↑↑p}) _ s rfl
    refine RingEquiv.trans ?_ (quotientEquiv _ _ s' rfl).symm










    let e := polynomialQuotientEquivQuotientPolynomial (span {(p : ℤ)})
    let f := mapEquiv (Int.quotientSpanNatEquivZMod p)
    let g := f.symm.trans e





    sorry
--      let h := RingHom.quotientKerEquivOfSurjective (f := map (Int.castRingHom (ZMod p)))


#exit
    let f : (ZMod p)[X] →+* 𝓞 K ⧸ span {(p : 𝓞 K)} := by
      convert RingHom.quotientKerEquivOfSurjective  ?_

      sorry
    let e := quotAdjoinEquivQuotMap (R := ℤ) (S := 𝓞 K) (x := θ) (I := span {(p : ℤ)}) sorry sorry
    rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_natCast,
      map_natCast] at e



    refine RingEquiv.symm ?_
    let f : (ZMod p)[X] →+* 𝓞 K ⧸ span {(p : 𝓞 K), aeval θ Q} := by
      let g := (Ideal.Quotient.mk (span {(p : 𝓞 K), aeval θ Q}))
      refine RingHom.comp g ?_


    have : span {Polynomial.map (Int.castRingHom (ZMod ↑p)) Q} = RingHom.ker f := sorry
    rw [this]
    refine RingHom.quotientKerEquivOfSurjective (f := f) ?_
    sorry
  · ext; simp

theorem Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply (hp : ¬ ↑p ∣ index θ)
    {Q : ℤ[X]} (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod p (minpoly ℤ θ)) :
    inertiaDeg (span {(p : ℤ)}) ((primesOverSpanEquivMonicFactorsMod hp).symm
      ⟨Q.map (Int.castRingHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) =
        natDegree (Q.map (Int.castRingHom (ZMod p))) := by
  have := liesOver_primesOverSpanEquivMonicFactorsMod_symm hp hQ
  rw [primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span]
  rw [inertiaDeg_algebraMap, finrank_eq_finrank_of_mem_liesOver hp hQ]
  rw [finrank_quotient_span_eq_natDegree]
  sorry


#exit

  --  inertiaDeg_algebraMap]

  let e := (DoubleQuot.quotQuotEquivQuotSupₐ ℤ
    (span {(p : 𝓞 K)}) (span {(aeval θ) Q})).toLinearEquiv
  have : AddCommMonoid ((𝓞 K ⧸ span {↑↑p}) ⧸
    map (Quotient.mkₐ ℤ (span {↑↑p})) (span {(aeval θ) Q})) := NonUnitalNonAssocSemiring.toAddCommMonoid
  have := @LinearEquiv.finrank_eq _ _ _ _ NonUnitalNonAssocSemiring.toAddCommMonoid _ _ _ e


  have :=
    LinearEquiv.finrank_eq (DoubleQuot.quotQuotEquivQuotSupₐ _ _ _).toLinearEquiv.symm
-- DoubleQuot.quotQuotEquivQuotSup
  sorry






#exit

     · refine Equiv.ofBijective ?_ ⟨?_, ?_⟩
        · exact fun f ↦ normalize (mapEquiv (Int.quotientSpanNatEquivZMod p).symm f)
        · sorry
        · sorry

#exit

      refine Equiv.ofBijective ?_ ?_
      · rintro ⟨f, hf⟩
        refine ⟨normalize (mapEquiv (Int.quotientSpanNatEquivZMod p).symm f), ?_⟩
        rw [Set.mem_setOf, UniqueFactorizationMonoid.mem_normalizedFactors_iff']
        refine ⟨?_, normalize_idem _, ?_⟩
        · rw [irreducible_normalize_iff]
          refine (MulEquiv.irreducible_iff _).mpr ?_
          sorry
        · rw [normalize_dvd_iff]
          rw [RingEquiv_dvd_iff]
          rw [mapEquiv_symm_apply, RingEquiv.symm_symm]
          rw [Polynomial.map_map]
          exact hf.2.2
        · apply Polynomial.map_monic_ne_zero
          refine minpoly.monic ?_
          exact RingOfIntegers.isIntegral θ
      ·
      -- let s := mapEquiv (Int.quotientSpanNatEquivZMod p)
      -- refine Equiv.subtypeEquiv s ?_
      -- intro x
      -- rw [Set.mem_setOf_eq]

#exit

      sorry
  · refine Ideal.Quotient.maximal_of_isField _ ?_
    refine MulEquiv.isField _ (Field.toIsField (ZMod p))
      (Int.quotientSpanNatEquivZMod p).toMulEquiv
  · aesop
  · sorry
  · exact RingOfIntegers.isIntegral α

end

#exit

def modp : ℤ →+* ZMod p := sorry -- ℤ ⧸ Ideal.span {(p : ℤ)} ≃+* ZMod p := Int.quotientSpanNatEquivZMod p

example : Ideal.inertiaDeg (Ideal.span {(p : ℤ)}) P = 1 := by
  let e := KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
    (S := 𝓞 K) (I := Ideal.span {(p : ℤ)}) (x := ζ) sorry sorry sorry sorry
