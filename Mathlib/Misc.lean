import Mathlib

section Ideal.map

theorem Ideal.map_algEquiv {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A]
    [Algebra R B] (f : A ≃ₐ[R] B) (I : Ideal A) :
    map f I = map (f : A ≃+* B) I := rfl

theorem Ideal.comap_algEquiv {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (f : B ≃ₐ[R] A) (I : Ideal A) :
    comap f I = comap (f : B ≃+* A) I := rfl

theorem Ideal.map_ringEquiv {R S : Type*} [Semiring R] [Semiring S] (f : R ≃+* S) (I : Ideal R) :
    map f I = map (f : R →+* S) I := rfl

theorem Ideal.comap_ringEquiv {R S : Type*} [Semiring R] [Semiring S] (f : S ≃+* R) (I : Ideal R) :
    comap f I = comap (f : S →+* R) I := rfl

theorem Ideal.map_eq_iff_eq_comap {R S : Type*} [Semiring R] [Semiring S] {I : Ideal R}
    {J : Ideal S} {f : R ≃+* S} :
    map f I = J ↔ I = comap f J :=
  ⟨fun h ↦ by rw [← h, ← map_symm, ← map_coe f.symm, ← map_coe f, map_of_equiv],
    fun h ↦ by
      rw [h, ← comap_symm, ← comap_coe f.symm, ← comap_coe f]
      exact (RingEquiv.symm_symm f) ▸ comap_of_equiv f.symm⟩

theorem Ideal.map_injective_of_equiv {R S : Type*} [Semiring R] [Semiring S] (f : R ≃+* S) :
    Function.Injective (map f) := by
  intro _ _ h
  rwa [map_eq_iff_eq_comap, comap_map_of_bijective _ f.bijective ] at h

theorem Ideal.comap_injective_of_equiv {R S : Type*} [Semiring R] [Semiring S] (f : R ≃+* S) :
    Function.Injective (comap f) := by
  intro _ _ h
  rw [← map_symm, ← map_symm] at h
  exact Ideal.map_injective_of_equiv f.symm h

end Ideal.map

noncomputable section AlgEquiv.restrictNormal'

variable {A C₁ C₂ : Type*} (K B L M₁ M₂ : Type*) [CommRing A] [CommRing C₁] [Algebra A C₁]
  [Field K]
  [Field M₁] [CommRing C₂] [Algebra A C₂] [Field M₂] [Algebra A K] [IsFractionRing A K]
  [Algebra K M₁] [Algebra K M₂] [Algebra A M₁] [Algebra A M₂]
  [IsScalarTower A K M₁] [Algebra C₁ M₁] [IsScalarTower A C₁ M₁] [IsIntegralClosure C₁ A M₁]
  [Algebra.IsAlgebraic K M₁]
  [IsScalarTower A K M₂] [Algebra C₂ M₂] [IsScalarTower A C₂ M₂] [IsIntegralClosure C₂ A M₂]
  [Algebra.IsAlgebraic K M₂]
  [CommRing B] [Field L]
  [Algebra B L] [Algebra A B] [Algebra K L] [Algebra L M₁] [Algebra L M₂]
  [IsScalarTower K L M₁] [IsScalarTower K L M₂]
  [Normal K L]
  [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] [IsIntegralClosure B A L]

/-- Docstring. -/
def AlgEquiv.restrictNormal' (σ : C₁ ≃ₐ[A] C₂) : B ≃ₐ[A] B :=
  galRestrict A K L B ((galLiftEquiv K M₁ M₂ σ).restrictNormal L)

variable [Algebra B C₁] [Algebra B C₂] [Algebra B M₁] [IsScalarTower B C₁ M₁] [Algebra B M₂]
  [IsScalarTower B C₂ M₂] [IsScalarTower B L M₁] [IsScalarTower B L M₂]

@[simp]
theorem AlgEquiv.restrictNormal'_commutes (σ : C₁ ≃ₐ[A] C₂) (x : B) :
    algebraMap B C₂ (σ.restrictNormal' K B L M₁ M₂ x) = σ (algebraMap B C₁ x) := by
  unfold restrictNormal'
  apply IsIntegralClosure.algebraMap_injective C₂ A M₂
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply B L M₂,
    algebraMap_galRestrict_apply, AlgEquiv.restrictNormal_commutes,
    ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply B C₁ M₁,
    galLiftEquiv_algebraMap_apply]

end AlgEquiv.restrictNormal'

noncomputable section AlgEquiv.liftNormal'

variable {A B₁ B₂ : Type*} (K L₁ L₂ C M) [CommRing A] [CommRing B₁] [Algebra A B₁] [Field K]
  [Field L₁]
  [Algebra A K] [IsFractionRing A K] [Algebra K L₁] [Algebra A L₁] [IsScalarTower A K L₁]
  [CommRing B₂] [Algebra A B₂] [Field L₂] [Algebra K L₂] [Algebra A L₂] [IsScalarTower A K L₂]
  [CommRing C] [Algebra.IsAlgebraic K L₁] [Algebra.IsAlgebraic K L₂]
  [Algebra B₁ L₁] [IsScalarTower A B₁ L₁] [IsIntegralClosure B₁ A L₁]
  [Algebra B₂ L₂] [IsScalarTower A B₂ L₂] [IsIntegralClosure B₂ A L₂]
  [Field M] [Algebra K M] [Algebra L₁ M] [Algebra L₂ M] [IsScalarTower K L₁ M]
  [IsScalarTower K L₂ M] [Normal K M] [Algebra A C] [Algebra A M] [IsScalarTower A K M]
  [Algebra C M] [IsScalarTower A C M] [IsIntegralClosure C A M]

/-- Docstring. -/
def AlgEquiv.liftNormal' (σ : B₁ ≃ₐ[A] B₂) : C ≃ₐ[A] C :=
  galRestrict A K M C ((galLiftEquiv K L₁ L₂ σ).liftNormal M)

variable [Algebra B₁ C] [Algebra B₂ C] [Algebra B₁ M] [IsScalarTower B₁ C M]
  [IsScalarTower B₁ L₁ M] [Algebra B₂ M] [IsScalarTower B₂ C M] [IsScalarTower B₂ L₂ M]

@[simp]
theorem AlgEquiv.liftNormal'_commutes (σ : B₁ ≃ₐ[A] B₂) (x : B₁) :
    (σ.liftNormal' K L₁ L₂ C M) (algebraMap B₁ C x) = algebraMap B₂ C (σ x) := by
  unfold liftNormal'
  apply IsIntegralClosure.algebraMap_injective C A M
  rw [algebraMap_galRestrict_apply, ← IsScalarTower.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply B₁ L₁ M,
    AlgEquiv.liftNormal_commutes, galLiftEquiv_algebraMap_apply, ← IsScalarTower.algebraMap_apply]

@[simp]
theorem AlgEquiv.restrict_liftNormal' [FaithfulSMul B₁ C] [Normal K L₁] (σ : B₁ ≃ₐ[A] B₁) :
    (σ.liftNormal' K L₁ L₁ C M).restrictNormal' K B₁ L₁ M M = σ := by
  ext
  apply FaithfulSMul.algebraMap_injective B₁ C
  rw [AlgEquiv.restrictNormal'_commutes, AlgEquiv.liftNormal'_commutes]

end AlgEquiv.liftNormal'

section primesOverGalois

variable {A C₁ C₂ : Type*} [CommRing A]
  [CommRing C₁] [IsIntegrallyClosed C₁] [Algebra A C₁] [Module.Finite A C₁]
  [CommRing C₂] [IsIntegrallyClosed C₂] [Algebra A C₂] [Module.Finite A C₂]
  {K L M₁ M₂ : Type*} [Field K] [Field M₁] [Field M₂] [Algebra A K] [IsFractionRing A K]
  [Algebra C₁ M₁] [IsFractionRing C₁ M₁] [Algebra K M₁] [Algebra A M₁] [IsScalarTower A C₁ M₁]
  [IsScalarTower A K M₁] [FiniteDimensional K M₁]
  [Algebra C₂ M₂] [IsFractionRing C₂ M₂] [Algebra K M₂] [Algebra A M₂] [IsScalarTower A C₂ M₂]
  [IsScalarTower A K M₂] [FiniteDimensional K M₂]
  {B : Type*} [CommRing B] [Field L] [Algebra B L] [Algebra A B]
  [Algebra K L] [Normal K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
  [IsIntegralClosure B A L]
  [Algebra B C₁] [Algebra L M₁] [IsScalarTower K L M₁] [Algebra B M₁] [IsScalarTower B L M₁]
  [IsScalarTower B C₁ M₁]
  [Algebra B C₂] [Algebra L M₂] [IsScalarTower K L M₂] [Algebra B M₂] [IsScalarTower B L M₂]
  [IsScalarTower B C₂ M₂]

variable (K L M₁ M₂) in
theorem Ideal.liesOver_iff_map_liesOver_map (P : Ideal B) (Q : Ideal C₁) (σ : C₁ ≃ₐ[A] C₂) :
    (Q.map σ).LiesOver (P.map (σ.restrictNormal' K B L M₁ M₂)) ↔ Q.LiesOver P := by
  rw [liesOver_iff, under_def, liesOver_iff, under_def, map_algEquiv, map_eq_iff_eq_comap,
    comap_ringEquiv, comap_comap, map_algEquiv, ← comap_symm, comap_ringEquiv, comap_comap]
  congr!
  ext
  simp [← AlgEquiv.symm_toRingEquiv]

variable (K L M₁ M₂) in
theorem Ideal.liesOver_iff_comap_liesOver_comap (P : Ideal B) (Q : Ideal C₁) (σ : C₁ ≃ₐ[A] C₁) :
    (Q.comap σ).LiesOver (P.comap (σ.restrictNormal' K B L M₁ M₁)) ↔ Q.LiesOver P := by
  rw [← liesOver_iff_map_liesOver_map K L M₁ M₁ _ _ σ, map_comap_eq_self_of_equiv,
    map_comap_eq_self_of_equiv]

variable [IsDomain A] [IsIntegrallyClosed A] [IsDomain B] [IsIntegrallyClosed B] [Module.Finite A B]
  [IsFractionRing B L] [FiniteDimensional K L] {C M : Type*} [CommRing C]
  [IsIntegrallyClosed C] [Field M] [Algebra C M] [IsFractionRing C M] [Algebra A C] [Algebra B C]
  [Algebra A M] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [IsScalarTower A K M]
  [IsScalarTower A C M] [IsIntegralClosure C A M] [Module.Finite A C] [Algebra B M]
  [IsScalarTower B C M] [FiniteDimensional K M] [IsScalarTower B L M]
  [FaithfulSMul B C]

open Ideal in

variable (K L M) in
theorem Ideal.ncard_primesOver_eq_ncard_primesOver (p : Ideal A) (P₁ P₂ : Ideal B) [P₁.IsPrime]
    [P₂.IsPrime] [P₁.LiesOver p] [P₂.LiesOver p] [IsGalois K L] [Normal K M] :
    (P₁.primesOver C).ncard = (P₂.primesOver C).ncard := by
  obtain ⟨σ, hσ⟩ := exists_map_eq_of_isGalois p P₁ P₂ K L
  let τ := σ.liftNormal' K L L C M
  refine Set.ncard_congr ?_ (fun Q ↦ ?_) ?_ ?_
  · exact fun Q _ ↦ Q.map (σ.liftNormal' K L L C M)
  · intro ⟨h₁, h₂⟩
    refine ⟨map_isPrime_of_equiv _, ?_⟩
    · rwa [← liesOver_iff_map_liesOver_map K L M M _ _ (σ.liftNormal' K L L C M),
        AlgEquiv.restrict_liftNormal', hσ] at h₂
  · exact fun _ _ _ _ h ↦ map_injective_of_equiv (AlgEquiv.liftNormal' K L L C M σ).toRingEquiv h
  · intro Q ⟨hQ₁, hQ₂⟩
    refine ⟨?_, ⟨?_, ?_⟩ , ?_⟩
    · exact comap (AlgEquiv.liftNormal' K L L C M σ) Q
    · exact comap_isPrime _ _
    · have := liesOver_iff_comap_liesOver_comap (σ := σ.liftNormal' K L L C M)
        (Q := Q) (P := P₂) (M₁ := M) (L := L) (K := K) ..
      rwa [← this, AlgEquiv.restrict_liftNormal', ← hσ, comap_map_of_bijective] at hQ₂
      exact σ.bijective
    · rw [map_comap_eq_self_of_equiv]









end primesOverGalois


section primesOverRestrict

@[simp]
theorem Ideal.primesOverFinset_bot (A : Type*) [CommRing A] (B : Type*) [CommRing B] [Algebra A B]
    [IsDedekindDomain B] :
    primesOverFinset (⊥ : Ideal A) B = ∅ := by
  classical
  rw [primesOverFinset, map_bot, UniqueFactorizationMonoid.factors_eq_normalizedFactors,
    ← zero_eq_bot, UniqueFactorizationMonoid.normalizedFactors_zero, Multiset.toFinset_eq_empty]

-- variable {A : Type*} [CommSemiring A] (p : Ideal A)

-- def Ideal.primesOverRestrict (B C : Type*) [CommSemiring B] [Semiring C] [Algebra A B]
--     [Algebra A C] [Algebra B C] [IsScalarTower A B C] :
--     p.primesOver C → p.primesOver B :=
--   fun P ↦
--     ⟨comap (algebraMap B C) P, ⟨IsPrime.under B P.1, under_liesOver_of_liesOver B P.1 p⟩⟩

-- @[simp]
-- theorem Ideal.primesOverRestrict_apply (B C : Type*) [CommSemiring B] [Semiring C] [Algebra A B]
--     [Algebra A C] [Algebra B C] [IsScalarTower A B C] (P : p.primesOver C) :
--     p.primesOverRestrict B C P = comap (algebraMap B C) P := rfl

-- theorem Ideal.primesOverRestrict_surjective (B C : Type*) [CommRing B] [CommRing C]
--     [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C] [FaithfulSMul B C]
--     [Algebra.IsIntegral B C] :
--     Function.Surjective (p.primesOverRestrict B C) := by
--   intro P
--   have hQ := exists_ideal_over_prime_of_isIntegral P.1 (⊥ : Ideal C)
--     (by simp [comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective B C)])
--   refine ⟨⟨hQ.choose, ⟨hQ.choose_spec.2.1, ?_⟩⟩, ?_⟩
--   · have : hQ.choose.LiesOver P.1 := (liesOver_iff _ _).mpr hQ.choose_spec.2.2.symm
--     exact LiesOver.trans hQ.choose P.1 p
--   · simpa [Subtype.ext_iff] using hQ.choose_spec.2.2

open Ideal in
theorem Ideal.mem_primesOver_of_mem_primesOver_and_liesOver {A : Type*} [CommSemiring A]
    (p : Ideal A) {B C : Type*} [CommSemiring B] [Semiring C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C] (P : Ideal B) (Q : Ideal C)
    [P.LiesOver p] :
    Q ∈ p.primesOver C ∧ Q.LiesOver P ↔ Q ∈ P.primesOver C :=
  ⟨fun ⟨⟨h₁, _⟩, h₃⟩ ↦ ⟨h₁, h₃⟩, fun ⟨h₁, h₂⟩ ↦ ⟨⟨h₁, LiesOver.trans Q P p⟩, h₂⟩⟩



-- theorem Ideal.primesOverRestrict_eq_iff (B C : Type*) [CommSemiring B] [Semiring C] [Algebra A B]
--     [Algebra A C] [Algebra B C] [IsScalarTower A B C] (P : p.primesOver B)
--     (Q : p.primesOver C) : p.primesOverRestrict B C Q = P ↔ Q.1.LiesOver P.1 := by
--   sorry

-- theorem Ideal.primesOverRestrict_eq_iff' (B C : Type*) [CommSemiring B] [Semiring C] [Algebra A B]
--     [Algebra A C] [Algebra B C] [IsScalarTower A B C] (P : Ideal B) [P.LiesOver p]
--     (Q : p.primesOver C) : p.primesOverRestrict B C Q = P ↔ Q.1 ∈ P.primesOver C := by
--   simp [primesOver, primesOver.isPrime, liesOver_iff, under_def, eq_comm]

theorem Ideal.card_primesOverFinset_eq_sum_card_primesOverFinset (A B C : Type*) [CommRing A]
    [CommRing B] [IsDedekindDomain B] [CommRing C] [IsDedekindDomain C] [Algebra A B]
    [NoZeroSMulDivisors A B] [Algebra A C] [NoZeroSMulDivisors A C] [Algebra B C]
    [NoZeroSMulDivisors B C] [IsScalarTower A B C] (p : Ideal A) [p.IsMaximal] :
    (primesOverFinset p C).card = ∑ P ∈ primesOverFinset p B, (primesOverFinset P C).card := by
  classical
  by_cases hp : p = ⊥
  · simp [hp]
  rw [Finset.card_eq_sum_ones, ← Finset.sum_fiberwise_of_maps_to (t := primesOverFinset p B)
    (g := fun x ↦ comap (algebraMap B C) x)]
  · refine Finset.sum_congr rfl fun P hP ↦ ?_
    rw [← Finset.card_eq_sum_ones]
    refine Finset.card_bijective (fun Q ↦ Q) Function.bijective_id fun Q ↦ ?_
    rw [mem_primesOverFinset_iff hp] at hP
    have hP' : P ≠ ⊥ := by
      have := hP.2
      apply ne_bot_of_liesOver_of_ne_bot hp
    have : P.IsMaximal := by
      have := hP.1
      exact Ring.DimensionLEOne.maximalOfPrime hP' this
    rw [Finset.mem_filter, mem_primesOverFinset_iff hp, mem_primesOverFinset_iff hP',
      ← under_def, eq_comm, ← liesOver_iff]
    have : P.LiesOver p := by
      exact hP.2
    exact mem_primesOver_of_mem_primesOver_and_liesOver p P Q
  · intro Q hQ
    rw [mem_primesOverFinset_iff hp] at hQ ⊢
    have := hQ.1
    have := hQ.2
    exact ⟨IsPrime.under B Q, under_liesOver_of_liesOver B Q p⟩

theorem Ideal.ncard_primesOver_eq_sum_ncard_primesOver (A B C : Type*) [CommRing A] [Nontrivial A]
    [CommRing B] [IsDedekindDomain B] [CommRing C] [IsDedekindDomain C] [Algebra A B]
    [NoZeroSMulDivisors A B] [Algebra A C] [NoZeroSMulDivisors A C] [Algebra B C]
    [NoZeroSMulDivisors B C] [IsScalarTower A B C] [Algebra.IsIntegral A C]
    [Algebra.IsIntegral A B] [Algebra.IsIntegral B C] (p : Ideal A) [p.IsMaximal] :
    (p.primesOver C).ncard = ∑ P : p.primesOver B, (P.1.primesOver C).ncard := by
  by_cases hp : p = ⊥
  · simp [hp, primesOver_bot]
    let _ : Unique (p.primesOver B) := by
      rw [hp, primesOver_bot]
      exact Set.uniqueSingleton ⊥
    rw [Fintype.sum_subsingleton _  ⟨⊥, Ideal.bot_prime, hp ▸ Ideal.bot_liesOver_bot A B⟩,
      primesOver_bot, Set.ncard_singleton]
  have (P : p.primesOver B) : P.1 ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp _
  simp_rw [← coe_primesOverFinset hp C, ← coe_primesOverFinset (this _) C, Set.ncard_coe_finset]
  rw [card_primesOverFinset_eq_sum_card_primesOverFinset A B C, Finset.sum_subtype]
  exact fun  _ ↦ by rw [mem_primesOverFinset_iff hp]

end primesOverRestrict


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
