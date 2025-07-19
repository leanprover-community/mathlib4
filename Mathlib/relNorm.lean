import Mathlib





#exit

open Ideal Submodule Pointwise
attribute [local instance] FractionRing.liftAlgebra

variable (R : Type*) [CommRing R] {S : Type*} [CommRing S] [Algebra R S] [Module.Finite R S]
 [IsDomain R] [IsDomain S] [NoZeroSMulDivisors R S] [IsDedekindDomain S]

open nonZeroDivisors in
example : Function.Injective (map (algebraMap R S)) := by
  let g := IsScalarTower.toAlgHom R R S
  have := FractionalIdeal.map_injective (S := R⁰) g (FaithfulSMul.algebraMap_injective R S)
  intro I J h
  rw [← FractionalIdeal.coeIdeal_inj (K := FractionRing S)] at h






  sorry


#exit

variable (p : Ideal R) (Q Q' : p.primesOver S)

open Classical in
theorem lemm1 :
    Multiset.count Q (Multiset.map (fun σ : S ≃ₐ[R] S ↦ σ • Q) Finset.univ.val)
     = Fintype.card (MulAction.stabilizer (S ≃ₐ[R] S) Q) := by
  simp only [Multiset.count_map, ← Finset.filter_val, Finset.card_val, MulAction.mem_stabilizer_iff,
    eq_comm, Fintype.card_subtype]

variable [IsDedekindDomain R] [IsIntegrallyClosed R]

open Classical in
theorem lemm2 [p.IsMaximal] [IsGalois (FractionRing R) (FractionRing S)] (hp : p ≠ ⊥) :
    Fintype.card (MulAction.stabilizer (S ≃ₐ[R] S) Q) =
      p.ramificationIdxIn S * p.inertiaDegIn S := by
  have t₁ := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp S (FractionRing R)
    (FractionRing S)
  have := Ideal.isPretransitive_of_isGalois p (B := S) (FractionRing R) (FractionRing S)
  have t₂ := MulAction.index_stabilizer_of_transitive (S ≃ₐ[R] S) Q
  have t₃ := Subgroup.index_mul_card (MulAction.stabilizer (S ≃ₐ[R] S) Q)
  rw [← Nat.card_coe_set_eq, ← t₂, ← IsGalois.card_aut_eq_finrank] at t₁
  have : Fintype.card (FractionRing S ≃ₐ[FractionRing R] FractionRing S) =
    Fintype.card (S ≃ₐ[R] S) := by
    exact (Fintype.ofEquiv_card (galRestrict R (FractionRing R) (FractionRing S) S).toEquiv).symm
  rw [this] at t₁
  have t₄ := Subgroup.index_mul_card (MulAction.stabilizer (S ≃ₐ[R] S) Q)
  simp_rw [Nat.card_eq_fintype_card] at t₄
  rwa [← t₄, mul_right_inj', eq_comm] at t₁
  exact Subgroup.FiniteIndex.index_ne_zero

variable [IsIntegrallyClosed S]

open nonZeroDivisors

-- set_option maxHeartbeats 10000000 in
theorem lemm3 (P : Ideal S) [P.IsMaximal] (p : Ideal R) [p.IsMaximal] [P.LiesOver p]
    (hp : p ≠ ⊥) (hP : IsPrincipal P) [IsGalois (FractionRing R) (FractionRing S)] :
    relNorm R P = p ^ p.inertiaDeg P := by
  classical
  obtain ⟨a, ha⟩ := hP
  nth_rewrite 1 [ha]
  simp only [submodule_span_eq, relNorm_singleton]
  have : Function.Injective ((map (algebraMap R S))) := by
    let g := IsScalarTower.toAlgHom R R S
    have := FractionalIdeal.map_injective (S := R⁰) g ?_
    intro I J h
    rw [← FractionalIdeal.coeIdeal_inj (K := FractionRing S)] at h






    sorry
    unfold g
    have : Function.Injective (algebraMap R S) := FaithfulSMul.algebraMap_injective R S
    exact this

#exit
  apply this
  simp only [Ideal.map_span, Set.image_singleton]
  rw [Algebra.algebraMap_intNorm_of_isGalois]
  rw [← Ideal.prod_span_singleton]
  rw [← Ideal.mapHom_apply, map_pow]
  simp only [Ideal.mapHom_apply]
  have := Ideal.map_algebraMap_eq_finset_prod_pow S hp
  rw [this]
  have : ∀ P ∈ (p.primesOver S).toFinset,
    ramificationIdx (algebraMap R S) p P = p.ramificationIdxIn S := sorry
  simp_rw +contextual [this]
  rw [Finset.prod_pow, ← pow_mul,
    ← inertiaDegIn_eq_inertiaDeg p P (FractionRing R) (FractionRing S), ← Finset.prod_pow]
  lift P to (p.primesOver S) using sorry
  have : ∀ g : S ≃ₐ[R] S, Ideal.span {g a} = g • P := sorry
  simp_rw [this]
  rw [Finset.prod_eq_multiset_prod]
  rw [Finset.prod_multiset_count]
  refine Finset.prod_congr ?_ ?_
  · ext Q
    simp only [Multiset.mem_toFinset, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and,
      Set.mem_toFinset]
    constructor
    · rintro ⟨σ, rfl⟩
      exact (σ • P).prop
    · intro hQ
      lift Q to (p.primesOver S) using sorry
      simp_rw [← coe_smul_primesOver, Subtype.coe_inj]
      have := Ideal.isPretransitive_of_isGalois p (B := S) (FractionRing R) (FractionRing S)
      apply MulAction.exists_smul_eq
  · intro Q hQ
    congr
    simp_rw [← coe_smul_primesOver]
    simp only [Multiset.count_map, ← Finset.filter_val, Finset.card_val]

    have : Finset.card {g : S ≃ₐ[R] S | Q = ↑(g • P)} =
        Finset.card {g : S ≃ₐ[R] S | ↑(g • P) = P} := by
      have : Q.IsPrime := sorry
      have : Q.LiesOver p := sorry
      obtain ⟨σ, rfl⟩ := Ideal.exists_map_eq_of_isGalois p P Q (FractionRing R) (FractionRing S)
      have : Ideal.map σ ↑P = (σ • P : p.primesOver S) := rfl -- make a simp lemma?
      simp_rw [this, Subtype.coe_inj]
      have : ∀ g, σ • P = g • P ↔ (σ⁻¹ * g) • P = P  := by
        intro g
        rw [smul_eq_iff_eq_inv_smul, eq_comm, smul_smul]
      simp_rw [this]
      refine Finset.card_equiv ?_ ?_
      · exact Equiv.mulLeft σ⁻¹
      · intro g
        simp
    rw [this]
    lift Q to (p.primesOver S) using sorry
    have := lemm2 R p P hp
    convert this
    rw [← Fintype.card_subtype]
    rfl





















#exit

variable [Module.Free ℤ R] [Module.Free ℤ S] [Module.Finite ℤ S] [Module.Finite ℤ R]

open UniqueFactorizationMonoid

theorem lemm2 (I : Ideal S) :
    absNorm (relNorm R I) = absNorm I := by
  by_cases hI : I = ⊥
  · simp [hI]
  rw [← prod_normalizedFactors_eq_self hI]
  refine Multiset.prod_induction (fun I ↦ absNorm (relNorm R I) = absNorm I) _ ?_ ?_ ?_
  · intro _ _ hx hy
    rw [map_mul, map_mul, map_mul, hx, hy]
  · simp
  · intro Q hQ
    have hQ' : Q ≠ ⊥ := by
      contrapose! hQ
      simpa [hQ] using zero_notMem_normalizedFactors _
    rw [Ideal.mem_normalizedFactors_iff hI] at hQ
    have : Q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hQ' hQ.1
    let P := under R Q
    let p := absNorm (under ℤ P)
    have : Q.LiesOver P := by simp [liesOver_iff, P]
    have : P.LiesOver (span {(p : ℤ)}) := sorry
    have : Q.LiesOver (span {(p : ℤ)}) := sorry
    have : (span {(p : ℤ)}).IsMaximal := sorry
    have hp : Prime (p : ℤ) := sorry
    rw [lemm1 R Q P, map_pow, absNorm_eq_pow_inertiaDeg Q hp, absNorm_eq_pow_inertiaDeg P hp,
      inertiaDeg_algebra_tower (span {(p : ℤ)}) P Q, pow_mul]

theorem lemm3  (K L : Type*) [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra S L]
    [IsFractionRing S L] [Algebra K L] [Module.Finite K L] (I : Ideal R) :
    relNorm R (map (algebraMap R S) I) = I ^ Module.finrank K L := by
  by_cases hI : I = ⊥
  · rw [hI, Ideal.map_bot, relNorm_bot, ← Ideal.zero_eq_bot, zero_pow Module.finrank_pos.ne']
  rw [← prod_normalizedFactors_eq_self hI]
  refine Multiset.prod_induction
    (fun I ↦ relNorm R (map (algebraMap R S) I) = I ^ Module.finrank K L) _ ?_ ?_ ?_
  sorry
