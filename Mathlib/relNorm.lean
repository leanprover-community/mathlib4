import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.Factorization

section associates

theorem Associates.count_mk_factors_eq_multiset_count {α : Type*} [CancelCommMonoidWithZero α]
    [UniqueFactorizationMonoid α] [Subsingleton αˣ] [DecidableEq (Associates α)] [DecidableEq α]
    [(p : Associates α) → Decidable (Irreducible p)] {p a : α} (hp : Irreducible p) (ha : a ≠ 0) :
    (Associates.mk p).count (Associates.mk a).factors =
      Multiset.count p (UniqueFactorizationMonoid.normalizedFactors a) := by
  rw [Associates.factors_mk _ ha, Associates.count_some (Associates.irreducible_mk.mpr hp),
    ← Multiset.count_map_eq_count' _ _ Subtype.val_injective, Associates.map_subtype_coe_factors',
    UniqueFactorizationMonoid.factors_eq_normalizedFactors,
    ← Multiset.count_map_eq_count' _ _ (Associates.mk_injective (M := α))]

end associates

section primesOver

theorem Ideal.ne_bot_of_mem_primesOver {A B : Type*} [CommRing A] [Ring B] [Algebra A B]
    [NoZeroSMulDivisors A B] [Nontrivial B] {p : Ideal A}
    (hp : p ≠ ⊥) {P : Ideal B} (hP : P ∈ p.primesOver B) :
    P ≠ ⊥ := @ne_bot_of_liesOver_of_ne_bot _ _ _ _ _ _ _ _ hp P hP.2

end primesOver

section primesplitting

open Ideal

theorem Ideal.pow_eq_top_iff {R : Type*} [CommSemiring R] (I : Ideal R) (n : ℕ) :
    I ^ n = ⊤ ↔ I = ⊤ ∨ n = 0 := by
  constructor
  · intro h
    refine or_iff_not_imp_right.mpr fun hn ↦ ?_
    rw [eq_top_iff_one] at h ⊢
    exact pow_le_self hn h
  · intro h
    obtain h | h := h
    · simp [h, top_pow]
    · simp [h]

theorem Ideal.liesOver_iff_dvd_map {A : Type*} [CommSemiring A] {B : Type*} [CommRing B]
    [IsDedekindDomain B] [Algebra A B] (P : Ideal B) (p : Ideal A) (hP : P ≠ ⊤) [p.IsMaximal] :
    P.LiesOver p ↔ P ∣ Ideal.map (algebraMap A B) p := by
  rw [liesOver_iff, dvd_iff_le, under_def, map_le_iff_le_comap,
    IsCoatom.le_iff_eq (by rwa [← isMaximal_def]) (comap_ne_top _ hP), eq_comm]

noncomputable instance {A : Type*} [CommRing A] (p : Ideal A) [hpm : p.IsMaximal] (B : Type*)
    [CommRing B] [IsDedekindDomain B] [Algebra A B] [NoZeroSMulDivisors A B]
    [Algebra.IsIntegral A B] :
    Fintype (p.primesOver B) := Set.Finite.fintype (primesOver_finite p B)

variable {R S : Type*} [CommRing R] -- [IsDedekindDomain R]
  [CommRing S] -- [IsDedekindDomain S]
  [Algebra R S] [NoZeroSMulDivisors R S] -- [Algebra.IsIntegral R S]
  -- [Nontrivial S]

open Ideal

namespace IsDedekindDomain.HeightOneSpectrum

theorem maxPowDividing_ne_one_iff_mem_primesOver [IsDedekindDomain S] (v : HeightOneSpectrum S)
    (P : Ideal R) [P.IsMaximal] (hP : P ≠ 0) :
    maxPowDividing v (map (algebraMap R S) P) ≠ 1 ↔ v.asIdeal ∈ P.primesOver S := by
  classical
  simpa [maxPowDividing, one_eq_top, pow_eq_top_iff, IsPrime.ne_top',
      Associates.count_ne_zero_iff_dvd (map_ne_bot_of_ne_bot hP) (irreducible v), primesOver,
      liesOver_iff_dvd_map] using fun _ ↦ v.isPrime

theorem maxPowDividing_eq_pow_multiset_count [IsDedekindDomain S] [DecidableEq (Ideal S)]
    (v : HeightOneSpectrum S) {I : Ideal S} (hI : I ≠ 0) :
    maxPowDividing v I =
      v.asIdeal ^ Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors I) := by
  classical
  rw [maxPowDividing, Associates.count_mk_factors_eq_multiset_count (irreducible v) hI]

variable (S) in
def equiv :
    HeightOneSpectrum S ≃ {P : Ideal S // P.IsPrime ∧ P ≠ ⊥} where
  toFun v := ⟨v.asIdeal, v.isPrime, v.ne_bot⟩
  invFun P := ⟨P.val, P.prop.1, P.prop.2⟩

@[simp]
theorem equiv_apply (v : HeightOneSpectrum S) :
    equiv S v = v.asIdeal := rfl

-- variable (S) in
-- def ofPrimesOver {I : Ideal R} (hI : I ≠ ⊥) :
--     I.primesOver S → IsDedekindDomain.HeightOneSpectrum S :=
--   fun ⟨P, ⟨hP, _⟩⟩ ↦ ⟨P, hP, ne_bot_of_liesOver_of_ne_bot hI _⟩

-- @[simp]
-- theorem ofPrimesOver_asIdeal {I : Ideal R} (hI : I ≠ ⊥)
--     {P : Ideal S} (hP : P ∈ I.primesOver S) :
--     (ofPrimesOver S hI ⟨P, hP⟩).asIdeal = P := by
--   rw [ofPrimesOver]
--   · exact hP.1
--   · exact hP.2

-- theorem mem_ofPrimesOver_iff {I : Ideal R} (hI : I ≠ ⊥) {x : IsDedekindDomain.HeightOneSpectrum S} :
--     x ∈ Set.range (ofPrimesOver S hI) ↔ x.asIdeal ∈ I.primesOver S := by
--   simp [Set.mem_range, IsDedekindDomain.HeightOneSpectrum.ext_iff]


end IsDedekindDomain.HeightOneSpectrum

variable [IsDedekindDomain R] [IsDedekindDomain S] [Algebra.IsIntegral R S]

open IsDedekindDomain.HeightOneSpectrum

theorem Ideal.map_algebraMap_eq_finset_prod_pow (P : Ideal R) [P.IsMaximal] (hP : P ≠ 0) :
    Ideal.map (algebraMap R S) P =
      ∏ Q ∈ P.primesOver S, Q ^ P.ramificationIdx (algebraMap R S) Q := by
  classical
  have h₁ : map (algebraMap R S) P ≠ 0 := map_ne_bot_of_ne_bot hP
  rw [← finprod_heightOneSpectrum_factorization (I := P.map (algebraMap R S)) h₁]
  let T := {v : IsDedekindDomain.HeightOneSpectrum S | v.asIdeal ∣ P.map (algebraMap R S)}
  have : Fintype T := by
    refine Set.Finite.fintype ?_
    exact finite_factors h₁
  rw [finprod_eq_finset_prod_of_mulSupport_subset (s := T.toFinset)]
  · refine Finset.prod_nbij (fun v ↦ v.asIdeal) ?_ ?_ ?_ ?_
    · intro v hv
      rw [Set.mem_toFinset]
      refine ⟨v.isPrime, ?_⟩
      · rw [liesOver_iff_dvd_map _ _ IsPrime.ne_top']
        simp only [Set.mem_toFinset] at hv
        exact hv
    · apply Function.Injective.injOn
      intro _ _ _
      rwa [IsDedekindDomain.HeightOneSpectrum.ext_iff]
    · intro Q hQ
      simp at hQ
      simp only [Set.coe_toFinset, Set.mem_image]
      refine ⟨⟨Q, hQ.1, ne_bot_of_mem_primesOver hP hQ⟩, ?_, rfl⟩
      simp [T]
      have := hQ.2
      rwa [liesOver_iff_dvd_map] at this
      exact hQ.1.ne_top
    · intro v hv
      rw [maxPowDividing_eq_pow_multiset_count _ h₁,
        IsDedekindDomain.ramificationIdx_eq_factors_count h₁ v.isPrime v.ne_bot,
        UniqueFactorizationMonoid.factors_eq_normalizedFactors]
  · intro v hv
    simp [T]
    rw [Function.mem_mulSupport] at hv
    rw [maxPowDividing_ne_one_iff_mem_primesOver] at hv
    have := hv.2
    rwa [liesOver_iff_dvd_map] at this
    exact IsPrime.ne_top'
    exact hP

#exit

  let T : Finset (IsDedekindDomain.HeightOneSpectrum S) := by
    exact Finset.image (equiv S).symm (P.primesOver S).toFinset

    have hP : P ≠ ⊥ := sorry
    exact Finset.image (ofPrimesOver S hP) Finset.univ
  rw [finprod_eq_finset_prod_of_mulSupport_subset (s := T)] -- _ (s := (P.primesOver S).toFinset)]
  · let e : (P.primesOver S).toFinset ≃ T := by
      refine Equiv.ofBijective ?_ ⟨?_, ?_⟩
      · intro x

        have := over S h₁ x
        sorry
      · sorry
      · sorry
  · intro x hx
    rw [Fintype.coe_image_univ, mem_primesOverToIsDedekindDomainHeightOneSpectrum_iff]
    rw [primesOver, Set.mem_setOf_eq]
    refine ⟨x.isPrime, ?_⟩
    rw [liesOver_iff_dvd_map]
    rw [Function.mem_mulSupport] at hx
    rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing] at hx
    replace hx :
        (Associates.mk x.asIdeal).count (Associates.mk (map (algebraMap R S) P)).factors ≠ 0 := by
      rw [one_eq_top] at hx
      rw [ne_eq] at hx
      rw [pow_eq_top_iff, not_or] at hx
      exact hx.2
    rwa [Associates.count_ne_zero_iff_dvd] at hx
    · exact h₁
    exact IsDedekindDomain.HeightOneSpectrum.irreducible x
    exact IsPrime.ne_top'











end primesplitting

open Ideal Submodule

attribute [local instance] FractionRing.liftAlgebra

variable (R : Type*) [CommRing R] [IsDomain R] {S : Type*} [CommRing S] [IsDomain S]
  [IsIntegrallyClosed R] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S]
  [NoZeroSMulDivisors R S] [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
  [IsDedekindDomain R] [IsDedekindDomain S]

theorem lemm1 (Q : Ideal S) (hQ : IsMaximal Q) (P : Ideal R) [Q.LiesOver P]
    (h₁ : IsPrincipal Q) (h₂ : IsPrincipal P) [IsGalois (FractionRing R) (FractionRing S)] :
    relNorm R Q = P ^ P.inertiaDeg Q := by
  obtain ⟨a, rfl⟩ := h₁
  --obtain ⟨b, rfl⟩ := h₂
  simp only [submodule_span_eq, relNorm_singleton]
  have : Function.Injective (map (algebraMap R S)) := sorry
  apply this
  simp only [Ideal.map_span, Set.image_singleton]
  rw [Algebra.algebraMap_intNorm_of_isGalois]
  rw [← Ideal.prod_span_singleton]
  rw [← Ideal.mapHom_apply, map_pow]
  simp
  have := finprod_heightOneSpectrum_factorization (I := Ideal.map (algebraMap R S) P)





  sorry

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
