import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.FractionalIdeal.Extended
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Instances
import Mathlib.RingTheory.Localization.AtPrime.Extension
import Mathlib.FieldTheory.Minpoly.IsConjRoot

set_option linter.style.header false

@[simp]
theorem Ideal.bot_pow {R : Type*} [Semiring R] {n : ℕ} (hn : n ≠ 0) :
    (⊥ : Ideal R) ^ n = ⊥ := by
  rw [← Ideal.zero_eq_bot]
  sorry


attribute [local instance] FractionRing.liftAlgebra

open Algebra Ideal

-- theorem step11 {R S : Type*} [CommRing R] [IsDomain R] {S : Type*} [CommRing S] [IsDomain S]
--     [IsIntegrallyClosed R] [IsIntegrallyClosed S]
--     [Algebra R S] [Module.Finite R S] [NoZeroSMulDivisors R S]
--     [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
--     (x : S)
--     {E : Type*} [Field E] [Algebra (FractionRing R) E]
--     [IsAlgClosure (FractionRing R) E]
--     [Algebra (FractionRing S) E]
--     [IsScalarTower (FractionRing R) (FractionRing S) E]
--     [FaithfulSMul (FractionRing S) E] :
--     ∃ y : S, algebraMap R S (intNorm R S x) = y * x := by
--   classical
--   by_cases hx : x = 0
--   · exact ⟨1, by simp [hx]⟩
--   let K := FractionRing R
--   let L := FractionRing S
--   let u := (algebraMap R L (intNorm R S x)) * (algebraMap S L x)⁻¹
--   suffices IsIntegral S u by
--     have : u ∈ (algebraMap S L).range := by
--       rw [IsIntegrallyClosed.isIntegral_iff] at this
--       exact this
--     obtain ⟨y, hy⟩ := this
--     refine ⟨y, ?_⟩
--     apply FaithfulSMul.algebraMap_injective S L
--     rw [← IsScalarTower.algebraMap_apply, map_mul, hy]
--     unfold u
--     rw [inv_mul_cancel_right₀]
--     refine (map_ne_zero_iff (algebraMap S L) ?_).mpr ?_
--     · exact FaithfulSMul.algebraMap_injective S L
--     · exact hx
--   suffices IsIntegral R u by
--     exact IsIntegral.tower_top this
--   let _ : Algebra R E := by
--     refine RingHom.toAlgebra ?_
--     exact (algebraMap L E).comp (algebraMap R L)
--   have : IsScalarTower R L E := IsScalarTower.of_algebraMap_eq' rfl
--   let f := IsScalarTower.toAlgHom R L E
--   rw [← isIntegral_algHom_iff (f := f)]
--   · unfold f u
--     simp only [IsScalarTower.coe_toAlgHom', map_mul, map_inv₀]
--     rw [IsScalarTower.algebraMap_apply R K L]
--     rw [algebraMap_intNorm (A := R) (K := K) (B := S) (L := L)]
--     let _ : Algebra S E := by
--       refine RingHom.toAlgebra ?_
--       exact (algebraMap L E).comp (algebraMap S L)
--     have : IsScalarTower S L E := IsScalarTower.of_algebraMap_eq' rfl
--     let _ : Algebra R E := by
--       refine RingHom.toAlgebra ?_
--       exact (algebraMap S E).comp (algebraMap R S)
--     have : IsScalarTower R L E := IsScalarTower.of_algebraMap_eq' rfl
--     have : IsScalarTower R S E := sorry
--     rw [← IsScalarTower.algebraMap_apply]
--     have : IsAlgClosed E :=  IsAlgClosure.isAlgClosed (FractionRing R)
--     rw [norm_eq_prod_embeddings]
--     let τ := IsScalarTower.toAlgHom K L E
--     rw [←  Finset.univ.prod_erase_mul _ (Finset.mem_univ τ)]
--     unfold τ
--     simp
--     rw [mul_inv_cancel_right₀]
--     · apply IsIntegral.prod
--       intro σ _
--       have :  IsScalarTower R K E := sorry
--       change IsIntegral R ((σ.restrictScalars R) ((algebraMap S L) x))
--       rw [isIntegral_algHom_iff]
--       change IsIntegral R (IsScalarTower.toAlgHom R S L x)
--       rw [isIntegral_algHom_iff]
--       exact IsIntegral.isIntegral x
--       sorry -- exact FaithfulSMul.algebraMap_injective S E
--       sorry -- exact FaithfulSMul.algebraMap_injective S E
--     · refine (map_ne_zero_iff _ ?_).mpr ?_
--       · exact FaithfulSMul.algebraMap_injective L E
--       · refine (map_ne_zero_iff _ ?_).mpr ?_
--         · exact FaithfulSMul.algebraMap_injective S L
--         · exact hx
--   · exact FaithfulSMul.algebraMap_injective L E


theorem dvd_algebraMap_intNorm_self {R : Type*} [CommRing R] [IsDomain R] {S : Type*} [CommRing S]
    [IsDomain S] [IsIntegrallyClosed R] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S]
    [NoZeroSMulDivisors R S] [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    (x : S) :
    x ∣ algebraMap R S (intNorm R S x) := by
  classical
  by_cases hx : x = 0
  · exact ⟨1, by simp [hx]⟩
  let K := FractionRing R
  let L := FractionRing S
  let E := AlgebraicClosure L
  suffices IsIntegral R ((algebraMap S L x)⁻¹ * (algebraMap R L (intNorm R S x))) by
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp <| IsIntegral.tower_top (A := S) this
    refine ⟨y, ?_⟩
    apply FaithfulSMul.algebraMap_injective S L
    rw [← IsScalarTower.algebraMap_apply, map_mul, hy, mul_inv_cancel_left₀]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective S L)).mpr hx
  rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom R L E)
    (FaithfulSMul.algebraMap_injective L E), IsScalarTower.coe_toAlgHom', map_mul, map_inv₀,
    IsScalarTower.algebraMap_apply R K L, algebraMap_intNorm (L := L),
    ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, norm_eq_prod_embeddings,
    ←  Finset.univ.mul_prod_erase _ (Finset.mem_univ (IsScalarTower.toAlgHom K L E)),
    IsScalarTower.coe_toAlgHom', ← IsScalarTower.algebraMap_apply, inv_mul_cancel_left₀]
  · refine IsIntegral.prod _ fun σ _ ↦ ?_
    change IsIntegral R ((σ.restrictScalars R) (IsScalarTower.toAlgHom R S L x))
    rw [isIntegral_algHom_iff _ (RingHom.injective _),
      isIntegral_algHom_iff _ (FaithfulSMul.algebraMap_injective S L)]
    exact IsIntegral.isIntegral x
  · have := NoZeroSMulDivisors.trans_faithfulSMul S L E
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective S E)).mpr hx

theorem step01 {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [IsIntegrallyClosed R] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S]
    [NoZeroSMulDivisors R S] [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    {I : Ideal S} {x : S} (hx : x ∈ I) :
    algebraMap R S ((Algebra.intNorm R S) x) ∈ I :=
  Ideal.mem_of_dvd _ (dvd_algebraMap_intNorm_self x) hx

theorem Ideal.spanNorm_le_comap (R : Type*) [CommRing R] [IsDomain R] {S : Type*} [CommRing S]
    [IsDomain S] [IsIntegrallyClosed R] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S]
    [NoZeroSMulDivisors R S] [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    (I : Ideal S) : spanNorm R I ≤ comap (algebraMap R S) I := by
  rw [spanNorm, Ideal.map, Ideal.span_le, ← Submodule.span_le]
  apply Submodule.span_induction
  · rintro _ ⟨x, hx, rfl⟩
    rw [Ideal.mem_comap]
    exact Ideal.mem_of_dvd _ (dvd_algebraMap_intNorm_self x) hx
  · simp
  · intro _ _ _ _ hx hy
    exact Submodule.add_mem _ hx hy
  · intro _ _ _ hx
    exact Submodule.smul_mem _ _ hx



attribute [local instance] FractionRing.liftAlgebra

variable (R : Type*) [CommRing R] {S : Type*} [CommRing S] [Algebra R S] [Module.Finite R S]
 [IsDomain R] [IsDomain S] [FaithfulSMul R S] [IsDedekindDomain S]

variable (p : Ideal R) (Q Q' : p.primesOver S)

variable [IsDedekindDomain R] [IsIntegrallyClosed R]

variable {R p} in
open Classical in
theorem Ideal.card_stabilizer_eq_ramificationIdxIn_mul_inertiaDegIn [p.IsMaximal]
    [IsGalois (FractionRing R) (FractionRing S)] (hp : p ≠ ⊥) :
    Fintype.card (MulAction.stabilizer (S ≃ₐ[R] S) Q) =
      p.ramificationIdxIn S * p.inertiaDegIn S := by
  have := Ideal.isPretransitive_of_isGalois p (B := S) (FractionRing R) (FractionRing S)
  rw [← mul_right_inj' (primesOver_ncard_ne_zero p S),
    ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp S (FractionRing R) (FractionRing S),
    ← Nat.card_coe_set_eq, ← MulAction.index_stabilizer_of_transitive (S ≃ₐ[R] S) Q,
    ← Nat.card_eq_fintype_card, Subgroup.index_mul_card, Nat.card_eq_fintype_card,
    ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card]
  exact Fintype.ofEquiv_card (galRestrict R (FractionRing R) (FractionRing S) S).toEquiv

variable [IsIntegrallyClosed S]

open nonZeroDivisors Submodule Pointwise

theorem relNorm_eq_pow_of_isMaximal'' [IsGalois (FractionRing R) (FractionRing S)] (P : Ideal S)
    [P.IsMaximal] {p : Ideal R} [p.IsMaximal] (hp : p ≠ ⊥) [P.LiesOver p] (hP : IsPrincipal P) :
    relNorm R P = p ^ p.inertiaDeg P := by
  classical
  have hPp : P ∈ p.primesOver S := ⟨IsMaximal.isPrime' _, inferInstance⟩
  refine (map_algebraMap_injective R S).eq_iff.mp ?_
  rw [show Ideal.map (algebraMap R S) ((relNorm R) P) = ∏ g : S ≃ₐ[R] S, g • P by
    obtain ⟨a, ha⟩ := hP
    simp [relNorm_singleton, Set.image_singleton, Algebra.algebraMap_intNorm_of_isGalois,
      ← Ideal.prod_span_singleton, ha, pointwise_smul_def, Ideal.map_span]]
  rw [Ideal.map_pow, map_algebraMap_eq_finset_prod_pow S hp, Finset.prod_eq_multiset_prod,
    Finset.prod_multiset_count, ← inertiaDegIn_eq_inertiaDeg p P (FractionRing R) (FractionRing S),
    ← Finset.prod_pow]
  have {Q} (hQ : Q ∈ (p.primesOver S).toFinset) :
      ramificationIdx (algebraMap R S) p Q = p.ramificationIdxIn S := by
    lift Q to (p.primesOver S) using Set.mem_toFinset.mp hQ
    rw [ramificationIdxIn_eq_ramificationIdx p Q (FractionRing R) (FractionRing S)]
  simp_rw +contextual [this, ← pow_mul]
  lift P to (p.primesOver S) using hPp
  refine Finset.prod_congr (Finset.ext fun Q ↦ ?_) fun Q hQ ↦ ?_
  · simp only [Multiset.mem_toFinset, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and,
      Set.mem_toFinset]
    refine ⟨?_, fun hQ ↦ ?_⟩
    · rintro ⟨σ, rfl⟩
      exact (σ • P).prop
    · lift Q to (p.primesOver S) using hQ
      simp_rw [← coe_smul_primesOver, Subtype.coe_inj]
      have := Ideal.isPretransitive_of_isGalois p (B := S) (FractionRing R) (FractionRing S)
      exact MulAction.exists_smul_eq ..
  · lift Q to (p.primesOver S) using Set.mem_toFinset.mp hQ
    have : Fintype.card {g : S ≃ₐ[R] S // Q.val = g • P.val} =
        Fintype.card (MulAction.stabilizer (S ≃ₐ[R] S) Q) := by
      simp_rw [← coe_smul_primesOver, Subtype.coe_inj]
      have := Ideal.isPretransitive_of_isGalois p (B := S) (FractionRing R) (FractionRing S)
      obtain ⟨σ, rfl⟩ := MulAction.exists_smul_eq (S ≃ₐ[R] S) Q P
      rw [Fintype.subtype_card, Fintype.subtype_card _ (fun _ ↦ by simp)]
      refine Finset.card_equiv (Equiv.mulRight σ) fun _ ↦ ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_mulRight,
        MulAction.mem_stabilizer_iff, eq_comm, smul_smul]
    rw [Multiset.count_map, ← Finset.filter_val, Finset.card_val, ← Fintype.card_subtype, this,
      ← card_stabilizer_eq_ramificationIdxIn_mul_inertiaDegIn Q hp]

attribute [local instance] Ideal.Quotient.field

attribute [-instance] instAlgebraAtPrimeFractionRing

open IsLocalization.AtPrime in
theorem relNorm_eq_pow_of_isMaximal' [IsGalois (FractionRing R) (FractionRing S)] (P : Ideal S)
    [P.IsMaximal] (p : Ideal R) [p.IsMaximal] [hPp : P.LiesOver p] :
    relNorm R P = p ^ p.inertiaDeg P := by
  by_cases hp : p = ⊥
  · have h : p.inertiaDeg P ≠ 0 := (Ideal.inertiaDeg_pos p P).ne'
    rw [hp] at hPp
    rw [liesOver_iff, under_def, eq_comm] at hPp
    rw [eq_bot_iff] at hPp
    have := (Ideal.spanNorm_le_comap R P).trans hPp
    rw [le_bot_iff] at this
    rw [spanNorm_eq_bot_iff] at this
    rw [hp, this, relNorm_bot, ← Ideal.zero_eq_bot, zero_pow]
    rwa [hp, this] at h
  refine eq_of_localization_maximal (fun q hq ↦ ?_)
  let Rₚ := Localization.AtPrime q
  let Mₛ := Algebra.algebraMapSubmonoid S q.primeCompl
  let Sₚ := Localization Mₛ
  by_cases hq : p = q
  · subst hq
    have : NeZero p := ⟨hp⟩
    have hP : P ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp P
    have : IsScalarTower R Sₚ (FractionRing S) := .trans_right R S Sₚ (FractionRing S)
    have : NoZeroSMulDivisors S Sₚ := noZeroSMulDivisors_localization p Sₚ
    have : IsGalois (FractionRing Rₚ) (FractionRing Sₚ) := by
      apply IsGalois.of_equiv_equiv (F := FractionRing R) (E := FractionRing S)
        (f := ((FractionRing.algEquiv Rₚ (FractionRing R)).restrictScalars R).symm)
        (g := ((FractionRing.algEquiv Sₚ (FractionRing S)).restrictScalars R).symm)
      ext x
      obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective R⁰ x
      simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
        IsFractionRing.mk'_eq_div, map_div₀, ← IsScalarTower.algebraMap_apply,
        AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
    have : (Ideal.map (algebraMap S Sₚ) P).IsMaximal := by
      apply Ring.DimensionLEOne.maximalOfPrime
      · exact Ideal.map_ne_bot_of_ne_bot hP
      · exact isPrime_algebraMap_of_liesOver p P Sₚ
    have : (Ideal.map (algebraMap R Rₚ) p).IsMaximal := map_isMaximal p Rₚ
    have : (Ideal.map (algebraMap S Sₚ) P).LiesOver (IsLocalRing.maximalIdeal Rₚ) :=
      liesOver_map_of_liesOver p P Rₚ Sₚ
    have : (Ideal.map (algebraMap S Sₚ) P).LiesOver (Ideal.map (algebraMap R Rₚ) p) := by
      rwa [map_eq_maximalIdeal p Rₚ]
    rw [← spanNorm_eq, ← spanIntNorm_localization (R := R) (Sₘ := Sₚ) (M := p.primeCompl) _
      (primeCompl_le_nonZeroDivisors p), spanNorm_eq, Ideal.map_pow]
    rw [relNorm_eq_pow_of_isMaximal'' _ (Ideal.map (algebraMap S Sₚ) P)
      (p := Ideal.map (algebraMap R Rₚ) p)]
    · rw [Localization.AtPrime.map_eq_maximalIdeal]
      rw [IsLocalization.AtPrime.inertiaDeg_map_eq_inertiaDeg p]
    · exact map_ne_bot_of_ne_bot hp
    exact IsPrincipalIdealRing.principal _
    -- case q ≠ p
  · let Mₛ := Algebra.algebraMapSubmonoid S q.primeCompl
    let Sₚ := Localization Mₛ
    obtain ⟨x, hx₁, hx₂⟩ : ∃ x ∈ p, x ∈ q.primeCompl :=
      SetLike.not_le_iff_exists.mp <|
        (Ring.DimensionLeOne.prime_le_prime_iff_eq hp).not.mpr <| ne_comm.mp (Ne.symm hq)
    have h₁ : Ideal.map (algebraMap R Rₚ) p = ⊤ :=
      eq_top_of_isUnit_mem _ (mem_map_of_mem _ hx₁) <|
        (IsLocalization.AtPrime.isUnit_to_map_iff _ _ _).mpr hx₂
    have h₂ : Ideal.map (algebraMap S Sₚ) P = ⊤ := by
      have : algebraMap R S x ∈ Mₛ := Algebra.mem_algebraMapSubmonoid_of_mem ⟨_, hx₂⟩
      refine eq_top_of_isUnit_mem _ ?_ <| IsLocalization.map_units _ ⟨_, this⟩
      rw [← IsScalarTower.algebraMap_apply]
      exact mem_map_of_mem _ (by simpa [← Ideal.mem_of_liesOver P p])
    rw [← spanNorm_eq, ← spanIntNorm_localization R (Sₘ := Sₚ) _ _
      (primeCompl_le_nonZeroDivisors q), spanNorm_eq, Ideal.map_pow, h₁, h₂, relNorm_top, top_pow]

theorem relNorm_eq_pow_of_isMaximal [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    (P : Ideal S) [P.IsMaximal] (p : Ideal R) [p.IsMaximal] [P.LiesOver p] :
    relNorm R P = p ^ p.inertiaDeg P := by
  let K := FractionRing R
  let L := FractionRing S
  let E := IntermediateField.normalClosure K L (AlgebraicClosure L)
  let _ : Algebra K E := sorry
  let _ : Algebra L E := sorry
  let _ : Algebra S E := sorry
  have : IsGalois K E := sorry
  have : IsGalois L E := sorry
  let T := integralClosure S E
  let _ : Algebra R T := sorry
  have : Module.Finite S T := sorry
  have : Module.Finite R T := sorry
  have : FaithfulSMul S T := sorry
  have : FaithfulSMul R T := sorry
  have : IsDedekindDomain T := sorry
  have : IsScalarTower R S T := sorry
  have : IsGalois (FractionRing S) (FractionRing T) := sorry
  have : IsGalois (FractionRing R) (FractionRing T) := sorry
  have : ∃ Q : Ideal T, Q ∈ primesOver P T := sorry
  obtain ⟨Q, hQ⟩ := this
  have hQ₁ : Q.IsMaximal := sorry
  have hQ₂ : Q.LiesOver P := sorry
  have t₁ := relNorm_eq_pow_of_isMaximal' S Q P
  have hQ₃ : Q.LiesOver p := sorry
  have t₂ := relNorm_eq_pow_of_isMaximal' R Q p
  rw [← relNorm_relNorm R S, t₁, map_pow] at t₂
  sorry


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
