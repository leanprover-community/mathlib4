import Mathlib.Algebra.Order.Star.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.FractionalIdeal.Extended
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.DedekindDomain.Instances
import Mathlib.RingTheory.Trace.Quotient

open Ideal Submodule Pointwise

-- theorem IsLocalization.AtPrime.map_ideal_eq_top {R : Type*} [CommSemiring R] (S : Type*)
--     [CommSemiring S] [Algebra R S] (I : Ideal R) [hI : I.IsPrime] [IsLocalization.AtPrime S I]
--     {J : Ideal R} (hJ : ¬ J ≤ I) :
--     Ideal.map (algebraMap R S) J = ⊤ := by
--   obtain ⟨x, hx₁, hx₂⟩ := SetLike.not_le_iff_exists.mp hJ
--   exact eq_top_of_isUnit_mem _ (mem_map_of_mem _ hx₁) <| (isUnit_to_map_iff S I _).mpr hx₂

@[simp]
theorem Ideal.mem_primeCompl_iff {α : Type*} [Semiring α] {P : Ideal α} [hp : P.IsPrime] {x : α} :
    x ∈ P.primeCompl ↔ x ∉ P := Iff.rfl

theorem Ideal.comap_map_eq_of_isMaximal (A : Type*) [CommSemiring A] (B : Type*)
    [Semiring B] [Algebra A B] {P : Ideal A} [hP' : P.IsMaximal]
    (hP : Ideal.map (algebraMap A B) P ≠ ⊤) :
    Ideal.comap (algebraMap A B) (Ideal.map (algebraMap A B) P) = P :=
  (IsCoatom.le_iff_eq hP'.out (comap_ne_top _ hP)).mp <| Ideal.le_comap_map

set_option maxHeartbeats 1000000 in
theorem Ideal.under_map (A : Type*) [CommSemiring A] (B : Type*) [CommSemiring B] [Algebra A B]
    (P : Ideal B) (C D : Type*) [CommSemiring C] [Semiring D] [Algebra A C] [Algebra C D]
    [Algebra A D] [Algebra B D] [IsScalarTower A C D] [IsScalarTower A B D]
    (h₁ : (map (algebraMap A C) (under A P)).IsMaximal)
    (h₂ : map (algebraMap B D) P ≠ ⊤) :
    under C (map (algebraMap B D) P) = map (algebraMap A C) (under A P) := by
  rw [← IsCoatom.le_iff_eq]
  simp [under_def]
  · apply Ideal.le_comap_of_map_le
    rw [map_map]
    rw [← IsScalarTower.algebraMap_eq]
    rw [map_le_iff_le_comap]
    rw [IsScalarTower.algebraMap_eq A B D]
    rw [← Ideal.comap_comap]
    apply Ideal.comap_mono
    exact le_comap_map
  exact isMaximal_def.mp h₁
  refine comap_ne_top (algebraMap C D) h₂



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
    ← IsGalois.card_aut_eq_finrank]
  exact Fintype.ofEquiv_card (galRestrict R (FractionRing R) (FractionRing S) S).toEquiv

variable [IsIntegrallyClosed S]

open nonZeroDivisors

theorem relNorm_eq_pow_of_isMaximal_aux₁ [IsGalois (FractionRing R) (FractionRing S)] (P : Ideal S)
    [P.IsMaximal] {p : Ideal R} [p.IsMaximal] [P.LiesOver p] (hp : p ≠ ⊥) (hP : IsPrincipal P) :
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

set_option maxHeartbeats 1000000 in
theorem relNorm_eq_pow_of_isMaximal_aux₂ [IsGalois (FractionRing R) (FractionRing S)] (P : Ideal S)
    [P.IsMaximal] (p : Ideal R) [p.IsMaximal] [hP₁ : P.LiesOver p]
    [Algebra.IsSeparable (FractionRing R)
    (FractionRing S)] (hp : p ≠ ⊥) :
    relNorm R P = p ^ p.inertiaDeg P := by
  refine eq_of_localization_maximal (fun q hq ↦ ?_)
  let Rₚ := Localization.AtPrime q
  let Mₛ := Algebra.algebraMapSubmonoid S q.primeCompl
  let Sₚ := Localization Mₛ
  by_cases hq : p = q
  · subst hq
    have : NeZero p := ⟨hp⟩
    have hP : P ≠ 0 := by
      apply Ideal.ne_bot_of_liesOver_of_ne_bot hp _
    let _ : Algebra (FractionRing Rₚ) (FractionRing Sₚ) :=
      FractionRing.liftAlgebra Rₚ (FractionRing Sₚ)
    have : IsDomain Sₚ := by exact
      IsLocalization.instIsDomainLocalizationAlgebraMapSubmonoidPrimeComplOfFaithfulSMul S
    have : NoZeroSMulDivisors S Sₚ := by
      rw [NoZeroSMulDivisors.iff_algebraMap_injective]
      rw [IsLocalization.injective_iff_isRegular Mₛ]
      rintro ⟨x, hx⟩
      rw [isRegular_iff_ne_zero']
      refine ne_of_mem_of_not_mem hx ?_
      unfold Mₛ Algebra.algebraMapSubmonoid
      simp only [Submonoid.mem_map, mem_primeCompl_iff, FaithfulSMul.algebraMap_eq_zero_iff,
        exists_eq_right, Submodule.zero_mem, not_true_eq_false, not_false_eq_true]
    have : IsGalois (FractionRing Rₚ) (FractionRing Sₚ) := by
      refine { to_isSeparable := inferInstance, to_normal := ?_ }


      sorry
    have h₁ : (Ideal.map (algebraMap R Rₚ) p).IsMaximal := by
      rw [Localization.AtPrime.map_eq_maximalIdeal]
      exact IsLocalRing.maximalIdeal.isMaximal Rₚ
    have h₂ : (Ideal.map (algebraMap S Sₚ) P).IsMaximal := by
      have : (Ideal.map (algebraMap S Sₚ) P).IsPrime := by
        refine IsLocalization.isPrime_of_isPrime_disjoint Mₛ _ _ ?_ ?_
        · exact IsMaximal.isPrime inferInstance
        · refine Set.disjoint_left.mpr fun x hx ↦ ?_
          unfold Mₛ at hx
          simp only [Algebra.algebraMapSubmonoid, Submonoid.coe_map, Set.mem_image, SetLike.mem_coe,
            mem_primeCompl_iff] at hx
          obtain ⟨a, ha, rfl⟩ := hx
          rw [liesOver_iff, under_def] at hP₁
          rw [hP₁] at ha
          contrapose! ha
          exact ha
      apply Ring.DimensionLEOne.maximalOfPrime
      exact map_ne_bot_of_ne_bot hP
      exact this
    have : (Ideal.map (algebraMap S Sₚ) P).LiesOver (Ideal.map (algebraMap R Rₚ) p) := by
      rw [liesOver_iff] at hP₁
      subst hP₁
      rw [liesOver_iff, eq_comm]
      apply Ideal.under_map
      exact h₁
      exact h₂.ne_top
    rw [← spanNorm_eq, ← spanIntNorm_localization (R := R) (Sₘ := Sₚ) (M := p.primeCompl) _ sorry,
      spanNorm_eq, Ideal.map_pow]
    rw [relNorm_eq_pow_of_isMaximal_aux₁ _ (Ideal.map (algebraMap S Sₚ) P)
     (p := Ideal.map (algebraMap R Rₚ) p)]
    have : (Ideal.map (algebraMap R Rₚ) p).inertiaDeg (Ideal.map (algebraMap S Sₚ) P) =
        p.inertiaDeg P := by
      have := comap_map_eq_map_of_isLocalization_algebraMapSubmonoid p (S := S) (Sₚ := Sₚ)

      rw [Ideal.inertiaDeg_algebraMap]
      rw [Ideal.inertiaDeg_algebraMap]
      rw [liesOver_iff, under_def] at hP₁


      apply Algebra.finrank_eq_of_equiv_equiv

      sorry
      · refine RingEquiv.symm ?_
        refine (equivQuotMaximalIdealOfIsLocalization p Rₚ).trans (Ideal.quotEquivOfEq ?_)
        exact Localization.AtPrime.map_eq_maximalIdeal.symm
      · refine RingEquiv.symm ?_
        refine (Ideal.quotEquivOfEq ?_).trans
          (RingHom.quotientKerEquivOfSurjective (f := algebraMap S (Sₚ ⧸ _)) ?_)

        · have : IsScalarTower S Sₚ (Sₚ ⧸ Ideal.map (algebraMap S Sₚ) P) := by
            exact Submodule.Quotient.isScalarTower _ _
          have := IsScalarTower.algebraMap_eq S Sₚ (Sₚ ⧸ Ideal.map (algebraMap S Sₚ) P)
          rw [this, ← RingHom.comap_ker]
          rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
          rw [← Ring.DimensionLeOne.prime_le_prime_iff_eq hP]
          exact Ideal.le_comap_map
        · intro x
          obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
          obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective Mₛ x
          obtain ⟨s', hs⟩ := Ideal.Quotient.mk_surjective (I := P) (Ideal.Quotient.mk P s)⁻¹
          simp only [IsScalarTower.algebraMap_eq S Sₚ (Sₚ ⧸ _),
            Ideal.Quotient.algebraMap_eq, RingHom.comp_apply]
          use x * s'
          rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
          have : algebraMap S Sₚ s ∉ Ideal.map (algebraMap S Sₚ) P := by
--            rw [← Ideal.mem_comap, IsLocalization.AtPrime.comap_maximalIdeal Rₚ p]
--            exact s.prop
            sorry
          refine ((inferInstanceAs <|
            (Ideal.map (algebraMap S Sₚ) P).IsPrime).mem_or_mem ?_).resolve_left this
          rw [mul_sub, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_mul_cancel_left,
            ← map_mul, ← map_sub, ← Ideal.mem_comap]
--          rw [IsLocalization.AtPrime.comap_maximalIdeal Rₚ p]
          have : Ideal.comap (algebraMap S Sₚ) (Ideal.map (algebraMap S Sₚ) P) = P := by
            apply Ideal.comap_map_eq_of_isMaximal
            exact IsPrime.ne_top'
          rw [mul_left_comm, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_mul, this, hs,
            mul_inv_cancel₀, mul_one, sub_self]
          rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
          sorry -- This is proved above


    rw [this]
    · exact map_ne_bot_of_ne_bot hp
    · exact IsPrincipalIdealRing.principal _
  · obtain ⟨x, hx₁, hx₂⟩ : ∃ x ∈ p, x ∈ q.primeCompl :=
      SetLike.not_le_iff_exists.mp <|
        (Ring.DimensionLeOne.prime_le_prime_iff_eq hp).not.mpr <| hq
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


#exit

set_option maxHeartbeats 10000000 in
theorem relNorm_eq_pow_of_isMaximal_aux₂ [IsGalois (FractionRing R) (FractionRing S)] (P : Ideal S)
    [P.IsMaximal] (p : Ideal R) [p.IsMaximal] [hP₁ : P.LiesOver p]
    [Algebra.IsSeparable (FractionRing R)
    (FractionRing S)] (hp : p ≠ ⊥) :
    relNorm R P = p ^ p.inertiaDeg P := by
  refine eq_of_localization_maximal (fun q hq ↦ ?_)
  let Rₚ := Localization.AtPrime q
  by_cases hq : q = p
  · subst hq
    have : NeZero q := ⟨hp⟩
    let Sₚ := Localization.AtPrime P
    have :  IsLocalization (Algebra.algebraMapSubmonoid S q.primeCompl) Sₚ := by
      refine
        (IsLocalization.iff_of_le_of_exists_dvd (Algebra.algebraMapSubmonoid S q.primeCompl) ?_
              (fun ⦃x⦄ ↦ ?_) ?_).mpr ?_
      · exact P.primeCompl
      · rintro ⟨x, hx, rfl⟩
        rw [liesOver_iff, under_def] at hP₁
      · intro x hx
        let y := Algebra.intNorm R S x
        refine ⟨algebraMap R S y, ?_, ?_⟩
        · unfold Algebra.algebraMapSubmonoid
          refine Submonoid.mem_map_of_mem (algebraMap R S) ?_
          -- simp
          rw [← IsLocalization.AtPrime.isUnit_to_map_iff Sₚ P] at hx
          rw [← IsLocalization.AtPrime.isUnit_to_map_iff Rₚ q]
          unfold y


          sorry
        · unfold y
          rw [Algebra.algebraMap_intNorm_of_isGalois]

          sorry
      · exact Localization.isLocalization
    have : NoZeroSMulDivisors Rₚ Sₚ := sorry
    have : Module.Finite Rₚ Sₚ := sorry
    have : Algebra.IsSeparable (FractionRing Rₚ) (FractionRing Sₚ) := sorry
    rw [← spanNorm_eq, ← spanIntNorm_localization (R := R) (Sₘ := Sₚ) (M := q.primeCompl),
      spanNorm_eq, Ideal.map_pow]
    have : IsPrincipal (Ideal.map (algebraMap S Sₚ) P) := IsPrincipalIdealRing.principal _


#exit

    let Mₛ := Algebra.algebraMapSubmonoid S q.primeCompl
    let Sₚ := Localization Mₛ
    -- let Sₚ := Localization.AtPrime P
    -- This is not true
    -- have : IsLocalization (Algebra.algebraMapSubmonoid S q.primeCompl) Sₚ := by
    --   refine IsLocalization.commutes S ?_ Sₚ ?_ q.primeCompl
    --   apply?
    --  sorry
    let _ : Algebra (FractionRing Rₚ) (FractionRing Sₚ) :=
      FractionRing.liftAlgebra Rₚ (FractionRing Sₚ)

    -- have : Module.Finite Rₚ Sₚ := sorry
    -- have : Algebra.IsSeparable (FractionRing Rₚ) (FractionRing Sₚ) := sorry
--    let _ : Algebra Rₚ Sₚ := sorry
--    have : IsScalarTower R Rₚ Sₚ := sorry
--    have : Module.Finite (Localization.AtPrime q) Sₚ := sorry
--    have : NoZeroSMulDivisors Rₚ Sₚ := sorry
    have : Algebra.IsIntegral S Sₚ := sorry
    have : NoZeroSMulDivisors S Sₚ := sorry
--    have : Module.Finite S Sₚ := sorry
    have : IsGalois (FractionRing Rₚ) (FractionRing Sₚ) := sorry
    have : (Ideal.map (algebraMap R Rₚ) q).IsMaximal := sorry
    rw [← spanNorm_eq, ← spanIntNorm_localization (R := R) (Sₘ := Sₚ) (M := q.primeCompl),
      spanNorm_eq, Ideal.map_pow]

    --> rw [Ideal.map_algebraMap_eq_finset_prod_pow Sₚ (p := P), map_prod]

    -- rw [← Ideal.finprod_heightOneSpectrum_factorization this]
    -- rw [← Finset.prod_finset_coe]
    -- have h₀ (Q : (P.primesOver Sₚ).toFinset) : Q.1.LiesOver P := sorry
    -- have h₁ (Q : (P.primesOver Sₚ).toFinset) :
    --   Q.1.LiesOver (Ideal.map (algebraMap R Rₚ) q) := sorry
    -- have h₂ (Q : (P.primesOver Sₚ).toFinset) : Q.1.IsMaximal := sorry
    -- have h₃ (Q : (P.primesOver Sₚ).toFinset) : IsPrincipal Q.1 := sorry
    -- have h₄ : Ideal.map (algebraMap R (Localization.AtPrime q)) q ≠ 0 := sorry
    have : (map (algebraMap S Sₚ) P).LiesOver (map (algebraMap R Rₚ) q) := sorry
    have : Ideal.map (algebraMap R Rₚ) q ≠ 0 := sorry
    rw [relNorm_eq_pow_of_isMaximal_aux₁ Rₚ _ this]
    simp_rw +contextual [map_pow, relNorm_eq_pow_of_isMaximal_aux₁ _ _ h₄ (h₃ _), ← pow_mul]
    -- have (Q : (P.primesOver Sₚ).toFinset) :
    --     P.ramificationIdxIn Sₚ = ramificationIdx (algebraMap S Sₚ) P Q := by

    --     have := Ideal.ramificationIdxIn_eq_ramificationIdx P Q.1 (FractionRing S) (FractionRing S)
    --     exact this
    conv_lhs =>
      enter [2, Q, 2]
      rw [← Ideal.inertiaDegIn_eq_inertiaDeg _ _ (FractionRing Rₚ) (FractionRing Sₚ)]
      -- rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (map (algebraMap R Rₚ) q) _ (FractionRing Rₚ) (FractionRing Sₚ)]


      -- ← ramificationIdxIn_eq_ramificationIdx _ _ (FractionRing Rₚ) (FractionRing Sₚ)]
    rw [Finset.prod_pow_eq_pow_sum]
    congr




    have : (Ideal.map (algebraMap S Sₚ) P).IsMaximal := sorry

    have : (Ideal.map (algebraMap S Sₚ) P).LiesOver (Ideal.map (algebraMap R Rₚ) q) := sorry

    conv_lhs =>
      enter [2, Q]
      rw [relNorm_eq_pow_of_isMaximal_aux₁]

      sorry

    simp_rw [relNorm_eq_pow_of_isMaximal_aux₁ _ (Ideal.map (algebraMap S Sₚ) P)
     (p := Ideal.map (algebraMap R Rₚ) q)]

    congr 1

    rw [Ideal.inertiaDeg_algebraMap, Ideal.inertiaDeg_algebraMap]

    · sorry
    · sorry
    · exact IsPrincipalIdealRing.principal _
    · sorry

   -- case q ≠ p
  · let Mₛ := Algebra.algebraMapSubmonoid S q.primeCompl
    let Sₚ := Localization Mₛ
    obtain ⟨x, hx₁, hx₂⟩ : ∃ x ∈ p, x ∈ q.primeCompl :=
      SetLike.not_le_iff_exists.mp <|
        (Ring.DimensionLeOne.prime_le_prime_iff_eq hp).not.mpr <| ne_comm.mp hq
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



#exit
      IsLocalization.AtPrime.map_ideal_eq_top Rₚ q <|
       (Ring.DimensionLeOne.prime_le_prime_iff_eq hp).not.mpr <| ne_comm.mp hq

      have : ∃ x, x ∈ Mₛ ∧ x ∈ P := by
        simp [Mₛ, Algebra.algebraMapSubmonoid]


        sorry
      obtain ⟨x, hx₁, hx₂⟩ := this
      refine eq_top_of_isUnit_mem _ (mem_map_of_mem _ hx₂) ?_
      exact IsLocalization.map_units _ ⟨x, hx₁⟩
    rw [← spanNorm_eq, ← spanIntNorm_localization R (Sₘ := Sₚ) _ _
      (primeCompl_le_nonZeroDivisors q), spanNorm_eq, Ideal.map_pow, h₁, h₂, relNorm_top, top_pow]




#exit
    rw [← spanNorm_eq, ← spanIntNorm_localization R (Sₘ := Sₚ) _ _
      (primeCompl_le_nonZeroDivisors q), spanNorm_eq, Ideal.map_pow,
      IsLocalization.AtPrime.map_ideal_eq_top Rₚ q]
    · have : Ideal.map (algebraMap S Sₚ) P = ⊤ := by
        have : ∃ x, x ∈ q ∧ x ∉ p := sorry
        obtain ⟨x, hx₁, hx₂⟩ := this
        apply eq_top_of_isUnit_mem (x := algebraMap R Sₚ x)
        · sorry
        · sorry
      rw [this]
      rw [relNorm_top, top_pow]
    · rwa [Ring.DimensionLeOne.prime_le_prime_iff_eq hp, eq_comm]

#exit

  ·
    let _ : Algebra (FractionRing Rₚ) (FractionRing Sₚ) :=
      FractionRing.liftAlgebra Rₚ (FractionRing Sₚ)
    have : IsGalois (FractionRing Rₚ) (FractionRing Sₚ) := sorry
    have : (Ideal.map (algebraMap S Sₚ) P).IsMaximal := by

      sorry
    have : (Ideal.map (algebraMap R Rₚ) q).IsMaximal := by
      rw [Localization.AtPrime.map_eq_maximalIdeal]
      exact IsLocalRing.maximalIdeal.isMaximal Rₚ
    have : (Ideal.map (algebraMap S Sₚ) P).LiesOver (Ideal.map (algebraMap R Rₚ) q) := by

      rw [liesOver_iff, under_def]
      have :  IsLocalization (Algebra.algebraMapSubmonoid Rₚ q.primeCompl) Sₚ := sorry
      have := comap_map_eq_map_of_isLocalization_algebraMapSubmonoid q (S := Rₚ) (Sₚ := Sₚ)
      rw [← this]
      congr 1



      rw [Ideal.under_map R S, ← hP₁.1]
    rw [relNorm_eq_pow_of_isMaximal_aux₁ _ (Ideal.map (algebraMap S Sₚ) P)
     (p := Ideal.map (algebraMap R Rₚ) q)]
    congr 1
    · sorry
    · sorry
    · sorry




#exit
  -- Need to consider the cases q = p and q ≠ p

  rw [← spanNorm_eq]
  rw [← spanIntNorm_localization (R := R) (Sₘ := Sₚ) _ _ q.primeCompl_le_nonZeroDivisors]
  rw [spanNorm_eq]
  have : (Ideal.map (algebraMap S Sₚ) P).LiesOver (Ideal.map (algebraMap R Rₚ) p) := sorry
  have : (Ideal.map (algebraMap S Sₚ) P).IsMaximal := sorry
  have : (Ideal.map (algebraMap R Rₚ) p).IsMaximal := sorry
  let _ : Algebra (FractionRing Rₚ) (FractionRing Sₚ) := by
    exact FractionRing.liftAlgebra Rₚ (FractionRing Sₚ)
  have : IsGalois (FractionRing Rₚ) (FractionRing Sₚ) := sorry
  rw [relNorm_eq_pow_of_isMaximal_aux₁ _ (Ideal.map (algebraMap S Sₚ) P)
     (p := Ideal.map (algebraMap R Rₚ) p)]
  rw [Ideal.map_pow]
  congr 1


  sorry


#exit

    congr
    -- have : Finset.card {g : S ≃ₐ[R] S | Q = ↑(g • P)} =
    --     Finset.card {g : S ≃ₐ[R] S | ↑(g • P) = P} := by
    --   simp at hQ
    --   have : Q.IsPrime := hQ.1
    --   have : Q.LiesOver p := hQ.2
    --   obtain ⟨σ, rfl⟩ := Ideal.exists_map_eq_of_isGalois p P Q (FractionRing R) (FractionRing S)
    --   have : Ideal.map σ ↑P = σ • P := rfl -- make a simp lemma?
    --   simp_rw [this]
    --   have : ∀ g, σ • P = g • P ↔ (σ⁻¹ * g) • P = P  := by
    --     intro g
    --     rw [smul_eq_iff_eq_inv_smul, eq_comm, smul_smul]
    --   simp_rw [this]
    --   refine Finset.card_equiv ?_ ?_
    --   · exact Equiv.mulLeft σ⁻¹
    --   · intro g
    --     simp
    rw [this]
    lift Q to (p.primesOver S) using Set.mem_toFinset.mp hQ
    lift P to (p.primesOver S) using hPp
    convert card_stabilizer_eq_ramificationIdxIn_mul_inertiaDegIn R p P hp
    rw [← Fintype.card_subtype]
    simp [← coe_smul_primesOver, Subtype.coe_inj]



















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
