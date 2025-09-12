import Mathlib.Algebra.GroupWithZero.Torsion
import Mathlib.Algebra.Regular.Opposite
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Ideal.Norm.RelNorm

set_option linter.style.header false

open Ideal Algebra Pointwise

attribute [local instance] FractionRing.liftAlgebra

-- noncomputable def FractionRing.algEquiv_apply (A : Type*) [CommRing A] (K : Type*) [CommRing K]
--     [Algebra A K] [FaithfulSMul A K] [IsFractionRing A K] (x) :
--     FractionRing.algEquiv A K (algebraMap (FractionRing A) K x) = 0 := sorry

theorem Ideal.exists_mem_primesOver_of_isIntegral {R : Type*} [CommRing R] {S : Type*} [CommRing S]
    [Nontrivial S] [Algebra R S] [Algebra.IsIntegral R S] [NoZeroSMulDivisors R S] (P : Ideal R)
    [P.IsPrime] :
    ∃ (Q : Ideal S), Q ∈ primesOver P S := by
  obtain ⟨Q, _, hQ₁, hQ₂⟩ := exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal S) (by simp)
  exact ⟨Q, ⟨hQ₁, (liesOver_iff _ _).mpr hQ₂.symm⟩⟩

theorem Ideal.exists_maximal_ideal_liesOver_of_isIntegral {R : Type*} [CommRing R] {S : Type*}
    [CommRing S] [Algebra R S] [Algebra.IsIntegral R S] [FaithfulSMul R S] (P : Ideal R)
    [P.IsMaximal] :
    ∃ (Q : Ideal S), Q.IsMaximal ∧ Q.LiesOver P := by
  simp_rw [liesOver_iff, eq_comm (a := P)]
  exact exists_ideal_over_maximal_of_isIntegral P (by
    simp [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective R S)])

theorem Ideal.smul_def {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S] (σ : S ≃ₐ[R] S)
    (I : Ideal S) : σ • I = map σ I := rfl

theorem Ideal.ramificationIdx_ne_zero_of_liesOver {R : Type*} [CommRing R]
    {S : Type*} [CommRing S] [IsDedekindDomain S] [Algebra R S] [NoZeroSMulDivisors R S]
    {p : Ideal R} (hp : p ≠ ⊥) (P : Ideal S) [hP : P.IsPrime] [hPp : P.LiesOver p] :
    ramificationIdx (algebraMap R S) p P ≠ 0 := by
  apply IsDedekindDomain.ramificationIdx_ne_zero
  · apply map_ne_bot_of_ne_bot hp
  · exact hP
  rw [liesOver_iff] at hPp
  rw [map_le_iff_le_comap]
  exact le_of_eq hPp

attribute [local instance] FractionRing.liftAlgebra

-- (A : Type u_1)  (B : Type u_4)  [CommRing A]  [CommRing B]  [Algebra A B] [IsIntegrallyClosed A]
-- [IsDomain A]  [IsDomain B]  [IsIntegrallyClosed B] [Module.Finite A B]  [NoZeroSMulDivisors A B]
-- [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

-- def Algebra.norm (R : Type u_1)  {S : Type u_2}  [CommRing R]  [Ring S]  [Algebra R S] :

variable (R : Type*) [CommRing R] {S₀ : Type*} [Ring S₀] [Algebra R S₀]

variable [IsDomain R] {S : Type*} [CommRing S] [Algebra R S] [IsDomain S] [IsIntegrallyClosed R]
  [IsIntegrallyClosed S] [Module.Finite R S] [NoZeroSMulDivisors R S]

variable [IsDedekindDomain R] [IsDedekindDomain S]

theorem relNorm_smul [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    (I : Ideal S) (σ : S ≃ₐ[R] S) :
    relNorm R (σ • I) = relNorm R I := by
  have h (J : Ideal S) (τ : S ≃ₐ[R] S) : relNorm R (τ • J) ≤ relNorm R J  := by
    simp_rw [Ideal.relNorm_apply]
    apply span_mono
    rintro _ ⟨x, hx₁, hx₂⟩
    exact ⟨τ⁻¹ x, mem_pointwise_smul_iff_inv_smul_mem.mp hx₁, hx₂ ▸ intNorm_eq_of_algEquiv x τ⁻¹⟩
  apply le_antisymm
  · exact h I σ
  · convert h (σ • I) σ⁻¹
    simp

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S] [Module.Finite R S]
  [IsDedekindDomain R] [IsDedekindDomain S] [IsIntegrallyClosed R] [IsIntegrallyClosed S]
  [NoZeroSMulDivisors R S]

  -- [FaithfulSMul R S] [IsDedekindDomain S]

variable (p : Ideal R) (P : Ideal S) [hPp : P.LiesOver p]

lemma res1 [Algebra.IsSeparable (FractionRing R) (FractionRing S)] [p.IsPrime] (hp : p ≠ ⊥) :
    ∃ s, relNorm R P = p ^ s := by
  have : map (algebraMap R S) p ≤ P := by
    rw [liesOver_iff] at hPp
    rw [map_le_iff_le_comap]
    exact le_of_eq hPp
  have := relNorm_mono R this
  rw [relNorm_algebraMap S, ← dvd_iff_le] at this
  rw [dvd_prime_pow] at this
  · obtain ⟨s, _, hs⟩ := this
    refine ⟨s, ?_⟩
    rwa [associated_iff_eq] at hs
  exact prime_of_isPrime hp inferInstance

lemma res2 [p.IsMaximal] [P.IsPrime] [IsGalois (FractionRing R) (FractionRing S)] :
    relNorm R P = p ^ p.inertiaDeg P := by
  by_cases hp : p = ⊥
  · have h : p.inertiaDeg P ≠ 0 :=  by
      rw [Nat.ne_zero_iff_zero_lt]
      exact Ideal.inertiaDeg_pos p P
    have hP : P = ⊥ := by
      rw [hp] at hPp
      exact eq_bot_of_liesOver_bot R P
    rw [hp, hP, relNorm_bot, bot_pow]
    rwa [hp, hP] at h
  have t₁ := congr_arg (relNorm R ·) <| Ideal.map_algebraMap_eq_finset_prod_pow S hp
  have t₂ := relNorm_algebraMap S p
  have h := t₁.symm.trans t₂
  dsimp at h
  simp_rw [map_prod, map_pow] at h
  obtain ⟨s, hs⟩ := res1 p P hp
  have {Q} (hQ : Q ∈ (p.primesOver S).toFinset) :
      relNorm R Q ^ ramificationIdx (algebraMap R S) p Q = p ^ ((p.ramificationIdxIn S) * s) := by
    rw [Set.mem_toFinset] at hQ
    have : Q.IsPrime := hQ.1
    have : Q.LiesOver p := hQ.2
    rw [← ramificationIdxIn_eq_ramificationIdx p Q (FractionRing R) (FractionRing S)]
    obtain ⟨σ, rfl⟩ := Ideal.exists_map_eq_of_isGalois p P Q (FractionRing R) (FractionRing S)
    have := relNorm_smul R P σ
    rw [Ideal.smul_def] at this
    rw [this]
    rw [hs, ← pow_mul, mul_comm]
  simp_rw +contextual [this] at h
  rw [Finset.prod_const, ← pow_mul] at h
  have : IsLeftRegular p := IsLeftCancelMulZero.mul_left_cancel_of_ne_zero hp
  have := IsLeftRegular.pow_inj this ?_
  · rw [this.eq_iff] at h
    rw [← Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp S] at h
    rw [← Set.ncard_eq_toFinset_card', mul_comm, mul_right_inj',
      mul_right_inj'] at h
    · rwa [h, inertiaDegIn_eq_inertiaDeg p P (FractionRing R) (FractionRing S)] at hs
    · rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P (FractionRing R) (FractionRing S)]
      exact ramificationIdx_ne_zero_of_liesOver hp _
    · exact primesOver_ncard_ne_zero p S
  · rw [one_eq_top]
    exact IsMaximal.ne_top inferInstance

set_option maxHeartbeats 800000 in
-- set_option synthInstance.maxHeartbeats 100000 in
theorem relNorm_eq_pow_of_isMaximal --
    -- [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    -- [Algebra.IsSeparable (FractionRing R) (AlgebraicClosure (FractionRing S))]
    [PerfectField (FractionRing R)]
    (P : Ideal S) [P.IsMaximal] (p : Ideal R) [p.IsMaximal] [P.LiesOver p] :
    relNorm R P = p ^ p.inertiaDeg P := by
  let K := FractionRing R
  let L := FractionRing S
  let A := AlgebraicClosure L
  let E := IntermediateField.normalClosure K L A
  -- Lean has trouble finding this instance
  let _ : Algebra K A := AlgebraicClosure.instAlgebra L
  -- Lean has trouble finding this instance
  let _ : Algebra L E := normalClosure.algebra K L A
  -- Lean has trouble finding this instance
  let _ : Algebra K E := (IntermediateField.normalClosure K L A).algebra'
  let _ : Algebra S E := ((algebraMap L E).comp (algebraMap S L)).toAlgebra

  let T := integralClosure S E

  let _ : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra

  have : IsScalarTower S L E := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R L E := IsScalarTower.to₁₃₄ R K L E
  have : IsScalarTower R S E := IsScalarTower.to₁₂₄ R S L E
  have : IsScalarTower R T E := IsScalarTower.to₁₃₄ R S T E

  have : IsScalarTower K L E := by exact
    normalClosure.instIsScalarTowerSubtypeMemIntermediateFieldNormalClosure K L A

  have : Module.Finite L E := Module.Finite.right K L E

  have : Algebra.IsSeparable L E := by
    have : PerfectField L := Algebra.IsAlgebraic.perfectField (K := K)
    have : Algebra.IsAlgebraic L E := Algebra.IsAlgebraic.of_finite L E
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField

  have : IsDedekindDomain T := integralClosure.isDedekindDomain S L E

  have : Module.Finite S T := IsIntegralClosure.finite S L E T
  have : Module.Finite R T := Module.Finite.trans S T

  have : IsFractionRing (integralClosure S E) E :=
    integralClosure.isFractionRing_of_finite_extension L E

  have : FaithfulSMul S E := (faithfulSMul_iff_algebraMap_injective S E).mpr <|
      (FaithfulSMul.algebraMap_injective L E).comp (FaithfulSMul.algebraMap_injective S L)

  have : FaithfulSMul R T := (faithfulSMul_iff_algebraMap_injective R T).mpr <|
      (FaithfulSMul.algebraMap_injective S T).comp (FaithfulSMul.algebraMap_injective R S)

  let _ : Algebra K (FractionRing T) := FractionRing.liftAlgebra R (FractionRing ↥T)

  have : IsGalois K (FractionRing T) := by
    refine { to_isSeparable := ?_, to_normal := ?_ }
    · exact IsAlgebraic.isSeparable_of_perfectField
    have : Normal K E := normalClosure.normal K L A
    apply Normal.of_equiv_equiv (F := K) (E := E) (f := RingEquiv.refl K)
      (g := (FractionRing.algEquiv T E).symm)
    ext x
    refine x.ind fun ⟨r, s⟩ ↦ ?_
    simp only [RingEquiv.coe_ringHom_refl, RingHomCompTriple.comp_eq, FractionRing.mk_eq_div,
      map_div₀, AlgEquiv.symm_toRingEquiv, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
    rw [← IsScalarTower.algebraMap_apply R K E]
    rw [← IsScalarTower.algebraMap_apply R K E]
    rw [← IsScalarTower.algebraMap_apply R K (FractionRing T)]
    rw [← IsScalarTower.algebraMap_apply R K (FractionRing T)]
    rw [← AlgEquiv.symm_toRingEquiv]
    rw [AlgEquiv.coe_ringEquiv]
    rw [IsScalarTower.algebraMap_apply R T E]
    rw [IsScalarTower.algebraMap_apply R T E]
    rw [AlgEquiv.commutes, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]

  have : IsGalois L (FractionRing T) := IsGalois.tower_top_of_isGalois K _ _

  obtain ⟨Q, hQ₁, hQ₂⟩ : ∃ Q : Ideal T, Q.IsMaximal ∧ Q.LiesOver P :=
    exists_maximal_ideal_liesOver_of_isIntegral P
  have t₁ := res2 P Q
  have : Q.LiesOver p := LiesOver.trans Q P p
  have t₂ := res2 p Q

  rw [← relNorm_relNorm R S, t₁, map_pow] at t₂
  rw [Ideal.inertiaDeg_algebra_tower p P Q] at t₂
  rw [pow_mul] at t₂
  rwa [pow_left_inj] at t₂
  rw [Nat.ne_zero_iff_zero_lt]
  apply Ideal.inertiaDeg_pos

#exit

  have h₀ := congr_arg (relNorm R ·) <| congr_arg (map (algebraMap R S) ·) (hs 1)
  dsimp at h₀
  rw [Ideal.map_pow, map_pow, one_smul, relNorm_algebraMap] at h₀
  rw [Ideal.map_algebraMap_eq_finset_prod_pow] at h₀

  have : ∏ P ∈ (p.primesOver S).toFinset, P ^ ramificationIdx (algebraMap R S) p P =
    (∏ σ : S ≃ₐ[R] S, σ • P) ^ p.ramificationIdxIn S := sorry
  rw [this] at h₀
  rw [map_pow, ← pow_mul, map_prod] at h₀
  simp_rw [hs] at h₀
  have : relNorm R P = p ^ s := sorry
  rw [this] at h₀
  simp at h₀






#exit

open scoped nonZeroDivisors

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


-- theorem dvd_algebraMap_intNorm_self {R : Type*} [CommRing R] [IsDomain R] {S : Type*} [CommRing S]
--     [IsDomain S] [IsIntegrallyClosed R] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S]
--     [NoZeroSMulDivisors R S] [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
--     (x : S) :
--     x ∣ algebraMap R S (intNorm R S x) := by
--   classical
--   by_cases hx : x = 0
--   · exact ⟨1, by simp [hx]⟩
--   let K := FractionRing R
--   let L := FractionRing S
--   let E := AlgebraicClosure L
--   suffices IsIntegral R ((algebraMap S L x)⁻¹ * (algebraMap R L (intNorm R S x))) by
--     obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp <| IsIntegral.tower_top (A := S) this
--     refine ⟨y, ?_⟩
--     apply FaithfulSMul.algebraMap_injective S L
--     rw [← IsScalarTower.algebraMap_apply, map_mul, hy, mul_inv_cancel_left₀]
--     exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective S L)).mpr hx
--   rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom R L E)
--     (FaithfulSMul.algebraMap_injective L E), IsScalarTower.coe_toAlgHom', map_mul, map_inv₀,
--     IsScalarTower.algebraMap_apply R K L, algebraMap_intNorm (L := L),
--     ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, norm_eq_prod_embeddings,
--     ←  Finset.univ.mul_prod_erase _ (Finset.mem_univ (IsScalarTower.toAlgHom K L E)),
--     IsScalarTower.coe_toAlgHom', ← IsScalarTower.algebraMap_apply, inv_mul_cancel_left₀]
--   · refine IsIntegral.prod _ fun σ _ ↦ ?_
--     change IsIntegral R ((σ.restrictScalars R) (IsScalarTower.toAlgHom R S L x))
--     rw [isIntegral_algHom_iff _ (RingHom.injective _),
--       isIntegral_algHom_iff _ (FaithfulSMul.algebraMap_injective S L)]
--     exact IsIntegral.isIntegral x
--   · have := NoZeroSMulDivisors.trans_faithfulSMul S L E
--     exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective S E)).mpr hx

-- theorem step01 {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
--     [IsIntegrallyClosed R] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S]
--     [NoZeroSMulDivisors R S] [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
--     {I : Ideal S} {x : S} (hx : x ∈ I) :
--     algebraMap R S ((Algebra.intNorm R S) x) ∈ I :=
--   Ideal.mem_of_dvd _ (dvd_algebraMap_intNorm_self x) hx

-- theorem Ideal.spanNorm_le_comap (R : Type*) [CommRing R] [IsDomain R] {S : Type*} [CommRing S]
--     [IsDomain S] [IsIntegrallyClosed R] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S]
--     [NoZeroSMulDivisors R S] [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
--     (I : Ideal S) : spanNorm R I ≤ comap (algebraMap R S) I := by
--   rw [spanNorm, Ideal.map, Ideal.span_le, ← Submodule.span_le]
--   apply Submodule.span_induction
--   · rintro _ ⟨x, hx, rfl⟩
--     rw [Ideal.mem_comap]
--     exact Ideal.mem_of_dvd _ (dvd_algebraMap_intNorm_self x) hx
--   · simp
--   · intro _ _ _ _ hx hy
--     exact Submodule.add_mem _ hx hy
--   · intro _ _ _ hx
--     exact Submodule.smul_mem _ _ hx



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

open IsLocalization.AtPrime in
theorem relNorm_eq_pow_of_isMaximal' [IsGalois (FractionRing R) (FractionRing S)] (P : Ideal S)
    [P.IsMaximal] (p : Ideal R) [p.IsMaximal] [hPp : P.LiesOver p] :
    relNorm R P = p ^ p.inertiaDeg P := by
  by_cases hp : p = ⊥
  · have h : p.inertiaDeg P ≠ 0 := (Ideal.inertiaDeg_pos p P).ne'
    rw [hp] at hPp h ⊢
    rw [Ideal.bot_pow h, eq_bot_of_liesOver_bot R P, relNorm_eq_bot_iff]
  refine eq_of_localization_maximal (fun q hq ↦ ?_)
  let Rₚ := Localization.AtPrime q
  let Mₛ := Algebra.algebraMapSubmonoid S q.primeCompl
  let Sₚ := Localization Mₛ
  by_cases hq : p = q
  · subst hq
    have : NeZero p := ⟨hp⟩
    have hP : P ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp P
    let _ : Algebra Sₚ (FractionRing S) :=
    have : IsScalarTower R Sₚ (FractionRing S) := sorry -- .trans_right R S Sₚ (FractionRing S)
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
    have : IsNoetherianRing Rₚ := by exact
      IsLocalization.instIsNoetherianRingLocalization p.primeCompl
    have : IsBezout Rₚ := by exact IsBezout.of_isPrincipalIdealRing Rₚ
    have : IsPrincipalIdealRing Rₚ := by exact
      IsPrincipalIdealRing.of_isNoetherianRing_of_isBezout
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
  rw [Ideal.inertiaDeg_algebra_tower p P Q] at t₂
  rw [pow_mul] at t₂


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
