import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.Minpoly.ConjRootClass
import Mathlib.Cyclotomic
import Mathlib.Basis
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.Misc

attribute [local instance] FractionRing.liftAlgebra in
theorem Ideal.absNorm_algebraMap (A K L B : Type*) [CommRing A] [IsDedekindDomain A]
    [Module.Free ℤ A] [CommRing B] [IsDedekindDomain B] [Module.Free ℤ B] [Module.Finite ℤ B]
    [Algebra A B] [NoZeroSMulDivisors A B] [Field K] [Algebra A K] [IsFractionRing A K] [Field L]
    [Algebra B L] [Algebra A L] [IsFractionRing B L] [Algebra K L] [IsScalarTower A K L]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [IsScalarTower A B L]
    (I : Ideal A) : absNorm (I.map (algebraMap A B)) = absNorm I ^ Module.finrank K L := by
  have : Module.Finite ℤ A := Module.Finite.left ℤ A B
  have : Module.Finite A B := Module.Finite.right ℤ A B
  rw [← absNorm_relNorm ℤ, ← relNorm_relNorm ℤ A, relNorm_algebraMap, absNorm_relNorm, map_pow]
  let e := FractionRing.algEquiv A K
  let f := FractionRing.algEquiv B L
  rw [Algebra.finrank_eq_of_equiv_equiv e.symm.toRingEquiv f.symm.toRingEquiv]
  ext x
  simp [e, f]
  have := FractionRing.algEquiv_algebraMap_commutes A B K L x
  exact this

open NumberField

theorem NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow (E F : Type*)
    [Field E] [Field F] [NumberField E] [NumberField F] [Algebra E F] :
    (discr F).natAbs = Ideal.absNorm (differentIdeal (𝓞 E) (𝓞 F)) *
      (discr E).natAbs ^ Module.finrank E F := by
  have := congr_arg Ideal.absNorm
    (differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 E) (𝓞 F))
  rwa [absNorm_differentIdeal F, map_mul, Ideal.absNorm_algebraMap (𝓞 E) E F (𝓞 F),
    absNorm_differentIdeal E] at this

theorem NumberField.discr_dvd_discr (E F : Type*) [Field E] [Field F] [NumberField E]
    [NumberField F] [Algebra E F] : discr E ∣ discr F := by
  suffices discr E ^ Module.finrank E F ∣ discr F from
    dvd_trans (dvd_pow_self _ (Nat.ne_zero_of_lt Module.finrank_pos)) this
  rw [← Int.dvd_natAbs, natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow E F,
    Nat.cast_mul, Nat.cast_pow, ← Int.mul_sign_self, mul_pow, ← mul_assoc,
    mul_comm _ (discr E ^ _), mul_assoc]
  exact Int.dvd_mul_right _ _

theorem NumberField.isCoprime_differentIdeal_of_isCoprime_discr (E : Type*) [Field E]
    [NumberField E] {F₁ F₂ : Type*} [Field F₁] [NumberField F₁] [Field F₂] [NumberField F₂]
    [Algebra F₁ E] [Algebra F₂ E]
    (h : IsCoprime (discr F₁) (discr F₂)) :
    IsCoprime ((differentIdeal ℤ (𝓞 F₁)).map (algebraMap (𝓞 F₁) (𝓞 E)))
      ((differentIdeal ℤ (𝓞 F₂)).map (algebraMap (𝓞 F₂) (𝓞 E))) := by
  rw [Ideal.isCoprime_iff_exists]
  obtain ⟨u, v, h⟩ := h
  refine ⟨u * discr F₁, ?_, v * discr F₂, ?_, ?_⟩
  · apply Ideal.mul_mem_left
    rw [← map_intCast (algebraMap (𝓞 F₁) (𝓞 E))]
    exact Ideal.mem_map_of_mem (algebraMap (𝓞 F₁) (𝓞 E)) discr_mem_differentIdeal
  · apply Ideal.mul_mem_left
    rw [← map_intCast (algebraMap (𝓞 F₂) (𝓞 E))]
    exact Ideal.mem_map_of_mem (algebraMap (𝓞 F₂) (𝓞 E)) discr_mem_differentIdeal
  rw [← Int.cast_mul, ← Int.cast_mul, ← Int.cast_add, h, Int.cast_one]

open IntermediateField

theorem NumberField.discr_eq_discr_pow_mul_discr_pow {E : Type*} [Field E] [NumberField E]
    (L₁ L₂ : IntermediateField ℚ E) (h₁ : L₁.LinearDisjoint L₂) (h₂ : L₁ ⊔ L₂ = ⊤)
    (h₃ : IsCoprime ((differentIdeal ℤ (𝓞 L₁)).map (algebraMap (𝓞 L₁) (𝓞 E)))
      ((differentIdeal ℤ (𝓞 L₂)).map (algebraMap (𝓞 L₂) (𝓞 E)))) :
    (discr E).natAbs = (discr L₁).natAbs ^ Module.finrank ℚ L₂ *
      (discr L₂).natAbs ^ Module.finrank ℚ L₁ := by
  have := congr_arg Ideal.absNorm <|
    differentIdeal_eq_differentIdeal_mul_differentIdeal_of_isCoprime ℤ (𝓞 E) (𝓞 L₁) (𝓞 L₂) h₁ h₂ h₃
  rwa [map_mul, absNorm_differentIdeal E, differentIdeal_eq_map_differentIdeal_of_isCoprime ℤ (𝓞 E)
    (𝓞 L₁) (𝓞 L₂) h₁ h₂ h₃, Ideal.absNorm_algebraMap (𝓞 L₂) L₂ E, absNorm_differentIdeal L₂,
    differentIdeal_eq_map_differentIdeal_of_isCoprime ℤ (𝓞 E) (𝓞 L₂) (𝓞 L₁) (L₁ := L₂) (L₂ := L₁)
    (by rwa [linearDisjoint_comm]) (by rwa [sup_comm]) (by rwa [isCoprime_comm]),
    Ideal.absNorm_algebraMap (𝓞 L₁) L₁ E, absNorm_differentIdeal L₁, mul_comm,
    h₁.finrank_left_eq_finrank h₂, h₁.finrank_right_eq_finrank h₂] at this

theorem NumberField.LinearDisjoint.of_isGalois_isCoprime_discr {E : Type*} [Field E] [NumberField E]
    (F₁ F₂ : IntermediateField ℚ E) [IsGalois ℚ F₁]
    (h : IsCoprime (discr F₁) (discr F₂)) :
    F₁.LinearDisjoint F₂ := by
  apply IntermediateField.LinearDisjoint.of_inf_eq_bot
  suffices IsUnit (discr ↥(F₁ ⊓ F₂)) by
    contrapose! this
    have : 1 < Module.finrank ℚ ↥(F₁ ⊓ F₂) := by
      refine Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨?_, ?_⟩
      · exact Module.finrank_pos.ne'
      · rwa [ne_eq, ← IntermediateField.finrank_eq_one_iff] at this
    have := abs_discr_gt_two this
    rw [Int.isUnit_iff_abs_eq]
    linarith
  let _ : Algebra ↥(F₁ ⊓ F₂) F₁ := RingHom.toAlgebra (inclusion inf_le_left).toRingHom
  let _ : Algebra ↥(F₁ ⊓ F₂) F₂ := RingHom.toAlgebra (inclusion inf_le_right).toRingHom
  exact h.isUnit_of_dvd' (NumberField.discr_dvd_discr _ _) (NumberField.discr_dvd_discr _ _)

---- CYCLOTOMIC FIELDS

theorem IsCyClotomicExtension.Rat.absdiscr (K : Type*) [Field K] [NumberField K] (n : ℕ)
    [hn : NeZero n] [hK : IsCyclotomicExtension {n} ℚ K] :
    (discr K).natAbs = n ^ n.totient / ∏ p ∈ n.primeFactors, p ^ (n.totient / (p - 1)) := by
  induction n using Nat.recOnPrimeCoprime generalizing K hn with
  | zero => exact (neZero_zero_iff_false.mp hn).elim
  | prime_pow p k hp =>
    have : Fact (Nat.Prime p) := ⟨hp⟩
    rw [IsCyclotomicExtension.Rat.absdiscr_prime_pow p k K]
    by_cases hk : k = 0
    · simp [hk]
    have h₁ : 0 < p - 1 := Nat.zero_lt_sub_of_lt <| Nat.Prime.one_lt hp
    have h₂ : p ^ (k - 1) ≤ k * (p ^ (k - 1) * (p - 1)) := by
      rw [mul_comm k, mul_assoc]
      exact Nat.le_mul_of_pos_right _ <| Nat.mul_pos h₁ (Nat.zero_lt_of_ne_zero hk)
    rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul,
      Int.natAbs_pow, Int.natAbs_cast, Nat.primeFactors_prime_pow hk hp, Finset.prod_singleton,
      Nat.totient_prime_pow hp (Nat.zero_lt_of_ne_zero hk), Nat.mul_div_left _ h₁, ← pow_mul,
      Nat.pow_div h₂ p.pos_of_neZero]
    simp only [Nat.sub_mul, one_mul, Nat.mul_sub, mul_one]
    ring_nf
  | coprime n₁ n₂ hn₁ hn₂ h hK₁ hK₂ =>
    have : NeZero n₁ := NeZero.of_gt hn₁
    have : NeZero n₂ := NeZero.of_gt hn₂
    let ζ := IsCyclotomicExtension.zeta (n₁ * n₂) ℚ K
    have hζ := IsCyclotomicExtension.zeta_spec (n₁ * n₂) ℚ K
    have hζ₁ := hζ.pow (NeZero.pos _) (a := n₁) (b := n₂) rfl
    have := hζ₁.intermediateField_adjoin_isCyclotomicExtension ℚ
    have hζ₂' : IsPrimitiveRoot (AdjoinSimple.gen ℚ (ζ ^ n₁)) n₂ :=
      IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ₁
    replace hK₂ := @hK₂ ℚ⟮ζ ^ n₁⟯ _ _ _ _
    have hζ₂ := hζ.pow (NeZero.pos _) (a := n₂) (b := n₁) (by rw [mul_comm])
    have := hζ₂.intermediateField_adjoin_isCyclotomicExtension ℚ
    have hζ₁' : IsPrimitiveRoot (AdjoinSimple.gen ℚ (ζ ^ n₂)) n₁ :=
      IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ₂
    replace hK₁ := @hK₁ ℚ⟮ζ ^ n₂⟯ _ _ _ _
    have : IsGalois ℚ ℚ⟮ζ ^ n₁⟯ := IsCyclotomicExtension.isGalois {n₂} ℚ ℚ⟮ζ ^ n₁⟯
    have h₁ : IsCoprime (discr ℚ⟮ζ ^ n₁⟯) (discr ℚ⟮ζ ^ n₂⟯) := by
      rw [Int.isCoprime_iff_nat_coprime, hK₁, hK₂]
      apply Nat.Coprime.coprime_div_left
      apply Nat.Coprime.coprime_div_right
      apply Nat.Coprime.pow_left
      apply Nat.Coprime.pow_right
      exact h.symm
      exact Nat.prod_primeFractors_pow_dvd_pow_totient n₁
      exact Nat.prod_primeFractors_pow_dvd_pow_totient n₂
    have h₂ : ℚ⟮ζ ^ n₁⟯ ⊔ ℚ⟮ζ ^ n₂⟯ = ⊤ := by
        have : IsCyclotomicExtension {n₁ * n₂} ℚ (⊤ : IntermediateField ℚ K) :=
          hK.equiv _ _ _ topEquiv.symm
        have : IsCyclotomicExtension {n₁ * n₂} ℚ ↥(ℚ⟮ζ ^ n₁⟯ ⊔ ℚ⟮ζ ^ n₂⟯) := by
          rw [mul_comm, ← Nat.Coprime.lcm_eq_mul h.symm]
          exact IntermediateField.isCyclotomicExtension_lcm_sup ℚ⟮ζ ^ n₁⟯ ℚ⟮ζ ^ n₂⟯
        exact IntermediateField.isCyclotomicExtension_eq_of_eq _ _ (n₁ * n₂)
    have := NumberField.discr_eq_discr_pow_mul_discr_pow ℚ⟮ζ ^ n₁⟯ ℚ⟮ζ ^ n₂⟯
      (LinearDisjoint.of_isGalois_isCoprime_discr _ _ h₁)
      h₂
      (isCoprime_differentIdeal_of_isCoprime_discr _ h₁)
    rw [this, hK₁, hK₂]
    rw [Nat.div_pow, Nat.div_pow, ← Nat.mul_div_mul_comm,
      IsCyclotomicExtension.finrank (n := n₁) ℚ⟮ζ ^ n₂⟯,
      IsCyclotomicExtension.finrank (n := n₂) ℚ⟮ζ ^ n₁⟯, ← pow_mul, ← pow_mul, mul_comm n₂.totient,
      ← Nat.totient_mul h, ← mul_pow, mul_comm n₁]
    congr
    rw [← Finset.prod_pow, ← Finset.prod_pow]
    simp_rw [← pow_mul]
    rw [h.symm.primeFactors_mul, Finset.prod_union, Nat.totient_mul h.symm]
    simp_rw +contextual [Nat.div_mul_right_comm (Nat.sub_one_dvd_totient_of_mem_primeFactors _),
      mul_comm n₁.totient]
    exact h.symm.disjoint_primeFactors
    exact Polynomial.cyclotomic.irreducible_rat (NeZero.pos _)
    exact Polynomial.cyclotomic.irreducible_rat (NeZero.pos _)
    refine (Nat.pow_dvd_pow_iff ?_).mpr ?_
    exact Module.finrank_pos.ne'
    exact Nat.prod_primeFractors_pow_dvd_pow_totient n₂
    refine (Nat.pow_dvd_pow_iff ?_).mpr ?_
    exact Module.finrank_pos.ne'
    exact Nat.prod_primeFractors_pow_dvd_pow_totient n₁
    exact Nat.prod_primeFractors_pow_dvd_pow_totient n₁
    exact Nat.prod_primeFractors_pow_dvd_pow_totient n₂

theorem step1 (F₁ F₂ : Type*) [Field F₁] [Field F₂] [NumberField F₁] [NumberField F₂] {n₁ n₂ : ℕ}
    [NeZero n₁] [NeZero n₂] [h₁ : IsCyclotomicExtension {n₁} ℚ F₁] [h₂ : IsCyclotomicExtension {n₂} ℚ F₂]
    (h : n₁.Coprime n₂) : IsCoprime (discr F₁) (discr F₂) := by
  rw [Int.isCoprime_iff_nat_coprime, IsCyClotomicExtension.Rat.absdiscr F₁ n₁,
    IsCyClotomicExtension.Rat.absdiscr F₂ n₂]
  apply Nat.Coprime.coprime_div_left
  apply Nat.Coprime.coprime_div_right
  apply Nat.Coprime.pow_left
  apply Nat.Coprime.pow_right
  exact h
  exact Nat.prod_primeFractors_pow_dvd_pow_totient n₂
  exact Nat.prod_primeFractors_pow_dvd_pow_totient n₁

theorem step2 {E : Type*} [Field E] [NumberField E] (F₁ F₂ : IntermediateField ℚ E) {n₁ n₂ : ℕ}
    [NeZero n₁] [NeZero n₂] [IsCyclotomicExtension {n₁} ℚ F₁] [IsCyclotomicExtension {n₂} ℚ F₂]
    {ζ₁ : F₁} (hζ₁ : IsPrimitiveRoot ζ₁ n₁) (h₁ : Algebra.adjoin ℤ {hζ₁.toInteger} = ⊤)
    {ζ₂ : F₂} (hζ₂ : IsPrimitiveRoot ζ₂ n₂) (h₂ : Algebra.adjoin ℤ {hζ₂.toInteger} = ⊤)
    (h : n₁.Coprime n₂) (htop : F₁ ⊔ F₂ = ⊤) (ζ : E) (hζ : IsPrimitiveRoot ζ (n₁ * n₂)) :
    Algebra.adjoin ℤ {hζ.toInteger} = ⊤ := by
  have : IsGalois ℚ F₁ := IsCyclotomicExtension.isGalois {n₁} ℚ F₁
  have t₁ := step1 F₁ F₂ h
  have t₁' := NumberField.isCoprime_differentIdeal_of_isCoprime_discr E <| t₁
  have t₂ := NumberField.LinearDisjoint.of_isGalois_isCoprime_discr F₁ F₂ t₁
  have htop' : F₁.toSubalgebra ⊔ F₂.toSubalgebra = ⊤ := by
    simp [← sup_toSubalgebra_of_left, htop]
  have t₃ := Algebra.adjoin_pair_eq_top_of_isCoprime_differentialIdeal (A := ℤ) (C := 𝓞 E)
    (B₁ := 𝓞 F₁) (B₂ := 𝓞 F₂) (L₁ := F₁) (L₂ := F₂) t₂ htop' t₁' h₁ h₂
  rw [← t₃]
  replace hζ₁ : IsPrimitiveRoot hζ₁.toInteger n₁ := hζ₁.toInteger_isPrimitiveRoot
  replace hζ₁ := hζ₁.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F₁) (𝓞 E))
  replace hζ₂ : IsPrimitiveRoot hζ₂.toInteger n₂ := hζ₂.toInteger_isPrimitiveRoot
  replace hζ₂ := hζ₂.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F₂) (𝓞 E))
  have := IsPrimitiveRoot.adjoin_pair_eq ℤ hζ₁ hζ₂ (NeZero.ne _) (NeZero.ne _) (ζ := hζ.toInteger)
    ?_
  · rw [this]
  · rw [Nat.Coprime.lcm_eq_mul h]
    exact IsPrimitiveRoot.toInteger_isPrimitiveRoot hζ

theorem step3 {K : Type*} [Field K] [NumberField K] (n : ℕ) [hn : NeZero n]
    [hK : IsCyclotomicExtension {n} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    Algebra.adjoin ℤ {hζ.toInteger} = ⊤ := by
  induction n using Nat.recOnPrimeCoprime generalizing K hn with
  | zero => exact (neZero_zero_iff_false.mp hn).elim
  | prime_pow p k hp =>
    have : Fact (p.Prime) := ⟨hp⟩
    rw [← hζ.integralPowerBasis.adjoin_gen_eq_top, hζ.integralPowerBasis_gen]
  | coprime n₁ n₂ hn₁ hn₂ h hK₁ hK₂ =>
    have : NeZero n₁ := NeZero.of_gt hn₁
    have : NeZero n₂ := NeZero.of_gt hn₂
    have hζ₁ := hζ.pow (NeZero.pos _) (a := n₁) (b := n₂) rfl
    have := hζ₁.intermediateField_adjoin_isCyclotomicExtension ℚ
    have hζ₂' : IsPrimitiveRoot (AdjoinSimple.gen ℚ (ζ ^ n₁)) n₂ :=
      IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ₁
    replace hK₂ := @hK₂ ℚ⟮ζ ^ n₁⟯ _ _ _ _ (AdjoinSimple.gen _ _) hζ₂'
    have hζ₂ := hζ.pow (NeZero.pos _) (a := n₂) (b := n₁) (by rw [mul_comm])
    have := hζ₂.intermediateField_adjoin_isCyclotomicExtension ℚ
    have hζ₁' : IsPrimitiveRoot (AdjoinSimple.gen ℚ (ζ ^ n₂)) n₁ :=
      IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ₂
    replace hK₁ := @hK₁ ℚ⟮ζ ^ n₂⟯ _ _ _ _ (AdjoinSimple.gen _ _) hζ₁'
    have htop : ℚ⟮ζ ^ n₂⟯ ⊔ ℚ⟮ζ ^ n₁⟯ = ⊤ := by
        have : IsCyclotomicExtension {n₁ * n₂} ℚ (⊤ : IntermediateField ℚ K) :=
          hK.equiv _ _ _ topEquiv.symm
        have : IsCyclotomicExtension {n₁ * n₂} ℚ ↥(ℚ⟮ζ ^ n₂⟯ ⊔ ℚ⟮ζ ^ n₁⟯) := by
          rw [← Nat.Coprime.lcm_eq_mul h]
          exact IntermediateField.isCyclotomicExtension_lcm_sup ℚ⟮ζ ^ n₂⟯ ℚ⟮ζ ^ n₁⟯
        exact IntermediateField.isCyclotomicExtension_eq_of_eq _ _ (n₁ * n₂)
    have := step2 ℚ⟮ζ ^ n₂⟯ ℚ⟮ζ ^ n₁⟯ hζ₁' ?_ hζ₂' ?_ h ?_ ζ hζ -- ⟨ζ, ?_⟩ ?_
    · exact this
    · exact hK₁
    · exact hK₂
    · exact htop

#exit





-- theorem normalClosure_eq_adjoin_rootSet (F L : Type*) [Field F] [Field L] [Algebra F L]
--     [Normal F L] (α : L) :
--     normalClosure F (adjoin F {α}) L = adjoin F (Polynomial.rootSet (minpoly F α) L) := by
--   rw [normalClosure_def, ← biSup_adjoin_simple ((minpoly F α).rootSet L)]
--   let i : (adjoin F {α} →ₐ[F] L) ≃ {β : L | IsConjRoot F α β} := by
--     refine { toFun := ?_, invFun := ?_, left_inv := ?_, right_inv := ?_ }
--     · intro f
--       refine ⟨f (AdjoinSimple.gen F α), ?_⟩
--       let g := AlgHom.liftNormal f L
--       have : f (AdjoinSimple.gen F α) = g α := by
--         unfold g
--         have := AdjoinSimple.algebraMap_gen F α
--         have := AlgHom.congr_arg g this
--         rw [← this]
--         unfold g
--         rw [AlgHom.liftNormal_commutes]
--         simp
--       rw [this]
--       dsimp
--       rw?

--       sorry
--     · sorry
--     · sorry
--     · sorry
--   have : (minpoly F α).rootSet L = {β : L | IsConjRoot F α β} := sorry
--   -- isConjRoot_iff_mem_minpoly_rootSet
--   rw [this]

-- #exit

--   rw [normalClosure_def, ← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly_of_splits]
--   have (f : F⟮α⟯ →ₐ[F] L) : f.fieldRange = adjoin F {f (AdjoinSimple.gen F α)} := by
--     ext
--     simp
--     sorry
--   simp_rw [this]
--   rw [← adjoin_iUnion]
--   congr
--   rw [Set.range_eq_iUnion]
--   ext




--   sorry



-- theorem NumberField.discr_pow_dvd_discr (E F : Type*) [Field E] [Field F] [NumberField E]
--     [NumberField F] [Algebra E F] : discr E ^ Module.finrank E F ∣ discr F := by
--   have := congr_arg Ideal.absNorm
--     (differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 E) (𝓞 F))
--   rw [absNorm_differentIdeal (K := F), map_mul, Ideal.absNorm_algebraMap E F,
--     absNorm_differentIdeal (K := E)] at this
--   rw [← Int.dvd_natAbs, this, Nat.cast_mul, Nat.cast_pow, ← Int.mul_sign_self, mul_pow,
--     ← mul_assoc, mul_comm _ (discr E ^ _), mul_assoc]
--   exact Int.dvd_mul_right _ _




theorem step0 {E : Type*} [Field E] [CharZero E] (F₁ F₂ : IntermediateField ℚ E) [NumberField F₁]
    [NumberField F₂] (h : IsCoprime (discr F₁) (discr F₂)) (K : IntermediateField ℚ E)
    [NumberField K] [IsGalois ℚ K] (hK₁ : F₁ ≤ K)
    (hK₂ : ∀ p : ℕ, p.Prime → (p ∣ (discr K).natAbs ↔ p ∣ (discr F₁).natAbs)) :
    F₁.LinearDisjoint F₂ := by
  refine .of_le_left ?_ hK₁
  refine NumberField.LinearDisjoint.of_isGalois_isCoprime_discr K F₂ ?_
  rw [Int.isCoprime_iff_nat_coprime] at h ⊢
  apply Nat.coprime_of_dvd
  intro p hp
  specialize hK₂ p hp
  rw [hK₂]
  intro h'
  have := Nat.Coprime.of_dvd_left h' h
  rwa [hp.coprime_iff_not_dvd] at this

theorem step1 {E : Type*} [Field E] [NumberField E] (F₁ F₂ : IntermediateField ℚ E)
    (p : ℕ) (hp : p.Prime) :
    p ∣ (discr ↥(F₁ ⊔ F₂)).natAbs ↔ (p ∣ (discr F₁).natAbs ∨ p ∣ (discr F₂).natAbs) := by
  let _ : Algebra F₁ ↥(F₁ ⊔ F₂) := RingHom.toAlgebra (inclusion le_sup_left).toRingHom
  let _ : Algebra F₂ ↥(F₁ ⊔ F₂) := RingHom.toAlgebra (inclusion le_sup_right).toRingHom
  constructor
  · intro h
    refine Decidable.or_iff_not_imp_left.mpr fun h₁ ↦ ?_
    have h₂ := natAbs_discr_eq_absNorm_diffenrentIdeal_mul_natAbs_discr_pow F₁ ↥(F₁ ⊔ F₂)
    have h₃ : p ∣ Ideal.absNorm (differentIdeal (𝓞 F₁) (𝓞 ↥(F₁ ⊔ F₂))) := by
      rw [h₂, Nat.Prime.dvd_mul hp, Prime.dvd_pow_iff_dvd (Nat.prime_iff.mp hp)] at h
      simp_rw [h₁, or_false] at h
      exact h
      have : NoZeroSMulDivisors F₁ ↥(F₁ ⊔ F₂) := sorry
      exact Module.finrank_pos.ne'

    sorry
  · rintro (h | h)
    · exact Nat.dvd_trans h <| Int.natAbs_dvd_natAbs.mpr (discr_dvd_discr _ _)
    · exact Nat.dvd_trans h <| Int.natAbs_dvd_natAbs.mpr (discr_dvd_discr _ _)

-- theorem step2 {A : Type*} [Field A] [IsAlgClosed A] [CharZero A] (α : A) (hα : IsAlgebraic ℚ α)
--     [NumberField (adjoin ℚ {α})] (β : A) (hβ : IsConjRoot ℚ α β) (p : ℕ)
--     [NumberField (adjoin ℚ {α, β})] (hp : p.Prime) :
--     p ∣ (discr (adjoin ℚ {α, β})).natAbs ↔ p ∣ (discr (adjoin ℚ {α})).natAbs := by
--   have : NumberField (adjoin ℚ {β}) := sorry
--   have : NumberField ↥((adjoin ℚ {α}) ⊔ (adjoin ℚ {β})) := sorry
--   have main := step1 (adjoin ℚ {α}) (adjoin ℚ {β}) p hp
--   have : discr (adjoin ℚ {α}) = discr (adjoin ℚ {β}) := by
--     apply discr_eq_discr_of_algEquiv
--     refine minpoly.algEquiv hα hβ
--   rw [← this, or_self] at main
--   rw [← main]
--   have : discr ↥(adjoin ℚ {α, β}) = discr (↥(adjoin ℚ {α} ⊔ adjoin ℚ {β})) := by
--     congr!
--     all_goals rw [← adjoin_union, Set.singleton_union]
--   rw [this]

-- theorem step3 {A : Type*} [Field A] [NumberField A] (α : A) (S : Finset A) (hS₁ : S.Nonempty)
--     (hS₂ : ∀ β ∈ S, IsConjRoot ℚ α β) (p : ℕ) (hp : p.Prime) :
--     (p ∣ (discr (adjoin ℚ (S : Set A))).natAbs ↔ p ∣ (discr (adjoin ℚ {α})).natAbs) := by
--   induction hS₁ using Finset.Nonempty.cons_induction with
--   | singleton β =>
--       rw [Finset.coe_singleton]
--       simp at hS₂
--       rw [discr_eq_discr_of_algEquiv _ (minpoly.algEquiv (Algebra.IsAlgebraic.isAlgebraic α) hS₂)]
--   | cons β S hβ hS h_ind =>
--       rw [Finset.coe_cons, Set.insert_eq, adjoin_union, step1 _ _ _ hp, h_ind]
--       · simp at hS₂
--         rw [← discr_eq_discr_of_algEquiv _ (minpoly.algEquiv
--           (Algebra.IsAlgebraic.isAlgebraic α) hS₂.1), or_self]
--       · intro β hβ
--         apply hS₂
--         exact Finset.mem_cons_of_mem hβ

-- theorem step3' {E : Type*} [Field E] [NumberField E] (F : IntermediateField ℚ E)
--     (S : Finset (F →ₐ[ℚ] E)) (hS : S.Nonempty) (p : ℕ) (hp : p.Prime) :
--     p ∣ (discr ↥(sSup ((fun f : F →ₐ[ℚ] E ↦ f.fieldRange) '' S))).natAbs ↔
--       p ∣ (discr F).natAbs := by
--   have h (f : F →ₐ[ℚ] E) : discr f.fieldRange = discr F :=
--     discr_eq_discr_of_ringEquiv _ <| (RingHom.rangeRestrictFieldEquiv f.toRingHom).symm
--   induction hS using Finset.Nonempty.cons_induction with
--   | singleton a =>
--     rw [Finset.coe_singleton, Set.image_singleton, sSup_singleton, h]
--   | cons a s _ _ hi =>
--     rw [Finset.coe_cons, Set.image_insert_eq, sSup_insert, step1 _ _ _ hp, h]
--     exact or_iff_left_of_imp hi.1

theorem step4 {E : Type*} [Field E] [NumberField E] (F : Type*) [Field F] [NumberField F]
    [Algebra F E] {p : ℕ} (hp : p.Prime) :
    p ∣ (discr (normalClosure ℚ F E)).natAbs ↔ p ∣ (discr F).natAbs := by
  have hf (f : F →ₐ[ℚ] E) : discr f.fieldRange = discr F :=
    discr_eq_discr_of_ringEquiv _ <| (RingHom.rangeRestrictFieldEquiv f.toRingHom).symm
  have : Inhabited (F →ₐ[ℚ] E) := ⟨RingHom.equivRatAlgHom (algebraMap F E)⟩
  rw [normalClosure_def, iSup, ← Set.image_univ, ← Finset.coe_univ]
  have hS := (Finset.univ_nonempty (α := F →ₐ[ℚ] E))
  generalize Finset.univ (α := F →ₐ[ℚ] E) = S at hS
  induction hS using Finset.Nonempty.cons_induction with
  | singleton a => rw [Finset.coe_singleton, Set.image_singleton, sSup_singleton, hf]
  | cons a s _ _ hi =>
    rw [Finset.coe_cons, Set.image_insert_eq, sSup_insert, step1 _ _ _ hp, hf,
      or_iff_left_of_imp hi.1]


  -- refine step3' F Finset.univ ?_ p hp
  -- exact Finset.univ_nonempty

example {E : Type*} [Field E] [NumberField E] (F : IntermediateField ℚ E) :
    Inhabited (F →ₐ[ℚ] E) := by exact AlgHom.inhabited F

#exit

theorem step4 {A : Type*} [Field A] [NumberField A] [Normal ℚ A] (F : IntermediateField ℚ A)
    (p : ℕ) (hp : p.Prime) :
    ∃ N : IntermediateField ℚ A, F ≤ N ∧ IsGalois ℚ N ∧
      (p ∣ (discr (normalClosure ℚ F A)).natAbs ↔ p ∣ (discr F).natAbs) := by
  have : Finite (IntermediateField ℚ A) := by
    refine Field.finite_intermediateField_of_exists_primitive_element ℚ A ?_
    exact Field.exists_primitive_element ℚ A
  obtain ⟨α, rfl⟩ := Field.exists_primitive_element_of_finite_intermediateField ℚ A F
  let S := Polynomial.rootSet (minpoly ℚ α) A
  use adjoin ℚ (Polynomial.rootSet (minpoly ℚ α) A)
  refine ⟨?_, ?_, ?_⟩
  · apply adjoin.mono
    rw [Set.singleton_subset_iff, Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero_of_finite ℚ α, minpoly.aeval ℚ α⟩
  ·
    sorry
  · sorry

#exit

  have : Finite (IntermediateField ℚ A) := by
    refine Field.finite_intermediateField_of_exists_primitive_element ℚ A ?_
    exact Field.exists_primitive_element ℚ A
  obtain ⟨α, rfl⟩ := Field.exists_primitive_element_of_finite_intermediateField ℚ A F
  rw [normalClosure_def]






#exit

instance {K : Type*} [Field K] [NumberField K] : Finite (IntermediateField ℚ K) := by
  refine Field.finite_intermediateField_of_exists_primitive_element ℚ K ?_
  exact Field.exists_primitive_element ℚ K

-- Use Polynomial.rootSet
