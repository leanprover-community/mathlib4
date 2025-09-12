import Mathlib.FieldTheory.LinearDisjoint

set_option linter.style.header false

section Arithmetic

theorem Nat.sub_one_dvd_totient_of_mem_primeFactors {n p : ℕ} (hp : p ∈ n.primeFactors) :
    p - 1 ∣ n.totient := by
  rw [← Nat.totient_prime (Nat.prime_of_mem_primeFactors hp)]
  exact Nat.totient_dvd_of_dvd <| Nat.dvd_of_mem_primeFactors hp

theorem Nat.prod_primeFractors_pow_dvd_pow_totient (n : ℕ) :
    ∏ p ∈ n.primeFactors, p ^ (n.totient / (p - 1)) ∣ n ^ n.totient := by
  induction n using Nat.recOnPrimeCoprime with
  | zero => simp
  | prime_pow q k hq =>
    by_cases hk : k = 0
    · simp [hk]
    have h₁ : 0 < q - 1 := Nat.zero_lt_sub_of_lt <| Nat.Prime.one_lt hq
    rw [Nat.primeFactors_prime_pow hk hq, Finset.prod_singleton, Nat.totient_prime_pow hq
      (Nat.zero_lt_of_ne_zero hk), ← pow_mul, Nat.mul_div_left _ h₁]
    refine Nat.pow_dvd_pow q ?_
    rw [mul_comm k, mul_assoc]
    exact Nat.le_mul_of_pos_right _ <| Nat.mul_pos h₁ (Nat.zero_lt_of_ne_zero hk)
  | coprime a b _ _ h ha hb =>
    replace ha := pow_dvd_pow_of_dvd ha b.totient
    replace hb := pow_dvd_pow_of_dvd hb a.totient
    rw [Nat.totient_mul h, mul_pow, pow_mul, pow_mul, pow_right_comm b]
    convert mul_dvd_mul ha hb using 1
    simp_rw +contextual [h.primeFactors_mul, Finset.prod_union h.disjoint_primeFactors,
        ← Finset.prod_pow, ← pow_mul,
        Nat.div_mul_right_comm (sub_one_dvd_totient_of_mem_primeFactors _), mul_comm b.totient]

end Arithmetic

open Module

theorem IntermediateField.LinearDisjoint.finrank_left_eq_finrank {F E : Type*} [Field F] [Field E]
    [Algebra F E] {A B : IntermediateField F E} [Module.Finite F A]
    (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤) : finrank A E = finrank F B := by
  have := finrank_mul_finrank F A E ▸ finrank_top F E ▸ h₂ ▸ h₁.finrank_sup
  rwa [mul_right_inj' (finrank_pos.ne')] at this

theorem IntermediateField.LinearDisjoint.finrank_right_eq_finrank {F E : Type*} [Field F] [Field E]
    [Algebra F E] {A B : IntermediateField F E} [Module.Finite F B]
    (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤) : finrank B E = finrank F A :=
  h₁.symm.finrank_left_eq_finrank (by rwa [sup_comm])

#exit
section cyclotomic

open Algebra

theorem IsPrimitiveRoot.mul_isPrimitiveRoot_of_coprime {M : Type*} [CommMonoid M] {k : ℕ}
    {ζ ζ' : M} {k' : ℕ} (hζ : IsPrimitiveRoot ζ k) (hζ' : IsPrimitiveRoot ζ' k')
    (h : k.Coprime k') :
    IsPrimitiveRoot (ζ * ζ') (k * k') := by
  convert IsPrimitiveRoot.orderOf (ζ * ζ')
  rw [hζ.eq_orderOf, hζ'.eq_orderOf] at h ⊢
  exact (Commute.orderOf_mul_eq_mul_orderOf_of_coprime (Commute.all ζ ζ') h).symm

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (T₁ T₂ : Subalgebra A B)
  (n₁ n₂ : ℕ) [hcycl₁ : IsCyclotomicExtension {n₁} A T₁] [hcycl₂ : IsCyclotomicExtension {n₂} A T₂]

theorem Subalgebra.isCyclotomicExtension_iff [IsDomain B] {T : Subalgebra A B} {S : Set ℕ} :
    IsCyclotomicExtension S A T ↔
      (∀ n, n ∈ S → n ≠ 0 → ∃ b : B, IsPrimitiveRoot b n) ∧
        T = adjoin A {b : B | ∃ s ∈ S, s ≠ 0 ∧ b ^ s = 1} := by
  rw [IsCyclotomicExtension.iff_adjoin_eq_top, eq_comm]
  have := Subalgebra.map_injective (f := IsScalarTower.toAlgHom A T B)
    (FaithfulSMul.algebraMap_injective T B)
  rw [← this.eq_iff, AlgHom.map_adjoin, IsScalarTower.coe_toAlgHom',
    show Subalgebra.map (IsScalarTower.toAlgHom A T B) ⊤ = T by aesop]
  constructor
  · rintro ⟨h₁, h₂⟩
    rw [h₂]
    refine ⟨?_, ?_⟩
    · intro n hn₁ hn₂
      obtain ⟨ζ, hζ⟩ := h₁ n hn₁ hn₂
      exact ⟨algebraMap T B ζ, hζ.map_of_injective (FaithfulSMul.algebraMap_injective T B)⟩
    congr
    ext x
    simp_rw [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨_, ⟨n, hn₁, hn₂, hx⟩, rfl⟩
      exact ⟨n, hn₁, hn₂, by rw [← map_pow, hx, map_one]⟩
    · rintro ⟨n, hn₁, hn₂, hx⟩
      obtain ⟨ζ, hζ⟩ := h₁ n hn₁ hn₂
      have hζ' := hζ.map_of_injective (FaithfulSMul.algebraMap_injective T B)
      have := NeZero.mk hn₂
      obtain ⟨k, _, rfl⟩ := hζ'.eq_pow_of_pow_eq_one hx
      exact ⟨ζ ^ k, ⟨n, hn₁, hn₂, by rw [pow_right_comm, hζ.pow_eq_one, one_pow]⟩, rfl⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨?_, ?_⟩
    · intro n hn₁ hn₂
      obtain ⟨ζ, hζ⟩ := h₁ n hn₁ hn₂
      refine ⟨⟨ζ, ?_⟩, IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ⟩
      rw [h₂]
      apply subset_adjoin -- Algebra.mem_adjoin_of_mem
      exact ⟨n, hn₁, hn₂, hζ.pow_eq_one⟩
    · nth_rewrite 1 [h₂]
      congr
      ext x
      simp_rw [Set.mem_image, Set.mem_setOf_eq]
      constructor
      · rintro ⟨n, hn₁, hn₂, hx⟩
        have := NeZero.mk hn₂
        obtain ⟨ζ, hζ⟩ := h₁ n hn₁ hn₂
        obtain ⟨k, _, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
        refine ⟨⟨ζ ^ k, ?_⟩, ⟨n, hn₁, hn₂, (Subalgebra.coe_eq_one T).mp hx⟩, rfl⟩
        rw [h₂]
        apply subset_adjoin
        refine ⟨n, hn₁, hn₂, hx⟩
      · rintro ⟨_, ⟨n, hn₁, hn₂, hx⟩, rfl⟩
        exact ⟨n, hn₁, hn₂, by rw [← map_pow, hx, map_one]⟩

variable {n₁ n₂} in
theorem Subalgebra.isCyclotomicExtension_le_of_dvd [IsDomain B] (h : n₁ ∣ n₂) (h' : n₂ ≠ 0) :
    T₁ ≤ T₂ := by
  rw [Subalgebra.isCyclotomicExtension_iff] at hcycl₁ hcycl₂
  rw [hcycl₁.2, hcycl₂.2]
  apply adjoin_mono
  rintro x ⟨n, rfl, hn₁, hx⟩
  obtain ⟨c, rfl⟩ := h
  exact ⟨n * c, rfl, h', by rw [pow_mul, hx, one_pow]⟩

theorem Subalgebra.isCyclotomicExtension_lcm_sup [NeZero n₁] [NeZero n₂] :
    IsCyclotomicExtension {n₁.lcm n₂} A (T₁ ⊔ T₂ : Subalgebra A B) where
  exists_isPrimitiveRoot := by
    intro n h hn
    obtain ⟨ζ₁, hζ₁⟩ := hcycl₁.1 rfl (NeZero.ne n₁)
    obtain ⟨ζ₂, hζ₂⟩ := hcycl₂.1 rfl (NeZero.ne n₂)
    let _ : Algebra T₁ ↥(T₁ ⊔ T₂) := (Subalgebra.inclusion le_sup_left).toAlgebra
    let _ : Algebra T₂ ↥(T₁ ⊔ T₂) := (Subalgebra.inclusion le_sup_right).toAlgebra
    have : FaithfulSMul T₁ ↥(T₁ ⊔ T₂) := Subalgebra.inclusion.faithfulSMul le_sup_left
    have : FaithfulSMul T₂ ↥(T₁ ⊔ T₂) := Subalgebra.inclusion.faithfulSMul le_sup_right
    replace hζ₁ := hζ₁.map_of_injective (FaithfulSMul.algebraMap_injective T₁ ↥(T₁ ⊔ T₂))
    replace hζ₂ := hζ₂.map_of_injective (FaithfulSMul.algebraMap_injective T₂ ↥(T₁ ⊔ T₂))
    exact ⟨_, h ▸ IsPrimitiveRoot.pow_mul_pow_lcm hζ₁ hζ₂ (NeZero.ne n₁) (NeZero.ne n₂)⟩
  adjoin_roots := by
    rintro ⟨x, hx⟩
    induction hx using adjoin_induction with
    | mem x h =>
        let _ : Algebra T₁ ↥(T₁ ⊔ T₂) := (Subalgebra.inclusion le_sup_left).toAlgebra
        let _ : Algebra T₂ ↥(T₁ ⊔ T₂) := (Subalgebra.inclusion le_sup_right).toAlgebra
        -- Use IsCyclotomicExtension.iff_singleton
        obtain h | h := h
        · have := Set.mem_image_of_mem (IsScalarTower.toAlgHom A T₁ ↥(T₁ ⊔ T₂)) <| hcycl₁.2 ⟨_, h⟩
          rw [← Subalgebra.coe_map, ← adjoin_algebraMap, SetLike.mem_coe] at this
          refine adjoin_mono ?_ this
          rintro _ ⟨z, ⟨n₁, rfl, ⟨hn₁, hn₁'⟩⟩, rfl⟩
          refine ⟨_, rfl, Nat.lcm_ne_zero hn₁ (NeZero.ne n₂), ?_⟩
          obtain ⟨c, hc⟩ := Nat.dvd_lcm_left n₁ n₂
          rw [← map_pow, hc, pow_mul, hn₁', one_pow, map_one]
        · have := Set.mem_image_of_mem (IsScalarTower.toAlgHom A T₂ ↥(T₁ ⊔ T₂)) <| hcycl₂.2 ⟨_, h⟩
          rw [← Subalgebra.coe_map, ← adjoin_algebraMap, SetLike.mem_coe] at this
          refine adjoin_mono ?_ this
          rintro _ ⟨z, ⟨n₂, rfl, ⟨hn₂, hn₂'⟩⟩, rfl⟩
          refine ⟨_, rfl,  Nat.lcm_ne_zero (NeZero.ne n₁) hn₂, ?_⟩
          obtain ⟨c, hc⟩ := Nat.dvd_lcm_right n₁ n₂
          rw [← map_pow, hc, pow_mul, hn₂', one_pow, map_one]
    | algebraMap r =>
        rw [Algebra.mem_adjoin_iff]
        apply Subring.subset_closure
        apply Set.mem_union_left
        exact Set.mem_range_self r
    | add _ _ _ _ hx hy => simpa [AddMemClass.mk_add_mk] using Subalgebra.add_mem  _ hx hy
    | mul _ _ _ _ hx hy => simpa [MulMemClass.mk_mul_mk] using Subalgebra.mul_mem  _ hx hy

end cyclotomic

-- open nonZeroDivisors NumberField

-- theorem Submodule.span_mono_left {R S M : Type*} [Semiring R] [Semiring S] [AddCommMonoid M]
--     [Module R M] [Module S M] [SMul R S] [IsScalarTower R S M] {s : Set M} :
--     (span R s : Set M) ≤ span S s := by
--   rw [← Submodule.span_span_of_tower R S]
--   exact Submodule.subset_span

-- theorem differentIdeal_ne_bot' (A K B L : Type*) [CommRing A] [Field K] [Algebra A K]
--     [IsFractionRing A K] [CommRing B] [Field L] [Algebra B L] [IsFractionRing B L]
--     [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
--     [IsDomain A] [IsIntegrallyClosed A] [IsDedekindDomain B] [NoZeroSMulDivisors A B]
--     [Module.Finite A B] [Algebra.IsSeparable K L] :
--     differentIdeal A B ≠ ⊥ := by
--   have : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
--     IsIntegralClosure.isLocalization _ K _ _
--   have : FiniteDimensional K L := Module.Finite_of_isLocalization A B _ _ A⁰
--   rw [ne_eq, ← FractionalIdeal.coeIdeal_inj (K := L), coeIdeal_differentIdeal (K := K)]
--   simp

-- open nonZeroDivisors Algebra FractionalIdeal
-- section numberfield

-- open NumberField

-- variable (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
--   [NumberField M] [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

-- theorem differentIdeal_eq_differentIdeal_mul_differentIdeal' :
--     differentIdeal (𝓞 K) (𝓞 M) =
--        differentIdeal (𝓞 L) (𝓞 M) *
--         (differentIdeal (𝓞 K) (𝓞 L)).map (algebraMap (𝓞 L) (𝓞 M)) :=
--   differentIdeal_eq_differentIdeal_mul_differentIdeal (𝓞 K) K L (𝓞 L) (𝓞 M) M

-- end numberfield

namespace IntermediateField.LinearDisjoint

open Submodule IntermediateField

variable {A K C M : Type*} [CommRing A] [Field K] [CommRing C] [Field M] [Algebra K M]
  [Algebra A K] [IsFractionRing A K] [Algebra C M] [Algebra A M] [IsScalarTower A K M]
  {L₁ L₂ : IntermediateField K M} {B₁ B₂ : Type*} [CommRing B₁] [CommRing B₂] [Algebra B₁ L₁]
  [Algebra B₂ L₂] [Algebra A B₂] [Algebra B₁ C] [Algebra B₂ C] [Algebra B₁ M] [Algebra B₂ M]
  [IsScalarTower A B₂ L₂] [IsScalarTower B₁ C M] [IsScalarTower B₂ C M] [IsScalarTower B₁ L₁ M]
  [IsScalarTower B₂ L₂ M] [Algebra.IsSeparable K M] [FiniteDimensional K M]

-- variable (A C B₁ B₂) in
-- theorem traceDual_le_span_traceDual' [IsLocalization (algebraMapSubmonoid B₂ A⁰) L₂]
--     [Module.Free A B₂] [Module.Finite A B₂]
--     (h₁ : L₁.LinearDisjoint L₂) (h₂ : L₁ ⊔ L₂ = ⊤) :
--     traceDual B₁ L₁ (1 : Submodule C M) ≤
--       span C (algebraMap L₂ M '' (traceDual A K (1 : Submodule B₂ L₂))) := by
--   intro x hx
--   let b₂ := (Module.Free.chooseBasis A B₂).localizationLocalization K A⁰ L₂
--   have h₂' : L₁.toSubalgebra ⊔ L₂.toSubalgebra = ⊤ := by
--     simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg toSubalgebra h₂
--   let bM : Basis _ L₁ M := h₁.basisOfBasisRight h₂' b₂.traceDual
--   rw [← bM.sum_repr x]
--   refine Submodule.sum_mem _ fun i _ ↦ ?_
--   rsuffices ⟨c, hc⟩ : bM.repr x i ∈ (algebraMap B₁ L₁).range := by
--     have : (h₁.basisOfBasisRight h₂' b₂).traceDual = bM := by
--       refine (DFunLike.ext'_iff.trans Basis.traceDual_eq_iff).mpr fun _ _ ↦ ?_
--       rw [h₁.basisOfBasisRight_apply, h₁.basisOfBasisRight_apply, traceForm_apply, ← map_mul,
--         h₁.trace_algebraMap_eq h₂, b₂.trace_traceDual_mul, MonoidWithZeroHom.map_ite_one_zero]
--     rw [← this, (h₁.basisOfBasisRight h₂' b₂).traceDual_repr_apply x i]
--     refine mem_traceDual.mp hx _ ?_
--     rw [mem_one, h₁.basisOfBasisRight_apply, Basis.localizationLocalization_apply,
--       ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply B₂ C M]
--     exact ⟨_, rfl⟩
--   rw [← hc, ← algebra_compatible_smul L₁, algebra_compatible_smul C]
--   refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
--   refine ⟨b₂.traceDual i, ?_, by rw [h₁.basisOfBasisRight_apply]⟩
--   rw [SetLike.mem_coe, ← restrictScalars_mem A, traceDual_span_of_basis A _ b₂
--     (by rw [Basis.localizationLocalization_span K A⁰ L₂]; ext; simp)]
--   exact Submodule.subset_span <| Set.mem_range_self i

open Algebra

open scoped nonZeroDivisors

variable (A C B₁ B₂) in
theorem traceDual_le_span_traceDual [IsLocalization (algebraMapSubmonoid B₂ A⁰) L₂]
    [Module.Free A B₂] [Module.Finite A B₂]
    (h₁ : L₁.LinearDisjoint L₂) (h₂ : L₁ ⊔ L₂ = ⊤) :
    (traceDual B₁ L₁ (1 : Submodule C M)).restrictScalars B₁ ≤
      span B₁ (algebraMap L₂ M '' (traceDual A K (1 : Submodule B₂ L₂))) := by
  intro x hx
  let b₂ := (Module.Free.chooseBasis A B₂).localizationLocalization K A⁰ L₂
  have h₂' : L₁.toSubalgebra ⊔ L₂.toSubalgebra = ⊤ := by
    simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg toSubalgebra h₂
  let bM : Basis _ L₁ M := h₁.basisOfBasisRight h₂' b₂.traceDual
  rw [← bM.sum_repr x]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rsuffices ⟨c, hc⟩ : bM.repr x i ∈ (algebraMap B₁ L₁).range := by
    have : (h₁.basisOfBasisRight h₂' b₂).traceDual = bM := by
      refine (DFunLike.ext'_iff.trans Basis.traceDual_eq_iff).mpr fun _ _ ↦ ?_
      rw [h₁.basisOfBasisRight_apply, h₁.basisOfBasisRight_apply, traceForm_apply, ← map_mul,
        h₁.trace_algebraMap_eq h₂, b₂.trace_traceDual_mul, MonoidWithZeroHom.map_ite_one_zero]
    rw [← this, (h₁.basisOfBasisRight h₂' b₂).traceDual_repr_apply x i]
    refine mem_traceDual.mp hx _ ?_
    rw [mem_one, h₁.basisOfBasisRight_apply, Basis.localizationLocalization_apply,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply B₂ C M]
    exact ⟨_, rfl⟩
  rw [← hc, ← algebra_compatible_smul L₁]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  refine ⟨b₂.traceDual i, ?_, by rw [h₁.basisOfBasisRight_apply]⟩
  rw [SetLike.mem_coe, ← restrictScalars_mem A, traceDual_span_of_basis A _ b₂
    (by rw [Basis.localizationLocalization_span K A⁰ L₂]; ext; simp)]
  exact Submodule.subset_span <| Set.mem_range_self i

variable [IsDomain A] [IsDomain B₁]
  [IsIntegrallyClosed A] [IsIntegrallyClosed B₁] [IsDedekindDomain B₂] [IsDedekindDomain C]
  [IsFractionRing B₁ L₁] [IsFractionRing B₂ L₂] [IsFractionRing C M]
  [IsIntegralClosure B₂ A L₂] [IsIntegralClosure C B₂ M] [IsIntegralClosure C B₁ M]
  [NoZeroSMulDivisors B₁ C] [NoZeroSMulDivisors B₂ C]

-- variable (A B₁ B₂ C) in
-- -- That's essentially a weaker version of `traceDual_le_span_traceDual'`
-- theorem differentIdeal_dvd_differentIdeal_map [Module.Free A B₂] [Module.Finite A B₂]
--     (h₁ : L₁.LinearDisjoint L₂) (h₂ : L₁ ⊔ L₂ = ⊤) :
--     differentIdeal B₁ C ∣ (differentIdeal A B₂).map (algebraMap B₂ C) := by
--   have := IsIntegralClosure.isLocalization A K L₂ B₂
--   have := IsIntegralClosure.isLocalization B₂ L₂ M C
--   rw [Ideal.dvd_iff_le, ← coeIdeal_le_coeIdeal' C⁰ (P := M) le_rfl, coeIdeal_differentIdeal B₁ L₁,
--     le_inv_comm _ (by simp), ← extended_coeIdeal_eq_map_algebraMap L₂ M, ← extended_inv,
--     coeIdeal_differentIdeal A K, inv_inv, ← coe_le_coe, coe_dual_one, coe_extended_eq_span,
--     ← coeToSet_coeToSubmodule, coe_dual_one]
--   · convert traceDual_le_span_traceDual A C B₁ B₂ h₁ h₂
--     exact (IsLocalization.algebraMap_eq_map_map_submonoid B₂⁰ C L₂ M).symm
--   · exact coeIdeal_ne_zero.mpr <| differentIdeal_ne_bot' A K B₂ L₂
--   · exact coeIdeal_ne_zero.mpr <| Ideal.map_ne_bot_of_ne_bot <| differentIdeal_ne_bot' A K B₂ L₂

variable [Algebra A B₁] [IsDedekindDomain B₁] [NoZeroSMulDivisors A B₁]
  [Algebra A C] [IsScalarTower A B₁ L₁] [IsScalarTower A C M] [IsIntegralClosure B₁ A L₁]
  [IsIntegralClosure C A M] [NoZeroSMulDivisors A C] [IsScalarTower K L₂ M] [IsScalarTower K L₁ M]

-- theorem differentIdeal_map_eq_differentIdeal [Module.Free A B₁] [Module.Finite A B₁]
--     [Module.Free A B₂] [Module.Finite A B₂] (h₁ : L₁.LinearDisjoint L₂) (h₂ : L₁ ⊔ L₂ = ⊤)
--     (h₃ : IsCoprime ((differentIdeal A B₁).map (algebraMap B₁ C))
--       ((differentIdeal A B₂).map (algebraMap B₂ C))) :
--     (differentIdeal A B₁).map (algebraMap B₁ C) = differentIdeal B₂ C := by
--   have := IsIntegralClosure.isLocalization B₁ L₁ M C
--   have := IsIntegralClosure.isLocalization B₂ L₂ M C
--   have main := (differentIdeal_eq_differentIdeal_mul_differentIdeal
--     A K L₁ B₁ C M).symm.trans (differentIdeal_eq_differentIdeal_mul_differentIdeal A K L₂ B₂ C M)
--   apply dvd_antisymm'
--   · have h' : IsCoprime (differentIdeal B₂ C) (differentIdeal B₁ C) := by
--       refine (h₃.of_isCoprime_of_dvd_right ?_).of_isCoprime_of_dvd_left ?_
--       · exact differentIdeal_dvd_differentIdeal_map A C B₁ B₂ h₁ h₂
--       · exact differentIdeal_dvd_differentIdeal_map A C B₂ B₁ h₁.symm (by rwa [sup_comm])
--     exact h'.dvd_of_dvd_mul_left (dvd_of_mul_right_eq _ main.symm)
--   · exact h₃.dvd_of_dvd_mul_right (dvd_of_mul_left_eq _ main)

open FractionalIdeal

variable (A C B₁ B₂) in
theorem traceDual_eq_span_traceDual [Module.Finite A B₂] [Module.Free A B₂]
    [NoZeroSMulDivisors A B₂] (h₁ : L₁.LinearDisjoint L₂) (h₂ : L₁ ⊔ L₂ = ⊤)
    (h₃ : IsCoprime ((differentIdeal A B₁).map (algebraMap B₁ C))
      ((differentIdeal A B₂).map (algebraMap B₂ C))) :
    span B₁ (algebraMap L₂ M '' (traceDual A K (1 : Submodule B₂ L₂))) =
      (traceDual B₁ L₁ (1 : Submodule C M)).restrictScalars B₁ := by
  apply le_antisymm
  · suffices span C (algebraMap L₂ M '' (traceDual A K (1 : Submodule B₂ L₂))) ≤
        traceDual B₁ L₁ (1 : Submodule C M) by
      refine SetLike.coe_subset_coe.mp (subset_trans ?_ this)
      rw [← Submodule.span_span_of_tower B₁ C]
      exact Submodule.subset_span
    have := IsIntegralClosure.isLocalization B₂ L₂ M C
    rw [← coe_dual_one, coeToSet_coeToSubmodule, ← coe_extended_eq_span_algebraMap, ← coe_dual_one,
      coe_le_coe, ← inv_inv (dual B₁ L₁ 1), ← le_inv_comm (inv_ne_zero (by simp)),
      ← extended_inv _ (by simp), ← coeIdeal_differentIdeal A K, ← coeIdeal_differentIdeal B₁ L₁,
      extended_coeIdeal_eq_map_algebraMap L₂ M, coeIdeal_le_coeIdeal' _ le_rfl, ← Ideal.dvd_iff_le]
    · have := (differentIdeal_eq_differentIdeal_mul_differentIdeal A K L₂ B₂ C M).symm.trans
          (differentIdeal_eq_differentIdeal_mul_differentIdeal A K L₁ B₁ C M)
      exact h₃.symm.dvd_of_dvd_mul_right (dvd_of_mul_left_eq _ this)
    · exact extended_ne_zero _ _ (FaithfulSMul.algebraMap_injective _ _) (by simp)
  · have := IsIntegralClosure.isLocalization A K L₂ B₂
    exact traceDual_le_span_traceDual A C B₁ B₂ h₁ h₂

variable (A C B₁ B₂) in
theorem span_eq_range
    [IsScalarTower A L₂ M]
    [IsScalarTower A B₁ M]
    [Module.Free A B₂]
    [Module.Finite A B₂]
    [NoZeroSMulDivisors A B₂]
    (h₁ : L₁.LinearDisjoint L₂) (h₂ : L₁ ⊔ L₂ = ⊤)
    (h₃ : IsCoprime ((differentIdeal A B₁).map (algebraMap B₁ C))
      ((differentIdeal A B₂).map (algebraMap B₂ C)))
    {ι : Type*} (b : Basis ι K L₂)
    (hb : span A (Set.range b) = (1 : Submodule B₂ L₂).restrictScalars A) :
    span B₁ (Set.range (algebraMap L₂ M ∘ b)) =
      LinearMap.range (IsScalarTower.toAlgHom B₁ C M) := by
  classical
  have : Finite ι := Module.Finite.finite_basis b
  have h_main : (traceDual B₁ L₁ (1 : Submodule C M)).restrictScalars B₁ =
      span B₁ (algebraMap L₂ M '' (traceDual A K (1 : Submodule B₂ L₂))) :=
    (traceDual_eq_span_traceDual A C B₁ B₂ h₁ h₂ h₃).symm
  convert congr_arg (Submodule.restrictScalars B₁) <|
    congr_arg coeToSubmodule <| (1 : FractionalIdeal C⁰ M).dual_dual B₁ L₁
  · rw [coe_dual _ _ (by simp), coe_dual_one]
    rw [restrictScalars_traceDual, h_main]
--    have : IsLocalization (algebraMapSubmonoid B₂ A⁰) L₂ :=
--      IsIntegralClosure.isLocalization A K L₂ B₂
--    let b₂ := b.localizationLocalization K A⁰ L₂
    have := Submodule.traceDual_span_of_basis A (1 : Submodule B₂ L₂) b ?_
    · rw [← Submodule.coe_restrictScalars A, this, ← IsScalarTower.coe_toAlgHom' A L₂ M,
        ← map_coe, map_span, span_span_of_tower, IsScalarTower.coe_toAlgHom', ← Set.range_comp]
      have h₂' : L₁.toSubalgebra ⊔ L₂.toSubalgebra = ⊤ := by
        simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg toSubalgebra h₂
      have : algebraMap L₂ M ∘ b.traceDual = (h₁.basisOfBasisRight h₂' b).traceDual := by
        rw [eq_comm, Basis.traceDual_eq_iff]
        intro i j
        simp only [Function.comp_apply, basisOfBasisRight_apply, traceForm_apply]
        rw [← map_mul, h₁.trace_algebraMap_eq h₂]
        rw [b.trace_traceDual_mul i j, MonoidWithZeroHom.map_ite_one_zero]
      rw [this, (traceForm L₁ M).dualSubmodule_span_of_basis (traceForm_nondegenerate L₁ M),
        ← Basis.traceDual_def, Basis.traceDual_traceDual]
      congr!
      ext
      rw [Function.comp_apply, basisOfBasisRight_apply]
    · rw [hb]
  · ext; simp

end LinearDisjoint
section NumberField

open NumberField Submodule

variable {K : Type*} [Field K] [NumberField K] (F₁ F₂ : IntermediateField ℚ K)
  (h₁ : F₁.LinearDisjoint F₂) (h₂ : F₁ ⊔ F₂ = ⊤) (h₃ : IsCoprime (discr F₁) (discr F₂))

example : (algebraMap (𝓞 F₁) (𝓞 K)).range ⊔ (algebraMap (𝓞 F₂) (𝓞 K)).range = ⊤ := by
    let b₂ := integralBasis F₂
    have : span (𝓞 F₁) (Set.range (algebraMap F₂ K ∘ b₂)) =
        LinearMap.range (IsScalarTower.toAlgHom (𝓞 F₁) (𝓞 K) K) := by
      apply IntermediateField.LinearDisjoint.span_eq_range ℤ (𝓞 K) (𝓞 F₁) (𝓞 F₂) h₁ h₂
      · obtain ⟨u, v, h⟩ := h₃
        rw [Ideal.isCoprime_iff_exists]
        refine ⟨algebraMap ℤ (𝓞 K) (u * discr F₁), ?_,
          algebraMap ℤ (𝓞 K) (v * discr F₂), ?_, by rw [← map_add, h, map_one]⟩
        · rw [IsScalarTower.algebraMap_apply ℤ (𝓞 F₁) (𝓞 K)]
          apply Ideal.mem_map_of_mem
          simp only [algebraMap_int_eq, eq_intCast, Int.cast_mul]
          exact Ideal.mul_mem_left _ _ <| discr_mem_differentIdeal
        · rw [IsScalarTower.algebraMap_apply ℤ (𝓞 F₂) (𝓞 K)]
          apply Ideal.mem_map_of_mem
          simp only [algebraMap_int_eq, eq_intCast, Int.cast_mul]
          exact Ideal.mul_mem_left _ _ <| discr_mem_differentIdeal
      · ext; simp [b₂, mem_span_integralBasis]
    sorry

end NumberField

end IntermediateField

section misc

variable {F E : Type*} [Field F] [Field E] [Algebra F E] (K L : IntermediateField F E)
  [FiniteDimensional F E] [hN : Normal F K] [Algebra.IsSeparable F K] (h : K ⊓ L = ⊥)

open IntermediateField

example : K.LinearDisjoint L := by
  apply LinearDisjoint.of_finrank_sup
  let hA : Algebra L ↥(K ⊔ L) := (inclusion le_sup_right).toAlgebra
  let hM : Module L ↥(K ⊔ L) := hA.toModule
  rw [← Module.finrank_mul_finrank F L ↥(K ⊔ L), mul_comm, mul_left_inj' sorry]
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element F K
  let T := minpoly F θ
  have hT : T.IsSplittingField F K := by
    refine isSplittingField_iff_intermediateField.mpr ⟨?_, ?_⟩
    · exact Normal.splits hN θ
    · have : θ ∈ T.rootSet K := by
        refine Polynomial.mem_rootSet'.mpr ⟨?_, minpoly.aeval F θ⟩
        · sorry
      rw [eq_top_iff]
      refine le_of_eq_of_le hθ.symm ?_
      apply adjoin.mono
      exact Set.singleton_subset_iff.mpr this
  let T' := Polynomial.map (algebraMap F L) T
  have t₁ : T'.IsSplittingField L ↥(K ⊔ L) := by
    rw [isSplittingField_iff_intermediateField]
    refine ⟨?_, ?_⟩
    · sorry
    · sorry
  have : Normal L ↥(K ⊔ L) := Normal.of_isSplittingField (F := L) (E := ↥(K ⊔ L)) T'
  have : Algebra.IsSeparable L ↥(K ⊔ L) := by
    exact?
    sorry
  let r : (↥(K ⊔ L) ≃ₐ[L] ↥(K ⊔ L)) ≃ (K ≃ₐ[F] K) := sorry
  have t₂ : IsGalois L ↥(K ⊔ L) := IsGalois.mk
  have : FiniteDimensional ↥L ↥(K ⊔ L) := sorry
  have : IsGalois F K := sorry
  rw [← IsGalois.card_aut_eq_finrank L ↥(K ⊔ L), ← IsGalois.card_aut_eq_finrank F K]
  exact Fintype.card_congr r







end misc

section discr

open NumberField IntermediateField

theorem NumberField.discr_pow_dvd_discr (E F : Type*) [Field E] [Field F] [NumberField E]
    [NumberField F] [Algebra E F] :
    discr E ^ Module.finrank E F ∣ discr F := by
  have := congr_arg Ideal.absNorm
    (differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ ℚ E (𝓞 E) (𝓞 F) F)
  rw [absNorm_differentIdeal (K := F), map_mul, Ideal.absNorm_algebraMap E F,
    absNorm_differentIdeal (K := E)] at this
  rw [← Int.dvd_natAbs, this, Nat.cast_mul, Nat.cast_pow, ← Int.mul_sign_self, mul_pow,
    ← mul_assoc, mul_comm _ (discr E ^ _), mul_assoc]
  exact Int.dvd_mul_right _ _

theorem NumberField.discr_dvd_discr (E F : Type*) [Field E] [Field F] [NumberField E]
    [NumberField F] [Algebra E F] :
    discr E ∣ discr F :=
  dvd_trans (dvd_pow_self _ (Nat.ne_zero_of_lt Module.finrank_pos)) (discr_pow_dvd_discr E F)

example {E : Type*} [Field E] [NumberField E] (F₁ F₂ : IntermediateField ℚ E)
    (h : IsCoprime (discr F₁) (discr F₂)) :
    F₁.LinearDisjoint F₂ := by
  apply LinearDisjoint.of_basis_left (integralBasis F₁)




  sorry


end discr

variable (n₁ n₂ : ℕ) {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {n₁ * n₂} ℚ K]
  (F₁ F₂ : IntermediateField ℚ K) [IsCyclotomicExtension {n₁} ℚ F₁]
  [IsCyclotomicExtension {n₂} ℚ F₂] {ζ₁ : F₁} {ζ₂ : F₂} (hζ₁ : IsPrimitiveRoot ζ₁ n₁)
  (hζ₂ : IsPrimitiveRoot ζ₂ n₂) (hc₁ : IsIntegralClosure (adjoin ℤ {ζ₁}) ℤ F₁)
  (hc₂ : IsIntegralClosure (adjoin ℤ {ζ₂}) ℤ F₂) (hn : n₁.Coprime n₂)
  (hd : IsCoprime (discr F₁) (discr F₂))

example : ∃ ζ : K, IsPrimitiveRoot ζ (n₁ * n₂) := by
  refine ⟨algebraMap F₁ K ζ₁ * algebraMap F₂ K ζ₂, ?_⟩
  replace hζ₁ := hζ₁.map_of_injective (FaithfulSMul.algebraMap_injective F₁ K)
  replace hζ₂ := hζ₂.map_of_injective (FaithfulSMul.algebraMap_injective F₂ K)
  exact hζ₁.mul_isPrimitiveRoot_of_coprime hζ₂ hn

example : F₁ ⊔ F₂ = ⊤ := by
  have : NeZero n₁ := sorry
  have : NeZero n₂ := sorry
  have :=  Subalgebra.isCyclotomicExtension_lcm_sup F₁.toSubalgebra F₂.toSubalgebra n₁ n₂


end cyclotomic



#exit


    have : IsLocalization (algebraMapSubmonoid B₁ A⁰) L₁ :=
      IsIntegralClosure.isLocalization A K L₁ B₁
    have : IsLocalization (algebraMapSubmonoid C B₁⁰) M :=
      IsIntegralClosure.isLocalization B₁ L₁ M C
    have h₂' : L₁.toSubalgebra ⊔ L₂.toSubalgebra = ⊤ := by
      simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg toSubalgebra h₂
    let b₁ := b.localizationLocalization K A⁰ L₁
    have : algebraMap B₁ M ∘ b = (h₁.basisOfBasisRight h₂' b₁) := by
      sorry
    rw [this]
    have := Submodule.traceDual_span_of_basis (A := B₂) (K := L₂) (B := C) (L := M)
      (I := span C (Set.range (h₁.basisOfBasisRight h₂' b₁).traceDual)) (ι := ι)
      (h₁.basisOfBasisRight h₂' b₁).traceDual ?_
    sorry
  · ext; simp


#exit
  classical
  have : Finite ι := sorry
  convert congr_arg (Submodule.restrictScalars B₂) <|
    congr_arg coeToSubmodule <| (1 : FractionalIdeal C⁰ M).dual_dual B₂ L₂
  · have : IsLocalization (algebraMapSubmonoid B₁ A⁰) L₁ :=
      IsIntegralClosure.isLocalization A K L₁ B₁
    have : IsLocalization (algebraMapSubmonoid C B₁⁰) M :=
      IsIntegralClosure.isLocalization B₁ L₁ M C
    have h₂' : L₁.toSubalgebra ⊔ L₂.toSubalgebra = ⊤ := by
      simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg toSubalgebra h₂
    let b₁ := b.localizationLocalization K A⁰ L₁
    have : algebraMap B₁ M ∘ b = (h₁.basisOfBasisRight h₂' b₁) := by
      sorry
    rw [this]
    have := Submodule.traceDual_span_of_basis (A := B₂) (K := L₂) (B := C) (L := M)
      (I := span C (Set.range (h₁.basisOfBasisRight h₂' b₁).traceDual)) (ι := ι)
      (h₁.basisOfBasisRight h₂' b₁).traceDual ?_
    sorry


    rw [Basis.traceDual_traceDual] at this
    rw [← this]
    congr

    have h := congr_arg ((↑) : Ideal C → FractionalIdeal C⁰ M)
        (differentIdeal_map_eq_differentIdeal h₁ h₂ h₃)
    rw [← inv_inj, coeIdeal_differentIdeal B₂ L₂, ← extended_coeIdeal_eq_map_algebraMap L₁ M,
      ← extended_inv, coeIdeal_differentIdeal A K, inv_inv, inv_inv] at h
    replace h := congr_arg coeToSubmodule <| h
    rw [coe_extended_eq_span, coe_dual_one, ← coeToSet_coeToSubmodule, coe_dual_one] at h
    have := IsLocalization.algebraMap_eq_map_map_submonoid B₁⁰ C L₁ M
    erw [← this] at h
    rw [coe_dual, coe_dual_one]
    rw [← h]
    congr

#exit
    let b₁ := b.localizationLocalization K A⁰ L₁
    have : (traceDual A K (1 : Submodule B₁ L₁) : Set L₁) = span A (Set.range b₁.traceDual) := by
      rw [← Submodule.traceDual_span_of_basis A (1 : Submodule B₁ L₁),
        Submodule.coe_restrictScalars]
      rw [b.localizationLocalization_span K A⁰ L₁]
      ext; simp
    rw [this, ← IsScalarTower.coe_toAlgHom' A L₁ M, ← map_coe, map_span, span_span_of_tower]
    rw [IsScalarTower.coe_toAlgHom', ← Set.range_comp]
    have h₂' : L₁.toSubalgebra ⊔ L₂.toSubalgebra = ⊤ := by
      simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg toSubalgebra h₂
    have : algebraMap L₁ M ∘ b₁.traceDual = (h₁.basisOfBasisRight h₂' b₁).traceDual := by
      rw [eq_comm, Basis.traceDual_eq_iff]
      intro i j
      simp only [Function.comp_apply, basisOfBasisRight_apply, traceForm_apply]
      rw [← map_mul, h₁.symm.trace_algebraMap_eq (by rwa [sup_comm])]
      rw [b₁.trace_traceDual_mul i j, MonoidWithZeroHom.map_ite_one_zero]
    rw [this]
    have := Submodule.traceDual_span_of_basis (A := B₂) (K := L₂) (B := C) (L := M)
      (I := span C (Set.range (h₁.basisOfBasisRight h₂' b₁).traceDual)) (ι := ι)
      (h₁.basisOfBasisRight h₂' b₁).traceDual ?_
    · rw [this]
      congr
      simp
      congr!
      ext
      simp
      sorry
    · ext
      simp
      sorry
    · simp
    · sorry
  · ext
    simp [mem_one_iff]
