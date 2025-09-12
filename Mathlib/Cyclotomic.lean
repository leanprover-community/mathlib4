import Mathlib.NumberTheory.Cyclotomic.PID


section Subalgebra

-- theorem IsPrimitiveRoot.isIntegral' {n : ℕ} [NeZero n] {K : Type*} [CommRing K] {μ : K}
--     {R : Type*} [CommRing R] [Algebra R K] [CharZero R] [IsScalarTower ℤ R K]
--     (h : IsPrimitiveRoot μ n) :
--     IsIntegral R μ := (h.isIntegral (NeZero.pos _)).tower_top

open Algebra Subalgebra


-- TODO: use the same arguments order everywhere



theorem IsPrimitiveRoot.adjoin_pair_eq (A : Type*) {B : Type*} [CommSemiring A] [CommRing B]
    [Algebra A B] [IsDomain B] {ζ₁ ζ₂ : B} {k₁ : ℕ} {k₂ : ℕ} (hζ₁ : IsPrimitiveRoot ζ₁ k₁)
    (hζ₂ : IsPrimitiveRoot ζ₂ k₂) (hk₁ : k₁ ≠ 0) (hk₂ : k₂ ≠ 0)
    {ζ : B} (hζ : IsPrimitiveRoot ζ (k₁.lcm k₂)) :
    adjoin A {ζ₁, ζ₂} = adjoin A {ζ} := by
  have : NeZero (k₁.lcm k₂) := ⟨Nat.lcm_ne_zero hk₁ hk₂⟩
  refine le_antisymm (adjoin_le ?_) (adjoin_le ?_)
  · refine Set.pair_subset_iff.mpr ⟨?_, ?_⟩
    · obtain ⟨_, _, rfl⟩ := hζ.eq_pow_of_pow_eq_one <|
        (hζ₁.pow_eq_one_iff_dvd _).mpr <| k₁.dvd_lcm_left k₂
      exact Subalgebra.pow_mem _ (self_mem_adjoin_singleton A _) _
    · obtain ⟨_, _, rfl⟩ := hζ.eq_pow_of_pow_eq_one <|
        (hζ₂.pow_eq_one_iff_dvd _).mpr <| k₁.dvd_lcm_right k₂
      exact Subalgebra.pow_mem _ (self_mem_adjoin_singleton A _) _
  · have hζ' := IsPrimitiveRoot.pow_mul_pow_lcm hζ₁ hζ₂ hk₁ hk₂
    obtain ⟨_, _, rfl⟩ := hζ'.eq_pow_of_pow_eq_one hζ.pow_eq_one
    aesop

theorem IsPrimitiveRoot.adjoin_pair_eq' (A : Type*) {B : Type*} [CommSemiring A] [CommRing B]
    [Algebra A B] [IsDomain B] {ζ₁ ζ₂ : B} {k₁ : ℕ} {k₂ : ℕ} (hζ₁ : IsPrimitiveRoot ζ₁ k₁)
    (hζ₂ : IsPrimitiveRoot ζ₂ k₂) (hk₁ : k₁ ≠ 0) (hk₂ : k₂ ≠ 0) :
    adjoin A {ζ₁, ζ₂} =
      adjoin A {ζ₁ ^ (k₁ / k₁.factorizationLCMLeft k₂) *
        ζ₂ ^ (k₂ / k₁.factorizationLCMRight k₂)} :=
  hζ₁.adjoin_pair_eq A hζ₂ hk₁ hk₂ <| pow_mul_pow_lcm hζ₁ hζ₂ hk₁ hk₂

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

theorem IsCyclotomicExtension.mem_of_pow_eq_one {A : Type*} {B : Type*} [CommRing A] [CommRing B]
    [IsDomain B] [Algebra A B] {T : Subalgebra A B} {S : Set ℕ} [h : IsCyclotomicExtension S A T]
    {n : ℕ} {ζ : B} (hn₀ : n ∈ S) (hn₁ : n ≠ 0) (hζ : ζ ^ n = 1) : ζ ∈ T := by
  have : NeZero n := ⟨hn₁⟩
  obtain ⟨η, hη⟩ := h.1 hn₀ (NeZero.ne n)
  replace hη := hη.map_of_injective (FaithfulSMul.algebraMap_injective T B)
  obtain ⟨k, _, rfl⟩ := hη.eq_pow_of_pow_eq_one hζ
  rw [← map_pow]
  exact Subalgebra.pow_mem _ η.prop _

theorem IsCyclotomicExtension.zero_eq (T : Subalgebra A B) [hT : IsCyclotomicExtension {0} A T] :
    T = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have := hT.2 ⟨x, hx⟩
  simp at this
  have := Set.mem_image_of_mem (IsScalarTower.toAlgHom A T B) this
  rwa [← Subalgebra.coe_map, Algebra.map_bot] at this

variable [IsDomain B]

theorem IsCyclotomicExtension.iff_eq_adjoin (S : Set ℕ) (T : Subalgebra A B)
    (hS : ∀ n ∈ S, n ≠ 0 → ∃ (r : B), IsPrimitiveRoot r n) :
    IsCyclotomicExtension S A T ↔ T = Algebra.adjoin A {b : B | ∃ n ∈ S, n ≠ 0 ∧ b ^ n = 1} := by
  constructor
  · intro h
    apply le_antisymm
    · intro x hx
      have := Set.mem_image_of_mem (IsScalarTower.toAlgHom A T B) <| h.2 ⟨x, hx⟩
      rw [← Subalgebra.coe_map, ← Algebra.adjoin_algebraMap, IsScalarTower.coe_toAlgHom',
        Subalgebra.algebraMap_mk, algebraMap_self, RingHom.id_apply, SetLike.mem_coe] at this
      refine Set.mem_of_subset_of_mem ?_ this
      apply adjoin_le
      rintro _ ⟨x, ⟨n, hn₁, hn₂, hn₃⟩, rfl⟩
      refine Set.mem_of_subset_of_mem subset_adjoin ?_
      exact ⟨n, hn₁, hn₂, by simpa using congr_arg (algebraMap T B) hn₃⟩
    · apply adjoin_le
      exact fun x ⟨n, hn₁, hn₂, hn₃⟩ ↦ h.mem_of_pow_eq_one hn₁ hn₂ hn₃
  · exact fun h ↦ h ▸ isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot S A B hS

theorem IsCyclotomicExtension.singleton_iff_eq_adjoin (n : ℕ) [NeZero n] (T : Subalgebra A B)
    {ζ : B} (hζ : IsPrimitiveRoot ζ n) :
    IsCyclotomicExtension {n} A T ↔ T = adjoin A {ζ} := by
  rw [IsCyclotomicExtension.iff_eq_adjoin]
  · simp only [Set.mem_singleton_iff, exists_eq_left]
    suffices adjoin A {b | n ≠ 0 ∧ b ^ n = 1} = adjoin A {ζ} by rw [this]
    apply le_antisymm
    · apply adjoin_le
      intro x ⟨_, hx⟩
      obtain ⟨k, _, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
      exact Subalgebra.pow_mem _ (self_mem_adjoin_singleton A ζ) _
    · apply adjoin_mono
      simp only [Set.singleton_subset_iff, Set.mem_setOf_eq]
      refine ⟨NeZero.ne n, hζ.pow_eq_one⟩
  · simpa only [Set.mem_singleton_iff, ne_eq, forall_eq, NeZero.ne n, not_false_eq_true,
      forall_const] using ⟨ζ, hζ⟩

theorem isCyclotomicExtension_eq_of_eq (T₁ T₂ : Subalgebra A B) (n : ℕ) [NeZero n]
    [h₁ : IsCyclotomicExtension {n} A T₁] [h₂ : IsCyclotomicExtension {n} A T₂] :
    T₁ = T₂ := by
  have hζ := h₁.zeta_spec _ _
  replace hζ := hζ.map_of_injective (FaithfulSMul.algebraMap_injective T₁ B)
  rw [(IsCyclotomicExtension.singleton_iff_eq_adjoin _ T₁ hζ).mp h₁,
    (IsCyclotomicExtension.singleton_iff_eq_adjoin _ T₂ hζ).mp h₂]

theorem IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin {K L : Type*} [Field K]
    [CharZero K] [Field L] [Algebra K L] (n : ℕ) [NeZero n] (T : IntermediateField K L) {ζ : L}
    (hζ : IsPrimitiveRoot ζ n) :
    IsCyclotomicExtension {n} K T ↔ T = IntermediateField.adjoin K {ζ} := by
  rw [← toSubalgebra_inj, adjoin_simple_toSubalgebra_of_integral
    (hζ.isIntegral (NeZero.pos _)).tower_top]
  exact IsCyclotomicExtension.singleton_iff_eq_adjoin n T.toSubalgebra hζ

protected theorem IntermediateField.isCyclotomicExtension_eq_of_eq {K L : Type*} [Field K] [Field L]
    [Algebra K L] (T₁ T₂ : IntermediateField K L) (n : ℕ) [NeZero n]
    [h₁ : IsCyclotomicExtension {n} K T₁] [h₂ : IsCyclotomicExtension {n} K T₂] :
    T₁ = T₂ := by
  rw [← toSubalgebra_inj]
  exact isCyclotomicExtension_eq_of_eq _ _ n

variable (T₁ T₂ : Subalgebra A B) (n₁ n₂ : ℕ) [hcycl₁ : IsCyclotomicExtension {n₁} A T₁]
  [hcycl₂ : IsCyclotomicExtension {n₂} A T₂]

theorem IsCyclotomicExtension.le_of_dvd [NeZero n₂] (h : n₁ ∣ n₂) : T₁ ≤ T₂ := by
  by_cases hn₁ : n₁ = 0
  · rw [hn₁, zero_dvd_iff] at h
    exact False.elim <| NeZero.ne n₂ h
  have : NeZero n₁ := ⟨hn₁⟩
  obtain ⟨ζ, hζ⟩ := hcycl₂.1 rfl (NeZero.ne n₂)
  replace hζ := hζ.map_of_injective (FaithfulSMul.algebraMap_injective T₂ B)
  obtain ⟨d, hd⟩ := h
  have := IsPrimitiveRoot.pow n₂.pos_of_neZero hζ (by rwa [mul_comm])
  simp only [(singleton_iff_eq_adjoin n₁ T₁ this).mp hcycl₁,
    (singleton_iff_eq_adjoin n₂ T₂ hζ).mp hcycl₂]
  apply adjoin_le
  simp only [Set.singleton_subset_iff, SetLike.mem_coe]
  exact Subalgebra.pow_mem _ (self_mem_adjoin_singleton A _) _

theorem IsCyclotomicExtension.lcm_sup [NeZero n₁] [NeZero n₂] :
    IsCyclotomicExtension {n₁.lcm n₂} A (T₁ ⊔ T₂ : Subalgebra A B) := by
  obtain ⟨ζ₁, hζ₁⟩ := hcycl₁.1 rfl (NeZero.ne n₁)
  obtain ⟨ζ₂, hζ₂⟩ := hcycl₂.1 rfl (NeZero.ne n₂)
  replace hζ₁ := hζ₁.map_of_injective (FaithfulSMul.algebraMap_injective T₁ B)
  replace hζ₂ := hζ₂.map_of_injective (FaithfulSMul.algebraMap_injective T₂ B)
  rw [sup_comm, (singleton_iff_eq_adjoin n₁ T₁ hζ₁).mp hcycl₁,
    (singleton_iff_eq_adjoin n₂ T₂ hζ₂).mp hcycl₂, ← adjoin_union, Set.union_singleton]
  rw [hζ₁.adjoin_pair_eq' A hζ₂ (NeZero.ne _) (NeZero.ne _)]
  have : NeZero (n₁.lcm n₂) := ⟨Nat.lcm_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  exact (hζ₁.pow_mul_pow_lcm hζ₂ (NeZero.ne n₁) (NeZero.ne n₂)).adjoin_isCyclotomicExtension A

end Subalgebra

section IntermediateField

theorem IntermediateField.isCyclotomicExtension_lcm_sup {F E : Type*} [Field F] [Field E]
    [Algebra F E] (L₁ L₂ : IntermediateField F E) {n₁ : ℕ} {n₂ : ℕ} [NeZero n₁] [NeZero n₂]
    [IsCyclotomicExtension {n₁} F L₁] [IsCyclotomicExtension {n₂} F L₂] :
    IsCyclotomicExtension {n₁.lcm n₂} F ↥(L₁ ⊔ L₂) := by
  have : FiniteDimensional F L₁ := IsCyclotomicExtension.finite_of_singleton n₁ F L₁
  have := IsCyclotomicExtension.lcm_sup L₁.toSubalgebra L₂.toSubalgebra n₁ n₂
  rwa [← sup_toSubalgebra_of_left] at this

end IntermediateField
