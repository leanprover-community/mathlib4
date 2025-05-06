import Mathlib

@[simp]
theorem Algebra.norm_self_apply {R : Type*} [CommRing R] (x : R) :
    Algebra.norm R x = x := by
  simp [norm_apply]

open scoped Polynomial


  -- let f := mapRingHom (Int.castRingHom (ZMod p))
  -- have hf : Function.Surjective f :=
  --   map_surjective (Int.castRingHom (ZMod p)) (ZMod.ringHom_surjective  _)
  -- have : span {C (p : ℤ)} = RingHom.ker f := by
  --   sorry
  -- rw [this]
  -- exact RingHom.quotientKerEquivOfSurjective hf

theorem finrank_quotient_span_eq_natDegree {F : Type*} [Field F] {f : F[X]} (hf : f ≠ 0) :
    Module.finrank F (F[X] ⧸ Ideal.span {f}) = f.natDegree := by
  simpa using finrank_quotient_span_eq_natDegree_norm (Basis.singleton (Fin 1) F[X]) hf

theorem Algebra.finrank_eq_of_equiv_equiv {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    {R' : Type*} [CommSemiring R'] {S' : Type*} [Semiring S'] [Algebra R' S'] (i : R ≃+* R')
    (j : S ≃+* S') (hc : (algebraMap R' S').comp i.toRingHom = j.toRingHom.comp (algebraMap R S)) :
    Module.finrank R S = Module.finrank R' S' := by
  simpa using (congr_arg Cardinal.toNat (lift_rank_eq_of_equiv_equiv i j hc))

theorem Int.ideal_span_isMaximal_of_prime (p : ℕ+) [hp : Fact (Nat.Prime p)] :
    (Ideal.span {(p : ℤ)}).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _ <|
    (Int.quotientSpanNatEquivZMod p).toMulEquiv.isField _ (Field.toIsField _)



theorem associated_abs {α : Type*} [Ring α] [LinearOrder α] [IsOrderedAddMonoid α] (x : α) :
    Associated x |x| := by
  obtain h | h := abs_choice x
  · rw [h]
  · rw [h]
    refine ⟨-1, by simp⟩

theorem Int.ideal_eq_span_absNorm_self (J : Ideal ℤ) :
    J = Ideal.span ({(Ideal.absNorm J : ℤ)}) := by
  have : Submodule.IsPrincipal J := by exact IsPrincipalIdealRing.principal J
  obtain ⟨g, rfl⟩ := this
  rw [Ideal.submodule_span_eq, Ideal.span_singleton_eq_span_singleton]
  rw [Ideal.absNorm_span_singleton]
  rw [Int.natCast_natAbs, Algebra.norm_self_apply]
  exact associated_abs _

open Polynomial

variable {α : Type*}

theorem Polynomial.normalize_eq_self_iff_monic {K : Type*} [Field K] [DecidableEq K]
    {p : Polynomial K} (hp : p ≠ 0) :
    normalize p = p ↔ p.Monic :=
  ⟨fun h ↦ h ▸ monic_normalize hp, fun h ↦ Monic.normalize_eq_self h⟩

theorem MulEquiv_dvd_iff [Monoid α] {β : Type*} [Monoid β] {a : α} {b : β} {e : α ≃* β} :
    e a ∣ b ↔ a ∣ e.symm b := by
  simp_rw [dvd_def, MulEquiv.symm_apply_eq, map_mul]
  refine ⟨?_, ?_⟩
  · rintro ⟨c, rfl⟩
    exact ⟨e.symm c, by rw [MulEquiv.apply_symm_apply]⟩
  · rintro ⟨c, rfl⟩
    refine ⟨e c, rfl⟩

theorem RingEquiv_dvd_iff [Ring α] {β : Type*} [Ring β] {a : α} {b : β} {e : α ≃+* β} :
    e a ∣ b ↔ a ∣ e.symm b := by
  exact MulEquiv_dvd_iff (e := e.toMulEquiv)

variable [CancelCommMonoidWithZero α] [NormalizationMonoid α]

theorem irreducible_normalize_iff {a : α} :
    Irreducible (normalize a) ↔ Irreducible a := by
  rw [normalize_apply, irreducible_mul_units]

theorem normalize_eq_iff_associated {x y : α} :
    normalize x = normalize y ↔ Associated x y := by
  rw [normalize_eq_normalize_iff, dvd_dvd_iff_associated]

namespace UniqueFactorizationMonoid

variable [UniqueFactorizationMonoid α]

omit [NormalizationMonoid α] in
theorem zero_notMem_factors {a : α} :
    0 ∉ factors a := by
  by_cases h : a = 0
  · simp [h]
  · by_contra h'
    simpa [Multiset.prod_eq_zero h', Associated.comm, h] using factors_prod h

theorem zero_notMem_normalizedFactors {a : α} :
    0 ∉ normalizedFactors a := by
  exact zero_not_mem_normalizedFactors a

theorem dvd_of_normalized_factor {a : α} :
    ∀ x : α, x ∈ normalizedFactors a → x ∣ a := fun x h ↦ by
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp h
  exact normalize_dvd_iff.mpr <| dvd_of_mem_factors hy

theorem mem_normalizedFactors_iff' {a x : α} (h : a ≠ 0):
    x ∈ normalizedFactors a ↔ Irreducible x ∧ normalize x = x ∧ x ∣ a := by
  refine ⟨fun h ↦ ⟨irreducible_of_normalized_factor x h, normalize_normalized_factor x h,
    dvd_of_normalized_factor x h⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ?_⟩
  obtain ⟨y, hy₁, hy₂⟩ := UniqueFactorizationMonoid.exists_mem_factors_of_dvd h h₁ h₃
  exact Multiset.mem_map.mpr ⟨y, hy₁, by rwa [← h₂, normalize_eq_iff_associated, Associated.comm]⟩
