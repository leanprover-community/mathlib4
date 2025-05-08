import Mathlib

@[simp]
theorem Int.quotientSpanNatEquivZMod_comp_Quotient_mk_eq (n :ℕ) :
  (Int.quotientSpanNatEquivZMod n : _ →+* _).comp (Ideal.Quotient.mk (Ideal.span {(n : ℤ)})) =
    Int.castRingHom (ZMod n) := rfl

theorem IsCoatom.sup_eq_top_iff {α : Type*} {a b : α} [SemilatticeSup α] [OrderTop α]
    (ha : IsCoatom a) :
    a ⊔ b = ⊤ ↔ ¬ b ≤ a := by
  by_cases hb : b = ⊤
  · simpa [hb] using ha.1
  · exact ⟨fun h ↦ left_lt_sup.mp (h ▸ IsCoatom.lt_top ha), fun h ↦ ha.2 _ (left_lt_sup.mpr h)⟩

theorem adjoin_eq_top_of_conductor_eq_top {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] {x : S} (h : conductor R x = ⊤) :
    Algebra.adjoin R {x} = ⊤ :=
    Algebra.eq_top_iff.mpr fun y ↦
      one_mul y ▸ (mem_conductor_iff).mp ((Ideal.eq_top_iff_one (conductor R x)).mp h) y

theorem conductor_eq_top_iff_adjoin_eq_top {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] {x : S} :
    conductor R x = ⊤ ↔ Algebra.adjoin R {x} = ⊤ :=
  ⟨fun h ↦ adjoin_eq_top_of_conductor_eq_top h, fun h ↦ conductor_eq_top_of_adjoin_eq_top h⟩

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

theorem Int.ideal_span_isMaximal_of_prime (p : ℕ) [hp : Fact (Nat.Prime p)] :
    (Ideal.span {(p : ℤ)}).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _ <|
    (Int.quotientSpanNatEquivZMod p).toMulEquiv.isField _ (Field.toIsField _)

theorem associated_abs {α : Type*} [Ring α] [LinearOrder α] (x : α) :
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

variable {α : Type*}

open Polynomial in
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

end UniqueFactorizationMonoid

theorem Ideal.ne_bot_of_le_comap_algebra {A : Type*} [CommRing A] {p : Ideal A} {B : Type*} [Ring B]
    [Nontrivial B] (P : Ideal B) [Algebra A B] [NoZeroSMulDivisors A B] (hp : p ≠ ⊥)
    (hP : p ≤ comap (algebraMap A B) P) :
    P ≠ ⊥ := by
  contrapose! hp
  simpa [hp] using hP

theorem Ideal.ne_bot_of_liesOver_of_ne_bot' {A : Type*} [CommRing A] {B : Type*} [Ring B]
    [Nontrivial B] [Algebra A B] [NoZeroSMulDivisors A B] {p : Ideal A} (hp : p ≠ ⊥)
    (P : Ideal B) [hP : P.LiesOver p] : P ≠ ⊥ :=
  ne_bot_of_le_comap_algebra P hp <| le_of_eq ((Ideal.liesOver_iff _ _).mp hP)

open Ideal UniqueFactorizationMonoid in
theorem Ideal.primesOver_eq_normalizedFactors {A : Type*} [CommRing A] [IsDedekindDomain A]
    (p : Ideal A) [h : p.IsMaximal] (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [NoZeroSMulDivisors A B] (hp : p ≠ ⊥) :
    p.primesOver B =  {P | P ∈ normalizedFactors (Ideal.map (algebraMap A B) p)} := by
  ext P
  simp only [primesOver, liesOver_iff, under_def, Set.mem_setOf_eq, mem_normalizedFactors_iff'
    (map_ne_bot_of_ne_bot hp :  map (algebraMap A B) p ≠ 0), irreducible_iff_prime,
    normalize_eq, dvd_iff_le, map_le_iff_le_comap, true_and]
  refine ⟨fun ⟨h₁, h₂⟩ ↦ ⟨?_, le_of_eq h₂⟩, fun ⟨h₁, h₂⟩ ↦ ⟨?_, ?_⟩⟩
  · rwa [prime_iff_isPrime (ne_bot_of_le_comap_algebra P hp <| le_of_eq h₂)]
  · rwa [← prime_iff_isPrime (ne_bot_of_le_comap_algebra P hp h₂)]
  · rw [prime_iff_isPrime (ne_bot_of_le_comap_algebra P hp h₂)] at h₁
    refine ((IsCoatom.le_iff_eq (isMaximal_def.mp h) ?_).mp h₂).symm
    exact comap_ne_top (algebraMap A B) (IsPrime.ne_top h₁)
