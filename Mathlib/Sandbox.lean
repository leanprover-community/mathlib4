import Mathlib

section cyclo

theorem IsIntegralClosure.subalgebra_eq_of_integralClosure {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] {S : Subalgebra R A} (hS : IsIntegralClosure S R A) :
    S = integralClosure R A := by
  ext x
  rw [mem_integralClosure_iff, hS.isIntegral_iff]
  refine ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩, ?_⟩
  rintro ⟨y, rfl⟩
  exact y.prop

open NumberField

example {p : ℕ+} {k : ℕ} {K : Type*} [Field K] {ζ : K} [hp : Fact (Nat.Prime p)] [NumberField K]
    [hcycl : IsCyclotomicExtension {p ^ k} ℚ K] (hζ : IsPrimitiveRoot ζ ↑(p ^ k)) :
    Algebra.adjoin ℤ {(hζ.toInteger : 𝓞 K)} = ⊤ := by
  have := IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_pow hζ
  have k := IsIntegralClosure.subalgebra_eq_of_integralClosure this

  let f : 𝓞 K →ₐ[ℤ] K := by exact Algebra.algHom ℤ (𝓞 K) K
  let g := Subalgebra.map f
  have : Function.Injective g := sorry
  rw [← this.eq_iff]
  simp [g, f]
  convert k
  unfold RingOfIntegers
  
  apply IsIntegralClosure.subalgebra_eq_of_integralClosure


#exit

  apply IsIntegralClosure.subalgebra_integralClosure_eq_top
  convert IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_pow hζ


#exit
  refine Algebra.eq_top_iff.mpr fun x ↦ ?_
  have : x = hζ.adjoinEquivRingOfIntegers (hζ.adjoinEquivRingOfIntegers.symm x) := by
    exact (AlgEquiv.symm_apply_eq hζ.adjoinEquivRingOfIntegers).mp rfl
  rw [this]
  simp




#exit





  obtain ⟨y, hy⟩ := hζ.adjoinEquivRingOfIntegers.symm x
  have := hζ.adjoinEquivRingOfIntegers_symm_apply x
  have : x = ⟨y, sorry⟩ := sorry
  rw [this]


end cyclo

@[to_additive]
theorem Monoid.exponent_eq_sInf {G : Type*} [Monoid G] :
    Monoid.exponent G = sInf {d : ℕ | 0 < d ∧ ∀ x : G, x ^ d = 1} := by
  by_cases h : Monoid.ExponentExists G
  · rw [Monoid.exponent, dif_pos h]
    obtain ⟨d, hd⟩ := h
    have h' : {d : ℕ | 0 < d ∧ ∀ x : G, x ^ d = 1}.Nonempty := by
      refine ⟨d, hd⟩
    rw [Nat.sInf_def h']
    congr
  · rw [Monoid.exponent_eq_zero_iff.mpr h]
    have : {d | 0 < d ∧ ∀ (x : G), x ^ d = 1} = ∅ :=
      Set.eq_empty_of_forall_not_mem fun n hn ↦ h ⟨n, hn⟩
    rw [this, Nat.sInf_empty]

@[simp]
theorem Algebra.norm_self_apply {R : Type*} [CommRing R] (x : R) :
    Algebra.norm R x = x := by
  simp [norm_apply]

theorem associated_abs {α : Type*} [Ring α] [LinearOrder α] (x : α) :
    Associated x |x| := by
  obtain h | h := abs_choice x
  · rw [h]
  · rw [h]
    refine ⟨-1, by simp⟩

section Int.Ideal

open Ideal

theorem Int.ideal_eq_span_absNorm_self (J : Ideal ℤ) :
    J = span {(absNorm J : ℤ)} := by
  have : Submodule.IsPrincipal J := by exact IsPrincipalIdealRing.principal J
  obtain ⟨g, rfl⟩ := this
  rw [submodule_span_eq, span_singleton_eq_span_singleton, absNorm_span_singleton,
    Int.natCast_natAbs, Algebra.norm_self_apply]
  exact associated_abs _

theorem Int.cast_mem_ideal_iff {R : Type*} [Ring R] [Algebra ℤ R] {I : Ideal R} {d : ℤ} :
    (d : R) ∈ I ↔ (absNorm (under ℤ I) : ℤ) ∣ d := by
  rw [← mem_span_singleton, ← Int.ideal_eq_span_absNorm_self, under_def, mem_comap, eq_intCast]

theorem Int.absNorm_under_mem {R : Type*} [Ring R] [Algebra ℤ R] (I : Ideal R) :
    (absNorm (under ℤ I) : R) ∈ I := by
  rw [← Int.cast_natCast, Int.cast_mem_ideal_iff]

theorem Int.absNorm_under_eq_sInf {R : Type*} [Ring R] [Algebra ℤ R] (I : Ideal R) :
    absNorm (under ℤ I) = sInf {d : ℕ | 0 < d ∧ (d : R) ∈ I} := by
  by_cases h : absNorm (under ℤ I) = 0
  · have : {d : ℕ | 0 < d ∧ ↑d ∈ I} = ∅ := by
      refine Set.eq_empty_of_forall_not_mem ?_
      intro x ⟨hx₁, hx₂⟩
      rw [← Int.cast_natCast, Int.cast_mem_ideal_iff, h, Int.natCast_dvd_natCast,
        Nat.zero_dvd] at hx₂
      rw [Nat.pos_iff_ne_zero] at hx₁
      exact hx₁ hx₂
    rw [h, this, Nat.sInf_empty]
  · have h₁ : absNorm (under ℤ I) ∈ {d : ℕ | 0 < d ∧ ↑d ∈ I} :=
      ⟨Nat.pos_of_ne_zero h, Int.absNorm_under_mem I⟩
    refine le_antisymm ?_ (Nat.sInf_le h₁)
    by_contra! h₀
    have h₂ := (Nat.sInf_mem (Set.nonempty_of_mem h₁)).2
    rw [← Int.cast_natCast, Int.cast_mem_ideal_iff, Int.natCast_dvd_natCast] at h₂
    exact lt_iff_not_le.mp h₀ <| Nat.le_of_dvd (Nat.sInf_mem (Set.nonempty_of_mem h₁)).1 h₂

theorem Int.absNorm_under_dvd_absNorm {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Module.Free ℤ R] (I : Ideal R) :
    absNorm (under ℤ I) ∣ absNorm I := by
  by_cases h : Finite (R ⧸ I)
  · have : Fintype (R ⧸ I) := Fintype.ofFinite (R ⧸ I)
    have h_main {d : ℕ} : (d : R) ∈ I ↔ ∀ (x : R ⧸ I), d • x = 0 := by
      simp_rw [nsmul_eq_mul, ← map_natCast (Ideal.Quotient.mk I), ← Quotient.eq_zero_iff_mem]
      exact ⟨fun h _ ↦ by simp [h], fun h ↦ by simpa using h 1⟩
    rw [Ideal.absNorm_apply I, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    simp_rw [Int.absNorm_under_eq_sInf, h_main, ← AddMonoid.exponent_eq_sInf]
    exact AddGroup.exponent_dvd_card (G := R ⧸ I)
  · rw [show absNorm I = 0 by
      exact AddSubgroup.index_eq_zero_iff_infinite.mpr <| not_finite_iff_infinite.mp h]
    exact Nat.dvd_zero _

end Int.Ideal

theorem Ideal.span_pair_eq_span_singleton_of_dvd {R : Type*} [CommSemiring R] {a b : R}
    (h : a ∣ b) :
    Ideal.span {a, b} = Ideal.span {a} := by
  rwa [Ideal.span_insert, sup_eq_left, Ideal.span_singleton_le_span_singleton]

@[simp]
theorem Int.quotientSpanNatEquivZMod_comp_Quotient_mk_eq (n :ℕ) :
    (Int.quotientSpanNatEquivZMod n : _ →+* _).comp (Ideal.Quotient.mk (Ideal.span {(n : ℤ)})) =
      Int.castRingHom (ZMod n) := rfl

@[simp]
theorem Int.quotientSpanNatEquivZMod_comp_castRingHom_eq (n : ℕ) :
    RingHom.comp (Int.quotientSpanNatEquivZMod n).symm (Int.castRingHom (ZMod n)) =
      Ideal.Quotient.mk (Ideal.span {(n : ℤ)}) := by ext; simp

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

theorem Ideal.ramificationIdx_eq_multiplicity {R : Type*} [CommRing R] {S : Type*} [CommRing S]
    [IsDedekindDomain S] {f : R →+* S} (hf : Function.Injective f) {p : Ideal R} (hp : p ≠ ⊥)
    {P : Ideal S} (hP₁: P.IsPrime) (hP₂ : P ≠ ⊥)  :
    ramificationIdx f p P = multiplicity P (Ideal.map f p) := by
  classical
  have hp' : map f p ≠ ⊥ := (map_eq_bot_iff_of_injective hf).not.mpr hp
  rw [multiplicity_eq_of_emultiplicity_eq_some]
  rw [IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hp' hP₁ hP₂, ← normalize_eq P,
    ← UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors _ hp', normalize_eq]
  exact irreducible_iff_prime.mpr <| prime_of_isPrime hP₂ hP₁

open scoped Polynomial

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



variable {α : Type*}

open Polynomial in
theorem Polynomial.normalize_eq_self_iff_monic {K : Type*} [Field K] [DecidableEq K]
    {p : Polynomial K} (hp : p ≠ 0) :
    normalize p = p ↔ p.Monic :=
  ⟨fun h ↦ h ▸ monic_normalize hp, fun h ↦ Monic.normalize_eq_self h⟩

open Polynomial in
@[simp]
theorem Polynomial.map_normalize {K : Type*} [Field K] [DecidableEq K]
    {p : Polynomial K} {S : Type*} [Field S] [DecidableEq S] (f : K →+* S) :
    map f (normalize p) = normalize (map (f : K →+* S) p) := by
  by_cases hp : p = 0
  · simp [hp]
  · simp [normalize_apply, Polynomial.map_mul, normUnit, hp]

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

theorem mem_normalizedFactors_iff' {a x : α} (h : a ≠ 0) :
    x ∈ normalizedFactors a ↔ Irreducible x ∧ normalize x = x ∧ x ∣ a := by
  refine ⟨fun h ↦ ⟨irreducible_of_normalized_factor x h, normalize_normalized_factor x h,
    dvd_of_normalized_factor x h⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ?_⟩
  obtain ⟨y, hy₁, hy₂⟩ := UniqueFactorizationMonoid.exists_mem_factors_of_dvd h h₁ h₃
  exact Multiset.mem_map.mpr ⟨y, hy₁, by rwa [← h₂, normalize_eq_iff_associated, Associated.comm]⟩

def normalizedFactorsEquiv {β : Type*} [CancelCommMonoidWithZero β]
    [NormalizationMonoid β] [UniqueFactorizationMonoid β] {e : α ≃* β}
    (he : ∀ x, normalize (e x) = e (normalize x)) (a : α) :
    {x | x ∈ normalizedFactors a} ≃ {y | y ∈ normalizedFactors (e a)} := by
  refine Equiv.subtypeEquiv e fun x ↦ ?_
  by_cases ha : a = 0
  · simp [ha]
  · simp [mem_normalizedFactors_iff' ha, mem_normalizedFactors_iff'
      (EmbeddingLike.map_ne_zero_iff.mpr ha), MulEquiv_dvd_iff, MulEquiv.symm_apply_apply,
      MulEquiv.irreducible_iff, he]

theorem normalizedFactorsEquiv_apply {β : Type*} [CancelCommMonoidWithZero β]
    [NormalizationMonoid β] [UniqueFactorizationMonoid β] (e : α ≃* β)
    (he : ∀ x, normalize (e x) = e (normalize x)) (a : α) {x : α} (hx : x ∈ normalizedFactors a) :
    (normalizedFactorsEquiv he a) ⟨x, hx⟩ = e x := rfl

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
