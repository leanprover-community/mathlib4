import Mathlib.RingTheory.DedekindDomain.Factorization

section IsDedekindDomain

instance {R : Type*} [CommSemiring R] :
    OrderedCommSemiring (Ideal R) := CanonicallyOrderedAdd.toOrderedCommSemiring

lemma mul_inf₀ {α : Type*} [Lattice α] [GroupWithZero α] [PosMulMono α] [PosMulReflectLE α]
    {c : α} (hc : 0 ≤ c) (a b : α) :
    c * (a ⊓ b) = c * a ⊓ c * b := by
  obtain (rfl|hc) := hc.eq_or_lt
  · simp
  · exact (OrderIso.mulLeft₀ c hc).map_inf a b

lemma inf_mul₀ {α : Type*} [Lattice α] [GroupWithZero α] [MulPosMono α] [MulPosReflectLE α]
    {c : α} (hc : 0 ≤ c) (a b : α) :
    (a ⊓ b) * c = a * c ⊓ b * c := by
  obtain (rfl|hc) := hc.eq_or_lt
  · simp
  · exact (OrderIso.mulRight₀ c hc).map_inf a b

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
variable [Algebra R K] [IsFractionRing R K]

open nonZeroDivisors

instance : CanonicallyOrderedAdd (FractionalIdeal R⁰ K) where
  exists_add_of_le h := ⟨_, (sup_eq_right.mpr h).symm⟩
  le_self_add _ _ := le_sup_left

instance : OrderedCommSemiring (FractionalIdeal R⁰ K) :=
  CanonicallyOrderedAdd.toOrderedCommSemiring

instance : PosMulReflectLE (FractionalIdeal R⁰ K) :=
  ⟨fun I _ _ ↦ (FractionalIdeal.mul_left_le_iff I.2.ne').mp⟩

instance : MulPosReflectLE (FractionalIdeal R⁰ K) :=
  ⟨fun I J K e ↦ by rwa [mul_comm, mul_comm K, FractionalIdeal.mul_left_le_iff I.2.ne'] at e⟩

instance : PosMulStrictMono (FractionalIdeal R⁰ K) :=
  PosMulMono.toPosMulStrictMono

instance : MulPosStrictMono (FractionalIdeal R⁰ K) := MulPosMono.toMulPosStrictMono

instance : PosMulReflectLE (Ideal R) where
  elim I J K e := by
    rwa [← FractionalIdeal.coeIdeal_le_coeIdeal (FractionRing R),
      ← FractionalIdeal.mul_left_le_iff (J := I) (by simpa using I.2.ne'),
      ← FractionalIdeal.coeIdeal_mul, ← FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.coeIdeal_le_coeIdeal]

instance : PosMulStrictMono (Ideal R) := PosMulMono.toPosMulStrictMono

instance : MulPosStrictMono (Ideal R) := MulPosMono.toMulPosStrictMono

lemma Ideal.mul_iInf (I : Ideal R) {ι : Type*} [Nonempty ι] (J : ι → Ideal R) :
    I * ⨅ i, J i = ⨅ i, I * J i := by
  by_cases hI : I = 0
  · simp [hI]
  refine (le_iInf fun i ↦ Ideal.mul_mono_right (iInf_le _ _)).antisymm ?_
  have H : ⨅ i, I * J i ≤ I := (iInf_le _ (Nonempty.some ‹_›)).trans Ideal.mul_le_right
  obtain ⟨K, hK⟩ := Ideal.dvd_iff_le.mpr H
  rw [hK]
  refine mul_le_mul_left' ?_ I
  rw [le_iInf_iff]
  intro i
  rw [← mul_le_mul_iff_of_pos_left (a := I), ← hK]
  · exact iInf_le _ _
  · exact bot_lt_iff_ne_bot.mpr hI

lemma Ideal.iInf_mul (I : Ideal R) {ι : Type*} [Nonempty ι] (J : ι → Ideal R) :
    (⨅ i, J i) * I = ⨅ i, J i * I := by
  simp only [mul_iInf, mul_comm _ I]

lemma Ideal.mul_inf (I J K : Ideal R) : I * (J ⊓ K) = I * J ⊓ I * K := by
  rw [inf_eq_iInf, Ideal.mul_iInf, inf_eq_iInf]
  congr! 2 with ⟨⟩

lemma Ideal.inf_mul (I J K : Ideal R) : (I ⊓ J) * K = I * K ⊓ J * K := by
  simp only [Ideal.mul_inf, mul_comm _ K]

lemma FractionalIdeal.mul_inf (I J K : FractionalIdeal R⁰ K) : I * (J ⊓ K) = I * J ⊓ I * K :=
  mul_inf₀ (zero_le _) _ _

lemma FractionalIdeal.inf_mul (I J K : FractionalIdeal R⁰ K) : (I ⊓ J) * K = I * K ⊓ J * K :=
  inf_mul₀ (zero_le _) _ _

/-- In a dedekind domain, for every ideals `0 < I ≤ J` there exists `a` such that `J = I + ⟨a⟩`.
This property uniquely characterizes dedekind domains. -/
lemma IsDedekindDomain.exists_sup_span_eq {I J : Ideal R} (hIJ : I ≤ J) (hI : I ≠ 0) :
    ∃ a, I ⊔ Ideal.span {a} = J := by
  classical
  obtain ⟨I, rfl⟩ := Ideal.dvd_iff_le.mpr hIJ
  simp only [ne_eq, mul_eq_zero, not_or] at hI
  obtain ⟨hJ, hI⟩ := hI
  suffices ∃ a, ∃ K, J * K = Ideal.span {a} ∧ I + K = ⊤ by
    obtain ⟨a, K, e, e'⟩ := this
    exact ⟨a, by rw [← e, ← Ideal.add_eq_sup, ← mul_add, e', Ideal.mul_top]⟩
  let s := (I.finite_factors hI).toFinset
  have : ∀ p ∈ s, J * ∏ q ∈ s, q.asIdeal < J * ∏ q ∈ s \ {p}, q.asIdeal := by
    intro p hps
    conv_rhs => rw [← mul_one (J * _)]
    rw [Finset.prod_eq_mul_prod_diff_singleton hps, ← mul_assoc,
      mul_right_comm _ p.asIdeal]
    refine mul_lt_mul_of_pos_left ?_ ?_
    · rw [Ideal.one_eq_top, lt_top_iff_ne_top]
      exact p.2.ne_top
    · rw [Ideal.zero_eq_bot, bot_lt_iff_ne_bot, ← Ideal.zero_eq_bot,
        mul_ne_zero_iff, Finset.prod_ne_zero_iff]
      exact ⟨hJ, fun x _ ↦ x.3⟩
  choose! a ha ha' using fun p hps ↦ SetLike.exists_of_lt (this p hps)
  obtain ⟨K, hK⟩ : J ∣ Ideal.span {∑ p ∈ s, a p} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact sum_mem fun p hp ↦ Ideal.mul_le_right (ha p hp)
  refine ⟨_, _, hK.symm, ?_⟩
  by_contra H
  obtain ⟨p, hp, h⟩ := Ideal.exists_le_maximal _ H
  let p' : HeightOneSpectrum R := ⟨p, hp.isPrime, fun e ↦ hI (by simp_all)⟩
  have hp's : p' ∈ s := by simpa [p', s, Ideal.dvd_iff_le] using le_sup_left.trans h
  have H₁ : J * K ≤ J * p := Ideal.mul_mono_right (le_sup_right.trans h)
  replace H₁ := hK.trans_le H₁ (Ideal.mem_span_singleton_self _)
  have H₂ : ∑ q ∈ s \ {p'}, a q ∈ J * p := by
    refine sum_mem fun q hq ↦ ?_
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hq
    refine Ideal.mul_mono_right ?_ (ha q hq.1)
    exact Ideal.prod_le_inf.trans (Finset.inf_le (b := p') (by simpa [hp's] using Ne.symm hq.2))
  apply ha' _ hp's
  have := IsDedekindDomain.inf_prime_pow_eq_prod s (fun i ↦ i.asIdeal) (fun _ ↦ 1)
    (fun i _ ↦ i.prime) (fun i _ j _ e ↦ mt HeightOneSpectrum.ext e)
  simp only [pow_one] at this
  have inst : Nonempty {x // x ∈ s} := ⟨_, hp's⟩
  rw [← this, Finset.inf_eq_iInf, iInf_subtype', Ideal.mul_iInf, Ideal.mem_iInf]
  rintro ⟨q, hq⟩
  by_cases hqp : q = p'
  · subst hqp
    convert sub_mem H₁ H₂
    rw [Finset.sum_eq_add_sum_diff_singleton hp's, add_sub_cancel_right]
  · refine Ideal.mul_mono_right ?_ (ha p' hp's)
    exact Ideal.prod_le_inf.trans (Finset.inf_le (b := q) (by simpa [hq] using hqp))

/-- In a dedekind domain, any ideal is spanned by two elements. -/
lemma IsDedekindDomain.exists_eq_span_pair {I : Ideal R} {x : R} (hxI : x ∈ I) (hx : x ≠ 0) :
    ∃ y, I = .span {x, y} := by
  obtain ⟨y, rfl⟩ := exists_sup_span_eq (I.span_singleton_le_iff_mem.mpr hxI) (by simpa)
  simp_rw [← Ideal.span_union, Set.union_singleton, Set.pair_comm x]
  use y

lemma IsDedekindDomain.exists_add_spanSingleton_mul_eq
    {a b c : FractionalIdeal R⁰ K} (hac : a ≤ c) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ x : K, a + FractionalIdeal.spanSingleton R⁰ x * b = c := by
  wlog hb' : b = 1
  · obtain ⟨x, e⟩ := this (a := b⁻¹ * a) (b := 1) (c := b⁻¹ * c)
      (FractionalIdeal.mul_le_mul_left hac _) (by simp [ha, hb]) one_ne_zero rfl
    use x
    simpa [hb, ← mul_assoc, mul_add, mul_comm b (.spanSingleton _ _)] using congr(b * $e)
  subst hb'
  have h0 : FractionalIdeal.spanSingleton R⁰ ((algebraMap R K) (↑a.den * ↑c.den)) ≠ 0 := by
    simp [FractionalIdeal.spanSingleton_eq_zero_iff]
  have H : Ideal.span {c.den.1} * a.num ≤ c.num * Ideal.span {a.den.1} := by
    rw [← FractionalIdeal.coeIdeal_le_coeIdeal K]
    simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton, ←
      FractionalIdeal.den_mul_self_eq_num']
    ring_nf
    exact FractionalIdeal.mul_le_mul_left hac _
  obtain ⟨x, hx⟩ := exists_sup_span_eq H
    (by simpa using FractionalIdeal.num_eq_zero_iff.not.mpr ha)
  refine ⟨algebraMap R K x / algebraMap R K (a.den.1 * c.den.1), ?_⟩
  refine mul_left_injective₀ (b := .spanSingleton _
    (algebraMap R K (a.den.1 * c.den.1))) ?_ ?_
  · simp [FractionalIdeal.spanSingleton_eq_zero_iff]
  · simp only [map_mul, mul_one, add_mul, FractionalIdeal.spanSingleton_mul_spanSingleton,
      isUnit_iff_ne_zero, ne_eq, mul_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff, coe_ne_zero,
      or_self, not_false_eq_true, IsUnit.div_mul_cancel]
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, ← mul_assoc, mul_comm a,
      FractionalIdeal.den_mul_self_eq_num', ← mul_assoc, mul_right_comm,
      mul_comm c, FractionalIdeal.den_mul_self_eq_num', mul_comm]
    simp_rw [← FractionalIdeal.coeIdeal_span_singleton, ← FractionalIdeal.coeIdeal_mul,
      ← hx, ← FractionalIdeal.coeIdeal_sup]

/-- `c / b (mod a)` is an arbitrary `x` such that `c = bx + a`.
This is zero if the above is not possible, i.e. when `a = 0` or `b = 0` or `¬ a ≤ c`. -/
noncomputable
def FractionalIdeal.divMod (c b a : FractionalIdeal R⁰ K) : K :=
  letI := Classical.propDecidable
  if h : a ≤ c ∧ a ≠ 0 ∧ b ≠ 0 then
    (IsDedekindDomain.exists_add_spanSingleton_mul_eq h.1 h.2.1 h.2.2).choose else 0

lemma FractionalIdeal.divMod_spec
    {a b c : FractionalIdeal R⁰ K} (hac : a ≤ c) (ha : a ≠ 0) (hb : b ≠ 0) :
    a + spanSingleton R⁰ (c.divMod b a) * b = c := by
  rw [divMod, dif_pos ⟨hac, ha, hb⟩]
  exact (IsDedekindDomain.exists_add_spanSingleton_mul_eq hac ha hb).choose_spec

@[simp]
lemma FractionalIdeal.divMod_zero_left {I J : FractionalIdeal R⁰ K} : I.divMod 0 J = 0 := by
  simp [divMod]

@[simp]
lemma FractionalIdeal.divMod_zero_right {I J : FractionalIdeal R⁰ K} : I.divMod J 0 = 0 := by
  simp [divMod]

lemma FractionalIdeal.divMod_zero_of_not_le {a b c : FractionalIdeal R⁰ K} (hac : ¬ a ≤ c) :
    c.divMod b a = 0 := by
  simp [divMod, hac]

omit [IsDedekindDomain R] in
lemma FractionalIdeal.coeIdeal_inf (I J : Ideal R) :
    (↑(I ⊓ J) : FractionalIdeal R⁰ K) = ↑I ⊓ ↑J := by
  apply coeToSubmodule_injective
  exact Submodule.map_inf (Algebra.linearMap R K) (FaithfulSMul.algebraMap_injective R K)

lemma FractionalIdeal.inf_mul_add (I J : FractionalIdeal R⁰ K) :
    (I ⊓ J) * (I + J) = I * J := by
  apply mul_left_injective₀ (b := spanSingleton R⁰ (algebraMap R K
    (I.den.1 * I.den.1 * J.den.1 * J.den.1))) (by simp [spanSingleton_eq_zero_iff])
  have := Ideal.sup_mul_inf (Ideal.span {J.den.1} * I.num) (Ideal.span {I.den.1} * J.num)
  simp only [← coeIdeal_inj (K := K), coeIdeal_mul, coeIdeal_sup, coeIdeal_inf,
    ← den_mul_self_eq_num', coeIdeal_span_singleton] at this
  rw [mul_left_comm, ← mul_add, ← mul_add, ← mul_inf₀ (zero_le _),
    ← mul_inf₀ (zero_le _)] at this
  simp only [_root_.map_mul, ← spanSingleton_mul_spanSingleton]
  convert this using 1 <;> ring

/-- Let `I J I' J'` be nonzero fractional ideals in a dedekind domain with `J ≤ I` and `J' ≤ I'`.
If `I/J = I'/J'` in the group of fractional ideals, then `I/J ≃ I'/J'` as quotient `R`-modules. -/
noncomputable
def FractionalIdeal.quotientEquiv (I J I' J' : FractionalIdeal R⁰ K)
    (H : I * J' = I' * J) (h : J ≤ I) (h' : J' ≤ I') (hJ' : J' ≠ 0) (hI : I ≠ 0) :
    (I ⧸ J.coeToSubmodule.comap I.coeToSubmodule.subtype) ≃ₗ[R]
      I' ⧸ J'.coeToSubmodule.comap I'.coeToSubmodule.subtype := by
  haveI : J' ⊓ spanSingleton R⁰ (I'.divMod I J') * I = spanSingleton R⁰ (I'.divMod I J') * J := by
    have := FractionalIdeal.inf_mul_add J' (spanSingleton R⁰ (I'.divMod I J') * I)
    rwa [divMod_spec h' hJ' hI, mul_left_comm, mul_comm J' I, H, mul_comm I' J,
      ← mul_assoc, (mul_left_injective₀ _).eq_iff] at this
    rintro rfl
    exact hJ' (by simpa using h')
  refine .ofBijective (Submodule.mapQ _ _ (LinearMap.restrict
    (Algebra.lsmul R _ _ (I'.divMod I J')) ?_) ?_) ⟨?_, ?_⟩
  · intro x hx
    refine (divMod_spec h' hJ' hI).le ?_
    exact Submodule.mem_sup_right (mul_mem_mul (mem_spanSingleton_self _ _) hx)
  · rw [← Submodule.comap_comp, LinearMap.subtype_comp_restrict, LinearMap.domRestrict,
      Submodule.comap_comp]
    refine Submodule.comap_mono ?_
    intro x hx
    refine (Submodule.mem_inf.mp (this.ge ?_)).1
    simp only [val_eq_coe, Submodule.mem_comap, Algebra.lsmul_coe, smul_eq_mul, mem_coe]
    exact mul_mem_mul (mem_spanSingleton_self _ _) hx
  · rw [← LinearMap.ker_eq_bot, Submodule.mapQ, Submodule.ker_liftQ,
      LinearMap.ker_comp, Submodule.ker_mkQ, ← Submodule.comap_comp,
      LinearMap.subtype_comp_restrict, ← le_bot_iff, Submodule.map_le_iff_le_comap,
      Submodule.comap_bot, Submodule.ker_mkQ, LinearMap.domRestrict,
      Submodule.comap_comp, ← Submodule.map_le_iff_le_comap,
      Submodule.map_comap_eq, Submodule.range_subtype]
    by_cases H' : I'.divMod I J' = 0
    · obtain rfl : J' = I' := by simpa [H'] using divMod_spec h' hJ' hI
      obtain rfl : I = J := mul_left_injective₀ hJ' (H.trans (mul_comm _ _))
      exact inf_le_left
    rw [← inv_mul_eq_iff_eq_mul₀ (by simpa [spanSingleton_eq_zero_iff] using H'), mul_inf₀
      (zero_le _), inv_mul_cancel_left₀ (by simpa [spanSingleton_eq_zero_iff] using H')] at this
    rw [← this, inf_comm, coe_inf]
    refine inf_le_inf ?_ le_rfl
    intro x hx
    rw [spanSingleton_inv]
    convert mul_mem_mul (mem_spanSingleton_self _ _) hx
    simp [H']
  · have H : Submodule.map (Algebra.lsmul R R K (I'.divMod I J')) ↑I =
        (spanSingleton R⁰ (I'.divMod I J') * I) := by
      ext x
      simp [Submodule.mem_span_singleton_mul]
    rw [← LinearMap.range_eq_top, Submodule.mapQ, Submodule.range_liftQ,
      LinearMap.range_comp, LinearMap.restrict, LinearMap.range_codRestrict,
      LinearMap.range_domRestrict, ← top_le_iff, H,
      ← LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _),
      ← Submodule.map_top, Submodule.map_le_iff_le_comap, Submodule.comap_map_eq, Submodule.ker_mkQ,
      ← Submodule.map_le_map_iff_of_injective I'.coeToSubmodule.injective_subtype,
      Submodule.map_top, Submodule.map_sup,
      Submodule.map_comap_eq, Submodule.map_comap_eq, Submodule.range_subtype, sup_comm,
      inf_eq_right.mpr, inf_eq_right.mpr]
    · exact le_trans (divMod_spec h' hJ' hI).ge (by simp)
    · exact le_trans (by simp) (divMod_spec h' hJ' hI).le
    · exact h'

end IsDedekindDomain
