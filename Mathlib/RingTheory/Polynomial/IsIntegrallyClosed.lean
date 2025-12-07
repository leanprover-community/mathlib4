import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot

section

open scoped nonZeroDivisors

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

variable (R) in
/-- An element `s` in an `R`-algebra is almost integral if there exists `r ∈ R⁰` such that
`r • s ^ n ∈ R` for all `n`. -/
@[stacks 00GW]
def IsAlmostIntegral (s : S) : Prop := ∃ r ∈ R⁰, ∀ n, r • s ^ n ∈ (algebraMap R S).range

variable (R S) in
/-- The complete integral closure is the subalgebra of almost integral elements. -/
def completeIntegralClosure : Subalgebra R S where
  carrier := { s | IsAlmostIntegral R s }
  mul_mem' := by
    rintro a b ⟨r, hr, hr'⟩ ⟨s, hs, hs'⟩
    refine ⟨r * s, mul_mem hr hs, fun n ↦ ?_⟩
    rw [mul_pow, mul_smul_mul_comm]
    exact mul_mem (hr' _) (hs' _)
  add_mem' := by
    rintro a b ⟨r, hr, hr'⟩ ⟨s, hs, hs'⟩
    refine ⟨r * s, mul_mem hr hs, fun n ↦ ?_⟩
    simp only [add_pow, Finset.smul_sum, ← smul_mul_assoc _ (_ * _),
      ← smul_mul_smul_comm _ (a ^ _)]
    exact sum_mem fun i _ ↦ mul_mem (mul_mem (hr' _) (hs' _)) (by simp)
  algebraMap_mem' r := ⟨1, one_mem _, by simp [← map_pow]⟩

lemma mem_completeIntegralClosure {x : S} :
    x ∈ completeIntegralClosure R S ↔ IsAlmostIntegral R x := .rfl

lemma IsIntegral.isAlmostIntegral_of_exists_smul_mem_range
    {s : S} (H : IsIntegral R s) (h : ∃ t ∈ R⁰, t • s ∈ (algebraMap R S).range) :
    IsAlmostIntegral R s := by
  obtain ⟨b, hb', hb⟩ :
      ∃ b ∈ R⁰, ∀ i < (minpoly R s).natDegree, (b • s ^ i) ∈ (algebraMap R S).range := by
    obtain ⟨t, ht, ht'⟩ := h
    refine ⟨t ^ (minpoly R s).natDegree, pow_mem ht _, fun i hi ↦ ?_⟩
    rw [← Nat.sub_add_cancel hi.le, pow_add, mul_smul, ← smul_pow]
    exact (AlgHom.range (Algebra.ofId _ _)).smul_mem (Subalgebra.pow_mem _ ht' _) _
  refine ⟨b, hb', fun n ↦ ?_⟩
  induction n using Nat.strong_induction_on with | h n IH =>
  obtain hn | hn := lt_or_ge n (minpoly R s).natDegree
  · exact hb _ (by simpa)
  have := minpoly.aeval R s
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, add_eq_zero_iff_eq_neg',
    Polynomial.coeff_natDegree, minpoly.monic H, one_smul] at this
  rw [← Nat.sub_add_cancel hn, pow_add, this, mul_neg, smul_neg, Finset.mul_sum, Finset.smul_sum]
  simp_rw [mul_smul_comm, ← pow_add, smul_comm b]
  refine neg_mem (sum_mem fun i hi ↦ (AlgHom.range (Algebra.ofId _ _)).smul_mem (IH _ ?_) _)
  simp only [Finset.mem_range] at hi
  cutsat

lemma IsIntegral.isAlmostIntegral_of_isLocalization
    {s : S} (H : IsIntegral R s) (M : Submonoid R) (hM : M ≤ R⁰) [IsLocalization M S] :
    IsAlmostIntegral R s := by
  obtain ⟨s, t, rfl⟩ := IsLocalization.exists_mk'_eq M s
  exact H.isAlmostIntegral_of_exists_smul_mem_range ⟨t, hM t.2, by simp⟩

lemma IsIntegral.isAlmostIntegral [IsFractionRing R S]
    {s : S} (H : IsIntegral R s) : IsAlmostIntegral R s :=
  H.isAlmostIntegral_of_isLocalization _ le_rfl

lemma IsAlmostIntegral.isIntegral_of_nonZeroDivisors_le_comap
    {s : S} (H : IsAlmostIntegral R s) [IsNoetherianRing R]
    (H' : R⁰ ≤ S⁰.comap (algebraMap R S)) : IsIntegral R s := by
  obtain ⟨r, hr, hr'⟩ := H
  let f : Algebra.adjoin R {s} →ₗ[R]
      Submodule.span R {Localization.Away.invSelf (algebraMap R S r)} :=
    (IsScalarTower.toAlgHom R S (Localization.Away (algebraMap R S r))).toLinearMap.restrict
      (p := (Algebra.adjoin R {s}).toSubmodule) <| by
    change (Algebra.adjoin R {s}).toSubmodule ≤ (Submodule.span _ _).comap _
    rw [Algebra.adjoin_eq_span, ← Submonoid.powers_eq_closure, Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    obtain ⟨a, ha⟩ := hr' n
    refine Submodule.mem_span_singleton.mpr ⟨a, ?_⟩
    suffices algebraMap _ _ (s ^ n) * algebraMap _ _ ((algebraMap R S) r) *
        Localization.Away.invSelf ((algebraMap R S) r) = algebraMap S _ (s ^ n) by
      simpa [Algebra.smul_def, IsScalarTower.algebraMap_apply R S (Localization.Away _),
        ha, mul_assoc, mul_left_comm] using this
    simp [mul_assoc, Localization.Away.invSelf, Localization.mk_eq_mk']
  have : Function.Injective f := by
    have : Function.Injective (algebraMap S (Localization.Away (algebraMap R S r))) := by
      apply IsLocalization.injective (M := .powers (algebraMap R S r))
      exact Submonoid.powers_le.mpr (H' hr)
    exact fun x y e ↦ Subtype.ext (this congr($e))
  have : (Algebra.adjoin R {s}).toSubmodule.FG := by
    rw [← Submodule.fg_top, ← Module.finite_def]
    exact .of_injective f this
  exact .of_mem_of_fg _ this _ (Algebra.self_mem_adjoin_singleton R s)

lemma IsAlmostIntegral.isIntegral [IsNoetherianRing R] [IsDomain S] [FaithfulSMul R S]
    {s : S} (H : IsAlmostIntegral R s) : IsIntegral R s := by
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain
  exact H.isIntegral_of_nonZeroDivisors_le_comap fun _ ↦ by simp

lemma isAlmostIntegral_iff_isIntegral [IsNoetherianRing R] [IsDomain R] [IsFractionRing R S]
    {s : S} : IsAlmostIntegral R s ↔ IsIntegral R s :=
  letI := IsFractionRing.isDomain R (K := S)
  ⟨IsAlmostIntegral.isIntegral, IsIntegral.isAlmostIntegral⟩

open Polynomial

attribute [local instance] Polynomial.algebra

lemma IsAlmostIntegral.coeff
    [IsDomain R] [FaithfulSMul R S]
    {p : S[X]} (hp : IsAlmostIntegral R[X] p) (i : ℕ) :
    IsAlmostIntegral R (p.coeff i) := by
  have H {q : S[X]} (hq : IsAlmostIntegral R[X] q) : IsAlmostIntegral R q.leadingCoeff := by
    obtain ⟨p, hp, hp'⟩ := hq
    refine ⟨p.leadingCoeff, by simpa using hp, fun n ↦ ?_⟩
    obtain ⟨r, hr⟩ := hp' n
    simp only [Algebra.smul_def, algebraMap_def, coe_mapRingHom] at hr ⊢
    by_cases h : algebraMap R S p.leadingCoeff * q.leadingCoeff ^ n = 0
    · simp [h]
    have h' : q.leadingCoeff ^ n ≠ 0 := by aesop
    use r.leadingCoeff
    simp only [← leadingCoeff_map_of_injective (FaithfulSMul.algebraMap_injective R S), hr] at h ⊢
    rw [← leadingCoeff_pow' h'] at h ⊢
    rw [leadingCoeff_mul' h]
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with | h n IH =>
  by_cases hp' : p.natDegree = 0
  · obtain ⟨p, rfl⟩ := natDegree_eq_zero.mp hp'
    simp only [coeff_C]
    split_ifs with h
    · simpa using H hp
    · exact (completeIntegralClosure R S).zero_mem
  by_cases hi : i = p.natDegree
  · simp [hi, H hp]
  have : IsAlmostIntegral R[X] p.eraseLead := by
    rw [← self_sub_monomial_natDegree_leadingCoeff, ← mem_completeIntegralClosure,
      ← C_mul_X_pow_eq_monomial, ← map_X (algebraMap R S), ← Polynomial.map_pow]
    refine sub_mem hp (mul_mem ?_ (algebraMap_mem (R := R[X]) _ _))
    obtain ⟨r, hr, hr'⟩ := H hp
    refine ⟨C r, by simpa using hr, fun n ↦ ?_⟩
    obtain ⟨s, hs⟩ := hr' n
    exact ⟨C s, by simp [Algebra.smul_def, hs]⟩
  simpa [hi, eraseLead_coeff_of_ne] using
    IH (p := p.eraseLead) _ (p.eraseLead_natDegree_le.trans_lt (by cutsat)) this rfl

lemma IsIntegral.coeff_of_exists_smul_mem_lifts
    [FaithfulSMul R S] [IsDomain S]
    {p : S[X]} (hp : IsIntegral R[X] p) (hp' : ∃ r ∈ R⁰, r • p ∈ lifts (algebraMap R S)) (i : ℕ) :
    IsIntegral R (p.coeff i) := by
  classical
  have := (FaithfulSMul.algebraMap_injective R S).isDomain
  obtain ⟨r, hr, q, hq⟩ := hp'
  let R' := Algebra.adjoin ℤ
    (↑((minpoly R[X] p).coeffs.biUnion coeffs ∪ (insert r q.coeffs)) : Set R)
  have : Algebra.FiniteType ℤ R' := ⟨(Subalgebra.fg_top _).mpr <| Subalgebra.fg_adjoin_finset _⟩
  have := Algebra.FiniteType.isNoetherianRing ℤ R'
  have : IsIntegral R'[X] p := by
    suffices minpoly R[X] p ∈ lifts (mapRingHom (algebraMap R' R)) by
      obtain ⟨q, hq, -, hq'⟩ := lifts_and_degree_eq_and_monic this (minpoly.monic hp)
      refine ⟨q, hq', ?_⟩
      simpa only [algebraMap_def, IsScalarTower.algebraMap_eq R' R S, ← mapRingHom_comp,
        ← eval₂_map, hq] using minpoly.aeval R[X] p
    refine (lifts_iff_coeff_lifts _).mpr fun n ↦ (lifts_iff_coeff_lifts _).mpr fun m ↦ ?_
    simp only [Subalgebra.setRange_algebraMap, SetLike.mem_coe]
    by_cases h : ((minpoly R[X] p).coeff n).coeff m = 0
    · simp [h]
    refine Algebra.subset_adjoin (Finset.mem_union_left _ ?_)
    exact Finset.mem_biUnion.mpr ⟨_, coeff_mem_coeffs (by aesop), coeff_mem_coeffs h⟩
  refine ((this.isAlmostIntegral_of_exists_smul_mem_range ?_).coeff i).isIntegral.tower_top
  refine ⟨C ⟨r, Algebra.subset_adjoin (Finset.mem_union_right _ (by simp))⟩, ?_, ?_⟩
  · simpa [← SetLike.coe_eq_coe] using hr
  · simp only [algebraMap_def, IsScalarTower.algebraMap_eq R' R S, ← mapRingHom_comp,
      ← RingHom.map_range]
    refine ⟨q, (lifts_iff_coeff_lifts _).mpr fun n ↦ ?_, by simpa [Algebra.smul_def] using hq⟩
    simp only [Subalgebra.setRange_algebraMap, SetLike.mem_coe]
    by_cases h : q.coeff n = 0
    · simp [h]
    · exact Algebra.subset_adjoin (Finset.mem_union_right _ (by simp [coeff_mem_coeffs h]))

lemma IsIntegral.coeff_of_isFractionRing
    [IsFractionRing R S] [IsDomain R]
    {p : S[X]} (hp : IsIntegral R[X] p) (i : ℕ) :
    IsIntegral R (p.coeff i) := by
  have := IsFractionRing.isDomain R (K := S)
  refine hp.coeff_of_exists_smul_mem_lifts ?_ i
  obtain ⟨r, hr⟩ := IsLocalization.integerNormalization_map_to_map R⁰ p
  exact ⟨r, r.2, ⟨_, hr⟩⟩

lemma IsIntegrallyClosed.of_isIntegrallyClosedIn
    (R K : Type*) [CommRing R] [Field K] [Algebra R K] [FaithfulSMul R K]
    [IsIntegrallyClosedIn R K] : IsIntegrallyClosed R := by
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R K).isDomain _
  let f : FractionRing R →ₐ[R] K := IsFractionRing.liftAlgHom (g := Algebra.ofId _ _)
    (FaithfulSMul.algebraMap_injective R K)
  rw [isIntegrallyClosed_iff (K := FractionRing R)]
  intro x hx
  convert (IsIntegralClosure.isIntegral_iff (A := R)).mp (hx.map f)
  simp [← f.toRingHom.injective.eq_iff]

lemma IsIntegralClosure.of_isIntegralClosure_of_isIntegrallyClosedIn
    (R S T U : Type*) [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R T] [Algebra S T] [Algebra R U] [Algebra S U] [Algebra T U]
    [IsScalarTower S T U] [IsScalarTower R T U]
    [IsIntegralClosure S R T] [IsIntegrallyClosedIn T U] : IsIntegralClosure S R U := by
  refine ⟨?_, ?_⟩
  · rw [IsScalarTower.algebraMap_eq S T U]
    exact (IsIntegralClosure.algebraMap_injective T T U).comp
      (IsIntegralClosure.algebraMap_injective S R T)
  · intro x
    refine ⟨fun h ↦ ?_, ?_⟩
    · obtain ⟨x, rfl⟩ := (IsIntegralClosure.isIntegral_iff (R := T) (A := T)).mp h.tower_top
      rw [isIntegral_algebraMap_iff (IsIntegralClosure.algebraMap_injective T T U)] at h
      obtain ⟨x, rfl⟩ := (IsIntegralClosure.isIntegral_iff (R := R) (A := S)).mp h
      exact ⟨x, IsScalarTower.algebraMap_apply ..⟩
    · rintro ⟨x, rfl⟩
      rw [IsScalarTower.algebraMap_apply S T U]
      exact ((IsIntegralClosure.isIntegral_iff (A := S) (R := R) (B := T)).mpr ⟨x, rfl⟩).map
        (IsScalarTower.toAlgHom R T U)

lemma IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [IsDomain S] [FaithfulSMul R S]
     [IsIntegrallyClosed S] [IsIntegrallyClosedIn R S] : IsIntegrallyClosed R :=
  have : IsIntegrallyClosedIn R (FractionRing S) :=
    .of_isIntegralClosure_of_isIntegrallyClosedIn _ _ S _
  .of_isIntegrallyClosedIn R (FractionRing S)

instance {R : Type*} [CommRing R] :
    IsIntegralClosure R R R :=
  ⟨Function.injective_id, by simp [Algebra.IsIntegral.isIntegral]⟩

instance {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] :
    IsIntegrallyClosed R[X] := by
  let K := FractionRing R
  have : IsIntegrallyClosed K[X] := UniqueFactorizationMonoid.instIsIntegrallyClosed
  suffices IsIntegrallyClosedIn R[X] K[X] from .of_isIntegrallyClosed_of_isIntegrallyClosedIn _ K[X]
  refine isIntegrallyClosedIn_iff.mpr ⟨map_injective _ (IsFractionRing.injective _ _), ?_⟩
  refine fun {p} hp ↦ (lifts_iff_coeff_lifts _).mpr fun n ↦ ?_
  exact IsIntegrallyClosed.isIntegral_iff.mp (hp.coeff_of_isFractionRing _)

end
