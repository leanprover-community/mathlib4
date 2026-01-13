/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Algebraic.StronglyTranscendental
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.RingTheory.QuasiFinite
public import Mathlib.RingTheory.ZariskisMainTheorem

/-! # Algebraic ZMT -/

@[expose] public section

variable {R S T : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

open scoped TensorProduct nonZeroDivisors

open Polynomial

attribute [local instance 1100] Algebra.toSMul in
/-- Given a map `φ : R[X] →ₐ[R] S`. Suppose `t = φ r / φ p` is integral over `R[X]` where
`p` is monic with `deg p > deg r`, then `t` is integral over `R`. -/
lemma isIntegral_of_isIntegralElem_of_monic_of_natDegree_lt
    (φ : R[X] →ₐ[R] S) (t : S) (ht : φ.IsIntegralElem t) (p r : R[X]) (hpm : p.Monic)
    (hpr : r.natDegree < p.natDegree) (hp : φ p * t = φ r) : IsIntegral R t := by
  let St := Localization.Away t
  let t' : St := IsLocalization.Away.invSelf t
  have ht't : t' * algebraMap S St t = 1 := by rw [mul_comm, IsLocalization.Away.mul_invSelf]
  let R₁ := Algebra.adjoin R {t'}
  let R₂ := Algebra.adjoin R₁ {algebraMap S St (φ X)}
  letI : Algebra R₁ R₂ := R₂.algebra
  letI : Algebra R₂ St := R₂.toAlgebra
  letI : Algebra R₁ St := R₁.toAlgebra
  haveI : IsScalarTower R₁ R₂ St := Subalgebra.isScalarTower_mid _
  have : Algebra.IsIntegral R₁ R₂ := by
    cases subsingleton_or_nontrivial R₁
    · have := (algebraMap R₁ R₂).codomain_trivial; exact ⟨(Subsingleton.elim · 0 ▸ isIntegral_zero)⟩
    rw [← le_integralClosure_iff_isIntegral, Algebra.adjoin_le_iff, Set.singleton_subset_iff,
      SetLike.mem_coe, mem_integralClosure_iff]
    refine ⟨p.map (algebraMap R R₁) - C ⟨t', Algebra.self_mem_adjoin_singleton R t'⟩ *
        r.map (algebraMap R R₁), (hpm.map _).sub_of_left (degree_lt_degree ?_), ?_⟩
    · grw [natDegree_C_mul_le, natDegree_map_le, hpm.natDegree_map]; assumption
    · simp [← aeval_def, aeval_algebraMap_apply, aeval_algHom_apply,
        ← hp, ← mul_assoc, ht't, mul_right_comm]
  have : IsIntegral R₁ (algebraMap S St t) := by
    refine isIntegral_trans (A := R₂) (algebraMap S St t) ?_
    obtain ⟨q, hq, hq'⟩ := ht
    refine ⟨q.map (aeval ⟨_, Algebra.self_mem_adjoin_singleton _ _⟩).toRingHom, hq.map _, ?_⟩
    rw [AlgHom.toRingHom_eq_coe, eval₂_map, ← map_zero (algebraMap S St), ← hq',
      hom_eval₂]
    congr 1
    ext <;> simp [- Polynomial.algebraMap_apply, ← algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  simpa using IsLocalization.Away.isIntegral_of_isIntegral_map t
                (isIntegral_of_isIntegral_adjoin_of_mul_eq_one _ _ ht't this)

@[stacks 00PT]
lemma exists_isIntegral_sub_of_isIntegralElem_of_mul_mem_range
    (φ : R[X] →ₐ[R] S) (t : S) (ht : φ.IsIntegralElem t) (p : R[X]) (hpm : p.Monic)
    (hp : φ p * t ∈ φ.range) : ∃ q, IsIntegral R (t - φ q) := by
  obtain ⟨r, hr : φ r = _⟩ := hp
  obtain rfl | hp1 := eq_or_ne p 1
  · exact ⟨r, by simp_all [isIntegral_zero]⟩
  exact ⟨_, isIntegral_of_isIntegralElem_of_monic_of_natDegree_lt φ (t - φ (r /ₘ p))
    (ht.sub _ φ.isIntegralElem_map) p (r %ₘ p) hpm (natDegree_modByMonic_lt _ hpm hp1)
    (by simp [mul_sub, ← hr, sub_eq_iff_eq_add, ← map_mul, ← map_add, r.modByMonic_add_div hpm])⟩

open IsScalarTower in
attribute [local simp] IsLocalization.map_eq aeval_algebraMap_apply aeval_algHom_apply in
@[stacks 00PV]
lemma exists_isIntegral_leadingCoeff_pow_smul_sub_of_isIntegralElem_of_mul_mem_range
    (φ : R[X] →ₐ[R] S) (t : S) (ht : φ.IsIntegralElem t) (p : R[X])
    (hp : φ p * t ∈ φ.range) : ∃ q n, IsIntegral R (p.leadingCoeff ^ n • t - φ q) := by
  set a := p.leadingCoeff
  let R' := Localization.Away a
  let S' := Localization.Away (algebraMap R S a)
  letI : Algebra R' S' := (Localization.awayMap (algebraMap R S) a).toAlgebra
  have : IsScalarTower R R' S' := .of_algebraMap_eq (by
    simp +zetaDelta [RingHom.algebraMap_toAlgebra, IsLocalization.Away.map, ← algebraMap_apply R S])
  have ha : IsUnit (algebraMap R R' a) := IsLocalization.Away.algebraMap_isUnit a
  have H : (aeval ((algebraMap S S') (φ X))).toRingHom.comp (mapRingHom (algebraMap R R')) =
    (algebraMap S S').comp φ := by ext <;>
      simp [- Polynomial.algebraMap_apply, ← Polynomial.algebraMap_eq, ← algebraMap_apply]
  obtain ⟨q, hq⟩ := exists_isIntegral_sub_of_isIntegralElem_of_mul_mem_range (R := R')
    (aeval (algebraMap S S' (φ X))) (algebraMap S S' t) (by
      obtain ⟨q, hqm, hq⟩ := ht
      refine ⟨q.map (mapRingHom (algebraMap _ _)), hqm.map _, ?_⟩
      rw [eval₂_map, H, ← hom_eval₂, ← AlgHom.toRingHom_eq_coe, hq, map_zero])
    (C ha.unit⁻¹.1 * p.map (algebraMap _ _)) (by
      nontriviality R'
      simp [Monic, leadingCoeff_C_mul_of_isUnit,
        leadingCoeff_map_of_leadingCoeff_ne_zero _ ha.ne_zero, a]) (by
      obtain ⟨r, hr : φ r = _⟩ := hp
      use C ha.unit⁻¹.1 * mapRingHom (algebraMap R R') r
      simp [aeval_algebraMap_apply, aeval_algHom_apply, hr, mul_assoc])
  obtain ⟨⟨_, n, rfl⟩, e⟩ := IsLocalization.integerNormalization_map_to_map (.powers a) q
  generalize IsLocalization.integerNormalization (.powers a) q = q' at e
  have : IsIntegral R' ((algebraMap S S') (a ^ n • t - φ q')) := by
    have : algebraMap S S' (φ q') = (algebraMap R S' a) ^ n * aeval (algebraMap S S' (φ X)) q := by
      simpa [Algebra.smul_def, aeval_algebraMap_apply, aeval_algHom_apply, ← algebraMap_apply] using
        congr(aeval (algebraMap S S' (φ X)) $e)
    simpa [Algebra.smul_def, ← mul_sub, ← algebraMap_apply, this] using
      (isIntegral_algebraMap (A := S') (x := algebraMap R R' a ^ n)).mul hq
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := this.exists_multiple_integral_of_isLocalization (.powers a) _
  simp only [Algebra.smul_def, Submonoid.smul_def, algebraMap_apply R S S', ← map_mul] at hm
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := IsLocalization.exists_isIntegral_smul_of_isIntegral_map (.powers a) hm
  refine ⟨C a ^ (k + m) * q', k + m + n, ?_⟩
  convert hk using 1
  simp only [Algebra.smul_def, map_pow, ← Polynomial.algebraMap_eq, map_mul, AlgHom.commutes]
  ring

@[stacks 00PX]
lemma exists_leadingCoeff_pow_smul_mem_conductor
    (hRS : integralClosure R S = ⊥) -- `IsIntegrallyClosedIn` but without injective assumption
    (φ : R[X] →ₐ[R] S) (hφ : φ.toRingHom.Finite)
    (t : S) (p : R[X]) (hp : φ p * t ∈ conductor R (φ X)) :
    ∃ n, p.leadingCoeff ^ n • t ∈ conductor R (φ X) := by
  algebraize [φ.toRingHom]
  have : IsScalarTower R R[X] S := .of_algebraMap_eq' φ.comp_algebraMap.symm
  have (x : _) : ∃ n, p.leadingCoeff ^ n • (t * x) ∈ φ.range := by
    have : φ p * t * x ∈ φ.range := by simpa [← AlgHom.map_adjoin_singleton] using hp x
    obtain ⟨q, n, hn⟩ :=
      exists_isIntegral_leadingCoeff_pow_smul_sub_of_isIntegralElem_of_mul_mem_range φ _
        (hφ.to_isIntegral (t * x)) p (by convert this using 1; ring)
    obtain ⟨r, hr : algebraMap _ _ r = _⟩ := hRS.le hn
    exact ⟨n, (C r + q), by simp [← Polynomial.algebraMap_eq, - Polynomial.algebraMap_apply, hr]⟩
  choose n hn using this
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R[X]) (M := S)
  refine ⟨s.sup n, fun x ↦ ?_⟩
  rw [← AlgHom.map_adjoin_singleton, adjoin_X, Algebra.map_top, Algebra.smul_mul_assoc]
  induction hs.ge (Set.mem_univ x) using Submodule.span_induction with
  | mem x h =>
    rw [← Nat.sub_add_cancel (s.le_sup h), pow_add, mul_smul]
    exact Subalgebra.smul_mem _ (hn _) _
  | zero => simp
  | add x y _ _ hx hy => simpa only [mul_add, smul_add] using add_mem hx hy
  | smul a x hx IH =>
    rw [mul_smul_comm, smul_comm, Algebra.smul_def]
    exact mul_mem (AlgHom.mem_range_self _ _) IH

@[stacks 00PY]
lemma exists_leadingCoeff_pow_smul_mem_radical_conductor
    (hRS : integralClosure R S = ⊥) -- `IsIntegrallyClosedIn` but without injective assumption
    (φ : R[X] →ₐ[R] S) (hφ : φ.toRingHom.Finite)
    (t : S) (p : R[X]) (hp : φ p * t ∈ (conductor R (φ X)).radical) (i : ℕ) :
    p.coeff i • t ∈ (conductor R (φ X)).radical := by
  wlog hi : i = p.natDegree generalizing p i
  · clear hi
    simp only [forall_eq, coeff_natDegree] at this
    induction hpn : p.natDegree using Nat.strong_induction_on generalizing p with
    | h n IH =>
    cases n with
    | zero =>
      obtain hi' | hi' := lt_or_ge p.natDegree i
      · simp [coeff_eq_zero_of_natDegree_lt hi']
      · simpa [← coeff_natDegree, hpn, show i = 0 by aesop] using this _ hp
    | succ n =>
      obtain hi' | hi' := eq_or_ne i p.natDegree
      · simpa [hi'] using this _ hp
      have : φ p.eraseLead * t ∈ (conductor R (φ X)).radical := by
        simp only [← self_sub_C_mul_X_pow, map_sub, ← algebraMap_eq, map_mul, AlgHom.commutes,
          map_pow, sub_mul, mul_right_comm _ _ t, ← Algebra.smul_def _ t]
        exact sub_mem hp (Ideal.mul_mem_right _ _ (this _ hp))
      simpa [eraseLead_coeff, hi'] using
        IH _ ((eraseLead_natDegree_le _).trans_lt (by aesop)) _ this rfl
  obtain ⟨n, hn⟩ := hp
  obtain ⟨k, hk⟩ := exists_leadingCoeff_pow_smul_mem_conductor hRS φ hφ (t ^ n) (p ^ n)
    (by simpa [mul_pow] using hn)
  by_cases hpn : p.leadingCoeff ^ n = 0
  · use n; simp [_root_.smul_pow, hpn, hi]
  rw [leadingCoeff_pow' hpn, ← pow_mul] at hk
  refine ⟨n * k + n, ?_⟩
  rw [_root_.smul_pow,  pow_add, add_comm, pow_add, mul_smul_mul_comm, hi]
  exact Ideal.mul_mem_right _ _ hk

@[stacks 00PY]
lemma isStronglyTranscendental_mk_radical_conductor
    (hRS : integralClosure R S = ⊥) -- `IsIntegrallyClosedIn` but without injective assumption
    (x : S) (hx : (aeval (R := R) x).Finite) :
    IsStronglyTranscendental R (Ideal.Quotient.mk (conductor R x).radical x) := by
  refine Ideal.Quotient.mk_surjective.forall.mpr fun u p e ↦ ?_
  rw [← Ideal.Quotient.algebraMap_eq, aeval_algebraMap_apply, Ideal.Quotient.algebraMap_eq,
    ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at e
  ext i
  simpa [← Ideal.Quotient.mk_algebraMap, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Algebra.smul_def] using exists_leadingCoeff_pow_smul_mem_radical_conductor hRS _ hx u p
      (by simpa using e) i

attribute [local instance] Polynomial.isLocalization Polynomial.algebra

lemma not_quasiFiniteAt_of_stronglyTranscendental_of_isIntegrallyClosed [FaithfulSMul R S]
    [IsIntegrallyClosed R] [IsDomain S]
    {x : S} (hx : IsStronglyTranscendental R x) (hx' : (aeval (R := R) x).Finite)
    (P : Ideal S) [P.IsPrime] : ¬ Algebra.QuasiFiniteAt R P := by
  intro H
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain
  have hf' : Function.Injective (aeval (R := R) x) := (injective_iff_map_eq_zero _).mpr
    fun p hp ↦ not_not.mp fun hp' ↦ hx.transcendental ⟨p, hp', hp⟩
  generalize hf : aeval (R := R) x = f at *
  obtain rfl : f X = x := by simp [← hf]
  let := f.toRingHom.toAlgebra
  have := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : Module.Finite R[X] S := RingHom.finite_algebraMap.mpr hx'
  have : FaithfulSMul R[X] S := by
    rw [faithfulSMul_iff_algebraMap_injective, injective_iff_map_eq_zero]
    intro p hp
    by_contra hp'
    exact hx.transcendental ⟨p, hp', by rwa [aeval_algHom_apply, aeval_X_left_apply]⟩
  have : (P.under R).map C < P.under R[X] := Ideal.map_under_lt_comap_of_quasiFiniteAt _ _
  obtain ⟨Q, hQ, _, ⟨e⟩⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (S := S) P this
  refine hQ.ne (Algebra.QuasiFiniteAt.eq_of_le_of_under_eq (R := R) _ _ hQ.le ?_)
  rw [← Ideal.under_under (B := R[X]), ← e]
  ext
  simp [Ideal.mem_map_C_iff, coeff_C, apply_ite]

set_option maxHeartbeats 0 in
attribute [local instance 2000] Algebra.toSMul Subalgebra.toCommRing CommRing.toRing
  Ring.toAddCommGroup AddCommGroup.toAddCommMonoid SetLike.instIsScalarTower
  SetLike.instSMulCommClass Algebra.toModule Module.toDistribMulAction Algebra.id in
@[stacks 00Q1]
lemma not_quasiFiniteAt_of_stronglyTranscendental_of_isDomain [FaithfulSMul R S]
    [IsDomain S]
    {x : S} (hx : IsStronglyTranscendental R x) (hx' : (aeval (R := R) x).Finite)
    (P : Ideal S) [P.IsPrime] : ¬ Algebra.QuasiFiniteAt R P := by
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain
  let K := FractionRing R
  let L := FractionRing S
  let : Algebra K L := FractionRing.liftAlgebra _ _
  let R' := integralClosure R K
  have : IsIntegrallyClosed R' := integralClosure.isIntegrallyClosedOfFiniteExtension K
  let S' : Subalgebra R' L := Algebra.adjoin R' (algebraMap S L).range
  let f : S →ₐ[R] S' := (IsScalarTower.toAlgHom R S L).codRestrict (S'.restrictScalars R) fun x ↦ by
    simpa using show algebraMap S L x ∈ S' from Algebra.subset_adjoin ⟨x, rfl⟩
  have hf' : Function.Injective f :=
    (AlgHom.injective_codRestrict ..).mpr (FaithfulSMul.algebraMap_injective S L)
  let : Algebra R' S' := S'.algebra
  let : Algebra R S' := S'.algebra'
  let : Algebra R R' := R'.algebra
  have : IsScalarTower R R' S' := Subalgebra.instIsScalarTowerSubtypeMem _
  let : Algebra R' (R' ⊗[R] S) := Algebra.TensorProduct.leftAlgebra
  have : FaithfulSMul K L :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap K L).injective
  have : FaithfulSMul R' S' := Subalgebra.faithfulSMul_right _
  have : IsScalarTower R R' (R' ⊗[R] S) := by exact TensorProduct.isScalarTower_left
  let g : R' ⊗[R] S →ₐ[R'] S' := Algebra.TensorProduct.lift
    (Algebra.ofId _ _) f fun _ _ ↦ .all _ _
  have hg : Function.Surjective g := by
    rw [← AlgHom.range_eq_top,
      ← (Subalgebra.map_injective (f := S'.val) Subtype.val_injective).eq_iff, Algebra.map_top]
    refine le_antisymm (Set.image_subset_range S'.val g.range) ?_
    simp only [RingHom.coe_range, Subalgebra.range_val, Algebra.adjoin_le_iff, Subalgebra.coe_map,
      Subalgebra.coe_val, AlgHom.coe_range, Set.range_subset_iff, Set.mem_image, Set.mem_range,
      exists_exists_eq_and, S']
    exact fun y ↦ ⟨1 ⊗ₜ y, by simp [g, S']; rfl⟩
  have hf : f.IsIntegral := by
    have : f = (g.restrictScalars R).comp ((Algebra.TensorProduct.comm _ _ _).toAlgHom.comp
        (IsScalarTower.toAlgHom _ _ _)) := by ext; simp [g]
    simp only [this, AlgEquiv.toAlgHom_eq_coe, AlgHom.toRingHom_eq_coe,
      AlgHom.comp_toRingHom, ← RingHom.comp_assoc]
    refine .trans _ _ (algebraMap_isIntegral_iff.mpr inferInstance) ?_
    exact RingHom.isIntegral_of_surjective _
      (hg.comp (Algebra.TensorProduct.comm _ _ _).surjective)
  have H₁ : IsStronglyTranscendental R' (f x) := by
    refine .of_map (f := S'.val) Subtype.val_injective ?_
    exact ((hx.of_isLocalization S⁰).of_isLocalization_left R⁰).restrictScalars (S := K)
  have H₂ : (aeval (R := R') (f x)).toRingHom.Finite := by
    convert ((RingHom.Finite.of_surjective g.toRingHom hg).comp
      (RingHom.Finite.tensorProductMap (f := AlgHom.id R R') (RingEquiv.refl _).finite hx')).comp
      (polyEquivTensor R R').toRingEquiv.finite using 1
    ext <;> simp [g]
  obtain ⟨⟨Q, _⟩, hQ⟩ := hf.comap_surjective hf' ⟨P, ‹_›⟩
  refine fun H ↦ not_quasiFiniteAt_of_stronglyTranscendental_of_isIntegrallyClosed H₁ H₂ Q ?_
  have : Algebra.QuasiFiniteAt R' (Q.comap g.toRingHom) := .baseChange P _ <| by
    rw [Ideal.comap_comap]
    convert congr(($hQ.symm).1)
    ext; simp [g]
  exact .of_surjectiveOnStalks _ g (RingHom.surjectiveOnStalks_of_surjective hg) _ rfl

@[stacks 00Q2]
nonrec lemma not_quasiFiniteAt_of_stronglyTranscendental [IsReduced S] [FaithfulSMul R S]
    {x : S} (hx : IsStronglyTranscendental R x) (hx' : (aeval (R := R) x).Finite)
    (P : Ideal S) [P.IsPrime] : ¬ Algebra.QuasiFiniteAt R P := by
  intro H
  obtain ⟨p, hp, hpP⟩ := Ideal.exists_minimalPrimes_le (J := P) bot_le
  have := hp.1.1
  have : (P.map (Ideal.Quotient.mk p)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa)
  refine not_quasiFiniteAt_of_stronglyTranscendental_of_isDomain (R := R ⧸ p.under R)
    ((isStronglyTranscendental_mk_of_mem_minimalPrimes hx p hp).of_surjective_left
      Ideal.Quotient.mk_surjective) ?_ (P.map (Ideal.Quotient.mk p)) ?_
  · refine RingHom.Finite.of_comp_finite (f := mapRingHom (Ideal.Quotient.mk _)) ?_
    convert (RingHom.Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := p))).comp hx'
    ext <;> simp
  · suffices Algebra.QuasiFiniteAt R (P.map (Ideal.Quotient.mk p)) from .of_restrictScalars R _ _
    refine .of_surjectiveOnStalks P (Ideal.Quotient.mkₐ _ _)
      (RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective) _ ?_
    refine .trans ?_ (Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective _).symm
    simpa [← RingHom.ker_eq_comap_bot]
namespace Algebra

section FixedUniverse
-- since the lemmas in this section are subsumed by <insert lemma name> anyways.

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

lemma ZariskisMainProperty.of_adjoin_eq_top
    (p : Ideal S) [p.IsPrime] [Algebra.QuasiFiniteAt R p]
    (x : S) (hx : Algebra.adjoin R {x} = ⊤) : ZariskisMainProperty R p := by
  wlog H : integralClosure R S = ⊥
  · letI inst : Algebra (integralClosure R S) (Localization.AtPrime p) :=
      OreLocalization.instAlgebra
    have inst : Algebra.QuasiFiniteAt (integralClosure R S) p :=
      .of_restrictScalars R (integralClosure R S) _
    refine .restrictScalars (this p x ?_ (integralClosure_idem (R := R)))
    suffices ⊤ ≤ (Algebra.adjoin (integralClosure R S) {x}).restrictScalars R from
      top_le_iff.mp fun x _ ↦ (Subalgebra.mem_restrictScalars _).mp (this trivial)
    refine hx.ge.trans ?_
    rw [Algebra.restrictScalars_adjoin]
    exact Algebra.adjoin_mono (by aesop)
  have H₀ : Function.Surjective (aeval (R := R) x) := by
    rwa [← AlgHom.range_eq_top, ← Algebra.adjoin_singleton_eq_range_aeval]
  have ⟨f, (hf : aeval x f = 0), hfp⟩ := SetLike.not_le_iff_exists.mp
    (Polynomial.ker_le_map_C_of_surjective_of_quasiFiniteAt _ H₀ p (p.under R))
  obtain ⟨n, hfn⟩ : ∃ x, algebraMap R S (f.coeff x) ∉ p := by simpa [Ideal.mem_map_C_iff] using hfp
  clear hfp
  induction hm : f.natDegree using Nat.strong_induction_on generalizing f n with | h m IH =>
  obtain (_ | m) := m
  · obtain ⟨r, rfl⟩ := natDegree_eq_zero.mp hm
    cases n <;> aesop
  by_cases Hfp : algebraMap _ _ f.leadingCoeff ∈ p
  · obtain ⟨a, ha⟩ := H.le (isIntegral_leadingCoeff_smul f x hf)
    refine IH _ ?_ (f.eraseLead + C a * X ^ m) (hm := rfl) ?_ n ?_
    · suffices f.eraseLead.natDegree ≤ m by compute_degree!
      exact (eraseLead_natDegree_le ..).trans (by lia)
    · simp [← self_sub_monomial_natDegree_leadingCoeff, hf, hm, pow_succ', ← Algebra.smul_def,
        ← Algebra.smul_mul_assoc, ← ha]
    · suffices algebraMap R S (f.coeff n) + algebraMap R S (if n = m then a else 0) ∉ p by
        simpa [eraseLead_coeff, show n ≠ f.natDegree by rintro rfl; exact hfn (by simpa)]
      rwa [Ideal.add_mem_iff_left]
      split_ifs
      · convert p.mul_mem_right x Hfp
        simpa [Algebra.smul_def] using ha
      · simp
  · refine zariskisMainProperty_iff_exists_saturation_eq_top.mpr ⟨_, Hfp, isIntegral_algebraMap, ?_⟩
    rw [← top_le_iff, ← hx]
    refine Algebra.adjoin_singleton_le ⟨_, ⟨1, rfl⟩, ?_⟩
    simpa [Algebra.smul_def] using isIntegral_leadingCoeff_smul f x hf

lemma ZariskisMainProperty.of_algHom_polynomial
    (p : Ideal S) [p.IsPrime] [Algebra.QuasiFiniteAt R p]
    (f : R[X] →ₐ[R] S) (hf : f.Finite) : ZariskisMainProperty R p := by
  wlog H : integralClosure R S = ⊥
  · letI inst : Algebra (integralClosure R S) (Localization.AtPrime p) :=
      OreLocalization.instAlgebra
    have inst : Algebra.QuasiFiniteAt (integralClosure R S) p :=
      .of_restrictScalars R (integralClosure R S) _
    refine .restrictScalars (this p (aeval (f X)) ?_  (integralClosure_idem (R := R)))
    refine RingHom.Finite.of_comp_finite (f := mapRingHom (algebraMap R _)) ?_
    convert (show f.toRingHom.Finite from hf)
    ext <;> simp [show ∀ x, f (C x) = algebraMap _ _ x from f.commutes]
  have := isStronglyTranscendental_mk_radical_conductor H (f X) (by convert hf; ext; simp)
  have := this.of_surjective_left (S := R ⧸ (conductor R (f X)).radical.under R)
    Ideal.Quotient.mk_surjective
  have : ¬ conductor R (f X) ≤ p := by
    intro hp
    rw [← ‹p.IsPrime›.isRadical.radical_le_iff] at hp
    have inst : (p.map (Ideal.Quotient.mk (conductor R (f X)).radical)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hp)
    have inst : IsReduced (S ⧸ (conductor R (f X)).radical) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
    refine not_quasiFiniteAt_of_stronglyTranscendental this ?_
      (p.map (Ideal.Quotient.mk (conductor R (f X)).radical)) ?_
    · refine RingHom.Finite.of_comp_finite (f := mapRingHom (Ideal.Quotient.mk _)) ?_
      convert (RingHom.Finite.of_surjective (Ideal.Quotient.mk (conductor R (f X)).radical)
        Ideal.Quotient.mk_surjective).comp hf using 1
      have (x : _) : f (C x) = algebraMap _ _ x := f.commutes _
      ext <;> simp [show ∀ x, f (C x) = algebraMap _ _ x from f.commutes]
    · suffices Algebra.QuasiFiniteAt R (p.map (Ideal.Quotient.mk (conductor R (f X)).radical)) from
        .of_restrictScalars R _ _
      refine .of_surjectiveOnStalks p (Ideal.Quotient.mkₐ R (conductor R (f X)).radical)
        (RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective) _
        ((Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective p).trans ?_).symm
      simpa [← RingHom.ker_eq_comap_bot]
  obtain ⟨x, hx, hxp⟩ := SetLike.not_le_iff_exists.mp this
  replace hx (a : _) : x * a ∈ f.range := by simpa [← AlgHom.map_adjoin_singleton f] using hx a
  refine ZariskisMainProperty.trans (S := f.range) _ ?_ ?_
  · have : Algebra.QuasiFiniteAt R (p.under f.range) := by
      let e : Localization.AtPrime (p.under f.range) ≃ₐ[R] Localization.AtPrime p :=
        .ofBijective (IsScalarTower.toAlgHom _ _ _)
          (Localization.localRingHom_bijective_of_not_conductor_le this
            (by simp [← AlgHom.map_adjoin_singleton f]) _)
      exact .of_surjective_algHom e.symm.toAlgHom e.symm.surjective
    refine .of_adjoin_eq_top _ ⟨f X, X, rfl⟩ ?_
    simp [← (Subalgebra.map_injective (f := Subalgebra.val _) Subtype.val_injective).eq_iff,
      ← AlgHom.map_adjoin_singleton f]
  · refine ⟨⟨x, by simpa using hx 1⟩, hxp, top_le_iff.mp fun s _ ↦ ⟨_, ⟨1, rfl⟩, ?_⟩⟩
    simpa [Algebra.mem_bot] using hx s

open scoped Pointwise in
lemma ZariskisMainProperty.of_algHom_mvPolynomial
    (p : Ideal S) [p.IsPrime] [Algebra.QuasiFiniteAt R p] {n : ℕ}
    (f : MvPolynomial (Fin n) R →ₐ[R] S) (hf : f.Finite) : ZariskisMainProperty R p := by
  classical
  induction n generalizing R S with
  | zero =>
    have : Module.Finite R S := by
      rw [← RingHom.finite_algebraMap]
      convert RingHom.Finite.comp hf (RingHom.Finite.of_surjective _ (MvPolynomial.C_surjective _))
      exact f.comp_algebraMap.symm
    exact .of_isIntegral _
  | succ n IH =>
    let f' := f.comp (MvPolynomial.finSuccEquiv _ _).symm.toAlgHom
    let := (f'.toRingHom.comp C).toAlgebra
    have : IsScalarTower R (MvPolynomial (Fin n) R) S := .of_algebraMap_eq fun r ↦
      (f.commutes r).symm.trans congr(f ($(MvPolynomial.finSuccEquiv_comp_C_eq_C n) r)).symm
    let f'' : (MvPolynomial (Fin n) R)[X] →ₐ[MvPolynomial (Fin n) R] S :=
      ⟨f'.toRingHom, fun _ ↦ rfl⟩
    have : Algebra.QuasiFiniteAt (MvPolynomial (Fin n) R) p := by
      exact .of_restrictScalars R _ _
    have := ZariskisMainProperty.of_algHom_polynomial p f''
      (RingHom.Finite.comp hf (MvPolynomial.finSuccEquiv R n).symm.toRingEquiv.finite)
    choose r hrp hr m hm using zariskisMainProperty_iff.mp this
    obtain ⟨⟨s, hs⟩⟩ : Algebra.FiniteType R S := by
      rw [← RingHom.finiteType_algebraMap, ← f.comp_algebraMap]
      exact RingHom.FiniteType.comp hf.finiteType (RingHom.finiteType_algebraMap.mpr inferInstance)
    let R' : Subalgebra R S :=
      Algebra.adjoin R ↑(Finset.univ.image (f ∘ .X ∘ Fin.succ) ∪ r ^ (s.sup m) • s ∪ {r})
    have hrR' : r ∈ R' := Algebra.subset_adjoin (by simp)
    have : Algebra.QuasiFiniteAt R (p.under R') := by
      let e : Localization.AtPrime (p.under R') ≃ₐ[R] Localization.AtPrime p :=
        .ofBijective (IsScalarTower.toAlgHom _ _ _) <| by
          refine Localization.localRingHom_bijective_of_localized_inf_eq_top ?_ _
          rw [← top_le_iff, ← hs, Algebra.adjoin_le_iff]
          intro x hx
          refine ⟨r ^ (s.sup m), pow_mem (by exact ⟨hrp, hrR'⟩) _, Algebra.subset_adjoin ?_⟩
          simp [Set.smul_mem_smul_set hx, ← smul_eq_mul]
      exact .of_surjective_algHom e.symm.toAlgHom e.symm.surjective
    let φ : MvPolynomial (Fin n) R →ₐ[R] R' :=
      MvPolynomial.aeval fun i ↦ ⟨f (.X i.succ), Algebra.subset_adjoin (by simp)⟩
    have := IH (R := R) (S := R') (p.under R') φ <| by
      refine RingHom.finite_iff_isIntegral_and_finiteType.mpr ⟨?_, ?_⟩
      · letI := φ.toAlgebra
        have : IsScalarTower (MvPolynomial (Fin n) R) R' S := .of_algebraMap_eq' <| by
          ext <;> simp [φ, (f'.toRingHom.comp C).algebraMap_toAlgebra, φ.algebraMap_toAlgebra, f',
            MvPolynomial.finSuccEquiv, MvPolynomial.optionEquivLeft]
        refine algebraMap_isIntegral_iff.mpr (integralClosure_eq_top_iff.mp ?_)
        apply Subalgebra.restrictScalars_injective R
        rw [← (Subalgebra.map_injective (f := R'.val) Subtype.val_injective).eq_iff]
        simp only [Subalgebra.restrictScalars_top, Algebra.map_top]
        refine le_antisymm (Set.image_subset_range _ _) ?_
        suffices (∀ (a : Fin n), IsIntegral (MvPolynomial (Fin n) R) (f (MvPolynomial.X a.succ))) ∧
            ∀ a ∈ s, IsIntegral (MvPolynomial (Fin n) R) (r ^ s.sup m * a) by
          simp +contextual only [Subalgebra.range_val, Algebra.adjoin_le_iff, Subalgebra.coe_map,
            Subalgebra.coe_val, Set.subset_def, SetLike.mem_coe, Algebra.mem_adjoin_of_mem,
            Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right, R']
          simpa [R', mem_integralClosure_iff,
            ← isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective R' S),
            forall_and, hr, or_imp, Finset.mem_smul_finset]
        refine ⟨fun i ↦ ?_, fun a has ↦ ?_⟩
        · convert isIntegral_algebraMap (x := MvPolynomial.X i)
          simp [RingHom.algebraMap_toAlgebra, f', MvPolynomial.finSuccEquiv,
            MvPolynomial.optionEquivLeft]
        · rw [← Nat.sub_add_cancel (s.le_sup has), pow_add, mul_assoc]
          exact (hr.pow _).mul (hm _)
      · refine .of_comp_finiteType (f := algebraMap R _) ?_
        rw [AlgHom.toRingHom_eq_coe, φ.comp_algebraMap, RingHom.finiteType_algebraMap]
        exact ⟨(Subalgebra.fg_top _).mpr ⟨_, rfl⟩⟩
    refine this.trans _ ⟨⟨r, hrR'⟩, hrp, ?_⟩
    suffices ⊤ ≤ R'.localized (.powers r) (by simpa [Submonoid.powers_le]) by
      simpa [SetLike.le_def, Subalgebra.smul_def, Submonoid.mem_powers_iff,
        SetLike.ext_iff, Algebra.mem_bot] using this
    rw [← hs, Algebra.adjoin_le_iff]
    intro x hx
    refine ⟨_, ⟨s.sup m, rfl⟩, Algebra.subset_adjoin ?_⟩
    simp [Set.smul_mem_smul_set hx, ← smul_eq_mul]

end FixedUniverse

lemma ZariskisMainProperty.of_finiteType.{u, v} {R : Type u} {S : Type v} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (p : Ideal S) [p.IsPrime] [Algebra.QuasiFiniteAt R p] : ZariskisMainProperty R p := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  have : Small.{u} S := small_of_surjective hf
  have := ZariskisMainProperty.of_algHom_mvPolynomial (p.comap (Shrink.algEquiv R S).toRingHom)
    ((Shrink.algEquiv R S).symm.toAlgHom.comp f)
    (.of_surjective _ <| (Shrink.algEquiv R S).symm.surjective.comp hf)
  rw [zariskisMainProperty_iff'] at this ⊢
  obtain ⟨r, hr, H⟩ := this
  refine ⟨Shrink.algEquiv R S r, hr, fun x ↦ ?_⟩
  obtain ⟨m, hm⟩ := H ((Shrink.algEquiv R S).symm x)
  exact ⟨m, by simpa [-Shrink.algEquiv_apply, -Shrink.algEquiv_symm_apply]
    using hm.map (Shrink.algEquiv R S).toAlgHom⟩

lemma ZariskisMainProperty.exists_foobar {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (p : Ideal S) [p.IsPrime] (H : ZariskisMainProperty R p) :
    ∃ S' : Subalgebra R S, S'.toSubmodule.FG ∧ ∃ r : S',
      r.1 ∉ p ∧ Function.Bijective (Localization.awayMap S'.val.toRingHom r) := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := S)
  choose r hrp hr m hm using zariskisMainProperty_iff.mp H
  let t := insert r { r ^ m x * x | x ∈ s }
  let r' : Algebra.adjoin R t := ⟨r, Algebra.subset_adjoin (by simp [t])⟩
  refine ⟨Algebra.adjoin R t, fg_adjoin_of_finite ?_ ?_, ?_⟩
  · simp only [t, Set.finite_insert]
    exact s.finite_toSet.image (fun x ↦ r ^ m x * x)
  · rintro a (rfl | ⟨x, hx, rfl⟩); exacts [hr, hm _]
  refine ⟨r', hrp,
    IsLocalization.map_injective_of_injective _ _ _ Subtype.val_injective, ?_⟩
  have : (IsScalarTower.toAlgHom R S _).range ≤
      (Localization.awayMapₐ (Algebra.adjoin R t).val r').range := by
    rw [← Algebra.map_top, ← hs, Subalgebra.map_le, Algebra.adjoin_le_iff]
    intro x hx
    suffices ∃ a ∈ Algebra.adjoin R t, ∃ n, r ^ n ∈ Algebra.adjoin R t ∧
        ∃ k, r ^ k * a = r ^ k * (x * r ^ n) by
      simpa [(IsLocalization.mk'_surjective (.powers r')).exists,
        (IsLocalization.mk'_surjective (.powers r)).forall, Localization.awayMapₐ,
        IsLocalization.Away.map, IsLocalization.map_mk', Submonoid.mem_powers_iff,
        Subtype.ext_iff, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul, ← map_pow,
        IsLocalization.eq_iff_exists (.powers r), Subalgebra.val]
    exact ⟨_, Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨x, hx, mul_comm _ _⟩),
      m x, pow_mem r'.2 _, 1, rfl⟩
  intro x
  obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq
    (.powers ((Algebra.adjoin R t).val.toRingHom r')) x
  obtain ⟨y, hy : Localization.awayMap _ _ _ = _⟩ := this ⟨x, rfl⟩
  refine ⟨y * Localization.Away.invSelf _ ^ n, ?_⟩
  simp only [map_mul, map_pow, hy]
  simp [Localization.Away.invSelf, Localization.awayMap, ← Algebra.smul_def,
    IsLocalization.Away.map, IsLocalization.map_mk', Localization.mk_eq_mk',
    ← IsLocalization.mk'_pow]

lemma ZariskisMainProperty.exists_fg_and_exists_notMem_and_awayMap_bijective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (p : Ideal S) [p.IsPrime] (H : ZariskisMainProperty R p) :
    ∃ S' : Subalgebra R S, S'.toSubmodule.FG ∧ ∃ r : S',
      r.1 ∉ p ∧ Function.Bijective (Localization.awayMap S'.val.toRingHom r) := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := S)
  choose r hrp hr m hm using zariskisMainProperty_iff.mp H
  let t := insert r { r ^ m x * x | x ∈ s }
  let r' : Algebra.adjoin R t := ⟨r, Algebra.subset_adjoin (by simp [t])⟩
  refine ⟨Algebra.adjoin R t, fg_adjoin_of_finite ?_ ?_, ?_⟩
  · simp only [t, Set.finite_insert]
    exact s.finite_toSet.image (fun x ↦ r ^ m x * x)
  · rintro a (rfl | ⟨x, hx, rfl⟩); exacts [hr, hm _]
  refine ⟨r', hrp,
    IsLocalization.map_injective_of_injective _ _ _ Subtype.val_injective, ?_⟩
  have : (IsScalarTower.toAlgHom R S _).range ≤
      (Localization.awayMapₐ (Algebra.adjoin R t).val r').range := by
    rw [← Algebra.map_top, ← hs, Subalgebra.map_le, Algebra.adjoin_le_iff]
    intro x hx
    suffices ∃ a ∈ Algebra.adjoin R t, ∃ n, r ^ n ∈ Algebra.adjoin R t ∧
        ∃ k, r ^ k * a = r ^ k * (x * r ^ n) by
      simpa [(IsLocalization.mk'_surjective (.powers r')).exists,
        (IsLocalization.mk'_surjective (.powers r)).forall, Localization.awayMapₐ,
        IsLocalization.Away.map, IsLocalization.map_mk', Submonoid.mem_powers_iff,
        Subtype.ext_iff, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul, ← map_pow,
        IsLocalization.eq_iff_exists (.powers r), Subalgebra.val]
    exact ⟨_, Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨x, hx, mul_comm _ _⟩),
      m x, pow_mem r'.2 _, 1, rfl⟩
  intro x
  obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq
    (.powers ((Algebra.adjoin R t).val.toRingHom r')) x
  obtain ⟨y, hy : Localization.awayMap _ _ _ = _⟩ := this ⟨x, rfl⟩
  refine ⟨y * Localization.Away.invSelf _ ^ n, ?_⟩
  simp only [map_mul, map_pow, hy]
  simp [Localization.Away.invSelf, Localization.awayMap, ← Algebra.smul_def,
    IsLocalization.Away.map, IsLocalization.map_mk', Localization.mk_eq_mk',
    ← IsLocalization.mk'_pow]

end Algebra
