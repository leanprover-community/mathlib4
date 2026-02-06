/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Algebraic.StronglyTranscendental
public import Mathlib.RingTheory.Conductor
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.RingTheory.QuasiFinite.Basic

/-!
# Algebraic Zariski's Main Theorem

The statement of Zariski's main theorem is the following:
Given a finite type `R`-algebra `S`, and `p` a prime of `S` such that `S` is quasi-finite at `R`,
then there exists a `f ∉ p` such that `S[1/f]` is isomorphic to `R'[1/f]` where `R'` is the integral
closure of `R` in `S`.

We follow https://stacks.math.columbia.edu/tag/00PI and proceed in the following steps

1. `Algebra.ZariskisMainProperty.of_adjoin_eq_top`:
  The case where `S = R[X]/I`.
  The key is `Polynomial.not_ker_le_map_C_of_surjective_of_quasiFiniteAt`
  which shows that there exists some `g ∈ I` such that some coefficient `gᵢ ∉ p`.
  Then one basically takes `f = gᵢ` and `g` becomes monic in `R[1/gᵢ][X]` up to some minor technical
  issues, and then `S[1/gᵢ]` is basically integral over `R[1/gᵢ]`.
2. `Algebra.ZariskisMainProperty.of_algHom_polynomial`:
  The case where `S` is finite over `R⟨x⟩` for some `x : S`.
  The following key results are first esablished:
  - `isStronglyTranscendental_mk_radical_conductor`:
    Let `𝔣` be the conductor of `x` (i.e. the largest `S`-ideal in `R⟨x⟩`).
    `x` as an element of `S/√𝔣` is strongly transcendental over `R`.
  - `Algebra.not_quasiFiniteAt_of_stronglyTranscendental`:
    If `S` is reduced, then `x : S` is not strongly transcendental over `R`.
    One first reduces to when `R ⊆ S` are domains, and then to when `R` is integrally closed.
    A going down theorem is now available, which could be applied to
    `Polynomial.map_under_lt_comap_of_quasiFiniteAt`:`(p ∩ R)[X] < p ∩ R<x>` to get a contradiction.
  The second result applied to `S/√𝔣` together with the first result implies that
  `p` does not contain `𝔣`.
  The claim then follows from `Localization.localRingHom_bijective_of_not_conductor_le`.
3. TODO (@erdOne): Induct on the number of `{ xᵢ }` such that `S` is finite over `R⟨xᵢ⟩` to get the
  general statement.

-/

@[expose] public section

variable {R S T : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

open scoped TensorProduct nonZeroDivisors

open Polynomial

namespace Algebra

variable (R) in
/-- We say that an `R` algebra `S` satisfies the Zariski's main property at a prime `p` of `S`
if there exists `r ∉ p` in the integral closure `S'` of `R` in `S`, such that `S'[1/r] = S[1/r]`. -/
def ZariskisMainProperty (p : Ideal S) : Prop :=
  ∃ r : integralClosure R S, r.1 ∉ p ∧ Function.Bijective
    (Localization.awayMap (integralClosure R S).val.toRingHom r)

lemma zariskisMainProperty_iff {p : Ideal S} :
    ZariskisMainProperty R p ↔ ∃ r ∉ p, IsIntegral R r ∧ ∀ x, ∃ m, IsIntegral R (r ^ m * x) := by
  simp only [ZariskisMainProperty, Subtype.exists, ← exists_prop, @exists_comm (_ ∉ p)]
  refine exists₃_congr fun r hr hrp ↦ ?_
  rw [Function.Bijective, and_iff_right
    (by exact IsLocalization.map_injective_of_injective _ _ _ Subtype.val_injective),
    Localization.awayMap_surjective_iff]
  simp [mem_integralClosure_iff]

lemma zariskisMainProperty_iff' {p : Ideal S} :
    ZariskisMainProperty R p ↔ ∃ r ∉ p, ∀ x, ∃ m, IsIntegral R (r ^ m * x) := by
  refine zariskisMainProperty_iff.trans (exists_congr fun r ↦ and_congr_right fun hrp ↦
    and_iff_right_of_imp fun H ↦ ?_)
  obtain ⟨n, hn⟩ := H r
  rw [← pow_succ] at hn
  exact (IsIntegral.pow_iff (by simp)).mp hn

lemma zariskisMainProperty_iff_exists_saturation_eq_top {p : Ideal S} :
    ZariskisMainProperty R p ↔ ∃ r ∉ p, ∃ h : IsIntegral R r,
      (integralClosure R S).saturation (.powers r) (by simpa [Submonoid.powers_le]) = ⊤ := by
  simp [zariskisMainProperty_iff, ← top_le_iff, SetLike.le_def,
    Submonoid.mem_powers_iff, mem_integralClosure_iff]

lemma ZariskisMainProperty.restrictScalars [Algebra S T] [IsScalarTower R S T]
    [Algebra.IsIntegral R S] {p : Ideal T} (H : ZariskisMainProperty S p) :
    ZariskisMainProperty R p := by
  rw [zariskisMainProperty_iff'] at H ⊢
  obtain ⟨r, hrp, H⟩ := H
  exact ⟨r, hrp, fun x ↦ ⟨_, isIntegral_trans _ (H x).choose_spec⟩⟩

lemma ZariskisMainProperty.trans [Algebra S T] [IsScalarTower R S T] (p : Ideal T) [p.IsPrime]
    (h₁ : ZariskisMainProperty R (p.under S))
    (h₂ : ∃ r ∉ p.under S, (⊥ : Subalgebra S T).saturation (.powers (algebraMap _ _ r))
      (by simp [Submonoid.powers_le]) = ⊤) :
    ZariskisMainProperty R p := by
  rw [zariskisMainProperty_iff] at h₁
  rw [zariskisMainProperty_iff']
  obtain ⟨s, hsp, hs, Hs⟩ := h₁
  obtain ⟨t, htp, Ht⟩ := h₂
  obtain ⟨m, hm⟩ := Hs t
  refine ⟨algebraMap _ _ (s ^ (m + 1) * t), ?_, fun x ↦ ?_⟩
  · simpa using ‹p.IsPrime›.mul_notMem
      (mt ((inferInstanceAs (p.under S).IsPrime).mem_of_pow_mem (m + 1)) hsp) htp
  obtain ⟨_, ⟨n, rfl⟩, a, ha⟩ := Ht.ge (Set.mem_univ x)
  obtain ⟨k, hk⟩ := Hs a
  refine ⟨k + n, ?_⟩
  convert_to IsIntegral R (algebraMap S T ((s ^ ((m + 1) * n) * (s ^ m * t) ^ k * (s ^ k * a))))
  · simp only [AlgHom.toRingHom_eq_coe, Algebra.toRingHom_ofId] at ha
    simp only [map_pow, map_mul, ha, pow_add, mul_pow]
    ring
  · exact .algebraMap (.mul ((hs.pow _).mul (hm.pow _)) hk)

lemma ZariskisMainProperty.of_isIntegral (p : Ideal S) [p.IsPrime] [Algebra.IsIntegral R S] :
    ZariskisMainProperty R p :=
  zariskisMainProperty_iff'.mpr ⟨1, p.primeCompl.one_mem,
    fun _ ↦ ⟨0, Algebra.IsIntegral.isIntegral _⟩⟩

end Algebra

section IsStronglyTranscendental

variable (φ : R[X] →ₐ[R] S) (t : S) (p r : R[X])

/-- Given a map `φ : R[X] →ₐ[R] S`. Suppose `t = φ r / φ p` is integral over `R[X]` where
`p` is monic with `deg p > deg r`, then `t` is also integral over `R`. -/
lemma isIntegral_of_isIntegralElem_of_monic_of_natDegree_lt
    (ht : φ.IsIntegralElem t) (hpm : p.Monic)
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
    (ht : φ.IsIntegralElem t) (hpm : p.Monic) (hp : φ p * t ∈ φ.range) :
    ∃ q, IsIntegral R (t - φ q) := by
  obtain ⟨r, hr : φ r = _⟩ := hp
  obtain rfl | hp1 := eq_or_ne p 1
  · exact ⟨r, by simp_all [isIntegral_zero]⟩
  exact ⟨_, isIntegral_of_isIntegralElem_of_monic_of_natDegree_lt φ (t - φ (r /ₘ p)) p (r %ₘ p)
    (ht.sub _ φ.isIntegralElem_map) hpm (natDegree_modByMonic_lt _ hpm hp1)
    (by simp [mul_sub, ← hr, sub_eq_iff_eq_add, ← map_mul, ← map_add, r.modByMonic_add_div hpm])⟩

open IsScalarTower in
attribute [local simp] IsLocalization.map_eq aeval_algebraMap_apply aeval_algHom_apply in
@[stacks 00PV]
lemma exists_isIntegral_leadingCoeff_pow_smul_sub_of_isIntegralElem_of_mul_mem_range
    (ht : φ.IsIntegralElem t) (hp : φ p * t ∈ φ.range) :
    ∃ q n, IsIntegral R (p.leadingCoeff ^ n • t - φ q) := by
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
    (aeval (algebraMap S S' (φ X))) (algebraMap S S' t) (C ha.unit⁻¹.1 * p.map (algebraMap _ _)) (by
      obtain ⟨q, hqm, hq⟩ := ht
      refine ⟨q.map (mapRingHom (algebraMap _ _)), hqm.map _, ?_⟩
      rw [eval₂_map, H, ← hom_eval₂, ← AlgHom.toRingHom_eq_coe, hq, map_zero]) (by
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
    (hφ : φ.toRingHom.Finite) (hp : φ p * t ∈ conductor R (φ X)) :
    ∃ n, p.leadingCoeff ^ n • t ∈ conductor R (φ X) := by
  algebraize [φ.toRingHom]
  have : IsScalarTower R R[X] S := .of_algebraMap_eq' φ.comp_algebraMap.symm
  have (x : _) : ∃ n, p.leadingCoeff ^ n • (t * x) ∈ φ.range := by
    have : φ p * t * x ∈ φ.range := by simpa [← AlgHom.map_adjoin_singleton] using hp x
    obtain ⟨q, n, hn⟩ :=
      exists_isIntegral_leadingCoeff_pow_smul_sub_of_isIntegralElem_of_mul_mem_range φ _ p
        (hφ.to_isIntegral (t * x)) (by convert this using 1; ring)
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
    (hφ : φ.toRingHom.Finite) (hp : φ p * t ∈ (conductor R (φ X)).radical) (i : ℕ) :
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
  obtain ⟨k, hk⟩ := exists_leadingCoeff_pow_smul_mem_conductor φ  (t ^ n) (p ^ n) hRS hφ
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
    Algebra.smul_def] using exists_leadingCoeff_pow_smul_mem_radical_conductor _ u p hRS hx
      (by simpa using e) i

end IsStronglyTranscendental

namespace Algebra

attribute [local instance] Polynomial.isLocalization Polynomial.algebra

section not_quasiFiniteAt

/-- Use `not_isStronglyTranscendental_of_quasiFiniteAt` below instead. -/
private lemma not_isStronglyTranscendental_of_quasiFiniteAt_of_isIntegrallyClosed [FaithfulSMul R S]
    [IsIntegrallyClosed R] [IsDomain S]
    {x : S} (hx' : (aeval (R := R) x).Finite)
    (P : Ideal S) [P.IsPrime] [Algebra.QuasiFiniteAt R P] : ¬ IsStronglyTranscendental R x := by
  intro hx
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
  have : (P.under R).map C < P.under R[X] := Polynomial.map_under_lt_comap_of_quasiFiniteAt _ _
  obtain ⟨Q, hQ, _, ⟨e⟩⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (S := S) P this
  refine hQ.ne (Algebra.QuasiFiniteAt.eq_of_le_of_under_eq (R := R) hQ.le ?_)
  rw [← Ideal.under_under (B := R[X]), ← e]
  ext
  simp [Ideal.mem_map_C_iff, coeff_C, apply_ite]

/-- This asks for an explict `K = Frac(R)`, `L = Frac(S)`,
`R'` the integral closure of `R` in `K`, and `S' ⊆ L` the subalgebra spanned by `R'` and `S`,
to aid typeclass synthesis.

Use `not_isStronglyTranscendental_of_quasiFiniteAt` below instead. -/
@[stacks 00Q1]
private lemma not_isStronglyTranscendental_of_quasiFiniteAt_of_isDomain_aux
    (K L : Type*) [Field K] [Field L] [Algebra R K] [Algebra R L] [Algebra S L] [Algebra K L]
    [IsScalarTower R K L] [IsScalarTower R S L] [IsFractionRing R K] [IsFractionRing S L]
    {R' S' : Type*} [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra R' S'] [Algebra R S']
    [Algebra S' L] [Algebra R' L] [IsScalarTower R' S' L] [Algebra R' K] [IsScalarTower R' K L]
    [IsScalarTower R R' S'] [FaithfulSMul S' L] [IsIntegralClosure R' R K]
    [IsScalarTower R R' K]
    (f : S →ₐ[R] S') (hf₁ : Function.Surjective
      (Algebra.TensorProduct.lift (Algebra.ofId R' S') f fun _ _ ↦ .all _ _))
    (hf₂ : (algebraMap S' L).comp f.toRingHom = algebraMap _ _)
    {x : S} (hx' : (aeval (R := R) x).Finite)
    (P : Ideal S) [P.IsPrime] [Algebra.QuasiFiniteAt R P] : ¬ IsStronglyTranscendental R x := by
  intro hx
  have := (FaithfulSMul.algebraMap_injective S' L).isDomain
  have := (FaithfulSMul.algebraMap_injective R K).isDomain
  have : Algebra.IsIntegral R R' := IsIntegralClosure.isIntegral_algebra _ K
  have : FaithfulSMul R' K := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (IsIntegralClosure.algebraMap_injective R' R K)
  have : FaithfulSMul R R' := .tower_bot _ _ K
  have : FaithfulSMul R' L := .trans _ K _
  have : FaithfulSMul R' S' := .tower_bot _ _ L
  have : IsIntegrallyClosedIn R' K := .of_isIntegralClosure R
  have : IsIntegrallyClosed R' := .of_isIntegrallyClosed_of_isIntegrallyClosedIn _ K
  let g := Algebra.TensorProduct.lift (Algebra.ofId R' S') f fun _ _ ↦ .all _ _
  have hf₃ : Function.Injective f :=
    .of_comp (f := algebraMap S' L) (hf₂ ▸ FaithfulSMul.algebraMap_injective S L:)
  have hf₄ : f.IsIntegral := by
    have : f = (g.restrictScalars R).comp ((Algebra.TensorProduct.comm _ _ _).toAlgHom.comp
        (IsScalarTower.toAlgHom _ _ _)) := by ext; simp [g]
    simp only [this, AlgEquiv.toAlgHom_eq_coe, AlgHom.toRingHom_eq_coe,
      AlgHom.comp_toRingHom, ← RingHom.comp_assoc]
    refine .trans _ _ (algebraMap_isIntegral_iff.mpr inferInstance) ?_
    exact RingHom.isIntegral_of_surjective _
      (hf₁.comp (Algebra.TensorProduct.comm _ _ _).surjective)
  have H₁ : IsStronglyTranscendental R' (f x) := by
    refine .of_map (f := IsScalarTower.toAlgHom R' S' L) (FaithfulSMul.algebraMap_injective S' L) ?_
    dsimp
    rw [show algebraMap S' L (f x) = algebraMap _ _ x from congr($hf₂ x)]
    exact ((hx.of_isLocalization S⁰).of_isLocalization_left R⁰).restrictScalars (S := K)
  have H₂ : (aeval (R := R') (f x)).toRingHom.Finite := by
    convert ((RingHom.Finite.of_surjective g.toRingHom hf₁).comp
      (RingHom.Finite.tensorProductMap (f := AlgHom.id R R') (RingEquiv.refl _).finite hx')).comp
      (polyEquivTensor R R').toRingEquiv.finite using 1
    ext <;> simp [g]
  obtain ⟨⟨Q, _⟩, hQ⟩ := hf₄.comap_surjective hf₃ ⟨P, ‹_›⟩
  suffices QuasiFiniteAt R' Q from
    not_isStronglyTranscendental_of_quasiFiniteAt_of_isIntegrallyClosed H₂ Q H₁
  have : Algebra.QuasiFiniteAt R' (Q.comap g.toRingHom) := .baseChange P _ <| by
    rw [Ideal.comap_comap]
    convert congr(($hQ.symm).1)
    ext; simp [g]
  exact .of_surjectiveOnStalks _ g (RingHom.surjectiveOnStalks_of_surjective hf₁) _ rfl

@[stacks 00Q2]
nonrec lemma not_isStronglyTranscendental_of_quasiFiniteAt [IsReduced S]
    {x : S} (hx' : (aeval (R := R) x).toRingHom.Finite)
    (P : Ideal S) [P.IsPrime] [Algebra.QuasiFiniteAt R P] : ¬ IsStronglyTranscendental R x := by
  wlog hS : IsDomain S ∧ FaithfulSMul R S
  · intro hx
    obtain ⟨p, hp, hpP⟩ := Ideal.exists_minimalPrimes_le (J := P) bot_le
    have inst := hp.1.1
    have inst : (P.map (Ideal.Quotient.mk p)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa)
    have inst : QuasiFiniteAt (R ⧸ Ideal.under R p) (Ideal.map (Ideal.Quotient.mk p) P) := by
      suffices Algebra.QuasiFiniteAt R (P.map (Ideal.Quotient.mk p)) from .of_restrictScalars R _ _
      refine .of_surjectiveOnStalks P (Ideal.Quotient.mkₐ _ _)
        (RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective) _ ?_
      refine .trans ?_ (Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective _).symm
      simpa [← RingHom.ker_eq_comap_bot]
    refine this (R := R ⧸ p.under R) ?_ (P.map (Ideal.Quotient.mk p)) ⟨inferInstance, inferInstance⟩
      ((isStronglyTranscendental_mk_of_mem_minimalPrimes hx p hp).of_surjective_left
        Ideal.Quotient.mk_surjective)
    refine RingHom.Finite.of_comp_finite (f := mapRingHom (Ideal.Quotient.mk _)) ?_
    convert (RingHom.Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := p))).comp hx'
    ext <;> simp
  cases hS
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain
  let K := FractionRing R
  let L := FractionRing S
  let : Algebra K L := FractionRing.liftAlgebra _ _
  let R' := integralClosure R K
  let S' : Subalgebra R' L := Algebra.adjoin R' (algebraMap S L).range
  let f : S →ₐ[R] S' := (IsScalarTower.toAlgHom R S L).codRestrict (S'.restrictScalars R) fun x ↦ by
    simpa using show algebraMap S L x ∈ S' from Algebra.subset_adjoin ⟨x, rfl⟩
  let g := Algebra.TensorProduct.lift (Algebra.ofId R' S') f fun _ _ ↦ .all _ _
  have hf : Function.Surjective g := by
    rw [← AlgHom.range_eq_top,
      ← (Subalgebra.map_injective (f := S'.val) Subtype.val_injective).eq_iff, Algebra.map_top]
    refine le_antisymm (Set.image_subset_range S'.val g.range) ?_
    simp only [RingHom.coe_range, Subalgebra.range_val, Algebra.adjoin_le_iff, Subalgebra.coe_map,
      Subalgebra.coe_val, AlgHom.coe_range, Set.range_subset_iff, Set.mem_image, Set.mem_range,
      exists_exists_eq_and, S']
    exact fun y ↦ ⟨1 ⊗ₜ y, by simp [g, S']; rfl⟩
  exact not_isStronglyTranscendental_of_quasiFiniteAt_of_isDomain_aux K L f hf rfl hx' P

end not_quasiFiniteAt

section FixedUniverse

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
    (Polynomial.not_ker_le_map_C_of_surjective_of_quasiFiniteAt _ H₀ p)
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
  have : ¬ conductor R (f X) ≤ p := by
    intro hp
    rw [← ‹p.IsPrime›.isRadical.radical_le_iff] at hp
    set J := (conductor R (f X)).radical
    have inst : (p.map (Ideal.Quotient.mk J)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hp)
    have inst : IsReduced (S ⧸ J) :=
        (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
    have inst : QuasiFiniteAt R (p.map (Ideal.Quotient.mk J)) := by
      refine .of_surjectiveOnStalks p (Ideal.Quotient.mkₐ R _)
        (RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective) _
        ((Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective p).trans ?_).symm
      simpa [← RingHom.ker_eq_comap_bot]
    refine not_isStronglyTranscendental_of_quasiFiniteAt ?_ (p.map (Ideal.Quotient.mk J))
      (isStronglyTranscendental_mk_radical_conductor H (f X) (by convert hf; ext; simp))
    convert (RingHom.Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := J))).comp hf using 1
    ext <;> simp [show ∀ x, f (C x) = algebraMap _ _ x from f.commutes, J]
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
      ← AlgHom.map_adjoin_singleton f, Subalgebra.range_val]
  · refine ⟨⟨x, by simpa using hx 1⟩, hxp, top_le_iff.mp fun s _ ↦ ⟨_, ⟨1, rfl⟩, ?_⟩⟩
    simpa [Algebra.mem_bot] using hx s

end FixedUniverse

end Algebra
