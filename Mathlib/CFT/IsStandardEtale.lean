module

public import Mathlib.CFT.Stuff2
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.ZariskiMain

@[expose] public section

open Polynomial TensorProduct
open IsLocalRing

universe u

variable {R : Type*} [CommRing R] [IsLocalRing R]

local notation "𝓀[" R "]" => ResidueField R
local notation "𝓂[" R "]" => maximalIdeal R

open Polynomial TensorProduct KaehlerDifferential

open nonZeroDivisors

attribute [ext high] Ideal.Quotient.algHom_ext

lemma Polynomial.fiberEquivQuotient_tmul {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (f : R[X] →ₐ[R] S) (hf : Function.Surjective ⇑f) (p : Ideal R) [p.IsPrime] (a b) :
    Polynomial.fiberEquivQuotient f hf p (a ⊗ₜ f b) =
      Ideal.Quotient.mk _ (C a * b.map (algebraMap _ _)) := by
  simp [Polynomial.fiberEquivQuotient]; rfl

theorem Algebra.FormallyEtale.isStandardEtale_of_finite_aux
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    (P : Ideal R) [P.IsPrime] (x : S) (hx : adjoin R {x} = ⊤) :
    (RingHom.ker (aeval (R := R) x).toRingHom).map (mapRingHom (algebraMap R P.ResidueField)) =
      RingHom.ker (aeval (1 ⊗ₜ x : P.ResidueField ⊗[R] S)).toRingHom := by
  have hx' : Function.Surjective (aeval (R := R) x) :=
    (AlgHom.range_eq_top _).mp ((adjoin_singleton_eq_range_aeval R x).symm.trans hx)
  set I := RingHom.ker (RingHomClass.toRingHom <| aeval (R := R) x)
  let e : P.ResidueField ⊗[R] S ≃ₐ[P.ResidueField]
      P.ResidueField[X] ⧸ (I.map (mapRingHom (algebraMap _ P.ResidueField))) :=
    Polynomial.fiberEquivQuotient (aeval (R := R) x) hx' _
  rw [← RingHom.ker_comp_of_injective _ (f := e.toRingHom) e.injective]
  have H : (Ideal.quotientKerAlgEquivOfSurjective hx').symm x = (X : R[X]) :=
    (Ideal.quotientKerAlgEquivOfSurjective hx').symm_apply_eq.mpr (aeval_X _).symm
  convert Ideal.mk_ker.symm
  ext a
  · dsimp [-TensorProduct.algebraMap_apply]
    rw [aeval_C, AlgEquiv.commutes]
    rfl
  · simpa [e] using Polynomial.fiberEquivQuotient_tmul _ hx' P 1 X

set_option maxHeartbeats 0 in
set_option synthInstance.maxHeartbeats 0 in
theorem Algebra.FormallyEtale.isStandardEtale_of_finite_aux2
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] (P : Ideal R) [P.IsPrime] (Q : Ideal S) [Q.IsPrime]
    [Q.LiesOver P] [Algebra.IsUnramifiedAt R Q] (x : S) (p : R[X])
    (hp₁ : Ideal.span {p.map (algebraMap R P.ResidueField)} =
      RingHom.ker (aeval ((1 : P.ResidueField) ⊗ₜ[R] x)).toRingHom)
    (hp₂ : Function.Surjective (aeval (R := R) x)) :
    ¬ minpoly P.ResidueField (algebraMap S Q.ResidueField x) ^ 2 ∣
      p.map (algebraMap R P.ResidueField) := by
  let Q' : Ideal (P.ResidueField ⊗[R] S) := (PrimeSpectrum.primesOverOrderIsoFiber
    R S P ⟨Q, ‹_›, ‹_›⟩).asIdeal
  have : Q'.LiesOver P := .trans _ (⊥ : Ideal P.ResidueField) _
  have hQ' : Q = Q'.comap Algebra.TensorProduct.includeRight.toRingHom :=
    congr($((PrimeSpectrum.primesOverOrderIsoFiber R S P).symm_apply_apply ⟨Q, ‹_›, ‹_›⟩).1).symm
  have : Q'.IsPrime := inferInstance
  clear_value Q'
  have : IsUnramifiedAt P.ResidueField Q' := .residueField P Q _ hQ'
  have : Function.Surjective (aeval (R := P.ResidueField) ((1 : P.ResidueField) ⊗ₜ[R] x)) := by
    convert (Algebra.TensorProduct.map_surjective
      (AlgHom.id P.ResidueField P.ResidueField) (aeval x) Function.surjective_id hp₂).comp
      (polyEquivTensor' R P.ResidueField).surjective
    rw [← AlgEquiv.coe_algHom, ← AlgHom.coe_comp]
    congr 1; ext; simp
  convert Algebra.IsUnramifiedAt.not_minpoly_sq_dvd
    (K := P.ResidueField) (A := P.ResidueField ⊗[R] S) Q' (1 ⊗ₜ x) _ hp₁ this
  let f₀ : Q.ResidueField →+* Q'.ResidueField :=
    Ideal.ResidueField.map _ _ Algebra.TensorProduct.includeRight.toRingHom hQ'
  let f : Q.ResidueField →ₐ[P.ResidueField] Q'.ResidueField :=
  { toRingHom := f₀,
    commutes' r := by
      change (f₀.comp (algebraMap _ Q.ResidueField)) r = _
      congr 1
      ext
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, Function.comp_apply,
        ← IsScalarTower.algebraMap_apply R P.ResidueField Q.ResidueField,
        IsScalarTower.algebraMap_apply R S Q.ResidueField, Ideal.ResidueField.map_algebraMap,
        RingHom.coe_coe, AlgHom.commutes, f₀]
      simp only [← IsScalarTower.algebraMap_apply] }
  rw [← minpoly.algHom_eq f f.injective]
  congr 1
  · apply Algebra.algebra_ext; intros r; congr 1; ext x; simp [← IsScalarTower.algebraMap_apply]
  · simp [f, f₀]

theorem Ideal.exists_mem_span_singleton_map_residueField_eq
    {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] (I : Ideal R[X]) :
    ∃ p ∈ I, Ideal.span {p.map (algebraMap R P.ResidueField)} =
      I.map (mapRingHom (algebraMap R P.ResidueField)) := by
  obtain ⟨p, hp : _ = Ideal.span _⟩ := inferInstanceAs
    (I.map (mapRingHom (algebraMap R P.ResidueField))).IsPrincipal
  letI := (mapRingHom (algebraMap (R ⧸ P) P.ResidueField)).toAlgebra
  have := Polynomial.isLocalization (R ⧸ P)⁰ P.ResidueField
  have : p ∈ (I.map (mapRingHom (algebraMap R (R ⧸ P)))).map (algebraMap _ _) := by
    rw [Ideal.map_map, RingHom.algebraMap_toAlgebra, mapRingHom_comp,
      ← IsScalarTower.algebraMap_eq, hp]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨⟨⟨r, hr⟩, s⟩, e⟩ := (IsLocalization.mem_map_algebraMap_iff ((R ⧸ P)⁰.map C) _).mp this
  obtain ⟨r, hr', rfl⟩ := (Ideal.mem_map_iff_of_surjective _
    (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective)).mp hr
  simp only [algebraMap_def, coe_mapRingHom,
    Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at e
  refine ⟨r, hr', le_antisymm ?_ ?_⟩
  · simpa [-le_of_subsingleton, Ideal.span_le] using Ideal.mem_map_of_mem _ hr'
  · simp only [hp, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    rw [(IsLocalization.map_units P.ResidueField[X] s).unit.eq_mul_inv_iff_mul_eq.mpr e]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

def HasStandardEtaleSurjectionAt (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (f : S) : Prop :=
  ∃ (P : StandardEtalePair R) (φ : P.Ring →ₐ[R] Localization.Away f), Function.Surjective φ

lemma HasStandardEtaleSurjectionAt.mk {R A S Sf : Type*} [CommRing R] [CommRing A] [CommRing S]
    [CommRing Sf] [Algebra R S] [Algebra R A] [Algebra.IsStandardEtale R A] [Algebra S Sf]
    [Algebra R Sf] [IsScalarTower R S Sf] {f : S} [IsLocalization.Away f Sf]
    (φ : A →ₐ[R] Sf) (H : Function.Surjective φ) : HasStandardEtaleSurjectionAt R f := by
  let P : StandardEtalePresentation R A := Nonempty.some inferInstance
  refine ⟨P.P, (((IsLocalization.algEquiv (.powers f) (Localization.Away f) Sf).restrictScalars R)
    |>.symm.toAlgHom).comp (φ.comp P.equivRing.symm.toAlgHom), by simpa⟩

lemma HasStandardEtaleSurjectionAt.of_dvd
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {f g : S} (H : HasStandardEtaleSurjectionAt R f) (h : f ∣ g) :
    HasStandardEtaleSurjectionAt R g := by
  obtain ⟨P, φ, hsurj⟩ := H
  obtain ⟨g, rfl⟩ := h
  obtain ⟨a, ha⟩ := hsurj (algebraMap _ _ g)
  have : IsLocalization.Away (f * g) (Localization.Away (φ a)) :=
    ha ▸ .mul' (Localization.Away f) _ _ _
  have : Algebra.IsStandardEtale R (Localization.Away a) := .of_isLocalizationAway a
  exact .mk _ (IsLocalization.Away.mapₐ_surjective_of_surjective
    (Aₚ := Localization.Away a) (Bₚ := Localization.Away (φ a)) a hsurj)

lemma HasStandardEtaleSurjectionAt.isStandardEtale
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {f : S} (H : HasStandardEtaleSurjectionAt R f) [Algebra.Etale R (Localization.Away f)] :
    Algebra.IsStandardEtale R (Localization.Away f) :=
  .of_surjective _ _ _ _ H.choose_spec.choose_spec

attribute [local irreducible] Prime in
lemma Algebra.IsUnramifiedAt.exist_hasStandardEtaleSurjectionAt_of_exists_adjoin_singleton_eq_top
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    [Module.Finite R S] (H : ∃ x : S, Algebra.adjoin R {x} = ⊤)
    (Q : Ideal S) [Q.IsPrime] [Algebra.IsUnramifiedAt R Q] :
    ∃ f ∉ Q, HasStandardEtaleSurjectionAt R f := by
  cases subsingleton_or_nontrivial S
  · cases Ideal.IsPrime.ne_top' (Subsingleton.elim Q ⊤)
  have := (algebraMap R S).domain_nontrivial
  let P := Q.under R
  let : Algebra.IsIntegral P.ResidueField Q.ResidueField := inferInstance
  obtain ⟨x, hx⟩ := H
  let I := RingHom.ker (aeval (R := R) x).toRingHom
  have hx' : Function.Surjective (aeval (R := R) x) :=
    (AlgHom.range_eq_top _).mp ((adjoin_singleton_eq_range_aeval R x).symm.trans hx)
  obtain ⟨p, hpI, hp⟩ := Ideal.exists_mem_span_singleton_map_residueField_eq P I
  have hI' : I.map (mapRingHom (algebraMap R P.ResidueField)) =
      RingHom.ker (aeval (1 ⊗ₜ x : P.ResidueField ⊗[R] S)).toRingHom :=
    Algebra.FormallyEtale.isStandardEtale_of_finite_aux P x hx
  have hmp₁ : minpoly P.ResidueField (algebraMap S Q.ResidueField x) ∣ p.map (algebraMap _ _) := by
    rw [minpoly.dvd_iff, aeval_map_algebraMap, aeval_algebraMap_apply,
      show aeval x p = 0 from RingHom.mem_ker.mp hpI, map_zero]
  have hmp₂ :
      ¬ minpoly P.ResidueField (algebraMap S Q.ResidueField x) ^ 2 ∣ p.map (algebraMap _ _) :=
    Algebra.FormallyEtale.isStandardEtale_of_finite_aux2 P Q x p (hp.trans hI') hx'
  let q := minpoly R x ^ (p.natDegree + 2) + p
  have ⟨w, h₁, h₂⟩ : ∃ w, q.map (algebraMap R P.ResidueField) =
      p.map (algebraMap R P.ResidueField) * w ∧
        ¬ minpoly P.ResidueField (algebraMap S Q.ResidueField x) ∣ w := by
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp
      (hp.ge (Ideal.mem_map_of_mem _ (x := minpoly R x) (by simp [I])))
    refine ⟨1 + w * (minpoly R x).map (algebraMap R P.ResidueField) ^ (p.natDegree + 1), ?_, ?_⟩
    · simp_all [q]; grind
    · rw [dvd_add_left (dvd_mul_of_dvd_right (dvd_pow
        (by simp [minpoly.dvd_iff, aeval_algebraMap_apply]) (by simp)) _),
        ← isUnit_iff_dvd_one]
      exact (minpoly.prime (Algebra.IsIntegral.isIntegral _)).not_unit
  have hq : q.Monic := by
    rw [Monic, leadingCoeff_add_of_degree_lt']
    · exact (minpoly.monic (Algebra.IsIntegral.isIntegral x)).pow _
    · refine degree_lt_degree ?_
      rw [natDegree_pow']
      · refine ((Nat.lt_succ_self _).trans (Nat.lt_succ_self _)).trans_le ?_
        exact Nat.le_mul_of_pos_right _ (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral x))
      · simp [minpoly.monic (Algebra.IsIntegral.isIntegral x)]
  have : Algebra.IsSeparable P.ResidueField Q.ResidueField :=
    ((Algebra.isUnramifiedAt_iff_map_eq _ _ _).mp inferInstance).1
  have hqx : aeval x q.derivative ∉ Q := by
    rw [← Ideal.ker_algebraMap_residueField Q, RingHom.mem_ker, ← aeval_algebraMap_apply,
      ← aeval_map_algebraMap P.ResidueField, ← derivative_map, h₁, ← minpoly.dvd_iff]
    simp only [derivative_mul, derivative_map]
    rw [dvd_add_left (dvd_mul_of_dvd_left hmp₁ _),
      (minpoly.prime (Algebra.IsIntegral.isIntegral _)).dvd_mul, not_or]
    refine ⟨fun h₃ ↦ hmp₂ ?_, h₂⟩
    obtain ⟨c, hc⟩ := hmp₁
    letI : derivative (minpoly P.ResidueField ((algebraMap S Q.ResidueField) x)) ≠ 0 := fun h ↦
      (separable_iff_derivative_ne_zero (minpoly.prime (IsIntegral.isIntegral
        (algebraMap S Q.ResidueField x))).irreducible).not_left.mpr h
          (Algebra.IsSeparable.isSeparable P.ResidueField (algebraMap S Q.ResidueField x))
    rw [← derivative_map, hc, derivative_mul, dvd_add_left (by simp),
      (minpoly.prime (Algebra.IsIntegral.isIntegral _)).dvd_mul, dvd_derivative_iff] at h₃
    obtain ⟨d, rfl⟩ := h₃.resolve_left this
    exact ⟨d, by linear_combination hc⟩
  let P : StandardEtalePair R := ⟨q, hq, q.derivative, 1, 0, 1, by simp⟩
  have hP : P.HasMap (algebraMap _ (Localization.Away (aeval x q.derivative)) x) := by
    constructor
    · have : aeval x P.f = 0 := by simpa [P, q]
      rw [aeval_algebraMap_apply, this, map_zero]
    · rw [aeval_algebraMap_apply]; exact IsLocalization.Away.algebraMap_isUnit _
  have : Function.Surjective (P.lift _ hP) := by
    intro a
    obtain ⟨a, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (.powers (aeval x q.derivative)) a
    obtain ⟨a, rfl⟩ := hx' a
    refine ⟨Ideal.Quotient.mk _ (C a * .X ^ n), ?_⟩
    dsimp [StandardEtalePair.Ring, StandardEtalePair.lift]
    simp only [map_mul, map_pow, aeval_X, eval_mul, eval_pow, eval_C,
      ← Units.inv_pow_eq_pow_inv, Units.mul_inv_eq_iff_eq_mul]
    simp [aeval_algebraMap_apply, ← map_pow, P]
  exact ⟨aeval x q.derivative, hqx, .mk _ this⟩

/-- If `S` is an integral `R`-algebra such that `q` is the unique prime of `S` lying over
a prime `p` of `R`, then any `x ∉ q` divides some `r ∉ p`. -/
@[stacks 00EA "(a)"]
lemma exists_mul_eq_algebraMap_of_primesOver_eq_singleton
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
    (q : Ideal S) [q.IsPrime] [Algebra.IsIntegral R S]
    (hq : p.primesOver S = {q}) (x : S) (hx : x ∉ q) :
    ∃ r ∉ p, x ∣ algebraMap _ _ r := by
  simp only [dvd_def, eq_comm, mul_comm x]
  by_contra!
  obtain ⟨Q, hQ, hxQ, hQp⟩ := Ideal.exists_le_prime_disjoint (.span {x})
    (Algebra.algebraMapSubmonoid _ p.primeCompl)
    (by simpa [Set.disjoint_iff_forall_ne, Ideal.mem_span_singleton',
      Algebra.algebraMapSubmonoid, @forall_comm S])
  have hQp' : Q.under _ ≤ p := by
    intro x hxQ
    by_contra hxp
    exact Set.subset_compl_iff_disjoint_right.mpr hQp hxQ ⟨x, hxp, rfl⟩
  obtain ⟨Q', hQ'Q, hQ', hQ'p⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime _ _ hQp'
  obtain rfl : Q' = q := hq.le ⟨hQ', ⟨hQ'p.symm⟩⟩
  exact hx (hQ'Q (hxQ (Ideal.mem_span_singleton_self _)))

lemma localRingHom_injective_of_primesOver_eq_singleton
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
    (q : Ideal S) [q.IsPrime] [Algebra.IsIntegral R S] [FaithfulSMul R S]
    (hq : p.primesOver S = {q}) :
    Function.Injective (Localization.localRingHom p q (algebraMap R S) (hq.ge rfl).2.1) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
  obtain ⟨a, haq, e⟩ : ∃ a ∉ q, a * (algebraMap R S) x = 0 := by
    simpa [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] using hx
  obtain ⟨r, hrp, t, e'⟩ := exists_mul_eq_algebraMap_of_primesOver_eq_singleton _ _ hq _ haq
  refine (IsLocalization.mk'_eq_zero_iff _ _).mpr
    ⟨⟨r, hrp⟩, FaithfulSMul.algebraMap_injective R S ?_⟩
  simp only [map_mul, e', map_zero]
  grind

lemma Localization.finite_of_primesOver_eq_singleton
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
    (q : Ideal S) [q.IsPrime] [Module.Finite R S]
    (hq : p.primesOver S = {q}) [q.LiesOver p] :
    Module.Finite (Localization.AtPrime p) (Localization.AtPrime q) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := S)
  refine ⟨s.image (IsScalarTower.toAlgHom R _ _).toLinearMap, ?_⟩
  rw [Finset.coe_image, ← Submodule.span_span_of_tower R, ← Submodule.map_span, hs,
    Submodule.map_top, LinearMap.coe_range, AlgHom.coe_toLinearMap, IsScalarTower.coe_toAlgHom',
    ← top_le_iff]
  rintro x -
  obtain ⟨x, ⟨s, hsq⟩, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
  obtain ⟨r, hr, t, e'⟩ := exists_mul_eq_algebraMap_of_primesOver_eq_singleton _ _ hq _ hsq
  rw [← Submodule.smul_mem_iff_of_isUnit _ (IsLocalization.map_units (M := p.primeCompl) _ ⟨r, hr⟩),
    Algebra.smul_def, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply _ S, e',
      map_mul, mul_assoc, mul_left_comm, IsLocalization.mk'_spec'_mk, ← map_mul]
  exact Submodule.subset_span ⟨_, rfl⟩

instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Algebra.IsUnramifiedAt R q] :
    Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q) :=
  .of_restrictScalars R _ _

lemma localRingHom_surjective_of_primesOver_eq_singleton
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] (hq : p.primesOver S = {q})
    [Algebra.IsUnramifiedAt R q]
    (H : Function.Surjective (algebraMap p.ResidueField q.ResidueField)) :
    Function.Surjective (Localization.localRingHom p q (algebraMap R S) (q.over_def p)) := by
  have := Localization.finite_of_primesOver_eq_singleton _ _ hq
  change Function.Surjective (Algebra.linearMap _ _)
  rw [← LinearMap.range_eq_top, ← top_le_iff]
  apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top (maximalIdeal_le_jacobson _)
  rw [Ideal.smul_top_eq_map, Algebra.FormallyUnramified.map_maximalIdeal]
  rintro x -
  obtain ⟨a, ha⟩ := H (algebraMap _ _ x)
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a
  rw [← ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply _ (Localization.AtPrime q), ResidueField.algebraMap_eq,
    ← sub_eq_zero, ← map_sub, residue_eq_zero_iff] at ha
  rw [← sub_sub_self (algebraMap _ _ a) x]
  refine sub_mem (Submodule.mem_sup_left ⟨_, rfl⟩) (Submodule.mem_sup_right ha)

lemma Localization.exists_awayMap_injective_of_localRingHom_injective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (hRS : (RingHom.ker (algebraMap R S)).FG)
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (H : Function.Injective (Localization.localRingHom p q (algebraMap R S) (q.over_def p))) :
    ∃ r ∉ p, ∀ r', r ∣ r' → Function.Injective (Localization.awayMap (algebraMap R S) r') := by
  classical
  obtain ⟨s, hs⟩ := hRS
  have (x : s) : algebraMap R (Localization.AtPrime p) x.1 = 0 := by
    apply H
    simp [Localization.localRingHom_to_map, -FaithfulSMul.algebraMap_eq_zero_iff,
      show algebraMap R S _ = 0 from hs.le (Ideal.subset_span x.2)]
  choose m hm using fun x ↦ (IsLocalization.map_eq_zero_iff p.primeCompl _ _).mp (this x)
  have H : RingHom.ker (algebraMap R S) ≤ RingHom.ker
      (algebraMap R (Localization.Away (∏ i, m i).1)) := by
    rw [← hs, Ideal.span_le]
    intro x hxs
    refine (IsLocalization.map_eq_zero_iff (.powers (∏ i, m i).1) _ _).mpr ⟨⟨_, 1, rfl⟩, ?_⟩
    simp only [pow_one]
    rw [Fintype.prod_eq_mul_prod_compl ⟨x, hxs⟩, Submonoid.coe_mul, mul_assoc, mul_left_comm, hm,
      mul_zero]
  refine ⟨_, (∏ i : s, m i).2, ?_⟩
  rintro r' ⟨s, e⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, _, rfl⟩ := IsLocalization.exists_mk'_eq (.powers r') x
  simp only [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_mk',
    IsLocalization.mk'_eq_zero_iff] at hx
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := hx
  simp only [← map_pow, ← map_mul] at hn
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (.powers (∏ i, m i).1) _ _).mp (H hn)
  refine (IsLocalization.mk'_eq_zero_iff _ _).mpr ⟨⟨_, k + n, rfl⟩, ?_⟩
  dsimp only at hk ⊢
  rw [pow_add, mul_assoc, e, mul_pow, ← e, mul_assoc, mul_left_comm, hk, mul_zero]

lemma Localization.exists_awayMap_surjective_of_localRingHom_surjective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (hRS : (RingHom.ker (algebraMap R S)).FG)
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] (hq : p.primesOver S = {q})
    (H : Function.Bijective (Localization.localRingHom p q (algebraMap R S) (q.over_def p))) :
    ∃ r ∉ p, ∀ r', r ∣ r' → Function.Bijective (Localization.awayMap (algebraMap R S) r') := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := S)
  have (x : S) : ∃ a, ∃ b ∉ p, algebraMap R S a = x * algebraMap R S b := by
    have := (IsLocalization.mk'_surjective p.primeCompl).exists.mp (H.2 (algebraMap _ _ x))
    simp only [localRingHom_mk', Prod.exists, Subtype.exists, Ideal.mem_primeCompl_iff,
      IsLocalization.mk'_eq_iff_eq_mul, exists_prop, ← map_mul,
      IsLocalization.eq_iff_exists q.primeCompl] at this
    obtain ⟨a, b, hbp, c, hcq, hc⟩ := this
    obtain ⟨d, hd, e, he⟩ := exists_mul_eq_algebraMap_of_primesOver_eq_singleton _ _ hq _ hcq
    exact ⟨d * a, d * b, ‹p.IsPrime›.mul_notMem hd hbp, by grind⟩
  choose a b hbp e using this
  obtain ⟨r, hrp, hr⟩ := Localization.exists_awayMap_injective_of_localRingHom_injective hRS _ _ H.1
  refine ⟨r * ∏ i ∈ s, b i, mul_mem (s := p.primeCompl) hrp (prod_mem fun _ _ ↦ hbp _), ?_⟩
  refine fun r' hr' ↦ ⟨hr _ (.trans ⟨_, rfl⟩ hr'), ?_⟩
  have H : (IsScalarTower.toAlgHom R S _).range ≤
      (Localization.awayMapₐ (Algebra.ofId R S) r').range := by
    rw [← Algebra.map_top, Subalgebra.map_le, ← hs, Algebra.adjoin_le_iff]
    intro x hxs
    obtain ⟨r'', hr'⟩ := hr'
    refine ⟨IsLocalization.mk' (M := .powers r') _
      (r'' * r * (∏ i ∈ s.erase x, b i) * a x) ⟨_, 1, rfl⟩, ?_⟩
    dsimp [awayMapₐ, IsLocalization.Away.map]
    simp only [pow_one, IsLocalization.map_mk', IsLocalization.mk'_eq_iff_eq_mul,
      ← map_mul (algebraMap S _), map_mul (algebraMap R _), e]
    congr 1
    rw [hr', ← Finset.prod_erase_mul s b hxs, map_mul, map_mul, map_mul]
    ring_nf
  intro x
  obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (.powers (algebraMap R S r')) x
  obtain ⟨y, hy : awayMap _ _ _ = _⟩ := H ⟨x, rfl⟩
  dsimp at hy
  refine ⟨y * Localization.Away.invSelf _ ^ n, ?_⟩
  simp only [map_mul, hy]
  simp [Away.invSelf, Localization.mk_eq_mk', awayMap, IsLocalization.Away.map,
    IsLocalization.map_mk', ← Algebra.smul_def, IsLocalization.smul_mk', ← IsLocalization.mk'_pow]

set_option maxHeartbeats 0 in
-- set_option synthInstance.maxHeartbeats 0 in
lemma Ideal.Fiber.liftResidueField_surjective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p] [Module.Finite R S] :
    Function.Surjective (Algebra.TensorProduct.lift (Algebra.ofId _ _)
      (IsScalarTower.toAlgHom _ _ _) fun _ _ ↦ .all _ _ :
      p.Fiber S →ₐ[p.ResidueField] q.ResidueField) := by
  set φ : p.Fiber S →ₐ[p.ResidueField] q.ResidueField := Algebra.TensorProduct.lift
      (Algebra.ofId _ _) (IsScalarTower.toAlgHom _ _ _) fun _ _ ↦ .all _ _
  intro x
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨x, ⟨y, hy : y ∉ q⟩, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
  have : IsArtinianRing (p.Fiber S) := .of_finite p.ResidueField _
  obtain ⟨n, z, hz⟩ := IsArtinian.exists_pow_succ_smul_dvd (1 ⊗ₜ y : p.Fiber S) (1 : p.Fiber S)
  use 1 ⊗ₜ x * z
  have : algebraMap _ q.ResidueField y ^ n ≠ 0 := by simp [hy]
  have : algebraMap S q.ResidueField y * φ z = 1 := by
    simpa [pow_succ, mul_assoc, hy, φ] using congr(φ $hz)
  apply (IsUnit.mk0 (algebraMap _ _ y) (by simp [hy])).mul_right_injective
  simp only [map_mul, mul_left_comm (algebraMap _ _ y), this, mul_one]
  rw [IsScalarTower.algebraMap_apply S (Localization.AtPrime q) q.ResidueField,
    ← IsLocalRing.ResidueField.algebraMap_eq, ← map_mul, IsLocalization.mk'_spec'_mk,
    ← IsScalarTower.algebraMap_apply]
  simp [φ]

lemma IsArtinianRing.exists_not_mem_forall_mem_of_ne'
    {R : Type*} [CommRing R] [IsArtinianRing R] (p : Ideal R) [p.IsPrime] :
    ∃ r ∉ p, IsIdempotentElem r ∧ ∀ q : Ideal R, q.IsPrime → q ≠ p → r ∈ q := by
  classical
  obtain ⟨r, hr⟩ := PrimeSpectrum.toPiLocalization_bijective.2 (Pi.single ⟨p, inferInstance⟩ 1)
  have : algebraMap R (Localization p.primeCompl) r = 1 := by
    simpa [PrimeSpectrum.toPiLocalization,
      -FaithfulSMul.algebraMap_eq_one_iff] using funext_iff.mp hr ⟨p, inferInstance⟩
  refine ⟨r, ?_, ?_, ?_⟩
  · rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p, this]
    simp
  · apply PrimeSpectrum.toPiLocalization_bijective.injective
    simp [map_mul, hr, ← Pi.single_mul]
  · intro q hq e
    have : PrimeSpectrum.mk q inferInstance ≠ ⟨p, inferInstance⟩ := ne_of_apply_ne (·.1) e
    have : (algebraMap R (Localization.AtPrime q)) r = 0 := by
      simpa [PrimeSpectrum.toPiLocalization, this,
        -FaithfulSMul.algebraMap_eq_zero_iff] using funext_iff.mp hr ⟨q, inferInstance⟩
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q, this]
    simp

instance {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] :
    Algebra.EssFiniteType R p.ResidueField :=
  have : Algebra.FiniteType (Localization.AtPrime p) p.ResidueField :=
    .of_surjective (Algebra.ofId _ _) IsLocalRing.residue_surjective
  .comp _ (Localization.AtPrime p) _

instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    Algebra.EssFiniteType p.ResidueField q.ResidueField := by
  have : Algebra.EssFiniteType R q.ResidueField := .comp _ S _
  refine .of_comp R _ _

attribute [local instance 100000] Algebra.toModule Module.toDistribMulAction
  DistribMulAction.toMulAction MulAction.toSemigroupAction SemigroupAction.toSMul
  IsScalarTower.right in
lemma Algebra.IsUnramifiedAt.exists_notMem_forall_ne_mem_and_adjoin_eq_top
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (Q : Ideal S) [Q.IsPrime] [Module.Finite R S] [Algebra.IsUnramifiedAt R Q] :
    ∃ t ∉ Q, (∀ Q' ∈ (Q.under R).primesOver S, Q' ≠ Q → t ∈ Q') ∧
      adjoin (Ideal.under R Q).ResidueField {algebraMap _ Q.ResidueField t} = ⊤ := by
  let p := Q.under R
  letI : Algebra p.ResidueField (p.Fiber S) := TensorProduct.leftAlgebra ..
  have : IsScalarTower p.ResidueField (p.Fiber S) (p.Fiber S) := IsScalarTower.right
  have : Module.Free p.ResidueField Q.ResidueField := .of_divisionRing ..
  classical
  have : IsArtinianRing (p.Fiber S) := .of_finite p.ResidueField _
  let α := PrimeSpectrum.primesOverOrderIsoFiber R S p
  have := Algebra.FormallyUnramified.finite_of_free p.ResidueField Q.ResidueField
  obtain ⟨x, hx0, hx⟩ : ∃ x : Q.ResidueField, x ≠ 0 ∧
      Algebra.adjoin (Ideal.under R Q).ResidueField {x} = ⊤ := by
    obtain ⟨x, hx⟩ := Field.exists_primitive_element p.ResidueField Q.ResidueField
    rw [IntermediateField.adjoin_eq_top_iff] at hx
    by_cases hx0 : x = 0
    · exact ⟨1, by simp, by simpa [p, hx0] using hx⟩
    · exact ⟨x, hx0, hx⟩
  obtain ⟨x, rfl⟩ := Ideal.Fiber.liftResidueField_surjective p _ x
  set φ : p.Fiber S →ₐ[p.ResidueField] Q.ResidueField := Algebra.TensorProduct.lift
      (Algebra.ofId _ _) (IsScalarTower.toAlgHom _ _ _) fun _ _ ↦ .all _ _
  obtain ⟨r, hrQ, hrid, hr⟩ :=
    IsArtinianRing.exists_not_mem_forall_mem_of_ne' (α ⟨Q, ‹_›, ⟨rfl⟩⟩).asIdeal
  obtain ⟨s, hsQ, t, e⟩ := Ideal.Fiber.exists_smul_eq_one_tmul _ (r * x)
  have hrQ' : φ r ≠ 0 := hrQ
  have hsQ' : algebraMap R Q.ResidueField s ≠ 0 := by
    simpa [IsScalarTower.algebraMap_apply R S Q.ResidueField]
  replace hrQ' : φ r = 1 := by
    simpa [hrQ', sub_eq_zero, @eq_comm _ _ (φ r)] using (hrid.map φ).one_sub_mul_self
  have e' : algebraMap _ _ s * φ x = algebraMap _ _ t := by
    simpa [φ, Algebra.smul_def, mul_assoc, hrQ'] using congr(φ $e)
  refine ⟨t, ?_, ?_, ?_⟩
  · rw [← Ideal.algebraMap_residueField_eq_zero, ← e']
    simpa [hx0, IsScalarTower.algebraMap_apply R S Q.ResidueField]
  · rintro Q' ⟨_, _⟩ H
    have hsQ'' : algebraMap R Q'.ResidueField s ≠ 0 := by
      suffices s ∉ Q'.under _ by simpa [IsScalarTower.algebraMap_apply R S Q'.ResidueField]
      rwa [← Q'.over_def p]
    let φ' : p.Fiber S →ₐ[p.ResidueField] Q'.ResidueField := Algebra.TensorProduct.lift
        (Algebra.ofId _ _) (IsScalarTower.toAlgHom _ _ _) fun _ _ ↦ .all _ _
    have H : φ' r = 0 := (hr (α ⟨Q', ⟨‹_›, ‹_›⟩⟩).asIdeal inferInstance (by
        rwa [ne_eq, ← PrimeSpectrum.ext_iff, EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq]):)
    rw [← Ideal.algebraMap_residueField_eq_zero]
    trans φ' (1 ⊗ₜ t)
    · simp [φ']
    · simpa [Algebra.smul_def, H] using congr(φ' $e).symm
  · have : φ x = (algebraMap _ p.ResidueField s)⁻¹ • algebraMap _ _ t := by
      simpa [Algebra.smul_def, ← IsScalarTower.algebraMap_apply, eq_inv_mul_iff_mul_eq₀ hsQ']
    rw [← top_le_iff, ← hx, this]
    refine adjoin_singleton_le ?_
    exact Subalgebra.smul_mem _ (self_mem_adjoin_singleton _ _) _

attribute [local instance 100000] Algebra.toModule Module.toDistribMulAction
  DistribMulAction.toMulAction MulAction.toSemigroupAction SemigroupAction.toSMul
  IsScalarTower.right in
lemma Algebra.FormallyEtale.isStandardEtale_of_isNoetherianRing_aux
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (Q : Ideal S) [Q.IsPrime] [Module.Finite R S] [Algebra.IsUnramifiedAt R Q] :
    ∃ x : S, (Q.under (Algebra.adjoin R {x})).primesOver S = {Q} ∧
      Function.Surjective (algebraMap (Q.under (Algebra.adjoin R {x})).ResidueField
        Q.ResidueField) := by
  obtain ⟨t, htQ, htQ', ht⟩ :=
    Algebra.IsUnramifiedAt.exists_notMem_forall_ne_mem_and_adjoin_eq_top (R := R) Q
  let p := Q.under R
  classical
  refine ⟨t, ?_, ?_⟩
  · refine Set.ext fun Q' ↦ ⟨fun ⟨_, _⟩ ↦ ?_, fun e ↦ by exact ⟨e ▸ inferInstance, ⟨e ▸ rfl⟩⟩⟩
    by_contra! H
    have : Q'.LiesOver p := .trans _ (Q.under (adjoin R {t})) _
    exact htQ (SetLike.le_def.mp (Q'.over_def (Q.under (adjoin R {t}))).ge
      (x := ⟨t, self_mem_adjoin_singleton _ _⟩) (htQ' Q' ⟨‹_›, ‹_›⟩ H))
  · change Function.Surjective (IsScalarTower.toAlgHom p.ResidueField _ _)
    rw [← AlgHom.range_eq_top, ← top_le_iff, ← ht]
    refine adjoin_singleton_le ?_
    use algebraMap (adjoin R {t}) _ ⟨t, self_mem_adjoin_singleton _ _⟩
    let : Algebra (adjoin R {t}) (Localization.AtPrime Q) :=
      OreLocalization.instAlgebra
    let : Algebra (adjoin R {t}) Q.ResidueField :=
      ResidueField.algebra _
    have : IsScalarTower (adjoin R {t}) (Localization.AtPrime (Q.under (adjoin R {t})))
        (Localization.AtPrime Q) := Localization.AtPrime.instIsScalarTower ..
    have : IsScalarTower (adjoin R {t}) (Q.under (adjoin R {t})).ResidueField Q.ResidueField :=
      ResidueField.instIsScalarTower
    rw [AlgHom.toRingHom_eq_coe, IsScalarTower.coe_toAlgHom, ← IsScalarTower.algebraMap_apply]
    rfl

lemma Algebra.IsStandardEtale.of_dvd {R A Aₛ Aₜ : Type*}
    [CommRing R] [CommRing A] [CommRing Aₛ] [CommRing Aₜ]
    [Algebra R A] [Algebra R Aₛ] [Algebra R Aₜ] [Algebra A Aₛ] [Algebra A Aₜ]
    [IsScalarTower R A Aₛ] [IsScalarTower R A Aₜ] {s t : A} (h : s ∣ t)
    [IsLocalization.Away s Aₛ] [IsLocalization.Away t Aₜ] [IsStandardEtale R Aₛ] :
    IsStandardEtale R Aₜ := by
  obtain ⟨t, rfl⟩ := h
  have : IsLocalization.Away (s * t) (Localization.Away (algebraMap A Aₛ t)) := .mul' Aₛ _ _ _
  let e : Localization.Away (algebraMap A Aₛ t) ≃ₐ[A] Aₜ :=
    IsLocalization.algEquiv (.powers (s * t)) _ _
  have : IsStandardEtale R (Localization.Away (algebraMap A Aₛ t)) :=
    .of_isLocalizationAway (algebraMap A Aₛ t)
  exact .of_equiv (e.restrictScalars R)

-- set_option synthInstance.maxHeartbeats 0 in
attribute [-simp] mul_eq_zero smul_eq_zero FaithfulSMul.ker_algebraMap_eq_bot map_eq_zero in
attribute [local instance 11000] RingHom.instRingHomClass RingHomClass.toAddMonoidHomClass
  Algebra.toModule Module.toDistribMulAction
  DistribMulAction.toMulAction MulAction.toSemigroupAction SemigroupAction.toSMul
  IsScalarTower.right in
lemma Algebra.IsUnramifiedAt.exist_hasStandardEtaleSurjectionAt_of_finite
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    (Q : Ideal S) [Q.IsPrime] [Module.Finite R S] [Algebra.IsUnramifiedAt R Q] :
    ∃ f ∉ Q, HasStandardEtaleSurjectionAt R f := by
  obtain ⟨x, hQ', hQ'Q⟩ := Algebra.FormallyEtale.isStandardEtale_of_isNoetherianRing_aux (R := R) Q
  let S' := Algebra.adjoin R {x}
  let Q' := Q.under S'
  have : Module.Finite S' S := .of_restrictScalars_finite R _ _
  have : IsUnramifiedAt S' Q := .of_restrictScalars R _
  have hφ : Function.Bijective (Localization.localRingHom Q' Q S'.val rfl) :=
    ⟨localRingHom_injective_of_primesOver_eq_singleton _ _ hQ',
      localRingHom_surjective_of_primesOver_eq_singleton _ _ hQ' hQ'Q⟩
  obtain ⟨r, hrQ', H⟩ := Localization.exists_awayMap_surjective_of_localRingHom_surjective
    (by rw [FaithfulSMul.ker_algebraMap_eq_bot S' S]; exact Submodule.fg_bot) _ _ hQ' hφ
  have : Module.Finite R S' := finite_adjoin_simple_of_isIntegral (Algebra.IsIntegral.isIntegral _)
  have : IsUnramifiedAt R Q' := by
    let φ : Localization.AtPrime Q' ≃ₐ[R] Localization.AtPrime Q :=
      .ofBijective (IsScalarTower.toAlgHom _ _ _) hφ
    exact .of_equiv φ.symm
  obtain ⟨f, hfQ', hf⟩ :=
    Algebra.IsUnramifiedAt.exist_hasStandardEtaleSurjectionAt_of_exists_adjoin_singleton_eq_top
    (R := R) (S := S') ⟨⟨x, Algebra.self_mem_adjoin_singleton _ _⟩, Subalgebra.map_injective
      (f := S'.val) Subtype.val_injective (by simp [Subalgebra.range_val, S'])⟩ Q'
  obtain ⟨P, φ, hP⟩ := hf.of_dvd (g := f * r) (by simp)
  exact ⟨_, (inferInstanceAs Q'.IsPrime).mul_notMem hfQ' hrQ', .mk
    (f := IsScalarTower.toAlgHom R S' S (f * r))
    ((Localization.awayMapₐ (IsScalarTower.toAlgHom _ _ S) (f * r)).comp φ)
    ((H _ (by simp)).surjective.comp hP)⟩

lemma ZariskiMainProperty.exists_fg_and_exists_notMem_and_awayMap_bijective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (p : Ideal S) [p.IsPrime] (H : ZariskiMainProperty R p) :
    ∃ S' : Subalgebra R S, S'.toSubmodule.FG ∧ ∃ r : S',
      r.1 ∉ p ∧ Function.Bijective (Localization.awayMap S'.val.toRingHom r) := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := S)
  choose r hrp hr m hm using zariskiMainProperty_iff.mp H
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

attribute [local instance high] Module.Free.of_divisionRing in
set_option synthInstance.maxHeartbeats 0 in
lemma Algebra.QuasiFinite.of_formallyUnramified
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S] : Algebra.QuasiFinite R S where
  finite_fiber _ _ := Algebra.FormallyUnramified.finite_of_free _ _

instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S]
    (Q : Ideal S) [Q.IsPrime] [Algebra.IsUnramifiedAt R Q] : Algebra.QuasiFiniteAt R Q :=
  .of_formallyUnramified

lemma awayMap_injective_iff {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S} {r : R} :
    Function.Injective (Localization.awayMap f r) ↔ ∀ a, f a = 0 → ∃ n, r ^ n * a = 0 := by
  rw [injective_iff_map_eq_zero]
  trans ∀ a n, f r ^ n * f a = 0 → ∃ m, r ^ m * a = 0
  · simp [(IsLocalization.mk'_surjective (.powers r)).forall, Submonoid.mem_powers_iff,
      Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_mk',
      IsLocalization.mk'_eq_zero_iff]
  · refine ⟨fun H x hx ↦ H x 0 (by simpa), fun H a n ha ↦ ?_⟩
    obtain ⟨m, hm⟩ := H (r ^ n * a) (by simpa)
    exact ⟨m + n, by simp [pow_add, mul_assoc, *]⟩

lemma awayMap_surjective_iff {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S} {r : R} :
    Function.Surjective (Localization.awayMap f r) ↔ ∀ a, ∃ b m, f b = f r ^ m * a := by
  trans ∀ a n, ∃ b m k, f (r ^ (k + n) * b) = f r ^ (k + m) * a
  · simp [Function.Surjective, (IsLocalization.mk'_surjective (.powers (f r))).forall, ← map_pow,
      (IsLocalization.mk'_surjective (.powers r)).exists, Submonoid.mem_powers_iff, pow_add,
      Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_mk', ← mul_assoc,
      IsLocalization.mk'_eq_iff_eq, ← map_mul, IsLocalization.eq_iff_exists (.powers (f r))]
  · refine ⟨fun H x ↦ ⟨_, _, (H x 0).choose_spec.choose_spec.choose_spec⟩, fun H a n ↦ ?_⟩
    obtain ⟨b, m, e⟩ := H a
    exact ⟨b, n + m, 0, by simp [e, pow_add]; ring_nf⟩

lemma awayMap_bijective_of_dvd {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {a b : R} (h : a ∣ b) (H : Function.Bijective (Localization.awayMap f a)) :
    Function.Bijective (Localization.awayMap f b) := by
  simp only [Function.Bijective, awayMap_injective_iff, awayMap_surjective_iff] at H ⊢
  obtain ⟨b, rfl⟩ := h
  refine ⟨fun x hx ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨n, hn⟩ := H.1 x hx
    exact ⟨n, by simp [mul_pow, mul_assoc, mul_left_comm (a ^ n), hn]⟩
  · obtain ⟨c, m, e⟩ := H.2 x
    exact ⟨b ^ m * c, m, by simp [mul_pow, e, mul_assoc, mul_left_comm]⟩

lemma Algebra.exists_formallyUnramified_of_isUnramifiedAt
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (P : Ideal A) [P.IsPrime] [Algebra.IsUnramifiedAt R P] [EssFiniteType R A] :
    ∃ f ∉ P, Algebra.FormallyUnramified R (Localization.Away f) := by
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hpr, hr⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
      (show ⟨P, ‹_›⟩ ∈ unramifiedLocus R A by assumption) isOpen_unramifiedLocus
  exact ⟨r, hpr, basicOpen_subset_unramifiedLocus_iff.mp hr⟩

-- set_option synthInstance.maxHeartbeats 0 in
attribute [-simp] mul_eq_zero smul_eq_zero FaithfulSMul.ker_algebraMap_eq_bot map_eq_zero in
attribute [local instance 11000] RingHom.instRingHomClass RingHomClass.toAddMonoidHomClass
  Algebra.toModule Module.toDistribMulAction
  DistribMulAction.toMulAction MulAction.toSemigroupAction SemigroupAction.toSMul
  IsScalarTower.right in
lemma Algebra.Unramified.exist_hasStandardEtaleSurjectionAt
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    (Q : Ideal S) [Q.IsPrime] [Algebra.Unramified R S] :
    ∃ f ∉ Q, HasStandardEtaleSurjectionAt R f := by
  obtain ⟨S', hS', r, hrQ, hr⟩ := ZariskiMainProperty.of_finiteType (R := R) Q
    |>.exists_fg_and_exists_notMem_and_awayMap_bijective
  have : Module.Finite R S' := ⟨(Submodule.fg_top _).mpr hS'⟩
  have : Algebra.FormallyUnramified R (Localization.Away r) :=
    .of_equiv (AlgEquiv.ofBijective (Localization.awayMapₐ S'.val r) hr:).symm
  have : IsUnramifiedAt R (Ideal.under (↥S') Q) := by
    rw [← Algebra.basicOpen_subset_unramifiedLocus_iff] at this
    exact @this ⟨Q.under S', inferInstance⟩ hrQ
  obtain ⟨f, hfQ, hf⟩ :=
    Algebra.IsUnramifiedAt.exist_hasStandardEtaleSurjectionAt_of_finite (R := R) (Q.under S')
  let e : Localization.Away (r * f) ≃ₐ[R] Localization.Away (r.1 * f.1) :=
    .ofBijective (Localization.awayMapₐ S'.val (r * f))
      (awayMap_bijective_of_dvd _ (dvd_mul_right r f) hr)
  obtain ⟨P, φ, hφ⟩ := hf.of_dvd (g := r * f) (by simp)
  refine ⟨_, ‹Q.IsPrime›.mul_notMem hrQ hfQ,
    .mk (f := r.1 * f.1) (e.toAlgHom.comp φ) (e.surjective.comp hφ)⟩

instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S] (s : S) :
    Algebra.FiniteType R (Localization.Away s) :=
  .trans (S := S) inferInstance inferInstance

lemma Algebra.IsUnramifiedAt.exist_hasStandardEtaleSurjectionAt
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    (Q : Ideal S) [Q.IsPrime] [FiniteType R S] [Algebra.IsUnramifiedAt R Q] :
    ∃ f ∉ Q, HasStandardEtaleSurjectionAt R f := by
  obtain ⟨s, hsQ, hs⟩ := Algebra.exists_formallyUnramified_of_isUnramifiedAt (R := R) Q
  have : (Ideal.map (algebraMap S (Localization.Away s)) Q).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers s) _ _ ‹_› (by simp [Set.disjoint_iff,
      Set.ext_iff, Submonoid.mem_powers_iff, mt (‹Q.IsPrime›.mem_of_pow_mem _) hsQ])
  have : Unramified R (Localization.Away s) := {}
  obtain ⟨f, hf, H⟩ := Algebra.Unramified.exist_hasStandardEtaleSurjectionAt (R := R)
    (Q.map (algebraMap _ (Localization.Away s)))
  obtain ⟨f, t, rfl⟩ := IsLocalization.exists_mk'_eq (.powers s) f
  refine ⟨s * f, ?_, ?_⟩
  · simpa [IsLocalization.mk'_mem_map_algebraMap_iff, Submonoid.mem_powers_iff,
      Ideal.IsPrime.mul_mem_left_iff, hsQ, (mt (‹Q.IsPrime›.mem_of_pow_mem _) hsQ)] using hf
  obtain ⟨P, φ, hφ⟩ : HasStandardEtaleSurjectionAt R (algebraMap S (Localization.Away s) f) :=
    H.of_dvd ⟨algebraMap _ _ t.1, by simp⟩
  exact .mk _ hφ

section

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A] [Algebra R A]

@[simps]
noncomputable
def StandardEtalePair.map (𝓟 : StandardEtalePair R) (f : R →+* S) : StandardEtalePair S where
  f := 𝓟.f.map f
  monic_f := 𝓟.monic_f.map _
  g := 𝓟.g.map f
  cond := by
    obtain ⟨p₁, p₂, n, e⟩ := 𝓟.cond
    refine ⟨p₁.map f, p₂.map f, n, ?_⟩
    simp [← Polynomial.map_mul, ← Polynomial.map_add, e]

lemma StandardEtalePair.HasMap.map_algebraMap [Algebra R S] [Algebra S A] [IsScalarTower R S A]
    {𝓟 : StandardEtalePair R} {x : A} (H : 𝓟.HasMap x) :
    (𝓟.map (algebraMap R S)).HasMap x := by
  simpa [HasMap]

lemma StandardEtalePresentation.hom_ext [Algebra R S] (𝓟 : StandardEtalePresentation R S)
    {f₁ f₂ : S →ₐ[R] A} (h : f₁ 𝓟.x = f₂ 𝓟.x) : f₁ = f₂ := by
  have : f₁.comp 𝓟.equivRing.symm.toAlgHom = f₂.comp 𝓟.equivRing.symm.toAlgHom :=
    𝓟.P.hom_ext (by simpa)
  ext x
  obtain ⟨x, rfl⟩ := 𝓟.equivRing.symm.surjective x
  exact congr($this x)

noncomputable
def StandardEtalePresentation.baseChange [Algebra R S] (𝓟 : StandardEtalePresentation R S) :
    StandardEtalePresentation A (A ⊗[R] S) where
  __ := 𝓟.map (algebraMap R A)
  x := 1 ⊗ₜ 𝓟.x
  hasMap := (𝓟.hasMap.map (Algebra.TensorProduct.includeRight (R := R) (A := A))).map_algebraMap
  lift_bijective := by
    algebraize [(algebraMap A (𝓟.map (algebraMap R A)).Ring).comp (algebraMap R A)]
    have H : 𝓟.HasMap (𝓟.map (algebraMap R A)).X := by
      exact ⟨by simpa using (𝓟.map (algebraMap R A)).hasMap_X.1,
        by simpa using (𝓟.map (algebraMap R A)).hasMap_X.2⟩
    let f : A ⊗[R] S →ₐ[A] (𝓟.map (algebraMap R A)).Ring :=
      Algebra.TensorProduct.lift (Algebra.ofId _ _) ((𝓟.lift (𝓟.map _).X H).comp 𝓟.equivRing)
        fun _ _ ↦ .all _ _
    let α : A ⊗[R] S ≃ₐ[A] (𝓟.map (algebraMap R A)).Ring :=
      .ofAlgHom f ((𝓟.map (algebraMap R A)).lift (1 ⊗ₜ[R] 𝓟.x)
        (𝓟.hasMap.map (Algebra.TensorProduct.includeRight (R := R) (A := A))).map_algebraMap) (by
        ext; simp [f]) (by
        ext1
        · ext
        · apply 𝓟.hom_ext; simp [f])
    exact α.symm.bijective

instance [Algebra R S] [Algebra.IsStandardEtale R S] :
    Algebra.IsStandardEtale A (A ⊗[R] S) :=
  ⟨⟨Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some.baseChange⟩⟩

end

lemma Algebra.IsEtaleAt.exists_isStandardEtale
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    (Q : Ideal S) [Q.IsPrime] [Algebra.FinitePresentation R S] [Algebra.IsEtaleAt R Q] :
    ∃ f, f ∉ Q ∧ IsStandardEtale R (Localization.Away f) := by
  obtain ⟨f, hfQ, h⟩ := exists_etale_of_isEtaleAt (R := R) Q
  obtain ⟨g, hgQ, hg⟩ := Algebra.IsUnramifiedAt.exist_hasStandardEtaleSurjectionAt (R := R) Q
  have : Etale R (Localization.Away (f * g)) := by
    rw [← basicOpen_subset_etaleLocus_iff_etale] at h ⊢
    exact .trans (PrimeSpectrum.basicOpen_mul_le_left _ _) h
  exact ⟨f * g, ‹Q.IsPrime›.mul_notMem hfQ hgQ, (hg.of_dvd (by simp)).isStandardEtale⟩
