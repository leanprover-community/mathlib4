module
-- import Mathlib.Algebra.Lie.OfAssociative
-- import Mathlib.Order.BourbakiWitt
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
-- import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.QuasiFinite
-- import Mathlib.RingTheory.SimpleRing.Principal
-- import Mathlib

@[expose] public section

open TensorProduct

lemma PrimeSpectrum.toPiLocalization_bijective {R : Type*} [CommRing R]
    [DiscreteTopology (PrimeSpectrum R)] : Function.Bijective (PrimeSpectrum.toPiLocalization R) :=
  PrimeSpectrum.discreteTopology_iff_toPiLocalization_bijective.mp inferInstance

lemma IsArtinianRing.exists_not_mem_forall_mem_of_ne
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

attribute [local instance] RingHom.ker_isPrime

open scoped nonZeroDivisors

@[simp]
lemma Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul_one {A B : Type*} [CommRing A]
      [CommRing B] [Algebra A B] (I : Ideal A) (b : B) :
    (quotIdealMapEquivTensorQuot B I).symm (b ⊗ₜ[A] 1) = Ideal.Quotient.mk _ b :=
  (quotIdealMapEquivTensorQuot_symm_tmul ..).trans (by simp)

attribute [ext high] Ideal.Quotient.algHom_ext

open scoped nonZeroDivisors

attribute [ext high] Ideal.Quotient.algHom_ext

instance {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : S →ₐ[R] T) (I : Ideal T) (J : Ideal R) [I.LiesOver J] : (I.comap f).LiesOver J := by
  constructor; ext; simp [I.over_def J]

attribute [ext high] Ideal.Quotient.algHom_ext

open TensorProduct

attribute [local instance] RingHom.ker_isPrime

open scoped nonZeroDivisors

attribute [local instance high] Algebra.TensorProduct.leftAlgebra IsScalarTower.right
  DivisionRing.instIsArtinianRing in
lemma exists_not_mem_forall_mem_of_ne_of_liesOver
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    ∃ s ∉ q, ∀ q' : Ideal S, q'.IsPrime → q' ≠ q → q'.LiesOver p → s ∈ q' := by
  classical
  let F := p.ResidueField ⊗[R] S
  let e := PrimeSpectrum.preimageEquivFiber _ S ⟨p, inferInstance⟩
  have : IsScalarTower R p.ResidueField p.ResidueField := inferInstance
  let : IsArtinianRing F := .of_finite p.ResidueField _
  obtain ⟨r : p.ResidueField ⊗[R] S, hr, hr'⟩ := IsArtinianRing.exists_not_mem_forall_mem_of_ne
    (e ⟨⟨q, ‹_›⟩, PrimeSpectrum.ext (q.over_def p).symm⟩).asIdeal
  obtain ⟨s, hs, x, hsx⟩ := Ideal.Fiber.exists_smul_eq_one_tmul _ r
  have : x ∉ q := by
    rw [PrimeSpectrum.preimageEquivFiber_apply_asIdeal,
        ← Ideal.IsPrime.mul_mem_left_iff (x := algebraMap _ _ s), ← Algebra.smul_def, hsx] at hr
    · simpa using hr
    · simpa [IsScalarTower.algebraMap_apply R S q.ResidueField, q.over_def p] using hs
  refine ⟨x, this, fun q' _ hq' _ ↦ ?_⟩
  have := Ideal.mul_mem_left _ (algebraMap _ _ s) (hr'.2 (e ⟨⟨q', ‹_›⟩,  PrimeSpectrum.ext
    (q'.over_def p).symm⟩).asIdeal inferInstance (mt PrimeSpectrum.ext (e.injective.ne (by simpa))))
  rw [PrimeSpectrum.preimageEquivFiber_apply_asIdeal, ← Algebra.smul_def, hsx] at this
  simpa using this

instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Algebra.IsUnramifiedAt R q] : Algebra.IsSeparable p.ResidueField q.ResidueField :=
  ((Algebra.isUnramifiedAt_iff_map_eq _ _ _).mp inferInstance).1

open Polynomial in
/-- If `A = K[X]/p` is unramified at some prime `Q`, then the minpoly of `X` at `κ(Q)`
only divides `p` once. -/
theorem Algebra.IsUnramifiedAt.not_minpoly_sq_dvd
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (Q : Ideal A) [Q.IsPrime] [Algebra.IsUnramifiedAt K Q]
    (x : A) (p : K[X])
    (hp₁ : Ideal.span {p} = RingHom.ker (aeval x).toRingHom)
    (hp₂ : Function.Surjective (aeval (R := K) x)) :
    ¬ minpoly K (algebraMap A Q.ResidueField x) ^ 2 ∣ p := by
  have : Algebra.FiniteType K A := .of_surjective _ hp₂
  have := Algebra.FormallyUnramified.finite_of_free K (Localization.AtPrime Q)
  have : IsField (Localization.AtPrime Q) :=
    have := IsArtinianRing.of_finite K (Localization.AtPrime Q)
    have := Algebra.FormallyUnramified.isReduced_of_field K (Localization.AtPrime Q)
    IsArtinianRing.isField_of_isReduced_of_isLocalRing _
  letI := this.toField
  set q := minpoly K (algebraMap A Q.ResidueField x)
  have : algebraMap A (Localization.AtPrime Q) (aeval x q) = 0 := by
    apply (algebraMap (Localization.AtPrime Q) Q.ResidueField).injective
    rw [← IsScalarTower.algebraMap_apply, ← aeval_algebraMap_apply, minpoly.aeval, map_zero]
  obtain ⟨⟨m, hm⟩, hm'⟩ := (IsLocalization.map_eq_zero_iff Q.primeCompl _ _).mp this
  obtain ⟨m, rfl⟩ := hp₂ m
  simp_rw [← map_mul, ← AlgHom.coe_toRingHom, ← AlgHom.toRingHom_eq_coe, ← RingHom.mem_ker,
    ← hp₁, Ideal.mem_span_singleton] at hm'
  rw [pow_two]
  rintro H
  have := (mul_dvd_mul_iff_right (minpoly.ne_zero (Algebra.IsIntegral.isIntegral _))).mp
    (H.trans hm')
  rw [minpoly.dvd_iff, aeval_algebraMap_apply, Q.algebraMap_residueField_eq_zero] at this
  exact hm this

attribute [local instance high] Algebra.TensorProduct.leftAlgebra IsScalarTower.right
  DivisionRing.instIsArtinianRing in
theorem Algebra.IsUnramifiedAt.residueField
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] (P : Ideal R) [P.IsPrime] (Q : Ideal S) [Q.IsPrime]
    [Q.LiesOver P] [Algebra.IsUnramifiedAt R Q]
    (Q' : Ideal (P.ResidueField ⊗[R] S)) [Q'.IsPrime]
    (hQ' : Q = Q'.comap Algebra.TensorProduct.includeRight.toRingHom) :
  IsUnramifiedAt P.ResidueField Q' := by
  let f₀₀ := Localization.localRingHom Q Q' _ hQ'
  let f₀ : Localization.AtPrime Q →ₐ[R] Localization.AtPrime Q' :=
    ⟨Localization.localRingHom Q Q' _ hQ', fun r ↦ by
      simp [Localization.localRingHom_to_map,
        IsScalarTower.algebraMap_apply R S (Localization.AtPrime _)]; rfl⟩
  have hf₀ : Function.Surjective f₀ := by
    subst hQ'
    apply P.surjectiveOnStalks_residueField.baseChange'
  let f : P.ResidueField ⊗[R] Localization.AtPrime Q →ₐ[P.ResidueField] Localization.AtPrime Q' :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) f₀ fun _ _ ↦ .all _ _
  have hf : Function.Surjective f := hf₀.forall.mpr fun x ↦ ⟨1 ⊗ₜ x, by simp [f]⟩
  exact .of_surjective _ hf

-- #min_imports
