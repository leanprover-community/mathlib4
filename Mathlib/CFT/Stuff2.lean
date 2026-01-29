module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Unramified.LocalRing


@[expose] public section

open TensorProduct

attribute [local instance] RingHom.ker_isPrime

attribute [ext high] Ideal.Quotient.algHom_ext

open scoped nonZeroDivisors

@[simp]
lemma Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul_one {A B : Type*} [CommRing A]
      [CommRing B] [Algebra A B] (I : Ideal A) (b : B) :
    (quotIdealMapEquivTensorQuot B I).symm (b ⊗ₜ[A] 1) = Ideal.Quotient.mk _ b :=
  (quotIdealMapEquivTensorQuot_symm_tmul ..).trans (by simp)

instance {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : S →ₐ[R] T) (I : Ideal T) (J : Ideal R) [I.LiesOver J] : (I.comap f).LiesOver J := by
  constructor; ext; simp [I.over_def J]

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
