/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.RingTheory.LocalRing.ResidueField.Polynomial
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.Tactic.DepRewrite

/-!

# Local structure of unramified algebras

In this file, we will prove that if `S` is a finite type `R`-algebra unramified at `Q`, then
there exists `f ∉ Q` and a standard etale algebra `A` over `R` that surjects onto `S[1/f]`.
Geometrically, this says that unramified morphisms locally are closed subsets of etale covers.

## Main definition and results
- `HasStandardEtaleSurjectionAt`: The predicate
  "there exists a standard etale algebra `A` over `R` that surjects onto `S[1/f]`".
- `Algebra.IsUnramified.exist_hasStandardEtaleSurjectionAt_of_exists_adjoin_singleton_eq_top`:
  The claim is true when `S` has the form `R[X]/I` and is finite over `R`.

## TODO (@erdOne)
- Extend the result to arbitrary finite algebras.
- Extend the result to arbitrary finite-type algebras (needs Zariski's main theorem).

-/

@[expose] public section

open Polynomial TensorProduct

open scoped nonZeroDivisors

variable {R A S : Type*} [CommRing R] [CommRing A] [CommRing S] [Algebra R S] [Algebra R A]

variable (R) in
/-- The predicate "there exists a standard etale algebra `A` over `R` that surjects onto `S[1/f]`".
We shall show if `S` is `R`-unramified at `Q` then there exists `f ∉ Q` satisfying it. -/
def HasStandardEtaleSurjectionAt (f : S) : Prop :=
  ∃ (P : StandardEtalePair R) (φ : P.Ring →ₐ[R] Localization.Away f), Function.Surjective φ

lemma HasStandardEtaleSurjectionAt.mk [Algebra.IsStandardEtale R A]
    {Sf : Type*} [CommRing Sf] [Algebra R Sf] [Algebra S Sf] [IsScalarTower R S Sf]
    {f : S} [IsLocalization.Away f Sf] (φ : A →ₐ[R] Sf) (H : Function.Surjective φ) :
    HasStandardEtaleSurjectionAt R f :=
  let P : StandardEtalePresentation R A := Nonempty.some inferInstance
  ⟨P.P, (((IsLocalization.algEquiv (.powers f) (Localization.Away f) Sf).restrictScalars R)
    |>.symm.toAlgHom).comp (φ.comp P.equivRing.symm.toAlgHom), by simpa⟩

lemma HasStandardEtaleSurjectionAt.of_dvd
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
    {f : S} (H : HasStandardEtaleSurjectionAt R f) [Algebra.Etale R (Localization.Away f)] :
    Algebra.IsStandardEtale R (Localization.Away f) :=
  .of_surjective _ _ _ _ H.choose_spec.choose_spec

namespace Algebra.IsUnramifiedAt

theorem exist_hasStandardEtaleSurjectionAt_of_exists_adjoin_singleton_eq_top_aux₁
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

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem exist_hasStandardEtaleSurjectionAt_of_exists_adjoin_singleton_eq_top_aux₂
    [Algebra.EssFiniteType R S] (P : Ideal R) [P.IsPrime] (Q : Ideal S) [Q.IsPrime]
    [Q.LiesOver P] [Algebra.IsUnramifiedAt R Q] (x : S) (p : R[X])
    (hp₁ : Ideal.span {p.map (algebraMap R P.ResidueField)} =
      RingHom.ker (aeval ((1 : P.ResidueField) ⊗ₜ[R] x)).toRingHom)
    (hp₂ : Algebra.adjoin R {x} = ⊤) :
    ¬ minpoly P.ResidueField (algebraMap S Q.ResidueField x) ^ 2 ∣
      p.map (algebraMap R P.ResidueField) := by
  let Q' : Ideal (P.ResidueField ⊗[R] S) :=
    (PrimeSpectrum.primesOverOrderIsoFiber R S P ⟨Q, ‹_›, ‹_›⟩).asIdeal
  have : Q'.LiesOver Q := ⟨congr($((PrimeSpectrum.primesOverOrderIsoFiber R S P).symm_apply_apply
    ⟨Q, ‹_›, ‹_›⟩).1).symm⟩
  have : Q'.LiesOver P := .trans _ Q _
  have : Q'.IsPrime := inferInstance
  clear_value Q'
  have : IsUnramifiedAt P.ResidueField Q' := .residueField P Q _ (Q'.over_def Q)
  have : Function.Surjective (aeval (R := P.ResidueField) ((1 : P.ResidueField) ⊗ₜ[R] x)) := by
    rw [← AlgHom.range_eq_top, ← adjoin_singleton_eq_range_aeval]
    simpa using Algebra.TensorProduct.adjoin_one_tmul_image_eq_top (A := P.ResidueField) _ hp₂
  convert Algebra.IsUnramifiedAt.not_minpoly_sq_dvd (A := P.Fiber S) Q' (1 ⊗ₜ x) _ hp₁ this
  rw [← minpoly.algHom_eq _
    (IsScalarTower.toAlgHom P.ResidueField Q.ResidueField Q'.ResidueField).injective]
  congr 1
  · apply Algebra.algebra_ext; intros r; congr 1; ext x; simp [← IsScalarTower.algebraMap_apply]
  · simp [← Algebra.TensorProduct.right_algebraMap_apply, ← IsScalarTower.algebraMap_apply]

lemma exist_hasStandardEtaleSurjectionAt_of_exists_adjoin_singleton_eq_top
    [Module.Finite R S] (H : ∃ x : S, Algebra.adjoin R {x} = ⊤)
    (Q : Ideal S) [Q.IsPrime] [Algebra.IsUnramifiedAt R Q] :
    ∃ f ∉ Q, HasStandardEtaleSurjectionAt R f := by
  cases subsingleton_or_nontrivial S
  · cases Ideal.IsPrime.ne_top' (Subsingleton.elim Q ⊤)
  have := (algebraMap R S).domain_nontrivial
  let P := Q.under R
  obtain ⟨x, hx⟩ := H
  let I := RingHom.ker (aeval (R := R) x).toRingHom
  have hx' : Function.Surjective (aeval (R := R) x) :=
    (AlgHom.range_eq_top _).mp ((adjoin_singleton_eq_range_aeval R x).symm.trans hx)
  obtain ⟨p, hpI, hp⟩ := Ideal.exists_mem_span_singleton_map_residueField_eq P I
  have hI' : I.map (mapRingHom (algebraMap R P.ResidueField)) =
      RingHom.ker (aeval (1 ⊗ₜ x : P.ResidueField ⊗[R] S)).toRingHom :=
    exist_hasStandardEtaleSurjectionAt_of_exists_adjoin_singleton_eq_top_aux₁ P x hx
  have hmp₁ : minpoly P.ResidueField (algebraMap S Q.ResidueField x) ∣ p.map (algebraMap _ _) := by
    rw [minpoly.dvd_iff, aeval_map_algebraMap, aeval_algebraMap_apply,
      show aeval x p = 0 from RingHom.mem_ker.mp hpI, map_zero]
  have hmp₂ :
      ¬ minpoly P.ResidueField (algebraMap S Q.ResidueField x) ^ 2 ∣ p.map (algebraMap _ _) :=
    exist_hasStandardEtaleSurjectionAt_of_exists_adjoin_singleton_eq_top_aux₂
      P Q x p (hp.trans hI') hx
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
    · rw [aeval_algebraMap_apply, show aeval x P.f = 0 by simpa [P, q], map_zero]
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

end Algebra.IsUnramifiedAt
