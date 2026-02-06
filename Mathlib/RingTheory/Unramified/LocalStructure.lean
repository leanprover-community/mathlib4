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
- `HasStandardEtaleSurjectionOn`: The predicate
  "there exists a standard etale algebra `A` over `R` that surjects onto `S[1/f]`".
- `Algebra.IsUnramified.exist_HasStandardEtaleSurjectionOn_of_exists_adjoin_singleton_eq_top`:
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
def HasStandardEtaleSurjectionOn (f : S) : Prop :=
  ∃ (P : StandardEtalePair R) (φ : P.Ring →ₐ[R] Localization.Away f), Function.Surjective φ

lemma HasStandardEtaleSurjectionOn.mk [Algebra.IsStandardEtale R A]
    {Sf : Type*} [CommRing Sf] [Algebra R Sf] [Algebra S Sf] [IsScalarTower R S Sf]
    {f : S} [IsLocalization.Away f Sf] (φ : A →ₐ[R] Sf) (H : Function.Surjective φ) :
    HasStandardEtaleSurjectionOn R f :=
  let P : StandardEtalePresentation R A := Nonempty.some inferInstance
  ⟨P.P, (((IsLocalization.algEquiv (.powers f) (Localization.Away f) Sf).restrictScalars R)
    |>.symm.toAlgHom).comp (φ.comp P.equivRing.symm.toAlgHom), by simpa⟩

lemma HasStandardEtaleSurjectionOn.of_dvd
    {f g : S} (H : HasStandardEtaleSurjectionOn R f) (h : f ∣ g) :
    HasStandardEtaleSurjectionOn R g := by
  obtain ⟨P, φ, hsurj⟩ := H
  obtain ⟨g, rfl⟩ := h
  obtain ⟨a, ha⟩ := hsurj (algebraMap _ _ g)
  have : IsLocalization.Away (f * g) (Localization.Away (φ a)) :=
    ha ▸ .mul' (Localization.Away f) _ _ _
  have : Algebra.IsStandardEtale R (Localization.Away a) := .of_isLocalizationAway a
  exact .mk _ (IsLocalization.Away.mapₐ_surjective_of_surjective
    (Aₚ := Localization.Away a) (Bₚ := Localization.Away (φ a)) a hsurj)

lemma HasStandardEtaleSurjectionOn.isStandardEtale
    {f : S} (H : HasStandardEtaleSurjectionOn R f) [Algebra.Etale R (Localization.Away f)] :
    Algebra.IsStandardEtale R (Localization.Away f) :=
  .of_surjective _ _ _ _ H.choose_spec.choose_spec

namespace Algebra.IsUnramifiedAt

private theorem exists_hasStandardEtaleSurjectionOn_of_exists_adjoin_singleton_eq_top_aux₁
    (P : Ideal R) [P.IsPrime] (x : S) (hx : adjoin R {x} = ⊤) :
    (RingHom.ker (aeval (R := R) x).toRingHom).map (mapRingHom (algebraMap R P.ResidueField)) =
      RingHom.ker (aeval (1 ⊗ₜ x : P.Fiber S)).toRingHom := by
  have hx' : Function.Surjective (aeval (R := R) x) :=
    (AlgHom.range_eq_top _).mp ((adjoin_singleton_eq_range_aeval R x).symm.trans hx)
  let I := RingHom.ker (aeval (R := R) x).toRingHom
  let e : P.Fiber S ≃ₐ[P.ResidueField]
      P.ResidueField[X] ⧸ I.map (mapRingHom (algebraMap _ P.ResidueField)) :=
    Polynomial.fiberEquivQuotient (aeval (R := R) x) hx' _
  rw [← RingHom.ker_comp_of_injective _ (f := e.toRingHom) e.injective]
  convert Ideal.mk_ker.symm
  ext a
  · dsimp [-TensorProduct.algebraMap_apply]
    rw [aeval_C, AlgEquiv.commutes]
    rfl
  · simpa [e] using Polynomial.fiberEquivQuotient_tmul _ hx' P 1 X

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
private theorem exists_hasStandardEtaleSurjectionOn_of_exists_adjoin_singleton_eq_top_aux₂
    {P : Ideal R} [P.IsPrime] {Q : Ideal S} [Q.IsPrime]
    [Q.LiesOver P] [Algebra.IsUnramifiedAt R Q] (x : S) (p : R[X])
    (hp₁ : Ideal.span {p.map (algebraMap R P.ResidueField)} =
      RingHom.ker (aeval ((1 : P.ResidueField) ⊗ₜ[R] x)).toRingHom)
    (hp₂ : Algebra.adjoin R {x} = ⊤) :
    ¬ minpoly P.ResidueField (algebraMap S Q.ResidueField x) ^ 2 ∣
      p.map (algebraMap R P.ResidueField) := by
  let Q' : Ideal (P.Fiber S) :=
    (PrimeSpectrum.primesOverOrderIsoFiber R S P ⟨Q, ‹_›, ‹_›⟩).asIdeal
  have : Q'.LiesOver Q := ⟨congr($((PrimeSpectrum.primesOverOrderIsoFiber R S P).symm_apply_apply
    ⟨Q, ‹_›, ‹_›⟩).1).symm⟩
  have : Q'.LiesOver P := .trans _ Q _
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

attribute [local simp] aeval_algebraMap_apply in
lemma exists_hasStandardEtaleSurjectionOn_of_exists_adjoin_singleton_eq_top
    [Module.Finite R S] (H : ∃ x : S, Algebra.adjoin R {x} = ⊤)
    (Q : Ideal S) [Q.IsPrime] [Algebra.IsUnramifiedAt R Q] :
    ∃ f ∉ Q, HasStandardEtaleSurjectionOn R f := by
  cases subsingleton_or_nontrivial S
  · cases Ideal.IsPrime.ne_top' (Subsingleton.elim Q ⊤)
  have := (algebraMap R S).domain_nontrivial
  -- Suppose `S = R[X]/I` is finite (as an `R`-module), and `R`-unramified at a prime `Q`,
  -- which lies over the prime `P` of `R`.
  -- We shall show that `S[1/f]` has a surjection from a standard etale algebra for some `f ∉ Q`.
  let P := Q.under R
  obtain ⟨x, hx⟩ := H
  have hRx : IsIntegral R x := Algebra.IsIntegral.isIntegral _
  let I := RingHom.ker (aeval (R := R) x).toRingHom
  have hx' : Function.Surjective (aeval (R := R) x) :=
    (AlgHom.range_eq_top _).mp ((adjoin_singleton_eq_range_aeval R x).symm.trans hx)
  -- It suffices to find some monic `q : R[X]` such that `q(x) = 0` and `q'(x) ∉ Q`.
  suffices ∃ q : R[X], q.Monic ∧ aeval x q = 0 ∧ aeval x q.derivative ∉ Q by
    -- Since if we have such a `q`, then `(R[X]/q)[1/q'] → S[1/q'(x)]` is the desired surjection.
    obtain ⟨q, hq, hqx, hq'x⟩ := this
    let P : StandardEtalePair R := ⟨q, hq, q.derivative, 1, 0, 1, by simp⟩
    have hP : P.HasMap (algebraMap _ (Localization.Away (aeval x q.derivative)) x) :=
      ⟨by simp_all [P], by simpa using IsLocalization.Away.algebraMap_isUnit _⟩
    let f : AdjoinRoot P.f →ₐ[R] S := AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) x hqx
    have : IsLocalization.Away (aeval x (derivative q)) (Localization.Away (f (.mk P.f P.g))) := by
      simp only [AdjoinRoot.liftAlgHom_mk, toRingHom_ofId, f, ← aeval_def, P]; infer_instance
    refine ⟨_, hq'x, .mk ((Localization.awayMapₐ f _).comp P.equivAwayAdjoinRoot.toAlgHom) ?_⟩
    simpa using IsLocalization.Away.mapₐ_surjective_of_surjective _
      (Ideal.Quotient.lift_surjective_of_surjective _ _ hx')
  -- Using the fact that `κ(P)[X]` is a PID, the image of `I` in `κ(P)[X]`
  -- (i.e. the kernel of `κ(P)[X] → κ(P) ⊗[R] S`) is generated by a single polynomial `p ∈ I`.
  obtain ⟨p, hpI, hp⟩ := Ideal.exists_mem_span_singleton_map_residueField_eq P I
  have hI' : I.map (mapRingHom (algebraMap R P.ResidueField)) =
      RingHom.ker (aeval (1 ⊗ₜ x : P.Fiber S)).toRingHom :=
    exists_hasStandardEtaleSurjectionOn_of_exists_adjoin_singleton_eq_top_aux₁ P x hx
  -- Let `x` denote the image of `X` in `S`,
  -- and let `m` be the minimal polynomial of `x` (viewed as an element of `κ(Q)`) over `κ(P)`.
  -- By unramified-ness we know that `m` divides `p` only once.
  -- (via `Algebra.IsUnramifiedAt.not_minpoly_sq_dvd`).
  let m := minpoly P.ResidueField (algebraMap S Q.ResidueField x)
  have hm : Prime m := minpoly.prime (Algebra.IsIntegral.isIntegral _)
  have hmp₁ : m ∣ p.map (algebraMap _ _) := by simp_all [m, I, minpoly.dvd_iff]
  have hmp₂ : ¬ m ^ 2 ∣ p.map (algebraMap _ _) :=
    exists_hasStandardEtaleSurjectionOn_of_exists_adjoin_singleton_eq_top_aux₂ x p (hp.trans hI') hx
  -- But the issue is that `p` is not necessarily monic.
  -- Let `q := M + p` for some monic `M ∈ I` with large enough degree (since `S` is `R`-finite).
  -- I claim that `q` satisfies the desired properties.
  let q := minpoly R x ^ (p.natDegree + 2) + p
  refine ⟨q, ?_, by simpa [q], ?_⟩
  · refine ((minpoly.monic hRx).pow _).add_of_left (degree_lt_degree ?_)
    grw [natDegree_pow' (by simp [minpoly.monic hRx]),
      ← Nat.le_mul_of_pos_right _ (minpoly.natDegree_pos hRx)]; lia
  -- To show that `q'(x) ∉ Q`, we first show that `m` still divides `q` only once in `κ(P)[X]`.
  have ⟨w, h₁, h₂⟩ : ∃ w, q.map (algebraMap R _) = p.map (algebraMap R _) * w ∧ ¬ m ∣ w := by
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp
      (hp.ge (Ideal.mem_map_of_mem _ (x := minpoly R x) (by simp [I])))
    refine ⟨1 + w * (minpoly R x).map (algebraMap R P.ResidueField) ^ (p.natDegree + 1), ?_, ?_⟩
    · simp_all [q]; grind
    · rw [dvd_add_left (dvd_mul_of_dvd_right (dvd_pow (by simp [m, minpoly.dvd_iff]) (by simp)) _),
        ← isUnit_iff_dvd_one]
      exact hm.not_unit
  have hm' : derivative m ≠ 0 :=
    have : Algebra.IsSeparable P.ResidueField Q.ResidueField :=
      ((Algebra.isUnramifiedAt_iff_map_eq _ _ _).mp inferInstance).1
    (separable_iff_derivative_ne_zero hm.irreducible).mp (Algebra.IsSeparable.isSeparable ..)
  suffices ¬m ∣ derivative (q.map (algebraMap R _)) by
    rwa [← Ideal.ker_algebraMap_residueField Q, RingHom.mem_ker, ← aeval_algebraMap_apply,
      ← aeval_map_algebraMap P.ResidueField, ← derivative_map, ← minpoly.dvd_iff]
  obtain ⟨c, hc⟩ := hmp₁
  simp_all [hm.dvd_mul, dvd_add_left, pow_two, mul_dvd_mul_iff_left, hm.ne_zero]

end Algebra.IsUnramifiedAt
