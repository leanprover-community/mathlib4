/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.ZariskisMainTheorem

/-!

# Local structure of unramified algebras

In this file, we will prove that if `S` is a finite type `R`-algebra unramified at `Q`, then
there exists `f ∉ Q` and a standard etale algebra `A` over `R` that surjects onto `S[1/f]`.
Geometrically, this says that unramified morphisms locally are closed subsets of etale covers.

As a corollary, we also obtain results about the local structure of etale and smooth algebras.

## Main definition and results
- `HasStandardEtaleSurjectionOn`: The predicate
  "there exists a standard etale algebra `A` over `R` that surjects onto `S[1/f]`".
- `Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn`:
  If `S` is a finite type `R`-algebra that is unramified at a prime `p`, then
  there exists a standard etale algebra over `R` that surjects onto `S[1/f]` for some `f ∉ p`.
- `Algebra.IsEtaleAt.exists_isStandardEtale`:
  If `S` is a finitely presented `R`-algebra that is etale at a prime `p`, then
  `S[1/f]` is standard etale for some `f ∉ p`.
- `Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial`:
  If `S` is a finitely presented `R`-algebra that is smooth at a prime `p`, then
  there exists some `f ∉ p` such that `S[1/f]` is `R`-isomorphic to a standard etale algebra
  over `R[x₁,...,xₙ]`.

-/

@[expose] public section

open Polynomial TensorProduct Algebra

open scoped nonZeroDivisors

variable {R A S : Type*} [CommRing R] [CommRing A] [CommRing S] [Algebra R S] [Algebra R A]

variable (R) in
/-- The predicate "there exists a standard etale algebra `A` over `R` that surjects onto `S[1/f]`".
We shall show if `S` is `R`-unramified at `Q` then there exists `f ∉ Q` satisfying it. -/
def HasStandardEtaleSurjectionOn (f : S) : Prop :=
  ∃ (P : StandardEtalePair R) (φ : P.Ring →ₐ[R] Localization.Away f), Function.Surjective φ

lemma HasStandardEtaleSurjectionOn.mk [IsStandardEtale R A]
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
  have : IsStandardEtale R (Localization.Away a) := .of_isLocalizationAway a
  exact .mk _ (IsLocalization.Away.mapₐ_surjective_of_surjective
    (Aₚ := Localization.Away a) (Bₚ := Localization.Away (φ a)) a hsurj)

lemma HasStandardEtaleSurjectionOn.isStandardEtale
    {f : S} (H : HasStandardEtaleSurjectionOn R f) [Etale R (Localization.Away f)] :
    IsStandardEtale R (Localization.Away f) :=
  .of_surjective _ H.choose_spec.choose_spec

namespace Algebra.IsUnramifiedAt

set_option backward.isDefEq.respectTransparency false in
private theorem exists_hasStandardEtaleSurjectionOn_of_exists_adjoin_singleton_eq_top_aux₁
    (P : Ideal R) [P.IsPrime] (x : S) (hx : R[x] = ⊤) :
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
    simp [← Ideal.Quotient.mk_algebraMap, I]
  · simpa [e] using Polynomial.fiberEquivQuotient_tmul _ hx' P 1 X

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
private theorem exists_hasStandardEtaleSurjectionOn_of_exists_adjoin_singleton_eq_top_aux₂
    {P : Ideal R} [P.IsPrime] {Q : Ideal S} [Q.IsPrime]
    [Q.LiesOver P] [IsUnramifiedAt R Q] (x : S) (p : R[X])
    [Algebra (Localization.AtPrime P) (Localization.AtPrime Q)]
    [Localization.AtPrime.IsLiesOverAlgebra P Q]
    (hp₁ : Ideal.span {p.map (algebraMap R P.ResidueField)} =
      RingHom.ker (aeval ((1 : P.ResidueField) ⊗ₜ[R] x)).toRingHom)
    (hp₂ : R[x] = ⊤) :
    ¬ minpoly P.ResidueField (algebraMap S Q.ResidueField x) ^ 2 ∣
      p.map (algebraMap R P.ResidueField) := by
  let Q' : Ideal (P.Fiber S) :=
    (PrimeSpectrum.primesOverOrderIsoFiber R S P ⟨Q, ‹_›, ‹_›⟩).asIdeal
  have : Q'.LiesOver Q := ⟨congr($((PrimeSpectrum.primesOverOrderIsoFiber R S P).symm_apply_apply
    ⟨Q, ‹_›, ‹_›⟩).1).symm⟩
  have : Q'.LiesOver P := .trans _ Q _
  let := Localization.AtPrime.algebraOfLiesOver Q Q'
  let := Localization.AtPrime.algebraOfLiesOver P Q'
  have : IsUnramifiedAt P.ResidueField Q' := .residueField P Q _ (Q'.over_def Q)
  have : Function.Surjective (aeval (R := P.ResidueField) ((1 : P.ResidueField) ⊗ₜ[R] x)) := by
    rw [← AlgHom.range_eq_top, ← adjoin_singleton_eq_range_aeval]
    simpa using TensorProduct.adjoin_one_tmul_image_eq_top (A := P.ResidueField) _ hp₂
  convert IsUnramifiedAt.not_minpoly_sq_dvd (A := P.Fiber S) Q' (1 ⊗ₜ x) _ hp₁ this
  rw [← minpoly.algHom_eq _
    (IsScalarTower.toAlgHom P.ResidueField Q.ResidueField Q'.ResidueField).injective]
  congr 1
  · apply algebra_ext; intros r; congr 1; ext x; simp [← IsScalarTower.algebraMap_apply]
  · simp [← TensorProduct.right_algebraMap_apply, ← IsScalarTower.algebraMap_apply]

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] aeval_algebraMap_apply in
-- Subsumed by `Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn`.
private lemma exists_hasStandardEtaleSurjectionOn_of_exists_adjoin_singleton_eq_top
    [Module.Finite R S] (H : ∃ x : S, R[x] = ⊤)
    (Q : Ideal S) [Q.IsPrime] [IsUnramifiedAt R Q] :
    ∃ f ∉ Q, HasStandardEtaleSurjectionOn R f := by
  cases subsingleton_or_nontrivial S
  · cases Ideal.IsPrime.ne_top' (Subsingleton.elim Q ⊤)
  have := (algebraMap R S).domain_nontrivial
  -- Suppose `S = R[X]/I` is finite (as an `R`-module), and `R`-unramified at a prime `Q`,
  -- which lies over the prime `P` of `R`.
  -- We shall show that `S[1/f]` has a surjection from a standard etale algebra for some `f ∉ Q`.
  let P := Q.under R
  let := Localization.AtPrime.algebraOfLiesOver P Q
  obtain ⟨x, hx⟩ := H
  have hRx : IsIntegral R x := IsIntegral.isIntegral _
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
  have hm : Prime m := minpoly.prime (IsIntegral.isIntegral _)
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
    · simp_all [q]
      #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
      (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this
      goal. It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in
      the new canonicalizer; a minimization would help. The original proof was:
      `simp_all [q]; grind` -/
      ring
    · rw [dvd_add_left (dvd_mul_of_dvd_right (dvd_pow (by simp [m, minpoly.dvd_iff]) (by simp)) _),
        ← isUnit_iff_dvd_one]
      exact hm.not_unit
  have hm' : derivative m ≠ 0 :=
    (separable_iff_derivative_ne_zero hm.irreducible).mp (IsSeparable.isSeparable ..)
  suffices ¬m ∣ derivative (q.map (algebraMap R _)) by
    rwa [← Ideal.ker_algebraMap_residueField Q, RingHom.mem_ker, ← aeval_algebraMap_apply,
      ← aeval_map_algebraMap P.ResidueField, ← derivative_map, ← minpoly.dvd_iff]
  obtain ⟨c, hc⟩ := hmp₁
  simp_all [hm.dvd_mul, dvd_add_left, pow_two, mul_dvd_mul_iff_left, hm.ne_zero]

lemma exists_notMem_forall_ne_mem_and_adjoin_eq_top
    (Q : Ideal S) [Q.IsPrime] [Module.Finite R S] [IsUnramifiedAt R Q]
    [Algebra (Localization.AtPrime (Q.under R)) (Localization.AtPrime Q)]
    [Localization.AtPrime.IsLiesOverAlgebra (Q.under R) Q] :
    ∃ t ∉ Q, (∀ Q' ∈ (Q.under R).primesOver S, Q' ≠ Q → t ∈ Q') ∧
      adjoin (Ideal.under R Q).ResidueField {algebraMap _ Q.ResidueField t} = ⊤ := by
  let p := Q.under R
  #adaptation_note /-- Needed after nightly-2023-02-23 -/
  have : p.IsPrime := Ideal.IsPrime.under R Q
  classical
  have : IsArtinianRing (p.Fiber S) := .of_finite p.ResidueField _
  let α := PrimeSpectrum.primesOverOrderIsoFiber R S p
  obtain ⟨x, hx0, hx⟩ : ∃ x : Q.ResidueField, x ≠ 0 ∧ p.ResidueField[x] = ⊤ := by
    obtain ⟨x, hx⟩ := Field.exists_primitive_element p.ResidueField Q.ResidueField
    rw [IntermediateField.adjoin_eq_top_iff] at hx
    by_cases hx0 : x = 0
    · exact ⟨1, by simp, by simpa [p, hx0] using hx⟩
    · exact ⟨x, hx0, hx⟩
  obtain ⟨x, rfl⟩ := Ideal.Fiber.lift_residueField_surjective p _ x
  set φ : p.Fiber S →ₐ[p.ResidueField] Q.ResidueField := TensorProduct.lift
      (Algebra.ofId _ _) (IsScalarTower.toAlgHom _ _ _) fun _ _ ↦ .all _ _
  obtain ⟨r, hrQ, hrid, hr⟩ :=
    IsArtinianRing.exists_not_mem_forall_mem_of_ne (α ⟨Q, ‹_›, ⟨rfl⟩⟩).asIdeal
  obtain ⟨s, hsQ, t, e⟩ := Ideal.Fiber.exists_smul_eq_one_tmul _ (r * x)
  have hrQ' : φ r ≠ 0 := by
    have : Ideal.ResidueField.mapₐ p Q (ofId R S) (Ideal.over_def Q p) =
      AlgHom.restrictScalars R (ofId p.ResidueField Q.ResidueField) := by ext
    rw [← AlgHom.restrictScalars_apply R, Algebra.TensorProduct.restrictScalars_lift]
    convert hrQ
    rw [← SetLike.mem_coe, PrimeSpectrum.coe_primesOverOrderIsoFiber_apply_asIdeal]
    simp [this]
  have hsQ' : algebraMap R Q.ResidueField s ≠ 0 := by
    simpa [IsScalarTower.algebraMap_apply R S Q.ResidueField]
  replace hrQ' : φ r = 1 := by
    simpa [hrQ', sub_eq_zero, @eq_comm _ _ (φ r)] using (hrid.map φ).one_sub_mul_self
  have e' : algebraMap _ _ s * φ x = algebraMap _ _ t := by
    simpa [φ, smul_def, mul_assoc, hrQ'] using congr(φ $e)
  refine ⟨t, ?_, ?_, ?_⟩
  · rw [← Ideal.algebraMap_residueField_eq_zero, ← e']
    simpa [hx0, IsScalarTower.algebraMap_apply R S Q.ResidueField]
  · rintro Q' ⟨_, _⟩ H
    let := Localization.AtPrime.algebraOfLiesOver p Q'
    have hsQ'' : algebraMap R Q'.ResidueField s ≠ 0 := by
      suffices s ∉ Q'.under _ by simpa [IsScalarTower.algebraMap_apply R S Q'.ResidueField]
      rwa [← Q'.over_def p]
    let φ' : p.Fiber S →ₐ[p.ResidueField] Q'.ResidueField := TensorProduct.lift
        (Algebra.ofId _ _) (IsScalarTower.toAlgHom _ _ _) fun _ _ ↦ .all _ _
    have H : φ' r = 0 := (hr (α ⟨Q', ⟨‹_›, ‹_›⟩⟩).asIdeal inferInstance (by
        rwa [ne_eq, ← PrimeSpectrum.ext_iff, EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq]) :)
    rw [← Ideal.algebraMap_residueField_eq_zero]
    trans φ' (1 ⊗ₜ t)
    · simp [φ']
    · simpa [smul_def, H] using congr(φ' $e).symm
  · have : φ x = (algebraMap _ p.ResidueField s)⁻¹ • algebraMap _ _ t := by
      simpa [smul_def, ← IsScalarTower.algebraMap_apply, eq_inv_mul_iff_mul_eq₀ hsQ']
    rw [← top_le_iff, ← hx, this]
    refine adjoin_singleton_le ?_
    exact Subalgebra.smul_mem _ (self_mem_adjoin_singleton _ _) _

attribute [-instance] Subalgebra.instSMulSubtypeMem
  Subalgebra.toAlgebra Subalgebra.isScalarTower_left in
/-- Let `S` be an finite `R`-algebra that is unramified at some prime `Q`. Then there exists some
`x : S` such that `Q` is the unique prime lying over `P := Q ∩ R⟨x⟩` and `κ(P) = κ(Q)`. -/
lemma exists_primesOver_under_adjoin_eq_singleton_and_residueField_bijective
    (Q : Ideal S) [Q.IsPrime] [Module.Finite R S] [Algebra.IsUnramifiedAt R Q] :
    ∃ x : S, (Q.under (R[x])).primesOver S = {Q} ∧
      letI := Localization.AtPrime.algebraOfLiesOver (Q.under R[x]) Q
      Function.Bijective (algebraMap (Q.under (R[x])).ResidueField
        Q.ResidueField) := by
  let := Localization.AtPrime.algebraOfLiesOver (Q.under R) Q
  obtain ⟨t, htQ, htQ', ht⟩ :=
    IsUnramifiedAt.exists_notMem_forall_ne_mem_and_adjoin_eq_top (R := R) Q
  let p := Q.under R
  let := Localization.AtPrime.algebraOfLiesOver p (Q.under R[t])
  let := Localization.AtPrime.algebraOfLiesOver (Q.under R[t]) Q
  classical
  refine ⟨t, ?_, RingHom.injective _, ?_⟩
  · refine Set.ext fun Q' ↦ ⟨fun ⟨_, _⟩ ↦ ?_, fun e ↦ by exact ⟨e ▸ inferInstance, ⟨e ▸ rfl⟩⟩⟩
    by_contra! H
    have : Q'.LiesOver p := .trans _ (Q.under (R[t])) _
    exact htQ (SetLike.le_def.mp (Q'.over_def (Q.under (R[t]))).ge
      (x := ⟨t, self_mem_adjoin_singleton _ _⟩) (htQ' Q' ⟨‹_›, ‹_›⟩ H))
  · change Function.Surjective (IsScalarTower.toAlgHom p.ResidueField _ _)
    rw [← AlgHom.range_eq_top, ← top_le_iff, ← ht]
    refine adjoin_singleton_le ?_
    use algebraMap (R[t]) _ ⟨t, self_mem_adjoin_singleton _ _⟩
    rw [AlgHom.toRingHom_eq_coe, IsScalarTower.coe_toAlgHom, ← IsScalarTower.algebraMap_apply]
    rfl

set_option backward.isDefEq.respectTransparency false in
-- Subsumed by `Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn`.
private lemma exists_hasStandardEtaleSurjectionOn_of_finite
    (Q : Ideal S) [Q.IsPrime] [Module.Finite R S] [IsUnramifiedAt R Q] :
    ∃ f ∉ Q, HasStandardEtaleSurjectionOn R f := by
  obtain ⟨x, hQ', hQ'Q⟩ :=
    exists_primesOver_under_adjoin_eq_singleton_and_residueField_bijective (R := R) Q
  let S' := R[x]
  let Q' := Q.under S'
  let := Localization.AtPrime.algebraOfLiesOver Q' Q
  have : Module.Finite S' S := .of_restrictScalars_finite R _ _
  have : IsUnramifiedAt S' Q := .of_restrictScalars R _
  have hφ : Function.Bijective (Localization.localRingHom Q' Q S'.val rfl) :=
    ⟨Localization.localRingHom_injective_of_primesOver_eq_singleton hQ',
      Localization.localRingHom_surjective_of_primesOver_eq_singleton hQ' hQ'Q.2⟩
  obtain ⟨r, hrQ', H⟩ := Localization.exists_awayMap_bijective_of_residueField_surjective hQ' hQ'Q.2
  have : Module.Finite R S' := finite_adjoin_simple_of_isIntegral (IsIntegral.isIntegral _)
  have : IsUnramifiedAt R Q' := .of_equiv <| .symm <| .ofBijective (IsScalarTower.toAlgHom _ _ _) hφ
  obtain ⟨f, hfQ', hf⟩ :=
    IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn_of_exists_adjoin_singleton_eq_top
    (R := R) (S := S') ⟨⟨x, self_mem_adjoin_singleton _ _⟩, Subalgebra.map_injective
      (f := S'.val) Subtype.val_injective (by simp [Subalgebra.range_val, S'])⟩ Q'
  obtain ⟨P, φ, hP⟩ := hf.of_dvd (g := f * r) (by simp)
  exact ⟨_, (inferInstance : Q'.IsPrime).mul_notMem hfQ' hrQ', .mk
    (f := IsScalarTower.toAlgHom R S' S (f * r))
    ((Localization.awayMapₐ (IsScalarTower.toAlgHom _ _ S) (f * r)).comp φ)
    (by exact (H _ (by simp)).surjective.comp hP)⟩

attribute [local instance high] Module.Free.of_divisionRing in
instance (priority := low)
    [EssFiniteType R S] [FormallyUnramified R S] : QuasiFinite R S where
  finite_fiber _ _ := FormallyUnramified.finite_of_free _ _

lemma exists_hasStandardEtaleSurjectionOn
    (Q : Ideal S) [Q.IsPrime] [FiniteType R S] [IsUnramifiedAt R Q] :
    ∃ f ∉ Q, HasStandardEtaleSurjectionOn R f := by
  wlog H : Unramified R S
  · obtain ⟨s, hsQ, hs⟩ := exists_formallyUnramified_of_isUnramifiedAt (R := R) Q
    have hQ : (Ideal.map (algebraMap S (Localization.Away s)) Q).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (.powers s) _ _ ‹_› (by simp [Set.disjoint_iff,
        Set.ext_iff, Submonoid.mem_powers_iff, mt (‹Q.IsPrime›.mem_of_pow_mem _) hsQ])
    have inst : Unramified R (Localization.Away s) := {}
    obtain ⟨f, hf, H⟩ := this (R := R)
      (Q.map (algebraMap _ (Localization.Away s))) inferInstance
    obtain ⟨f, t, rfl⟩ := IsLocalization.exists_mk'_eq (.powers s) f
    refine ⟨s * f, ?_, ?_⟩
    · simpa [IsLocalization.mk'_mem_map_algebraMap_iff, Submonoid.mem_powers_iff,
        Ideal.IsPrime.mul_mem_left_iff, hsQ, (mt (‹Q.IsPrime›.mem_of_pow_mem _) hsQ)] using hf
    obtain ⟨P, φ, hφ⟩ : HasStandardEtaleSurjectionOn R (algebraMap S (Localization.Away s) f) :=
      H.of_dvd ⟨algebraMap _ _ t.1, by simp⟩
    exact .mk _ hφ
  obtain ⟨S', hS', r, hrQ, hr⟩ := ZariskisMainProperty.of_finiteType (R := R) Q
    |>.exists_fg_and_exists_notMem_and_awayMap_bijective
  have : Module.Finite R S' := ⟨(Submodule.fg_top _).mpr hS'⟩
  have : FormallyUnramified R (Localization.Away r) :=
    .of_equiv (AlgEquiv.ofBijective (Localization.awayMapₐ S'.val r) hr :).symm
  have : IsUnramifiedAt R (Ideal.under (↥S') Q) := by
    rw [← basicOpen_subset_unramifiedLocus_iff] at this
    exact @this ⟨Q.under S', inferInstance⟩ hrQ
  obtain ⟨f, hfQ, hf⟩ :=
    IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn_of_finite (R := R) (Q.under S')
  let e : Localization.Away (r * f) ≃ₐ[R] Localization.Away (r.1 * f.1) :=
    .ofBijective (Localization.awayMapₐ S'.val (r * f))
      (Localization.awayMap_bijective_of_dvd _ (dvd_mul_right r f) hr)
  obtain ⟨P, φ, hφ⟩ := hf.of_dvd (g := r * f) (by simp)
  refine ⟨_, ‹Q.IsPrime›.mul_notMem hrQ hfQ,
    .mk (f := r.1 * f.1) (e.toAlgHom.comp φ) (e.surjective.comp hφ)⟩

end IsUnramifiedAt

@[stacks 00UE]
lemma IsEtaleAt.exists_isStandardEtale
    (Q : Ideal S) [Q.IsPrime] [FinitePresentation R S] [IsEtaleAt R Q] :
    ∃ f, f ∉ Q ∧ IsStandardEtale R (Localization.Away f) := by
  obtain ⟨f, hfQ, h⟩ := exists_etale_of_isEtaleAt (R := R) Q
  obtain ⟨g, hgQ, hg⟩ := IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn (R := R) Q
  have : Etale R (Localization.Away (f * g)) := by
    rw [← basicOpen_subset_etaleLocus_iff_etale] at h ⊢
    exact .trans (PrimeSpectrum.basicOpen_mul_le_left _ _) h
  exact ⟨f * g, ‹Q.IsPrime›.mul_notMem hfQ hgQ, (hg.of_dvd (by simp)).isStandardEtale⟩

/-- Given `S` a finitely presented `R`-algebra, and `p` a prime of `S`. If `S` is smooth over `R`
at `p`, then there exists `f ∉ p` such that `R → S[1/f]` factors through some `R[X₁,...,Xₙ]`,
and that `S[1/f]` is standard etale over `R[X₁,...,Xₙ]`. -/
theorem IsSmoothAt.exists_isStandardEtale_mvPolynomial
    {p : Ideal S} [p.IsPrime] [FinitePresentation R S] [IsSmoothAt R p] :
    ∃ f ∉ p, ∃ (n : ℕ) (_ : Algebra (MvPolynomial (Fin n) R) (Localization.Away f)),
      IsScalarTower R (MvPolynomial (Fin n) R) (Localization.Away f) ∧
      IsStandardEtale (MvPolynomial (Fin n) R) (Localization.Away f) := by
  classical
  obtain ⟨f, hfp, H⟩ := IsSmoothAt.exists_notMem_isStandardSmooth R p
  obtain ⟨n, φ, hgC, hg⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial
    (f := algebraMap R (Localization.Away f)) (by simpa [RingHom.isStandardSmooth_algebraMap])
  algebraize [φ]
  have := IsScalarTower.of_algebraMap_eq' hgC.symm
  have : (Ideal.map (algebraMap S (Localization.Away f)) p).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers f) _ _ ‹_›
      ((Ideal.disjoint_powers_iff_notMem _ (Ideal.IsPrime.isRadical ‹_›)).mpr hfp)
  obtain ⟨g₀, hg, H⟩ := IsEtaleAt.exists_isStandardEtale (R := (MvPolynomial (Fin n) R))
    (S := (Localization.Away f)) (p.map (algebraMap _ _))
  obtain ⟨g, ⟨_, m, rfl⟩, hg₀⟩ := IsLocalization.exists_mk'_eq (.powers f) g₀
  replace hg : g ∉ p := by simpa [Submonoid.mem_powers_iff, Ideal.IsPrime.mul_mem_iff_mem_or_mem,
    IsLocalization.mk'_mem_map_algebraMap_iff, mt (‹p.IsPrime›.mem_of_pow_mem _) hfp,
    ← hg₀] using hg
  have : IsLocalization.Away (f * g) (Localization.Away g₀) := by
    suffices IsLocalization.Away (algebraMap _ (Localization.Away f) g) (Localization.Away g₀) from
      .mul' (Localization.Away f) _ _ _
    refine IsLocalization.Away.of_associated (r := g₀)
      ⟨(IsLocalization.Away.algebraMap_pow_isUnit f m).unit, ?_⟩
    simp only [← hg₀, IsUnit.unit_spec, ← map_pow, mul_comm, IsLocalization.mk'_spec'_mk]
  let e : Localization.Away g₀ ≃ₐ[S] Localization.Away (f * g) :=
    IsLocalization.algEquiv (.powers (f * g)) _ _
  let : Algebra (MvPolynomial (Fin n) R) (Localization.Away (f * g)) :=
    (e.toRingHom.comp (algebraMap (MvPolynomial (Fin n) R) _)).toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin n) R) (Localization.Away (f * g)) := by
    refine .of_algebraMap_eq' ?_
    simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
    exact (e.toAlgHom.comp_algebraMap_of_tower (R := R)).symm
  let e' : Localization.Away g₀ ≃ₐ[MvPolynomial (Fin n) R] Localization.Away (f * g) :=
    { __ := e, commutes' r := rfl }
  exact ⟨f * g, ‹p.IsPrime›.mul_notMem ‹_› ‹_›, n, ‹_›, ‹_›, .of_equiv e'⟩

end Algebra
