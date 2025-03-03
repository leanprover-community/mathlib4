/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanyi He, Jingting Wang, Andrew Yang, Shouxin Zhang
-/
import Mathlib.RingTheory.Artinian.Noetherian
import Mathlib.RingTheory.Jacobson.Ring

/-!
# Artinian property relating to finite algebra over a field

In this file, we collect results about artinian properties relating to a ring `R` being a finite
algebra over a field `K`.
-/

section AlgebraOverField

variable {R : Type*} [CommRing R] (K : Type*) [Field K] [Algebra K R] [Algebra.FiniteType K R]

lemma isArtinian_of_isArtinian_of_mul_of_field (I J : Ideal R) [I.IsMaximal] [IsArtinian R J]
    (H : IsArtinian K (I * J : _)) : IsArtinian K J := by
  let IJ := Submodule.comap J.subtype (I * J)
  have : Module.IsTorsionBySet R (J ⧸ IJ) I := by
    intro x ⟨y, hy⟩
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.mkQ_surjective _ x
    rw [Subtype.coe_mk, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    show _ ∈ I * J
    simpa using Ideal.mul_mem_mul hy hx
  letI : Module (R ⧸ I) (J ⧸ IJ) := this.module
  letI := Ideal.Quotient.field I
  have h : Function.Surjective (algebraMap R (R ⧸ I)) := Ideal.Quotient.mk_surjective
  haveI : Algebra.FiniteType K (R ⧸ I) := (‹Algebra.FiniteType K R›).trans inferInstance
  haveI : Module.Finite K (R ⧸ I) := finite_of_finite_type_of_isJacobsonRing _ _
  have h1_out := (IsArtinianRing.tfae (R ⧸ I) (J ⧸ IJ)).out 2 0
  have h2_out := (IsArtinianRing.tfae K (J ⧸ IJ)).out 2 0
  have : IsArtinian R (J ⧸ IJ) ↔ IsArtinian K (J ⧸ IJ) := by
    rw [isArtinian_iff_tower_of_surjective (J ⧸ IJ) h, h1_out, h2_out]
    constructor
    · intro h; exact Module.Finite.trans (R ⧸ I) _
    · intro h; exact Module.Finite.of_restrictScalars_finite K (R ⧸ I) _
  haveI := this.mp inferInstance
  refine isArtinian_of_range_eq_ker
    ((Submodule.inclusion (Ideal.mul_le_left) : (I * J : _) →ₗ[R] J).restrictScalars K)
    (IJ.mkQ.restrictScalars K) ?_
  rw [LinearMap.ker_restrictScalars, Submodule.ker_mkQ, Submodule.range_restrictScalars,
    Submodule.range_inclusion]

lemma isArtinianRing_iff_isArtinian_of_field : IsArtinianRing R ↔ IsArtinian K R := by
  classical
  refine ⟨?_, isArtinian_of_tower K⟩
  intro H
  by_contra H'
  obtain ⟨s, hs, hs'⟩ :=
    IsArtinianRing.exists_multiset_ideal_is_maximal_and_prod_eq_bot (R := R)
  suffices ¬ IsArtinian K s.prod by
    rw [hs'] at this
    exact this (by infer_instance)
  clear hs'
  induction s using Multiset.induction_on with
  | empty =>
    rw [Multiset.prod_zero, Ideal.one_eq_top]
    rwa [← isArtinian_top_iff] at H'
  | cons a s h₁ =>
    intro h₃
    rw [Multiset.prod_cons] at h₃
    apply h₁ (fun I hI => hs I (Multiset.mem_cons_of_mem hI))
    have := hs a (Multiset.mem_cons_self a s)
    exact isArtinian_of_isArtinian_of_mul_of_field _ a s.prod h₃

lemma isArtinianRing_iff_finite_of_field : IsArtinianRing R ↔ Module.Finite K R :=
  (isArtinianRing_iff_isArtinian_of_field K).trans ((IsArtinianRing.tfae K R).out 2 0)

omit [Algebra K R] [Algebra.FiniteType K R] in
lemma isArtinianRing_iff_ringHomFinite_of_field (f : K →+* R) (hf : f.FiniteType) :
    IsArtinianRing R ↔ f.Finite := by
  algebraize [f]
  exact isArtinianRing_iff_finite_of_field K

lemma finite_iff_forall_prime_is_maximal_of_field :
    Module.Finite K R ↔ ∀ I : Ideal R, I.IsPrime → I.IsMaximal := by
  haveI := isNoetherianRing_of_fg ‹Algebra.FiniteType K R›.1
  haveI := isNoetherianRing_of_surjective (⊤ : Subalgebra K R) R
    Subalgebra.topEquiv.toRingEquiv.toRingHom Subalgebra.topEquiv.surjective
  rw [← isArtinianRing_iff_finite_of_field K,
    isArtinianRing_iff_isNoetherianRing_and_primes_maximal]
  exact and_iff_right inferInstance

end AlgebraOverField
