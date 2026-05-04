/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!

# Results for the rank of a finite flat algebra

In this file we study a finite, flat `R`-algebra `S` and relate injectivity and
bijectivity of `R → S` with the rank of `S` over `R`.

## Main results

- `PrimeSpectrum.comap_surjective_iff_injective_of_finite`: `Spec S → Spec R` is surjective
  if and only if `R → S` is injective.
- `Module.Flat.tfae_algebraMap_surjective`: `R → S` is surjective iff `S ⊗[R] S → S` is an
  isomorphism iff the rank of `S` is at most `1` at all primes.
- `Module.algebraMap_bijective_iff_rankAtStalk`: `S` is of constant `R`-rank `1` if and only if
  `S` is isomorphic to `R`.

-/

public section

universe u

open TensorProduct

attribute [local instance] Module.free_of_flat_of_isLocalRing

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S] [Module.Finite R S]

set_option backward.isDefEq.respectTransparency false in
lemma PrimeSpectrum.rankAtStalk_pos_iff_mem_range_comap (p : PrimeSpectrum R) :
    0 < Module.rankAtStalk (R := R) S p ↔ p ∈ Set.range (PrimeSpectrum.comap (algebraMap R S)) := by
  rw [Module.rankAtStalk_eq, Module.finrank_pos_iff, p.nontrivial_iff_mem_rangeComap]

/-- The rank is positive at all stalks if and only if the induced map on prime spectra is
surjective. -/
lemma PrimeSpectrum.rankAtStalk_pos_iff_comap_surjective :
    (∀ p, 0 < Module.rankAtStalk (R := R) S p) ↔
      Function.Surjective (PrimeSpectrum.comap <| algebraMap R S) := by
  simp_rw [rankAtStalk_pos_iff_mem_range_comap, ← Set.range_eq_univ,
    Set.eq_univ_iff_forall]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
lemma PrimeSpectrum.comap_surjective_iff_injective_of_finite :
    (PrimeSpectrum.comap (algebraMap R S)).Surjective ↔ Function.Injective (algebraMap R S) := by
  refine ⟨fun h ↦ ?_, fun h ↦
    have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr h
    Algebra.IsIntegral.comap_surjective _ _⟩
  apply injective_of_isLocalization_isMaximal (fun P _ ↦ Localization.AtPrime P)
    (fun P _ ↦ Localization.AtPrime P ⊗[R] S)
  intro p _
  rw [← faithfulSMul_iff_algebraMap_injective]
  obtain ⟨⟨Q, _⟩, hQ⟩ := h ⟨p, inferInstance⟩
  have : Q.LiesOver p := ⟨congr($(hQ).asIdeal).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p Q
  have : Nontrivial (Localization.AtPrime p ⊗[R] S) := by
    let f : Localization.AtPrime p ⊗[R] S →ₐ[R] Localization.AtPrime Q :=
      Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R _ _)
        (IsScalarTower.toAlgHom R S _) (fun _ _ ↦ Commute.all _ _)
    exact f.domain_nontrivial
  infer_instance

lemma Module.rankAtStalk_pos_iff_algebraMap_injective :
    (∀ p, 0 < Module.rankAtStalk (R := R) S p) ↔ Function.Injective (algebraMap R S) := by
  rw [← PrimeSpectrum.comap_surjective_iff_injective_of_finite,
    PrimeSpectrum.rankAtStalk_pos_iff_comap_surjective]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
lemma Module.algebraMap_surjective_of_rankAtStalk_le_one (h : ∀ p, rankAtStalk (R := R) S p ≤ 1) :
    Function.Surjective (algebraMap R S) := by
  apply surjective_of_isLocalization_isMaximal (fun P _ ↦ Localization.AtPrime P)
    (fun P _ ↦ Localization.AtPrime P ⊗[R] S)
  intro p _
  by_cases hr : Module.rankAtStalk S ⟨p, inferInstance⟩ = 0
  · have : Subsingleton (Localization.AtPrime p ⊗[R] S) := by
      apply Module.subsingleton_of_rank_zero (R := Localization.AtPrime p)
      simp [← finrank_eq_rank, ← rankAtStalk_eq_finrank_tensorProduct ⟨p, inferInstance⟩, hr]
    exact Function.surjective_to_subsingleton _
  · refine (Free.bijective_algebraMap_of_finrank_eq_one ?_).2
    grind [rankAtStalk_eq_finrank_tensorProduct ⟨p, inferInstance⟩]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
variable (R) (S) in
/-- If `S` is a finite and flat `R`-algebra, `R → S` is surjective iff `S ⊗[R] S → S` is an
isomorphism iff the rank of `S` is at most `1` at all primes. -/
lemma Module.Flat.tfae_algebraMap_surjective :
    [Function.Surjective (algebraMap R S),
      Function.Bijective (LinearMap.mul' R S),
      (∀ p, Module.rankAtStalk (R := R) S p ≤ 1)].TFAE := by
  tfae_have 1 → 2 := LinearMap.mul'_bijective_of_surjective _ _
  tfae_have 2 → 3 := fun H p ↦ by
    have h : rankAtStalk (S ⊗[R] S) p = rankAtStalk S p ^ 2 := by
      simp [rankAtStalk_tensorProduct, sq]
    by_contra! hc
    apply Nat.succ_succ_ne_one 0
    rw [← Nat.pow_eq_self_iff hc, ← h, Module.rankAtStalk_eq_of_equiv
      (AlgEquiv.ofBijective (Algebra.TensorProduct.lmul' R (S := S)) H).toLinearEquiv]
  tfae_have 3 → 1 := Module.algebraMap_surjective_of_rankAtStalk_le_one
  tfae_finish

lemma Module.rankAtStalk_le_one_iff_surjective :
    (∀ p, Module.rankAtStalk (R := R) S p ≤ 1) ↔ Function.Surjective (algebraMap R S) :=
  (Module.Flat.tfae_algebraMap_surjective R S).out 2 0

/-- If `S` is a finite, flat `R`-algebra, `S` is of constant rank `1` if and only if
`S` is isomorphic to `R`. -/
lemma Module.algebraMap_bijective_iff_rankAtStalk :
    Module.rankAtStalk (R := R) S = 1 ↔ Function.Bijective (algebraMap R S) := by
  rw [Function.Bijective, ← rankAtStalk_pos_iff_algebraMap_injective,
    ← rankAtStalk_le_one_iff_surjective]
  refine ⟨fun h ↦ by simp [h], fun h ↦ ?_⟩
  ext p
  rw [Pi.one_apply]
  grind

alias ⟨Module.algebraMap_bijective_of_rankAtStalk, _⟩ := Module.algebraMap_bijective_iff_rankAtStalk
