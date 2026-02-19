/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Every number field has a ramified prime over `ℚ`
...except `ℚ` itself.

This is a trivial corollary of `NumberField.not_dvd_discr_iff_forall_pow_mem` and
`NumberField.abs_discr_gt_two` but is placed in a separate file to avoid large imports.

-/

@[expose] public section

variable {K 𝒪 : Type*} [Field K] [NumberField K] [CommRing 𝒪] [Algebra 𝒪 K]
variable [IsIntegralClosure 𝒪 ℤ K]

/-- If `K` is a number field with positive rank, then there exists some maximal ideal of `𝓞 K`
that is ramified over `ℤ`. -/
lemma NumberField.exists_not_isUramifiedAt_int (H : 1 < Module.finrank ℚ K) :
    ∃ (P : Ideal 𝒪) (_ : P.IsMaximal), P ≠ ⊥ ∧ ¬ Algebra.IsUnramifiedAt ℤ P := by
  have := (IsIntegralClosure.algebraMap_injective 𝒪 ℤ K).isDomain
  have := IsIntegralClosure.isDedekindDomain ℤ ℚ K 𝒪
  have := CharZero.of_module (R := 𝒪) K
  have := NumberField.abs_discr_gt_two H
  obtain ⟨q, hq, hqK⟩ := Int.exists_prime_and_dvd (n := discr K) (by zify; linarith)
  have := (not_dvd_discr_iff_forall_mem K 𝒪 hq).not_right.mp hqK
  push_neg at this
  obtain ⟨P, hP, h, H⟩ := this
  exact ⟨P, hP.isMaximal (by aesop), by aesop, H⟩

attribute [local simp] Ideal.span_le in
/-- If `K` is a number field with positive rank such that `K/ℚ` is galois, then there exists
some rational prime `p : ℤ` such that every prime of `K` over `P` is unramified. -/
lemma NumberField.exists_not_isUramifiedAt_int_of_isGalois [IsGalois ℚ K]
    (H : 1 < Module.finrank ℚ K) :
    ∃ p : ℕ, p.Prime ∧ ∀ (P : Ideal 𝒪) (_ : P.IsPrime), ↑p ∈ P → ¬ Algebra.IsUnramifiedAt ℤ P := by
  have := (IsIntegralClosure.algebraMap_injective 𝒪 ℤ K).isDomain
  have := IsIntegralClosure.isDedekindDomain ℤ ℚ K 𝒪
  have := IsIntegralClosure.isFractionRing_of_finite_extension ℤ ℚ K 𝒪
  have := IsIntegralClosure.finite ℤ ℚ K 𝒪
  have := CharZero.of_module (R := 𝒪) K
  have : MulSemiringAction Gal(K/ℚ) 𝒪 := sorry
  have : SMulDistribClass Gal(K/ℚ) 𝒪 K := sorry
  have := IsGaloisGroup.of_isFractionRing Gal(K/ℚ) ℤ 𝒪 ℚ K
  obtain ⟨P, _, hP, hP'⟩ := NumberField.exists_not_isUramifiedAt_int (𝒪 := 𝒪) H
  obtain ⟨p, hp : _ = Ideal.span _⟩ := IsPrincipalIdealRing.principal (P.under ℤ)
  have hp0 : p ≠ 0 := fun hp0 ↦ hP (Ideal.eq_bot_of_comap_eq_bot (hp.trans (by aesop)))
  have : Prime p := by rw [← Ideal.span_singleton_prime hp0, ← hp]; infer_instance
  refine ⟨p.natAbs, Int.prime_iff_natAbs_prime.mp this, fun Q _ hQ ↦ ?_⟩
  replace hQ : (p : 𝒪) ∈ Q := Q.mem_of_dvd
    (map_dvd (algebraMap _ _) p.associated_natAbs.symm.dvd) (by simpa using hQ)
  have : .span {p} = Ideal.under ℤ Q := (Ideal.IsPrime.isMaximal (hp ▸ inferInstance) (by simpa))
    |>.eq_of_le Ideal.IsPrime.ne_top' (by simpa)
  rwa [Algebra.isUnramifiedAt_iff_of_isDedekindDomain (by aesop),
    ← Ideal.ramificationIdxIn_eq_ramificationIdx _ _ Gal(K/ℚ), ← this, ← hp,
    Ideal.ramificationIdxIn_eq_ramificationIdx _ P Gal(K/ℚ),
    ← Algebra.isUnramifiedAt_iff_of_isDedekindDomain hP]
