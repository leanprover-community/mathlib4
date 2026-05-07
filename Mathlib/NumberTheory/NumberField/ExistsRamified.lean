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
  have := CharZero.of_module 𝒪 K
  have := NumberField.abs_discr_gt_two H
  obtain ⟨q, hq, hqK⟩ := Int.exists_prime_and_dvd (n := discr K) (by zify; linarith)
  have := (not_dvd_discr_iff_forall_mem (𝒪 := 𝒪) hq).not_right.mp hqK
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
  have := CharZero.of_module 𝒪 K
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
    ← Ideal.ramificationIdxIn_eq_ramificationIdx _ _ ℚ K, ← this, ← hp,
    Ideal.ramificationIdxIn_eq_ramificationIdx _ P ℚ K,
    ← Algebra.isUnramifiedAt_iff_of_isDedekindDomain hP]

open IsGaloisGroup NumberField -- probably should become a namespace

theorem NumberField.supr_inertia_eq_top (K : Type*) [Field K] [NumberField K]
    (G : Type*) [Group G] [MulSemiringAction G K] [IsGaloisGroup G ℚ K] :
    ⨆ m : MaximalSpectrum (𝓞 K), m.asIdeal.toAddSubgroup.inertia G = ⊤ := by
  have : Finite G := IsGaloisGroup.finite G ℚ K
  set H : Subgroup G := ⨆ m : MaximalSpectrum (𝓞 K), m.asIdeal.toAddSubgroup.inertia G
  set F : IntermediateField ℚ K := FixedPoints.intermediateField H
  suffices Module.finrank ℚ F ≤ 1 by
    rw [eq_top_iff, ← fixingSubgroup_fixedPoints G ℚ K H, ← le_fixedPoints_iff_le_fixingSubgroup,
      fixedPoints_top, le_bot_iff, ← IntermediateField.finrank_eq_one_iff]
    exact le_antisymm this Module.finrank_pos
  suffices h : ∀ (m : Ideal (𝓞 F)) (hm : m.IsMaximal), Algebra.IsUnramifiedAt ℤ m by
    contrapose! h
    obtain ⟨p, h1, h2, h3⟩ := NumberField.exists_not_isUramifiedAt_int (𝒪 := 𝓞 F) h
    exact ⟨p, h1, h3⟩
  intro m _
  have hm2 := Ideal.IsMaximal.ne_bot_of_isIntegral_int m
  rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain hm2]
  obtain ⟨m, hm, ⟨rfl⟩⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) m
  rw [Ideal.under_under]
  have hm1 := Ideal.IsMaximal.ne_bot_of_isIntegral_int (m.under ℤ)
  have h : m.toAddSubgroup.inertia G ≤ H :=
    le_iSup (fun m : MaximalSpectrum (𝓞 K) ↦ m.asIdeal.toAddSubgroup.inertia G) ⟨m, hm⟩
  replace h : Nat.card (m.toAddSubgroup.inertia H) = Nat.card (m.toAddSubgroup.inertia G) := by
    rw [← Subgroup.map_subgroupOf_eq_of_le h, Subgroup.card_subtype,
      AddSubgroup.subgroupOf_inertia]
  let := Ideal.Quotient.field m
  let := Ideal.Quotient.field (m.under (𝓞 F))
  let := Ideal.Quotient.field (m.under ℤ)
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := H) (m.under (𝓞 F)) hm2 m,
    Ideal.card_inertia_eq_ramificationIdxIn (G := G) (m.under ℤ) hm1 m,
    Ideal.ramificationIdxIn_eq_ramificationIdx (m.under (𝓞 F)) m H,
    Ideal.ramificationIdxIn_eq_ramificationIdx (m.under ℤ) m G] at h
  have key := Ideal.ramificationIdx_algebra_tower (Ideal.map_ne_bot_of_ne_bot hm2)
    (Ideal.map_ne_bot_of_ne_bot hm1) Ideal.map_comap_le
  rwa [h, right_eq_mul₀ (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver m hm1)] at key
