/-
Copyright (c) 2024 James Sundstrom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Sundstrom
-/
import Mathlib.RingTheory.FractionalIdeal.Extended
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Localization of a fractional ideal at a prime

This file defines the localization of a fractional ideal at a prime ideal.

## Main definition

* `FractionalIdeal.localizedAtPrime`: The localization of a fractional ideal at a prime ideal.

## Main results

* `FractionalIdeal.coe_localizedAtPrime`: The localization of `I` is `Submodule.span Aₚ I`.
* `FractionalIdeal.localizedAtPrime_add`: Localizing commutes with addition.
* `FractionalIdeal.localizedAtPrime_mul`: Localizing commutes with multiplication.
* `FractionalIdeal.localizedAtPrime_div`: Localizing commutes with division for finitely-generated
    denominator.
* `FractionalIdeal.localizedAtPrime_inv`: Localizing commutes with inverses for finitely-generated
    `I`.
* `FractionalIdeal.not_le_of_localizedAtPrime_eq_one`: If `I.localizedAtPrime P = 1`,
    then `¬ I ≤ P`.

## Tags

fractional ideal, fractional ideals, localization
-/

open IsLocalization Localization Algebra FractionalIdeal Submodule nonZeroDivisors Finset Module

variable {A : Type*} [CommRing A] [IsDomain A]

private lemma hf (P : Ideal A) [P.IsPrime] {Aₚ : Type*} [CommRing Aₚ] [Algebra A Aₚ]
    [h : IsLocalization P.primeCompl Aₚ] : A⁰ ≤ Submonoid.comap (algebraMap A Aₚ) Aₚ⁰ :=
  have := h.noZeroDivisors_of_le_nonZeroDivisors P.primeCompl_le_nonZeroDivisors
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ <|
    IsLocalization.injective Aₚ P.primeCompl_le_nonZeroDivisors

private lemma isFractionRing_Aₚ_K (P : Ideal A) [P.IsPrime] (Aₚ : Type*) [CommRing Aₚ]
    [Algebra A Aₚ] [IsLocalization P.primeCompl Aₚ] (K : Type*) [CommRing K] [Algebra A K]
    [Algebra Aₚ K] [IsFractionRing A K] [IsScalarTower A Aₚ K] : IsFractionRing Aₚ K :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl Aₚ K

variable (P : Ideal A) [P.IsPrime]
variable (Aₚ : Type*) [CommRing Aₚ] [Algebra A Aₚ] [IsLocalization P.primeCompl Aₚ]
variable {K : Type*} [Field K] [Algebra A K] [Algebra Aₚ K] [IsFractionRing A K]
variable [IsScalarTower A Aₚ K]
variable (I : FractionalIdeal A⁰ K) (J : FractionalIdeal A⁰ K)

instance : NoZeroSMulDivisors A K :=
  have : NoZeroDivisors K := noZeroDivisors_of_le_nonZeroDivisors A fun _ h ↦ h
  IsFractionRing.instNoZeroSMulDivisorsOfNoZeroDivisors

namespace FractionalIdeal

/-- The localization of a fractional ideal `I` of a domain `A`, at a prime ideal `P` of `A`.-/
abbrev localizedAtPrime : FractionalIdeal Aₚ⁰ K :=
  have := isFractionRing_Aₚ_K P Aₚ K
  I.extended K (hf P)

theorem coe_localizedAtPrime : (I.localizedAtPrime P Aₚ).coeToSubmodule = Submodule.span Aₚ I := by
  have := isFractionRing_Aₚ_K P Aₚ K
  simp [map_unique (hf P) (RingHom.id K) (fun a ↦ IsScalarTower.algebraMap_apply A Aₚ K a)]

theorem mem_localizedAtPrime_iff (x : K) :
    x ∈ I.localizedAtPrime P Aₚ ↔ x ∈ Submodule.span Aₚ I := by
  rw [← I.coe_localizedAtPrime P Aₚ, mem_coe]

theorem self_subset_localizedAtPrime : (I : Set K) ⊆ I.localizedAtPrime P Aₚ := by
  intro x hx
  rw [SetLike.mem_coe, mem_localizedAtPrime_iff]
  exact Submodule.subset_span hx

/-- The inclusion `I →ₗ[A] I.localizedAtPrime P`. -/
def localizedAtPrimeInclusion : I →ₗ[A] I.localizedAtPrime P Aₚ where
  toFun := Set.inclusion (I.self_subset_localizedAtPrime P Aₚ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
lemma localizedAtPrimeInclusion_mk {x : K} (hx : x ∈ I) :
    I.localizedAtPrimeInclusion P Aₚ ⟨x, hx⟩ = ⟨x, self_subset_localizedAtPrime _ _ _ hx⟩ := by
  simp [localizedAtPrimeInclusion]

variable {P} in
theorem mem_localizedAtPrime (x : K) : x ∈ I.localizedAtPrime P Aₚ ↔
    ∃ i : I, ∃ s : P.primeCompl, (s : A) • x = i := by
  simp_rw [mem_localizedAtPrime_iff]
  refine ⟨fun h ↦ ?_, fun ⟨i, s, h⟩ ↦ ?_⟩; swap
  · suffices x = (mk' Aₚ 1 s) • (i : K) from
      this ▸ smul_mem _ _ (mem_span.mpr fun _ a ↦ a (Subtype.coe_prop i))
    rw [algebra_compatible_smul Aₚ (s : A) x] at h
    rw [← MulAction.one_smul (α := Aₚ) x, ← h, ← smul_assoc]
    simp [← mk'_mul]
  refine span_induction h (fun y yI ↦ ⟨⟨y, yI⟩, 1, by simp⟩) ⟨0, 1, by simp⟩ ?_ ?_
  · rintro x y ⟨i₁, s₁, h₁⟩ ⟨i₂, s₂, h₂⟩
    use s₂ • i₁ + s₁ • i₂, s₁ * s₂
    nth_rewrite 1 [smul_add, mul_comm s₁ s₂, Submonoid.coe_mul, Submonoid.coe_mul]
    simp_rw [AddSubmonoid.coe_add, coe_toAddSubmonoid, coe_smul_of_tower, ← h₁, ← h₂, mul_smul]
    rfl
  · intro x y ⟨i, s, h⟩
    obtain ⟨a, s', rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
    use a • i, s * s'
    rw [Submonoid.coe_mul, coe_smul_of_tower, ← h, algebra_compatible_smul Aₚ, smul_smul, smul_smul]
    simp_rw [algebra_compatible_smul Aₚ (a * s), ← mk'_one (M := P.primeCompl), ← mk'_mul]
    congr 1
    apply IsLocalization.mk'_eq_of_eq
    rw [one_mul, show ((1 : P.primeCompl) : A) = 1 by rfl]
    ring

variable {I} {P}

theorem exists_smul_mem_of_mem_localizedAtPrime {x : K} (hx : x ∈ I.localizedAtPrime P Aₚ) :
    ∃ s ∈ P.primeCompl, s • x ∈ I :=
  have ⟨i, s, h⟩ := (I.mem_localizedAtPrime Aₚ x).1 hx
  ⟨s, SetLike.coe_mem s, h ▸ SetLike.coe_mem i⟩

-- `I.localizedAtPrime P` is actually the localization of `I` at `P`.
instance : IsLocalizedModule P.primeCompl (I.localizedAtPrimeInclusion P Aₚ) where
  map_units s := by
    refine (End_isUnit_iff _).mpr ⟨fun ⟨_, _⟩ ⟨_, _⟩ h ↦ ?_, fun x ↦ ⟨(mk' Aₚ 1 s) • x, ?_⟩⟩
    · have s0 : (s : A) ≠ 0 := fun hs ↦ (hs ▸ Subtype.coe_prop s) P.zero_mem
      rw [algebraMap_end_apply, algebraMap_end_apply, SetLike.mk_smul_of_tower_mk,
        Subtype.mk.injEq] at h
      exact Subtype.ext_iff_val.mpr <| smul_right_injective K s0 h
    · simp [← smul_assoc]
  surj' x :=
    have ⟨s, sP, sxI⟩ := exists_smul_mem_of_mem_localizedAtPrime Aₚ (Subtype.coe_prop x)
    ⟨⟨⟨s • x, sxI⟩, ⟨s, sP⟩⟩, (I.localizedAtPrimeInclusion_mk P Aₚ _).symm⟩
  exists_of_eq h := ⟨1, by simpa [localizedAtPrimeInclusion] using h⟩

theorem localizedAtPrime_eq_zero_iff : I.localizedAtPrime P Aₚ = 0 ↔ I = 0 := by
  constructor
  · rw [eq_zero_iff, eq_zero_iff]
    intro h x xI
    exact h _ (self_subset_localizedAtPrime P Aₚ I xI)
  · rintro rfl
    simp

variable (P)

theorem localizedAtPrime_ne_zero (hI : I ≠ 0) : I.localizedAtPrime P Aₚ ≠ 0 :=
  mt (localizedAtPrime_eq_zero_iff Aₚ).mp hI

variable (I)

theorem localizedAtPrime_zero : localizedAtPrime P Aₚ (0 : FractionalIdeal A⁰ K) = 0 :=
  have := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl Aₚ K
  extended_zero K (hf P)

theorem localizedAtPrime_one : localizedAtPrime P Aₚ (1 : FractionalIdeal A⁰ K) = 1 :=
  have := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl Aₚ K
  extended_one K (hf P)

theorem localizedAtPrime_add :
    (I + J).localizedAtPrime P Aₚ = (I.localizedAtPrime P Aₚ) + (J.localizedAtPrime P Aₚ) :=
  have := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl Aₚ K
  extended_add K (hf P) I J

theorem localizedAtPrime_mul :
    (I * J).localizedAtPrime P Aₚ = (I.localizedAtPrime P Aₚ) * (J.localizedAtPrime P Aₚ) :=
  have := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl Aₚ K
  extended_mul K (hf P) I J

--instance : Div (FractionalIdeal A⁰ K) := by sorry
/-  have := IsFractionRing.toField A (K := K)
  apply FractionalIdeal.instDivNonZeroDivisors (R₁ := A) (K := K)
  swap
  sorry
  exact this -/

--#check isDomain_of_le_nonZeroDivisors (S := Aₚ) A P.primeCompl_le_nonZeroDivisors

instance : IsDomain Aₚ := by sorry

instance : IsFractionRing Aₚ K := by sorry

theorem localizedAtPrime_div_le :
    (I/J).localizedAtPrime P Aₚ ≤ I.localizedAtPrime P Aₚ / J.localizedAtPrime P Aₚ := by
  by_cases J0 : J = 0
  · rw [J0, localizedAtPrime_zero, div_zero, div_zero, localizedAtPrime_zero]
  intro t ht
  simp only [val_eq_coe, coe_localizedAtPrime] at ht
  refine span_induction ht (fun x hx ↦ ?_) (zero_mem _)
    (fun x y hx hy ↦ Submodule.add_mem _ hx hy) (fun x y hy ↦ smul_mem _ x hy)
  simp_rw [val_eq_coe, mem_coe, mem_div_iff_of_nonzero (J.localizedAtPrime_ne_zero P Aₚ J0)]
  intro y hy
  rw [mem_localizedAtPrime_iff] at hy ⊢
  refine span_induction hy (fun j hj ↦ subset_span ?_) (by simp)
    (fun z w hz hw ↦ mul_add x z w ▸ Submodule.add_mem _ hz hw)
    (fun a z hz ↦ Algebra.mul_smul_comm a x z ▸ Submodule.smul_mem _ a hz)
  rw [div_nonzero J0] at hx
  exact (Submodule.mem_div_iff_forall_mul_mem).1 hx j hj

variable {J}


theorem localizedAtPrime_div (hJ : J.coeToSubmodule.FG) :
    (I/J).localizedAtPrime P Aₚ = I.localizedAtPrime P Aₚ / J.localizedAtPrime P Aₚ := by
  by_cases J0 : J = 0
  · rw [J0, localizedAtPrime_zero, div_zero, div_zero, localizedAtPrime_zero]
  apply le_antisymm (localizedAtPrime_div_le P Aₚ I J)
  intro t ht
  simp_rw [val_eq_coe, mem_coe, mem_div_iff_of_nonzero (J.localizedAtPrime_ne_zero P Aₚ J0)] at ht
  simp_rw [val_eq_coe, mem_coe, mem_localizedAtPrime_iff]
  -- Construct s ∈ P.primeCompl such that (s • t)J ⊆ I. Then s • t ∈ I/J, so t ∈ span Aₚ (I/J).
  obtain ⟨n, g, hgJ⟩ := fg_iff_exists_fin_generating_family.1 hJ
  have : ∀ i : Fin n, ∃ c ∈ P.primeCompl, c • (t * (g i)) ∈ I := fun i ↦
    have giJ : g i ∈ J := by rw [← mem_coe, ← hgJ]; exact subset_span ⟨i, rfl⟩
    exists_smul_mem_of_mem_localizedAtPrime Aₚ <| ht (g i) (J.self_subset_localizedAtPrime P Aₚ giJ)
  choose c cP hc using this
  let s := Finset.prod univ c
  let b := (algebraMap A Aₚ s) • t
  have hu : IsUnit (algebraMap A Aₚ s) := by
    simp_rw [s, map_prod]
    apply?



    sorry
  have : t = hu.unit⁻¹ • b := by sorry
  --have : t = (mk 1 ⟨s, Submonoid.prod_mem _ (fun i _ ↦ cP i)⟩) • b := by
  --  rw [smul_smul, mk_mul, one_mul, mul_one, mk_self ⟨s, _⟩, one_smul]
  rw [this]
  -- It remains only to check that b := s • t ∈ I/J
  refine smul_mem _ _ <| Submodule.subset_span <| (mem_div_iff_of_nonzero J0).2 (fun y hy ↦ ?_)
  rw [← mem_coe, ← hgJ] at hy
  refine span_induction hy ?_ ((mul_zero b).symm ▸ zero_mem I)
    (fun x y hx hy ↦ mul_add b x y ▸ Submodule.add_mem _ hx hy)
    (fun a x hx ↦ mul_smul_comm a b x ▸ Submodule.smul_mem _ a hx)
  rintro x ⟨i, rfl⟩
  simp_rw [b, s]
  rw [← mul_prod_erase univ c (mem_univ i), _root_.map_mul, mul_comm ((algebraMap A Aₚ) (c i))]
  simp_rw [mul_smul, algebraMap_smul,
    Algebra.smul_mul_assoc]
  apply Submodule.smul_mem _ _ (hc i)

variable {I}

@[simp]
theorem localizedAtPrime_inv (hI : I.coeToSubmodule.FG) :
    I⁻¹.localizedAtPrime P = (I.localizedAtPrime P)⁻¹ := by
  rw [inv_eq, localizedAtPrime_div P 1 hI, localizedAtPrime_one, inv_eq]

variable (I)

theorem not_le_of_localizedAtPrime_eq_one (hI : I.localizedAtPrime P = 1) : ¬ I ≤ P := by
  have ⟨i, s, h⟩ := (I.mem_localizedAtPrime 1).mp (hI.symm ▸ one_mem_one Aₚ⁰)
  unfold coeIdeal coeSubmodule
  refine Set.not_subset.2 ⟨i, Subtype.coe_prop i, ?_⟩
  have : (i : K) = (algebraMap A K) (s : A) := calc
    (i : K) = (s : A) • (Localization.mk 1 s • i) := by rw [← smul_assoc, smul_mk]; simp
    _       = (algebraMap A K) s                  := by rw [← h, Algebra.algebraMap_eq_smul_one]
  simpa [this] using Set.not_mem_of_mem_compl (Subtype.coe_prop s)

end FractionalIdeal
