/-
Copyright (c) 2024 James Sundstrom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Sundstrom
-/
import Mathlib.RingTheory.FractionalIdeal.Extended
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.Algebra.Module.LocalizedModule

/-!
# Localization of a fractional ideal at a prime

This file defines the localization of a fractional ideal at a prime ideal.

## Main definition

* `FractionalIdeal.localizationAtPrime`: The localization of a fractional ideal at a prime ideal.

## Main results

* `coe_localizedAtPrime`: The localization of `I` is `Submodule.span Aₚ I`.
* `localizedAtPrime_add`: Localizing commutes with addition.
* `localizedAtPrime_mul`: Localizing commutes with multiplication.
* `localizedAtPrime_div`: Localizing commutes with division for finitely-generated denominator.
* `localizedAtPrime_inv`: Localizing commutes with inverses for finitely-generated `I`.
* `not_le_of_localizedAtPrime_eq_one`: If `I.localizedAtPrime P = 1`, then `¬ I ≤ P`.

## Tags

fractional ideal, fractional ideals, localization
-/

open IsLocalization Localization Algebra FractionalIdeal Submodule nonZeroDivisors Finset Module

variable {A : Type*} [CommRing A] [IsDomain A] (P : Ideal A) [P.IsPrime]
variable (I : FractionalIdeal A⁰ (FractionRing A)) (J : FractionalIdeal A⁰ (FractionRing A))

local notation "Aₚ" => Localization.AtPrime P
local notation "K" => FractionRing A
local notation "hf" => nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ <|
  IsLocalization.injective Aₚ P.primeCompl_le_nonZeroDivisors

instance : IsScalarTower A Aₚ K :=
  localization_isScalarTower_of_submonoid_le Aₚ K P.primeCompl A⁰ P.primeCompl_le_nonZeroDivisors

instance : IsFractionRing Aₚ K :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl Aₚ K

namespace FractionalIdeal

/-- The localization of a fractional ideal `I` of a domain `A`, at a prime ideal `P` of `A`.-/
abbrev localizedAtPrime : FractionalIdeal Aₚ⁰ K :=
  I.extended K hf

theorem coe_localizedAtPrime : (I.localizedAtPrime P).coeToSubmodule = Submodule.span Aₚ I := by
  simp [map_unique hf (RingHom.id K) (fun a ↦ IsScalarTower.algebraMap_apply A Aₚ K a)]

theorem mem_localizedAtPrime_iff (x : K) : x ∈ I.localizedAtPrime P ↔ x ∈ Submodule.span Aₚ I := by
  rw [← I.coe_localizedAtPrime P, mem_coe]

theorem self_subset_localizedAtPrime : (I : Set K) ⊆ I.localizedAtPrime P := by
  intro x hx
  rw [SetLike.mem_coe, mem_localizedAtPrime_iff]
  exact Submodule.subset_span hx

/-- The inclusion `I →ₗ[A] I.localizedAtPrime P`. -/
def localizedAtPrime_inclusion : I →ₗ[A] I.localizedAtPrime P where
  toFun := Set.inclusion (I.self_subset_localizedAtPrime P)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem mem_localizedAtPrime_iff_eq (x : K) : x ∈ I.localizedAtPrime P ↔
    ∃ i : I, ∃ s : P.primeCompl, x = mk 1 s • i := by
  refine ⟨fun h ↦ ?_, fun ⟨i, s, h⟩ ↦ ?_⟩; swap
  · exact h ▸ (smul_mem _ (mk 1 s) <| I.self_subset_localizedAtPrime P (Subtype.coe_prop i))
  rw [mem_localizedAtPrime_iff] at h
  refine span_induction h (fun y yI ↦ ⟨⟨y, yI⟩, 1, by rw [mk_one, one_smul]⟩) ⟨0, 1, by simp⟩ ?_ ?_
  · rintro _ _ ⟨i₁, s₁, rfl⟩ ⟨i₂, s₂, rfl⟩
    use s₂ • i₁ + s₁ • i₂, s₁ * s₂
    simp only [AddSubmonoid.coe_add, coe_toAddSubmonoid, coe_smul_of_tower, smul_add]
    congr 1
    · rw [Submonoid.mk_smul, algebra_compatible_smul Aₚ (s₂ : A) (i₁ : K), ← mk_one_eq_algebraMap,
        ← smul_assoc, smul_eq_mul, mk_mul, mul_one, ← mk_mul, mk_self, mul_one]
    · rw [Submonoid.mk_smul, algebra_compatible_smul Aₚ (s₁ : A) (i₂ : K), ← mk_one_eq_algebraMap,
        ← smul_assoc, smul_eq_mul, mk_mul, mul_comm, mul_assoc, ← mk_mul, mk_self, one_mul, mul_one]
  · rintro y _ ⟨i, s, rfl⟩
    refine Localization.induction_on y (fun ⟨a, s₁⟩ ↦ ⟨a • i, s₁ * s, ?_⟩)
    rw [coe_smul_of_tower, ← smul_assoc, smul_comm, ← smul_assoc]
    nth_rewrite 1 [← mul_one a, ← smul_eq_mul, ← smul_mk]
    rw [smul_assoc a, smul_eq_mul, mk_mul, one_mul]

variable {I} {P}

theorem exists_smul_mem_of_mem_localizedAtPrime {x : K} (hx : x ∈ I.localizedAtPrime P) :
    ∃ s ∈ P.primeCompl, s • x ∈ I := by
  obtain ⟨i, s, rfl⟩ := (I.mem_localizedAtPrime_iff_eq P x).1 hx
  use s, Subtype.coe_prop s
  rw [← smul_assoc, smul_mk, mk_eq_mk', smul_eq_mul, mk'_mul_cancel_left, _root_.map_one, one_smul]
  apply SetLike.coe_mem

-- `I.localizedAtPrime P` is actually the localization of `I` at `P`.
instance : IsLocalizedModule P.primeCompl (I.localizedAtPrime_inclusion P) where
  map_units s := by
    refine (End_isUnit_iff _).mpr ⟨fun ⟨_, _⟩ ⟨_, _⟩ h ↦ ?_, fun x ↦ ⟨(mk 1 s) • x, ?_⟩⟩
    · have s0 : (s : A) ≠ 0 := fun hs ↦ (hs ▸ Subtype.coe_prop s) P.zero_mem
      rw [algebraMap_end_apply, algebraMap_end_apply, SetLike.mk_smul_of_tower_mk,
        Subtype.mk.injEq] at h
      exact Subtype.ext_iff_val.mpr <| smul_right_injective K s0 h
    · rw [algebraMap_end_apply, ← smul_assoc, smul_mk]
      simp
  surj' x :=
    have ⟨s, sP, sxI⟩ := exists_smul_mem_of_mem_localizedAtPrime (Subtype.coe_prop x)
    ⟨⟨⟨s • x, sxI⟩, ⟨s, sP⟩⟩, by rw [localizedAtPrime_inclusion]; rfl⟩
  exists_of_eq h := ⟨1, by simpa [localizedAtPrime_inclusion] using h⟩

variable (P)

theorem localizedAtPrime_ne_zero (hI : I ≠ 0) : I.localizedAtPrime P ≠ 0 := by
  simp_rw [ne_eq, eq_zero_iff, not_forall] at hI ⊢
  rcases hI with ⟨x, xI, x0⟩
  exact ⟨x, I.self_subset_localizedAtPrime P xI, x0⟩

variable (I)

theorem localizedAtPrime_zero : localizedAtPrime P 0 = 0 :=
  extended_zero K hf

theorem localizedAtPrime_one : localizedAtPrime P 1 = 1 :=
  extended_one K hf

theorem localizedAtPrime_add :
    (I + J).localizedAtPrime P = (I.localizedAtPrime P) + (J.localizedAtPrime P) :=
  extended_add K hf I J

theorem localizedAtPrime_mul :
    (I * J).localizedAtPrime P = (I.localizedAtPrime P) * (J.localizedAtPrime P) :=
  extended_mul K hf I J

theorem localizedAtPrime_div_le :
    (I/J).localizedAtPrime P ≤ I.localizedAtPrime P / J.localizedAtPrime P := by
  by_cases J0 : J = 0
  · rw [J0, localizedAtPrime_zero, div_zero, localizedAtPrime_zero, div_zero]
  intro t ht
  simp only [val_eq_coe, coe_localizedAtPrime] at ht
  refine span_induction ht (fun x hx ↦ ?_) (zero_mem _)
    (fun x y hx hy ↦ Submodule.add_mem _ hx hy) (fun x y hy ↦ smul_mem _ x hy)
  simp_rw [val_eq_coe, mem_coe, mem_div_iff_of_nonzero (J.localizedAtPrime_ne_zero P J0)]
  intro y hy
  rw [mem_localizedAtPrime_iff] at hy ⊢
  refine span_induction hy (fun j hj ↦ subset_span ?_) (by simp)
    (fun z w hz hw ↦ mul_add x z w ▸ Submodule.add_mem _ hz hw)
    (fun a z hz ↦ Algebra.mul_smul_comm a x z ▸ Submodule.smul_mem _ a hz)
  rw [div_nonzero J0] at hx
  exact (Submodule.mem_div_iff_forall_mul_mem).1 hx j hj

variable {J}

theorem localizedAtPrime_div (hJ : J.coeToSubmodule.FG) :
    (I/J).localizedAtPrime P = I.localizedAtPrime P / J.localizedAtPrime P := by
  by_cases J0 : J = 0
  · rw [J0, localizedAtPrime_zero, div_zero, localizedAtPrime_zero, div_zero]
  apply le_antisymm (localizedAtPrime_div_le P I J)
  intro t ht
  simp_rw [val_eq_coe, mem_coe, mem_div_iff_of_nonzero (J.localizedAtPrime_ne_zero P J0)] at ht
  simp_rw [val_eq_coe, mem_coe, mem_localizedAtPrime_iff]
  -- Construct s ∈ P.primeCompl such that (s • t)J ⊆ I. Then s • t ∈ I/J, so t ∈ span Aₚ (I/J).
  obtain ⟨n, g, hgJ⟩ := fg_iff_exists_fin_generating_family.1 hJ
  have : ∀ i : Fin n, ∃ c ∈ P.primeCompl, c • (t * (g i)) ∈ I := fun i ↦
    have giJ : g i ∈ J := by rw [← mem_coe, ← hgJ]; exact subset_span ⟨i, rfl⟩
    exists_smul_mem_of_mem_localizedAtPrime <| ht (g i) (J.self_subset_localizedAtPrime P giJ)
  choose c cP hc using this
  let s := Finset.prod univ c
  let b := (mk s 1 : Aₚ) • t
  have : t = (mk 1 ⟨s, Submonoid.prod_mem _ (fun i _ ↦ cP i)⟩) • b := by
    rw [smul_smul, mk_mul, one_mul, mul_one, mk_self ⟨s, _⟩, one_smul]
  rw [this]
  -- It remains only to check that b := s • t ∈ I/J
  refine smul_mem _ _ <| Submodule.subset_span <| (mem_div_iff_of_nonzero J0).2 (fun y hy ↦ ?_)
  rw [← mem_coe, ← hgJ] at hy
  refine span_induction hy ?_ ((mul_zero b).symm ▸ zero_mem I)
    (fun x y hx hy ↦ mul_add b x y ▸ Submodule.add_mem _ hx hy)
    (fun a x hx ↦ mul_smul_comm a b x ▸ Submodule.smul_mem _ a hx)
  rintro x ⟨i, rfl⟩
  simp_rw [b, mk_one_eq_algebraMap, ← algebra_compatible_smul, s]
  rw [← mul_prod_erase univ c (mem_univ i), mul_smul, smul_comm, smul_mul_assoc]
  exact Submodule.smul_mem _ _ (Algebra.smul_mul_assoc (c i) t (g i) ▸ hc i)

variable {I}

theorem localizedAtPrime_inv (hI : I.coeToSubmodule.FG) :
    (I⁻¹).localizedAtPrime P = (I.localizedAtPrime P)⁻¹ := by
  rw [inv_eq, localizedAtPrime_div P 1 hI, localizedAtPrime_one, inv_eq]

variable (I)

theorem not_le_of_localizedAtPrime_eq_one (hI : I.localizedAtPrime P = 1) : ¬ I ≤ P := by
  have ⟨i, s, h⟩ := (I.mem_localizedAtPrime_iff_eq P 1).1 <| hI.symm ▸ one_mem_one Aₚ⁰ (P := K)
  unfold coeIdeal coeSubmodule
  refine Set.not_subset.2 ⟨i, Subtype.coe_prop i, ?_⟩
  have : (i : K) = (algebraMap A K) (s : A) := calc
    (i : K) = ((s : A) • Localization.mk 1 s) • i := by rw [smul_mk]; simp
    _       = (s : A) • (Localization.mk 1 s • i) := by field_simp
    _       = (algebraMap A K) s                  := by rw [← h, Algebra.algebraMap_eq_smul_one]
  simp only [map_coe, linearMap_apply, Set.mem_image, mem_coe, not_exists, not_and, this]
  intro p hp s_eq_p
  replace s_eq_p := (NoZeroSMulDivisors.algebraMap_injective A K s_eq_p).symm
  exact (s_eq_p ▸ (Subtype.coe_prop s)) hp

end FractionalIdeal
