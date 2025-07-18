/-
Copyright (c) 2024 James Sundstrom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Sundstrom, Xavier Roblot
-/
import Mathlib.RingTheory.DedekindDomain.Ideal

/-!
# Extension of fractional ideals

This file defines the extension of a fractional ideal along a ring homomorphism.

## Main definition

* `FractionalIdeal.extended`: Let `A` and `B` be commutative rings with respective localizations
  `IsLocalization M K` and `IsLocalization N L`. Let `f : A →+* B` be a ring homomorphism with
  `hf : M ≤ Submonoid.comap f N`. If `I : FractionalIdeal M K`, then the extension of `I` along
  `f` is `extended L hf I : FractionalIdeal N L`.

## Main results

* `FractionalIdeal.extended_add` says that extension commutes with addition.
* `FractionalIdeal.extended_mul` says that extension commutes with multiplication.
* `FractionalIdeal.extended_inv` says that extension commutes with inversion.
* `FractionalIdeal.extended_injective` says that extension (by an algebra map) is injective.
* `Ideal.map_algebraMap_injective`: the map of an ideal by an algebra map is injective

## Tags

fractional ideal, fractional ideals, extended, extension
-/

open IsLocalization FractionalIdeal Submodule

namespace FractionalIdeal

variable {A : Type*} [CommRing A] {B : Type*} [CommRing B]

section General

variable {f : A →+* B}
variable {K : Type*} {M : Submonoid A} [CommRing K] [Algebra A K] [IsLocalization M K]
variable (L : Type*) {N : Submonoid B} [CommRing L] [Algebra B L] [IsLocalization N L]
variable (hf : M ≤ Submonoid.comap f N)
variable (I : FractionalIdeal M K) (J : FractionalIdeal M K)

/-- Given commutative rings `A` and `B` with respective localizations `IsLocalization M K` and
`IsLocalization N L`, and a ring homomorphism `f : A →+* B` satisfying `M ≤ Submonoid.comap f N`, a
fractional ideal `I` of `A` can be extended along `f` to a fractional ideal of `B`. -/
def extended (I : FractionalIdeal M K) : FractionalIdeal N L where
  val := span B <| (IsLocalization.map (S := K) L f hf) '' I
  property := by
    have ⟨a, ha, frac⟩ := I.isFractional
    refine ⟨f a, hf ha, fun b hb ↦ ?_⟩
    refine span_induction (fun x hx ↦ ?_) ⟨0, by simp⟩
      (fun x y _ _ hx hy ↦ smul_add (f a) x y ▸ isInteger_add hx hy) (fun b c _ hc ↦ ?_) hb
    · rcases hx with ⟨k, kI, rfl⟩
      obtain ⟨c, hc⟩ := frac k kI
      exact ⟨f c, by simp [← IsLocalization.map_smul, ← hc]⟩
    · rw [← smul_assoc, smul_eq_mul, mul_comm (f a), ← smul_eq_mul, smul_assoc]
      exact isInteger_smul hc

local notation "map_f" => (IsLocalization.map (S := K) L f hf)

lemma mem_extended_iff (x : L) : (x ∈ I.extended L hf) ↔ x ∈ span B (map_f '' I) := by
  constructor <;> { intro hx; simpa }

@[simp]
lemma coe_extended_eq_span : I.extended L hf = span B (map_f '' I) := by
  ext; simp [mem_coe, mem_extended_iff]

@[simp]
theorem extended_zero : extended L hf (0 : FractionalIdeal M K) = 0 :=
  have : ((0 : FractionalIdeal M K) : Set K) = {0} := by ext; simp
  coeToSubmodule_injective (by simp [this])

variable {I}

theorem extended_ne_zero [IsDomain K] [IsDomain L] [NoZeroSMulDivisors A K] [NoZeroSMulDivisors B L]
    (hf' : Function.Injective f) (hI : I ≠ 0) :
    extended L hf I ≠ 0 := by
  simp only [ne_eq, ← coeToSubmodule_inj, coe_extended_eq_span, coe_zero, Submodule.span_eq_bot,
    Set.mem_image, SetLike.mem_coe, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    not_forall]
  obtain ⟨x, hx₁, hx₂⟩ : ∃ x ∈ I, x ≠ 0 := by simpa [ne_eq, eq_zero_iff] using hI
  refine ⟨x, hx₁, ?_⟩
  exact (map_ne_zero_iff _ (IsLocalization.map_injective_of_injective' _ _ _ hf hf')).mpr hx₂

@[simp]
theorem extended_eq_zero_iff [IsDomain K] [IsDomain L] [NoZeroSMulDivisors A K]
    [NoZeroSMulDivisors B L] (hf' : Function.Injective f) :
    extended L hf I = 0 ↔ I = 0 := by
  refine ⟨?_, fun h ↦ h ▸ extended_zero _ _⟩
  contrapose!
  exact fun h ↦ extended_ne_zero L hf hf' h

variable (I)

@[simp]
theorem extended_one : extended L hf (1 : FractionalIdeal M K) = 1 := by
  refine coeToSubmodule_injective <| Submodule.ext fun x ↦ ⟨fun hx ↦ span_induction
    ?_ (zero_mem _) (fun y z _ _ hy hz ↦ add_mem hy hz) (fun b y _ hy ↦ smul_mem _ b hy) hx, ?_⟩
  · rintro ⟨b, _, rfl⟩
    rw [Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]
    exact smul_mem _ _ <| subset_span ⟨1, by simp [one_mem_one]⟩
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨f a, ha, by rw [Algebra.linearMap_apply, Algebra.linearMap_apply, map_eq]⟩

theorem extended_le_one_of_le_one (hI : I ≤ 1) : extended L hf I ≤ 1 := by
  obtain ⟨J, rfl⟩ := le_one_iff_exists_coeIdeal.mp hI
  intro x hx
  simp only [val_eq_coe, coe_one]
  simp only [val_eq_coe, mem_coe, mem_extended_iff, mem_span_image_iff_exists_fun,
    Finset.univ_eq_attach] at hx
  obtain ⟨s, hs, c, rfl⟩ := hx
  refine Submodule.sum_smul_mem _ _ fun x h ↦ mem_one.mpr ?_
  obtain ⟨a, ha⟩ : ∃ a, (algebraMap A K) a = ↑x := by
    simpa [val_eq_coe, coe_one, mem_one] using hI <| hs x.prop
  exact ⟨f a, by rw [← ha, map_eq]⟩

theorem one_le_extended_of_one_le (hI : 1 ≤ I) : 1 ≤ extended L hf I := by
  rw [one_le] at hI ⊢
  exact (mem_extended_iff _ _ _ _).mpr <| subset_span ⟨1, hI, by rw [map_one]⟩

theorem extended_add : (I + J).extended L hf = (I.extended L hf) + (J.extended L hf) := by
  apply coeToSubmodule_injective
  simp only [coe_extended_eq_span, coe_add, Submodule.add_eq_sup, ← span_union, ← Set.image_union]
  apply Submodule.span_eq_span
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨i, hi, j, hj, rfl⟩ := (mem_add I J y).mp <| SetLike.mem_coe.mp hy
    rw [RingHom.map_add]
    exact add_mem (Submodule.subset_span ⟨i, Set.mem_union_left _ hi, by simp⟩)
      (Submodule.subset_span ⟨j, Set.mem_union_right _ hj, by simp⟩)
  · rintro _ ⟨y, hy, rfl⟩
    suffices y ∈ I + J from SetLike.mem_coe.mpr <| Submodule.subset_span ⟨y, by simp [this]⟩
    exact hy.elim (fun h ↦ (mem_add I J y).mpr ⟨y, h, 0, zero_mem J, add_zero y⟩)
      (fun h ↦ (mem_add I J y).mpr ⟨0, zero_mem I, y, h, zero_add y⟩)

theorem extended_mul : (I * J).extended L hf = (I.extended L hf) * (J.extended L hf) := by
  apply coeToSubmodule_injective
  simp only [coe_extended_eq_span, coe_mul, span_mul_span]
  refine Submodule.span_eq_span (fun _ h ↦ ?_) (fun _ h ↦ ?_)
  · rcases h with ⟨x, hx, rfl⟩
    replace hx : x ∈ (I : Submodule A K) * (J : Submodule A K) := coe_mul I J ▸ hx
    rw [Submodule.mul_eq_span_mul_set] at hx
    refine span_induction (fun y hy ↦ ?_) (by simp) (fun y z _ _ hy hz ↦ ?_)
      (fun a y _ hy ↦ ?_) hx
    · rcases Set.mem_mul.mp hy with ⟨i, hi, j, hj, rfl⟩
      exact subset_span <| Set.mem_mul.mpr
        ⟨map_f i, ⟨i, hi, by simp⟩, map_f j, ⟨j, hj, by simp⟩, by simp⟩
    · exact map_add map_f y z ▸ Submodule.add_mem _ hy hz
    · rw [Algebra.smul_def, map_mul, map_eq, ← Algebra.smul_def]
      exact smul_mem _ (f a) hy
  · rcases Set.mem_mul.mp h with ⟨y, ⟨i, hi, rfl⟩, z, ⟨j, hj, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨i * j, mul_mem_mul hi hj, by simp⟩

theorem extended_coeIdeal_eq_map (I₀ : Ideal A) :
    (I₀ : FractionalIdeal M K).extended L hf = (I₀.map f : FractionalIdeal N L) := by
  rw [Ideal.map, Ideal.span, ← coeToSubmodule_inj, Ideal.submodule_span_eq, coe_coeIdeal,
    IsLocalization.coeSubmodule_span, coe_extended_eq_span]
  refine Submodule.span_eq_span ?_ ?_
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact Submodule.subset_span
      ⟨f a, Set.mem_image_of_mem f ha, by rw [Algebra.linearMap_apply, IsLocalization.map_eq hf a]⟩
  · rintro _ ⟨_ , ⟨a, ha, rfl⟩, rfl⟩
    exact Submodule.subset_span
      ⟨algebraMap A K a, mem_coeIdeal_of_mem M ha, IsLocalization.map_eq hf a⟩

end General
section FractionRing

open scoped nonZeroDivisors

variable {K : Type*} (L : Type*) [IsDomain A] [IsDomain B] [Field K] [Field L] [Algebra A K]
  [Algebra B L] [IsFractionRing A K] [IsFractionRing B L] [Algebra A B] [NoZeroSMulDivisors A B]

theorem extended_inv [IsDedekindDomain A] [IsDedekindDomain B] {I : FractionalIdeal A⁰ K}
    (hI : I ≠ 0) :
    haveI hs : A⁰ ≤ Submonoid.comap (algebraMap A B) B⁰ := fun _ hx ↦ by simpa using hx
    extended L hs (f := algebraMap A B) I⁻¹ =
       (extended L hs (f := algebraMap A B) I : FractionalIdeal B⁰ L)⁻¹ := by
  rw [← mul_eq_one_iff_eq_inv₀, ← extended_mul, inv_mul_cancel₀ hI, extended_one]
  exact extended_ne_zero _ _ (FaithfulSMul.algebraMap_injective _ _) hI

variable (K) in
theorem extended_coeIdeal_eq_map_algebraMap (I : Ideal A) :
    haveI hs : A⁰ ≤ Submonoid.comap (algebraMap A B) B⁰ := fun _ hx ↦ by simpa using hx
    (I : FractionalIdeal A⁰ K).extended L hs =
      (I.map (algebraMap A B) : FractionalIdeal B⁰ L) :=
  FractionalIdeal.extended_coeIdeal_eq_map _ _ _

variable [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]

variable (B)

lemma coe_extended_eq_span_algebraMap [IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L]
    (I : FractionalIdeal A⁰ K) :
    haveI hs : A⁰ ≤ Submonoid.comap (algebraMap A B) B⁰ := fun _ hx ↦ by simpa using hx
    I.extended L hs = span B (algebraMap K L '' I) := by
  rw [IsLocalization.algebraMap_eq_map_map_submonoid A⁰ B K L]
  exact coe_extended_eq_span L _ I

variable [IsIntegrallyClosed A] [IsIntegrallyClosed B] [Algebra.IsIntegral A B]

theorem le_one_of_extended_le_one {I : FractionalIdeal A⁰ K}
    (hs : A⁰ ≤ Submonoid.comap (algebraMap A B) B⁰) (hI : extended L hs I ≤ 1) : I ≤ 1 := by
  contrapose! hI
  rw [SetLike.not_le_iff_exists] at hI ⊢
  obtain ⟨x, hx₁, hx₂⟩ := hI
  refine ⟨algebraMap K L x, ?_, ?_⟩
  · rw [← FractionalIdeal.mem_coe, coe_extended_eq_span_algebraMap B L I]
    exact subset_span <| Set.mem_image_of_mem _ hx₁
  · contrapose! hx₂
    rw [mem_one_iff, ← IsIntegrallyClosed.isIntegral_iff] at hx₂ ⊢
    exact IsIntegral.tower_bot_of_field <| isIntegral_trans _ hx₂

theorem extended_le_one_iff {I : FractionalIdeal A⁰ K} :
    haveI hs : A⁰ ≤ Submonoid.comap (algebraMap A B) B⁰ := fun _ hx ↦ by simpa using hx
    extended L hs I ≤ 1 ↔ I ≤ 1 := by
  have hs : A⁰ ≤ Submonoid.comap (algebraMap A B) B⁰ := fun _ hx ↦ by simpa using hx
  exact ⟨fun h ↦ le_one_of_extended_le_one B L hs h, fun a ↦ extended_le_one_of_le_one L hs I a⟩

variable [IsDedekindDomain A] [IsDedekindDomain B]

theorem one_le_extended_iff {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) :
    haveI hs : A⁰ ≤ Submonoid.comap (algebraMap A B) B⁰ := fun _ hx ↦ by simpa using hx
    1 ≤ extended L hs I ↔ 1 ≤ I := by
  rw [← inv_le_inv_iff (extended_ne_zero _ _ (FaithfulSMul.algebraMap_injective _ _) hI)
    (by simp), inv_one, ← extended_inv _ hI, extended_le_one_iff, inv_le_comm hI one_ne_zero,
    inv_one]

theorem extended_eq_one_iff {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) :
    haveI hs : A⁰ ≤ Submonoid.comap (algebraMap A B) B⁰ := fun _ hx ↦ by simpa using hx
    extended L hs I = 1 ↔ I = 1 := by
  rw [le_antisymm_iff, extended_le_one_iff, one_le_extended_iff _ _ hI, ← le_antisymm_iff]

theorem extended_injective :
    haveI hs : A⁰ ≤ Submonoid.comap (algebraMap A B) B⁰ := fun _ hx ↦ by simpa using hx
    Function.Injective (fun I : FractionalIdeal A⁰ K ↦ extended L hs I) := by
  intro I J h
  by_cases hI : I = 0
  · rw [hI]
    dsimp only at h
    rwa [eq_comm, hI, extended_zero,
      extended_eq_zero_iff _ _ (FaithfulSMul.algebraMap_injective _ _), eq_comm] at h
  by_cases hJ : J = 0
  · rw [hJ]
    dsimp only at h
    rwa [hJ, extended_zero, extended_eq_zero_iff _ _ (FaithfulSMul.algebraMap_injective _ _)] at h
  rwa [← mul_inv_eq_one₀ (extended_ne_zero _ _ (FaithfulSMul.algebraMap_injective _ _) hJ),
    ← extended_inv _ hJ, ← extended_mul, extended_eq_one_iff _  _ (mul_ne_zero hI (inv_ne_zero hJ)),
    mul_inv_eq_one₀ hJ] at h

theorem _root_.Ideal.map_algebraMap_injective :
    Function.Injective (fun I : Ideal A ↦ I.map (algebraMap A B)) := by
  let _ : Algebra (FractionRing A) (FractionRing B) := FractionRing.liftAlgebra A (FractionRing B)
  intro I _ h
  rwa [← coeIdeal_inj (K := FractionRing B), ← extended_coeIdeal_eq_map_algebraMap (FractionRing A),
    ← extended_coeIdeal_eq_map_algebraMap (FractionRing A), (extended_injective _ _).eq_iff,
    coeIdeal_inj] at h

end FractionRing

end FractionalIdeal
