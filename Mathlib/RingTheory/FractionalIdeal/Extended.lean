/-
Copyright (c) 2024 James Sundstrom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Sundstrom
-/
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.FractionalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Basic

/-!
# Extension of fractional ideals

This file defines the extension of a fractional ideal along a ring homomorphism.

## Main definition

* `FractionalIdeal.extended`: Let `A` and `B` be commutative rings with respective localizations
  `IsLocalization M K` and `IsLocalization N L`. Let `f : A →+* B` be a ring homomorphism with
  `hf : M ≤ Submonoid.comap f N`. If `I : FractionalIdeal M K`, then the extension of `I` along
  `f` is `extended L hf I : FractionalIdeal N L`.
* `FractionalIdeal.extendedHom`: The ring homomorphism version of `FractionalIdeal.extended`.
* `FractionalIdeal.extendedHomₐ`: For `A ⊆ B` an extension of domains, the ring homomorphism that
  sends a fractional ideal of `A` to a fractional ideal of `B`.

## Main results

* `extended_add` says that extension commutes with addition.
* `extended_mul` says that extension commutes with multiplication.

## Tags

fractional ideal, fractional ideals, extended, extension
-/

open IsLocalization FractionalIdeal Submodule

namespace FractionalIdeal

section RingHom

variable {A : Type*} [CommRing A] {B : Type*} [CommRing B] {f : A →+* B}
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

lemma mem_extended_iff (x : L) : x ∈ I.extended L hf ↔ x ∈ span B (map_f '' I) := by
  constructor <;> { intro hx; simpa }

@[simp]
lemma coe_extended_eq_span : I.extended L hf = span B (map_f '' I) := by
  ext; simp [mem_coe, mem_extended_iff]

@[simp]
theorem extended_zero : extended L hf (0 : FractionalIdeal M K) = 0 :=
  have : ((0 : FractionalIdeal M K) : Set K) = {0} := by ext; simp
  coeToSubmodule_injective (by simp [this])

variable {I}

theorem extended_ne_zero [IsDomain B] (hf' : Function.Injective f) (hI : I ≠ 0) (hN : 0 ∉ N) :
    extended L hf I ≠ 0 := by
  simp only [ne_eq, ← coeToSubmodule_inj, coe_extended_eq_span, coe_zero, Submodule.span_eq_bot,
    Set.mem_image, SetLike.mem_coe, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    not_forall]
  obtain ⟨x, hx₁, hx₂⟩ : ∃ x ∈ I, x ≠ 0 := by simpa [ne_eq, eq_zero_iff] using hI
  refine ⟨x, hx₁, ?_⟩
  exact (map_ne_zero_iff _ (IsLocalization.map_injective_of_injective' _ _ _ _ hN hf')).mpr hx₂

@[simp]
theorem extended_eq_zero_iff [IsDomain B] (hf' : Function.Injective f) (hN : 0 ∉ N) :
    extended L hf I = 0 ↔ I = 0 := by
  refine ⟨?_, fun h ↦ h ▸ extended_zero _ _⟩
  contrapose!
  exact fun h ↦ extended_ne_zero L hf hf' h hN

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
  simp only [val_eq_coe, mem_coe, mem_extended_iff, mem_span_image_iff_exists_fun,
    Finset.univ_eq_attach, coe_one] at hx ⊢
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

@[simp]
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

/--
The ring homomorphism version of `FractionalIdeal.extended`.
-/
@[simps]
def extendedHom : FractionalIdeal M K →+* FractionalIdeal N L where
  toFun := extended L hf
  map_one' := extended_one L hf
  map_zero' := extended_zero L hf
  map_mul' := extended_mul L hf
  map_add' := extended_add L hf

end RingHom

section Algebra

open scoped nonZeroDivisors

variable {A K : Type*} (L B : Type*) [CommRing A] [CommRing B] [IsDomain B]
  [Algebra A B] [NoZeroSMulDivisors A B] [Field K] [Field L] [Algebra A K] [Algebra B L]
  [IsFractionRing A K] [IsFractionRing B L]

/--
The ring homomorphisme that extends a fractional ideal of `A` to a fractional ideal of `B` for
`A ⊆ B` an extension of domains.
-/
abbrev extendedHomₐ : FractionalIdeal A⁰ K →+* FractionalIdeal B⁰ L :=
  extendedHom L <|
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective _ _)

theorem extendedHomₐ_eq_zero_iff {I : FractionalIdeal A⁰ K} :
    extendedHomₐ L B I = 0 ↔ I = 0 :=
  extended_eq_zero_iff _ _ (FaithfulSMul.algebraMap_injective _ _) zero_notMem_nonZeroDivisors

theorem extendedHomₐ_coeIdeal_eq_map (I : Ideal A) :
    (I : FractionalIdeal A⁰ K).extendedHomₐ L B =
      (I.map (algebraMap A B) : FractionalIdeal B⁰ L) := extended_coeIdeal_eq_map L _ I

variable [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L] [IsDomain A]
  [Algebra.IsIntegral A B]

theorem coe_extendedHomₐ_eq_span (I : FractionalIdeal A⁰ K) :
    extendedHomₐ L B I = span B (algebraMap K L '' I) := by
  rw [extendedHom_apply, coe_extended_eq_span,
    IsLocalization.algebraMap_eq_map_map_submonoid A⁰ B K L]
  rfl

end Algebra

end FractionalIdeal
