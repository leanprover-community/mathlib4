/-
Copyright (c) 2024 James Sundstrom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Sundstrom
-/
import Mathlib.RingTheory.FractionalIdeal.Basic

/-!
# Extension of fractional ideals

This file defines the extension of a fractional ideal along a ring homomorphism.

## Main definition

* `FractionalIdeal.extended`: Let `A` and `B` be commutative rings with respective localizations
  `IsLocalization M K` and `IsLocalization N L`. Let `f : A →+* B` be a ring homomorphism with
  `hf : M ≤ Submonoid.comap f N`. If `I : FractionalIdeal M K`, then the extension of `I` along
  `f` is `extended L hf I : FractionalIdeal N L`.

## Main results

* `extended_add` says that extension commutes with addition.
* `extended_mul` says that extension commutes with multiplication.

## Tags

fractional ideal, fractional ideals, extended, extension
-/

open IsLocalization FractionalIdeal Submodule

namespace FractionalIdeal

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
    refine span_induction hb (fun x hx ↦ ?_) ⟨0, by simp⟩
      (fun x y hx hy ↦ smul_add (f a) x y ▸ isInteger_add hx hy) (fun b c hc ↦ ?_)
    · rcases hx with ⟨k, kI, rfl⟩
      obtain ⟨c, hc⟩ := frac k kI
      exact ⟨f c, by simp [← IsLocalization.map_smul, ← hc]⟩
    · rw [← smul_assoc, smul_eq_mul, mul_comm (f a), ← smul_eq_mul, smul_assoc]
      exact isInteger_smul hc

local notation "map_f" => (IsLocalization.map (S := K) L f hf)

lemma mem_extended_iff (x : L) : (x ∈ I.extended L hf) ↔ x ∈ span B (map_f '' I) := by
  constructor <;> { intro hx; simpa }

lemma extended_eq : (I.extended L hf).coeToSubmodule = span B (map_f '' I) := by
  ext; simp [mem_coe, mem_extended_iff]

theorem extended_zero : extended L hf (0 : FractionalIdeal M K) = 0 := by
  rw [extended, eq_zero_iff]
  intro x hx
  rw [← mem_coe, coe_mk] at hx
  change x ∈ (0 : Submodule B L)
  convert hx
  convert Submodule.span_zero.symm
  have : ((0 : FractionalIdeal M K) : Set K) = {0} := by ext; simp
  rw [this, Set.image_singleton, _root_.map_zero, Set.singleton_zero]

theorem extended_one : extended L hf (1 : FractionalIdeal M K) = 1 := by
  apply coeToSubmodule_injective
  convert extended_eq L hf (1 : FractionalIdeal M K)
  refine Submodule.ext <| fun x ↦ Iff.intro ?_  <| fun hx ↦
    span_induction hx ?_ (zero_mem _) (fun y z hy hz ↦ add_mem hy hz) (fun b y hy ↦ smul_mem _ b hy)
  · rintro ⟨b, _, rfl⟩
    rw [Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]
    exact smul_mem _ _ <| Submodule.subset_span ⟨1, by simp [one_mem_one M], _root_.map_one _⟩
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨f a, ha, by rw [Algebra.linearMap_apply, Algebra.linearMap_apply, map_eq]⟩

theorem extended_add : (I + J).extended L hf = (I.extended L hf) + (J.extended L hf) := by
  refine le_antisymm (fun _ h ↦ ?_) ?_
  · simp only [val_eq_coe, mem_coe] at h ⊢
    refine span_induction ((mem_extended_iff L hf _ _).1 h) ?_ (zero_mem _)
      (fun x y hx hy ↦ Submodule.add_mem _ hx hy) (fun b y hy ↦ smul_mem _ b hy)
    · rintro _ ⟨y, hy, rfl⟩
      rw [← FractionalIdeal.coeToSet_coeToSubmodule, SetLike.mem_coe, mem_coe, mem_add] at hy
      rw [mem_add]
      rcases hy with ⟨i, hi, j, hj, rfl⟩
      use map_f i, (I.extended_eq L hf) ▸ subset_span <| Set.mem_image_of_mem map_f hi
      use map_f j, (J.extended_eq L hf) ▸ subset_span <| Set.mem_image_of_mem map_f hj
      rw [map_add]
  · change (extended L hf I + extended L hf J).coeToSubmodule ≤ (extended L hf _).coeToSubmodule
    rw [coe_add, Submodule.add_eq_sup]
    refine sup_le (span_mono (Set.image_mono ?_)) (span_mono (Set.image_mono ?_))
    · intro i hi
      rw [← FractionalIdeal.coeToSet_coeToSubmodule, SetLike.mem_coe, mem_coe, mem_add]
      use i, hi, 0, zero_mem J, add_zero i
    · intro j hj
      rw [← FractionalIdeal.coeToSet_coeToSubmodule, SetLike.mem_coe, mem_coe, mem_add]
      use 0, zero_mem I, j, hj, zero_add j

theorem extended_mul : (I * J).extended L hf = (I.extended L hf) * (J.extended L hf) := by
  refine FractionalIdeal.ext fun _ ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine span_induction ((mem_extended_iff L hf _ _).1 h) ?_ (zero_mem _)
      (fun y z hy hz ↦ Submodule.add_mem _ hy hz) (fun b y hy ↦ smul_mem _ b hy)
    · rintro _ ⟨y, hy, rfl⟩
      refine FractionalIdeal.mul_induction_on hy (fun i hi j hj ↦ ?_) (fun y z hy hz ↦ ?_)
      · rw [_root_.map_mul]
        apply mul_mem_mul <;> refine (mem_extended_iff L hf _ _).2 <| Submodule.subset_span ?_
        · use i, hi
        · use j, hj
      · rw [_root_.map_add]
        exact Submodule.add_mem _ hy hz
  · refine FractionalIdeal.mul_induction_on h ?_ (fun x y hx hy ↦ Submodule.add_mem _ hx hy)
    intro x hx
    refine span_induction ((I.mem_extended_iff L hf x).1 hx) ?_ (by simp [zero_mem])
      (fun x y hx hy z hz ↦ add_mul x y z ▸ Submodule.add_mem _ (hx z hz) (hy z hz))
      (fun x y hy z hz ↦ smul_mul_assoc x y z ▸ smul_mem _ x (hy z hz))
    rintro _ ⟨i, hi, rfl⟩ y hy
    refine span_induction ((J.mem_extended_iff L hf y).1 hy) ?_
      ((mul_zero (map_f i)).symm ▸ zero_mem _)
      (fun z w hz hw ↦ mul_add (map_f i) z w ▸ Submodule.add_mem _ hz hw)
      (fun z w hw ↦ mul_smul_comm z (map_f i) w ▸ smul_mem _ z hw)
    rintro _ ⟨j, hj, rfl⟩
    exact Submodule.subset_span ⟨i * j, mul_mem_mul hi hj, RingHom.map_mul map_f i j⟩

end FractionalIdeal
