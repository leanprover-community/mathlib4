/-
Copyright (c) 2025 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Fangming Li
-/
import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Homogeneous subsemirings of a graded semiring

This file defines homogeneous subsemirings of a graded semiring, as well as operations on them.

## Main definitions

* `HomogeneousSubsemiring 𝒜`: The type of subsemirings which satisfy `SetLike.IsHomogeneous`.
-/

open DirectSum Set SetLike

section HomogeneousDef

variable {ι σ A : Type*} [AddMonoid ι] [Semiring A]
variable [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ι → σ) [DecidableEq ι] [GradedRing 𝒜]
variable (R : Subsemiring A)

/-- A subsemiring `R` is said to be homogeneous if for every `a ∈ R`, all homogeneous components of
`a` are in `R`. -/
def Subsemiring.IsHomogeneous : Prop :=
  SetLike.IsHomogeneous 𝒜 R

variable {R} in
theorem DirectSum.SetLike.IsHomogeneous.mem_iff (hR : IsHomogeneous 𝒜 R) {a} :
    a ∈ R ↔ ∀ i, (decompose 𝒜 a i : A) ∈ R :=
  AddSubmonoidClass.IsHomogeneous.mem_iff 𝒜 _ hR

/-- A `HomogeneousSubsemiring` is a `Subsemiring` that satisfies `IsHomogeneous`. -/
structure HomogeneousSubsemiring extends Subsemiring A where
  is_homogeneous' : IsHomogeneous 𝒜 toSubsemiring

variable {𝒜}

namespace HomogeneousSubsemiring

theorem toSubsemiring_injective :
    (toSubsemiring : HomogeneousSubsemiring 𝒜 → Subsemiring A).Injective :=
  fun ⟨x, hx⟩ ⟨y, hy⟩ => fun (h : x = y) => by simp [h]

instance setLike : SetLike (HomogeneousSubsemiring 𝒜) A where
  coe x := x.carrier
  coe_injective' _ _ h := toSubsemiring_injective <| SetLike.coe_injective h

theorem isHomogeneous (R : HomogeneousSubsemiring 𝒜) :
    IsHomogeneous 𝒜 R := R.is_homogeneous'

instance HomogeneousSubsemiring.subsemiringClass :
    SubsemiringClass (HomogeneousSubsemiring 𝒜) A where
  mul_mem {a} := a.toSubsemiring.mul_mem
  one_mem {a} := a.toSubsemiring.one_mem
  add_mem {a} := a.toSubsemiring.add_mem
  zero_mem {a} := a.toSubsemiring.zero_mem

@[ext]
theorem HomogeneousSubsemiring.ext {R S : HomogeneousSubsemiring 𝒜}
    (h : R.toSubsemiring = S.toSubsemiring) : R = S :=
  HomogeneousSubsemiring.toSubsemiring_injective h

theorem HomogeneousSubsemiring.ext' {R S : HomogeneousSubsemiring 𝒜}
    (h : ∀ i, ∀ a ∈ 𝒜 i, a ∈ R ↔ a ∈ S) : R = S := by
  ext
  rw [R.isHomogeneous.mem_iff, S.isHomogeneous.mem_iff]
  apply forall_congr'
  exact fun i ↦ h i _ (decompose 𝒜 _ i).2

@[simp high]
theorem mem_iff {R : HomogeneousSubsemiring 𝒜} {a} :
    a ∈ R.toSubsemiring ↔ a ∈ R :=
  Iff.rfl

end HomogeneousDef

section HomogeneousCore

variable {ι σ A : Type*} [Semiring A] [SetLike σ A]
variable (𝒜 : ι → σ) (R : Subsemiring A)

/-- For any subsemiring `R`, not necessarily homogeneous, `R.homogeneousCore' 𝒜` is the largest
homogeneous subsemiring contained in `R`, as a subsemiring. -/
def Subsemiring.homogeneousCore' : Subsemiring A :=
  Subsemiring.closure ((↑) '' (((↑) : Subtype (IsHomogeneousElem 𝒜) → A) ⁻¹' R))

theorem Subsemiring.homogeneousCore'_mono : Monotone (Subsemiring.homogeneousCore' 𝒜) :=
  fun _ _ h => Subsemiring.closure_mono <| Set.image_subset _ fun _ => @h _

theorem Subsemiring.homogeneousCore'_le : R.homogeneousCore' 𝒜 ≤ R :=
  Subsemiring.closure_le.2 <| image_preimage_subset _ _

end HomogeneousCore

section IsHomogeneousSubsemiringDefs

variable {ι σ A : Type*} [AddMonoid ι] [Semiring A]
variable [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ι → σ) [DecidableEq ι] [GradedRing 𝒜]
variable (R : Subsemiring A)

theorem Subsemiring.isHomogeneous_iff_forall_subset :
    R.IsHomogeneous 𝒜 ↔ ∀ i, (R : Set A) ⊆ GradedRing.proj 𝒜 i ⁻¹' (R : Set A) :=
  Iff.rfl

theorem Subsemiring.isHomogeneous_iff_subset_iInter :
    R.IsHomogeneous 𝒜 ↔ (R : Set A) ⊆ ⋂ i, GradedRing.proj 𝒜 i ⁻¹' R :=
  subset_iInter_iff.symm

end IsHomogeneousSubsemiringDefs
