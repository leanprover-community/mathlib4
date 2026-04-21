/-
Copyright (c) 2025 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Fangming Li
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Homogeneous subsemirings of a graded semiring

This file defines homogeneous subsemirings of a graded semiring, as well as operations on them.

## Main definitions

* `HomogeneousSubsemiring 𝒜`: The type of subsemirings which satisfy `SetLike.IsHomogeneous`.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open DirectSum Set SetLike

variable {ι σ A : Type*} [AddMonoid ι] [Semiring A]
variable [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ι → σ) [DecidableEq ι] [GradedRing 𝒜]
variable (R : Subsemiring A)

section HomogeneousDef

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

instance : PartialOrder (HomogeneousSubsemiring 𝒜) := .ofSetLike (HomogeneousSubsemiring 𝒜) A

theorem isHomogeneous (R : HomogeneousSubsemiring 𝒜) :
    IsHomogeneous 𝒜 R := R.is_homogeneous'

instance subsemiringClass : SubsemiringClass (HomogeneousSubsemiring 𝒜) A where
  mul_mem {a} := a.toSubsemiring.mul_mem
  one_mem {a} := a.toSubsemiring.one_mem
  add_mem {a} := a.toSubsemiring.add_mem
  zero_mem {a} := a.toSubsemiring.zero_mem

@[ext]
theorem ext {R S : HomogeneousSubsemiring 𝒜}
    (h : R.toSubsemiring = S.toSubsemiring) : R = S :=
  HomogeneousSubsemiring.toSubsemiring_injective h

theorem ext' {R S : HomogeneousSubsemiring 𝒜}
    (h : ∀ i, ∀ a ∈ 𝒜 i, a ∈ R ↔ a ∈ S) : R = S :=
  AddSubmonoidClass.IsHomogeneous.ext R.2 S.2 h

@[simp high]
theorem mem_iff {R : HomogeneousSubsemiring 𝒜} {a} :
    a ∈ R.toSubsemiring ↔ a ∈ R :=
  Iff.rfl

end HomogeneousSubsemiring

set_option backward.isDefEq.respectTransparency false in
theorem IsHomogeneous.subsemiringClosure {s : Set A}
    (h : ∀ (i : ι) ⦃x : A⦄, x ∈ s → (decompose 𝒜 x i : A) ∈ s) :
    IsHomogeneous 𝒜 (Subsemiring.closure s) := fun i x hx ↦ by
  induction hx using Subsemiring.closure_induction generalizing i with
  | mem _ hx => exact Subsemiring.subset_closure <| h i hx
  | zero => simp
  | one =>
    rw [decompose_one, one_def]
    obtain rfl | h := eq_or_ne i 0 <;> simp [of_eq_of_ne, *]
  | add _ _ _ _ h₁ h₂ => simpa using add_mem (h₁ i) (h₂ i)
  | mul x y _ _ h₁ h₂ =>
    classical
    rw [decompose_mul, DirectSum.mul_eq_dfinsuppSum]
    rw [DFinsupp.sum_apply, DFinsupp.sum, AddSubmonoidClass.coe_finset_sum]
    refine sum_mem fun j _ ↦ ?_
    rw [DFinsupp.sum_apply, DFinsupp.sum, AddSubmonoidClass.coe_finset_sum]
    refine sum_mem fun k _ ↦ ?_
    obtain rfl | h := eq_or_ne i (j + k) <;> simp [of_eq_of_ne, mul_mem, *]

theorem IsHomogeneous.subsemiringClosure_of_isHomogeneousElem {s : Set A}
    (h : ∀ x ∈ s, IsHomogeneousElem 𝒜 x) :
    IsHomogeneous 𝒜 (Subsemiring.closure s) := by
  rw [← Subsemiring.closure_insert_zero s]
  refine IsHomogeneous.subsemiringClosure fun i x hx ↦ ?_
  obtain rfl | hx := mem_insert_iff.mp hx
  · simp
  · obtain ⟨j, hj⟩ := h x hx
    obtain rfl | h := eq_or_ne i j <;> simp [decompose_of_mem _ hj, of_eq_of_ne, *]

end HomogeneousDef

section HomogeneousCore

/-- For any subsemiring `R`, not necessarily homogeneous, `R.homogeneousCore 𝒜` is the largest
homogeneous subsemiring contained in `R`. -/
def Subsemiring.homogeneousCore : HomogeneousSubsemiring 𝒜 where
  __ := Subsemiring.closure ((↑) '' (((↑) : Subtype (IsHomogeneousElem 𝒜) → A) ⁻¹' R))
  is_homogeneous' := IsHomogeneous.subsemiringClosure_of_isHomogeneousElem fun x ↦ by
    rintro ⟨x, _, rfl⟩; exact x.2

theorem Subsemiring.homogeneousCore_mono : Monotone (Subsemiring.homogeneousCore 𝒜) :=
  fun _ _ h => Subsemiring.closure_mono <| Set.image_mono <| fun _ ↦ @h _

theorem Subsemiring.toSubsemiring_homogeneousCore_le : (R.homogeneousCore 𝒜).toSubsemiring ≤ R :=
  Subsemiring.closure_le.2 <| image_preimage_subset _ _

end HomogeneousCore

section IsHomogeneousSubsemiringDefs

theorem Subsemiring.isHomogeneous_iff_forall_subset :
    SetLike.IsHomogeneous 𝒜 R ↔ ∀ i, (R : Set A) ⊆ GradedRing.proj 𝒜 i ⁻¹' (R : Set A) :=
  Iff.rfl

theorem Subsemiring.isHomogeneous_iff_subset_iInter :
    SetLike.IsHomogeneous 𝒜 R ↔ (R : Set A) ⊆ ⋂ i, GradedRing.proj 𝒜 i ⁻¹' R :=
  subset_iInter_iff.symm

end IsHomogeneousSubsemiringDefs
