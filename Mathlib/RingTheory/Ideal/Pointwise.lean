/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Ring.Action.End
import Mathlib.RingTheory.Ideal.Maps

/-! # Pointwise instances on `Ideal`s

This file provides the action `Ideal.pointwiseMulAction` which morally matches the action of
`mulActionSet` (though here an extra `Ideal.span` is inserted).

This actions is available in the `Pointwise` locale.

## Implementation notes

This file is similar (but not identical) to `Mathlib/Algebra/Ring/Subsemiring/Pointwise.lean`.
Where possible, try to keep them in sync.

-/


open Set

variable {M R : Type*}

namespace Ideal

section Monoid

variable [Monoid M] [Semiring R] [MulSemiringAction M R]

/-- The action on an ideal corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
protected def pointwiseDistribMulAction : DistribMulAction M (Ideal R) where
  smul a := Ideal.map (MulSemiringAction.toRingHom _ _ a)
  one_smul I :=
    congr_arg (I.map ·) (RingHom.ext <| one_smul M) |>.trans I.map_id
  mul_smul _ _ I :=
    congr_arg (I.map ·) (RingHom.ext <| mul_smul _ _) |>.trans (I.map_map _ _).symm
  smul_zero _ := Ideal.map_bot
  smul_add _ I J := Ideal.map_sup _ I J

scoped[Pointwise] attribute [instance] Ideal.pointwiseDistribMulAction

open Pointwise

/-- The action on an ideal corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
protected def pointwiseMulSemiringAction {R : Type*} [CommRing R] [MulSemiringAction M R] :
    MulSemiringAction M (Ideal R) where
  smul_one a := by simp only [Ideal.one_eq_top]; exact Ideal.map_top _
  smul_mul a I J := Ideal.map_mul (MulSemiringAction.toRingHom _ _ a) I J

scoped[Pointwise] attribute [instance] Ideal.pointwiseMulSemiringAction

theorem pointwise_smul_def {a : M} (S : Ideal R) :
    a • S = S.map (MulSemiringAction.toRingHom _ _ a) :=
  rfl

-- note: unlike with `Subring`, `pointwise_smul_toAddSubgroup` wouldn't be true

theorem smul_mem_pointwise_smul (m : M) (r : R) (S : Ideal R) : r ∈ S → m • r ∈ m • S :=
  fun h => subset_span <| Set.smul_mem_smul_set h

instance : CovariantClass M (Ideal R) HSMul.hSMul LE.le :=
  ⟨fun _ _ => map_mono⟩

-- note: unlike with `Subring`, `mem_smul_pointwise_iff_exists` wouldn't be true

@[simp]
theorem smul_bot (a : M) : a • (⊥ : Ideal R) = ⊥ :=
  map_bot

theorem smul_sup (a : M) (S T : Ideal R) : a • (S ⊔ T) = a • S ⊔ a • T :=
  map_sup _ _ _

theorem smul_closure (a : M) (s : Set R) : a • span s = span (a • s) :=
  Ideal.map_span _ _

instance pointwise_central_scalar [MulSemiringAction Mᵐᵒᵖ R] [IsCentralScalar M R] :
    IsCentralScalar M (Ideal R) :=
  ⟨fun _ S => (congr_arg fun f => S.map f) <| RingHom.ext <| op_smul_eq_smul _⟩

@[simp]
theorem pointwise_smul_toAddSubmonoid (a : M) (S : Ideal R)
    (ha : Function.Surjective fun r : R => a • r) :
    (a • S).toAddSubmonoid = a • S.toAddSubmonoid := by
  ext
  exact Ideal.mem_map_iff_of_surjective _ <| by exact ha

@[simp]
theorem pointwise_smul_toAddSubgroup {R : Type*} [Ring R] [MulSemiringAction M R]
    (a : M) (S : Ideal R) (ha : Function.Surjective fun r : R => a • r)  :
    (a • S).toAddSubgroup = a • S.toAddSubgroup := by
  ext
  exact Ideal.mem_map_iff_of_surjective _ <| by exact ha

@[deprecated (since := "2025-07-08")]
alias pointwise_smul_toAddSubGroup := pointwise_smul_toAddSubgroup

end Monoid

section Group

variable [Group M] [Semiring R] [MulSemiringAction M R]

open Pointwise

theorem pointwise_smul_eq_comap {a : M} (S : Ideal R) :
    a • S = S.comap (MulSemiringAction.toRingAut _ _ a).symm := by
  ext
  simp [pointwise_smul_def]
  rfl

@[simp]
theorem smul_mem_pointwise_smul_iff {a : M} {S : Ideal R} {x : R} : a • x ∈ a • S ↔ x ∈ S :=
  ⟨fun h => by simpa using smul_mem_pointwise_smul a⁻¹ _ _ h, smul_mem_pointwise_smul _ _ _⟩

theorem mem_pointwise_smul_iff_inv_smul_mem {a : M} {S : Ideal R} {x : R} :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  ⟨fun h => by simpa using smul_mem_pointwise_smul a⁻¹ _ _ h,
    fun h => by simpa using smul_mem_pointwise_smul a _ _ h⟩

theorem mem_inv_pointwise_smul_iff {a : M} {S : Ideal R} {x : R} : x ∈ a⁻¹ • S ↔ a • x ∈ S := by
  rw [mem_pointwise_smul_iff_inv_smul_mem, inv_inv]

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff {a : M} {S T : Ideal R} : a • S ≤ a • T ↔ S ≤ T :=
  ⟨fun h => by simpa using smul_mono_right a⁻¹ h, fun h => smul_mono_right a h⟩

theorem pointwise_smul_subset_iff {a : M} {S T : Ideal R} : a • S ≤ T ↔ S ≤ a⁻¹ • T := by
  rw [← pointwise_smul_le_pointwise_smul_iff (a := a⁻¹), inv_smul_smul]

theorem subset_pointwise_smul_iff {a : M} {S T : Ideal R} : S ≤ a • T ↔ a⁻¹ • S ≤ T := by
  rw [← pointwise_smul_le_pointwise_smul_iff (a := a⁻¹), inv_smul_smul]

instance IsPrime.smul {I : Ideal R} [H : I.IsPrime] (g : M) : (g • I).IsPrime := by
  rw [I.pointwise_smul_eq_comap]
  apply H.comap

@[simp]
theorem IsPrime.smul_iff {I : Ideal R} (g : M) : (g • I).IsPrime ↔ I.IsPrime :=
  ⟨fun H ↦ inv_smul_smul g I ▸ H.smul g⁻¹, fun H ↦ H.smul g⟩

/-! TODO: add `equivSMul` like we have for subgroup. -/

end Group

end Ideal
