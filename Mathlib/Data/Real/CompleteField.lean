/-
Copyright (c) 2024 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
module

public import Mathlib.Algebra.Order.CompleteField
public import Mathlib.Data.Real.Sqrt

/-!
# The reals are a conditionally complete linearly ordered field

TODO: rename this file
-/

@[expose] public section

noncomputable instance Real.uniqueOrderRingHom (α : Type*)
    [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Archimedean α] : Unique (α →+*o ℝ) :=
  ConditionallyCompleteLinearOrderedField.uniqueOrderRingHom _ _

instance Real.uniqueOrderRingIso : Unique (ℝ ≃+*o ℝ) :=
  uniqueOfSubsingleton <| OrderRingIso.refl ℝ

theorem ringHom_monotone {R S : Type*} [Ring R] [PartialOrder R] [IsOrderedAddMonoid R]
    [Ring S] [LinearOrder S] [IsOrderedAddMonoid S] [PosMulMono S]
    (hR : ∀ r : R, 0 ≤ r → IsSquare r) (f : R →+* S) : Monotone f :=
  (monotone_iff_map_nonneg f).2 fun r h => by
    obtain ⟨s, rfl⟩ := hR r h; rw [map_mul]; apply mul_self_nonneg

/-- There exists no nontrivial ring homomorphism `ℝ →+* ℝ`. -/
instance Real.RingHom.unique : Unique (ℝ →+* ℝ) where
  default := RingHom.id ℝ
  uniq f := congr_arg OrderRingHom.toRingHom (@Subsingleton.elim (ℝ →+*o ℝ) _
      ⟨f, ringHom_monotone (fun _ ↦ Real.isSquare_iff.mpr) f⟩ default)

@[simp]
theorem Real.ringHom_apply {F : Type*} [FunLike F ℝ ℝ] [RingHomClass F ℝ ℝ] (f : F) (r : ℝ) :
    f r = r :=
  DFunLike.congr_fun (Unique.eq_default (RingHomClass.toRingHom f)) r
