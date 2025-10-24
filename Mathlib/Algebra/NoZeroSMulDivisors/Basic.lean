/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Yury Kudryashov, Joseph Myers, Heather Macbeth, Kim Morrison, Yaël Dillies
-/
import Mathlib.Algebra.GroupWithZero.Action.Units
import Mathlib.Algebra.Module.End
import Mathlib.Algebra.NoZeroSMulDivisors.Defs

/-!
# `NoZeroSMulDivisors`

This file defines the `NoZeroSMulDivisors` class, and includes some tests
for the vanishing of elements (especially in modules over division rings).
-/

assert_not_exists Multiset Set.indicator Pi.single_smul₀ Field

section NoZeroSMulDivisors

variable {R M : Type*}

section Module

section Nat

theorem Nat.noZeroSMulDivisors
    (R) (M) [Semiring R] [CharZero R] [AddCommMonoid M] [Module R M] [NoZeroSMulDivisors R M] :
    NoZeroSMulDivisors ℕ M where
  eq_zero_or_eq_zero_of_smul_eq_zero {c x} := by rw [← Nat.cast_smul_eq_nsmul R, smul_eq_zero]; simp

end Nat

variable [Semiring R]
variable (R M)

/-- If `M` is an `R`-module with one and `M` has characteristic zero, then `R` has characteristic
zero as well. Usually `M` is an `R`-algebra. -/
theorem CharZero.of_module (M) [AddCommMonoidWithOne M] [CharZero M] [Module R M] : CharZero R := by
  refine ⟨fun m n h => @Nat.cast_injective M _ _ _ _ ?_⟩
  rw [← nsmul_one, ← nsmul_one, ← Nat.cast_smul_eq_nsmul R, ← Nat.cast_smul_eq_nsmul R, h]

end Module

section AddCommGroup

-- `R` can still be a semiring here
variable [Semiring R] [AddCommGroup M] [Module R M]

section SMulInjective

variable (M) in
theorem smul_right_injective [NoZeroSMulDivisors R M] {c : R} (hc : c ≠ 0) :
    Function.Injective (c • · : M → M) :=
  (injective_iff_map_eq_zero (smulAddHom R M c)).2 fun _ ha => (smul_eq_zero.mp ha).resolve_left hc

theorem smul_right_inj [NoZeroSMulDivisors R M] {c : R} (hc : c ≠ 0) {x y : M} :
    c • x = c • y ↔ x = y :=
  (smul_right_injective M hc).eq_iff

end SMulInjective
end AddCommGroup

section Module

variable [Ring R] [AddCommGroup M] [Module R M]

section SMulInjective

variable (R)
variable [NoZeroSMulDivisors R M]

theorem smul_left_injective {x : M} (hx : x ≠ 0) : Function.Injective fun c : R => c • x :=
  fun c d h =>
  sub_eq_zero.mp
    ((smul_eq_zero.mp
          (calc
            (c - d) • x = c • x - d • x := sub_smul c d x
            _ = 0 := sub_eq_zero.mpr h
            )).resolve_right
      hx)

end SMulInjective

instance [NoZeroSMulDivisors ℤ M] : NoZeroSMulDivisors ℕ M :=
  ⟨fun {c x} hcx ↦ by rwa [← Nat.cast_smul_eq_nsmul ℤ, smul_eq_zero, Nat.cast_eq_zero] at hcx⟩

variable (R M)

theorem NoZeroSMulDivisors.int_of_charZero
    (R) (M) [Ring R] [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M] [CharZero R] :
    NoZeroSMulDivisors ℤ M :=
  ⟨fun {z x} h ↦ by simpa [← smul_one_smul R z x] using h⟩

/-- Only a ring of characteristic zero can have a non-trivial module without additive or
scalar torsion. -/
theorem CharZero.of_noZeroSMulDivisors [Nontrivial M] [NoZeroSMulDivisors ℤ M] : CharZero R := by
  refine ⟨fun {n m h} ↦ ?_⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  replace h : (n : ℤ) • x = (m : ℤ) • x := by simp [← Nat.cast_smul_eq_nsmul R, h]
  simpa using smul_left_injective ℤ hx h

instance [AddCommGroup M] [NoZeroSMulDivisors ℤ M] : NoZeroSMulDivisors ℕ M :=
  ⟨fun {c x} hcx ↦ by rwa [← Nat.cast_smul_eq_nsmul ℤ c x, smul_eq_zero, Nat.cast_eq_zero] at hcx⟩

end Module

section GroupWithZero

variable [GroupWithZero R] [AddMonoid M] [DistribMulAction R M]

-- see note [lower instance priority]
/-- This instance applies to `DivisionSemiring`s, in particular `NNReal` and `NNRat`. -/
instance (priority := 100) GroupWithZero.toNoZeroSMulDivisors : NoZeroSMulDivisors R M :=
  ⟨fun {a _} h ↦ or_iff_not_imp_left.2 fun ha ↦ (smul_eq_zero_iff_eq <| Units.mk0 a ha).1 h⟩

end GroupWithZero

end NoZeroSMulDivisors
