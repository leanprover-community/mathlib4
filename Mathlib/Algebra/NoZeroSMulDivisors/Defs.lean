/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Yury Kudryashov, Joseph Myers, Heather Macbeth, Kim Morrison, Yaël Dillies
-/
module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Tactic.Contrapose

/-!
# `NoZeroSMulDivisors`

This file defines the `NoZeroSMulDivisors` class, and includes some tests
for the vanishing of elements (especially in modules over division rings).

## Usage notes

Note that `NoZeroSMulDivisors` is deprecated in favor of `Module.IsTorsionFree`, which is the
mathematically correct generalisation to semimodules.
-/

@[expose] public section

assert_not_exists RelIso Multiset Set.indicator Pi.single_smul₀

variable {R M G : Type*}

/-- `NoZeroSMulDivisors R M` states that a scalar multiple is `0` only if either argument is `0`.
This is a version of saying that `M` is torsion free, without assuming `R` is zero-divisor free.

The main application of `NoZeroSMulDivisors R M`, when `M` is a module,
is the result `smul_eq_zero`: a scalar multiple is `0` iff either argument is `0`.

It is a generalization of the `NoZeroDivisors` class to heterogeneous multiplication.
-/
@[mk_iff]
class NoZeroSMulDivisors (R M : Type*) [Zero R] [Zero M] [SMul R M] : Prop where
  /-- If scalar multiplication yields zero, either the scalar or the vector was zero. -/
  eq_zero_or_eq_zero_of_smul_eq_zero : ∀ {c : R} {x : M}, c • x = 0 → c = 0 ∨ x = 0

export NoZeroSMulDivisors (eq_zero_or_eq_zero_of_smul_eq_zero)

/-- Pullback a `NoZeroSMulDivisors` instance along an injective function. -/
theorem Function.Injective.noZeroSMulDivisors {R M N : Type*} [Zero R] [Zero M] [Zero N]
    [SMul R M] [SMul R N] [NoZeroSMulDivisors R N] (f : M → N) (hf : Function.Injective f)
    (h0 : f 0 = 0) (hs : ∀ (c : R) (x : M), f (c • x) = c • f x) : NoZeroSMulDivisors R M :=
  ⟨fun {_ _} h =>
    Or.imp_right (@hf _ _) <| h0.symm ▸ eq_zero_or_eq_zero_of_smul_eq_zero (by rw [← hs, h, h0])⟩

-- See note [lower instance priority]
instance (priority := 100) NoZeroDivisors.toNoZeroSMulDivisors [Zero R] [Mul R]
    [NoZeroDivisors R] : NoZeroSMulDivisors R R :=
  ⟨fun {_ _} => eq_zero_or_eq_zero_of_mul_eq_zero⟩

instance [Semiring R] [IsDomain R] [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M] :
    Module.IsTorsionFree R M where
  isSMulRegular r hr m₁ m₂ hm := by
    dsimp at hm
    rw [← sub_eq_zero, ← smul_sub] at hm
    simpa [hr.ne_zero, sub_eq_zero] using eq_zero_or_eq_zero_of_smul_eq_zero hm

theorem noZeroSMulDivisors_iff_right_eq_zero_of_smul [Zero R] [Zero M] [SMul R M] :
    NoZeroSMulDivisors R M ↔ ∀ r : R, r ≠ 0 → ∀ m : M, r • m = 0 → m = 0 := by
  simp_rw [noZeroSMulDivisors_iff, or_iff_not_imp_left]
  exact ⟨fun h r hr m eq ↦ h eq hr, fun h r m eq hr ↦ h r hr m eq⟩

instance IsAddTorsionFree.to_noZeroSMulDivisors_nat [AddMonoid M] [IsAddTorsionFree M] :
    NoZeroSMulDivisors ℕ M where
  eq_zero_or_eq_zero_of_smul_eq_zero {n x} hx := by
    contrapose! hx; simpa using (nsmul_right_injective hx.1).ne hx.2

instance IsAddTorsionFree.to_noZeroSMulDivisors_int [AddGroup G] [IsAddTorsionFree G] :
    NoZeroSMulDivisors ℤ G where
  eq_zero_or_eq_zero_of_smul_eq_zero {n x} hx := by
    contrapose! hx; simpa using (zsmul_right_injective hx.1).ne hx.2
