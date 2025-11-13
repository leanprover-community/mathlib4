/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Yury Kudryashov, Joseph Myers, Heather Macbeth, Kim Morrison, Yaël Dillies
-/
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.Group.Torsion
import Mathlib.Tactic.Contrapose

/-!
# `NoZeroSMulDivisors`

This file defines the `NoZeroSMulDivisors` class, and includes some tests
for the vanishing of elements (especially in modules over division rings).

## TODO

`NoZeroSMulDivisors` is mathematically incorrect for semimodules. Replace it with a new typeclass
`Module.IsTorsionFree`, cf https://github.com/kbuzzard/ClassFieldTheory. Torsion-free monoids have
seen the same change happen already.
-/

assert_not_exists RelIso Multiset Set.indicator Pi.single_smul₀ Ring Module

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

theorem smul_ne_zero [Zero R] [Zero M] [SMul R M] [NoZeroSMulDivisors R M] {c : R} {x : M}
    (hc : c ≠ 0) (hx : x ≠ 0) : c • x ≠ 0 := fun h =>
  (eq_zero_or_eq_zero_of_smul_eq_zero h).elim hc hx

theorem noZeroSMulDivisors_iff_right_eq_zero_of_smul [Zero R] [Zero M] [SMul R M] :
    NoZeroSMulDivisors R M ↔ ∀ r : R, r ≠ 0 → ∀ m : M, r • m = 0 → m = 0 := by
  simp_rw [noZeroSMulDivisors_iff, or_iff_not_imp_left]
  exact ⟨fun h r hr m eq ↦ h eq hr, fun h r m eq hr ↦ h r hr m eq⟩

section SMulWithZero

variable [Zero R] [Zero M] [SMulWithZero R M] [NoZeroSMulDivisors R M] {c : R} {x : M}

@[simp]
theorem smul_eq_zero : c • x = 0 ↔ c = 0 ∨ x = 0 :=
  ⟨eq_zero_or_eq_zero_of_smul_eq_zero, fun h =>
    h.elim (fun h => h.symm ▸ zero_smul R x) fun h => h.symm ▸ smul_zero c⟩

theorem smul_ne_zero_iff : c • x ≠ 0 ↔ c ≠ 0 ∧ x ≠ 0 := by rw [Ne, smul_eq_zero, not_or]

lemma smul_eq_zero_iff_left (hx : x ≠ 0) : c • x = 0 ↔ c = 0 := by simp [hx]
lemma smul_eq_zero_iff_right (hc : c ≠ 0) : c • x = 0 ↔ x = 0 := by simp [hc]
lemma smul_ne_zero_iff_left (hx : x ≠ 0) : c • x ≠ 0 ↔ c ≠ 0 := by simp [hx]
lemma smul_ne_zero_iff_right (hc : c ≠ 0) : c • x ≠ 0 ↔ x ≠ 0 := by simp [hc]

end SMulWithZero

instance IsAddTorsionFree.to_noZeroSMulDivisors_nat [AddMonoid M] [IsAddTorsionFree M] :
    NoZeroSMulDivisors ℕ M where
  eq_zero_or_eq_zero_of_smul_eq_zero {n x} hx := by
    contrapose! hx; simpa using (nsmul_right_injective hx.1).ne hx.2

instance IsAddTorsionFree.to_noZeroSMulDivisors_int [AddGroup G] [IsAddTorsionFree G] :
    NoZeroSMulDivisors ℤ G where
  eq_zero_or_eq_zero_of_smul_eq_zero {n x} hx := by
    contrapose! hx; simpa using (zsmul_right_injective hx.1).ne hx.2

@[simp]
lemma noZeroSMulDivisors_nat_iff_isAddTorsionFree [AddCommGroup G] :
    NoZeroSMulDivisors ℕ G ↔ IsAddTorsionFree G where
  mp _ := by
    refine ⟨fun n hn a b hab ↦ ?_⟩
    simp only [← sub_eq_zero (a := n • a), ← nsmul_sub] at hab
    simpa [sub_eq_zero] using (smul_eq_zero_iff_right hn).1 hab
  mpr _ := inferInstance

@[simp]
lemma noZeroSMulDivisors_int_iff_isAddTorsionFree [AddCommGroup G] :
    NoZeroSMulDivisors ℤ G ↔ IsAddTorsionFree G where
  mp _ := by
    refine ⟨fun n hn a b hab ↦ ?_⟩
    simp only [← sub_eq_zero (a := (n : ℤ) • a), ← zsmul_sub, ← natCast_zsmul] at hab
    simpa [sub_eq_zero] using (smul_eq_zero_iff_right <| Int.natCast_ne_zero.2 hn).1 hab
  mpr _ := inferInstance

alias ⟨IsAddTorsionFree.of_noZeroSMulDivisors_nat, _⟩ := noZeroSMulDivisors_nat_iff_isAddTorsionFree
alias ⟨IsAddTorsionFree.of_noZeroSMulDivisors_int, _⟩ := noZeroSMulDivisors_int_iff_isAddTorsionFree
