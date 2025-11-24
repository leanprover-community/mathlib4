/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.GroupWithZero.Regular
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.Algebra.Regular.Opposite
public import Mathlib.Algebra.Regular.SMul

/-!
# Torsion-free modules

This files defines a torsion-free `R`-(semi)module `M` as a (semi)module where scalar multiplication
by a regular element `r : R` is injective as a map `M → M`.

In the case of a module (group over a ring), this is equivalent to saying that `r • m = 0` for
some `r : R`, `m : M` implies that `r` is a zero-divisor.
If furthermore the base ring is a domain, this is equivalent to the naïve
`r • m = 0 ↔ r = 0 ∨ m = 0` definition.
-/

@[expose] public section

open Module

variable {R S M N : Type*}

section Semiring
variable [Semiring R] [Semiring S]

section AddCommMonoid
variable [AddCommMonoid M] [Module R M] [Module S M] [AddCommMonoid N] [Module R N]
  {r : R} {m m₁ m₂ : M}

variable (R M) in
/-- A `R`-module `M` is torsion-free if scalar multiplication by an element `r : R` is injective if
multiplication (on `R`) by `r` is.

For domains, this is equivalent to the usual condition of `r • m = 0 → r = 0 ∨ m = 0`.
See `smul_eq_zero`. -/
class Module.IsTorsionFree where
  isSMulRegular ⦃r : R⦄ : IsRegular r → IsSMulRegular M r

alias IsRegular.isSMulRegular := IsTorsionFree.isSMulRegular

instance : IsTorsionFree R R where isSMulRegular _r hr := hr.1
instance : IsTorsionFree Rᵐᵒᵖ R where isSMulRegular _r hr := hr.unop.2

/-- Pullback an `IsTorsionFree` instance along an injective function. -/
lemma Function.Injective.moduleIsTorsionFree [IsTorsionFree R N] (f : M → N) (hf : f.Injective)
    (smul : ∀ (r : R) (m : M), f (r • m) = r • f m) : IsTorsionFree R M where
  isSMulRegular r hr m₁ m₂ hm := hf <| hr.isSMulRegular <| by simpa [smul] using congr(f $hm)

instance IsAddTorsionFree.to_isTorsionFree_nat [IsAddTorsionFree M] : IsTorsionFree ℕ M where
  isSMulRegular n hn := nsmul_right_injective (by simpa [isRegular_iff_ne_zero] using hn)

instance Subsingleton.to_moduleIsTorsionFree [Subsingleton M] : IsTorsionFree R M where
  isSMulRegular _ _ := Function.injective_of_subsingleton _

variable [IsTorsionFree R M]

variable (M) in
protected lemma IsRegular.smul_right_injective (hr : IsRegular r) : ((r • ·) : M → M).Injective :=
  hr.isSMulRegular

@[simp] protected lemma IsRegular.smul_right_inj (hr : IsRegular r) : r • m₁ = r • m₂ ↔ m₁ = m₂ :=
  (hr.smul_right_injective _).eq_iff

@[simp] protected lemma IsRegular.smul_eq_zero_iff_right (hr : IsRegular r) :
    r • m = 0 ↔ m = 0 := by rw [← hr.smul_right_inj (m₁ := m), smul_zero]

protected lemma IsRegular.smul_ne_zero_iff_right (hr : IsRegular r) : r • m ≠ 0 ↔ m ≠ 0 :=
  hr.smul_eq_zero_iff_right.ne

variable (R) in
lemma Module.IsTorsionFree.trans [Module S R] [IsTorsionFree S R] [IsScalarTower S R R]
    [SMulCommClass S R R] [IsScalarTower S R M] : IsTorsionFree S M where
  isSMulRegular s hs x y hxy := by
    refine (?_ : IsRegular (s • 1 : R)).isSMulRegular (by simpa using hxy)
    exact ⟨fun x y hxy ↦ hs.isSMulRegular <| by simpa using hxy,
      fun x y hxy ↦ hs.isSMulRegular <| by simpa using hxy⟩

variable [IsDomain R]

lemma IsSMulRegular.of_ne_zero (hr : r ≠ 0) : IsSMulRegular M r :=
  (isRegular_of_ne_zero hr).isSMulRegular

variable [CharZero R]

variable (R M) in
include R in
lemma IsAddTorsionFree.of_isTorsionFree : IsAddTorsionFree M where
  nsmul_right_injective n hn := by
    simp_rw [← Nat.cast_smul_eq_nsmul R]
    apply IsRegular.smul_right_injective
    simpa [isRegular_iff_ne_zero]

/-- A characteristic zero domain is torsion-free. -/
instance (priority := 100) IsAddTorsionFree.of_isDomain_charZero : IsAddTorsionFree R :=
  .of_isTorsionFree R R

@[simp]
lemma Module.isTorsionFree_nat_iff_isAddTorsionFree : IsTorsionFree ℕ M ↔ IsAddTorsionFree M where
  mp _ := .of_isTorsionFree ℕ _
  mpr _ := inferInstance

end AddCommMonoid

section AddCommGroup
variable [CharZero R] [IsDomain R] [AddCommGroup M] [Module R M] {m : M}

instance [IsAddTorsionFree M] : IsTorsionFree ℤ M where
  isSMulRegular n hn := zsmul_right_injective (by simpa [isRegular_iff_ne_zero] using hn)

@[simp]
lemma Module.isTorsionFree_int_iff_isAddTorsionFree : IsTorsionFree ℤ M ↔ IsAddTorsionFree M where
  mp _ := .of_isTorsionFree ℤ _
  mpr _ := inferInstance

end AddCommGroup
end Semiring
