/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Data.Finset.SMulAntidiagonal

/-!
# Scalar multiplication by (additive) monoid rings on formal functions.
Given sets `G` and `P`, with a left-cancellative scalar-multiplication (or vector-addition) of `G`
on `P`, together with a module `V` over a semiring `R`, we define a convolution action of the monoid
algebra `R[G]` on the set of functions `P → V`.

-/

@[expose] public section

noncomputable section

variable {G P R V : Type*}

namespace MonoidAlgebra

@[to_additive]
theorem mem_smulAntidiagonal_of_group [Group G] [MulAction G P] [Semiring R] [Zero V]
    (f : R[G]) (x : P → V) (p : P) (gh : G × P) :
    gh ∈ Finset.SMulAntidiagonal p
      (Set.SMulAntidiagonal.finite_of_finite_fst f.support.finite_toSet x.support p) ↔
      f gh.1 ≠ 0 ∧ x gh.2 ≠ 0 ∧ gh.2 = gh.1⁻¹ • p := by
  rw [Finset.mem_smulAntidiagonal, eq_inv_smul_iff, Function.mem_support, Finset.mem_coe,
    Finsupp.mem_support_iff]

/-- A convolution-type scalar multiplication of the monoid algebra on the set of formal
functions. -/
@[to_additive (dont_translate := R) /-- A convolution-type scalar multiplication of the additive
monoid algebra on the set of formal functions. -/]
scoped instance [SMul G P] [IsLeftCancelSMul G P] [Semiring R] [AddCommMonoid V]
    [SMulWithZero R V] :
    SMul (R[G]) (P → V) where
  smul f x p := ∑ gh ∈ Finset.SMulAntidiagonal p
    (Set.SMulAntidiagonal.finite_of_finite_fst f.support.finite_toSet x.support p), f gh.1 • x gh.2

@[to_additive (dont_translate := R) smul_eq]
theorem smul_eq [SMul G P] [IsLeftCancelSMul G P] [Semiring R] [AddCommMonoid V] [SMulWithZero R V]
    (f : R[G]) (x : P → V) (p : P)
    (hp : ((f.support : Set G).smulAntidiagonal (Function.support x) p).Finite :=
      Set.SMulAntidiagonal.finite_of_finite_fst f.support.finite_toSet x.support p) :
    (f • x) p = ∑ gh ∈ Finset.SMulAntidiagonal p hp, f gh.1 • x gh.2 :=
  rfl

@[to_additive (dont_translate := R) smul_apply_addAction]
theorem smul_apply_mulAction [Group G] [MulAction G P] [Semiring R] [AddCommMonoid V]
    [SMulWithZero R V] (f : MonoidAlgebra R G) (x : P → V) (p : P) :
    (f • x) p = ∑ i ∈ f.support, (f i) • x (i⁻¹ • p) := by
  have hp : ((f.support : Set G).smulAntidiagonal (Function.support x) p).Finite :=
    Set.SMulAntidiagonal.finite_of_finite_fst f.support.finite_toSet x.support p
  set s : Set (G × P) := ↑(Finset.SMulAntidiagonal p hp)
  have h₁ : s.InjOn Prod.fst := fun _ h₁ _ h₂ h ↦ by
    rw [Finset.mem_coe, mem_smulAntidiagonal_of_group] at h₁ h₂
    aesop
  have h₂ : s.MapsTo Prod.fst ↑f.support := fun g hg ↦ by aesop
  have h₃ (g : G) (hg : g ∈ f.support) (hgn : g ∉ Prod.fst '' s) : f g • x (g⁻¹ • p) = 0 := by
    obtain (h | h) : f g = 0 ∨ ∀ q, ¬ x q = 0 → ¬g • q = p := by aesop
    · simp [h]
    · have := h (g⁻¹ • p)
      aesop
  rw [smul_eq, Finset.sum_of_injOn Prod.fst h₁ h₂ h₃]
  aesop

end MonoidAlgebra
