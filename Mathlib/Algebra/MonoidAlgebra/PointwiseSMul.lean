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
    (f : MonoidAlgebra R G) (x : P → V) (p : P) (gh : G × P) :
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
    SMul (MonoidAlgebra R G) (P → V) where
  smul f x p := ∑ gh ∈ Finset.SMulAntidiagonal p
    (Set.SMulAntidiagonal.finite_of_finite_fst f.support.finite_toSet x.support p), f gh.1 • x gh.2

@[to_additive (dont_translate := R) smul_eq]
theorem smul_eq [SMul G P] [IsLeftCancelSMul G P] [Semiring R] [AddCommMonoid V] [SMulWithZero R V]
    (f : MonoidAlgebra R G) (x : P → V) (p : P) :
    (f • x) p = ∑ gh ∈ Finset.SMulAntidiagonal p
      ((Set.SMulAntidiagonal.finite_of_finite_fst f.support.finite_toSet x.support p)),
        f gh.1 • x gh.2 :=
  rfl

@[to_additive (dont_translate := R) smul_apply_addAction]
theorem smul_apply_mulAction [Group G] [MulAction G P] [Semiring R] [AddCommMonoid V]
    [SMulWithZero R V] (f : MonoidAlgebra R G) (x : P → V) (p : P) :
    (f • x) p = ∑ i ∈ f.support, (f i) • x (i⁻¹ • p) := by
  rw [smul_eq, Finset.sum_of_injOn Prod.fst]
  · intro _ h₁ _ h₂ h
    rw [Finset.mem_coe, mem_smulAntidiagonal_of_group] at h₁ h₂
    simp [Prod.ext_iff, h₁.2.2, h₂.2.2, h]
  · intro g hg
    rw [Finset.mem_coe, Finset.mem_smulAntidiagonal] at hg
    exact hg.1
  · intro g hg hgn
    have h : f g = 0 ∨ ∀ (x_1 : P), ¬x x_1 = 0 → ¬g • x_1 = p := by
      simpa [← or_iff_not_imp_left] using hgn
    obtain (h | h) := h
    · simp [h]
    · have := h (g⁻¹ • p)
      simp only [smul_inv_smul, not_true_eq_false, imp_false, not_not] at this
      simp [this]
  · intro g hg
    rw [mem_smulAntidiagonal_of_group] at hg
    rw [hg.2.2]

end MonoidAlgebra
