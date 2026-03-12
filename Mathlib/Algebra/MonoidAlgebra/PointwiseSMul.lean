/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Data.Set.SMulAntidiagonal

/-!
# Scalar multiplication by (additive) monoid rings on formal functions.
Given sets `G` and `P`, with a left-cancellative scalar-multiplication (or vector-addition) of `G`
on `P`, together with a module `V` over a semiring `R`, we define a convolution action of the monoid
algebra `R[G]` on the set of functions `P → V`.
## Definitions
* MonoidAlgebra.smulAntidiagonal : The finset of pairs, whose parts lie in the support of specified
functions, that scalar-multiply to a given element.
* AddMonoidAlgebra.vaddAntidiagonal : The finset of pairs, whose parts lie in the support of
specified functions, that vector-add to a given element.
-/

@[expose] public section

noncomputable section

variable {G P R V : Type*}

namespace MonoidAlgebra

@[to_additive]
theorem finite_smulAntidiagonal [SMul G P] [IsLeftCancelSMul G P] [Semiring R] [Zero V]
    (f : MonoidAlgebra R G) (x : P → V) (p : P) :
    (Set.smulAntidiagonal (SetLike.coe f.support) x.support p).Finite := by
  refine Set.Finite.of_injOn (t := SetLike.coe f.support) (fun _ ⟨h, _⟩ ↦ h) ?_
    f.support.finite_toSet
  intro _ ⟨_, _, hp⟩ gp ⟨_, _, hgp⟩ h
  rw [h, ← hgp] at hp
  exact Prod.ext h (IsLeftCancelSMul.left_cancel gp.1 _ _ hp)

/-- The finset of pairs, whose parts lie in the support of specified functions, that vector-add to
a given element. -/
@[to_additive /-- The finset of pairs, whose parts lie in the support of specified functions, that
scalar-multiply to a given element. -/]
def smulAntidiagonal [SMul G P] [IsLeftCancelSMul G P] [Semiring R] [Zero V]
    (f : MonoidAlgebra R G) (x : P → V) (p : P) : Finset (G × P) :=
  (f.finite_smulAntidiagonal x p).toFinset

@[to_additive]
theorem mem_smulAntidiagonal_iff [SMul G P] [IsLeftCancelSMul G P] [Semiring R] [Zero V]
    (f : MonoidAlgebra R G) (x : P → V) (p : P) (gh : G × P) :
    gh ∈ smulAntidiagonal f x p ↔ f gh.1 ≠ 0 ∧ x gh.2 ≠ 0 ∧ gh.1 • gh.2 = p := by
  simp [smulAntidiagonal]

@[to_additive]
theorem mem_smulAntidiagonal_of_group [Group G] [MulAction G P] [Semiring R] [Zero V]
    (f : MonoidAlgebra R G) (x : P → V) (p : P) (gh : G × P) :
    gh ∈ smulAntidiagonal f x p ↔ f gh.1 ≠ 0 ∧ x gh.2 ≠ 0 ∧ gh.2 = gh.1⁻¹ • p := by
  rw [mem_smulAntidiagonal_iff, eq_inv_smul_iff]

/-- A convolution-type scalar multiplication of the monoid algebra on the set of formal
functions. -/
@[to_additive (dont_translate := R) /-- A convolution-type scalar multiplication of the additive
monoid algebra on the set of formal functions. -/]
scoped instance [SMul G P] [IsLeftCancelSMul G P] [Semiring R] [AddCommMonoid V]
    [SMulWithZero R V] :
    SMul (MonoidAlgebra R G) (P → V) where
  smul f x p := ∑ gh ∈ smulAntidiagonal f x p, f gh.1 • x gh.2

@[to_additive (dont_translate := R) smul_eq]
theorem smul_eq [SMul G P] [IsLeftCancelSMul G P] [Semiring R] [AddCommMonoid V] [SMulWithZero R V]
    (f : MonoidAlgebra R G) (x : P → V) (p : P) :
    (f • x) p = ∑ gh ∈ smulAntidiagonal f x p, f gh.1 • x gh.2 := rfl

@[to_additive (dont_translate := R) smul_apply_addAction]
theorem smul_apply_mulAction [Group G] [MulAction G P] [Semiring R] [AddCommMonoid V]
    [SMulWithZero R V] (f : MonoidAlgebra R G) (x : P → V) (p : P) :
    (f • x) p = ∑ i ∈ f.support, (f i) • x (i⁻¹ • p) := by
  rw [smul_eq, Finset.sum_of_injOn Prod.fst]
  · intro _ h₁ _ h₂ h
    rw [Finset.mem_coe, mem_smulAntidiagonal_of_group] at h₁ h₂
    simp [Prod.ext_iff, h₁.2.2, h₂.2.2, h]
  · intro g hg
    rw [Finset.mem_coe, mem_smulAntidiagonal_iff] at hg
    exact Finset.mem_coe.mpr <| Finsupp.mem_support_iff.mpr hg.1
  · intro g hg hgn
    have h : f g = 0 ∨ x (g⁻¹ • p) = 0 := by
      simpa [mem_smulAntidiagonal_of_group, or_iff_not_imp_left] using hgn
    rcases h with (h | h) <;> simp [h]
  · intro g hg
    rw [mem_smulAntidiagonal_of_group] at hg
    rw [hg.2.2]

@[to_additive (dont_translate := R) smul_eq_addMonoidAlgebra_mul]
theorem smul_eq_MonoidAlgebra_mul [Semiring R] [CancelMonoid G] (a b : MonoidAlgebra R G) :
    a • ⇑b = (a * b : MonoidAlgebra R G) := by
  ext g
  classical
  rw [MonoidAlgebra.smul_eq, MonoidAlgebra.mul_apply, Finsupp.sum]
  simp_rw [Finsupp.sum]
  rw [Finset.sum_sigma', Finset.sum_of_injOn]
  · exact fun (x, y) ↦ ⟨x, y⟩
  · simp
  · intro gh h
    rw [Finset.mem_coe, mem_smulAntidiagonal_iff] at h
    have : b gh.2 ≠ 0 := h.2.1
    simp [h.1, this]
  · intro gh _ h
    simp only [Set.mem_image, Finset.mem_coe, Prod.exists, not_exists, not_and] at h
    contrapose! h
    use gh.fst, gh.snd
    rw [mem_smulAntidiagonal_iff]
    simp only [ne_eq, ite_eq_right_iff, Classical.not_imp] at h
    exact ⟨⟨(by simp [left_ne_zero_of_mul h.2]), right_ne_zero_of_mul h.2, h.1⟩, rfl⟩
  · intro _ h
    rw [mem_smulAntidiagonal_iff, smul_eq_mul] at h
    simp [h.2.2]

end MonoidAlgebra
