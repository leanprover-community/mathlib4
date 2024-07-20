/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos Fernández
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.LinearAlgebra.Finsupp


/-! # weights of Finsupp functions -/

variable {σ M : Type*} (w : σ → M)

namespace Finsupp

section AddCommMonoid

variable [AddCommMonoid M]
/-- The `weight` of the finitely supported function `s : σ →₀ ℕ`
with respect to `w : σ → M` is the sum `∑(s i)•(w i)`. -/
noncomputable def weight : (σ →₀ ℕ) →+ M :=
  (Finsupp.total σ M ℕ w).toAddMonoidHom

theorem weight_apply (f : σ →₀ ℕ) :
    weight w f = Finsupp.sum f (fun i c => c • w i) := rfl

/-- A weight function is nontorsion if its values are not torsion. -/
class NonTorsionWeight (w : σ → M) : Prop where
  eq_zero_of_smul_eq_zero {n : ℕ} {s : σ} (h : n • w s = 0)  : n = 0

/-- Without zero divisors, nonzero weight is a NonTorsionWeight -/
theorem nonTorsionWeight_of [NoZeroSMulDivisors ℕ M] (hw : ∀ i : σ, w i ≠ 0) :
    NonTorsionWeight w where
  eq_zero_of_smul_eq_zero {n s} h := by
    rw [smul_eq_zero, or_iff_not_imp_right] at h
    exact h (hw s)

theorem NonTorsionWeight.ne_zero [NonTorsionWeight w] (s : σ) :
    w s ≠ 0 := fun h ↦ by
  rw [← one_smul ℕ (w s)] at h
  apply Nat.zero_ne_one.symm
  exact NonTorsionWeight.eq_zero_of_smul_eq_zero h

end AddCommMonoid

section OrderedAddCommMonoid

theorem Nat.le_weight (w : σ → ℕ) (s : σ) (hs : w s ≠ 0) (f : σ →₀ ℕ) :
    f s ≤ weight w f := by
  classical
  simp only [weight_apply, Finsupp.sum]
  by_cases h : s ∈ f.support
  · rw [Finset.sum_eq_add_sum_diff_singleton h]
    refine' le_trans _ (Nat.le_add_right _ _)
    apply Nat.le_mul_of_pos_right
    exact Nat.zero_lt_of_ne_zero hs
  · simp only [not_mem_support_iff] at h
    rw [h]
    apply zero_le

variable [OrderedAddCommMonoid M] (w : σ → M)

instance : SMulPosMono ℕ M := ⟨
  fun b hb m m' h ↦ by
    rw [← Nat.add_sub_of_le h, add_smul]
    exact le_add_of_nonneg_right (nsmul_nonneg hb (m' - m)) ⟩

variable {w} in
theorem le_weight_of_nonneg' (hw : ∀ s, 0 ≤ w s) (s : σ) (f : σ →₀ ℕ) (hs : f s ≠ 0) :
    w s ≤ weight w f := by
  classical
  simp only [weight_apply, Finsupp.sum]
  trans f s • w s
  · apply le_smul_of_one_le_left (hw s)
    exact Nat.one_le_iff_ne_zero.mpr hs
  · rw [← Finsupp.mem_support_iff] at hs
    rw [Finset.sum_eq_add_sum_diff_singleton hs]
    exact le_add_of_nonneg_right <| Finset.sum_nonneg <|
      fun i _ ↦ nsmul_nonneg (hw i) (f i)

end OrderedAddCommMonoid

section CanonicallyOrderedAddCommMonoid

variable {M : Type*} [CanonicallyOrderedAddCommMonoid M] (w : σ → M)

theorem le_weight' (s : σ) (f : σ →₀ ℕ) (hs : f s ≠ 0) :
    w s ≤ weight w f :=
  le_weight_of_nonneg' w (fun _ ↦ zero_le _) s f hs

/-- If `M` is a `CanonicallyOrderedAddCommMonoid`, then the `weightedHomogeneousComponent`
  of weighted degree `0` of a polynomial is its constant coefficient. -/
theorem weight_eq_zero_iff_eq_zero
    (w : σ → M) [NonTorsionWeight w] (f : σ →₀ ℕ) :
    weight w f = 0 ↔ f = 0 := by
  classical
  constructor
  · intro h
    ext s
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    by_contra hs
    apply NonTorsionWeight.ne_zero w _
    rw [← nonpos_iff_eq_zero, ← h]
    exact le_weight' w s f hs
  · intro h
    rw [h, map_zero]

end CanonicallyOrderedAddCommMonoid

/-- The degree of a finsupp function. -/
abbrev degree (d : σ →₀ ℕ) := ∑ i ∈ d.support, d i

lemma degree_eq_zero_iff (d : σ →₀ ℕ) : degree d = 0 ↔ d = 0 := by
  simp only [degree, Finset.sum_eq_zero_iff, Finsupp.mem_support_iff, ne_eq, Decidable.not_imp_self,
    DFunLike.ext_iff, Finsupp.coe_zero, Pi.zero_apply]

theorem degree_zero : degree (0 : σ →₀ ℕ) = 0 := by rw [degree_eq_zero_iff]

theorem degree_eq_weight_one (d : σ →₀ ℕ) :
    degree d = weight 1 d := by
  simp only [degree, weight_apply, Pi.one_apply, smul_eq_mul, mul_one, Finsupp.sum]

theorem le_degree (s : σ) (f : σ →₀ ℕ) : f s ≤ degree f  := by
  rw [degree_eq_weight_one]
  apply Nat.le_weight
  simp only [Pi.one_apply, ne_eq, one_ne_zero, not_false_eq_true]

end Finsupp
