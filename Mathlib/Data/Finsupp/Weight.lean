/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # weights of Finsupp functions

The theory of multivariate polynomials and power series is built
on the type `σ →₀ ℕ` which gives the exponents of the monomials.
Many aspects of the theory (degree, order, graded ring structure)
require to classify these exponents according to their total sum
`∑  i, f i`, or variants, and this files provides some API for that.

## Weight

We fix a type `σ`, a semiring `N`, a `N`-module `M`,
as well as a function `w : σ → M`. (The important case is `N = ℕ`.)

- `Finsupp.weight` of a finitely supported function `f : σ →₀ N`
with respect to `w`: it is the sum `∑ (f i) • (w i)`.
It is an `AddMonoidHom` map defined using `Finsupp.linearCombination`.

- `Finsupp.le_weight` says that `f s ≤ f.weight w` when `M = ℕ`

- `Finsupp.le_weight_of_ne_zero` says that `w s ≤ f.weight w`
for `OrderedAddCommMonoid M`, when `f s ≠ 0` and all `w i` are nonnegative.

- `Finsupp.le_weight_of_ne_zero'` is the same statement for `CanonicallyOrderedAddCommMonoid M`.

- `NonTorsionWeight`: all values `w s` are non torsion in `M`.

- `Finsupp.weight_eq_zero_iff_eq_zero` says that `f.weight w = 0` iff
`f = 0` for `NonTorsionWeight w` and `CanonicallyOrderedAddCommMonoid M`.

- For `w : σ → ℕ` and `Finite σ`, `Finsupp.finite_of_nat_weight_le` proves that
there are finitely many `f : σ →₀ ℕ` of bounded weight.

## Degree

- `Finsupp.degree f` is the sum of all `f s`, for `s ∈ f.support`.
  The present choice is to have it defined as a function.

- `Finsupp.degree_eq_zero_iff` says that `f.degree = 0` iff `f = 0`.

- `Finsupp.le_degree` says that `f s ≤ f.degree`.

- `Finsupp.degree_eq_weight_one` says `f.degree = f.weight 1` when `N` is a semiring.
This is useful to access the additivity properties of `Finsupp.degree`

- For `Finite σ`, `Finsupp.finite_of_degree_le` proves that
there are finitely many `f : σ →₀ ℕ` of bounded degree.


## TODO

* Maybe `Finsupp.weight w` and `Finsupp.degree` should have similar types,
both `AddCommMonoidHom` or both functions.

-/

variable {σ M N : Type*} [Semiring N] (w : σ → M)

namespace Finsupp

section AddCommMonoid

variable [AddCommMonoid M] [Module N M]
/-- The `weight` of the finitely supported function `f : σ →₀ N`
with respect to `w : σ → M` is the sum `∑(f i)•(w i)`. -/
noncomputable def weight : (σ →₀ N) →+ M :=
  (Finsupp.linearCombination N w).toAddMonoidHom

@[deprecated weight (since := "2024-07-20")]
alias _root_.MvPolynomial.weightedDegree := weight

theorem weight_apply (f : σ →₀ N) :
    weight w f = Finsupp.sum f (fun i c => c • w i) := rfl

@[deprecated weight_apply (since := "2024-07-20")]
alias _root_.MvPolynomial.weightedDegree_apply := weight_apply

theorem weight_single_index (s : σ) (c : M) (f : σ →₀ N) :
    weight (single s c) f = f s • c := by
  rw [weight_apply, sum_eq_single s]
  · simp only [single_eq_same]
  · intro i _ hi
    rw [single_eq_of_ne hi.symm, smul_zero]
  · intro _
    simp only [single_eq_same, zero_smul]

theorem weight_single_one_apply (s : σ) (f : σ →₀ N) :
    weight (single s 1) f = f s := by
  rw [weight_single_index, smul_eq_mul, mul_one]

theorem weight_single (s : σ) (n : N) :
    weight w (Finsupp.single s n) = n • w s := by
  simp only [weight_apply, zero_smul, sum_single_index]

variable (N) in
/-- A weight function is nontorsion if its values are not torsion. -/
class NonTorsionWeight (w : σ → M) : Prop where
  eq_zero_of_smul_eq_zero {n : N} {s : σ} (h : n • w s = 0) : n = 0

variable (N) in
/-- Without zero divisors, nonzero weight is a `NonTorsionWeight` -/
theorem nonTorsionWeight_of [NoZeroSMulDivisors N M] (hw : ∀ i : σ, w i ≠ 0) :
    NonTorsionWeight N w where
  eq_zero_of_smul_eq_zero {n s} h := by
    rw [smul_eq_zero, or_iff_not_imp_right] at h
    exact h (hw s)

variable (N) in
theorem NonTorsionWeight.ne_zero [Nontrivial N] [NonTorsionWeight N w] (s : σ) :
    w s ≠ 0 := fun h ↦ by
  rw [← one_smul N (w s)] at h
  apply zero_ne_one.symm (α := N)
  exact NonTorsionWeight.eq_zero_of_smul_eq_zero h

variable {w} in
lemma weight_sub_single_add {f : σ →₀ ℕ} {i : σ} (hi : f i ≠ 0) :
    (f - single i 1).weight w + w i = f.weight w := by
  conv_rhs => rw [← sub_add_single_one_cancel hi, weight_apply]
  rw [sum_add_index', sum_single_index, one_smul, weight_apply]
  exacts [zero_smul .., fun _ ↦ zero_smul .., fun _ _ _ ↦ add_smul ..]

end AddCommMonoid

section OrderedAddCommMonoid

theorem le_weight (w : σ → ℕ) {s : σ} (hs : w s ≠ 0) (f : σ →₀ ℕ) :
    f s ≤ weight w f := by
  classical
  simp only [weight_apply, Finsupp.sum]
  by_cases h : s ∈ f.support
  · rw [Finset.sum_eq_add_sum_diff_singleton h]
    refine le_trans ?_ (Nat.le_add_right _ _)
    apply Nat.le_mul_of_pos_right
    exact Nat.zero_lt_of_ne_zero hs
  · simp only [not_mem_support_iff] at h
    rw [h]
    apply zero_le

variable [OrderedAddCommMonoid M] (w : σ → M)
  {N : Type*} [CanonicallyOrderedCommSemiring N] [Module N M]

instance : SMulPosMono ℕ M :=
  ⟨fun b hb m m' h ↦ by
    rw [← Nat.add_sub_of_le h, add_smul]
    exact le_add_of_nonneg_right (nsmul_nonneg hb (m' - m))⟩

variable {w} in
theorem le_weight_of_ne_zero (hw : ∀ s, 0 ≤ w s) {s : σ} {f : σ →₀ ℕ} (hs : f s ≠ 0) :
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

theorem le_weight_of_ne_zero' {s : σ} {f : σ →₀ ℕ} (hs : f s ≠ 0) :
    w s ≤ weight w f :=
  le_weight_of_ne_zero (fun _ ↦ zero_le _) hs

/-- If `M` is a `CanonicallyOrderedAddCommMonoid`, then `weight f` is zero iff `f=0. -/
theorem weight_eq_zero_iff_eq_zero
    (w : σ → M) [NonTorsionWeight ℕ w] {f : σ →₀ ℕ} :
    weight w f = 0 ↔ f = 0 := by
  classical
  constructor
  · intro h
    ext s
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    by_contra hs
    apply NonTorsionWeight.ne_zero ℕ w s
    rw [← nonpos_iff_eq_zero, ← h]
    exact le_weight_of_ne_zero' w hs
  · intro h
    rw [h, map_zero]

theorem finite_of_nat_weight_le [Finite σ] (w : σ → ℕ) (hw : ∀ x, w x ≠ 0) (n : ℕ) :
    {d : σ →₀ ℕ | weight w d ≤ n}.Finite := by
  classical
  set fg := Finset.antidiagonal (Finsupp.equivFunOnFinite.symm (Function.const σ n)) with hfg
  suffices {d : σ →₀ ℕ | weight w d ≤ n} ⊆ ↑(fg.image fun uv => uv.fst) by
    exact Set.Finite.subset (Finset.finite_toSet _) this
  intro d hd
  rw [hfg]
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe,
    Finset.mem_antidiagonal, Prod.exists, exists_and_right, exists_eq_right]
  use Finsupp.equivFunOnFinite.symm (Function.const σ n) - d
  ext x
  simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
    Finsupp.equivFunOnFinite_symm_apply_toFun, Function.const_apply]
  rw [add_comm]
  apply Nat.sub_add_cancel
  apply le_trans (le_weight w (hw x) d)
  simpa only [Set.mem_setOf_eq] using hd

end CanonicallyOrderedAddCommMonoid

variable {N : Type*} [AddCommMonoid N]

/-- The degree of a finsupp function. -/
def degree (d : σ →₀ N) := ∑ i ∈ d.support, d i

@[deprecated degree (since := "2024-07-20")]
alias _root_.MvPolynomial.degree := degree

@[simp]
theorem degree_add (a b : σ →₀ N) : (a + b).degree = a.degree + b.degree :=
  sum_add_index' (h := fun _ ↦ id) (congrFun rfl) fun _ _ ↦ congrFun rfl

@[simp]
theorem degree_single (a : σ) (n : N) : (Finsupp.single a n).degree = n := by
  rw [degree, Finset.sum_eq_single a]
  · simp only [single_eq_same]
  · intro b _ hba
    exact single_eq_of_ne hba.symm
  · intro ha
    simp only [mem_support_iff, single_eq_same, ne_eq, Classical.not_not] at ha
    rw [single_eq_same, ha]

@[simp]
theorem degree_zero : degree (0 : σ →₀ N) = 0 := by simp [degree]

lemma degree_eq_zero_iff {N : Type*} [CanonicallyOrderedAddCommMonoid N] (d : σ →₀ N) :
    degree d = 0 ↔ d = 0 := by
  simp only [degree, Finset.sum_eq_zero_iff, mem_support_iff, ne_eq, _root_.not_imp_self,
    DFunLike.ext_iff, coe_zero, Pi.zero_apply]

@[deprecated degree_eq_zero_iff (since := "2024-07-20")]
alias _root_.MvPolynomial.degree_eq_zero_iff := degree_eq_zero_iff

theorem le_degree {N : Type*} [CanonicallyOrderedAddCommMonoid N] (s : σ) (f : σ →₀ N) :
    f s ≤ degree f  := by
  classical
  simp only [degree]
  by_cases h : s ∈ f.support
  · simp only [Finset.sum_eq_add_sum_diff_singleton h, self_le_add_right]
  · simp only [not_mem_support_iff] at h
    simp only [h, zero_le]

theorem degree_eq_weight_one {N : Type*} [Semiring N] :
    degree (N := N) (σ := σ) = weight (fun _ ↦ 1) := by
  ext d
  simp only [degree, weight_apply, Pi.one_apply, smul_eq_mul, mul_one, Finsupp.sum]

@[deprecated degree_eq_weight_one (since := "2024-07-20")]
alias _root_.MvPolynomial.weightedDegree_one := degree_eq_weight_one

theorem finite_of_degree_le [Finite σ] (n : ℕ) :
    {f : σ →₀ ℕ | degree f ≤ n}.Finite := by
  simp_rw [degree_eq_weight_one]
  refine finite_of_nat_weight_le (Function.const σ 1) ?_ n
  intro _
  simp only [Function.const_apply, ne_eq, one_ne_zero, not_false_eq_true]

end Finsupp
