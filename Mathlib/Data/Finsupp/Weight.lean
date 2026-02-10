/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Data.Finsupp.Antidiagonal
public import Mathlib.Data.Finsupp.Order
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

import Mathlib.Algebra.Group.TypeTags.Pointwise

/-! # weights of Finsupp functions

The theory of multivariate polynomials and power series is built
on the type `σ →₀ ℕ` which gives the exponents of the monomials.
Many aspects of the theory (degree, order, graded ring structure)
require classifying these exponents according to their total sum
`∑ i, f i`, or variants, and this file provides some API for that.

## Weight

We fix a type `σ`, a semiring `R`, an `R`-module `M`,
as well as a function `w : σ → M`. (The important case is `R = ℕ`.)

- `Finsupp.weight` of a finitely supported function `f : σ →₀ R`
  with respect to `w`: it is the sum `∑ (f i) • (w i)`.
  It is an `AddMonoidHom` map defined using `Finsupp.linearCombination`.

- `Finsupp.le_weight` says that `f s ≤ f.weight w` when `M = ℕ`

- `Finsupp.le_weight_of_ne_zero` says that `w s ≤ f.weight w`
  for `OrderedAddCommMonoid M`, when `f s ≠ 0` and all `w i` are nonnegative.

- `Finsupp.le_weight_of_ne_zero'` is the same statement for `CanonicallyOrderedAddCommMonoid M`.

- `NonTorsionWeight`: all values `w s` are nontorsion in `M`.

- `Finsupp.weight_eq_zero_iff_eq_zero` says that `f.weight w = 0` iff
  `f = 0` for `NonTorsionWeight w` and `CanonicallyOrderedAddCommMonoid M`.

- For `w : σ → ℕ` and `Finite σ`, `Finsupp.finite_of_nat_weight_le` proves that
  there are finitely many `f : σ →₀ ℕ` of bounded weight.

## Degree

- `Finsupp.degree f` is the sum of all `f s`, for `s ∈ f.support`.
  The present choice is to have it defined as a plain function.

- `Finsupp.degree_eq_zero_iff` says that `f.degree = 0` iff `f = 0`.

- `Finsupp.le_degree` says that `f s ≤ f.degree`.

- `Finsupp.degree_eq_weight_one` says `f.degree = f.weight 1` when `R` is a semiring.
  This is useful to access the additivity properties of `Finsupp.degree`

- For `Finite σ`, `Finsupp.finite_of_degree_le` proves that
  there are finitely many `f : σ →₀ ℕ` of bounded degree.


## TODO

* Maybe `Finsupp.weight w` and `Finsupp.degree` should have similar types,
  both `AddMonoidHom` or both functions.

-/

@[expose] public section

open Module

variable {σ M R : Type*} [Semiring R] (w : σ → M)

namespace Finsupp

section AddCommMonoid

variable [AddCommMonoid M] [Module R M]
/-- The `weight` of the finitely supported function `f : σ →₀ R`
with respect to `w : σ → M` is the sum `∑ i, f i • w i`. -/
noncomputable def weight : (σ →₀ R) →+ M :=
  (Finsupp.linearCombination R w).toAddMonoidHom

theorem weight_apply (f : σ →₀ R) :
    weight w f = Finsupp.sum f (fun i c => c • w i) := rfl

theorem weight_single_index [DecidableEq σ] (s : σ) (c : M) (f : σ →₀ R) :
    weight (Pi.single s c) f = f s • c :=
  linearCombination_single_index σ M R c s f

theorem weight_single_one_apply [DecidableEq σ] (s : σ) (f : σ →₀ R) :
    weight (Pi.single s 1) f = f s := by
  rw [weight_single_index, smul_eq_mul, mul_one]

theorem weight_single (s : σ) (r : R) :
    weight w (Finsupp.single s r) = r • w s :=
  Finsupp.linearCombination_single _ _ _

variable (R) in
/-- A weight function is nontorsion if its values are not torsion. -/
class NonTorsionWeight (w : σ → M) : Prop where
  eq_zero_of_smul_eq_zero {r : R} {s : σ} (h : r • w s = 0) : r = 0

variable (R) in
/-- Without zero divisors, nonzero weight is a `NonTorsionWeight` -/
theorem nonTorsionWeight_of [IsDomain R] [IsTorsionFree R M] (hw : ∀ i : σ, w i ≠ 0) :
    NonTorsionWeight R w where
  eq_zero_of_smul_eq_zero {n s} h := by
    rw [smul_eq_zero, or_iff_not_imp_right] at h
    exact h (hw s)

variable (R) in
theorem NonTorsionWeight.ne_zero [Nontrivial R] [NonTorsionWeight R w] (s : σ) :
    w s ≠ 0 := fun h ↦ by
  rw [← one_smul R (w s)] at h
  apply zero_ne_one.symm (α := R)
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
  · simp only [notMem_support_iff] at h
    rw [h]
    apply zero_le

variable [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M] (w : σ → M)
  {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
  [CanonicallyOrderedAdd R] [NoZeroDivisors R] [Module R M]

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

variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
  [CanonicallyOrderedAdd M] (w : σ → M)

theorem le_weight_of_ne_zero' {s : σ} {f : σ →₀ ℕ} (hs : f s ≠ 0) :
    w s ≤ weight w f :=
  le_weight_of_ne_zero (fun _ ↦ zero_le _) hs

/-- If `M` is a `CanonicallyOrderedAddCommMonoid`, then `weight f` is zero iff `f = 0`. -/
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
  dsimp at hd
  grw [← le_weight _ (hw x)] at hd
  simp [*]

end CanonicallyOrderedAddCommMonoid

variable {R : Type*} [AddCommMonoid R]

/-- The degree of a finsupp function. -/
def degree : (σ →₀ R) →+ R where
  toFun := fun d => ∑ i ∈ d.support, d i
  map_zero' := by simp
  map_add' := fun _ _ => sum_add_index' (h := fun _ ↦ id) (congrFun rfl) fun _ _ ↦ congrFun rfl

@[deprecated (since := "2025-12-09")] alias degree_add := map_add

@[deprecated (since := "2025-12-09")] alias degree_zero := map_zero

theorem degree_apply (d : σ →₀ R) : degree d = ∑ i ∈ d.support, d i := rfl

@[deprecated (since := "2025-12-09")]
alias degree_def := degree_apply

theorem degree_eq_sum [Fintype σ] (f : σ →₀ R) : f.degree = ∑ i, f i := by
  rw [degree_apply, Finset.sum_subset] <;> simp

@[simp]
theorem degree_single (a : σ) (r : R) : (Finsupp.single a r).degree = r :=
  Finsupp.sum_single_index (h := fun _ => id) rfl

lemma degree_eq_zero_iff {R : Type*}
    [AddCommMonoid R] [PartialOrder R] [CanonicallyOrderedAdd R]
    (d : σ →₀ R) :
    degree d = 0 ↔ d = 0 := by
  simp only [degree_apply, Finset.sum_eq_zero_iff, mem_support_iff, ne_eq, _root_.not_imp_self,
    DFunLike.ext_iff, coe_zero, Pi.zero_apply]

theorem le_degree {R : Type*}
    [AddCommMonoid R] [PartialOrder R] [CanonicallyOrderedAdd R]
    (s : σ) (f : σ →₀ R) :
    f s ≤ degree f := by
  by_cases h : s ∈ f.support
  · exact Finset.single_le_sum_of_canonicallyOrdered h
  · simp only [notMem_support_iff] at h
    simp only [h, zero_le]

theorem degree_eq_weight_one {R : Type*} [Semiring R] :
    degree (R := R) (σ := σ) = weight (fun _ ↦ 1) := by
  ext d
  simp [weight_apply, smul_eq_mul, mul_one]

theorem finite_of_degree_le [Finite σ] (n : ℕ) :
    {f : σ →₀ ℕ | degree f ≤ n}.Finite := by
  simp_rw [degree_eq_weight_one]
  refine finite_of_nat_weight_le (Function.const σ 1) ?_ n
  intro _
  simp only [Function.const_apply, ne_eq, one_ne_zero, not_false_eq_true]

lemma range_single_one :
    Set.range (fun a : σ ↦ Finsupp.single a 1) = { d | d.degree = 1 } := by
  refine subset_antisymm ?_ ?_
  · simp [Set.range_subset_iff]
  · intro p (hp : p.sum (fun a k ↦ k) = 1)
    obtain ⟨a, rfl⟩ := (Finsupp.sum_eq_one_iff _).mp hp
    use a

lemma degree_mono {R : Type*} [AddCommMonoid R] [PartialOrder R] [CanonicallyOrderedAdd R] :
    Monotone (Finsupp.degree (σ := σ) (R := R)) :=
  fun _ _ e ↦
    (Finset.sum_le_sum_of_subset (support_mono e)).trans (Finset.sum_le_sum fun _ _ ↦ e _)

lemma exists_le_degree_eq {σ : Type*} (f : σ →₀ ℕ) (n : ℕ) (hn : n ≤ f.degree) :
    ∃ g ≤ f, g.degree = n := by
  induction n with
  | zero => simp [degree_eq_zero_iff]
  | succ n IH =>
    obtain ⟨g, hgf, rfl⟩ := IH (by lia)
    obtain ⟨f, rfl⟩ := le_iff_exists_add.mp hgf
    obtain ⟨i, hi⟩ : f.support.Nonempty := by aesop
    exact ⟨g + .single i 1, add_le_add_right (by simp; grind) _, by simp⟩

open scoped Pointwise in
lemma degree_preimage_add {σ : Type*} (s t : Set ℕ) :
    degree (σ := σ) ⁻¹' (s + t) = degree (σ := σ) ⁻¹' s + degree (σ := σ) ⁻¹' t := by
  refine (Set.preimage_add_preimage_subset ..).antisymm' ?_
  rintro f ⟨m, hm, n, hn, e : m + n = _⟩
  obtain ⟨g, hgf, rfl⟩ := exists_le_degree_eq f m (by grind)
  obtain ⟨f, rfl⟩ := le_iff_exists_add.mp hgf
  exact Set.add_mem_add hm (by simp_all)

open scoped Pointwise in
lemma degree_preimage_nsmul {σ : Type*} (s : Set ℕ) (n : ℕ) (hn : n ≠ 0) :
    degree (σ := σ) ⁻¹' (n • s) = n • degree (σ := σ) ⁻¹' s := by
  obtain (_ | n) := n; · contradiction
  induction n <;> simp_all [succ_nsmul, degree_preimage_add]

open scoped Pointwise in
lemma nsmul_single_one_image {α : Type*} {n : ℕ} {s : Set α} :
    n • (single · 1) '' s = {x : α →₀ ℕ | x.degree = n ∧ ↑x.support ⊆ s} := by
  classical
  induction n with
  | zero => aesop (add simp degree_eq_zero_iff)
  | succ n ih =>
    rw [succ_nsmul, ih]
    refine subset_antisymm ?_ fun f ⟨f_deg, f_supp⟩ ↦ ?_
    · simp [Set.subset_def, Set.mem_add, @forall_comm (α →₀ ℕ)]; grind
    obtain ⟨i, hi⟩ : f.support.Nonempty := by aesop
    obtain ⟨x, hx⟩ := le_iff_exists_add'.mp
      (show single i 1 ≤ f by simpa [Nat.one_le_iff_ne_zero] using hi)
    exact ⟨x, by aesop (add simp Set.subset_def), _, ⟨_, f_supp (by simp_all), rfl⟩, hx.symm⟩

open scoped Pointwise in
theorem image_pow_eq_finsuppProd_image {α β : Type*} [CommMonoid β] {f : α → β} {n} {s : Set α} :
    (f '' s) ^ n = (·.prod (f · ^ ·)) '' {x : α →₀ ℕ | x.degree = n ∧ ↑x.support ⊆ s} := by
  classical
  suffices ∀ (s : Set (α →₀ ℕ)), ((·.prod (f · ^ ·)) '' s) ^ n = (·.prod (f · ^ ·)) '' (n • s) by
    simp [← nsmul_single_one_image, ← this, Set.image_image]
  intro s
  refine (Set.image_pow (⟨⟨(·.prod (f · ^ ·)) ∘ Multiplicative.toAdd, by simp⟩,
    by simp [Finsupp.prod_add_index, pow_add]⟩ : Multiplicative (α →₀ ℕ) →* β) _ _).symm.trans ?_
  simp [-Function.comp_apply, Set.image_comp, show Multiplicative.toAdd '' s = s from
    Set.image_id _]

end Finsupp
