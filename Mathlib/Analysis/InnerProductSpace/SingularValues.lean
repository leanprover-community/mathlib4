/-
Copyright (c) 2026 Niels Voss, Arnav Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Niels Voss, Arnav Mehta
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.Order.Interval.Set.Fin
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Order
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!
# Singular values for finite-dimensional linear maps

For a linear map `T` between finite-dimensional inner product spaces `E` and `F`, we define the
singular values, which are the square roots of the eigenvalues of `T.adjoint ∘ₗ T`, arranged in
descending order and repeated according to their multiplicity.

With our definition, there are countably infinitely many singular values, but only the first rank(T)
singular values are nonzero.

The singular values are zero-indexed, so `T.singularValues 0` is the first singular value.
This means the positive singular values occur at `0 ≤ i < rank(T)` and not `1 ≤ i ≤ rank(T)`.

## Main definition

- `LinearMap.singularValues`: The infinite but finitely supported sequence of the singular values of
  a linear map.

## Main statements

- `LinearMap.support_singularValues`: The first rank(T) many singular values are positive, and the
  rest are zero.

## Implementation notes

Suppose `T : E →ₗ[𝕜] F` where `dim(E) = n`, `dim(F) = m`.
In mathematical literature, the number of singular values varies, with popular choices including
- `rank(T)` singular values, all of which are positive.
- `min(n,m)` singular values, some of which might be zero.
- `n` singular values, some of which might be zero. This is the approach taken in [axler2024].
- Countably infinitely many singular values, with all but finitely many of them being zero.

We take the last approach for the following reasons:
- It avoid unnecessary dependent typing.
- You can easily convert this definition to the other three by composing with `Fin.val`, but
  converting between any two of the other definitions is more inconvenient because it involves
  multiple `Fin` types.
- If you prefer a definition where there are `k` singular values, you can treat the singular values
  after `k` as junk values.
  Not having to prove that `i < k` when getting the `i`th singular value has similar advantages to
  not having to prove that `y ≠ 0` when calculating `x / y`.
- This API coincides with a potential future API for approximation numbers, which are a
  generalization of singular values to continuous linear maps between possibly-infinite-dimensional
  normed vector spaces.

## TODO

- Generalize singular values to the approximation numbers for maps between
  possibly-infinite-dimensional normed vector spaces.
  This will likely have a similar type signature to the current singular values definition, except
  it will take in a `ContinuousLinearMap` and will not be finitely supported.

## References

* [Sheldon Axler, *Linear Algebra Done Right*][axler2024]

## Tags

singular values
-/

public section

open Module InnerProductSpace

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  (T : E →ₗ[𝕜] F)

/--
If `T : E →ₗ[𝕜] F` is a linear map between finite dimensional inner product spaces, then
`T.singularValues` is the infinite sequence where the first dim(E) elements are the square roots of
eigenvalues of `T.adjoint ∘ₗ T` (which are guaranteed to be nonnegative real numbers), arranged
in descending order and repeated according to their multiplicity, and the rest of the elements in
the infinite sequence are zero. Please see the module docstring of
`Mathlib/Analysis/InnerProductSpace/SingularValues.lean` for an explanation of this design decision.

The singular values are zero-indexed, so `T.singularValues 0` refers to the first singular value.
This means the positive singular values occur at `0 ≤ i < rank(T)` and not `1 ≤ i ≤ rank(T)`.
-/
noncomputable def singularValues : ℕ →₀ ℝ :=
  Finsupp.embDomain Fin.valEmbedding <|
    Finsupp.ofSupportFinite
      (fun i ↦ √(T.isSymmetric_adjoint_comp_self.eigenvalues rfl i))
      (Set.toFinite _)

theorem singularValues_nonneg (i : ℕ) : 0 ≤ T.singularValues i := by
  rw [singularValues, Finsupp.embDomain_apply, Finsupp.ofSupportFinite_coe]
  split_ifs <;> positivity

theorem singularValues_pos_iff_ne_zero (i : ℕ) : 0 < T.singularValues i ↔ T.singularValues i ≠ 0 :=
  by grind [T.singularValues_nonneg i]

/--
Connection between `LinearMap.singularValues` and `LinearMap.IsSymmetric.eigenvalues`.
Together with `LinearMap.singularValues_of_finrank_le`, this characterizes the singular values.

Because of the square root, you probably need to use
`T.isPositive_adjoint_comp_self.nonneg_eigenvalues` to make effective use of this theorem.
-/
theorem singularValues_fin {n : ℕ} (hn : finrank 𝕜 E = n) (i : Fin n) :
    T.singularValues i = √(T.isSymmetric_adjoint_comp_self.eigenvalues hn i) := by
  subst hn
  exact Finsupp.embDomain_apply_self _ _ i

theorem singularValues_of_lt {n : ℕ} (hn : finrank 𝕜 E = n) {i : ℕ} (hi : i < n) :
    T.singularValues i = √(T.isSymmetric_adjoint_comp_self.eigenvalues hn ⟨i, hi⟩) :=
  T.singularValues_fin hn ⟨i, hi⟩

theorem singularValues_of_finrank_le {i : ℕ} (hi : finrank 𝕜 E ≤ i) : T.singularValues i = 0 := by
  apply Finsupp.embDomain_notin_range
  simp [hi]

theorem sq_singularValues_fin {n : ℕ} (hn : finrank 𝕜 E = n) (i : Fin n) :
    T.singularValues i ^ 2 = T.isSymmetric_adjoint_comp_self.eigenvalues hn i := by
  simp [T.singularValues_fin hn, T.isPositive_adjoint_comp_self.nonneg_eigenvalues hn i]

theorem sq_singularValues_of_lt {n : ℕ} (hn : finrank 𝕜 E = n) {i : ℕ} (hi : i < n) :
    T.singularValues i ^ 2 = T.isSymmetric_adjoint_comp_self.eigenvalues hn ⟨i, hi⟩ :=
  T.sq_singularValues_fin hn ⟨i, hi⟩

theorem hasEigenvalue_adjoint_comp_self_sq_singularValues {n : ℕ} (hn : n < finrank 𝕜 E) :
    End.HasEigenvalue (adjoint T ∘ₗ T) (T.singularValues n ^ 2) := by
  convert T.isSymmetric_adjoint_comp_self.hasEigenvalue_eigenvalues rfl ⟨n, hn⟩ using 1
  simp [← T.sq_singularValues_fin]

theorem singularValues_antitone : Antitone T.singularValues := by
  intro i j hij
  by_cases! hj : finrank 𝕜 E ≤ j
  · simpa [T.singularValues_of_finrank_le hj] using T.singularValues_nonneg i
  have : (T.singularValues j : ℝ) ^ 2 ≤ (T.singularValues i : ℝ) ^ 2 := by
    rw [T.sq_singularValues_fin rfl ⟨j, hj⟩, T.sq_singularValues_fin rfl ⟨i, hij.trans_lt hj⟩]
    exact T.isSymmetric_adjoint_comp_self.eigenvalues_antitone rfl hij
  exact le_of_sq_le_sq this (T.singularValues_nonneg i)

/--
7.68(a) from [axler2024]. Note that we have countably infinitely many singular values whereas there
are only dim(domain(T)) singular values in [axler2024], so we modify the statement to account for
this.
-/
theorem injective_iff_forall_lt_finrank_singularValues_pos :
    Function.Injective T ↔ ∀ i < finrank 𝕜 E, 0 < T.singularValues i := by
  have := (adjoint T ∘ₗ T).not_hasEigenvalue_zero_tfae.out 4 0
  rw [← adjoint_comp_self_injective_iff, ← coe_comp, ← ker_eq_bot, ← not_iff_not, this.not_left]
  push Not
  constructor
  · intro h
    obtain ⟨i, hi⟩ := T.isSymmetric_adjoint_comp_self.exists_eigenvalues_eq rfl h
    use i, i.isLt
    simp [RCLike.ofReal_eq_zero.mp hi, T.singularValues_fin rfl]
  · intro ⟨i, h, hz⟩
    convert T.isSymmetric_adjoint_comp_self.hasEigenvalue_eigenvalues rfl ⟨i, h⟩
    rw [← sq_singularValues_of_lt, le_antisymm hz (T.singularValues_nonneg i)]
    simp

/--
7.68(b) from [axler2024]. See also `LinearMap.support_singularValues` for a stronger statement.
-/
theorem card_support_singularValues : T.singularValues.support.card = finrank 𝕜 T.range := by
  have hS : ∀ m ∈ T.singularValues.support, m < finrank 𝕜 E := by
    grind [singularValues_of_finrank_le]
  have hT := T.isSymmetric_adjoint_comp_self
  have : T.singularValues.support.attachFin hS = ({i | hT.eigenvalues rfl i = (0 : 𝕜)} : Finset _)ᶜ
    := by ext i; simp [T.singularValues_fin, T.isPositive_adjoint_comp_self.nonneg_eigenvalues]
  rw [← T.singularValues.support.card_attachFin hS, this, Finset.card_compl, Fintype.card_fin,
    hT.card_filter_eigenvalues_eq rfl 0, Module.End.eigenspace_zero,
    ← (T.adjoint ∘ₗ T).finrank_range_add_finrank_ker, add_tsub_cancel_right,
    T.range_adjoint_comp_self, finrank_range_adjoint]

theorem isLowerSet_support_singularValues : IsLowerSet (T.singularValues.support : Set ℕ) := by
  intro a b hl ha
  rw [Finset.mem_coe, Finsupp.mem_support_iff, ← singularValues_pos_iff_ne_zero] at ⊢ ha
  order [T.singularValues_antitone hl]

@[simp]
theorem support_singularValues : T.singularValues.support = Finset.range (finrank 𝕜 T.range) := by
  obtain ⟨n, hn⟩ := T.isLowerSet_support_singularValues.eq_univ_or_Iio.resolve_left
    (fun h ↦ Set.infinite_univ.not_finite (h ▸ Finset.finite_toSet _))
  rw [← Finset.coe_Iio, Finset.coe_inj, Nat.Iio_eq_range] at hn
  simp [← card_support_singularValues, hn]

theorem singularValues_pos_iff_lt_finrank_range {n : ℕ} :
    0 < T.singularValues n ↔ n < finrank 𝕜 T.range := by
  rw [singularValues_pos_iff_ne_zero, ← Finsupp.mem_support_iff, support_singularValues,
    Finset.mem_range]

theorem singularValues_finrank_range_self : T.singularValues (finrank 𝕜 T.range) = 0 := by
  rw [← Finsupp.notMem_support_iff, support_singularValues]
  exact Finset.notMem_range_self

theorem singularValues_eq_zero_iff_le_finrank_range {n : ℕ} :
    T.singularValues n = 0 ↔ finrank 𝕜 T.range ≤ n := by
  rw [← Finsupp.notMem_support_iff, support_singularValues, Finset.mem_range, not_lt]

@[simp]
theorem singularValues_zero : (0 : E →ₗ[𝕜] F).singularValues = 0 := by
  ext1 i
  rw [Finsupp.zero_apply, singularValues_eq_zero_iff_le_finrank_range, range_zero]
  simp

@[simp]
theorem singularValues_eq_zero_iff : T.singularValues = 0 ↔ T = 0 := by
  constructor <;> intro h
  · rw [← range_eq_bot, ← Submodule.finrank_eq_zero, ← Nat.le_zero,
      ← singularValues_eq_zero_iff_le_finrank_range, h, Finsupp.zero_apply]
  · exact h ▸ singularValues_zero

end LinearMap
