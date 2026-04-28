/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

module

public import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# Center of the algebra of linear endomorphisms

If `V` is an `R`-module, we say that an endomorphism `f : Module.End R V`
is a *homothety* with central ratio if there exists `a ∈ Set.center R`
such that `f x = a • x` for all `x`.
By `Module.End.mem_subsemiringCenter_iff`, these linear maps constitute
the center of `Module.End R V`.
(When `R` is commutative, we can write `f = a • LinearMap.id`.)

In what follows, `V` is assumed to be a free `R`-module.

* `LinearMap.commute_transvections_iff_of_basis`:
  if an endomorphism `f : V →ₗ[R] V` commutes with every elementary transvection
  (in a given basis), then it is a homothety with central ratio.
  (Assumes that the basis is provided and has a non trivial set of indices.)

* `LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent`:
  over a commutative ring `R` which is a domain, an endomorphism `f : V →ₗ[R] V`
  of a free module such that `v` and `f v` are not linearly independent,
  for all `v : V`, is a homothety.

* `LinearMap.exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent`:
  a variant that does not assume that `R` is commutative.
  Then the homothety has central ratio.

* `LinearMap.exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent_of_basis`:
  a variant that does not assume that `R` has the strong rank condition,
  but requires a basis.

Note. In the noncommutative case, the last two results do not hold
when the rank is equal to 1. Indeed, right multiplications
with noncentral ratio of the `R`-module `R` satisfy the property
that `f v` and `v` are linearly dependent, for all `v : V`,
but they are not left multiplication by some element.

-/

public section

open Module LinearMap LinearEquiv Set Finsupp

namespace LinearMap

variable {R V : Type*}

/-- A linear endomorphism of a free module of rank at least 2
that commutes with transvections consists of homotheties with central ratio. -/
theorem commute_transvections_iff_of_basis
    [Ring R] [AddCommGroup V] [Module R V]
    {ι : Type*} [Nontrivial ι] (b : Basis ι R V)
    {f : V →ₗ[R] V}
    (hcomm : ∀ i j (r : R) (_ : i ≠ j), Commute f (transvection (b.coord i) (r • b j))) :
    ∃ a : Subring.center R, f = a • 1 := by
  simp only [SetLike.exists, Subring.mem_center_iff]
  rcases subsingleton_or_nontrivial V with hV | hV
  · refine ⟨1, by simp, ?_⟩
    ext x
    simp [Subring.smul_def, hV.allEq (f x) x]
  simp only [commute_iff_eq] at hcomm
  replace hcomm (i j : ι) (hij : i ≠ j) (r : R) :
      r • f (b j) = b.coord i (f (b i)) • r • b j := by
    have := hcomm i j r hij
    rw [LinearMap.ext_iff] at this
    simpa [LinearMap.transvection.apply] using this (b i)
  have h_allEq (i j : ι) : b.coord i (f (b i)) = b.coord j (f (b j)) := by
    by_cases hij : j = i
    · simp [hij]
    simpa using congr_arg (b.coord i) (hcomm j i hij 1)
  replace hcomm (i : ι) (r : R) : r • f (b i) = b.coord i (f (b i)) • r • b i := by
    obtain ⟨j, hji⟩ := exists_ne i
    simpa [h_allEq j i] using hcomm j i hji r
  let i : ι := Classical.ofNonempty
  refine ⟨b.coord i (f (b i)), fun r ↦ by simpa using congr(b.coord i $(hcomm i r)), ?_⟩
  ext x
  rw [← b.linearCombination_repr x, linearCombination_apply, map_finsuppSum]
  simp only [smul_apply, End.one_apply, smul_sum]
  apply sum_congr
  intro j _
  simp [Subring.smul_def, h_allEq i j, hcomm j]

/-- Over a domain, an endomorphism `f` of a free module `V`
of rank ≠ 1 such that `f v` and `v` are collinear, for all `v : V`,
consists of homotheties with central ratio.

In the commutative case, use `LinearMap.exists_eq_smul_id`.

This is a variant of `LinearMap.exists_mem_center_apply_smul`
which switches the use of `StrongRankInduction` and `finrank`
for the cardinality of a given basis.

When `finrank R V = 1`, up to a linear equivalence `V ≃ₗ[R] R`,
then any `f` is *right*-multiplication by some `a : R`,
but not necessarily *left*-multiplication by an element of the center of `R`. -/
theorem exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent_of_basis
    [Ring R] [IsDomain R] [AddCommGroup V] [Module R V]
    {f : V →ₗ[R] V}
    {ι : Type*} [Nontrivial ι] (b : Basis ι R V)
    (h : ∀ v, ¬ LinearIndependent R ![v, f v]) :
    ∃ a : Subring.center R, f = a • 1 := by
  -- We make the linear dependence condition explicit
  have feq (i) : f (b i) = (b.coord i) (f (b i)) • b i := by
    classical
    rw [b.ext_elem_iff]
    intro j
    simp only [LinearIndependent.pair_iff, not_forall] at h
    obtain ⟨s, t, ⟨h, h'⟩⟩ := h (b i)
    simp only [Basis.coord_apply, _root_.map_smul, Basis.repr_self, smul_single,
      smul_eq_mul, mul_one, Finsupp.single_apply]
    split_ifs with hj
    · simp [hj]
    · have : t = 0 ∨ b.repr (f (b i)) j = 0 := by
        rw [b.ext_elem_iff] at h
        simpa [single_eq_of_ne' hj] using h j
      apply Or.resolve_left this
      contrapose h'
      refine ⟨?_, h'⟩
      simp only [h', zero_smul, add_zero] at h
      contrapose hj
      apply b.linearIndependent.eq_of_smul_apply_eq_smul_apply s 0 i j hj
      simpa using h
  have h' (i j) (hij : i ≠ j) (r : R) : b.coord i (f (b i)) * r = r * b.coord j (f (b j)) := by
    -- we use that `f (b i + r • b j)` is a multiple of `b i + r • b j`
    let x := b.repr.symm ((Finsupp.single i 1).update j r)
    specialize h x
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd,
      LinearIndependent.pair_iff, not_forall, not_and] at h
    obtain ⟨s, t, h, hst⟩ := h
    simp only [b.ext_elem_iff, map_add, _root_.map_smul, coe_add, Finsupp.coe_smul,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h
    have hx : x = b i + r • b j := by
      simp only [Basis.repr_symm_apply, linearCombination_apply, x]
      rw [← add_right_cancel_iff, sum_update_add] <;>
        simp [single_eq_of_ne' hij, add_smul]
    have h1 : s + t * (b.coord i (f (b i))) = 0 := by
      suffices s + t * ((b.repr (f (b i))) i + r * (b.repr (f (b j))) i) = 0 by
        rw [mul_add, ← add_assoc, ← mul_assoc, add_eq_zero_iff_eq_neg] at this
        rw [Basis.coord_apply, this, feq]
        simp [single_eq_of_ne hij]
      simpa [hx, single_eq_of_ne hij] using h i
    have h2 : s * r + t * r * b.coord j (f (b j)) = 0 := by
      suffices s * r + t * ((b.repr (f (b i))) j + r * (b.repr (f (b j))) j) = 0 by
        rw [mul_add, ← add_assoc, add_right_comm, add_eq_zero_iff_eq_neg, ← mul_assoc] at this
        rw [Basis.coord_apply, this, feq]
        simp [single_eq_of_ne' hij]
      simpa [hx, single_eq_same, single_eq_of_ne' hij] using h j
    rw [add_eq_zero_iff_eq_neg] at h1
    rw [h1, neg_mul, neg_add_eq_sub, mul_assoc, mul_assoc,
      ← mul_sub, mul_eq_zero, sub_eq_zero] at h2
    symm
    apply Or.resolve_left h2
    contrapose hst; simp [h1, hst]
  -- This generalizes the equality formerly known as `feq`
  replace feq (i j) : f (b j) = b.coord i (f (b i)) • b j := by
    by_cases hij : i = j
    · rw [← hij, ← feq]
    · have := h' i j hij 1
      simp only [mul_one, one_mul] at this
      rw [feq, ← this]
  let i : ι := Classical.ofNonempty
  have ha (r) : Commute (b.coord i (f (b i))) r := by
    obtain ⟨j, hij⟩ := exists_ne i
    rw [commute_iff_eq, h' i j (Ne.symm hij), feq i j, feq i i]
    simp
  refine ⟨⟨b.coord i (f (b i)), ?_⟩, ?_⟩
  · simpa [Subring.mem_center_iff, commute_iff_eq, eq_comm] using ha
  apply b.ext
  simpa only [smul_apply, End.one_apply, Subring.smul_def] using feq i

/-- Over a domain `R`, an endomorphism `f` of a free module `V`
of rank ≠ 1 such that `f v` and `v` are collinear, for all `v : V`,
consists of homotheties with central ratio.

When `R` does not satisfy `StrongRankCondition`, use
`LinearMap.exists_mem_center_apply_eq_smul_of_basis`.

When `finrank R V = 1`, up to a linear equivalence `V ≃ₗ[R] R`,
then any `f` is *right*-multiplication by some `a : R`,
but not necessarily *left*-multiplication by an element of the center of `R`. -/
theorem exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent
    [Ring R] [IsDomain R] [StrongRankCondition R]
    [AddCommGroup V] [Module R V] [Free R V]
    {f : V →ₗ[R] V}
    (hV1 : finrank R V ≠ 1)
    (h : ∀ v, ¬ LinearIndependent R ![v, f v]) :
    ∃ a : Subring.center R, f = a • 1 := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · use 1
    ext x
    apply hV.allEq
  let ι := Free.ChooseBasisIndex R V
  let b : Basis ι R V := Free.chooseBasis R V
  rcases subsingleton_or_nontrivial ι with hι | hι
  · have : Nonempty ι := Free.instNonemptyChooseBasisIndexOfNontrivial R V
    have : Fintype ι := Fintype.ofFinite ι
    simp_all [finrank_eq_card_basis b, ← Nat.card_eq_fintype_card]
  exact exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent_of_basis b h

/-- Over a commutative domain, an endomorphism `f` of a free module `V`
such that `f v` and `v` are collinear, for all `v : V`,
consists of homotheties. -/
theorem exists_eq_smul_id_of_forall_notLinearIndependent
    [CommRing R] [IsDomain R] [AddCommGroup V] [Module R V] [Free R V] {f : V →ₗ[R] V}
    (h : ∀ v, ¬ LinearIndependent R ![v, f v]) :
    ∃ a : R, f = a • 1 := by
  by_cases hV1 : finrank R V = 1
  · rw [finrank_eq_one_iff Unit] at hV1
    let b : Basis Unit R V := Classical.ofNonempty
    use b.coord () (f (b ()))
    apply b.ext
    intro i
    nth_rewrite 1 [← b.linearCombination_repr (f (b i))]
    simp [linearCombination_unique]
  obtain ⟨a, rfl⟩ := exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent hV1 h
  refine ⟨a, by simp [Subring.smul_def]⟩

end LinearMap
