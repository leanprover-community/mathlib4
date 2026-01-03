/-
Copyright (c) 2025 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Order.SuccPred.WithBot
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Algebra.Polynomial.Taylor

/-!
# Split polynomials

A polynomial `f : R[X]` splits if it is a product of constant and monic linear polynomials.

## Main definitions

* `Polynomial.Splits f`: A predicate on a polynomial `f` saying that `f` is a product of
  constant and monic linear polynomials.

-/

@[expose] public section

variable {R : Type*}

namespace Polynomial

section Semiring

variable [Semiring R]

/-- A polynomial `Splits` if it is a product of constant and monic linear polynomials.
This will eventually replace `Polynomial.Splits`. -/
def Splits (f : R[X]) : Prop := f ∈ Submonoid.closure ({C a | a : R} ∪ {X + C a | a : R})

@[simp, aesop safe apply]
protected theorem Splits.C (a : R) : Splits (C a) :=
  Submonoid.mem_closure_of_mem (Set.mem_union_left _ ⟨a, rfl⟩)

@[simp, aesop safe apply]
protected theorem Splits.zero : Splits (0 : R[X]) := by
  simpa using Splits.C (0 : R)

@[simp, aesop safe apply]
protected theorem Splits.one : Splits (1 : R[X]) :=
  Splits.C (1 : R)

@[simp, aesop safe apply]
theorem Splits.X_add_C (a : R) : Splits (X + C a) :=
  Submonoid.mem_closure_of_mem (Set.mem_union_right _ ⟨a, rfl⟩)

@[simp, aesop safe apply]
protected theorem Splits.X : Splits (X : R[X]) := by
  simpa using Splits.X_add_C (0 : R)

@[simp, aesop safe apply]
protected theorem Splits.mul {f g : R[X]} (hf : Splits f) (hg : Splits g) :
    Splits (f * g) :=
  mul_mem hf hg

protected theorem Splits.C_mul {f : R[X]} (hf : Splits f) (a : R) : Splits (C a * f) :=
  (Splits.C a).mul hf

@[simp, aesop safe apply]
theorem Splits.listProd {l : List R[X]} (h : ∀ f ∈ l, Splits f) : Splits l.prod :=
  list_prod_mem h

@[simp, aesop safe apply]
protected theorem Splits.pow {f : R[X]} (hf : Splits f) (n : ℕ) : Splits (f ^ n) :=
  pow_mem hf n

theorem Splits.X_pow (n : ℕ) : Splits (X ^ n : R[X]) :=
  Splits.X.pow n

theorem Splits.C_mul_X_pow (a : R) (n : ℕ) : Splits (C a * X ^ n) :=
  (Splits.X_pow n).C_mul a

@[simp, aesop safe apply]
theorem Splits.monomial (n : ℕ) (a : R) : Splits (monomial n a) := by
  simp [← C_mul_X_pow_eq_monomial]

protected theorem Splits.map {f : R[X]} (hf : Splits f) {S : Type*} [Semiring S] (i : R →+* S) :
    Splits (map i f) := by
  induction hf using Submonoid.closure_induction <;> aesop

theorem splits_of_natDegree_eq_zero {f : R[X]} (hf : natDegree f = 0) :
    Splits f :=
  (natDegree_eq_zero.mp hf).choose_spec ▸ by aesop

theorem splits_of_degree_le_zero {f : R[X]} (hf : degree f ≤ 0) :
    Splits f :=
  splits_of_natDegree_eq_zero (natDegree_eq_zero_iff_degree_le_zero.mpr hf)

theorem _root_.IsUnit.splits [NoZeroDivisors R] {f : R[X]} (hf : IsUnit f) : Splits f :=
  splits_of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit hf)

@[deprecated (since := "2025-11-27")]
alias splits_of_isUnit := IsUnit.splits

theorem splits_of_natDegree_le_one_of_invertible {f : R[X]}
    (hf : f.natDegree ≤ 1) (h : Invertible f.leadingCoeff) : f.Splits := by
  obtain ⟨a, b, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hf
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · replace h : Invertible a := by simpa [leadingCoeff, ha] using h
    rw [← mul_invOf_cancel_left a b, C_mul, ← mul_add]
    exact (Splits.C a).mul (Splits.X_add_C _)

theorem splits_of_degree_le_one_of_invertible {f : R[X]}
    (hf : f.degree ≤ 1) (h : Invertible f.leadingCoeff) : f.Splits :=
  splits_of_natDegree_le_one_of_invertible (natDegree_le_of_degree_le hf) h

theorem splits_of_natDegree_le_one_of_monic {f : R[X]} (hf : f.natDegree ≤ 1) (h : Monic f) :
    f.Splits :=
  splits_of_natDegree_le_one_of_invertible hf (h.leadingCoeff ▸ invertibleOne)

theorem splits_of_degree_le_one_of_monic {f : R[X]} (hf : f.degree ≤ 1) (h : Monic f) :
    f.Splits :=
  splits_of_natDegree_le_one_of_monic (natDegree_le_of_degree_le hf) h

end Semiring

section CommSemiring

variable [CommSemiring R]

@[simp, aesop safe apply]
theorem Splits.multisetProd {m : Multiset R[X]} (hm : ∀ f ∈ m, Splits f) : Splits m.prod :=
  multiset_prod_mem _ hm

@[simp, aesop safe apply]
protected theorem Splits.prod {ι : Type*} {f : ι → R[X]} {s : Finset ι}
    (h : ∀ i ∈ s, Splits (f i)) : Splits (∏ i ∈ s, f i) :=
  prod_mem h

lemma Splits.taylor {p : R[X]} (hp : p.Splits) (r : R) : (p.taylor r).Splits := by
  have (i : _) : (X + C r + C i).Splits := by simpa [add_assoc] using Splits.X_add_C (r + i)
  induction hp using Submonoid.closure_induction <;> aesop

/-- See `splits_iff_exists_multiset` for the version with subtraction. -/
theorem splits_iff_exists_multiset' {f : R[X]} :
    Splits f ↔ ∃ m : Multiset R, f = C f.leadingCoeff * (m.map (X + C ·)).prod := by
  refine ⟨fun hf ↦ ?_, ?_⟩
  · let S : Submonoid R[X] := MonoidHom.mrange C
    have hS : S = {C a | a : R} := MonoidHom.coe_mrange C
    rw [Splits, Submonoid.closure_union, ← hS, Submonoid.closure_eq, Submonoid.mem_sup] at hf
    obtain ⟨-, ⟨a, rfl⟩, g, hg, rfl⟩ := hf
    obtain ⟨mg, hmg, rfl⟩ := Submonoid.exists_multiset_of_mem_closure hg
    choose! j hj using hmg
    have hmg : mg = (mg.map j).map (X + C ·) := by simp [Multiset.map_congr rfl hj]
    rw [hmg, leadingCoeff_mul_monic, leadingCoeff_C]
    · use mg.map j
    · rw [hmg]
      apply monic_multiset_prod_of_monic
      simp [monic_X_add_C]
  · rintro ⟨m, hm⟩
    exact hm ▸ (Splits.C _).mul (.multisetProd (by simp [Splits.X_add_C]))

theorem Splits.natDegree_le_one_of_irreducible {f : R[X]} (hf : Splits f)
    (h : Irreducible f) : natDegree f ≤ 1 := by
  nontriviality R
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset'.mp hf
  rcases m.empty_or_exists_mem with rfl | ⟨a, ha⟩
  · rw [hm]
    simp
  · obtain ⟨m, rfl⟩ := Multiset.exists_cons_of_mem ha
    rw [Multiset.map_cons, Multiset.prod_cons] at hm
    rw [hm] at h
    simp only [irreducible_mul_iff, IsUnit.mul_iff, not_isUnit_X_add_C, false_and, and_false,
      or_false, false_or, ← Multiset.prod_toList, List.prod_isUnit_iff] at h
    have : m = 0 := by simpa [not_isUnit_X_add_C, ← Multiset.eq_zero_iff_forall_notMem] using h.1.2
    grw [hm, this, natDegree_mul_le]
    simp

theorem Splits.degree_le_one_of_irreducible {f : R[X]} (hf : Splits f)
    (h : Irreducible f) : degree f ≤ 1 :=
  degree_le_of_natDegree_le (hf.natDegree_le_one_of_irreducible h)

theorem Splits.comp_of_natDegree_le_one_of_invertible {f g : R[X]} (hf : f.Splits)
    (hg : g.natDegree ≤ 1) (h : Invertible g.leadingCoeff) : (f.comp g).Splits := by
  rcases lt_or_eq_of_le hg with hg | hg
  · rw [eq_C_of_natDegree_eq_zero (Nat.lt_one_iff.mp hg)]
    simp
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset'.mp hf
  rw [hm, mul_comp, C_comp, multiset_prod_comp]
  refine (Splits.C _).mul (multisetProd ?_)
  simp only [Multiset.mem_map]
  rintro - ⟨-, ⟨a, -, rfl⟩, rfl⟩
  apply splits_of_natDegree_le_one_of_invertible (by simpa)
  rw [leadingCoeff, hg] at h
  simpa [leadingCoeff, hg]

theorem Splits.comp_of_degree_le_one_of_invertible {f g : R[X]} (hf : f.Splits)
    (hg : g.degree ≤ 1) (h : Invertible g.leadingCoeff) : (f.comp g).Splits :=
  hf.comp_of_natDegree_le_one_of_invertible (natDegree_le_of_degree_le hg) h

theorem Splits.comp_of_natDegree_le_one_of_monic {f g : R[X]} (hf : f.Splits)
    (hg : g.natDegree ≤ 1) (h : Monic g) : (f.comp g).Splits :=
  hf.comp_of_natDegree_le_one_of_invertible hg (h.leadingCoeff ▸ invertibleOne)

theorem Splits.comp_of_degree_le_one_of_monic {f g : R[X]} (hf : f.Splits)
    (hg : g.degree ≤ 1) (h : Monic g) : (f.comp g).Splits :=
  hf.comp_of_natDegree_le_one_of_monic (natDegree_le_of_degree_le hg) h

theorem Splits.comp_X_add_C {f : R[X]} (hf : f.Splits) (a : R) : (f.comp (X + C a)).Splits :=
  hf.comp_of_natDegree_le_one_of_monic (natDegree_add_C.trans_le natDegree_X_le) (monic_X_add_C a)

theorem Splits.of_algHom {f : R[X]} {A B : Type*} [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (hf : Splits (f.map (algebraMap R A))) (e : A →ₐ[R] B) :
    Splits (f.map (algebraMap R B)) := by
  rw [← e.comp_algebraMap, ← map_map]
  apply hf.map

theorem Splits.of_isScalarTower {f : R[X]} {A : Type*} (B : Type*) [CommSemiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (hf : Splits (f.map (algebraMap R A))) : Splits (f.map (algebraMap R B)) :=
  hf.of_algHom (IsScalarTower.toAlgHom R A B)

end CommSemiring

section Ring

variable [Ring R]

@[simp, aesop safe apply]
theorem Splits.X_sub_C (a : R) : Splits (X - C a) := by
  simpa using Splits.X_add_C (-a)

@[aesop safe apply]
protected theorem Splits.neg {f : R[X]} (hf : Splits f) : Splits (-f) := by
  rw [← neg_one_mul, ← C_1, ← C_neg]
  exact hf.C_mul (-1)

@[simp]
theorem splits_neg_iff {f : R[X]} : Splits (-f) ↔ Splits f :=
  ⟨fun hf ↦ neg_neg f ▸ hf.neg, .neg⟩

theorem Splits.comp_neg_X {f : R[X]} (hf : f.Splits) : (f.comp (-X)).Splits := by
  refine Submonoid.closure_induction ?_ (by simp)
    (fun f g _ _ hf hg ↦ mul_comp_neg_X f g ▸ hf.mul hg) hf
  · rintro f (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · simp
    · rw [add_comp, X_comp, C_comp, neg_add_eq_sub, ← neg_sub]
      exact (X_sub_C a).neg

end Ring

section CommRing

variable [CommRing R] {f g : R[X]}

theorem splits_iff_exists_multiset :
    Splits f ↔ ∃ m : Multiset R, f = C f.leadingCoeff * (m.map (X - C ·)).prod := by
  refine splits_iff_exists_multiset'.trans ⟨?_, ?_⟩ <;>
    rintro ⟨m, hm⟩ <;> exact ⟨m.map (- ·), by simpa⟩

theorem Splits.exists_eval_eq_zero (hf : Splits f) (hf0 : degree f ≠ 0) :
    ∃ a, eval a f = 0 := by
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset.mp hf
  by_cases hf₀ : f.leadingCoeff = 0
  · simp [leadingCoeff_eq_zero.mp hf₀]
  obtain rfl | ⟨a, ha⟩ := m.empty_or_exists_mem
  · rw [hm, Multiset.map_zero, Multiset.prod_zero, mul_one, degree_C hf₀] at hf0
    contradiction
  obtain ⟨m, rfl⟩ := Multiset.exists_cons_of_mem ha
  exact ⟨a, hm ▸ by simp⟩

/-- Pick a root of a polynomial that splits. -/
noncomputable def rootOfSplits (hf : f.Splits) (hfd : f.degree ≠ 0) : R :=
  Classical.choose <| hf.exists_eval_eq_zero hfd

@[simp]
theorem eval_rootOfSplits (hf : f.Splits) (hfd : f.degree ≠ 0) :
    f.eval (rootOfSplits hf hfd) = 0 :=
  Classical.choose_spec <| hf.exists_eval_eq_zero hfd

theorem Splits.comp_X_sub_C (hf : f.Splits) (a : R) : (f.comp (X - C a)).Splits :=
  hf.comp_of_natDegree_le_one_of_monic (natDegree_sub_C.trans_le natDegree_X_le) (monic_X_sub_C a)

variable [IsDomain R]

theorem Splits.eq_prod_roots (hf : Splits f) :
    f = C f.leadingCoeff * (f.roots.map (X - C ·)).prod := by
  by_cases hf0 : f.leadingCoeff = 0
  · simp [leadingCoeff_eq_zero.mp hf0]
  · obtain ⟨m, hm⟩ := splits_iff_exists_multiset.mp hf
    suffices hf : f.roots = m by rwa [hf]
    rw [hm, roots_C_mul _ hf0, roots_multiset_prod_X_sub_C]

theorem Splits.eq_prod_roots_of_monic (hf : Splits f) (hm : f.Monic) :
    f = (f.roots.map (X - C ·)).prod := by
  conv_lhs => rw [hf.eq_prod_roots, hm.leadingCoeff, C_1, one_mul]

theorem Splits.eval_eq_prod_roots (hf : Splits f) (x : R) :
    f.eval x = f.leadingCoeff * (f.roots.map (x - ·)).prod := by
  conv_lhs => rw [hf.eq_prod_roots]
  simp [eval_multiset_prod]

theorem Splits.eval_eq_prod_roots_of_monic (hf : Splits f) (hm : Monic f) (x : R) :
    f.eval x = (f.roots.map (x - ·)).prod := by
  simp [hf.eval_eq_prod_roots, hm]

omit [IsDomain R] in
theorem Splits.aeval_eq_prod_aroots {A : Type*} [CommRing A] [IsDomain A]
    [IsSimpleRing R] [Algebra R A] (hf : (f.map (algebraMap R A)).Splits) (x : A) :
    f.aeval x = algebraMap R A f.leadingCoeff * ((f.aroots A).map (x - ·)).prod := by
  simp [← eval_map_algebraMap, hf.eval_eq_prod_roots]

omit [IsDomain R] in
theorem Splits.aeval_eq_prod_aroots_of_monic {A : Type*} [CommRing A] [IsDomain A]
    [IsSimpleRing R] [Algebra R A] (hf : (f.map (algebraMap R A)).Splits) (hm : Monic f) (x : A) :
    f.aeval x = ((f.aroots A).map (x - ·)).prod := by
  simp [hf.aeval_eq_prod_aroots, hm]

theorem Splits.eval_derivative [DecidableEq R] (hf : f.Splits) (x : R) :
    eval x f.derivative = f.leadingCoeff *
      (f.roots.map fun a ↦ ((f.roots.erase a).map (x - ·)).prod).sum := by
  conv_lhs => rw [hf.eq_prod_roots]
  simp [derivative_prod, eval_multisetSum, eval_multiset_prod]

/-- Let `f` be a monic polynomial over that splits. Let `x` be a root of `f`.
Then $f'(r) = \prod_{a}(x-a)$, where the product in the RHS is taken over all roots of `f`,
with the multiplicity of `x` reduced by one. -/
theorem Splits.eval_root_derivative [DecidableEq R] (hf : f.Splits) (hm : f.Monic) {x : R}
    (hx : x ∈ f.roots) : eval x f.derivative = ((f.roots.erase x).map (x - ·)).prod := by
  rw [← eval_multiset_prod_X_sub_C_derivative hx, ← hf.eq_prod_roots_of_monic hm]

omit [IsDomain R] in
theorem Splits.of_splits_map {S : Type*} [CommRing S] [IsDomain S] [IsSimpleRing R] (i : R →+* S)
    (hf : Splits (f.map i)) (hi : ∀ a ∈ (f.map i).roots, a ∈ i.range) : Splits f := by
  choose j hj using hi
  rw [splits_iff_exists_multiset]
  refine ⟨(f.map i).roots.pmap j fun _ ↦ id, map_injective i i.injective ?_⟩
  conv_lhs => rw [hf.eq_prod_roots]
  simp [Multiset.pmap_eq_map, hj, Multiset.map_pmap, Polynomial.map_multiset_prod]

theorem Splits.mem_lift_of_roots_mem_range (hf : f.Splits) (hm : f.Monic)
    {S : Type*} [Ring S] (i : S →+* R) (hr : ∀ a ∈ f.roots, a ∈ i.range) :
    f ∈ Polynomial.lifts i := by
  rw [hf.eq_prod_roots_of_monic hm, lifts_iff_liftsRing]
  refine Subring.multiset_prod_mem _ _ fun g hg => ?_
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hg
  exact Subring.sub_mem _ (X_mem_lifts i) (C'_mem_lifts (hr x hx))

theorem Splits.eq_X_sub_C_of_single_root (hf : Splits f) {x : R} (hr : f.roots = {x}) :
    f = C f.leadingCoeff * (X - C x) := by
  rw [hf.eq_prod_roots, hr]
  simp

theorem Splits.natDegree_eq_card_roots (hf : Splits f) :
    f.natDegree = f.roots.card := by
  by_cases hf0 : f.leadingCoeff = 0
  · simp [leadingCoeff_eq_zero.mp hf0]
  · conv_lhs => rw [hf.eq_prod_roots, natDegree_C_mul hf0, natDegree_multiset_prod_X_sub_C_eq_card]

theorem Splits.degree_eq_card_roots (hf : Splits f) (hf0 : f ≠ 0) :
    f.degree = f.roots.card :=
  (degree_eq_iff_natDegree_eq hf0).mpr hf.natDegree_eq_card_roots

/-- A polynomial splits if and only if it has as many roots as its degree. -/
theorem splits_iff_card_roots : Splits f ↔ f.roots.card = f.natDegree :=
  ⟨fun h ↦ h.natDegree_eq_card_roots.symm, fun h ↦ splits_iff_exists_multiset.mpr
    ⟨f.roots, (C_leadingCoeff_mul_prod_multiset_X_sub_C h).symm⟩⟩

theorem Splits.roots_ne_zero (hf : Splits f) (hf0 : natDegree f ≠ 0) :
    f.roots ≠ 0 := by
  simpa [hf.natDegree_eq_card_roots] using hf0

theorem Splits.map_roots {S : Type*} [CommRing S] [IsDomain S] [IsSimpleRing R]
    (hf : f.Splits) (i : R →+* S) : (f.map i).roots = f.roots.map i :=
  (roots_map_of_injective_of_card_eq_natDegree i.injective hf.natDegree_eq_card_roots.symm).symm

theorem Splits.mem_range_of_isRoot {S : Type*} [CommRing S] [IsDomain S] [IsSimpleRing R]
    (hf : f.Splits) (hf0 : f ≠ 0) {i : R →+* S} {x : S} (hx : (f.map i).IsRoot x) :
    x ∈ i.range := by
  rw [← mem_roots (map_ne_zero hf0), hf.map_roots, Multiset.mem_map] at hx
  obtain ⟨x, -, hx⟩ := hx
  exact ⟨x, hx⟩

omit [IsDomain R] in
theorem Splits.image_rootSet {A B : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsSimpleRing A] [Algebra R A] [Algebra R B] (hf : (f.map (algebraMap R A)).Splits)
    (g : A →ₐ[R] B) : g '' f.rootSet A = f.rootSet B := by
  classical
  rw [rootSet, ← Finset.coe_image, ← Multiset.toFinset_map, ← g.coe_toRingHom,
    ← hf.map_roots, map_map, g.comp_algebraMap, ← rootSet]

omit [IsDomain R] in
theorem Splits.adjoin_rootSet_eq_range {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [IsSimpleRing A] [Algebra R A] [Algebra R B]
    (hf : (f.map (algebraMap R A)).Splits) (g : A →ₐ[R] B) :
    Algebra.adjoin R (f.rootSet B) = g.range ↔ Algebra.adjoin R (f.rootSet A) = ⊤ := by
  rw [← hf.image_rootSet g, Algebra.adjoin_image, ← Algebra.map_top]
  exact (Subalgebra.map_injective g.injective).eq_iff

theorem Splits.coeff_zero_eq_leadingCoeff_mul_prod_roots (hf : Splits f) :
    f.coeff 0 = (-1) ^ f.natDegree * f.leadingCoeff * f.roots.prod := by
  conv_lhs => rw [hf.eq_prod_roots]
  simp [coeff_zero_eq_eval_zero, eval_multiset_prod, hf.natDegree_eq_card_roots,
    mul_assoc, mul_left_comm]

/-- If `f` is a monic polynomial that splits, then `coeff f 0` equals the product of the roots. -/
theorem Splits.coeff_zero_eq_prod_roots_of_monic (hf : Splits f) (hm : Monic f) :
    coeff f 0 = (-1) ^ f.natDegree * f.roots.prod := by
  simp [hf.coeff_zero_eq_leadingCoeff_mul_prod_roots, hm]

theorem Splits.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff (hf : Splits f) :
    f.nextCoeff = -f.leadingCoeff * f.roots.sum := by
  conv_lhs => rw [hf.eq_prod_roots]
  simp [Multiset.sum_map_neg', monic_X_sub_C, Monic.nextCoeff_multiset_prod]

/-- If `f` is a monic polynomial that splits, then `f.nextCoeff` equals the negative of the sum
of the roots. -/
theorem Splits.nextCoeff_eq_neg_sum_roots_of_monic (hf : Splits f) (hm : Monic f) :
    f.nextCoeff = -f.roots.sum := by
  simp [hf.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff,hm]

theorem splits_X_sub_C_mul_iff {a : R} : Splits ((X - C a) * f) ↔ Splits f := by
  refine ⟨fun hf ↦ ?_, ((Splits.X_sub_C _).mul ·)⟩
  by_cases hf₀ : f = 0
  · aesop
  have := hf.eq_prod_roots
  rw [leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul,
    roots_mul (mul_ne_zero (X_sub_C_ne_zero _) hf₀), roots_X_sub_C,
    Multiset.singleton_add, Multiset.map_cons, Multiset.prod_cons, mul_left_comm] at this
  rw [mul_left_cancel₀ (X_sub_C_ne_zero _) this]
  aesop

theorem splits_mul_iff (hf₀ : f ≠ 0) (hg₀ : g ≠ 0) :
    Splits (f * g) ↔ Splits f ∧ Splits g := by
  refine ⟨fun h ↦ ?_, and_imp.mpr .mul⟩
  generalize hp : f * g = p at *
  generalize hn : p.natDegree = n
  induction n generalizing p f g with
  | zero =>
    rw [← hp, natDegree_mul hf₀ hg₀, Nat.add_eq_zero_iff] at hn
    exact ⟨splits_of_natDegree_eq_zero hn.1, splits_of_natDegree_eq_zero hn.2⟩
  | succ n ih =>
    obtain ⟨a, ha⟩ := Splits.exists_eval_eq_zero h (degree_ne_of_natDegree_ne <| hn ▸ by aesop)
    have := dvd_iff_isRoot.mpr ha
    rw [← hp, (prime_X_sub_C a).dvd_mul] at this
    wlog hf : X - C a ∣ f with hf2
    · exact .symm <| hf2 n ih hg₀ hf₀ p ((mul_comm g f).trans hp) h hn a ha this.symm <|
        this.resolve_left hf
    obtain ⟨f, rfl⟩ := hf
    rw [mul_assoc] at hp; subst hp
    rw [natDegree_mul (by aesop) (by aesop), natDegree_X_sub_C, add_comm, Nat.succ_inj] at hn
    have := ih (by aesop) hg₀ (f * g) rfl  (splits_X_sub_C_mul_iff.mp h) hn
    aesop

theorem Splits.of_dvd (hg : Splits g) (hg₀ : g ≠ 0) (hfg : f ∣ g) : Splits f := by
  obtain ⟨g, rfl⟩ := hfg
  exact ((splits_mul_iff (by aesop) (by aesop)).mp hg).1

@[deprecated (since := "2025-11-27")]
alias Splits.splits_of_dvd := Splits.of_dvd

theorem splits_prod_iff {ι : Type*} {f : ι → R[X]} {s : Finset ι} (hf : ∀ i ∈ s, f i ≠ 0) :
    (∏ x ∈ s, f x).Splits ↔ ∀ x ∈ s, (f x).Splits :=
  ⟨fun h _ hx ↦ h.of_dvd (Finset.prod_ne_zero_iff.mpr hf) (Finset.dvd_prod_of_mem f hx),
    Splits.prod⟩

-- Todo: Remove or fix name once `Splits` is gone.
theorem Splits.splits (hf : Splits f) :
    f = 0 ∨ ∀ {g : R[X]}, Irreducible g → g ∣ f → degree g ≤ 1 :=
  or_iff_not_imp_left.mpr fun hf0 _ hg hgf ↦ degree_le_of_natDegree_le <|
    (hf.of_dvd hf0 hgf).natDegree_le_one_of_irreducible hg

lemma map_sub_sprod_roots_eq_prod_map_eval
    (s : Multiset R) (g : R[X]) (hg : g.Monic) (hg' : g.Splits) :
    ((s ×ˢ g.roots).map fun ij ↦ ij.1 - ij.2).prod = (s.map g.eval).prod := by
  have := hg'.eq_prod_roots
  rw [hg.leadingCoeff, map_one, one_mul] at this
  conv_rhs => rw [this]
  simp_rw [eval_multiset_prod, Multiset.prod_map_product_eq_prod_prod, Multiset.map_map]
  congr! with x hx
  ext; simp

lemma map_sub_roots_sprod_eq_prod_map_eval
    (s : Multiset R) (g : R[X]) (hg : g.Monic) (hg' : g.Splits) :
    ((g.roots ×ˢ s).map fun ij ↦ ij.1 - ij.2).prod =
      (-1) ^ (s.card * g.roots.card) * (s.map g.eval).prod := by
  trans ((s ×ˢ g.roots).map fun ij ↦ (-1) * (ij.1 - ij.2)).prod
  · rw [← Multiset.map_swap_product, Multiset.map_map]; simp
  · rw [Multiset.prod_map_mul]; simp [map_sub_sprod_roots_eq_prod_map_eval _ _ hg hg']

end CommRing

section DivisionSemiring

variable [DivisionSemiring R]

theorem Splits.of_natDegree_le_one {f : R[X]} (hf : natDegree f ≤ 1) : Splits f := by
  obtain ⟨a, b, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hf
  by_cases ha : a = 0
  · aesop
  · rw [← mul_inv_cancel_left₀ ha b, C_mul, ← mul_add]
    exact (X_add_C (a⁻¹ * b)).C_mul a

theorem Splits.of_natDegree_eq_one {f : R[X]} (hf : natDegree f = 1) : Splits f :=
  of_natDegree_le_one hf.le

theorem Splits.of_degree_le_one {f : R[X]} (hf : degree f ≤ 1) : Splits f :=
  of_natDegree_le_one (natDegree_le_of_degree_le hf)

theorem Splits.of_degree_eq_one {f : R[X]} (hf : degree f = 1) : Splits f :=
  of_degree_le_one hf.le

end DivisionSemiring

section Field

variable [Field R] {f g : R[X]}

theorem Splits.dvd_of_roots_le_roots (hp : f.Splits) (hp0 : f ≠ 0) (hq : f.roots ≤ g.roots) :
    f ∣ g := by
  rw [hp.eq_prod_roots, C_mul_dvd (leadingCoeff_ne_zero.2 hp0)]
  exact (Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hq)).trans
    (prod_multiset_X_sub_C_dvd _)

theorem Splits.dvd_iff_roots_le_roots (hf : f.Splits) (hf0 : f ≠ 0) (hg0 : g ≠ 0) :
    f ∣ g ↔ f.roots ≤ g.roots :=
  ⟨roots.le_of_dvd hg0, hf.dvd_of_roots_le_roots hf0⟩

theorem Splits.comp_of_natDegree_le_one {f g : R[X]} (hf : f.Splits) (hg : g.natDegree ≤ 1) :
    (f.comp g).Splits := by
  rcases eq_or_ne g 0 with rfl | hg0
  · simp
  · exact Splits.comp_of_natDegree_le_one_of_invertible hf hg
      (invertibleOfNonzero (leadingCoeff_ne_zero.mpr hg0))

theorem Splits.comp_of_degree_le_one {f g : R[X]} (hf : f.Splits) (hg : g.degree ≤ 1) :
    (f.comp g).Splits :=
  hf.comp_of_natDegree_le_one (natDegree_le_of_degree_le hg)

theorem splits_iff_comp_splits_of_natDegree_eq_one {f g : R[X]} (hg : g.natDegree = 1) :
    f.Splits ↔ (f.comp g).Splits := by
  refine ⟨fun hf ↦ hf.comp_of_natDegree_le_one hg.le, fun hf ↦ ?_⟩
  obtain ⟨a, b, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hg.le
  have ha : a ≠ 0 := by contrapose! hg; simp [hg]
  have : f = (f.comp (C a * X + C b)).comp ((C a⁻¹ * (X - C b))) := by
    simp only [comp_assoc, add_comp, mul_comp, C_comp, X_comp]
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ ha, C_1, one_mul, sub_add_cancel, comp_X]
  rw [this]
  refine Splits.comp_of_natDegree_le_one hf ?_
  rw [natDegree_C_mul (mt inv_eq_zero.mp ha), natDegree_X_sub_C]

theorem splits_iff_comp_splits_of_degree_eq_one {f g : R[X]} (hg : g.degree = 1) :
    f.Splits ↔ (f.comp g).Splits :=
  splits_iff_comp_splits_of_natDegree_eq_one (natDegree_eq_of_degree_eq_some hg)

theorem Splits.degree_eq_one_of_irreducible {f : R[X]} (hf : Splits f)
    (h : Irreducible f) : degree f = 1 :=
  le_antisymm (hf.degree_le_one_of_irreducible h)
    ((WithBot.one_le_iff_pos _).mpr (degree_pos_of_irreducible h))

theorem Splits.natDegree_eq_one_of_irreducible {f : R[X]} (hf : Splits f)
    (h : Irreducible f) : natDegree f = 1 :=
  natDegree_eq_of_degree_eq_some (hf.degree_eq_one_of_irreducible h)

theorem Splits.eval_derivative_eq_eval_mul_sum (hf : Splits f) {x : R} (hx : f.eval x ≠ 0) :
    f.derivative.eval x = f.eval x * (f.roots.map fun z ↦ 1 / (x - z)).sum := by
  classical
  simp only [hf.eval_derivative, hf.eval_eq_prod_roots, ← Multiset.sum_map_mul_left, mul_assoc]
  refine congr_arg Multiset.sum (Multiset.map_congr rfl fun z hz ↦ ?_)
  rw [← Multiset.prod_map_erase hz, mul_one_div, mul_div_cancel_left₀]
  aesop (add simp sub_eq_zero)

theorem Splits.eval_derivative_div_eval_of_ne_zero (hf : Splits f) {x : R} (hx : f.eval x ≠ 0) :
    f.derivative.eval x / f.eval x = (f.roots.map fun z ↦ 1 / (x - z)).sum := by
  rw [hf.eval_derivative_eq_eval_mul_sum hx, mul_div_cancel_left₀ _ hx]

theorem Splits.mem_subfield_of_isRoot (F : Subfield R) {f : F[X]} (hf : Splits f) (hf0 : f ≠ 0)
    {x : R} (hx : (f.map F.subtype).IsRoot x) : x ∈ F := by
  simpa using hf.mem_range_of_isRoot hf0 hx

/-- A polynomial of degree `2` with a root splits. -/
theorem Splits.of_natDegree_eq_two {x : R} (h₁ : f.natDegree = 2) (h₂ : f.eval x = 0) :
    Splits f := by
  have h : (f /ₘ (X - C x)).natDegree = 1 := by
    rw [natDegree_divByMonic f (monic_X_sub_C x), h₁, natDegree_X_sub_C]
  rw [← mul_divByMonic_eq_iff_isRoot.mpr h₂, splits_mul_iff (X_sub_C_ne_zero x) (by aesop)]
  exact ⟨Splits.X_sub_C x, Splits.of_natDegree_eq_one h⟩

theorem Splits.of_degree_eq_two {x : R} (h₁ : f.degree = 2) (h₂ : f.eval x = 0) : Splits f :=
  Splits.of_natDegree_eq_two (natDegree_eq_of_degree_eq_some h₁) h₂

open UniqueFactorizationMonoid in
-- Todo: Remove or fix name.
theorem splits_iff_splits {f : R[X]} :
    Splits f ↔ f = 0 ∨ ∀ {g : R[X]}, Irreducible g → g ∣ f → degree g = 1 := by
  refine ⟨fun hf ↦ hf.splits.imp_right (forall₃_imp fun g hg hgf ↦
    (le_antisymm · (Nat.WithBot.one_le_iff_zero_lt.mpr hg.degree_pos))), ?_⟩
  rintro (rfl | hf)
  · aesop
  classical
  by_cases hf0 : f = 0
  · simp [hf0]
  obtain ⟨u, hu⟩ := factors_prod hf0
  rw [← hu]
  refine (Splits.multisetProd fun g hg ↦ ?_).mul u.isUnit.splits
  exact Splits.of_degree_eq_one (hf (irreducible_of_factor g hg) (dvd_of_mem_factors hg))

end Field

end Polynomial
