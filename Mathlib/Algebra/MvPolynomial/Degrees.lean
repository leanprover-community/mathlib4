/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
import Mathlib.Algebra.MonoidAlgebra.Degree
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

#align_import data.mv_polynomial.variables from "leanprover-community/mathlib"@"2f5b500a507264de86d666a5f87ddb976e2d8de4"

/-!
# Degrees of polynomials

This file establishes many results about the degree of a multivariate polynomial.

The *degree set* of a polynomial $P \in R[X]$ is a `Multiset` containing, for each $x$ in the
variable set, $n$ copies of $x$, where $n$ is the maximum number of copies of $x$ appearing in a
monomial of $P$.

## Main declarations

* `MvPolynomial.degrees p` : the multiset of variables representing the union of the multisets
  corresponding to each non-zero monomial in `p`.
  For example if `7 ≠ 0` in `R` and `p = x²y+7y³` then `degrees p = {x, x, y, y, y}`

* `MvPolynomial.degreeOf n p : ℕ` : the total degree of `p` with respect to the variable `n`.
  For example if `p = x⁴y+yz` then `degreeOf y p = 1`.

* `MvPolynomial.totalDegree p : ℕ` :
  the max of the sizes of the multisets `s` whose monomials `X^s` occur in `p`.
  For example if `p = x⁴y+yz` then `totalDegree p = 5`.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ τ : Type*` (indexing the variables)

+ `R : Type*` `[CommSemiring R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `MvPolynomial σ R` which mathematicians might call `X^s`

+ `r : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : MvPolynomial σ R`

-/


noncomputable section

open Set Function Finsupp AddMonoidAlgebra

universe u v w

variable {R : Type u} {S : Type v}

namespace MvPolynomial

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section CommSemiring

variable [CommSemiring R] {p q : MvPolynomial σ R}

section Degrees

/-! ### `degrees` -/


/-- The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset.

(For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
-/
def degrees (p : MvPolynomial σ R) : Multiset σ :=
  letI := Classical.decEq σ
  p.support.sup fun s : σ →₀ ℕ => toMultiset s
#align mv_polynomial.degrees MvPolynomial.degrees

theorem degrees_def [DecidableEq σ] (p : MvPolynomial σ R) :
    p.degrees = p.support.sup fun s : σ →₀ ℕ => Finsupp.toMultiset s := by rw [degrees]; convert rfl
#align mv_polynomial.degrees_def MvPolynomial.degrees_def

theorem degrees_monomial (s : σ →₀ ℕ) (a : R) : degrees (monomial s a) ≤ toMultiset s := by
  classical
    refine (supDegree_single s a).trans_le ?_
    split_ifs
    exacts [bot_le, le_rfl]
#align mv_polynomial.degrees_monomial MvPolynomial.degrees_monomial

theorem degrees_monomial_eq (s : σ →₀ ℕ) (a : R) (ha : a ≠ 0) :
    degrees (monomial s a) = toMultiset s := by
  classical
    exact (supDegree_single s a).trans (if_neg ha)
#align mv_polynomial.degrees_monomial_eq MvPolynomial.degrees_monomial_eq

theorem degrees_C (a : R) : degrees (C a : MvPolynomial σ R) = 0 :=
  Multiset.le_zero.1 <| degrees_monomial _ _
set_option linter.uppercaseLean3 false in
#align mv_polynomial.degrees_C MvPolynomial.degrees_C

theorem degrees_X' (n : σ) : degrees (X n : MvPolynomial σ R) ≤ {n} :=
  le_trans (degrees_monomial _ _) <| le_of_eq <| toMultiset_single _ _
set_option linter.uppercaseLean3 false in
#align mv_polynomial.degrees_X' MvPolynomial.degrees_X'

@[simp]
theorem degrees_X [Nontrivial R] (n : σ) : degrees (X n : MvPolynomial σ R) = {n} :=
  (degrees_monomial_eq _ (1 : R) one_ne_zero).trans (toMultiset_single _ _)
set_option linter.uppercaseLean3 false in
#align mv_polynomial.degrees_X MvPolynomial.degrees_X

@[simp]
theorem degrees_zero : degrees (0 : MvPolynomial σ R) = 0 := by
  rw [← C_0]
  exact degrees_C 0
#align mv_polynomial.degrees_zero MvPolynomial.degrees_zero

@[simp]
theorem degrees_one : degrees (1 : MvPolynomial σ R) = 0 :=
  degrees_C 1
#align mv_polynomial.degrees_one MvPolynomial.degrees_one

theorem degrees_add [DecidableEq σ] (p q : MvPolynomial σ R) :
    (p + q).degrees ≤ p.degrees ⊔ q.degrees := by
  simp_rw [degrees_def]; exact supDegree_add_le
#align mv_polynomial.degrees_add MvPolynomial.degrees_add

theorem degrees_sum {ι : Type*} [DecidableEq σ] (s : Finset ι) (f : ι → MvPolynomial σ R) :
    (∑ i ∈ s, f i).degrees ≤ s.sup fun i => (f i).degrees := by
  simp_rw [degrees_def]; exact supDegree_sum_le
#align mv_polynomial.degrees_sum MvPolynomial.degrees_sum

theorem degrees_mul (p q : MvPolynomial σ R) : (p * q).degrees ≤ p.degrees + q.degrees := by
  classical
  simp_rw [degrees_def]
  exact supDegree_mul_le (map_add _)
#align mv_polynomial.degrees_mul MvPolynomial.degrees_mul

theorem degrees_prod {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R) :
    (∏ i ∈ s, f i).degrees ≤ ∑ i ∈ s, (f i).degrees := by
  classical exact supDegree_prod_le (map_zero _) (map_add _)
#align mv_polynomial.degrees_prod MvPolynomial.degrees_prod

theorem degrees_pow (p : MvPolynomial σ R) (n : ℕ) : (p ^ n).degrees ≤ n • p.degrees := by
  simpa using degrees_prod (Finset.range n) fun _ ↦ p
#align mv_polynomial.degrees_pow MvPolynomial.degrees_pow

theorem mem_degrees {p : MvPolynomial σ R} {i : σ} :
    i ∈ p.degrees ↔ ∃ d, p.coeff d ≠ 0 ∧ i ∈ d.support := by
  classical
  simp only [degrees_def, Multiset.mem_sup, ← mem_support_iff, Finsupp.mem_toMultiset, exists_prop]
#align mv_polynomial.mem_degrees MvPolynomial.mem_degrees

theorem le_degrees_add {p q : MvPolynomial σ R} (h : p.degrees.Disjoint q.degrees) :
    p.degrees ≤ (p + q).degrees := by
  classical
  apply Finset.sup_le
  intro d hd
  rw [Multiset.disjoint_iff_ne] at h
  obtain rfl | h0 := eq_or_ne d 0
  · rw [toMultiset_zero]; apply Multiset.zero_le
  · refine Finset.le_sup_of_le (b := d) ?_ le_rfl
    rw [mem_support_iff, coeff_add]
    suffices q.coeff d = 0 by rwa [this, add_zero, coeff, ← Finsupp.mem_support_iff]
    rw [Ne, ← Finsupp.support_eq_empty, ← Ne, ← Finset.nonempty_iff_ne_empty] at h0
    obtain ⟨j, hj⟩ := h0
    contrapose! h
    rw [mem_support_iff] at hd
    refine ⟨j, ?_, j, ?_, rfl⟩
    all_goals rw [mem_degrees]; refine ⟨d, ?_, hj⟩; assumption
#align mv_polynomial.le_degrees_add MvPolynomial.le_degrees_add

theorem degrees_add_of_disjoint [DecidableEq σ] {p q : MvPolynomial σ R}
    (h : Multiset.Disjoint p.degrees q.degrees) : (p + q).degrees = p.degrees ∪ q.degrees := by
  apply le_antisymm
  · apply degrees_add
  · apply Multiset.union_le
    · apply le_degrees_add h
    · rw [add_comm]
      apply le_degrees_add h.symm
#align mv_polynomial.degrees_add_of_disjoint MvPolynomial.degrees_add_of_disjoint

theorem degrees_map [CommSemiring S] (p : MvPolynomial σ R) (f : R →+* S) :
    (map f p).degrees ⊆ p.degrees := by
  classical
  dsimp only [degrees]
  apply Multiset.subset_of_le
  apply Finset.sup_mono
  apply MvPolynomial.support_map_subset
#align mv_polynomial.degrees_map MvPolynomial.degrees_map

theorem degrees_rename (f : σ → τ) (φ : MvPolynomial σ R) :
    (rename f φ).degrees ⊆ φ.degrees.map f := by
  classical
  intro i
  rw [mem_degrees, Multiset.mem_map]
  rintro ⟨d, hd, hi⟩
  obtain ⟨x, rfl, hx⟩ := coeff_rename_ne_zero _ _ _ hd
  simp only [Finsupp.mapDomain, Finsupp.mem_support_iff] at hi
  rw [sum_apply, Finsupp.sum] at hi
  contrapose! hi
  rw [Finset.sum_eq_zero]
  intro j hj
  simp only [exists_prop, mem_degrees] at hi
  specialize hi j ⟨x, hx, hj⟩
  rw [Finsupp.single_apply, if_neg hi]
#align mv_polynomial.degrees_rename MvPolynomial.degrees_rename

theorem degrees_map_of_injective [CommSemiring S] (p : MvPolynomial σ R) {f : R →+* S}
    (hf : Injective f) : (map f p).degrees = p.degrees := by
  simp only [degrees, MvPolynomial.support_map_of_injective _ hf]
#align mv_polynomial.degrees_map_of_injective MvPolynomial.degrees_map_of_injective

theorem degrees_rename_of_injective {p : MvPolynomial σ R} {f : σ → τ} (h : Function.Injective f) :
    degrees (rename f p) = (degrees p).map f := by
  classical
  simp only [degrees, Multiset.map_finset_sup p.support Finsupp.toMultiset f h,
    support_rename_of_injective h, Finset.sup_image]
  refine Finset.sup_congr rfl fun x _ => ?_
  exact (Finsupp.toMultiset_map _ _).symm
#align mv_polynomial.degrees_rename_of_injective MvPolynomial.degrees_rename_of_injective

end Degrees

section DegreeOf

/-! ### `degreeOf` -/


/-- `degreeOf n p` gives the highest power of X_n that appears in `p` -/
def degreeOf (n : σ) (p : MvPolynomial σ R) : ℕ :=
  letI := Classical.decEq σ
  p.degrees.count n
#align mv_polynomial.degree_of MvPolynomial.degreeOf

theorem degreeOf_def [DecidableEq σ] (n : σ) (p : MvPolynomial σ R) :
    p.degreeOf n = p.degrees.count n := by rw [degreeOf]; convert rfl
#align mv_polynomial.degree_of_def MvPolynomial.degreeOf_def

theorem degreeOf_eq_sup (n : σ) (f : MvPolynomial σ R) :
    degreeOf n f = f.support.sup fun m => m n := by
  classical
  rw [degreeOf_def, degrees, Multiset.count_finset_sup]
  congr
  ext
  simp
#align mv_polynomial.degree_of_eq_sup MvPolynomial.degreeOf_eq_sup

theorem degreeOf_lt_iff {n : σ} {f : MvPolynomial σ R} {d : ℕ} (h : 0 < d) :
    degreeOf n f < d ↔ ∀ m : σ →₀ ℕ, m ∈ f.support → m n < d := by
  rwa [degreeOf_eq_sup, Finset.sup_lt_iff]
#align mv_polynomial.degree_of_lt_iff MvPolynomial.degreeOf_lt_iff

lemma degreeOf_le_iff {n : σ} {f : MvPolynomial σ R} {d : ℕ} :
    degreeOf n f ≤ d ↔ ∀ m ∈ support f, m n ≤ d := by
  rw [degreeOf_eq_sup, Finset.sup_le_iff]

@[simp]
theorem degreeOf_zero (n : σ) : degreeOf n (0 : MvPolynomial σ R) = 0 := by
  classical simp only [degreeOf_def, degrees_zero, Multiset.count_zero]
#align mv_polynomial.degree_of_zero MvPolynomial.degreeOf_zero

@[simp]
theorem degreeOf_C (a : R) (x : σ) : degreeOf x (C a : MvPolynomial σ R) = 0 := by
  classical simp [degreeOf_def, degrees_C]
set_option linter.uppercaseLean3 false in
#align mv_polynomial.degree_of_C MvPolynomial.degreeOf_C

theorem degreeOf_X [DecidableEq σ] (i j : σ) [Nontrivial R] :
    degreeOf i (X j : MvPolynomial σ R) = if i = j then 1 else 0 := by
  classical
  by_cases c : i = j
  · simp only [c, if_true, eq_self_iff_true, degreeOf_def, degrees_X, Multiset.count_singleton]
  simp [c, if_false, degreeOf_def, degrees_X]
set_option linter.uppercaseLean3 false in
#align mv_polynomial.degree_of_X MvPolynomial.degreeOf_X

theorem degreeOf_add_le (n : σ) (f g : MvPolynomial σ R) :
    degreeOf n (f + g) ≤ max (degreeOf n f) (degreeOf n g) := by
  simp_rw [degreeOf_eq_sup]; exact supDegree_add_le
#align mv_polynomial.degree_of_add_le MvPolynomial.degreeOf_add_le

theorem monomial_le_degreeOf (i : σ) {f : MvPolynomial σ R} {m : σ →₀ ℕ} (h_m : m ∈ f.support) :
    m i ≤ degreeOf i f := by
  rw [degreeOf_eq_sup i]
  apply Finset.le_sup h_m
#align mv_polynomial.monomial_le_degree_of MvPolynomial.monomial_le_degreeOf

-- TODO we can prove equality here if R is a domain
theorem degreeOf_mul_le (i : σ) (f g : MvPolynomial σ R) :
    degreeOf i (f * g) ≤ degreeOf i f + degreeOf i g := by
  classical
  repeat' rw [degreeOf]
  convert Multiset.count_le_of_le i (degrees_mul f g)
  rw [Multiset.count_add]
#align mv_polynomial.degree_of_mul_le MvPolynomial.degreeOf_mul_le

theorem degreeOf_mul_X_ne {i j : σ} (f : MvPolynomial σ R) (h : i ≠ j) :
    degreeOf i (f * X j) = degreeOf i f := by
  classical
  repeat' rw [degreeOf_eq_sup (R := R) i]
  rw [support_mul_X]
  simp only [Finset.sup_map]
  congr
  ext
  simp only [Finsupp.single, Nat.one_ne_zero, add_right_eq_self, addRightEmbedding_apply, coe_mk,
    Pi.add_apply, comp_apply, ite_eq_right_iff, Finsupp.coe_add, Pi.single_eq_of_ne h]
set_option linter.uppercaseLean3 false in
#align mv_polynomial.degree_of_mul_X_ne MvPolynomial.degreeOf_mul_X_ne

-- TODO in the following we have equality iff f ≠ 0
theorem degreeOf_mul_X_eq (j : σ) (f : MvPolynomial σ R) :
    degreeOf j (f * X j) ≤ degreeOf j f + 1 := by
  classical
  repeat' rw [degreeOf]
  apply (Multiset.count_le_of_le j (degrees_mul f (X j))).trans
  simp only [Multiset.count_add, add_le_add_iff_left]
  convert Multiset.count_le_of_le j (degrees_X' (R := R) j)
  rw [Multiset.count_singleton_self]
set_option linter.uppercaseLean3 false in
#align mv_polynomial.degree_of_mul_X_eq MvPolynomial.degreeOf_mul_X_eq

theorem degreeOf_C_mul_le (p : MvPolynomial σ R) (i : σ) (c : R) :
    (C c * p).degreeOf i ≤ p.degreeOf i := by
  unfold degreeOf
  convert Multiset.count_le_of_le i <| degrees_mul (C c) p
  simp [degrees_C]

theorem degreeOf_mul_C_le (p : MvPolynomial σ R) (i : σ) (c : R) :
    (p * C c).degreeOf i ≤ p.degreeOf i := by
  unfold degreeOf
  convert Multiset.count_le_of_le i <| degrees_mul p (C c)
  simp [degrees_C]

theorem degreeOf_rename_of_injective {p : MvPolynomial σ R} {f : σ → τ} (h : Function.Injective f)
    (i : σ) : degreeOf (f i) (rename f p) = degreeOf i p := by
  classical
  simp only [degreeOf, degrees_rename_of_injective h, Multiset.count_map_eq_count' f p.degrees h]
#align mv_polynomial.degree_of_rename_of_injective MvPolynomial.degreeOf_rename_of_injective

end DegreeOf

section TotalDegree

/-! ### `totalDegree` -/


/-- `totalDegree p` gives the maximum |s| over the monomials X^s in `p` -/
def totalDegree (p : MvPolynomial σ R) : ℕ :=
  p.support.sup fun s => s.sum fun _ e => e
#align mv_polynomial.total_degree MvPolynomial.totalDegree

theorem totalDegree_eq (p : MvPolynomial σ R) :
    p.totalDegree = p.support.sup fun m => Multiset.card (toMultiset m) := by
  rw [totalDegree]
  congr; funext m
  exact (Finsupp.card_toMultiset _).symm
#align mv_polynomial.total_degree_eq MvPolynomial.totalDegree_eq

theorem le_totalDegree {p : MvPolynomial σ R} {s : σ →₀ ℕ} (h : s ∈ p.support) :
    (s.sum fun _ e => e) ≤ totalDegree p :=
  Finset.le_sup (α := ℕ) (f := fun s => sum s fun _ e => e) h

theorem totalDegree_le_degrees_card (p : MvPolynomial σ R) :
    p.totalDegree ≤ Multiset.card p.degrees := by
  classical
  rw [totalDegree_eq]
  exact Finset.sup_le fun s hs => Multiset.card_le_card <| Finset.le_sup hs
#align mv_polynomial.total_degree_le_degrees_card MvPolynomial.totalDegree_le_degrees_card

theorem totalDegree_le_of_support_subset (h : p.support ⊆ q.support) :
    totalDegree p ≤ totalDegree q :=
  Finset.sup_mono h

@[simp]
theorem totalDegree_C (a : R) : (C a : MvPolynomial σ R).totalDegree = 0 :=
  (supDegree_single 0 a).trans <| by rw [sum_zero_index, bot_eq_zero', ite_self]
set_option linter.uppercaseLean3 false in
#align mv_polynomial.total_degree_C MvPolynomial.totalDegree_C

@[simp]
theorem totalDegree_zero : (0 : MvPolynomial σ R).totalDegree = 0 := by
  rw [← C_0]; exact totalDegree_C (0 : R)
#align mv_polynomial.total_degree_zero MvPolynomial.totalDegree_zero

@[simp]
theorem totalDegree_one : (1 : MvPolynomial σ R).totalDegree = 0 :=
  totalDegree_C (1 : R)
#align mv_polynomial.total_degree_one MvPolynomial.totalDegree_one

@[simp]
theorem totalDegree_X {R} [CommSemiring R] [Nontrivial R] (s : σ) :
    (X s : MvPolynomial σ R).totalDegree = 1 := by
  rw [totalDegree, support_X]
  simp only [Finset.sup, Finsupp.sum_single_index, Finset.fold_singleton, sup_bot_eq]
set_option linter.uppercaseLean3 false in
#align mv_polynomial.total_degree_X MvPolynomial.totalDegree_X

theorem totalDegree_add (a b : MvPolynomial σ R) :
    (a + b).totalDegree ≤ max a.totalDegree b.totalDegree :=
  sup_support_add_le _ _ _
#align mv_polynomial.total_degree_add MvPolynomial.totalDegree_add

theorem totalDegree_add_eq_left_of_totalDegree_lt {p q : MvPolynomial σ R}
    (h : q.totalDegree < p.totalDegree) : (p + q).totalDegree = p.totalDegree := by
  classical
    apply le_antisymm
    · rw [← max_eq_left_of_lt h]
      exact totalDegree_add p q
    by_cases hp : p = 0
    · simp [hp]
    obtain ⟨b, hb₁, hb₂⟩ :=
      p.support.exists_mem_eq_sup (Finsupp.support_nonempty_iff.mpr hp) fun m : σ →₀ ℕ =>
        Multiset.card (toMultiset m)
    have hb : ¬b ∈ q.support := by
      contrapose! h
      rw [totalDegree_eq p, hb₂, totalDegree_eq]
      apply Finset.le_sup h
    have hbb : b ∈ (p + q).support := by
      apply support_sdiff_support_subset_support_add
      rw [Finset.mem_sdiff]
      exact ⟨hb₁, hb⟩
    rw [totalDegree_eq, hb₂, totalDegree_eq]
    exact Finset.le_sup (f := fun m => Multiset.card (Finsupp.toMultiset m)) hbb
#align mv_polynomial.total_degree_add_eq_left_of_total_degree_lt MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt

theorem totalDegree_add_eq_right_of_totalDegree_lt {p q : MvPolynomial σ R}
    (h : q.totalDegree < p.totalDegree) : (q + p).totalDegree = p.totalDegree := by
  rw [add_comm, totalDegree_add_eq_left_of_totalDegree_lt h]
#align mv_polynomial.total_degree_add_eq_right_of_total_degree_lt MvPolynomial.totalDegree_add_eq_right_of_totalDegree_lt

theorem totalDegree_mul (a b : MvPolynomial σ R) :
    (a * b).totalDegree ≤ a.totalDegree + b.totalDegree :=
  sup_support_mul_le (by exact (Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)).le) _ _
#align mv_polynomial.total_degree_mul MvPolynomial.totalDegree_mul

theorem totalDegree_smul_le [CommSemiring S] [DistribMulAction R S] (a : R) (f : MvPolynomial σ S) :
    (a • f).totalDegree ≤ f.totalDegree :=
  Finset.sup_mono support_smul
#align mv_polynomial.total_degree_smul_le MvPolynomial.totalDegree_smul_le

theorem totalDegree_pow (a : MvPolynomial σ R) (n : ℕ) :
    (a ^ n).totalDegree ≤ n * a.totalDegree := by
  rw [Finset.pow_eq_prod_const, ← Nat.nsmul_eq_mul, Finset.nsmul_eq_sum_const]
  refine supDegree_prod_le rfl (fun _ _ => ?_)
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)
#align mv_polynomial.total_degree_pow MvPolynomial.totalDegree_pow

@[simp]
theorem totalDegree_monomial (s : σ →₀ ℕ) {c : R} (hc : c ≠ 0) :
    (monomial s c : MvPolynomial σ R).totalDegree = s.sum fun _ e => e := by
  classical simp [totalDegree, support_monomial, if_neg hc]
#align mv_polynomial.total_degree_monomial MvPolynomial.totalDegree_monomial

theorem totalDegree_monomial_le (s : σ →₀ ℕ) (c : R) :
    (monomial s c).totalDegree ≤ s.sum fun _ ↦ id := by
  if hc : c = 0 then
    simp only [hc, map_zero, totalDegree_zero, zero_le]
  else
    rw [totalDegree_monomial _ hc]
    exact le_rfl

@[simp]
theorem totalDegree_X_pow [Nontrivial R] (s : σ) (n : ℕ) :
    (X s ^ n : MvPolynomial σ R).totalDegree = n := by simp [X_pow_eq_monomial, one_ne_zero]
set_option linter.uppercaseLean3 false in
#align mv_polynomial.total_degree_X_pow MvPolynomial.totalDegree_X_pow

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem totalDegree_list_prod :
    ∀ s : List (MvPolynomial σ R), s.prod.totalDegree ≤ (s.map MvPolynomial.totalDegree).sum
  | [] => by rw [@List.prod_nil (MvPolynomial σ R) _, totalDegree_one]; rfl
  | p::ps => by
    rw [@List.prod_cons (MvPolynomial σ R) _, List.map, List.sum_cons]
    exact le_trans (totalDegree_mul _ _) (add_le_add_left (totalDegree_list_prod ps) _)
#align mv_polynomial.total_degree_list_prod MvPolynomial.totalDegree_list_prod

theorem totalDegree_multiset_prod (s : Multiset (MvPolynomial σ R)) :
    s.prod.totalDegree ≤ (s.map MvPolynomial.totalDegree).sum := by
  refine Quotient.inductionOn s fun l => ?_
  rw [Multiset.quot_mk_to_coe, Multiset.prod_coe, Multiset.map_coe, Multiset.sum_coe]
  exact totalDegree_list_prod l
#align mv_polynomial.total_degree_multiset_prod MvPolynomial.totalDegree_multiset_prod

theorem totalDegree_finset_prod {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R) :
    (s.prod f).totalDegree ≤ ∑ i ∈ s, (f i).totalDegree := by
  refine le_trans (totalDegree_multiset_prod _) ?_
  rw [Multiset.map_map]
  rfl
#align mv_polynomial.total_degree_finset_prod MvPolynomial.totalDegree_finset_prod

theorem totalDegree_finset_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R) :
    (s.sum f).totalDegree ≤ Finset.sup s fun i => (f i).totalDegree := by
  induction' s using Finset.cons_induction with a s has hind
  · exact zero_le _
  · rw [Finset.sum_cons, Finset.sup_cons, sup_eq_max]
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le_max le_rfl hind)
#align mv_polynomial.total_degree_finset_sum MvPolynomial.totalDegree_finset_sum

lemma degreeOf_le_totalDegree (f : MvPolynomial σ R) (i : σ) : f.degreeOf i ≤ f.totalDegree :=
  degreeOf_le_iff.mpr fun d hd ↦ (eq_or_ne (d i) 0).elim (·.trans_le zero_le') fun h ↦
    (Finset.single_le_sum (fun _ _ ↦ zero_le') <| Finsupp.mem_support_iff.mpr h).trans
    (le_totalDegree hd)

theorem exists_degree_lt [Fintype σ] (f : MvPolynomial σ R) (n : ℕ)
    (h : f.totalDegree < n * Fintype.card σ) {d : σ →₀ ℕ} (hd : d ∈ f.support) : ∃ i, d i < n := by
  contrapose! h
  calc
    n * Fintype.card σ = ∑ _s : σ, n := by
      rw [Finset.sum_const, Nat.nsmul_eq_mul, mul_comm, Finset.card_univ]
    _ ≤ ∑ s, d s := Finset.sum_le_sum fun s _ => h s
    _ ≤ d.sum fun _ e => e := by
      rw [Finsupp.sum_fintype]
      intros
      rfl
    _ ≤ f.totalDegree := le_totalDegree hd
#align mv_polynomial.exists_degree_lt MvPolynomial.exists_degree_lt

theorem coeff_eq_zero_of_totalDegree_lt {f : MvPolynomial σ R} {d : σ →₀ ℕ}
    (h : f.totalDegree < ∑ i ∈ d.support, d i) : coeff d f = 0 := by
  classical
    rw [totalDegree, Finset.sup_lt_iff] at h
    · specialize h d
      rw [mem_support_iff] at h
      refine not_not.mp (mt h ?_)
      exact lt_irrefl _
    · exact lt_of_le_of_lt (Nat.zero_le _) h
#align mv_polynomial.coeff_eq_zero_of_total_degree_lt MvPolynomial.coeff_eq_zero_of_totalDegree_lt

theorem totalDegree_rename_le (f : σ → τ) (p : MvPolynomial σ R) :
    (rename f p).totalDegree ≤ p.totalDegree :=
  Finset.sup_le fun b => by
    classical
    intro h
    rw [rename_eq] at h
    have h' := Finsupp.mapDomain_support h
    rw [Finset.mem_image] at h'
    rcases h' with ⟨s, hs, rfl⟩
    exact (sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)).trans_le (le_totalDegree hs)
#align mv_polynomial.total_degree_rename_le MvPolynomial.totalDegree_rename_le

end TotalDegree

end CommSemiring

end MvPolynomial
