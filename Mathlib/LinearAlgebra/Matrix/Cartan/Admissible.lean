/-
Copyright (c) 2026 Ambrose Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ambrose Tang
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

import Mathlib.Analysis.Matrix.PosDefIntCast

/-!
# Admissible Gram matrices of finite Cartan matrices

Humphreys classifies Dynkin diagrams by looking at the unit vectors `εᵢ = αᵢ / ‖αᵢ‖` in the
directions of the simple roots. Their Gram matrix `A` is positive definite, has `1` on the
diagonal, and has off-diagonal entries `Aᵢⱼ = -√(Mᵢⱼ Mⱼᵢ) / 2`. We never need the vectors
themselves: every argument is a computation with `A`.

This file builds `A` directly from an integer matrix (`Matrix.cartanGram`), shows that it is
admissible when `M` is a finite Cartan matrix, and proves the one inequality that the whole
classification rests on (`Matrix.IsFiniteCartan.sum_mul_lt_four`):

> If `S` is a set of nodes whose "unit vector" `∑_{s ∈ S} εₛ` has length at most one (for
> example a path in the Dynkin diagram) and `N` is disjoint from `S`, then the numbers of bonds
> `Mₛⱼ Mⱼₛ` between `S` and `N` add up to less than `4`.

Taking `S` to be a single node gives Humphreys' step (4); taking `S` to be a path gives his steps
(6) and (7) without having to contract the path.

## Main definitions

* `Matrix.IsAdmissible`: a positive definite real matrix with unit diagonal, non-positive
  off-diagonal entries, and `4 Aᵢⱼ² ∈ {0, 1, 2, 3}`.
* `Matrix.cartanGram`: the normalised Gram matrix `Aᵢⱼ = -√(Mᵢⱼ Mⱼᵢ) / 2` of an integer matrix.

## Main results

* `Matrix.IsFiniteCartan.isAdmissible_cartanGram`: the normalised Gram matrix is admissible.
* `Matrix.IsFiniteCartan.sum_mul_lt_four`: the master inequality described above.
* `Matrix.IsFiniteCartan.cartanGram_sum_path_le`: the indices of a path satisfy `‖∑ εₛ‖ ≤ 1`.

## References

* [J. Humphreys, *Introduction to Lie Algebras and Representation Theory*][humphreys1972]
  §11.4
-/

@[expose] public section

open Finset

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-! ### Admissible matrices -/

/-- A real matrix is *admissible* if it is the Gram matrix of linearly independent unit vectors
meeting at obtuse angles whose squared cosines are `0`, `1/4`, `2/4` or `3/4`. These are
Humphreys' admissible sets, recorded through their Gram matrix. -/
structure IsAdmissible (A : Matrix ι ι ℝ) : Prop where
  posDef : A.PosDef
  diag_eq_one : ∀ i, A i i = 1
  offDiag_nonpos : ∀ i j, i ≠ j → A i j ≤ 0
  four_mul_sq : ∀ i j, i ≠ j → ∃ k : ℕ, k < 4 ∧ 4 * A i j ^ 2 = k

/-- The normalised Gram matrix of an integer matrix: `1` on the diagonal and `-√(Mᵢⱼ Mⱼᵢ) / 2`
off it. For a finite Cartan matrix these are the inner products `(εᵢ, εⱼ)` of the unit vectors
along the simple roots. -/
noncomputable def cartanGram (M : Matrix ι ι ℤ) : Matrix ι ι ℝ :=
  of fun i j ↦ if i = j then 1 else -√((M i j * M j i : ℤ) : ℝ) / 2

omit [Fintype ι] in
@[simp] lemma cartanGram_apply_self (M : Matrix ι ι ℤ) (i : ι) : cartanGram M i i = 1 := by
  simp [cartanGram]

omit [Fintype ι] in
lemma cartanGram_apply_of_ne (M : Matrix ι ι ℤ) {i j : ι} (h : i ≠ j) :
    cartanGram M i j = -√((M i j * M j i : ℤ) : ℝ) / 2 := by
  simp [cartanGram, h]

omit [Fintype ι] [Fintype κ] in
lemma cartanGram_submatrix (M : Matrix ι ι ℤ) {f : κ → ι} (hf : Function.Injective f) :
    cartanGram (M.submatrix f f) = (cartanGram M).submatrix f f := by
  ext i j
  simp [cartanGram, hf.eq_iff]

namespace IsFiniteCartan

variable {M : Matrix ι ι ℤ} (hM : M.IsFiniteCartan)
include hM

lemma four_mul_cartanGram_sq {i j : ι} (h : i ≠ j) :
    4 * cartanGram M i j ^ 2 = ((M i j * M j i : ℤ) : ℝ) := by
  have : (0 : ℝ) ≤ ((M i j * M j i : ℤ) : ℝ) := by exact_mod_cast hM.mul_nonneg_of_ne h
  rw [cartanGram_apply_of_ne _ h, div_pow, neg_sq, Real.sq_sqrt this]
  ring

lemma cartanGram_eq_zero_iff {i j : ι} (h : i ≠ j) : cartanGram M i j = 0 ↔ M i j = 0 := by
  have h₀ : (0 : ℝ) ≤ ((M i j * M j i : ℤ) : ℝ) := by exact_mod_cast hM.mul_nonneg_of_ne h
  rw [cartanGram_apply_of_ne _ h, div_eq_zero_iff, neg_eq_zero, Real.sqrt_eq_zero h₀]
  simp [hM.zero_comm i j]

/-- The normalised Gram matrix of a finite Cartan matrix is admissible. With `S = DM` the
positive definite symmetrisation and `P = diag (1 / √(2 dᵢ))`, it equals `Pᵀ S P`. -/
theorem isAdmissible_cartanGram : (cartanGram M).IsAdmissible := by
  refine ⟨?_, by simp, fun i j h ↦ ?_, fun i j h ↦ ?_⟩
  · obtain ⟨d, hd, hdM⟩ := hM.exists_posDef
    have hsym (i j : ι) : d i * M i j = d j * M j i := by simpa using hdM.isHermitian.apply j i
    have hd' (i : ι) : (0 : ℝ) < d i := by exact_mod_cast hd i
    set P : Matrix ι ι ℝ := diagonal fun i ↦ (√(2 * d i))⁻¹
    have hP : Function.Injective P.mulVec := by
      intro x y hxy
      ext i
      have := congrFun hxy i
      simp only [P, mulVec_diagonal] at this
      exact mul_left_cancel₀ (by have := hd' i; positivity) this
    convert hdM.map_intCast_real.conjTranspose_mul_mul_same hP using 1
    ext i j
    simp only [P, diagonal_conjTranspose, diagonal_mul, mul_diagonal, map_apply, star_trivial,
      Int.cast_mul]
    obtain rfl | hij := eq_or_ne i j
    · have := hd' i
      field_simp
      rw [Real.sq_sqrt (by positivity), cartanGram_apply_self, hM.diag]
      push_cast; ring
    · have hi := hd' i
      have hj := hd' j
      have hx : (d i * M i j : ℝ) ≤ 0 := by
        have := hM.offDiag_nonpos i j hij
        exact_mod_cast mul_nonpos_of_nonneg_of_nonpos (hd i).le this
      have hroot : √((M i j * M j i : ℤ) : ℝ) = -(d i * M i j) / √(d i * d j) := by
        rw [Real.sqrt_eq_iff_mul_self_eq (by exact_mod_cast hM.mul_nonneg_of_ne hij)
          (div_nonneg (by linarith) (Real.sqrt_nonneg _)), div_mul_div_comm,
          Real.mul_self_sqrt (by positivity), neg_mul_neg]
        have : (d i * M i j : ℝ) * (d i * M i j) = (d i * M i j) * (d j * M j i) := by
          rw [show (d j * M j i : ℝ) = d i * M i j by exact_mod_cast (hsym i j).symm]
        rw [this, eq_div_iff (by positivity)]
        push_cast; ring
      rw [cartanGram_apply_of_ne _ hij, hroot, Real.sqrt_mul (by positivity),
        Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
      field_simp
      rw [Real.sq_sqrt (by norm_num)]
  · rw [cartanGram_apply_of_ne _ h]
    have : 0 ≤ √((M i j * M j i : ℤ) : ℝ) := Real.sqrt_nonneg _
    linarith
  · refine ⟨(M i j * M j i).toNat, ?_, ?_⟩
    · have := hM.mul_lt_four h; lia
    · rw [hM.four_mul_cartanGram_sq h]
      exact_mod_cast (Int.toNat_of_nonneg (hM.mul_nonneg_of_ne h)).symm

end IsFiniteCartan

/-! ### The master inequality for admissible matrices -/

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma dotProduct_mulVec_self_eq_sum (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    x ⬝ᵥ (A *ᵥ x) = ∑ i, ∑ j, x i * A i j * x j := by
  simp [dotProduct, mulVec, mul_sum, mul_assoc]

namespace IsAdmissible

variable {A : Matrix ι ι ℝ} (hA : A.IsAdmissible)
include hA

omit [Fintype ι] [DecidableEq ι] in
lemma symm (i j : ι) : A i j = A j i := by
  simpa using (hA.posDef.isHermitian.apply i j).symm

omit [Fintype ι] [DecidableEq ι] in
/-- Two joined nodes meet at an angle of at least `120°`. -/
lemma le_neg_half {i j : ι} (hij : i ≠ j) (h : A i j ≠ 0) : A i j ≤ -1 / 2 := by
  obtain ⟨k, -, hk⟩ := hA.four_mul_sq i j hij
  have hk₀ : k ≠ 0 := by rintro rfl; simp_all
  have : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk₀
  nlinarith [hA.offDiag_nonpos i j hij]

omit [Fintype ι] [DecidableEq ι] in
/-- `‖∑_{s ∈ S} εₛ‖² > 0` for non-empty `S`, as the `εₛ` are linearly independent. -/
lemma sum_pos [Finite ι] {S : Finset ι} (hS : S.Nonempty) : 0 < ∑ i ∈ S, ∑ j ∈ S, A i j := by
  classical
  have := Fintype.ofFinite ι
  set u : ι → ℝ := fun k ↦ if k ∈ S then 1 else 0
  have hu : u ≠ 0 := by
    obtain ⟨s, hs⟩ := hS
    exact fun h ↦ by simpa [u, hs] using congrFun h s
  have := hA.posDef.dotProduct_mulVec_pos hu
  rw [star_trivial, dotProduct_mulVec_self_eq_sum] at this
  simpa [u, ite_mul, mul_ite, sum_ite_mem] using this

omit [Fintype ι] in
lemma sum_insert_eq {S : Finset ι} {x : ι} (hx : x ∉ S) :
    ∑ i ∈ insert x S, ∑ j ∈ insert x S, A i j =
      ∑ i ∈ S, ∑ j ∈ S, A i j + 2 * ∑ s ∈ S, A s x + 1 := by
  simp only [sum_insert hx, hA.diag_eq_one, sum_add_distrib]
  have : ∑ j ∈ S, A x j = ∑ t ∈ S, A t x := sum_congr rfl fun j _ ↦ hA.symm x j
  linarith

omit [Fintype ι] in
/-- Adding a node joined to `S` does not lengthen `∑_{s ∈ S} εₛ`: the new cross terms contribute
at most `2 · (-1/2)`, which cancels the new diagonal term `1`. -/
lemma sum_insert_le {S : Finset ι} {x s : ι} (hx : x ∉ S) (hs : s ∈ S) (h : A s x ≠ 0) :
    ∑ i ∈ insert x S, ∑ j ∈ insert x S, A i j ≤ ∑ i ∈ S, ∑ j ∈ S, A i j := by
  have hsx : s ≠ x := by rintro rfl; exact hx hs
  have hcross : ∑ t ∈ S, A t x ≤ -1 / 2 := by
    rw [← add_sum_erase _ _ hs]
    have : ∑ t ∈ S.erase s, A t x ≤ 0 :=
      sum_nonpos fun t ht ↦ hA.offDiag_nonpos t x (by rintro rfl; exact hx (mem_of_mem_erase ht))
    linarith [hA.le_neg_half hsx h]
  rw [hA.sum_insert_eq hx]
  linarith

omit [Fintype ι] [DecidableEq ι] in
/-- **Master inequality.** If `S` is non-empty with `‖∑_{s ∈ S} εₛ‖² ≤ 1` and `N` is disjoint from
`S`, put `bⱼ = (∑_{s ∈ S} εₛ, εⱼ)`. The vector `x = ∑_{s ∈ S} εₛ - ∑_{j ∈ N} bⱼ εⱼ` is non-zero, and
expanding `0 < ‖x‖²` gives `∑_{j ∈ N} bⱼ² < 1`. -/
theorem sum_sq_lt_one [Finite ι] {S N : Finset ι} (hS : S.Nonempty)
    (hq : ∑ i ∈ S, ∑ j ∈ S, A i j ≤ 1) (hSN : Disjoint S N) :
    ∑ j ∈ N, (∑ s ∈ S, A s j) ^ 2 < 1 := by
  classical
  have := Fintype.ofFinite ι
  set b : ι → ℝ := fun j ↦ ∑ s ∈ S, A s j
  have hb (j : ι) (hj : j ∈ N) : b j ≤ 0 :=
    sum_nonpos fun s hs ↦ hA.offDiag_nonpos s j fun h ↦ disjoint_left.mp hSN hs (h ▸ hj)
  set u : ι → ℝ := fun k ↦ if k ∈ S then 1 else 0
  set w : ι → ℝ := fun k ↦ if k ∈ N then b k else 0
  have hx : u - w ≠ 0 := by
    obtain ⟨s, hs⟩ := hS
    refine fun h ↦ absurd (congrFun h s) ?_
    simp [u, w, hs, disjoint_left.mp hSN hs]
  have hpos := hA.posDef.dotProduct_mulVec_pos hx
  rw [star_trivial, dotProduct_mulVec_self_eq_sum] at hpos
  have huu : ∑ i, ∑ j, u i * A i j * u j = ∑ i ∈ S, ∑ j ∈ S, A i j := by
    simp [u, ite_mul, mul_ite, sum_ite_mem]
  have huw : ∑ i, ∑ j, u i * A i j * w j = ∑ j ∈ N, b j ^ 2 := by
    simp only [u, w, ite_mul, mul_ite, one_mul, zero_mul, mul_zero, sum_ite_mem, univ_inter]
    rw [sum_comm]
    exact sum_congr rfl fun j _ ↦ by simp [b, sq, sum_mul]
  have hwu : ∑ i, ∑ j, w i * A i j * u j = ∑ j ∈ N, b j ^ 2 := by
    rw [← huw, sum_comm]
    exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by rw [hA.symm j i]; ring
  have hww : ∑ i, ∑ j, w i * A i j * w j ≤ ∑ j ∈ N, b j ^ 2 := by
    simp only [w, ite_mul, mul_ite, zero_mul, mul_zero, sum_ite_mem, univ_inter, sum_ite_irrel,
      sum_const_zero]
    refine sum_le_sum fun i hi ↦ ?_
    rw [← add_sum_erase _ _ hi, hA.diag_eq_one, mul_one, sq]
    have : ∑ j ∈ N.erase i, b i * A i j * b j ≤ 0 := by
      refine sum_nonpos fun j hj ↦ ?_
      have hij : i ≠ j := (ne_of_mem_erase hj).symm
      have := mul_nonneg_of_nonpos_of_nonpos (hb i hi) (hb j (mem_of_mem_erase hj))
      nlinarith [hA.offDiag_nonpos i j hij]
    linarith
  have : ∑ i, ∑ j, (u - w) i * A i j * (u - w) j =
      ∑ i, ∑ j, u i * A i j * u j - ∑ i, ∑ j, u i * A i j * w j -
        ∑ i, ∑ j, w i * A i j * u j + ∑ i, ∑ j, w i * A i j * w j := by
    simp only [Pi.sub_apply, sub_mul, mul_sub, sum_sub_distrib]
    ring
  linarith

end IsAdmissible

/-! ### The master inequality for finite Cartan matrices -/

namespace IsFiniteCartan

variable {M : Matrix ι ι ℤ} (hM : M.IsFiniteCartan)
include hM

lemma cartanGram_sum_insert_le {S : Finset ι} {x s : ι} (hx : x ∉ S) (hs : s ∈ S)
    (h : M s x ≠ 0) :
    ∑ i ∈ insert x S, ∑ j ∈ insert x S, cartanGram M i j ≤ ∑ i ∈ S, ∑ j ∈ S, cartanGram M i j :=
  hM.isAdmissible_cartanGram.sum_insert_le hx hs <| by
    rwa [Ne, hM.cartanGram_eq_zero_iff (by rintro rfl; exact hx hs)]

/-- **Master inequality.** If `‖∑_{s ∈ S} εₛ‖ ≤ 1` and `N` is disjoint from the non-empty set `S`,
then the bonds between `S` and `N` number fewer than four. -/
theorem sum_mul_lt_four {S N : Finset ι} (hS : S.Nonempty)
    (hq : ∑ i ∈ S, ∑ j ∈ S, cartanGram M i j ≤ 1) (hSN : Disjoint S N) :
    ∑ j ∈ N, ∑ s ∈ S, M s j * M j s < 4 := by
  have hA := hM.isAdmissible_cartanGram
  have hne {s j : ι} (hs : s ∈ S) (hj : j ∈ N) : s ≠ j :=
    fun h ↦ disjoint_left.mp hSN hs (h ▸ hj)
  have key : ∑ j ∈ N, ∑ s ∈ S, cartanGram M s j ^ 2 < 1 := by
    refine lt_of_le_of_lt (sum_le_sum fun j hj ↦ ?_) (hA.sum_sq_lt_one hS hq hSN)
    have := sum_sq_le_sq_sum_of_nonneg (s := S) (f := fun s ↦ -cartanGram M s j)
      fun s hs ↦ neg_nonneg.mpr (hA.offDiag_nonpos s j (hne hs hj))
    simpa [sum_neg_distrib] using this
  have : ((∑ j ∈ N, ∑ s ∈ S, M s j * M j s : ℤ) : ℝ) =
      4 * ∑ j ∈ N, ∑ s ∈ S, cartanGram M s j ^ 2 := by
    push_cast
    rw [mul_sum]
    refine sum_congr rfl fun j hj ↦ ?_
    rw [mul_sum]
    exact sum_congr rfl fun s hs ↦ by rw [hM.four_mul_cartanGram_sq (hne hs hj)]; push_cast; ring
  have : ((∑ j ∈ N, ∑ s ∈ S, M s j * M j s : ℤ) : ℝ) < 4 := by linarith
  exact_mod_cast this

/-- **Step (4) of Humphreys.** A node carries fewer than four bonds in total. -/
theorem sum_mul_lt_four_of_notMem {i : ι} {N : Finset ι} (hi : i ∉ N) :
    ∑ j ∈ N, M i j * M j i < 4 := by
  simpa using hM.sum_mul_lt_four (S := {i}) (by simp) (by simp) (by simpa using hi)

/-- The indices `f 0, f 1, …, f k` of a path have `‖∑ εₛ‖ ≤ 1`: add them one at a time, each
joined to the previous one. -/
lemma cartanGram_sum_path_le {k : ℕ} (f : Fin (k + 1) → ι) (hf : Function.Injective f)
    (hadj : ∀ i : Fin k, M (f i.castSucc) (f i.succ) ≠ 0) :
    ∑ i ∈ univ.image f, ∑ j ∈ univ.image f, cartanGram M i j ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have himg : univ.image f = insert (f (Fin.last (k + 1))) (univ.image (f ∘ Fin.castSucc)) := by
      ext x; simp [Fin.exists_fin_succ', or_comm, eq_comm]
    have hnot : f (Fin.last (k + 1)) ∉ univ.image (f ∘ Fin.castSucc) := by
      simp [hf.eq_iff, Fin.castSucc_ne_last]
    rw [himg]
    refine (hM.cartanGram_sum_insert_le hnot (s := f (Fin.last k).castSucc) (by simp)
      (by simpa using hadj (Fin.last k))).trans ?_
    exact ih _ (hf.comp (Fin.castSucc_injective _)) fun i ↦ by simpa using hadj i.castSucc

end IsFiniteCartan

end Matrix
