/-
Copyright (c) 2026 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Aristotle AI
-/
module

public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.SemiringInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Linear independence and nonsingularity of matrices

In this file we formalize several theorems proved by Yi-Jia Tan in his paper [Tan2016]
*Free sets and free subsemimodules in a semimodule*. As consequences, we show that
commutative semirings satisfy the strong rank condition, and that the columns of a square matrix
are linearly independent if and only if the matrix is nonsingular (over a commutative ring,
a matrix is nonsingular if and only if its determinant is not a zero divisor).

## Main definition

* `Matrix.Nonsingular`: if `R` is a commutative semiring, a matrix `A` in `Mₙ(R)` is called
  nonsingular if `a|A|⁺ + b|A|⁻ = b|A|⁻ + a|A|⁺` implies `a = b` for `a, b : R`.
  `|A|⁺` and `|A|⁻` are `A.detp 1` and `A.detp (-1)` respectively in mathlib (`Matrix.detp`).

## Main theorems

* `Matrix.nonsingular_of_linearIndependent`: if `A = (aᵢⱼ)` is a `m × m` matrix with entries
  in `R` and `(bᵢ)` for `i : m` are elements in an `R`-module such that `∑ᵢ aᵢⱼ bᵢ` for `j : m`
  are linearly independent, then `A` is nonsingular. Theorem 3.1(1) of [Tan2016].

* `Matrix.nonsingular_of_linearIndependent_col`: if the columns of a square matrix are linearly
  independent, then the matrix is nonsingular. Corollary 3.2(1) of [Tan2016].

* `Matrix.linearIndependent_col_of_nonsingular`: if a matrix over a commutative semiring with
  cancellative addition is nonsingular, then its columns are linearly independent.
  Corollary 3.2(2) of [Tan2016].

* `Matrix.instStrongRankConditionOfNontrivial`: a commutative semiring satisfies the strong rank
  condition.
-/

namespace Matrix

variable {R m : Type*} [CommSemiring R] [Fintype m] [DecidableEq m] (A : Matrix m m R)

/-- A matrix `A` in `Mₙ(R)` is called nonsingular if `a|A|⁺ + b|A|⁻ = b|A|⁻ + a|A|⁺`
implies `a = b` for `a, b : R`. -/
@[expose] public def Nonsingular : Prop :=
  ∀ a b : R, a * A.detp 1 + b * A.detp (-1) = b * A.detp 1 + a * A.detp (-1) → a = b

public lemma nonsingular_iff_det_mem_nonZeroDivisors {R : Type*} [CommRing R]
    {A : Matrix m m R} : A.Nonsingular ↔ A.det ∈ nonZeroDivisors R := by
  rw [Nonsingular, det_eq_detp_sub_detp, ← nonZeroDivisorsRight_eq_nonZeroDivisors,
    mem_nonZeroDivisorsRight_iff]
  refine ⟨fun h x eq ↦ h x 0 (by simpa [mul_sub, sub_eq_zero] using eq),
    fun h a b eq ↦ sub_eq_zero.mp <| h _ ?_⟩
  convert sub_eq_zero.mpr eq using 1
  ring

/-- If all entries in some row of a square matrix are zero, then `detp s A = 0`. -/
public lemma detp_eq_zero_of_exists_row_eq_zero (s : ℤˣ) (i : m) (hi : ∀ j, A i j = 0) :
    A.detp s = 0 :=
  Finset.sum_eq_zero fun _ _ ↦ Finset.prod_eq_zero (Finset.mem_univ i) (hi _)

-- use transpose?
public lemma adjp_mul_apply_eq (s : ℤˣ) (k : m) : (adjp s A * A) k k = detp s A := by
  simp only [adjp, mul_apply, of_apply]
  simp only [Finset.sum_mul, detp]
  rw [Finset.sum_sigma']
  apply Finset.sum_bij (fun x _ ↦ x.2) <;> simp only [Equiv.Perm.mem_ofSign, Finset.mem_sigma,
    Finset.mem_univ, Finset.mem_filter, true_and, exists_prop, Sigma.exists, exists_eq_right,
    exists_and_left, and_imp]
  · aesop
  · aesop
  · exact fun b hb => ⟨hb, b.symm k, by simp⟩
  · intro a ha hk
    rw [← Finset.prod_sdiff (Finset.subset_univ {a.fst})]
    simp only [Finset.prod_singleton, hk]
    rw [Finset.compl_eq_univ_sdiff]

theorem adjp_mul_apply_ne (k j : m) (h : k ≠ j) :
    (adjp 1 A * A) k j = (adjp (-1) A * A) k j := by
  have := mul_adjp_apply_ne A.transpose j k h.symm
  contrapose! this
  convert this using 1
  · unfold adjp
    simp only [transpose_apply, mul_apply, of_apply, mul_comm]
    refine Finset.sum_congr rfl fun x hx =>
      congr_arg _ (Finset.sum_bij (fun σ hσ => σ⁻¹) ?_ ?_ ?_ ?_) <;>
        simp only [Finset.mem_filter, Equiv.Perm.mem_ofSign, Equiv.Perm.sign_inv,
          Equiv.Perm.coe_inv, and_imp, inv_inj, imp_self, implies_true]
    · exact fun a ha hk => ⟨ha, by rw [← hk, Equiv.symm_apply_apply]⟩
    · intro b hb hx; use b⁻¹; aesop
    · intro a ha hk; rw [← hk]
      refine Finset.prod_bij (fun x hx => a x) ?_ ?_ ?_ ?_ <;>
        simp only [Finset.mem_compl, Finset.mem_singleton, EmbeddingLike.apply_eq_iff_eq, imp_self,
          Equiv.symm_apply_apply, implies_true, exists_prop]
      exact fun b hb => ⟨a.symm b, by aesop⟩
  · unfold adjp
    simp only [transpose_apply, mul_apply, of_apply, mul_comm]
    refine Finset.sum_bij (fun x _ => x) ?_ ?_ ?_ ?_ <;>
      simp only [Finset.mem_univ, exists_const, exists_eq, imp_self, implies_true, forall_const]
    intro a
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_bij (fun x _ => x⁻¹) ?_ ?_ ?_ ?_ <;>
      simp only [Finset.mem_filter, Equiv.Perm.mem_ofSign, Equiv.Perm.sign_inv, Equiv.Perm.coe_inv,
        and_imp, inv_inj, imp_self, implies_true]
    · exact fun σ hσ hk => ⟨hσ, by rw [← hk, Equiv.symm_apply_apply]⟩
    · intro b hb hk; use b⁻¹; aesop
    · intro σ hσ hk; rw [← hk]
      refine congr_arg _ (Finset.prod_bij (fun x _ => σ x) ?_ ?_ ?_ ?_) <;>
        simp only [Finset.mem_compl, Finset.mem_singleton, EmbeddingLike.apply_eq_iff_eq, imp_self,
          Equiv.symm_apply_apply, implies_true, exists_prop]
      exact fun b hb => ⟨σ.symm b, by aesop⟩

/-! ### Key lemma: repeated row implies detp 1 = detp (-1) -/

public lemma detp_eq_of_eq_row {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n R) (p q : n) (hpq : p ≠ q) (hrow : B p = B q) :
    B.detp 1 = B.detp (-1) := by
  apply Finset.sum_bij (fun σ _ ↦ σ * Equiv.swap p q) <;>
    simp only [Equiv.Perm.mem_ofSign, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap', mul_ite, mul_one,
    mul_neg, mul_left_inj, Equiv.Perm.ext_iff, imp_self, implies_true,
  Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_def, exists_prop]
  · lia
  · intro b hb; use b * Equiv.swap p q; aesop
  · intro a ha; rw [← Equiv.prod_comp (Equiv.swap p q)]
    simp [Equiv.swap_apply_def]; grind

/-! ### Adjoint lemmas -/

open Matrix Finset in
lemma adjp_last_col_eq
    {r : ℕ} (s : ℤˣ) (B B' : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
    (h : ∀ k : Fin r, B (Fin.castSucc k) = B' (Fin.castSucc k))
    (l : Fin (r + 1)) :
    adjp s B l (Fin.last r) = adjp s B' l (Fin.last r) := by
  refine Finset.sum_congr rfl fun σ _ => Finset.prod_congr rfl fun k hk ↦ ?_
  cases k using Fin.lastCases <;> aesop

noncomputable def finNeLastEquiv (r : ℕ) :
    Fin r ≃ {x : Fin (r + 1) // x ≠ Fin.last r} where
  toFun i := ⟨Fin.castSucc i, (Fin.castSucc_lt_last i).ne⟩
  invFun x := ⟨x.1.val, by
    have := x.1.isLt; have := x.2; simp [Fin.ext_iff, Fin.last] at this; omega⟩
  left_inv i := by ext; simp
  right_inv x := by ext; simp

open Matrix Finset in
lemma adjp_diag_last_eq_detp_sub
    {r : ℕ} (s : ℤˣ) (B : Matrix (Fin (r + 1)) (Fin (r + 1)) R) :
    adjp s B (Fin.last r) (Fin.last r) = detp s (B.submatrix Fin.castSucc Fin.castSucc) := by
  unfold adjp; simp only [of_apply]
  have h_bij : Finset.filter (fun σ : Equiv.Perm (Fin (r + 1)) => σ (Fin.last r) = Fin.last r)
      (Equiv.Perm.ofSign s) = Finset.image
      (fun σ : Equiv.Perm (Fin r) => Equiv.Perm.extendDomain σ (finNeLastEquiv r))
      (Equiv.Perm.ofSign s) := by
    ext σ; constructor
    · intro hσ
      obtain ⟨σ', hσ'⟩ : ∃ σ' : Equiv.Perm (Fin r),
          σ = Equiv.Perm.extendDomain σ' (finNeLastEquiv r) := by
        use Equiv.permCongr (finNeLastEquiv r).symm (σ.subtypePerm (by
          intro x; by_cases hx : x = Fin.last r <;>
            simp_all only [mem_filter, Equiv.Perm.mem_ofSign, ne_eq, not_false_eq_true, iff_true]
          exact fun h ↦ hx (σ.injective (h.trans hσ.2.symm))))
        generalize_proofs at *
        ext x; by_cases hx : x = Fin.last r <;> simp_all [Equiv.Perm.extendDomain]
      aesop
    · simp only [Equiv.Perm.extendDomain, ne_eq, mem_image, Equiv.Perm.mem_ofSign,
        mem_filter, forall_exists_index, and_imp]
      rintro x hx rfl; simp [hx, Equiv.Perm.subtypeCongr]
  rw [h_bij, Finset.sum_image]
  · refine Finset.sum_congr rfl fun σ _ ↦ ?_
    refine Finset.prod_bij (fun x hx ↦ ⟨x.val, ?_⟩) ?_ ?_ ?_ ?_ <;>
      simp_all only [Fin.ext_iff, Fin.val_last, Equiv.Perm.extendDomain, ne_eq,
        Equiv.Perm.mem_ofSign, mem_compl, mem_singleton, mem_univ, implies_true, exists_prop,
        forall_const, not_false_eq_true, Equiv.Perm.subtypeCongr.left_apply, Equiv.permCongr_apply,
        submatrix_apply, Fin.castSucc_mk, Fin.eta]
    · exact lt_of_le_of_ne (Nat.le_of_lt_succ x.2) hx
    · exact fun b ↦ ⟨Fin.castSucc b, ne_of_lt (Fin.castSucc_lt_last b), rfl⟩
    · intro a ha; congr
  · intro σ _ τ _ h_eq; simp_all only [Equiv.Perm.extendDomain, ne_eq, SetLike.mem_coe,
      Equiv.Perm.mem_ofSign, Equiv.Perm.ext_iff]
    intro x; specialize h_eq (Fin.castSucc x)
    simp_all [Equiv.Perm.subtypeCongr, finNeLastEquiv]

/-! ### Case 1: all entries satisfy a * A i j = b * A i j -/

omit [DecidableEq m] in
lemma not_linearIndependent_of_smul_eq
    (M : Type*) [AddCommMonoid M] [Module R M]
    (B : m → M) {a b : R} (hab : a ≠ b) [Nonempty m]
    (hall : ∀ i j, a * A i j = b * A i j) :
    ¬ LinearIndependent R (fun j ↦ ∑ i : m, A i j • B i) := by
  intro h_ind
  obtain ⟨j₀, _⟩ : ∃ j₀ : m, True := ⟨Classical.arbitrary m, trivial⟩
  set f : m →₀ R := Finsupp.single j₀ a
  set g : m →₀ R := Finsupp.single j₀ b
  have h_fg : ∑ j, f j • (∑ i, A i j • B i) = ∑ j, g j • (∑ i, A i j • B i) := by
    simp +zetaDelta only [ne_eq] at *
    classical simp [Finsupp.single_apply, Finset.smul_sum, smul_smul, hall]
  have h_fg' : Finsupp.linearCombination R (fun j => ∑ i, A i j • B i) f =
      Finsupp.linearCombination R (fun j => ∑ i, A i j • B i) g := by
    convert h_fg using 1 <;> simp [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
  exact hab (by simpa [f, g] using Finsupp.ext_iff.mp (h_ind h_fg') j₀)

/-! ### Case 2: the main construction via maximal bad submatrix

The proof constructs `f ≠ g` with `A.mulVec f = A.mulVec g` using:
1. A maximal bad submatrix of size `r` (1 ≤ r < Fintype.card m).
2. Cofactor expansion via `mul_adjp_apply_eq` along the last row of
   augmented `(r+1)×(r+1)` submatrices.
-/

/-
Given `r`, `S : Fin r → m`, `T : Fin r → m` (injective), `t₀ ∉ range T`:
for each `i`, the augmented matrix `A.submatrix (Fin.snoc S i) (Fin.snoc T t₀)` satisfies
the detp equation, provided the bad (S, T) of size `r` exists and all `(r+1)`-sized
submatrices are good.
-/
omit [DecidableEq m] [Fintype m] in
lemma augmented_good {a b : R} {r : ℕ}
    (S : Fin r → m) (hS : Function.Injective S)
    (T : Fin r → m) (hT : Function.Injective T)
    (t₀ : m) (ht₀ : t₀ ∉ Set.range T)
    (hmax : ∀ (S' : Fin (r + 1) → m) (T' : Fin (r + 1) → m),
      Function.Injective S' → Function.Injective T' →
      a * (A.submatrix S' T').detp 1 + b * (A.submatrix S' T').detp (-1) =
      b * (A.submatrix S' T').detp 1 + a * (A.submatrix S' T').detp (-1))
    (i : m) :
    let B := A.submatrix (Fin.snoc S i) (Fin.snoc T t₀)
    a * B.detp 1 + b * B.detp (-1) = b * B.detp 1 + a * B.detp (-1) := by
  by_cases hi : i ∈ Set.range S <;> simp_all only [Set.mem_range, not_exists,
    Fin.snoc_injective_iff, exists_false, not_false_eq_true, and_self]
  obtain ⟨k, rfl⟩ := hi
  have h_detp_eq : detp 1 (A.submatrix (Fin.snoc S (S k)) (Fin.snoc T t₀)) =
      detp (-1) (A.submatrix (Fin.snoc S (S k)) (Fin.snoc T t₀)) := by
    apply detp_eq_of_eq_row
    · exact ne_of_lt (Fin.castSucc_lt_last k)
    · ext j; simp [Fin.snoc]
  rw [h_detp_eq, add_comm]

/-
The Laplace expansion identity: `detp s B = ∑ l, B (last r) l * adjp s B l (last r)`.
-/
lemma detp_laplace_last_row
    {r : ℕ} (s : ℤˣ) (B : Matrix (Fin (r + 1)) (Fin (r + 1)) R) :
    B.detp s = ∑ l, B (Fin.last r) l * adjp s B l (Fin.last r) := by
  -- By definition of matrix multiplication, the element at position (i, j) in the product of B and
  -- adjp s B is the sum of the products of elements from row i of B and column j of adjp s B.
  rw [← mul_apply, mul_adjp_apply_eq]

/-
Main construction: from a bad submatrix and the augmented good condition,
build `f ≠ g` with `A.mulVec f = A.mulVec g`.
-/
omit [DecidableEq m] in
lemma witness_from_bad_submatrix {a b : R} {r : ℕ}
    (S T : Fin r → m) (hT : Function.Injective T)
    (t₀ : m) (ht₀ : t₀ ∉ Set.range T)
    (hbad_ST : a * (A.submatrix S T).detp 1 + b * (A.submatrix S T).detp (-1) ≠
               b * (A.submatrix S T).detp 1 + a * (A.submatrix S T).detp (-1))
    (hgood : ∀ i : m,
      let B := A.submatrix (Fin.snoc S i) (Fin.snoc T t₀)
      a * B.detp 1 + b * B.detp (-1) = b * B.detp 1 + a * B.detp (-1)) :
    ∃ f g : m → R, f ≠ g ∧ A.mulVec f = A.mulVec g := by
  classical
  -- Define p l = a * C 1 l + b * C (-1) l and q l = b * C 1 l + a * C (-1) l.
  set C : ℤˣ → Fin (r + 1) → R := fun s l => adjp s (A.submatrix (Fin.snoc S (Classical.choose
      (show ∃ i₀ : m, True from ⟨t₀, trivial⟩))) (Fin.snoc T t₀)) l (Fin.last r)
  -- By adjp_last_col_eq, C s l doesn't depend on the choice of i₀
  -- (all augmented matrices agree on the first r rows).
  have hC_indep : ∀ (i : m), C = fun s l =>
      adjp s (A.submatrix (Fin.snoc S i) (Fin.snoc T t₀)) l (Fin.last r) := by
    intro i
    funext s l
    apply adjp_last_col_eq
    aesop
  -- Define f and g as the extensions of p and q respectively.
  use Function.extend (Fin.snoc T t₀) (fun l => a * C 1 l + b * C (-1) l) 0,
    Function.extend (Fin.snoc T t₀) (fun l => b * C 1 l + a * C (-1) l) 0
  refine ⟨?_, ?_⟩
  · intro h_eq
    replace h_eq := congr_fun h_eq t₀
    simp only [Function.extend, Fin.snoc, Fin.castSucc_castLT, cast_eq, dite_eq_right_iff,
      Pi.zero_apply] at h_eq
    split_ifs at h_eq <;>
      simp_all only [Set.mem_range, not_exists, ne_eq, imp_false, not_lt, not_le]
    · have h_detp_eq : C 1 (Fin.last r) = detp 1 (A.submatrix S T) ∧ C (-1) (Fin.last r) =
          detp (-1) (A.submatrix S T) := by
        have h_detp_eq : ∀ s : ℤˣ, C s (Fin.last r) = detp s (A.submatrix S T) := by
          intro s
          have h_detp_eq : adjp s (A.submatrix (Fin.snoc S (Classical.choose
            (show ∃ i₀ : m, True from ⟨t₀, trivial⟩))) (Fin.snoc T t₀)) (Fin.last r) (Fin.last r) =
              detp s (A.submatrix S T) := by
            convert adjp_diag_last_eq_detp_sub s _
            ext i j; simp [Fin.snoc]
          exact h_detp_eq
        exact ⟨h_detp_eq 1, h_detp_eq (-1)⟩
      grind
    · exact absurd (‹∀ x : Fin (r + 1), (x : ℕ) < r› (Fin.last r)) (by simp)
  · ext i
    convert hgood i using 1
    · rw [detp_laplace_last_row, detp_laplace_last_row]
      simp only [mulVec, dotProduct, hC_indep i, submatrix_apply, Fin.snoc_last,
        Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.image (Fin.snoc T t₀) Finset.univ))]
      · rw [Finset.sum_image] <;> simp only [hT, ht₀, not_false_eq_true, Finset.coe_univ,
          Fin.snoc_injective_of_injective, Function.Injective.extend_apply, Set.injOn_univ]
        exact Finset.sum_congr rfl fun _ _ => by ring
      · simp +contextual [Function.extend_apply']
    · rw [mulVec, dotProduct]
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.image (Fin.snoc T t₀) Finset.univ))]
      · rw [Finset.sum_image] <;> simp only [hT, ht₀, not_false_eq_true, Finset.coe_univ,
          Fin.snoc_injective_of_injective, Function.Injective.extend_apply, Set.injOn_univ]
        rw [detp_laplace_last_row, detp_laplace_last_row]
        simp [Fin.snoc, mul_add, mul_left_comm, Finset.mul_sum, Finset.sum_add_distrib, hC_indep i]
      · simp +contextual [Function.extend_apply']

/-
The detp equation is preserved when reindexing by equivalences.
-/
lemma detp_eq_submatrix_equiv {a b : R}
    (hdetp : a * A.detp 1 + b * A.detp (-1) = b * A.detp 1 + a * A.detp (-1))
    (e₁ e₂ : m ≃ m) :
    a * (A.submatrix e₁ e₂).detp 1 + b * (A.submatrix e₁ e₂).detp (-1) =
    b * (A.submatrix e₁ e₂).detp 1 + a * (A.submatrix e₁ e₂).detp (-1) := by
  simp only [detp] at hdetp ⊢
  have h_reindex (σ : Equiv.Perm m) : ∏ k, A (e₁ k) (e₂ (σ k)) = ∏ k, A k (e₂ (σ (e₁.symm k))) := by
    rw [← e₁.symm.prod_comp]; simp
  -- Apply the reindexing result to rewrite the sums.
  have h_sum_reindex : ∀ s : ℤˣ, ∑ σ ∈ Equiv.Perm.ofSign s, ∏ k, A (e₁ k) (e₂ (σ k)) =
      ∑ σ ∈ Equiv.Perm.ofSign (Equiv.Perm.sign e₁ * Equiv.Perm.sign e₂ * s), ∏ k, A k (σ k) := by
    intro s
    apply Finset.sum_bij (fun σ _ => e₂ * σ * e₁.symm)
    · simp [Equiv.Perm.ofSign, mul_assoc]
      grind
    · simp [mul_assoc]
    · intro σ hσ
      use e₂.symm * σ * e₁
      simp_all only [Equiv.Perm.mem_ofSign, Equiv.Perm.sign_mul, Equiv.Perm.sign_symm, exists_prop]
      simp only [mul_comm, mul_left_comm, Int.units_mul_self, one_mul, mul_one, mul_assoc,
        Equiv.Perm.mul_symm, true_and]
      exact (eq_mul_of_inv_mul_eq rfl).symm
    · aesop
  rcases Int.units_eq_one_or (Equiv.Perm.sign e₁) with h₁ | h₁ <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign e₂) with h₂ | h₂ <;> simp only [h₁, h₂] at *
  · convert hdetp using 1
    iterate 2
      exact congr_arg₂ (· + ·) (congr_arg _ (h_sum_reindex 1)) (congr_arg _ (h_sum_reindex (-1)))
  · convert hdetp using 1 <;>
      simp only [submatrix_apply, h_sum_reindex, mul_neg, mul_one, neg_neg]
    · grind
    · convert hdetp using 1; ring
  · convert hdetp using 1 <;>
      simp only [submatrix_apply, h_sum_reindex, mul_one, mul_neg, neg_neg]
    · grind
    · convert hdetp using 1; ring
  · simp_all [submatrix]

lemma exists_mulVec_eq_of_bad_entry' {a b : R}
    (hdetp : a * A.detp 1 + b * A.detp (-1) = b * A.detp 1 + a * A.detp (-1))
    {i₀ j₀ : m} (hbad : a * A i₀ j₀ ≠ b * A i₀ j₀) :
    ∃ f g : m → R, f ≠ g ∧ A.mulVec f = A.mulVec g := by
  -- Step 1: The set of "bad sizes" is nonempty and bounded
  set badP : ℕ → Prop := fun r => ∃ (S : Fin r → m) (T : Fin r → m),
    Function.Injective S ∧ Function.Injective T ∧
    a * (A.submatrix S T).detp 1 + b * (A.submatrix S T).detp (-1) ≠
    b * (A.submatrix S T).detp 1 + a * (A.submatrix S T).detp (-1)
  have h1 : badP 1 := ⟨![i₀], ![j₀],
    Function.injective_of_subsingleton _,
    Function.injective_of_subsingleton _,
    by simp [detp, Equiv.Perm.ofSign, Finset.filter_singleton, hbad]⟩
  obtain ⟨r, hr⟩ : ∃ r : ℕ, badP r ∧ ∀ s : ℕ, badP s → s ≤ r := by
    have h_finite : Set.Finite {r | badP r} := by
      exact Set.finite_iff_bddAbove.mpr ⟨Fintype.card m, fun r hr => by
        rcases hr with ⟨S, T, hS, hT, h⟩
        exact Fintype.card_le_of_injective S hS |> le_trans (by simp)⟩
    exact ⟨Finset.max' (h_finite.toFinset) ⟨1, h_finite.mem_toFinset.mpr h1⟩,
      h_finite.mem_toFinset.mp (Finset.max'_mem _ _),
      fun s hs => Finset.le_max' _ _ (h_finite.mem_toFinset.mpr hs)⟩;
  -- Since $r < \text{Fintype.card } m$, there exists $t₀ \notin \text{range } T$.
  obtain ⟨S, T, hS, hT, hbad_ST⟩ := hr.left
  have ht₀ : ∃ t₀ : m, t₀ ∉ Set.range T := by
    by_contra! ht₀_contra
    have hr_eq_card : r = Fintype.card m := by
      have := Fintype.card_le_of_surjective T (by tauto)
      simp_all only [ne_eq, Set.mem_range, Fintype.card_fin]
      exact le_antisymm (by simpa using Fintype.card_le_of_injective S hS) this
    generalize_proofs at *
    -- Since $S$ and $T$ are bijective, we can construct an equivalence between $Fin r$ and $m$.
    obtain ⟨e₁, he₁⟩ : ∃ e₁ : Fin r ≃ m, ∀ i, e₁ i = S i := by
      have hS_bijective : Function.Bijective S := by
        have := Fintype.bijective_iff_injective_and_card S; aesop
      generalize_proofs at *
      exact ⟨Equiv.ofBijective S hS_bijective, fun i => rfl⟩
    obtain ⟨e₂, he₂⟩ : ∃ e₂ : Fin r ≃ m, ∀ i, e₂ i = T i := by
      exact ⟨Equiv.ofBijective T ⟨hT, fun x => by simpa using ht₀_contra x⟩, fun i => rfl⟩
    generalize_proofs at *
    have h_detp_eq_submatrix_equiv :
        a * (A.submatrix e₁ e₂).detp 1 + b * (A.submatrix e₁ e₂).detp (-1) =
        b * (A.submatrix e₁ e₂).detp 1 + a * (A.submatrix e₁ e₂).detp (-1) := by
      convert detp_eq_submatrix_equiv A hdetp (Equiv.refl m) (e₁.symm.trans e₂) using 1
      · congr! 2
        · -- same proof repeated four times verbatim
          refine Finset.sum_bij (fun σ _ => e₁.symm.trans σ |> Equiv.trans <| e₁) ?_ ?_ ?_ ?_ <;>
            simp only [Equiv.Perm.ofSign, Finset.mem_filter, Finset.mem_univ, true_and,
              Equiv.Perm.sign_symm_trans_trans, imp_self, implies_true, exists_prop,
              submatrix_apply, Equiv.coe_refl, Equiv.coe_trans, Equiv.trans_apply,
              id_eq, Function.comp_apply, Equiv.symm_apply_apply]
          · simp only [Equiv.Perm.ext_iff, Equiv.trans_apply, EmbeddingLike.apply_eq_iff_eq]
            exact fun a₁ ha₁ a₂ ha₂ h x => by simpa using h (e₁ x)
          · intro b hb; use e₁.trans b |> Equiv.trans <| e₁.symm
            simp only [Equiv.Perm.sign_trans_trans_symm, hb, true_and]
            ext; simp
          · intro σ hσ; simp [← Equiv.prod_comp e₁]
        · refine Finset.sum_bij (fun σ _ => e₁.symm.trans σ |> Equiv.trans <| e₁) ?_ ?_ ?_ ?_ <;>
            simp only [Equiv.Perm.ofSign, Finset.mem_filter, Finset.mem_univ, true_and,
              Equiv.Perm.sign_symm_trans_trans, imp_self, implies_true, exists_prop,
              submatrix_apply, Equiv.coe_refl, Equiv.coe_trans, Equiv.trans_apply,
              id_eq, Function.comp_apply, Equiv.symm_apply_apply]
          · simp only [Equiv.Perm.ext_iff, Equiv.trans_apply, EmbeddingLike.apply_eq_iff_eq]
            exact fun a₁ ha₁ a₂ ha₂ h x => by simpa using h (e₁ x)
          · intro b hb; use e₁.trans b |> Equiv.trans <| e₁.symm
            simp only [Equiv.Perm.sign_trans_trans_symm, hb, true_and]
            ext; simp
          · intro σ hσ; simp [← Equiv.prod_comp e₁]
      · congr! 2
        · refine Finset.sum_bij (fun σ _ => e₁.symm.trans σ |> Equiv.trans <| e₁) ?_ ?_ ?_ ?_ <;>
            simp only [Equiv.Perm.ofSign, Finset.mem_filter, Finset.mem_univ, true_and,
              Equiv.Perm.sign_symm_trans_trans, imp_self, implies_true, exists_prop,
              submatrix_apply, Equiv.coe_refl, Equiv.coe_trans, Equiv.trans_apply,
              id_eq, Function.comp_apply, Equiv.symm_apply_apply]
          · simp only [Equiv.Perm.ext_iff, Equiv.trans_apply, EmbeddingLike.apply_eq_iff_eq]
            exact fun a₁ ha₁ a₂ ha₂ h x => by simpa using h (e₁ x)
          · intro b hb; use e₁.trans b |> Equiv.trans <| e₁.symm
            simp only [Equiv.Perm.sign_trans_trans_symm, hb, true_and]
            ext; simp
          · intro σ hσ; simp [← Equiv.prod_comp e₁]
        · refine Finset.sum_bij (fun σ _ => e₁.symm.trans σ |> Equiv.trans <| e₁) ?_ ?_ ?_ ?_ <;>
            simp only [Equiv.Perm.ofSign, Finset.mem_filter, Finset.mem_univ, true_and,
              Equiv.Perm.sign_symm_trans_trans, imp_self, implies_true, exists_prop,
              submatrix_apply, Equiv.coe_refl, Equiv.coe_trans, Equiv.trans_apply,
              id_eq, Function.comp_apply, Equiv.symm_apply_apply]
          · simp only [Equiv.Perm.ext_iff, Equiv.trans_apply, EmbeddingLike.apply_eq_iff_eq]
            exact fun a₁ ha₁ a₂ ha₂ h x => by simpa using h (e₁ x)
          · intro b hb; use e₁.trans b |> Equiv.trans <| e₁.symm
            simp only [Equiv.Perm.sign_trans_trans_symm, hb, true_and]
            ext; simp
          · intro σ hσ; simp [← Equiv.prod_comp e₁]
    generalize_proofs at *
    exact hbad_ST (by simpa only
      [show A.submatrix S T = A.submatrix e₁ e₂ from by ext i j; simp [he₁, he₂]]
        using h_detp_eq_submatrix_equiv)
  obtain ⟨t₀, ht₀⟩ := ht₀
  have hmax : ∀ (S' : Fin (r + 1) → m) (T' : Fin (r + 1) → m),
    Function.Injective S' → Function.Injective T' →
    a * (A.submatrix S' T').detp 1 + b * (A.submatrix S' T').detp (-1) =
    b * (A.submatrix S' T').detp 1 + a * (A.submatrix S' T').detp (-1) := by
      exact fun S' T' hS' hT' => Classical.not_not.1 fun h => not_lt_of_ge
        (hr.2 _ ⟨S', T', hS', hT', h⟩) (Nat.lt_succ_self _)
  exact witness_from_bad_submatrix A S T hT t₀ ht₀ hbad_ST (augmented_good A S hS T hT t₀ ht₀ hmax)

lemma not_linearIndependent_of_bad_entry
    (M : Type*) [AddCommMonoid M] [Module R M]
    (B : m → M) {a b : R}
    (hdetp : a * A.detp 1 + b * A.detp (-1) = b * A.detp 1 + a * A.detp (-1))
    {i₀ j₀ : m} (hbad : a * A i₀ j₀ ≠ b * A i₀ j₀) :
    ¬ LinearIndependent R (fun j ↦ ∑ i : m, A i j • B i) := by
  obtain ⟨f, g, hfg, hmv⟩ := exists_mulVec_eq_of_bad_entry' A hdetp hbad
  intro ind_BA
  apply hfg
  -- From both LI assumptions, mulVec A is injective, so f = g
  convert ind_BA
  constructor <;> intro h <;> simp_all only [ne_eq, funext_iff, not_forall, LinearIndependent]
  contrapose! ind_BA
  simp only [Function.Injective, Finsupp.linearCombination_apply, not_forall, ne_eq]
  refine ⟨Finsupp.equivFunOnFinite.symm f, Finsupp.equivFunOnFinite.symm g, ?_, ?_⟩ <;>
    simp_all only [mulVec, dotProduct, ne_eq, zero_smul, implies_true, Finsupp.sum_fintype,
      Finsupp.equivFunOnFinite_symm_apply_apply, EmbeddingLike.apply_eq_iff_eq]
  · simp only [Finset.smul_sum, smul_smul, mul_comm]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, hmv]
    rw [Finset.sum_comm]
    simp only [Finset.sum_smul]
  · exact fun h => ind_BA.elim fun x hx => hx (congr_fun h x)

/-! ### Main theorems -/

/-- If `A = (aᵢⱼ)` is a `m × m` matrix with entries in `R` and `(bᵢ)` for `i : m` are elements
in an `R`-module such that `∑ᵢ aᵢⱼ bᵢ` for `j : m` are linearly independent,
then `A` is nonsingular. -/
public theorem nonsingular_of_linearIndependent (M : Type*) [AddCommMonoid M] [Module R M]
    (B : m → M) (ind_BA : LinearIndependent R fun j ↦ ∑ i : m, A i j • B i) :
    A.Nonsingular := by
  intro a b h
  by_contra hab
  cases isEmpty_or_nonempty m with
  | inl hempty =>
    apply hab; simp only [detp] at h
    have huniv : (Finset.univ : Finset (Equiv.Perm m)) = {1} := by
      ext σ; simp [Equiv.Perm.ext_iff]
    -- Since $m$ is empty, the only permutation is the identity permutation, so the sums over
    -- the permutations are just the products of the entries of $A$.
    simp [Equiv.Perm.ofSign] at h
    simp [Finset.filter_singleton] at h; aesop
  | inr hne =>
    by_cases hall : ∀ i j, a * A i j = b * A i j
    · exact absurd ind_BA (not_linearIndependent_of_smul_eq A M B hab hall)
    · push Not at hall
      obtain ⟨i₀, j₀, hbad⟩ := hall
      exact absurd ind_BA (not_linearIndependent_of_bad_entry A M B h hbad)

variable {A}

/-- If the columns of a square matrix are linearly independent, then the matrix is nonsingular. -/
public theorem nonsingular_of_linearIndependent_col
    (ind : LinearIndependent R A.col) : A.Nonsingular :=
  nonsingular_of_linearIndependent A (m → R) (fun i ↦ Pi.single i 1)
    (by convert ind using 1; ext j i; simp [col_apply, Pi.single_apply, mul_one, mul_zero])

/-- If a matrix over a commutative semiring with cancellative addition is nonsingular, then its
columns are linearly independent. Generalizes `Matrix.linearIndependent_cols_of_det_ne_zero`. -/
public theorem linearIndependent_col_of_nonsingular [IsCancelAdd R]
    (hA : A.Nonsingular) : LinearIndependent R A.col := by
  have h_mulVec_inj : Function.Injective A.mulVec := by
    intro x y hxy
    have h_det : ∀ k : m,
        A.detp 1 * x k + A.detp (-1) * y k =
        A.detp 1 * y k + A.detp (-1) * x k := by
      intro k
      have h_eq : ∑ j, (adjp 1 A * A) k j * x j =
          ∑ j, (adjp 1 A * A) k j * y j := by
        have h_detp_eq : (A.adjp 1 * A).mulVec x = (A.adjp 1 * A).mulVec y := by
          simp [← mulVec_mulVec, hxy]
        exact congr_fun h_detp_eq k
      have h_eq' : ∑ j, (adjp (-1) A * A) k j * x j =
          ∑ j, (adjp (-1) A * A) k j * y j := by
        have h_eq' : mulVec (adjp (-1) A * A) x = mulVec (adjp (-1) A * A) y := by
          simp_all [← mulVec_mulVec]
        exact congr_fun h_eq' k
      have h_adjp : ∀ j, (adjp 1 A * A) k j =
          if k = j then detp 1 A else (adjp (-1) A * A) k j := by
        intro j
        split_ifs with h <;>
          simp_all [adjp_mul_apply_eq, adjp_mul_apply_ne]
      simp_all [Finset.sum_ite, Finset.filter_eq, Finset.filter_ne,
        ← Finset.sum_erase_add _ _ (Finset.mem_univ k), adjp_mul_apply_eq]
      grind
    ext k
    exact hA _ _ (by simpa [mul_comm] using h_det k)
  exact mulVec_injective_iff.mp h_mulVec_inj

public theorem linearIndependent_col_iff [IsCancelAdd R] :
    LinearIndependent R A.col ↔ A.Nonsingular :=
  ⟨nonsingular_of_linearIndependent_col, linearIndependent_col_of_nonsingular⟩

/-
A nontrivial commutative semiring has the strong rank condition.
-/
instance [Nontrivial R] : StrongRankCondition R where
  le_of_fin_injective {n m} f hf_inj := by
    set A : Matrix (Fin m) (Fin n) R := of (fun i j => f (Pi.single j 1) i)
    by_contra! hnm
    /- By adding $n - m$ zero rows to $A$, we obtain an $n \times n$ matrix $B$ with
      linearly independent columns. -/
    set B : Matrix (Fin n) (Fin n) R := of (fun i j => if h : i.val < m then A ⟨i.val, h⟩ j else 0)
    -- Since $B$ has linearly independent columns, $B$ is nonsingular.
    have hB_nonsingular : B.Nonsingular := by
      have hB_inj : (mulVec B).Injective := by
        intro x y hxy
        have hB_inj : f x = f y := by
          ext i
          convert congr_fun hxy ⟨i, by linarith [Fin.is_lt i]⟩ using 1 <;>
            simp only [mulVec, dotProduct]
          · have hB_inj : f x = ∑ j, x j • f (Pi.single j 1) := by
              convert f.pi_apply_eq_sum_univ x; aesop
            simp only [hB_inj, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
            exact Finset.sum_congr rfl fun _ _ => by aesop
          · have hB_inj : f y = ∑ j : Fin n, y j • f (Pi.single j 1) := by
              convert f.pi_apply_eq_sum_univ y
              aesop
            simp [hB_inj, mul_comm]
            aesop
        exact hf_inj hB_inj
      classical exact nonsingular_of_linearIndependent_col (mulVec_injective_iff.mp hB_inj)
    -- Since $B$ has a zero row, its determinant is zero.
    have hB_det_zero : B.detp 1 = 0 ∧ B.detp (-1) = 0 := by
      have hB_det_zero : ∀ s : ℤˣ, B.detp s = 0 := by
        intro s
        apply detp_eq_zero_of_exists_row_eq_zero B s ⟨m, by linarith⟩
        intro j
        simp [B]
      exact ⟨hB_det_zero 1, hB_det_zero (-1)⟩
    have := hB_nonsingular 1 0; simp_all

end Matrix
