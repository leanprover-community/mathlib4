/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Defs
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Order.Preorder.Finite

/-!
# Correctness of Bird's determinant algorithm

This file contains a proof that Bird's division-free algorithm computes
`Matrix.det`, in both its matrix form `BirdDet.Spec.birdDet`
(`birdDetSpec_eq_det`) and its flat-array form `BirdDet.birdDet`
(`det_eq_birdDet`), formalizing the combinatorial argument of
[Richard S. Bird, *A simple division-free algorithm for computing determinants*][bird2011].

## Correspondence with the paper

* A word of length `p` is a tuple `Fin p → Fin n`, using the indexing convention
  above (NB: Indices in Bird's paper start at 1).
* `f[α, β]`, the minor on rows `α` and columns `β`, is `(A.submatrix α β).det`.
* `f[iα, jα]`, a bordered minor, is `bminor A i j α`, with the word `iα` spelled
  `Fin.cons i α`.
* `f[α, α]`, a principal minor, is `pminor A α`.
* If `i : Fin n` represents Bird's symbol `r = i.val + 1`, then Bird's
  `βᵣ = [r + 1, ..., n]` is represented by `Finset.Ioi i`.
* Bird's `Sₚ(βᵣ)`, the length `p` subsequences of `βᵣ`, is represented by `S p i`.

The theorem names `paper_eq1`, ..., `paper_eq5` follow Bird's numbering.

## Main results

- `BirdDet.birdDetSpec_eq_det`: `Matrix.det` computes the same determinant as `BirdDet.Spec.birdDet`
- `BirdDet.det_eq_birdDet`: `Matrix.det` computes the same determinant as `BirdDet.birdDet`
-/

namespace BirdDet

open scoped BigOperators

variable {R : Type*} [CommRing R] {m n : ℕ}

/-- `∑` over `Finset.Ioi i` as an `if`-guarded sum over all of `Fin n`. -/
theorem sum_Ioi_eq_sum_ite {M : Type*} [AddCommMonoid M] (i : Fin n) (f : Fin n → M) :
    ∑ k ∈ Finset.Ioi i, f k = ∑ k : Fin n, if i < k then f k else 0 := by
  rw [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]

/-- `S p i` is Bird's `Sₚ(βᵢ)`: words `α` of length `p` over the alphabet `βᵢ`. -/
def S (p : ℕ) (i : Fin n) : Finset (Fin p → Fin n) :=
  {α : Fin p → Fin n | StrictMono (Fin.cons i α)}

/-- Membership in `S p i` is strict monotonicity of the bordered word. -/
theorem mem_S {p : ℕ} {i : Fin n} {α : Fin p → Fin n} :
    α ∈ S p i ↔ StrictMono (Fin.cons i α) := by
  exact Finset.mem_filter_univ α

/-- Membership in `S p i` means that the word is strictly monotone and lies above `i`. -/
theorem mem_S_iff {p : ℕ} {i : Fin n} {α : Fin p → Fin n} :
    α ∈ S p i ↔ StrictMono α ∧ ∀ j, i < α j := by
  rw [mem_S]
  constructor
  · intro h
    constructor
    · exact h.comp Fin.strictMono_succ
    · intro j
      exact h (Fin.succ_pos j)
  · rintro ⟨hmono, hbound⟩
    cases p with
    | zero =>
      intro a b hab
      omega
    | succ p => exact hmono.vecCons (hbound 0)

/-- The base case of equation (1): `S₀(α) = {ε}`, the singleton of the empty
word `ε`. -/
theorem S_zero (i : Fin n) : S 0 i = {![]} := by
  ext α
  simp [mem_S, Fin.strictMono_iff_lt_succ, eq_iff_true_of_subsingleton]

/-- Bird's bordered minor `f[iα, jα]`. -/
abbrev bminor (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) {p : ℕ}
    (α : Fin p → Fin n) : R :=
  (A.submatrix (Fin.cons i α) (Fin.cons j α)).det

/-- Bird's principal minor `f[α, α]`. -/
abbrev pminor (A : Matrix (Fin n) (Fin n) R) {p : ℕ} (α : Fin p → Fin n) : R :=
  (A.submatrix α α).det

/-- Bird's equation (1) : `x^(p)_ij = (-1)^p ∑ { f[iα, jα] | α ∈ S_p(βᵢ) }` -/
abbrev Eq1 (A : Matrix (Fin n) (Fin n) R) (p : ℕ) : Prop :=
  Spec.iterMatrix A p =
    .of fun i j ↦ (-1 : R) ^ p • ∑ α ∈ S p i, bminor A i j α

/-! ## Decomposition `S_{p+1}(βᵢ) = { kα | k ∈ βᵢ, α ∈ S_p(β_k) }` -/

/-- `S (p + 1) i` can be written as the image of a `biUnion` -/
theorem S_succ_eq_biUnion {p : ℕ} (i : Fin n) :
    S (p + 1) i = (Finset.Ioi i).biUnion fun k ↦ (S p k).image (Fin.cons k) := by
  ext α
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_Ioi]
  constructor
  · intro hα
    exists α 0
    constructor
    · rw [mem_S_iff] at hα
      obtain ⟨_, hbounded⟩ := hα
      exact hbounded 0
    · exists Fin.tail α
      constructor
      · simp only [mem_S, Fin.cons_self_tail] at hα ⊢
        exact hα.comp Fin.strictMono_succ
      · exact Fin.cons_self_tail α
  · rintro ⟨k, hk, u, hu, rfl⟩
    simp only [mem_S] at hu ⊢
    exact StrictMono.vecCons hu hk

section MatrixProof

variable (A : Matrix (Fin n) (Fin n) R) {p : ℕ}

/-! ## Equations (2) and (3): substituting the induction hypothesis -/

/-- Bird's equation (2), assuming equation (1) at `p` as the induction hypothesis. -/
theorem paper_eq2 (i : Fin n) (hEq1 : Eq1 A p) :
    -Spec.diagSum (Spec.iterMatrix A p) i =
      (-1 : R) ^ (p + 1) • ∑ α ∈ S (p + 1) i, pminor A α := by
  calc
    -Spec.diagSum (Spec.iterMatrix A p) i =
      (-1 : R) ^ (p + 1) • ∑ k ∈ Finset.Ioi i, ∑ α ∈ S p k, bminor A k k α := by
      rw [Spec.diagSum_eq]
      rw [hEq1, ← sum_Ioi_eq_sum_ite]
      simp only [Matrix.of_apply, smul_eq_mul, ← Finset.mul_sum]
      ring
    _ = (-1 : R) ^ (p + 1) • ∑ α ∈ S (p + 1) i, pminor A α := by
      rw [S_succ_eq_biUnion, Finset.sum_biUnion]
      · apply congrArg ((-1) ^ (p + 1) • ·)
        apply Finset.sum_congr
        · rfl
        · intros
          symm
          apply Finset.sum_image
          intro _ _ _ _ hαβ
          rw [Fin.cons_inj] at hαβ
          obtain ⟨_, hαβ⟩ := hαβ
          assumption
      · intro k _ k' _ hne
        simp only [Function.onFun, Finset.disjoint_left, Finset.mem_image]
        rintro _ ⟨α, _, rfl⟩ ⟨β, _, hαβ⟩
        apply hne
        rw [Fin.cons_inj] at hαβ
        obtain ⟨hkk', _⟩ := hαβ
        symm
        exact hkk'

/-- One step of Bird's scalar recurrence, split into diagonal and tail parts. -/
theorem iter_succ_entry (i j : Fin n) :
    Spec.iterMatrix A (p + 1) i j =
      -Spec.diagSum (Spec.iterMatrix A p) i * A i j
      + ∑ k ∈ Finset.Ioi i, Spec.iterMatrix A p i k * A k j := by
  rw [Spec.iterMatrix_succ_apply, Spec.stepEntry_eq, Spec.diagSum_eq, sum_Ioi_eq_sum_ite]

/-- Bird's equation (3), assuming equation (1) at `p` as the induction hypothesis. -/
theorem paper_eq3 (i j : Fin n) (hEq1 : Eq1 A p) :
    Spec.iterMatrix A (p + 1) i j
      = (-1 : R) ^ (p + 1) • (∑ α ∈ S (p + 1) i, pminor A α * A i j
        - ∑ k ∈ Finset.Ioi i, ∑ α ∈ S p i, bminor A i k α * A k j) := by
  rw [iter_succ_entry, paper_eq2 _ _ hEq1, hEq1]
  simp only [smul_eq_mul, Matrix.of_apply, mul_assoc, Finset.sum_mul, ← Finset.mul_sum]
  ring

/-! ## Equation (5): first-column Laplace expansion -/

/-- Restricting Fin.cons i α to its successor indices recovers its tail α -/
lemma fin_cons_succ (α : Fin (p + 1) → Fin n) (i : Fin n) :
    Fin.cons i α ∘ Fin.succ = α := by
  funext q
  simp only [Function.comp_apply, Fin.cons_succ]

/--
Precomposing `Fin.cons i α` with the embedding that skips `s.succ` preserves the head `i`
and removes the entry at position `s` from the tail `α`.
-/
lemma fin_cons_succAbove (α : Fin (p + 1) → Fin n) (i : Fin n) (s : Fin (p + 1)) :
    Fin.cons i α ∘ s.succ.succAbove = Fin.cons i (s.removeNth α) := by
  funext q
  cases q using Fin.cases with
  | zero => rfl
  | succ t =>
    simp only [Function.comp_apply, Fin.succ_succAbove_succ, Fin.cons_succ]
    rfl

lemma det_submatrix_removeNth_eq_sign_mul_bminor
  (α : Fin (p + 1) → Fin n) (i : Fin n) (s : Fin (p + 1)) :
    (A.submatrix (Fin.cons i (s.removeNth α)) α).det =
      (-1 : R) ^ s.val * bminor A i (α s) (s.removeNth α) := by
  calc
    (A.submatrix (Fin.cons i (s.removeNth α)) α).det =
        (A.submatrix (Fin.cons i (s.removeNth α))
          (s.insertNth (α s) (s.removeNth α))).det := by
      rw [Fin.insertNth_self_removeNth]
    _ =
        ((A.submatrix (Fin.cons i (s.removeNth α))
          (Fin.cons (α s) (s.removeNth α))).submatrix id (Fin.cycleRange s)).det := by
      apply congrArg Matrix.det
      ext q r
      simp only [Matrix.submatrix_apply, id_eq]
      rw [Fin.cons_apply_cycleRange]
    _ = Equiv.Perm.sign (Fin.cycleRange s) *
        (A.submatrix (Fin.cons i (s.removeNth α))
          (Fin.cons (α s) (s.removeNth α))).det := by
      apply Matrix.det_permute'
    _ = (-1 : R) ^ s.val * bminor A i (α s) (s.removeNth α) := by
      rw [Fin.sign_cycleRange]
      simp

/-- First-column Laplace expansion of a bordered minor -/
theorem det_bordered_expand (α : Fin (p + 1) → Fin n) (i j : Fin n) :
    bminor A i j α =
      pminor A α * A i j -
      ∑ s : Fin (p + 1), bminor A i (α s) (s.removeNth α) * A (α s) j := by
  unfold pminor bminor
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  simp only [Nat.succ_eq_add_one, Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero,
    Matrix.submatrix_apply, Fin.cons_zero, one_mul, Fin.succAbove_zero, Matrix.submatrix_submatrix,
    Fin.val_succ, Fin.cons_succ, Finset.sum_neg_distrib]
  rw [fin_cons_succ, fin_cons_succ, mul_comm (A i j)]
  apply congrArg ((A.submatrix α α).det * A i j + ·)
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr
  · rfl
  · intro x _
    rw [mul_right_comm, ← neg_mul]
    congr
    rw [fin_cons_succAbove, det_submatrix_removeNth_eq_sign_mul_bminor, ← mul_assoc, ← pow_add]
    simp

/-- Bird's equation (5) -/
theorem paper_eq5 (i j : Fin n) :
    ∑ α ∈ S (p + 1) i, bminor A i j α =
      ∑ α ∈ S (p + 1) i, pminor A α * A i j -
      ∑ α ∈ S (p + 1) i, ∑ t : Fin (p + 1), bminor A i (α t) (t.removeNth α) * A (α t) j := by
  calc
    ∑ α ∈ S (p + 1) i, bminor A i j α =
        ∑ α ∈ S (p + 1) i, (pminor A α * A i j -
          ∑ t : Fin (p + 1), bminor A i (α t) (t.removeNth α) * A (α t) j) := by
      apply Finset.sum_congr
      · rfl
      · intro α _
        apply det_bordered_expand
    _ = ∑ α ∈ S (p + 1) i, pminor A α * A i j -
        ∑ α ∈ S (p + 1) i, ∑ t : Fin (p + 1),
          bminor A i (α t) (t.removeNth α) * A (α t) j := by
      rw [Finset.sum_sub_distrib]

/-! ## Comparing equations (3) and (5): reindex by sorted insert/delete -/

/-- A bordered minor is zero when its border column already occurs in the word. -/
theorem bminor_eq_zero_of_mem_range
    {k : Fin n} (α : Fin p → Fin n) (i : Fin n) (hk : k ∈ Set.range α) :
    bminor A i k α = 0 := by
  obtain ⟨q, hq⟩ := hk
  -- The repeated columns in the submatrix used in bminor are `0` and `q + 1`.
  apply Matrix.det_zero_of_column_eq (Fin.succ_ne_zero q)
  intro r
  simp only [Matrix.submatrix_apply, Fin.cons_succ, Fin.cons_zero]
  rw [hq]

/-- Inserting an entry into a tuple adds that entry to its range. -/
lemma range_insertNth {β : Type*} (q : Fin (p + 1)) (x : β) (f : Fin p → β) :
    Set.range (q.insertNth x f) = Set.insert x (Set.range f) := by
  ext y
  simp [Fin.exists_iff_succAbove q, Set.insert, eq_comm]

/-- A symbol above `i` that does not occur in a word in `S p i` can be inserted while
preserving strict monotonicity. -/
lemma exists_insertNth_mem_S {i : Fin n} {α : Fin p → Fin n} {k : Fin n}
    (hα : α ∈ S p i) (hik : i < k) (hk : k ∉ Set.range α) :
    ∃ t : Fin (p + 1), t.insertNth k α ∈ S (p + 1) i := by
  induction p generalizing i with
  | zero =>
    exact ⟨0, by simpa [Fin.insertNth_zero', mem_S, Fin.strictMono_iff_lt_succ] using hik⟩
  | succ p ih =>
    rw [mem_S_iff] at hα
    obtain ⟨hmono, hbound⟩ := hα
    have htail : Fin.tail α ∈ S p (α 0) := by
      rw [mem_S, Fin.cons_self_tail]
      assumption
    have hk_tail : k ∉ Set.range (Fin.tail α) := by
      rintro ⟨j, hj⟩
      exact hk ⟨j.succ, hj⟩
    by_cases hhead : k < α 0
    · exists 0
      simp only [Fin.insertNth_zero', mem_S]
      exact (hmono.vecCons hhead).vecCons hik
    · obtain ⟨t, ht⟩ := ih htail (by grind) hk_tail
      exists t.succ
      rw [← Fin.cons_self_tail α, Fin.insertNth_succ_cons, mem_S]
      rw [mem_S] at ht
      exact ht.vecCons (hbound 0)

/-- The off-diagonal sums in Bird's equations (3) and (5) agree. -/
theorem paper_eq3_eq5_off_diag (i j : Fin n) :
    ∑ k ∈ Finset.Ioi i, ∑ α ∈ S p i, bminor A i k α * A k j
      = ∑ α' ∈ S (p + 1) i, ∑ t : Fin (p + 1),
          bminor A i (α' t) (t.removeNth α') * A (α' t) j := by
  rw [Finset.sum_comm, ← Finset.sum_product', ← Finset.sum_product']
  symm
  -- Let
  --    `source := S (p + 1) i ×ˢ univ` indexes the right-hand sum, while
  --    `target := S p i ×ˢ Ioi i` indexes the left-hand sum.
  --
  -- The functions being summed are
  --    `f (α, t) := bminor A i (α t) (t.removeNth α) * A (α t) j` over `source` and
  --    `g (α, k) := bminor A i k α * A k j` over `target`.
  --
  -- `sum_of_injOn` proves:
  --    `∑ x ∈ source, f x = ∑ y ∈ target, g y`
  --
  -- The 'deletion map d' from source to target is:
  --    `d (α, t) ↦ (t.removeNth α, α t)`
  --
  -- To apply `sum_of_injOn` we are required to prove :
  --    1. `d` is injective
  --    2. `source.image d ⊆ target`
  --    3. `∀ x ∈ target, x ∉ source.image d → g x = 0`
  --    4. `∀ x ∈ source, f x = g (d x)`
  refine Finset.sum_of_injOn ?_ ?_ ?_ ?_ ?_
  · exact fun ⟨α, k⟩ ↦ ⟨k.removeNth α, α k⟩
  · unfold Set.InjOn
    simp only [Finset.coe_product, Finset.coe_univ, Set.mem_prod, Set.mem_univ, and_true,
      Finset.mem_coe, Prod.mk.injEq, and_imp, Prod.forall, mem_S_iff]
    intros α k hiα hi α' k' hiα' hj hremove hvalue
    have hrange : Set.range α = Set.range α' := calc
      Set.range α = Set.range (k.insertNth (α k) (k.removeNth α)) := by
        rw [Fin.insertNth_self_removeNth]
      _ = Set.insert (α k) (Set.range (k.removeNth α)) := by
        rw [range_insertNth]
      _ = Set.insert (α' k') (Set.range (k'.removeNth α')) := by
        rw [hvalue, hremove]
      _ = Set.range (k'.insertNth (α' k') (k'.removeNth α')) := by
        rw [range_insertNth]
      _ = Set.range α' := by
        rw [Fin.insertNth_self_removeNth]
    have hαα' := (hiα.range_inj hiα').mp hrange
    subst α'
    exact ⟨rfl, hiα.injective hvalue⟩
  · rintro ⟨α, t⟩ hα
    simp only [Finset.coe_product, Finset.coe_univ, Set.mem_prod, Set.mem_univ, and_true,
      Finset.mem_coe, Finset.coe_Ioi, Set.mem_Ioi, mem_S_iff] at hα ⊢
    obtain ⟨hmono, hbound⟩ := hα
    exact ⟨⟨hmono.comp (Fin.strictMono_succAbove t), fun q => hbound (t.succAbove q)⟩,
      hbound t⟩
  · rintro ⟨α, k⟩ htarget hnotmem
    simp only [Finset.mem_product, Finset.mem_Ioi] at htarget
    obtain ⟨hα, hk⟩ := htarget
    by_cases hoccurs : k ∈ Set.range α
    · rw [bminor_eq_zero_of_mem_range A α i hoccurs, zero_mul]
    · exfalso
      apply hnotmem
      obtain ⟨t, ht⟩ := exists_insertNth_mem_S hα hk hoccurs
      refine ⟨(t.insertNth k α, t), ?_, ?_⟩
      · simp only [Finset.coe_product, Finset.coe_univ, Set.mem_prod, Set.mem_univ, and_true]
        exact ht
      · simp only [Fin.removeNth_insertNth, Fin.insertNth_apply_same]
  · simp

/-- Bird's equation (4) -/
theorem paper_eq4 (i j : Fin n) :
    ∑ α ∈ S (p + 1) i, pminor A α * A i j
      - ∑ k ∈ Finset.Ioi i, ∑ α ∈ S p i, bminor A i k α * A k j
      = ∑ α ∈ S (p + 1) i, bminor A i j α := by
  rw [paper_eq5 A i j, paper_eq3_eq5_off_diag A i j]

/-! ## Bird's Equation (1) -/
theorem paper_eq1 : Eq1 A p := by
  induction p with
  | zero =>
    ext i j
    simp [Spec.iterMatrix_zero, S_zero, bminor]
  | succ p ih =>
    ext i j
    rw [Matrix.of_apply, paper_eq3 A i j ih, paper_eq4 A i j]

/-! ## instantiating equation (1) to prove Theorem 1 -/

/-- The bordered word of `Fin.succ` at `0` is the identity: Bird's `[1 .. n]`. -/
lemma cons_zero_succ : (Fin.cons 0 Fin.succ : Fin (p + 1) → Fin (p + 1)) = id :=
  Fin.cons_self_tail id

/-- The unique maximum-length word over the symbols above `0` is `Fin.succ`. -/
lemma S_max_length_eq_singleton : S p 0 = {Fin.succ} := by
  ext α
  simp only [mem_S, Finset.mem_singleton]
  constructor
  · intro h
    funext x
    simpa only [Fin.cons_succ, id_eq] using congrFun h.eq_id x.succ
  · intro hα
    rw [hα, cons_zero_succ]
    exact strictMono_id

/-- The sum of the maximum-length bordered minors based at `0` equals `A.det` -/
theorem sum_bminor_max_length_eq_det (A : Matrix (Fin (p + 1)) (Fin (p + 1)) R) :
    ∑ α ∈ S p 0, bminor A 0 0 α = A.det := by
  rw [S_max_length_eq_singleton, Finset.sum_singleton]
  unfold bminor
  rw [cons_zero_succ, Matrix.submatrix_id_id]


end MatrixProof

section FlatArrayProof

variable {rows cols n lo : ℕ}

/-! ## The flat-array implementation -/

/-- The row-major index is in-bounds of the Array of size `rows * cols`. -/
theorem rowMajorIndex_lt (i : Fin rows) (j : Fin cols) :
    cols * i.val + j.val < rows * cols := by
  exact (Fin.mkDivMod i j).isLt

/-- `sumFrom n lo f` is the sum of `f` over the half-open interval `[lo, n)`. -/
theorem sumFrom_eq_sum_Ico (f : ℕ → R) :
    BirdDet.sumFrom n lo f = ∑ k ∈ Finset.Ico lo n, f k := by
  induction lo using BirdDet.sumFrom_induct n with
  | step lo hlo ih =>
    rw [BirdDet.sumFrom_step n lo f hlo, ih,
      ← Finset.sum_eq_sum_Ico_succ_bot hlo f]
  | stop lo hlo =>
    rw [BirdDet.sumFrom_stop n lo f hlo, Finset.Ico_eq_empty hlo, Finset.sum_empty]

/-- Row-major array lookup agrees with lookup in the corresponding matrix. -/
theorem get_eq_ofArray_apply (A : Array R) (hA : A.size = rows * cols)
  (i : Fin rows) (j : Fin cols) :
    BirdDet.get cols A i.val j.val = Matrix.ofArray (m := rows) (n := cols) A hA i j := by
  have hidx : cols * i.val + j.val < A.size := by
    rw [hA]
    exact rowMajorIndex_lt i j
  simp [BirdDet.get_eq, Matrix.ofArray, Array.getD, hidx]

/-- A tail sum is the corresponding guarded sum over `Fin n`. -/
theorem sumFrom_fin_tail (i : Fin n) (f : ℕ → R) :
    BirdDet.sumFrom n (i.val + 1) f =
      ∑ k : Fin n, if i < k then f k.val else 0 := by
  rw [sumFrom_eq_sum_Ico]
  calc
    ∑ k ∈ Finset.Ico (i.val + 1) n, f k =
        ∑ k ∈ (Finset.range n).filter (fun x ↦ i.val < x), f k := by
      congr
      ext x
      simp only [Finset.mem_Ico, Order.add_one_le_iff,
        Finset.mem_filter, Finset.mem_range, and_comm]
    _ = ∑ k ∈ Finset.range n, if i.val < k then f k else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ k : Fin n, if i.val < k.val then f k.val else 0 := by
      rw [← Fin.sum_univ_eq_sum_range]
    _ = ∑ k : Fin n, if i < k then f k.val else 0 := by
      rfl

/-- The scalar recurrence initialized by array lookup agrees pointwise
  with the matrix recurrence. -/
theorem iter_get_eq_spec_iterMatrix (A : Array R) (hA : A.size = n * n) (t : ℕ) (i j : Fin n) :
    BirdDet.iter n A t (BirdDet.get n A) i.val j.val =
      Spec.iterMatrix (Matrix.ofArray (m := n) (n := n) A hA) t i j := by
  induction t generalizing i j with
  | zero =>
    rw [BirdDet.iter_zero, Spec.iterMatrix_zero]
    exact get_eq_ofArray_apply A hA i j
  | succ t ih =>
    rw [BirdDet.iter_succ, stepEntry_eq]
    rw [Spec.iterMatrix_succ_apply]
    rw [Spec.stepEntry_eq, sumFrom_fin_tail, sumFrom_fin_tail]
    simp only [ih, get_eq_ofArray_apply A hA, neg_mul]

end FlatArrayProof

public section

variable {n : ℕ}

/-- Bird's Theorem 1 -/
public theorem birdDetSpec_eq_det (A : Matrix (Fin n) (Fin n) R) :
    Matrix.det A = Spec.birdDet A := by
  cases n with
  | zero =>
    rw [Spec.birdDetSpec_zero]
    exact Matrix.det_fin_zero
  | succ k =>
    rw [Spec.birdDetSpec_succ_iterMatrix, paper_eq1,
      Matrix.of_apply, sum_bminor_max_length_eq_det, smul_eq_mul,
      ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨k, rfl⟩, one_mul]

/-- The flat-array algorithm `BirdDet.birdDet` computes the same determinant as
  `BirdDet.Spec.birdDet`. -/
theorem birdDet_eq_birdDetSpec (A : Array R) (hA : A.size = n * n) :
    birdDet n A = Spec.birdDet (Matrix.ofArray (m := n) (n := n) A hA) := by
  cases n with
  | zero => rw [birdDet_zero, Spec.birdDetSpec_zero]
  | succ k =>
    rw [birdDet_succ, Spec.birdDetSpec_succ_iterMatrix]
    apply congrArg ((-1 : R) ^ k * ·)
    exact iter_get_eq_spec_iterMatrix A hA k 0 0

/-- `BirdDet.birdDet n A` computes the determinant of the `n × n` matrix whose
  entries are stored in row-major order in `A`. -/
theorem det_eq_birdDet (A : Array R) (hA : A.size = n * n) :
    Matrix.det (Matrix.ofArray (m := n) (n := n) A hA) = birdDet n A := by
  rw [birdDet_eq_birdDetSpec]
  exact birdDetSpec_eq_det (Matrix.ofArray A hA)

end

end BirdDet
