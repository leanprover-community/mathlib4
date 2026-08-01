/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Defs
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Data.Fintype.Order
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

open Function
variable {R : Type*} [CommRing R] {m n : ℕ}

/-- `sumFrom n lo f` is the sum of `f` over the half-open interval `[lo, n)`. -/
theorem sumFrom_eq_sum_Ico {lo : ℕ} (f : ℕ → R) :
    BirdDet.sumFrom n lo f = ∑ k ∈ Finset.Ico lo n, f k := by
  induction lo using BirdDet.sumFrom_induct n with
  | step lo hlo ih => rw [sumFrom_step n lo f hlo, ih, ← Finset.sum_eq_sum_Ico_succ_bot hlo f]
  | stop lo hlo => rw [sumFrom_stop n lo f hlo, Finset.Ico_eq_empty hlo, Finset.sum_empty]

theorem sumFrom_fin_tail (i : Fin n) (f : ℕ → R) :
    BirdDet.sumFrom n (i.val + 1) f = ∑ k ∈ Finset.Ioi i, f k.val := calc
  _ = ∑ k ∈ Finset.Ico (i.val + 1) n, f k := by rw [sumFrom_eq_sum_Ico]
  _ = ∑ k ∈ (Finset.range n).filter (i.val < ·), f k := by congr; ext; aesop
  _ = ∑ k ∈ Finset.range n, if i.val < k then f k else 0 := by rw [Finset.sum_filter]
  _ = ∑ k : Fin n, if i.val < k.val then f k.val else 0 := by rw [← Fin.sum_univ_eq_sum_range]
  _ = ∑ k ∈ Finset.Ioi i, f k.val := by simp [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]

/-- The scalar recurrence initialized by array lookup agrees pointwise
  with the matrix recurrence. -/
theorem iterate_stepEntry_get_eq_spec (A : Array R) (hA : A.size = n * n) (t : ℕ) (i j : Fin n) :
    ((stepEntry n A)^[t] (BirdDet.get n A)) i.val j.val =
      (Spec.stepEntry (.ofArray A hA))^[t] (.ofArray A hA) i j := by
  rw [Matrix.ofArray_eq_of_getD]
  induction t generalizing i j with
  | zero => simp [get_eq]
  | succ t ih =>
    simp_rw [iterate_succ_apply', stepEntry_eq, Spec.stepEntry_eq, sumFrom_fin_tail, ih,
      Matrix.of_apply, get_eq]

/-- The flat-array algorithm `BirdDet.birdDet` computes the same determinant as
  `BirdDet.Spec.birdDet`. -/
theorem birdDet_eq_birdDetSpec (A : Array R) (hA : A.size = n * n) :
    birdDet n A = Spec.birdDet (.ofArray A hA) := by
  cases n with
  | zero => rw [birdDet_zero, Spec.birdDetSpec_zero]
  | succ k => simp [birdDet_succ, Spec.birdDetSpec_succ, ← iterate_stepEntry_get_eq_spec A hA k]

variable (A : Matrix (Fin n) (Fin n) R) {p : ℕ}

/-- Bird's bordered minor `f[iα, jα]`. -/
abbrev bminor (i j : Fin n) (α : Fin p → Fin n) : R :=
  (A.submatrix (Fin.cons i α) (Fin.cons j α)).det

/-- Bird's principal minor `f[α, α]`. -/
abbrev pminor (α : Fin p → Fin n) : R :=
  (A.submatrix α α).det

lemma det_submatrix_removeNth_eq_sign_mul_bminor
  (α : Fin (p + 1) → Fin n) (i : Fin n) (s : Fin (p + 1)) :
    (A.submatrix (Fin.cons i (s.removeNth α)) α).det =
      (-1 : R) ^ s.val * bminor A i (α s) (s.removeNth α) :=
  calc
    _ = (-1 : R) ^ s.val * ((A.submatrix (Fin.cons i (s.removeNth α)) α)
        |>.submatrix id (Fin.cycleRange s).symm).det := by
      rw [Matrix.det_permute']
      simp [← mul_assoc, ← pow_add]
    _ = (-1 : R) ^ s.val * bminor A i (α s) (s.removeNth α) := by
      congrm _ * Matrix.det ?_
      simp [Fin.cons_removeNth_eq_comp_cycleRange_symm]

/-- First-column Laplace expansion of a bordered minor -/
theorem det_bordered_expand (α : Fin (p + 1) → Fin n) (i j : Fin n) :
    bminor A i j α =
      pminor A α * A i j - ∑ s : Fin (p + 1), bminor A i (α s) (s.removeNth α) * A (α s) j := calc
  _ = A i j * pminor A α +
        ∑ s : Fin (p + 1), (-1 : R) ^ (s.val + 1) * A (α s) j *
          (A.submatrix (Fin.cons i (s.removeNth α)) α).det := by
      rw [bminor, Matrix.det_succ_column_zero, Fin.sum_univ_succ]; simp
  _ = pminor A α * A i j +
        ∑ s : Fin (p + 1),
          ((-1 : R) ^ (s.val + 1) *
            (A.submatrix (Fin.cons i (s.removeNth α)) α).det) * A (α s) j := by
    simp only [mul_comm (A i j), mul_right_comm]
  _ = pminor A α * A i j +
      ∑ s : Fin (p + 1), -(bminor A i (α s) (s.removeNth α) * A (α s) j) := by
    simp only [det_submatrix_removeNth_eq_sign_mul_bminor, ← mul_assoc, ← pow_add]; aesop
  _ = pminor A α * A i j -
      ∑ s : Fin (p + 1), bminor A i (α s) (s.removeNth α) * A (α s) j := by
    simp only [Finset.sum_neg_distrib, sub_eq_add_neg]

/-- A bordered minor is zero when its border column already occurs in the word. -/
theorem bminor_eq_zero_of_mem_range
    {k : Fin n} (α : Fin p → Fin n) (i : Fin n) (hk : k ∈ Set.range α) :
    bminor A i k α = 0 := by
  obtain ⟨q, rfl⟩ := hk
  -- The repeated columns in the submatrix used in bminor are `0` and `q + 1`.
  exact Matrix.det_zero_of_column_eq q.succ_ne_zero <| by simp

/-- `S p i` is Bird's `Sₚ(βᵢ)`: words `α` of length `p` over the alphabet `βᵢ`. -/
def S (p : ℕ) (i : Fin n) : Finset (Fin p → Fin n) :=
  {α : Fin p → Fin n | StrictMono (Fin.cons i α)}

/-- Membership in `S p i` is strict monotonicity of the bordered word. -/
theorem mem_S_iff {p : ℕ} {i : Fin n} {α : Fin p → Fin n} :
    α ∈ S p i ↔ StrictMono (Fin.cons i α) :=
  Finset.mem_filter_univ α

/-- The base case of equation (1): `S₀(α) = {ε}`, the singleton of the empty
word `ε`. -/
theorem S_zero (i : Fin n) : S 0 i = {![]} := by
  ext; simp [mem_S_iff, Fin.strictMono_iff_lt_succ, eq_iff_true_of_subsingleton]

/-- The unique maximum-length word over the symbols above `0` is `Fin.succ`. -/
@[simp] lemma S_zero_eq_singleton {p : ℕ} : S p 0 = {Fin.succ} := by
  ext; simp [mem_S_iff]

/-! ## Decomposition `S_{p+1}(βᵢ) = { kα | k ∈ βᵢ, α ∈ S_p(β_k) }` -/

/-- `S (p + 1) i` can be written as the image of a `biUnion` -/
theorem S_succ_eq_biUnion {p : ℕ} (i : Fin n) :
    S (p + 1) i = (Finset.Ioi i).biUnion fun k ↦ (S p k).image (Fin.cons k) := by
  ext α
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_Ioi, mem_S_iff]
  refine ⟨fun hα ↦ ⟨α 0, (Fin.strictMono_cons.mp hα).1 0, Fin.tail α, ?_, Fin.cons_self_tail α⟩, ?_⟩
  · simp only [Fin.cons_self_tail]
    exact hα.comp Fin.strictMono_succ
  · rintro ⟨k, hk, u, hu, rfl⟩
    exact StrictMono.vecCons hu hk

/-- A symbol above `i` that does not occur in a word in `S p i` can be inserted while
preserving strict monotonicity. -/
lemma exists_insertNth_mem_S {p : ℕ} {i : Fin n} {α : Fin p → Fin n} {k : Fin n}
    (hα : α ∈ S p i) (hik : i < k) (hk : k ∉ Set.range α) :
    ∃ t : Fin (p + 1), t.insertNth k α ∈ S (p + 1) i := by
  set t := ⨅ j ∈ {j | k < α j}, j.castSucc with t_eq
  use t
  simp only [mem_S_iff, Fin.strictMono_cons] at ⊢ hα
  refine ⟨fun j ↦ Fin.succAboveCases t ?_ ?_ j, ?_⟩
  · simp only [t_eq, Set.mem_ofPred_eq, Fin.strictMono_insertNth_iff, hα.2, lt_iInf_iff,
      le_iInf_iff, forall_exists_index, and_imp, iInf_le_iff_forall_lt, iInf_lt_iff,
      exists_prop, true_and]
    refine ⟨fun j x hjx h ↦ ?_, fun j h ↦ ?_⟩
    · contrapose! h
      have k_ne (j : Fin p) : k ≠ α j := fun hj ↦ hk ⟨j, hj.symm⟩
      exact ⟨j, h.lt_of_ne (k_ne _), hjx⟩
    · obtain ⟨q, hkq, hqj⟩ := h j.succ j.castSucc_lt_succ
      exact hkq.trans_le <| hα.2.monotone <| Fin.castSucc_lt_succ_iff.mp hqj
  · simpa
  · simpa using hα.1

variable (p) in
/-- Bird's equation (1) : `x^(p)_ij = (-1)^p ∑ { f[iα, jα] | α ∈ S_p(βᵢ) }`. -/
abbrev Eq1 : Prop :=
  (Spec.stepEntry A)^[p] A = .of fun i j ↦ (-1) ^ p * ∑ α ∈ S p i, bminor A i j α

/-! ## Equations (2) and (3): substituting the induction hypothesis -/

/-- Bird's equation (2), assuming equation (1) at `p` as the induction hypothesis. -/
theorem paper_eq2 (i : Fin n) (hEq1 : Eq1 A p) :
    (-∑ k ∈ Finset.Ioi i, (Spec.stepEntry A)^[p] A k k) =
      (-1) ^ (p + 1) * ∑ α ∈ S (p + 1) i, pminor A α := by
  calc
    (-∑ k ∈ Finset.Ioi i, (Spec.stepEntry A)^[p] A k k) =
        (-1) ^ (p + 1) * ∑ k ∈ Finset.Ioi i, ∑ α ∈ S p k, bminor A k k α := by
      simp only [hEq1, Matrix.of_apply, ← Finset.mul_sum]
      ring
    _ = (-1) ^ (p + 1) * ∑ α ∈ S (p + 1) i, pminor A α := by
      rw [S_succ_eq_biUnion, Finset.sum_biUnion]
      · congrm (((-1) ^ (p + 1) * ∑ k ∈ Finset.Ioi i, ?_))
        symm
        exact Finset.sum_image fun _ _ _ _ hαβ => (Fin.cons_inj.mp hαβ).2
      · grind [Set.PairwiseDisjoint, Set.Pairwise, Finset.disjoint_left, Fin.cons_inj]

/-- Bird's equation (3), assuming equation (1) at `p` as the induction hypothesis. -/
theorem paper_eq3 (i j : Fin n) (hEq1 : Eq1 A p) :
    ((Spec.stepEntry A)^[p + 1] A) i j =
      (-1) ^ (p + 1) * (∑ α ∈ S (p + 1) i, pminor A α * A i j -
        ∑ k ∈ Finset.Ioi i, ∑ α ∈ S p i, bminor A i k α * A k j) := by
  simp_rw [iterate_succ_apply', Spec.stepEntry_eq, Matrix.of_apply, paper_eq2 _ _ hEq1, hEq1,
    Matrix.of_apply, mul_assoc, Finset.sum_mul, ← Finset.mul_sum]
  ring

/-! ## Equation (5): first-column Laplace expansion -/

/-- Bird's equation (5) -/
theorem paper_eq5 (i j : Fin n) :
    ∑ α ∈ S (p + 1) i, bminor A i j α =
      ∑ α ∈ S (p + 1) i, pminor A α * A i j -
      ∑ α ∈ S (p + 1) i, ∑ t : Fin (p + 1), bminor A i (α t) (t.removeNth α) * A (α t) j := calc
  _ = ∑ α ∈ S (p + 1) i, (pminor A α * A i j -
        ∑ t : Fin (p + 1), bminor A i (α t) (t.removeNth α) * A (α t) j) := by
      exact Finset.sum_congr rfl <| by simp [det_bordered_expand]
  _ = ∑ α ∈ S (p + 1) i, pminor A α * A i j -
        ∑ α ∈ S (p + 1) i, ∑ t : Fin (p + 1), bminor A i (α t) (t.removeNth α) * A (α t) j := by
    rw [Finset.sum_sub_distrib]

/-! ## Comparing equations (3) and (5): reindex by sorted insert/delete -/

/-- The off-diagonal sums in Bird's equations (3) and (5) agree. -/
theorem paper_eq3_eq5_off_diag (i j : Fin n) :
    ∑ k ∈ Finset.Ioi i, ∑ α ∈ S p i, bminor A i k α * A k j =
      ∑ α' ∈ S (p + 1) i, ∑ t : Fin (p + 1), bminor A i (α' t) (t.removeNth α') * A (α' t) j := by
  rw [Finset.sum_comm, ← Finset.sum_product', ← Finset.sum_product']
  -- The right-hand summand is the left-hand summand composed with the deletion map
  --
  --   d (α, t) := (t.removeNth α, α t).
  --
  -- This map is injective, and every left-hand summand outside its image is zero,
  -- so `sum_of_injOn` applies.
  symm
  refine Finset.sum_of_injOn (fun ⟨α, k⟩ ↦ ⟨k.removeNth α, α k⟩) ?_ ?_ ?_ ?_
  · simp only [Set.InjOn, Finset.coe_product, Finset.coe_univ, Set.mem_prod, Set.mem_univ,
      and_true, Finset.mem_coe, Prod.mk.injEq, and_imp, Prod.forall, mem_S_iff, Fin.strictMono_cons]
    intros α k hi hiα α' k' hj hiα' hremove hvalue
    suffices hrange : Set.range α = Set.range α' by
      rw [hiα.range_inj hiα'] at hrange
      subst α'
      exact ⟨rfl, hiα.injective hvalue⟩
    calc
      _ = Set.insert (α k) (Set.range (k.removeNth α)) := by
        rw [← Fin.range_insertNth, Fin.insertNth_self_removeNth]
      _ = Set.insert (α' k') (Set.range (k'.removeNth α')) := by
        rw [hvalue, hremove]
      _ = Set.range α' := by
        rw [← Fin.range_insertNth, Fin.insertNth_self_removeNth]
  · rintro ⟨α, t⟩ hα
    simp only [Finset.coe_product, Finset.coe_univ, Set.mem_prod, Set.mem_univ, and_true,
      Finset.mem_coe, Finset.coe_Ioi, Set.mem_Ioi, mem_S_iff, Fin.strictMono_cons] at hα ⊢
    obtain ⟨hbound, hmono⟩ := hα
    exact ⟨⟨fun q => hbound (t.succAbove q), hmono.removeNth t⟩, hbound t⟩
  · rintro ⟨α, k⟩ htarget hnotmem
    simp only [Finset.mem_product, Finset.mem_Ioi] at htarget
    obtain ⟨hα, hk⟩ := htarget
    by_cases hoccurs : k ∈ Set.range α
    · -- The border column `k` is repeated among the columns indexed by `α` and
      -- so the bordered minor is 0.
      rw [bminor_eq_zero_of_mem_range A α i hoccurs, zero_mul]
    · contrapose hnotmem
      obtain ⟨t, ht⟩ := exists_insertNth_mem_S hα hk hoccurs
      exact ⟨(t.insertNth k α, t), by simpa, by simp⟩
  · simp

/-! ## Bird's Equation (1) -/
theorem paper_eq1 : Eq1 A p := by
  induction p with
  | zero =>
    ext i j
    simp [iterate_zero_apply, S_zero, bminor]
  | succ p ih =>
    ext i j
    rw [Matrix.of_apply, paper_eq3 A i j ih, paper_eq5 A, paper_eq3_eq5_off_diag A]

/-! ## instantiating equation (1) to prove Theorem 1 -/

/-- Bird's Theorem 1 -/
theorem birdDetSpec_eq_det (A : Matrix (Fin n) (Fin n) R) :
    Matrix.det A = Spec.birdDet A := by
  cases n with
  | zero => simp
  | succ k =>
    have : ∑ α ∈ S k 0, bminor A 0 0 α = A.det := by simp [bminor]
    rw [Spec.birdDetSpec_succ, paper_eq1, Matrix.of_apply, ← mul_assoc, ← pow_add]; aesop

/-- `BirdDet.birdDet n A` computes the determinant of the `n × n` matrix whose
  entries are stored in row-major order in `A`. -/
public theorem det_eq_birdDet (A : Array R) (hA : A.size = n * n) :
    Matrix.det (.ofArray A hA) = birdDet n A := by
  rw [birdDet_eq_birdDetSpec, birdDetSpec_eq_det]

end BirdDet
