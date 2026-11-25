/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johnathon Kyle Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.GroupTheory.Coxeter.Presentation
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Faithfulness of the Geometric Representation of Coxeter Groups

This file constructs the classical Tits geometric representation of a finite-rank `CoxeterMatrix B`
(`B` finite) on `B → ℝ` via the symmetric bilinear form `B(eᵢ, eⱼ) = -2 cos(π / M i j)`
(with `B(eᵢ, eⱼ) = -2` when `M i j = 0`, representing `∞`, and `B(eᵢ, eᵢ) = 2` since `M i i = 1`).

Following Humphreys (*Reflection Groups and Coxeter Groups*, §5.3–5.4), we prove:
* root positivity (`w(eᵢ) ≥ 0 ↔ ℓ(w sᵢ) > ℓ(w)`) and the root partition
  `Φ = Φ⁺ ⊔ -Φ⁺`,
* the Exchange Property for the geometric reflection group,
* exact braid orders `orderOf (sᵢ * sⱼ) = M i j`,
* faithfulness (injectivity) of the geometric representation `W →* Matrix B B ℝ`.

As immediate corollaries for any finite-rank `CoxeterSystem M W`, the simple reflections
`cs.simple : B → W` are distinct (`CoxeterSystem.simple_injective`) and pairwise products have
exact order `orderOf (cs.simple i * cs.simple j) = M i j`.

## Main definitions
* `CoxeterMatrix.geometricForm`: The symmetric bilinear form matrix on `B`.
* `CoxeterMatrix.geometricReflection`: The `i`-th generating reflection matrix `sᵢ`.
* `CoxeterMatrix.geometricRep` / `CoxeterSystem.geometricRep`: The geometric representation
  into `Matrix B B ℝ`.

## Main results
* `CoxeterMatrix.geometricReflection_mul_self`: `sᵢ * sᵢ = 1`.
* `CoxeterMatrix.geometricReflection_preserves_form`: `sᵢᵀ * B * sᵢ = B`.
* `CoxeterMatrix.orderOf_geometricReflection_mul`: `orderOf (sᵢ * sⱼ) = M i j`.
* `CoxeterMatrix.geometricRep_injective` / `CoxeterSystem.geometricRep_injective`:
  Faithfulness of the geometric representation.
* `CoxeterSystem.simple_injective`: Distinct indices give distinct simple reflections.
* `CoxeterSystem.orderOf_simple_mul_simple`: `orderOf (cs.simple i * cs.simple j) = M i j`.
* `CoxeterSystem.geometricRep_mulVec_single_nonneg_iff`:
  `(∀ r, 0 ≤ (cs.geometricRep w *ᵥ Pi.single i 1) r) ↔`
  `cs.length w < cs.length (w * cs.simple i)`.
* `CoxeterSystem.geometricRep_mulVec_single_nonneg_or_nonpos`: Every root is positive or negative.
-/

open Matrix

@[expose] public section

namespace CoxeterMatrix

variable {B : Type*}

/-! ### Geometric bilinear form and generating reflections -/

/-- The canonical symmetric bilinear form of a Coxeter matrix `M`:
`geometricForm M i j = -2` if `M i j = 0` (`∞`), and `-2 * Real.cos (Real.pi / M i j)`
otherwise. In particular `geometricForm M i i = 2`. -/
noncomputable def geometricForm (M : CoxeterMatrix B) : Matrix B B ℝ :=
  Matrix.of fun i j ↦ if M i j = 0 then -2 else -2 * Real.cos (Real.pi / M i j)

@[simp]
lemma geometricForm_apply (M : CoxeterMatrix B) (i j : B) :
    M.geometricForm i j = if M i j = 0 then -2 else -2 * Real.cos (Real.pi / M i j) := rfl

theorem geometricForm_isSymm (M : CoxeterMatrix B) : M.geometricForm.IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, geometricForm_apply, M.symmetric j i]

theorem geometricForm_diag (M : CoxeterMatrix B) (i : B) : M.geometricForm i i = 2 := by
  simp [geometricForm_apply]

theorem geometricForm_apply_eq_neg_two (M : CoxeterMatrix B) {i j : B} (h : M i j = 0) :
    M.geometricForm i j = -2 := by
  simp [geometricForm_apply, h]

theorem geometricForm_apply_of_ne_zero (M : CoxeterMatrix B) {i j : B} (h : M i j ≠ 0) :
    M.geometricForm i j = -2 * Real.cos (Real.pi / M i j) := by
  simp [geometricForm_apply, h]

variable [DecidableEq B]

/-- The `i`-th generating reflection matrix `sᵢ` of the geometric representation of `M`:
`(sᵢ)_{r, c} = δ_{r, c} - δ_{r, i} * geometricForm M i c`. -/
noncomputable def geometricReflection (M : CoxeterMatrix B) (i : B) : Matrix B B ℝ :=
  Matrix.of fun r c ↦ (if r = c then 1 else 0) - (if r = i then M.geometricForm i c else 0)

@[simp]
lemma geometricReflection_apply (M : CoxeterMatrix B) (i r c : B) :
    M.geometricReflection i r c =
      (if r = c then 1 else 0) - (if r = i then M.geometricForm i c else 0) := rfl

lemma geometricReflection_apply_self (M : CoxeterMatrix B) (i : B) :
    M.geometricReflection i i i = -1 := by
  simp only [geometricReflection_apply, ite_true, geometricForm_diag]
  norm_num

theorem geometricReflection_injective (M : CoxeterMatrix B) :
    Function.Injective M.geometricReflection := by
  intro i j h
  by_contra hij
  have h1 := congrFun (congrFun h i) i
  rw [geometricReflection_apply_self] at h1
  simp only [geometricReflection_apply, ite_true, hij, ite_false, sub_zero] at h1
  norm_num at h1

variable [Fintype B]

/-- Every geometric reflection `sᵢ` is an involution (`sᵢ * sᵢ = 1`). -/
theorem geometricReflection_mul_self (M : CoxeterMatrix B) (i : B) :
    M.geometricReflection i * M.geometricReflection i = 1 := by
  set f := M.geometricForm
  ext r c
  simp only [Matrix.mul_apply, Matrix.one_apply, geometricReflection_apply]
  have hsum : ∀ k : B,
      ((if r = k then (1 : ℝ) else 0) - (if r = i then f i k else 0)) *
        ((if k = c then (1 : ℝ) else 0) - (if k = i then f i c else 0)) =
      (if k = r then if r = c then (1 : ℝ) else 0 else 0)
        - (if k = r then if r = i then f i c else 0 else 0)
        - (if k = c then if r = i then f i k else 0 else 0)
        + (if k = i then if r = i then f i k * f i c else 0 else 0) := by
    intro k
    split_ifs <;> simp_all <;> ring
  simp_rw [show ∀ k, ((if r = k then (1 : ℝ) else 0) -
      (if r = i then M.geometricForm i k else 0)) *
      ((if k = c then (1 : ℝ) else 0) - (if k = i then M.geometricForm i c else 0)) =
      (if k = r then if r = c then (1 : ℝ) else 0 else 0)
        - (if k = r then if r = i then f i c else 0 else 0)
        - (if k = c then if r = i then f i k else 0 else 0)
        + (if k = i then if r = i then f i k * f i c else 0 else 0) from hsum,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ]
  simp only [ite_true]
  by_cases hri : r = i
  · subst hri
    have hdiag : f r r = 2 := M.geometricForm_diag r
    simp only [ite_true, hdiag]
    ring
  · simp [hri]

/-- Every geometric reflection preserves `M.geometricForm`: `sᵢᵀ * B * sᵢ = B`. -/
theorem geometricReflection_preserves_form (M : CoxeterMatrix B) (i : B) :
    (M.geometricReflection i)ᵀ * M.geometricForm * M.geometricReflection i = M.geometricForm := by
  have hsymm : ∀ a b : B, M.geometricForm a b = M.geometricForm b a := fun a b ↦
    M.geometricForm_isSymm.apply b a
  ext r c
  simp only [Matrix.mul_apply, Matrix.transpose_apply, geometricReflection_apply]
  have hleft : ∀ k : B,
      (∑ x : B, ((if x = r then (1 : ℝ) else 0) -
          (if x = i then M.geometricForm i r else 0)) * M.geometricForm x k) =
      M.geometricForm r k - M.geometricForm i r * M.geometricForm i k := by
    intro k
    have hsplit : ∀ x : B,
        ((if x = r then (1 : ℝ) else 0) -
            (if x = i then M.geometricForm i r else 0)) * M.geometricForm x k =
        (if x = r then M.geometricForm x k else 0) -
          (if x = i then M.geometricForm i r * M.geometricForm x k else 0) := by
      intro x
      split_ifs <;> ring
    simp_rw [hsplit, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ]
    simp only [ite_true]
  simp_rw [hleft]
  have hright : ∀ k : B,
      (M.geometricForm r k - M.geometricForm i r * M.geometricForm i k) *
        ((if k = c then (1 : ℝ) else 0) - (if k = i then M.geometricForm i c else 0)) =
      (if k = c then M.geometricForm r k - M.geometricForm i r * M.geometricForm i k else 0) -
        (if k = i then (M.geometricForm r k - M.geometricForm i r * M.geometricForm i k) *
          M.geometricForm i c else 0) := by
    intro k
    split_ifs <;> ring
  simp_rw [hright, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ]
  simp only [ite_true, geometricForm_diag]
  rw [hsymm r i]
  ring

/-- Every geometric reflection has determinant `-1`. -/
theorem det_geometricReflection (M : CoxeterMatrix B) (i : B) :
    (M.geometricReflection i).det = -1 := by
  rw [Matrix.det_apply]
  have hterm : ∀ σ : Equiv.Perm B,
      Equiv.Perm.sign σ • ∏ r : B, M.geometricReflection i (σ r) r =
      if σ = 1 then -1 else 0 := by
    intro σ
    by_cases hσ : σ = 1
    · subst hσ
      simp only [Equiv.Perm.sign_one, one_smul, Equiv.Perm.coe_one, id_eq, ite_true]
      have hprod : ∏ r : B, M.geometricReflection i r r =
          ∏ r : B, (if r = i then (-1 : ℝ) else 1) := by
        refine Finset.prod_congr rfl fun r _ ↦ ?_
        by_cases hr : r = i
        · subst hr
          simp only [ite_true, geometricReflection_apply_self]
        · simp [geometricReflection_apply, hr]
      rw [hprod]
      simp
    · simp only [hσ, ite_false]
      have hex : ∃ r : B, σ r ≠ r ∧ σ r ≠ i := by
        by_contra hno
        apply hσ
        refine Equiv.ext fun r ↦ ?_
        by_cases hrr : σ r = r
        · exact hrr
        · have hri : σ r = i := by
            by_contra h
            exact hno ⟨r, hrr, h⟩
          have hne : r ≠ i := fun h ↦ hrr (h ▸ hri)
          have hσi : σ i ≠ i := fun h ↦ hne (σ.injective (hri.trans h.symm))
          have hii : σ i = i := by
            by_contra h
            exact hno ⟨i, hσi, h⟩
          exact absurd hii hσi
      obtain ⟨r, hr1, hr2⟩ := hex
      have hzero : M.geometricReflection i (σ r) r = 0 := by
        simp [geometricReflection_apply, hr1, hr2]
      have hprod0 : ∏ x : B, M.geometricReflection i (σ x) x = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ r) hzero
      rw [hprod0, smul_zero]
  simp_rw [hterm]
  simp

/-! ### Action on vectors, Chebyshev coefficients, and rank-two relations -/

section RootPositivity

private noncomputable abbrev geomWordProd (M : CoxeterMatrix B) (w : List B) : Matrix B B ℝ :=
  (w.map M.geometricReflection).prod

private lemma gwp_nil (M : CoxeterMatrix B) : geomWordProd M [] = 1 := rfl

private lemma gwp_cons (M : CoxeterMatrix B) (a : B) (w : List B) :
    geomWordProd M (a :: w) = M.geometricReflection a * geomWordProd M w := rfl

private lemma gwp_append (M : CoxeterMatrix B) (u v : List B) :
    geomWordProd M (u ++ v) = geomWordProd M u * geomWordProd M v := by
  simp [geomWordProd]

private lemma gwp_singleton (M : CoxeterMatrix B) (a : B) :
    geomWordProd M [a] = M.geometricReflection a := by
  simp [geomWordProd]

private lemma gwp_mul_reverse (M : CoxeterMatrix B) (w : List B) :
    geomWordProd M w * geomWordProd M w.reverse = 1 := by
  induction w with
  | nil => simp [geomWordProd]
  | cons a t ih =>
    simp only [geomWordProd, List.map_cons, List.prod_cons, List.reverse_cons, List.map_append,
      List.prod_append, List.map_nil, List.prod_nil, mul_one] at ih ⊢
    calc M.geometricReflection a * (t.map M.geometricReflection).prod *
          ((t.reverse.map M.geometricReflection).prod * M.geometricReflection a)
        = M.geometricReflection a *
          ((t.map M.geometricReflection).prod * (t.reverse.map M.geometricReflection).prod) *
          M.geometricReflection a := by simp only [mul_assoc]
      _ = 1 := by rw [ih, mul_one, geometricReflection_mul_self]

private lemma gwp_reverse_mul (M : CoxeterMatrix B) (w : List B) :
    geomWordProd M w.reverse * geomWordProd M w = 1 := by
  simpa using gwp_mul_reverse M w.reverse

private lemma gwp_append_self (M : CoxeterMatrix B) (w : List B) (a : B) :
    geomWordProd M (w ++ [a] ++ [a]) = geomWordProd M w := by
  rw [gwp_append, gwp_append, gwp_singleton, Matrix.mul_assoc, geometricReflection_mul_self,
    Matrix.mul_one]

private lemma det_geomWordProd (M : CoxeterMatrix B) (w : List B) :
    (geomWordProd M w).det = (-1 : ℝ) ^ w.length := by
  induction w with
  | nil => simp [geomWordProd]
  | cons a t ih =>
    simp only [geomWordProd, List.map_cons, List.prod_cons, Matrix.det_mul,
      det_geometricReflection, List.length_cons] at ih ⊢
    rw [ih, pow_succ']

private noncomputable def geomLen (M : CoxeterMatrix B) (g : Matrix B B ℝ) : ℕ :=
  sInf {k | ∃ w : List B, w.length = k ∧ geomWordProd M w = g}

private lemma geomLen_le (M : CoxeterMatrix B) (w : List B) :
    geomLen M (geomWordProd M w) ≤ w.length :=
  Nat.sInf_le ⟨w, rfl, rfl⟩

private lemma exists_word_geomLen (M : CoxeterMatrix B) (w : List B) :
    ∃ v : List B, v.length = geomLen M (geomWordProd M w) ∧
      geomWordProd M v = geomWordProd M w :=
  Nat.sInf_mem (s := {k | ∃ v : List B, v.length = k ∧ geomWordProd M v = geomWordProd M w})
    ⟨w.length, w, rfl, rfl⟩

private lemma geomLen_append_le (M : CoxeterMatrix B) (u v : List B) :
    geomLen M (geomWordProd M (u ++ v)) ≤
      geomLen M (geomWordProd M u) + geomLen M (geomWordProd M v) := by
  obtain ⟨u', hu', hu'p⟩ := exists_word_geomLen M u
  obtain ⟨v', hv', hv'p⟩ := exists_word_geomLen M v
  have h : geomWordProd M (u' ++ v') = geomWordProd M (u ++ v) := by
    rw [gwp_append, gwp_append, hu'p, hv'p]
  calc geomLen M (geomWordProd M (u ++ v)) = geomLen M (geomWordProd M (u' ++ v')) := by rw [h]
    _ ≤ (u' ++ v').length := geomLen_le M _
    _ = geomLen M (geomWordProd M u) + geomLen M (geomWordProd M v) := by
      rw [List.length_append, hu', hv']

private lemma geomLen_singleton_le (M : CoxeterMatrix B) (a : B) :
    geomLen M (geomWordProd M [a]) ≤ 1 := geomLen_le M [a]

private lemma gwp_eq_one_of_geomLen_eq_zero (M : CoxeterMatrix B) (w : List B)
    (h : geomLen M (geomWordProd M w) = 0) : geomWordProd M w = 1 := by
  obtain ⟨v, hv, hvp⟩ := exists_word_geomLen M w
  rw [h, List.length_eq_zero_iff] at hv
  rw [← hvp, hv, gwp_nil]

private lemma det_eq_geomLen (M : CoxeterMatrix B) (w : List B) :
    (geomWordProd M w).det = (-1 : ℝ) ^ geomLen M (geomWordProd M w) := by
  obtain ⟨v, hv, hvp⟩ := exists_word_geomLen M w
  rw [← hvp, det_geomWordProd, hv, hvp]

private lemma geomLen_ne_of_det_neg (M : CoxeterMatrix B) {u v : List B}
    (h : (geomWordProd M u).det = -(geomWordProd M v).det) :
    geomLen M (geomWordProd M u) ≠ geomLen M (geomWordProd M v) := by
  intro he
  rw [det_eq_geomLen, det_eq_geomLen, he] at h
  have hx : ((-1 : ℝ) ^ geomLen M (geomWordProd M v)) ≠ 0 := pow_ne_zero _ (by norm_num)
  apply hx
  linarith

private lemma det_append_singleton (M : CoxeterMatrix B) (w : List B) (a : B) :
    (geomWordProd M (w ++ [a])).det = -(geomWordProd M w).det := by
  rw [gwp_append, Matrix.det_mul, gwp_singleton, det_geometricReflection]
  ring

private lemma det_cons (M : CoxeterMatrix B) (w : List B) (a : B) :
    (geomWordProd M (a :: w)).det = -(geomWordProd M w).det := by
  rw [gwp_cons, Matrix.det_mul, det_geometricReflection]
  ring

private lemma geomLen_append_singleton (M : CoxeterMatrix B) (w : List B) (a : B) :
    geomLen M (geomWordProd M (w ++ [a])) = geomLen M (geomWordProd M w) + 1 ∨
      geomLen M (geomWordProd M (w ++ [a])) + 1 = geomLen M (geomWordProd M w) := by
  have h1 := geomLen_append_le M w [a]
  have h2 := geomLen_singleton_le M a
  have h3 : geomLen M (geomWordProd M w) ≤ geomLen M (geomWordProd M (w ++ [a])) + 1 := by
    have := geomLen_append_le M (w ++ [a]) [a]
    rw [gwp_append_self] at this
    omega
  have h4 := geomLen_ne_of_det_neg M (det_append_singleton M w a)
  omega

private lemma geomLen_cons (M : CoxeterMatrix B) (w : List B) (a : B) :
    geomLen M (geomWordProd M (a :: w)) = geomLen M (geomWordProd M w) + 1 ∨
      geomLen M (geomWordProd M (a :: w)) + 1 = geomLen M (geomWordProd M w) := by
  have h1 := geomLen_append_le M [a] w
  have h2 := geomLen_singleton_le M a
  have h3 : geomLen M (geomWordProd M w) ≤ geomLen M (geomWordProd M (a :: w)) + 1 := by
    have := geomLen_append_le M [a] (a :: w)
    have e : geomWordProd M ([a] ++ a :: w) = geomWordProd M w := by
      rw [gwp_append, gwp_singleton, gwp_cons, ← Matrix.mul_assoc, geometricReflection_mul_self,
        Matrix.one_mul]
    rw [e] at this
    omega
  have h4 := geomLen_ne_of_det_neg M (det_cons M w a)
  simp only [List.singleton_append] at h1
  omega

private lemma geomLen_reverse_le (M : CoxeterMatrix B) (w : List B) :
    geomLen M (geomWordProd M w.reverse) ≤ geomLen M (geomWordProd M w) := by
  obtain ⟨v, hv, hvp⟩ := exists_word_geomLen M w
  have h : geomWordProd M v.reverse = geomWordProd M w.reverse := by
    calc geomWordProd M v.reverse
        = geomWordProd M v.reverse * (geomWordProd M w * geomWordProd M w.reverse) := by
          rw [gwp_mul_reverse, Matrix.mul_one]
      _ = (geomWordProd M v.reverse * geomWordProd M v) * geomWordProd M w.reverse := by
          rw [hvp, Matrix.mul_assoc]
      _ = geomWordProd M w.reverse := by rw [gwp_reverse_mul, Matrix.one_mul]
  calc geomLen M (geomWordProd M w.reverse) = geomLen M (geomWordProd M v.reverse) := by rw [h]
    _ ≤ v.reverse.length := geomLen_le M _
    _ = geomLen M (geomWordProd M w) := by rw [List.length_reverse, hv]

private lemma geomLen_reverse (M : CoxeterMatrix B) (w : List B) :
    geomLen M (geomWordProd M w.reverse) = geomLen M (geomWordProd M w) := by
  have h1 := geomLen_reverse_le M w
  have h2 := geomLen_reverse_le M w.reverse
  rw [List.reverse_reverse] at h2
  omega

private lemma geomLen_of_isReducedWord (M : CoxeterMatrix B) {w : List B}
    (hw : CoxeterSystem.IsReducedWord M.geometricReflection w) :
    geomLen M (geomWordProd M w) = w.length := by
  obtain ⟨v, hv, hvp⟩ := exists_word_geomLen M w
  have := geomLen_le M w
  by_contra hne
  exact hw v (by omega) hvp.symm

private lemma mulVec_single (A : Matrix B B ℝ) (j : B) :
    A *ᵥ Pi.single j 1 = fun r ↦ A r j := by
  funext r
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

omit [Fintype B] in
private lemma single_ne_zero (i : B) : (Pi.single i (1 : ℝ) : B → ℝ) ≠ 0 := by
  intro h
  have := congrFun h i
  simp at this

private lemma geomRefl_mulVec (M : CoxeterMatrix B) (i : B) (v : B → ℝ) :
    M.geometricReflection i *ᵥ v = v - (M.geometricForm *ᵥ v) i • Pi.single i 1 := by
  funext r
  simp only [Matrix.mulVec, dotProduct, geometricReflection_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  by_cases hr : r = i
  · subst hr
    simp only [ite_true, Pi.single_eq_same, mul_one]
  · simp [hr]

private lemma geomRefl_single_self (M : CoxeterMatrix B) (i : B) :
    M.geometricReflection i *ᵥ Pi.single i 1 = -Pi.single i 1 := by
  rw [geomRefl_mulVec, mulVec_single]
  dsimp only
  rw [geometricForm_diag]
  funext r
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
  ring

private lemma geomRefl_fix (M : CoxeterMatrix B) (i : B) (v : B → ℝ)
    (hv : (M.geometricForm *ᵥ v) i = 0) : M.geometricReflection i *ᵥ v = v := by
  rw [geomRefl_mulVec, hv]
  simp

private lemma gwp_mulVec_single_ne_zero (M : CoxeterMatrix B) (w : List B) (i : B) :
    geomWordProd M w *ᵥ Pi.single i 1 ≠ 0 := by
  intro h
  have h2 : (geomWordProd M w.reverse * geomWordProd M w) *ᵥ Pi.single i 1 = 0 := by
    rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  rw [gwp_reverse_mul, Matrix.one_mulVec] at h2
  exact single_ne_zero i h2

private noncomputable def chebSeq (c : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | k + 2 => c * chebSeq c (k + 1) - chebSeq c k

private lemma chebSeq_step (c : ℝ) (hc : 2 ≤ c) : ∀ k : ℕ,
    1 ≤ chebSeq c (k + 1) - chebSeq c k ∧ 0 ≤ chebSeq c k
  | 0 => by simp [chebSeq]
  | k + 1 => by
    obtain ⟨h1, h2⟩ := chebSeq_step c hc k
    have h3 : 0 ≤ chebSeq c (k + 1) := by linarith
    refine ⟨?_, h3⟩
    rw [show chebSeq c (k + 2) = c * chebSeq c (k + 1) - chebSeq c k from rfl]
    nlinarith

private lemma chebSeq_ge (c : ℝ) (hc : 2 ≤ c) : ∀ k : ℕ, (k : ℝ) ≤ chebSeq c k
  | 0 => by simp [chebSeq]
  | k + 1 => by
    have := chebSeq_ge c hc k
    have := (chebSeq_step c hc k).1
    push_cast
    linarith

private lemma chebSeq_mul_sin (θ : ℝ) :
    ∀ k : ℕ, chebSeq (2 * Real.cos θ) k * Real.sin θ = Real.sin (k * θ)
  | 0 => by simp [chebSeq]
  | 1 => by simp [chebSeq]
  | k + 2 => by
    have e1 := chebSeq_mul_sin θ (k + 1)
    have e0 := chebSeq_mul_sin θ k
    have hs : Real.sin (((k + 2 : ℕ) : ℝ) * θ) =
        2 * Real.cos θ * Real.sin (((k + 1 : ℕ) : ℝ) * θ) - Real.sin ((k : ℝ) * θ) := by
      have h1 : ((k + 2 : ℕ) : ℝ) * θ = ((k + 1 : ℕ) : ℝ) * θ + θ := by push_cast; ring
      have h2 : (k : ℝ) * θ = ((k + 1 : ℕ) : ℝ) * θ - θ := by push_cast; ring
      rw [h1, h2, Real.sin_add, Real.sin_sub]
      ring
    rw [show chebSeq (2 * Real.cos θ) (k + 2) =
      2 * Real.cos θ * chebSeq (2 * Real.cos θ) (k + 1) - chebSeq (2 * Real.cos θ) k from rfl,
      hs]
    linear_combination (2 * Real.cos θ) * e1 - e0

private lemma sin_pi_div_pos {m : ℕ} (hm : 2 ≤ m) : 0 < Real.sin (Real.pi / m) := by
  have hm' : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  apply Real.sin_pos_of_pos_of_lt_pi
  · have : (0 : ℝ) < m := by linarith
    positivity
  · exact div_lt_self Real.pi_pos hm'

private lemma chebSeq_cos_nonneg {m : ℕ} (hm : 2 ≤ m) {k : ℕ} (hk : k ≤ m) :
    0 ≤ chebSeq (2 * Real.cos (Real.pi / m)) k := by
  have hs := sin_pi_div_pos hm
  have h := chebSeq_mul_sin (Real.pi / m) k
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hx : 0 ≤ Real.sin (k * (Real.pi / m)) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · positivity
    · calc (k : ℝ) * (Real.pi / m) ≤ (m : ℝ) * (Real.pi / m) := by gcongr
        _ = Real.pi := by field_simp
  by_contra hneg
  have hneg' : chebSeq (2 * Real.cos (Real.pi / m)) k < 0 := lt_of_not_ge hneg
  nlinarith

private lemma chebSeq_cos_two_mul {m : ℕ} (hm : 2 ≤ m) :
    chebSeq (2 * Real.cos (Real.pi / m)) (2 * m) = 0 ∧
      chebSeq (2 * Real.cos (Real.pi / m)) (2 * m + 1) = 1 := by
  have hs := sin_pi_div_pos hm
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have h0 := chebSeq_mul_sin (Real.pi / m) (2 * m)
  have h1 := chebSeq_mul_sin (Real.pi / m) (2 * m + 1)
  have e0 : ((2 * m : ℕ) : ℝ) * (Real.pi / m) = 2 * Real.pi := by push_cast; field_simp
  have e1 : ((2 * m + 1 : ℕ) : ℝ) * (Real.pi / m) = Real.pi / m + 2 * Real.pi := by
    push_cast; field_simp; ring
  rw [e0, Real.sin_two_pi] at h0
  rw [e1, Real.sin_add_two_pi] at h1
  constructor
  · rcases mul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd h hs.ne'
  · exact mul_right_cancel₀ hs.ne' (h1.trans (one_mul _).symm)

omit [Fintype B] in
private def pairVec (i j : B) (α β : ℝ) : B → ℝ :=
  fun r ↦ (if r = i then α else 0) + (if r = j then β else 0)

omit [Fintype B] in
private lemma pairVec_eq (i j : B) (α β : ℝ) :
    pairVec i j α β = α • Pi.single i 1 + β • Pi.single j 1 := by
  funext r
  simp [pairVec, Pi.single_apply]

omit [Fintype B] in
private lemma pairVec_single (i j : B) : pairVec i j 1 0 = Pi.single i 1 := by
  funext r
  by_cases hr : r = i <;> simp [pairVec, hr]

private lemma geomRefl_i_pairVec (M : CoxeterMatrix B) {i j : B} (hij : i ≠ j) (α β : ℝ) :
    M.geometricReflection i *ᵥ pairVec i j α β =
      pairVec i j (-M.geometricForm i j * β - α) β := by
  rw [geomRefl_mulVec, pairVec_eq, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    mulVec_single, mulVec_single, pairVec_eq]
  funext r
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    geometricForm_diag]
  by_cases hr : r = i
  · subst hr
    simp only [ite_true, hij, ite_false]
    ring
  · simp [hr]

private lemma geomRefl_j_pairVec (M : CoxeterMatrix B) {i j : B} (hij : i ≠ j) (α β : ℝ) :
    M.geometricReflection j *ᵥ pairVec i j α β =
      pairVec i j α (-M.geometricForm j i * α - β) := by
  rw [geomRefl_mulVec, pairVec_eq, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    mulVec_single, mulVec_single, pairVec_eq]
  funext r
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    geometricForm_diag]
  by_cases hr : r = j
  · subst hr
    simp only [ite_true, hij.symm, ite_false]
    ring
  · simp [hr]

omit [DecidableEq B] [Fintype B] in
private def altList (i j : B) : ℕ → List B
  | 0 => []
  | k + 1 => (if k % 2 = 0 then j else i) :: altList i j k

omit [DecidableEq B] [Fintype B] in
private lemma length_altList (i j : B) (k : ℕ) : (altList i j k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [altList, ih]

omit [DecidableEq B] [Fintype B] in
private lemma altList_append (i j : B) : ∀ k, altList i j k ++ [i] = altList j i (k + 1)
  | 0 => rfl
  | k + 1 => by
    rw [altList, List.cons_append, altList_append i j k]
    conv_rhs => rw [altList]
    congr 1
    split_ifs <;> first | rfl | omega

omit [DecidableEq B] [Fintype B] in
private lemma altList_add (i j : B) (q : ℕ) :
    ∀ r, ∃ Z : List B, Z.length = r ∧ altList i j (q + r) = Z ++ altList i j q
  | 0 => ⟨[], rfl, by simp⟩
  | r + 1 => by
    obtain ⟨Z, hZ, h⟩ := altList_add i j q r
    refine ⟨(if (q + r) % 2 = 0 then j else i) :: Z, by simp [hZ], ?_⟩
    rw [show q + (r + 1) = (q + r) + 1 by omega, altList, h]
    rfl

private lemma gwp_altList_even (M : CoxeterMatrix B) (i j : B) (k : ℕ) :
    geomWordProd M (altList i j (2 * k)) =
      (M.geometricReflection i * M.geometricReflection j) ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
    have hodd : (2 * k + 1) % 2 = 1 := by omega
    have heven : (2 * k) % 2 = 0 := by omega
    rw [e, altList, altList, gwp_cons, gwp_cons]
    simp only [hodd, one_ne_zero, ite_false, heven, ite_true, ih, pow_succ', Matrix.mul_assoc]

private lemma gwp_altList_mulVec_single (M : CoxeterMatrix B) {i j : B} (hij : i ≠ j) :
    ∀ m : ℕ, geomWordProd M (altList i j m) *ᵥ Pi.single i 1 =
      if m % 2 = 0 then pairVec i j (chebSeq (-M.geometricForm i j) (m + 1))
        (chebSeq (-M.geometricForm i j) m)
      else pairVec i j (chebSeq (-M.geometricForm i j) m)
        (chebSeq (-M.geometricForm i j) (m + 1))
  | 0 => by
    rw [show altList i j 0 = [] from rfl, gwp_nil, Matrix.one_mulVec, ← pairVec_single i j]
    simp [chebSeq]
  | m + 1 => by
    have ih := gwp_altList_mulVec_single M hij m
    have hsymm : -M.geometricForm j i = -M.geometricForm i j := by
      rw [M.geometricForm_isSymm.apply i j]
    rw [altList, gwp_cons, ← Matrix.mulVec_mulVec, ih]
    rcases Nat.mod_two_eq_zero_or_one m with hm | hm
    · have hm' : (m + 1) % 2 = 1 := by omega
      simp only [hm, hm', ite_true, one_ne_zero, ite_false]
      rw [geomRefl_j_pairVec M hij, hsymm]
      rfl
    · have hm' : (m + 1) % 2 = 0 := by omega
      simp only [hm, hm', ite_true, one_ne_zero, ite_false]
      rw [geomRefl_i_pairVec M hij]
      rfl

private lemma pow_mulVec_fixed (P : Matrix B B ℝ) (w : B → ℝ) (h : P *ᵥ w = w) :
    ∀ k : ℕ, P ^ k *ᵥ w = w
  | 0 => by simp
  | k + 1 => by rw [pow_succ, ← Matrix.mulVec_mulVec, h, pow_mulVec_fixed P w h k]

/-- For `i ≠ j` with `M i j ≠ 0`, `(sᵢ sⱼ) ^ M i j = 1`. -/
private lemma geometricReflection_mul_pow (M : CoxeterMatrix B) {i j : B} (hij : i ≠ j)
    (hM0 : M i j ≠ 0) :
    (M.geometricReflection i * M.geometricReflection j) ^ M i j = 1 := by
  set m := M i j with hm_def
  have hm : 2 ≤ m := by
    have h1 : m ≠ 1 := M.off_diagonal i j hij
    omega
  set c := 2 * Real.cos (Real.pi / m) with hc
  have hBij : M.geometricForm i j = -c := by
    rw [geometricForm_apply_of_ne_zero M hM0, ← hm_def, hc]; ring
  have hBji : M.geometricForm j i = -c := by
    rw [M.geometricForm_isSymm.apply i j, hBij]
  have hnegBij : -M.geometricForm i j = c := by rw [hBij, neg_neg]
  have hnegBji : -M.geometricForm j i = c := by rw [hBji, neg_neg]
  obtain ⟨t0, t1⟩ := chebSeq_cos_two_mul hm
  set P := M.geometricReflection i * M.geometricReflection j with hP
  set Q := M.geometricReflection j * M.geometricReflection i with hQ
  have hPi : P ^ m *ᵥ Pi.single i 1 = Pi.single i 1 := by
    have h := gwp_altList_mulVec_single M hij (2 * m)
    rw [gwp_altList_even, hnegBij] at h
    simp only [Nat.mul_mod_right, ite_true] at h
    rw [h, t0, t1, pairVec_single]
  have hQj : Q ^ m *ᵥ Pi.single j 1 = Pi.single j 1 := by
    have h := gwp_altList_mulVec_single M hij.symm (2 * m)
    rw [gwp_altList_even, hnegBji] at h
    simp only [Nat.mul_mod_right, ite_true] at h
    rw [h, t0, t1, pairVec_single]
  have hPQ : P * Q = 1 := by
    rw [hP, hQ, Matrix.mul_assoc, ← Matrix.mul_assoc (M.geometricReflection j),
      geometricReflection_mul_self, Matrix.one_mul, geometricReflection_mul_self]
  have hQP : Q * P = 1 := by
    rw [hP, hQ, Matrix.mul_assoc, ← Matrix.mul_assoc (M.geometricReflection i),
      geometricReflection_mul_self, Matrix.one_mul, geometricReflection_mul_self]
  have hPmQm : P ^ m * Q ^ m = 1 := by
    rw [← (show Commute P Q from hPQ.trans hQP.symm).mul_pow, hPQ, one_pow]
  have hPj : P ^ m *ᵥ Pi.single j 1 = Pi.single j 1 := by
    calc P ^ m *ᵥ Pi.single j 1 = P ^ m *ᵥ (Q ^ m *ᵥ Pi.single j 1) := by rw [hQj]
      _ = Pi.single j 1 := by rw [Matrix.mulVec_mulVec, hPmQm, Matrix.one_mulVec]
  have hfix : ∀ w : B → ℝ, (M.geometricForm *ᵥ w) i = 0 →
      (M.geometricForm *ᵥ w) j = 0 → P ^ m *ᵥ w = w := by
    intro w hwi hwj
    have hPw : P *ᵥ w = w := by
      rw [hP, ← Matrix.mulVec_mulVec, geomRefl_fix M j w hwj, geomRefl_fix M i w hwi]
    exact pow_mulVec_fixed P w hPw m
  have hden : 4 - c ^ 2 ≠ 0 := by
    have hs := sin_pi_div_pos hm
    have : 4 - c ^ 2 = 4 * Real.sin (Real.pi / m) ^ 2 := by rw [hc, Real.sin_sq]; ring
    rw [this]
    positivity
  have hall : ∀ v : B → ℝ, P ^ m *ᵥ v = v := by
    intro v
    set x := (M.geometricForm *ᵥ v) i
    set y := (M.geometricForm *ᵥ v) j
    set lam := (2 * x + c * y) / (4 - c ^ 2)
    set mu := (2 * y + c * x) / (4 - c ^ 2)
    set w := v - lam • Pi.single i 1 - mu • Pi.single j 1 with hw
    have hBe : ∀ a b : B, (M.geometricForm *ᵥ Pi.single b 1) a = M.geometricForm a b :=
      fun a b ↦ by rw [mulVec_single]
    have hwi : (M.geometricForm *ᵥ w) i = 0 := by
      rw [hw, Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hBe, geometricForm_diag, hBij,
        lam, mu, x, y]
      field_simp
      ring
    have hwj : (M.geometricForm *ᵥ w) j = 0 := by
      rw [hw, Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hBe, geometricForm_diag, hBji,
        lam, mu, x, y]
      field_simp
      ring
    have hv : v = w + lam • Pi.single i 1 + mu • Pi.single j 1 := by rw [hw]; abel
    rw [hv, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hfix w hwi hwj, hPi, hPj]
  ext r c'
  have := congrFun (hall (Pi.single c' 1)) r
  rw [mulVec_single] at this
  simp only [this, Pi.single_apply, Matrix.one_apply]

/-- The geometric reflections satisfy the Coxeter relations of `M`. -/
theorem geometricReflection_isLiftable (M : CoxeterMatrix B) :
    M.IsLiftable M.geometricReflection := by
  intro i j
  by_cases hij : i = j
  · subst hij
    simp [geometricReflection_mul_self]
  · by_cases hM0 : M i j = 0
    · simp [hM0]
    · exact geometricReflection_mul_pow M hij hM0

/-- The exact order of `sᵢ * sⱼ` in the geometric representation equals `M i j`. -/
theorem orderOf_geometricReflection_mul (M : CoxeterMatrix B) (i j : B) :
    orderOf (M.geometricReflection i * M.geometricReflection j) = M i j := by
  by_cases hij : i = j
  · subst hij
    simp [geometricReflection_mul_self]
  · by_cases hM0 : M i j = 0
    · rw [hM0]
      refine orderOf_eq_zero_iff'.mpr fun k hk hpow ↦ ?_
      have hv := gwp_altList_mulVec_single M hij (2 * k)
      rw [gwp_altList_even, hpow, Matrix.one_mulVec,
        geometricForm_apply_eq_neg_two M hM0] at hv
      simp only [Nat.mul_mod_right, ite_true, neg_neg] at hv
      have hcoord := congrFun hv i
      simp only [Pi.single_eq_same, pairVec, ite_true, hij, ite_false, add_zero] at hcoord
      have hge := chebSeq_ge 2 le_rfl (2 * k + 1)
      have hle : ((2 * k + 1 : ℕ) : ℝ) ≤ 1 := by linarith
      have hle' : 2 * k + 1 ≤ 1 := by exact_mod_cast hle
      omega
    · set m := M i j with hm_def
      have hm : 2 ≤ m := by
        have h1 : m ≠ 1 := M.off_diagonal i j hij
        omega
      have hpow_m : (M.geometricReflection i * M.geometricReflection j) ^ m = 1 :=
        geometricReflection_mul_pow M hij hM0
      have hdvd : orderOf (M.geometricReflection i * M.geometricReflection j) ∣ m :=
        orderOf_dvd_of_pow_eq_one hpow_m
      have hpos : 0 < orderOf (M.geometricReflection i * M.geometricReflection j) :=
        Nat.pos_of_dvd_of_pos hdvd (by omega)
      have hle : orderOf (M.geometricReflection i * M.geometricReflection j) ≤ m :=
        Nat.le_of_dvd (by omega) hdvd
      refine le_antisymm hle ?_
      by_contra hlt
      set k := orderOf (M.geometricReflection i * M.geometricReflection j)
      have hkm : k < m := Nat.lt_of_not_ge hlt
      have hpow_k : (M.geometricReflection i * M.geometricReflection j) ^ k = 1 :=
        pow_orderOf_eq_one _
      have hv := gwp_altList_mulVec_single M hij (2 * k)
      rw [gwp_altList_even, hpow_k, Matrix.one_mulVec,
        geometricForm_apply_of_ne_zero M hM0, ← hm_def] at hv
      simp only [Nat.mul_mod_right, ite_true, neg_mul, neg_neg] at hv
      have hs := sin_pi_div_pos hm
      have hm_pos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
      have hcj := congrFun hv j
      simp only [Pi.single_eq_of_ne (Ne.symm hij), pairVec, Ne.symm hij, ite_false, ite_true,
        zero_add] at hcj
      have hsin0 : Real.sin ((2 * k : ℕ) * (Real.pi / m)) = 0 := by
        rw [← chebSeq_mul_sin, ← hcj, zero_mul]
      rcases lt_trichotomy (2 * k) m with h2k | h2k | h2k
      · have hpos_ang : 0 < ((2 * k : ℕ) : ℝ) * (Real.pi / m) := by
          have : (0 : ℝ) < (2 * k : ℕ) := by exact_mod_cast (show 0 < 2 * k by omega)
          positivity
        have hlt_pi : ((2 * k : ℕ) : ℝ) * (Real.pi / m) < Real.pi := by
          have h2kr : ((2 * k : ℕ) : ℝ) < m := by exact_mod_cast h2k
          calc ((2 * k : ℕ) : ℝ) * (Real.pi / m) < m * (Real.pi / m) := by gcongr
            _ = Real.pi := by field_simp
        exact absurd hsin0 (Real.sin_pos_of_pos_of_lt_pi hpos_ang hlt_pi).ne'
      · have hci := congrFun hv i
        simp only [Pi.single_eq_same, pairVec, ite_true, hij, ite_false, add_zero] at hci
        have hsin1 := chebSeq_mul_sin (Real.pi / m) (2 * k + 1)
        rw [← hci, one_mul] at hsin1
        have hang : ((2 * k + 1 : ℕ) : ℝ) * (Real.pi / m) = Real.pi / m + Real.pi := by
          have h2kr : ((2 * k : ℕ) : ℝ) = m := by exact_mod_cast h2k
          push_cast at h2kr ⊢
          rw [show (2 : ℝ) * k + 1 = (m : ℝ) + 1 by linarith]
          field_simp
          ring
        rw [hang, Real.sin_add_pi] at hsin1
        linarith
      · have hpos_sub : 0 < ((2 * k : ℕ) : ℝ) * (Real.pi / m) - Real.pi := by
          have h2kr : (m : ℝ) < (2 * k : ℕ) := by exact_mod_cast h2k
          have : Real.pi < ((2 * k : ℕ) : ℝ) * (Real.pi / m) := by
            calc Real.pi = m * (Real.pi / m) := by field_simp
              _ < ((2 * k : ℕ) : ℝ) * (Real.pi / m) := by gcongr
          linarith
        have hlt_sub : ((2 * k : ℕ) : ℝ) * (Real.pi / m) - Real.pi < Real.pi := by
          have h2kr : ((2 * k : ℕ) : ℝ) < 2 * m := by
            exact_mod_cast (show 2 * k < 2 * m by omega)
          have : ((2 * k : ℕ) : ℝ) * (Real.pi / m) < 2 * Real.pi := by
            calc ((2 * k : ℕ) : ℝ) * (Real.pi / m) < (2 * m : ℝ) * (Real.pi / m) := by gcongr
              _ = 2 * Real.pi := by field_simp
          linarith
        have hneg : Real.sin (((2 * k : ℕ) : ℝ) * (Real.pi / m)) < 0 := by
          have heq : ((2 * k : ℕ) : ℝ) * (Real.pi / m) =
              (((2 * k : ℕ) : ℝ) * (Real.pi / m) - Real.pi) + Real.pi := by ring
          rw [heq, Real.sin_add_pi]
          linarith [Real.sin_pos_of_pos_of_lt_pi hpos_sub hlt_sub]
        exact absurd hsin0 hneg.ne

private lemma geomLen_altList_lt (M : CoxeterMatrix B) {i j : B} (hij : i ≠ j)
    (hM0 : M i j ≠ 0) {q : ℕ} (hq : M i j < q) :
    geomLen M (geomWordProd M (altList i j q)) < q := by
  have hbraid : geomWordProd M (altList i j (2 * M i j)) = 1 := by
    rw [gwp_altList_even]
    exact geometricReflection_mul_pow M hij hM0
  by_cases hq2 : q ≤ 2 * M i j
  · obtain ⟨Z, hZ, hsplit⟩ := altList_add i j q (2 * M i j - q)
    rw [show q + (2 * M i j - q) = 2 * M i j by omega] at hsplit
    have h1 : geomWordProd M Z * geomWordProd M (altList i j q) = 1 := by
      rw [← gwp_append, ← hsplit, hbraid]
    have h2 : geomWordProd M (altList i j q) = geomWordProd M Z.reverse := by
      calc geomWordProd M (altList i j q)
          = (geomWordProd M Z.reverse * geomWordProd M Z) * geomWordProd M (altList i j q) := by
            rw [gwp_reverse_mul, Matrix.one_mul]
        _ = geomWordProd M Z.reverse := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
    have := geomLen_le M Z.reverse
    rw [← h2, List.length_reverse, hZ] at this
    omega
  · obtain ⟨Z, hZ, hsplit⟩ := altList_add i j (2 * M i j) (q - 2 * M i j)
    rw [show 2 * M i j + (q - 2 * M i j) = q by omega] at hsplit
    have h2 : geomWordProd M (altList i j q) = geomWordProd M Z := by
      rw [hsplit, gwp_append, hbraid, Matrix.mul_one]
    have := geomLen_le M Z
    rw [← h2, hZ] at this
    omega

private lemma gwp_eq_altList (M : CoxeterMatrix B) {i j : B} (hij : i ≠ j) :
    ∀ u : List B, (∀ a ∈ u, a = i ∨ a = j) →
      geomLen M (geomWordProd M (u ++ [i])) = u.length + 1 →
      geomWordProd M u = geomWordProd M (altList i j u.length)
  | [], _, _ => rfl
  | a :: u', hu, hlen => by
    have hu' : ∀ b ∈ u', b = i ∨ b = j := fun b hb ↦ hu b (List.mem_cons_of_mem a hb)
    have hlen' : geomLen M (geomWordProd M (u' ++ [i])) = u'.length + 1 := by
      have h1 := geomLen_le M (u' ++ [i])
      have h2 := geomLen_append_le M [a] (u' ++ [i])
      have h3 := geomLen_singleton_le M a
      simp only [List.length_append, List.length_singleton] at h1
      simp only [List.singleton_append] at h2
      rw [List.cons_append, List.length_cons] at hlen
      omega
    have ih := gwp_eq_altList M hij u' hu' hlen'
    rw [List.length_cons, altList, gwp_cons, gwp_cons, ih]
    by_cases hax : a = (if u'.length % 2 = 0 then j else i)
    · rw [← hax]
    · exfalso
      rcases hk : u'.length with _ | k
      · rw [hk] at hax
        have hai : a = i := by
          rcases hu a List.mem_cons_self with h | h
          · exact h
          · simp only [Nat.zero_mod, ite_true] at hax
            exact absurd h hax
        have hu'nil : u' = [] := List.length_eq_zero_iff.mp hk
        subst hu'nil hai
        have e1 : geomWordProd M ([a] ++ [a]) = geomWordProd M [] := by
          simpa using gwp_append_self M [] a
        have := geomLen_le M ([] : List B)
        rw [← e1] at this
        simp only [List.length_nil] at this hlen
        omega
      · rw [hk] at hax ih
        have hy : a = (if k % 2 = 0 then j else i) := by
          rcases hu a List.mem_cons_self with h | h <;> subst h <;>
            split_ifs at hax ⊢ <;> first | rfl | exact absurd rfl hax | omega
        have e1 : geomWordProd M ((a :: u') ++ [i]) = geomWordProd M (altList i j k ++ [i]) := by
          rw [List.cons_append, gwp_cons, gwp_append, ih, altList, gwp_cons, ← hy,
            gwp_append, ← Matrix.mul_assoc, ← Matrix.mul_assoc, geometricReflection_mul_self,
            Matrix.one_mul]
        have := geomLen_le M (altList i j k ++ [i])
        rw [← e1] at this
        simp only [List.length_append, length_altList, List.length_singleton] at this
        rw [hlen, List.length_cons, hk] at this
        omega

private lemma rank_two_coeffs (M : CoxeterMatrix B) {i j : B} (hij : i ≠ j)
    (u : List B) (hu : ∀ a ∈ u, a = i ∨ a = j)
    (hlen : geomLen M (geomWordProd M (u ++ [i])) = u.length + 1) :
    ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧
      geomWordProd M u *ᵥ Pi.single i 1 = pairVec i j α β := by
  have halt := gwp_eq_altList M hij u hu hlen
  set p := u.length
  have hroot := gwp_altList_mulVec_single M hij p
  have hnn : 0 ≤ chebSeq (-M.geometricForm i j) p ∧
      0 ≤ chebSeq (-M.geometricForm i j) (p + 1) := by
    by_cases hM0 : M i j = 0
    · rw [geometricForm_apply_eq_neg_two M hM0, neg_neg]
      exact ⟨le_trans (Nat.cast_nonneg _) (chebSeq_ge 2 le_rfl p),
        le_trans (Nat.cast_nonneg _) (chebSeq_ge 2 le_rfl (p + 1))⟩
    · have hm : 2 ≤ M i j := by
        have h1 : M i j ≠ 1 := M.off_diagonal i j hij
        omega
      have hpm : p + 1 ≤ M i j := by
        by_contra hpm
        have hlt := geomLen_altList_lt M hij.symm (by rwa [M.symmetric j i])
          (show M j i < p + 1 by rw [M.symmetric j i]; omega)
        have e1 : geomWordProd M (u ++ [i]) = geomWordProd M (altList j i (p + 1)) := by
          rw [← altList_append, gwp_append, gwp_append, halt]
        rw [← e1, hlen] at hlt
        omega
      rw [geometricForm_apply_of_ne_zero M hM0]
      simp only [neg_mul, neg_neg]
      exact ⟨chebSeq_cos_nonneg hm (by omega), chebSeq_cos_nonneg hm hpm⟩
  rw [halt, hroot]
  split_ifs
  · exact ⟨_, _, hnn.2, hnn.1, rfl⟩
  · exact ⟨_, _, hnn.1, hnn.2, rfl⟩

private lemma nonneg_of_geomLen_lt (M : CoxeterMatrix B) :
    ∀ N : ℕ, ∀ w : List B, geomLen M (geomWordProd M w) = N → ∀ i : B,
      geomLen M (geomWordProd M w) < geomLen M (geomWordProd M (w ++ [i])) →
      ∀ r, 0 ≤ (geomWordProd M w *ᵥ Pi.single i 1) r := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro w hwN i hlt
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · have h1 : geomWordProd M w = 1 := gwp_eq_one_of_geomLen_eq_zero M w (hwN.trans h0)
    intro r
    rw [h1, Matrix.one_mulVec]
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  obtain ⟨v, hvlen, hvp⟩ := exists_word_geomLen M w
  have hne : v ≠ [] := by
    rintro rfl
    simp only [List.length_nil] at hvlen
    omega
  obtain ⟨v', j, rfl⟩ : ∃ v' j, v = v' ++ [j] :=
    ⟨v.dropLast, v.getLast hne, (List.dropLast_append_getLast hne).symm⟩
  simp only [List.length_append, List.length_singleton] at hvlen
  have hv'len : geomLen M (geomWordProd M v') = N - 1 := by
    have h1 := geomLen_le M v'
    have h2 := geomLen_append_le M v' [j]
    have h3 := geomLen_singleton_le M j
    rw [hvp] at h2
    omega
  have hji : j ≠ i := by
    rintro rfl
    have e1 : geomWordProd M (w ++ [j]) = geomWordProd M v' := by
      rw [gwp_append, ← hvp, ← gwp_append, gwp_append_self]
    rw [e1] at hlt
    omega
  classical
  let P : ℕ → Prop := fun k ↦ ∃ x u : List B, (∀ a ∈ u, a = i ∨ a = j) ∧
    geomWordProd M (x ++ u) = geomWordProd M w ∧ geomLen M (geomWordProd M x) = k ∧
    k + u.length = N
  have hP : ∃ k, P k := ⟨N - 1, v', [j], by simp, hvp, hv'len, by simp; omega⟩
  obtain ⟨x, u, hu, hxu, hxk, hkN⟩ := Nat.find_spec hP
  have hmin : ∀ k < Nat.find hP, ¬ P k := fun k hk ↦ Nat.find_min hP hk
  have hk0 : Nat.find hP ≤ N - 1 :=
    Nat.find_min' hP ⟨v', [j], by simp, hvp, hv'len, by simp; omega⟩
  set k0 := Nat.find hP
  have hxa : ∀ a, (a = i ∨ a = j) →
      geomLen M (geomWordProd M x) < geomLen M (geomWordProd M (x ++ [a])) := by
    intro a ha
    rcases geomLen_append_singleton M x a with h | h
    · omega
    · exfalso
      apply hmin (k0 - 1) (by omega)
      refine ⟨x ++ [a], a :: u, ?_, ?_, by omega, by simp; omega⟩
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ha
        · exact hu b hb
      · rw [← hxu, show x ++ [a] ++ a :: u = (x ++ [a] ++ [a]) ++ u by simp, gwp_append,
          gwp_append_self, ← gwp_append]
  have hxi := ih k0 (by omega) x hxk i (hxa i (Or.inl rfl))
  have hxj := ih k0 (by omega) x hxk j (hxa j (Or.inr rfl))
  have hwlen : geomLen M (geomWordProd M (x ++ u)) = N := by rw [hxu, hwN]
  have hulen : geomLen M (geomWordProd M u) = u.length := by
    have h1 := geomLen_le M u
    have h2 := geomLen_append_le M x u
    omega
  have hui : geomLen M (geomWordProd M (u ++ [i])) = u.length + 1 := by
    rcases geomLen_append_singleton M u i with h | h
    · omega
    · exfalso
      have h1 := geomLen_append_le M x (u ++ [i])
      have e1 : geomWordProd M (x ++ (u ++ [i])) = geomWordProd M (w ++ [i]) := by
        rw [← List.append_assoc, gwp_append, hxu, ← gwp_append]
      rw [e1] at h1
      omega
  obtain ⟨α, β, hα, hβ, hvec⟩ := rank_two_coeffs M hji.symm u hu hui
  intro r
  rw [← hxu, gwp_append, ← Matrix.mulVec_mulVec, hvec, pairVec_eq, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have := hxi r
  have := hxj r
  positivity

private lemma nonpos_of_geomLen_lt (M : CoxeterMatrix B) (w : List B) (i : B)
    (h : geomLen M (geomWordProd M (w ++ [i])) < geomLen M (geomWordProd M w)) :
    ∀ r, (geomWordProd M w *ᵥ Pi.single i 1) r ≤ 0 := by
  have h2 : geomLen M (geomWordProd M (w ++ [i])) <
      geomLen M (geomWordProd M (w ++ [i] ++ [i])) := by
    rw [gwp_append_self]
    exact h
  have hnn := nonneg_of_geomLen_lt M _ (w ++ [i]) rfl i h2
  intro r
  have := hnn r
  rw [gwp_append, gwp_singleton, ← Matrix.mulVec_mulVec, geomRefl_single_self,
    Matrix.mulVec_neg] at this
  simp only [Pi.neg_apply] at this
  linarith

private lemma root_nonneg_or_nonpos (M : CoxeterMatrix B) (w : List B) (i : B) :
    (∀ r, 0 ≤ (geomWordProd M w *ᵥ Pi.single i 1) r) ∨
      (∀ r, (geomWordProd M w *ᵥ Pi.single i 1) r ≤ 0) := by
  rcases geomLen_append_singleton M w i with h | h
  · exact Or.inl (nonneg_of_geomLen_lt M _ w rfl i (by omega))
  · exact Or.inr (nonpos_of_geomLen_lt M w i (by omega))

private lemma gwp_preserves_form (M : CoxeterMatrix B) (y : List B) :
    (geomWordProd M y)ᵀ * M.geometricForm * geomWordProd M y = M.geometricForm := by
  induction y with
  | nil => simp [gwp_nil]
  | cons a y ih =>
    rw [gwp_cons, Matrix.transpose_mul]
    calc (geomWordProd M y)ᵀ * (M.geometricReflection a)ᵀ * M.geometricForm *
          (M.geometricReflection a * geomWordProd M y)
        = (geomWordProd M y)ᵀ *
          ((M.geometricReflection a)ᵀ * M.geometricForm * M.geometricReflection a) *
          geomWordProd M y := by simp only [Matrix.mul_assoc]
      _ = M.geometricForm := by rw [geometricReflection_preserves_form, ih]

omit [DecidableEq B] in
private lemma dot_invariant (g A : Matrix B B ℝ) (x y : B → ℝ) :
    (g *ᵥ x) ⬝ᵥ (A *ᵥ (g *ᵥ y)) = x ⬝ᵥ ((gᵀ * A * g) *ᵥ y) := by
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
    Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mul_assoc]

private lemma dot_single (v : B → ℝ) (a : B) : Pi.single a 1 ⬝ᵥ v = v a := by
  simp [dotProduct, Pi.single_apply]

private lemma conj_of_root_eq (M : CoxeterMatrix B) (y : List B) (a b : B) (lam : ℝ)
    (hroot : geomWordProd M y *ᵥ Pi.single b 1 = lam • Pi.single a 1) :
    geomWordProd M y * M.geometricReflection b = M.geometricReflection a * geomWordProd M y := by
  set g := geomWordProd M y with hg
  have hinv := gwp_preserves_form M y
  rw [← hg] at hinv
  have hlam : lam * lam = 1 := by
    have h := dot_invariant g M.geometricForm (Pi.single b 1) (Pi.single b 1)
    rw [hinv, hroot, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, dot_single, dot_single,
      mulVec_single, mulVec_single] at h
    simp only [smul_eq_mul, geometricForm_diag] at h
    linarith
  have hkey : ∀ v : B → ℝ,
      (M.geometricForm *ᵥ (g *ᵥ v)) a = lam * (M.geometricForm *ᵥ v) b := by
    intro v
    have h := dot_invariant g M.geometricForm (Pi.single b 1) v
    rw [hinv, hroot, smul_dotProduct, dot_single, dot_single, smul_eq_mul] at h
    calc (M.geometricForm *ᵥ (g *ᵥ v)) a
        = (lam * lam) * (M.geometricForm *ᵥ (g *ᵥ v)) a := by rw [hlam, one_mul]
      _ = lam * (M.geometricForm *ᵥ v) b := by rw [mul_assoc, h]
  have hall : ∀ v,
      (g * M.geometricReflection b) *ᵥ v = (M.geometricReflection a * g) *ᵥ v := by
    intro v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, geomRefl_mulVec, geomRefl_mulVec,
      Matrix.mulVec_sub, Matrix.mulVec_smul, hroot, hkey, smul_smul, mul_comm lam]
  ext r c
  have := hall (Pi.single c 1)
  rw [mulVec_single, mulVec_single] at this
  exact congrFun this r

private lemma root_eq_smul (M : CoxeterMatrix B) (y : List B) (s a : B)
    (hv : ∀ r, 0 ≤ (geomWordProd M y *ᵥ Pi.single s 1) r)
    (hav : ¬ ∀ r, 0 ≤ (geomWordProd M (a :: y) *ᵥ Pi.single s 1) r) :
    geomWordProd M y *ᵥ Pi.single s 1 =
      (geomWordProd M y *ᵥ Pi.single s 1) a • Pi.single a 1 := by
  have hneg : ∀ r, (geomWordProd M (a :: y) *ᵥ Pi.single s 1) r ≤ 0 :=
    (root_nonneg_or_nonpos M (a :: y) s).resolve_left hav
  funext r
  by_cases hr : r = a
  · subst hr; simp
  · have h1 := hneg r
    rw [gwp_cons, ← Matrix.mulVec_mulVec, geomRefl_mulVec] at h1
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, hr,
      ite_false, mul_zero, sub_zero] at h1
    have h2 := hv r
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, hr, ite_false, mul_zero]
    linarith

/-- The geometric reflection matrices satisfy the Exchange Property. -/
theorem geometricReflection_hasExchangeProperty (M : CoxeterMatrix B) :
    CoxeterSystem.HasExchangeProperty M.geometricReflection := by
  intro s w hw ⟨u, hu, hsu⟩
  have hwl := geomLen_of_isReducedWord M hw
  have hsl : geomLen M (geomWordProd M (s :: w)) < w.length := by
    have h1 := geomLen_le M u
    change geomWordProd M (s :: w) = geomWordProd M u at hsu
    rw [← hsu] at h1
    have h2 := geomLen_ne_of_det_neg M (det_cons M w s)
    have h3 := geomLen_cons M w s
    simp only [List.length_cons] at hu
    omega
  have hrev : geomLen M (geomWordProd M (w.reverse ++ [s])) <
      geomLen M (geomWordProd M w.reverse) := by
    rw [← List.reverse_cons, geomLen_reverse, geomLen_reverse, hwl]
    exact hsl
  have hneg := nonpos_of_geomLen_lt M w.reverse s hrev
  have hne := gwp_mulVec_single_ne_zero M w.reverse s
  classical
  let X : ℕ → Prop := fun t ↦
    ¬ ∀ r, 0 ≤ (geomWordProd M (w.take t).reverse *ᵥ Pi.single s 1) r
  have hX : ∃ t, X t := by
    refine ⟨w.length, fun h ↦ hne ?_⟩
    rw [List.take_length] at h
    funext r
    exact le_antisymm (hneg r) (h r)
  have ht1pos : Nat.find hX ≠ 0 := by
    intro h0
    have := Nat.find_spec hX
    rw [h0] at this
    apply this
    intro r
    simp only [List.take_zero, List.reverse_nil, gwp_nil, Matrix.one_mulVec, Pi.single_apply]
    split_ifs <;> norm_num
  obtain ⟨t, ht1⟩ : ∃ t, Nat.find hX = t + 1 := ⟨Nat.find hX - 1, by omega⟩
  have hXt1 : X (t + 1) := ht1 ▸ Nat.find_spec hX
  have hXt : ¬ X t := Nat.find_min hX (by omega)
  have ht : t < w.length := by
    by_contra htl
    apply hXt
    have e1 : w.take (t + 1) = w.take t := by
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
    change ¬ ∀ r, 0 ≤ (geomWordProd M (w.take t).reverse *ᵥ Pi.single s 1) r
    rw [← e1]
    exact hXt1
  set P := w.take t with hPdef
  set a := w[t] with hadef
  set R := w.drop (t + 1) with hRdef
  have hw_eq : w = P ++ a :: R := by
    rw [hPdef, hadef, hRdef, ← List.drop_eq_getElem_cons ht, List.take_append_drop]
  have herase : w.eraseIdx t = P ++ R := by rw [List.eraseIdx_eq_take_drop_succ]
  have htake : (w.take (t + 1)).reverse = a :: P.reverse := by
    rw [List.take_add_one, List.getElem?_eq_getElem ht]
    simp [hPdef, hadef]
  have hXt' : ∀ r, 0 ≤ (geomWordProd M P.reverse *ᵥ Pi.single s 1) r := by
    by_contra h
    exact hXt h
  have hXt1' : ¬ ∀ r, 0 ≤ (geomWordProd M (a :: P.reverse) *ᵥ Pi.single s 1) r := by
    rw [← htake]
    exact hXt1
  have hroot := root_eq_smul M P.reverse s a hXt' hXt1'
  have hconj := conj_of_root_eq M P.reverse a s _ hroot
  have hsP : M.geometricReflection s * geomWordProd M P =
      geomWordProd M P * M.geometricReflection a := by
    calc M.geometricReflection s * geomWordProd M P
        = (geomWordProd M P * geomWordProd M P.reverse) *
          M.geometricReflection s * geomWordProd M P := by rw [gwp_mul_reverse, Matrix.one_mul]
      _ = geomWordProd M P * (geomWordProd M P.reverse * M.geometricReflection s) *
          geomWordProd M P := by simp only [Matrix.mul_assoc]
      _ = geomWordProd M P * (M.geometricReflection a * geomWordProd M P.reverse) *
          geomWordProd M P := by rw [hconj]
      _ = geomWordProd M P * M.geometricReflection a := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, gwp_reverse_mul, Matrix.mul_one]
  refine ⟨t, ht, ?_⟩
  change geomWordProd M (s :: w) = geomWordProd M (w.eraseIdx t)
  rw [herase]
  conv_lhs => rw [hw_eq]
  rw [gwp_cons, gwp_append, gwp_cons, gwp_append, ← Matrix.mul_assoc, hsP, Matrix.mul_assoc,
    ← Matrix.mul_assoc (M.geometricReflection a), geometricReflection_mul_self, Matrix.one_mul]

/-- The geometric reflection matrices satisfy the Deletion Property. -/
theorem geometricReflection_hasDeletionProperty (M : CoxeterMatrix B) :
    CoxeterSystem.HasDeletionProperty M.geometricReflection :=
  CoxeterSystem.hasDeletionProperty_of_hasExchangeProperty
    M.geometricReflection_hasExchangeProperty

/-! ### Faithfulness of the geometric representation -/

/-- The canonical geometric representation `M.Group →* Matrix B B ℝ` sending each simple
reflection `i` to `M.geometricReflection i`. -/
noncomputable def geometricRep (M : CoxeterMatrix B) : M.Group →* Matrix B B ℝ :=
  M.toCoxeterSystem.lift ⟨M.geometricReflection, M.geometricReflection_isLiftable⟩

@[simp]
theorem geometricRep_simple (M : CoxeterMatrix B) (i : B) :
    M.geometricRep (M.simple i) = M.geometricReflection i :=
  M.toCoxeterSystem.lift_apply_simple M.geometricReflection_isLiftable i

theorem geometricRep_wordProd (M : CoxeterMatrix B) (w : List B) :
    M.geometricRep (M.toCoxeterSystem.wordProd w) = (w.map M.geometricReflection).prod := by
  induction w with
  | nil => simp [CoxeterSystem.wordProd]
  | cons a t ih =>
    rw [CoxeterSystem.wordProd_cons, map_mul, ih, List.map_cons, List.prod_cons]
    exact congrArg (· * (t.map M.geometricReflection).prod) (M.geometricRep_simple a)

/-- **Faithfulness of the Tits geometric representation**:
`M.geometricRep : M.Group →* Matrix B B ℝ` is injective. -/
theorem geometricRep_injective (M : CoxeterMatrix B) : Function.Injective M.geometricRep := by
  intro x y hxy
  obtain ⟨ω, hω⟩ := M.toCoxeterSystem.wordProd_surjective (x⁻¹ * y)
  have h1 : (ω.map M.geometricReflection).prod = 1 := by
    rw [← M.geometricRep_wordProd, hω, map_mul, ← hxy, ← map_mul, inv_mul_cancel, map_one]
  have hbraid := CoxeterSystem.wordProd_alternatingWord_eq_of_orderOf
    M.geometricReflection_mul_self M.orderOf_geometricReflection_mul
  have hnil : CoxeterSystem.IsReducedWord M.geometricReflection [] :=
    fun _ hu ↦ absurd hu (by simp)
  have h2 := CoxeterSystem.wordProd_eq_of_isReducedWord M.geometricReflection_mul_self
    M.geometricReflection_hasExchangeProperty hbraid ω [] hnil (by simpa using h1)
  simp only [CoxeterSystem.wordProd_nil] at h2
  rw [hω] at h2
  exact inv_mul_eq_one.1 h2

end RootPositivity

end CoxeterMatrix

/-! ### Corollaries for `CoxeterSystem M W` -/

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B}

section GeometricRep

variable [Fintype B] [DecidableEq B]

/-- The geometric representation `W →* Matrix B B ℝ` of a finite-rank `CoxeterSystem M W`. -/
noncomputable def geometricRep (cs : CoxeterSystem M W) : W →* Matrix B B ℝ :=
  cs.lift ⟨M.geometricReflection, M.geometricReflection_isLiftable⟩

@[simp]
theorem geometricRep_simple (cs : CoxeterSystem M W) (i : B) :
    cs.geometricRep (cs.simple i) = M.geometricReflection i :=
  cs.lift_apply_simple M.geometricReflection_isLiftable i

theorem geometricRep_eq_comp (cs : CoxeterSystem M W) :
    cs.geometricRep = M.geometricRep.comp cs.mulEquiv.toMonoidHom := by
  apply cs.ext_simple
  intro i
  simp

theorem geometricRep_wordProd (cs : CoxeterSystem M W) (w : List B) :
    cs.geometricRep (cs.wordProd w) = (w.map M.geometricReflection).prod := by
  induction w with
  | nil => simp [CoxeterSystem.wordProd]
  | cons a t ih =>
    rw [cs.wordProd_cons, map_mul, ih, List.map_cons, List.prod_cons, cs.geometricRep_simple]

/-- **Faithfulness of the geometric representation** for any finite-rank `CoxeterSystem M W`. -/
theorem geometricRep_injective (cs : CoxeterSystem M W) : Function.Injective cs.geometricRep := by
  rw [cs.geometricRep_eq_comp]
  exact M.geometricRep_injective.comp cs.mulEquiv.injective

private lemma geomLen_geometricRep_eq_length (cs : CoxeterSystem M W) (w : W) :
    CoxeterMatrix.geomLen M (cs.geometricRep w) = cs.length w := by
  obtain ⟨u, hu_red, hu_eq⟩ := cs.exists_isReduced w
  have h1 : CoxeterMatrix.geomLen M (cs.geometricRep w) ≤ cs.length w := by
    rw [hu_eq, hu_red, cs.geometricRep_wordProd]
    exact CoxeterMatrix.geomLen_le M u
  obtain ⟨v, hv_len, hv_eq⟩ := CoxeterMatrix.exists_word_geomLen M u
  have hv_prod : cs.wordProd v = w := cs.geometricRep_injective (by
    rw [cs.geometricRep_wordProd, hu_eq, cs.geometricRep_wordProd]
    exact hv_eq)
  have h2 : cs.length w ≤ CoxeterMatrix.geomLen M (cs.geometricRep w) := by
    calc cs.length w = cs.length (cs.wordProd v) := by rw [hv_prod]
      _ ≤ v.length := cs.length_wordProd_le v
      _ = CoxeterMatrix.geomLen M (cs.geometricRep w) := by
        rw [hv_len, hu_eq, cs.geometricRep_wordProd]
  exact le_antisymm h1 h2

/-- **Root positivity (Humphreys, Theorem 5.4)**: for any `w ∈ W` and simple reflection `i`,
the root `w(eᵢ)` has nonnegative coordinates if and only if `ℓ(w sᵢ) > ℓ(w)`. -/
theorem geometricRep_mulVec_single_nonneg_iff (cs : CoxeterSystem M W) (w : W) (i : B) :
    (∀ r, 0 ≤ (cs.geometricRep w *ᵥ Pi.single i 1) r) ↔
      cs.length w < cs.length (w * cs.simple i) := by
  obtain ⟨ω, rfl⟩ := cs.wordProd_surjective w
  have hlen : CoxeterMatrix.geomLen M (CoxeterMatrix.geomWordProd M ω) =
      cs.length (cs.wordProd ω) := by
    dsimp only [CoxeterMatrix.geomWordProd]
    rw [← cs.geometricRep_wordProd, cs.geomLen_geometricRep_eq_length]
  have hlen' : CoxeterMatrix.geomLen M (CoxeterMatrix.geomWordProd M (ω ++ [i])) =
      cs.length (cs.wordProd ω * cs.simple i) := by
    dsimp only [CoxeterMatrix.geomWordProd]
    rw [← cs.geometricRep_wordProd, cs.wordProd_append, cs.wordProd_singleton,
      cs.geomLen_geometricRep_eq_length]
  rw [cs.geometricRep_wordProd, ← hlen, ← hlen']
  constructor
  · intro hpos
    by_contra hle
    have hlt : CoxeterMatrix.geomLen M (CoxeterMatrix.geomWordProd M (ω ++ [i])) <
        CoxeterMatrix.geomLen M (CoxeterMatrix.geomWordProd M ω) := by
      rcases CoxeterMatrix.geomLen_append_singleton M ω i with h | h <;> omega
    apply CoxeterMatrix.gwp_mulVec_single_ne_zero M ω i
    funext r
    exact le_antisymm (CoxeterMatrix.nonpos_of_geomLen_lt M ω i hlt r) (hpos r)
  · exact fun h ↦ CoxeterMatrix.nonneg_of_geomLen_lt M _ ω rfl i h

/-- **Root partition (`Φ = Φ⁺ ⊔ -Φ⁺`)**: every root `w(eᵢ)` has either all coordinates
nonnegative or all coordinates nonpositive. -/
theorem geometricRep_mulVec_single_nonneg_or_nonpos (cs : CoxeterSystem M W) (w : W) (i : B) :
    (∀ r, 0 ≤ (cs.geometricRep w *ᵥ Pi.single i 1) r) ∨
      (∀ r, (cs.geometricRep w *ᵥ Pi.single i 1) r ≤ 0) := by
  obtain ⟨ω, rfl⟩ := cs.wordProd_surjective w
  rw [cs.geometricRep_wordProd]
  exact CoxeterMatrix.root_nonneg_or_nonpos M ω i

end GeometricRep

/-- The simple reflections of a finite-rank `CoxeterSystem` are pairwise distinct. -/
theorem simple_injective [Finite B] (cs : CoxeterSystem M W) : Function.Injective cs.simple := by
  classical
  have := Fintype.ofFinite B
  intro i j h
  exact M.geometricReflection_injective (by simpa using congrArg cs.geometricRep h)

/-- In any finite-rank `CoxeterSystem`, the exact order of `cs.simple i * cs.simple j` is
`M i j`. -/
theorem orderOf_simple_mul_simple [Finite B] (cs : CoxeterSystem M W) (i j : B) :
    orderOf (cs.simple i * cs.simple j) = M i j := by
  classical
  have := Fintype.ofFinite B
  rw [← orderOf_injective cs.geometricRep cs.geometricRep_injective, map_mul,
    cs.geometricRep_simple, cs.geometricRep_simple, M.orderOf_geometricReflection_mul]

end CoxeterSystem
