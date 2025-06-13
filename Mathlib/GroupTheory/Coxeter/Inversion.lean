/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee, Óscar Álvarez
-/
import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Group

/-!
# Reflections, inversions, and inversion sequences

Throughout this file, `B` is a type and `M : CoxeterMatrix B` is a Coxeter matrix.
`cs : CoxeterSystem M W` is a Coxeter system; that is, `W` is a group, and `cs` holds the data
of a group isomorphism `W ≃* M.group`, where `M.group` refers to the quotient of the free group on
`B` by the Coxeter relations given by the matrix `M`. See `Mathlib/GroupTheory/Coxeter/Basic.lean`
for more details.

We define a *reflection* (`CoxeterSystem.IsReflection`) to be an element of the form
$t = u s_i u^{-1}$, where $u \in W$ and $s_i$ is a simple reflection. We say that a reflection $t$
is a *left inversion* (`CoxeterSystem.IsLeftInversion`) of an element $w \in W$ if
$\ell(t w) < \ell(w)$, and we say it is a *right inversion* (`CoxeterSystem.IsRightInversion`) of
$w$ if $\ell(w t) > \ell(w)$. Here $\ell$ is the length function
(see `Mathlib/GroupTheory/Coxeter/Length.lean`).

Given a word, we define its *left inversion sequence* (`CoxeterSystem.leftInvSeq`) and its
*right inversion sequence* (`CoxeterSystem.rightInvSeq`). We prove that if a word is reduced, then
both of its inversion sequences contain no duplicates. In fact, the right (respectively, left)
inversion sequence of a reduced word for $w$ consists of all of the right (respectively, left)
inversions of $w$ in some order, but we do not prove that in this file.

## Main definitions

* `CoxeterSystem.IsReflection`
* `CoxeterSystem.IsLeftInversion`
* `CoxeterSystem.IsRightInversion`
* `CoxeterSystem.leftInvSeq`
* `CoxeterSystem.rightInvSeq`

## References

* [A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*](bjorner2005)

-/

assert_not_exists TwoSidedIdeal

namespace CoxeterSystem

open List Matrix Function

variable {B : Type*}
variable {W : Type*} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length

/-- `t : W` is a *reflection* of the Coxeter system `cs` if it is of the form
$w s_i w^{-1}$, where $w \in W$ and $s_i$ is a simple reflection. -/
def IsReflection (t : W) : Prop := ∃ w i, t = w * s i * w⁻¹

theorem isReflection_simple (i : B) : cs.IsReflection (s i) := by use 1, i; simp

namespace IsReflection

variable {cs}
variable {t : W} (ht : cs.IsReflection t)
include ht

theorem pow_two : t ^ 2 = 1 := by
  rcases ht with ⟨w, i, rfl⟩
  simp

theorem mul_self : t * t = 1 := by
  rcases ht with ⟨w, i, rfl⟩
  simp

theorem inv : t⁻¹ = t := by
  rcases ht with ⟨w, i, rfl⟩
  simp [mul_assoc]

theorem isReflection_inv : cs.IsReflection t⁻¹ := by rwa [ht.inv]

theorem odd_length : Odd (ℓ t) := by
  suffices cs.lengthParity t = Multiplicative.ofAdd 1 by
    simpa [lengthParity_eq_ofAdd_length, ZMod.eq_one_iff_odd]
  rcases ht with ⟨w, i, rfl⟩
  simp [lengthParity_simple]

theorem length_mul_left_ne (w : W) : ℓ (w * t) ≠ ℓ w := by
  suffices cs.lengthParity (w * t) ≠ cs.lengthParity w by
    contrapose! this
    simp only [lengthParity_eq_ofAdd_length, this]
  rcases ht with ⟨w, i, rfl⟩
  simp [lengthParity_simple]

theorem length_mul_right_ne (w : W) : ℓ (t * w) ≠ ℓ w := by
  suffices cs.lengthParity (t * w) ≠ cs.lengthParity w by
    contrapose! this
    simp only [lengthParity_eq_ofAdd_length, this]
  rcases ht with ⟨w, i, rfl⟩
  simp [lengthParity_simple]

theorem conj (w : W) : cs.IsReflection (w * t * w⁻¹) := by
  obtain ⟨u, i, rfl⟩ := ht
  use w * u, i
  group

end IsReflection

@[simp]
theorem isReflection_conj_iff (w t : W) :
    cs.IsReflection (w * t * w⁻¹) ↔ cs.IsReflection t := by
  constructor
  · intro h
    simpa [← mul_assoc] using h.conj w⁻¹
  · exact IsReflection.conj (w := w)

/-- The proposition that `t` is a right inversion of `w`; i.e., `t` is a reflection and
$\ell (w t) < \ell(w)$. -/
def IsRightInversion (w t : W) : Prop := cs.IsReflection t ∧ ℓ (w * t) < ℓ w

/-- The proposition that `t` is a left inversion of `w`; i.e., `t` is a reflection and
$\ell (t w) < \ell(w)$. -/
def IsLeftInversion (w t : W) : Prop := cs.IsReflection t ∧ ℓ (t * w) < ℓ w

theorem isRightInversion_inv_iff {w t : W} :
    cs.IsRightInversion w⁻¹ t ↔ cs.IsLeftInversion w t := by
  apply and_congr_right
  intro ht
  rw [← length_inv, mul_inv_rev, inv_inv, ht.inv, cs.length_inv w]

theorem isLeftInversion_inv_iff {w t : W} :
    cs.IsLeftInversion w⁻¹ t ↔ cs.IsRightInversion w t := by
  convert cs.isRightInversion_inv_iff.symm
  simp

namespace IsReflection

variable {cs}
variable {t : W} (ht : cs.IsReflection t)
include ht

theorem isRightInversion_mul_left_iff {w : W} :
    cs.IsRightInversion (w * t) t ↔ ¬cs.IsRightInversion w t := by
  unfold IsRightInversion
  simp only [mul_assoc, ht.inv, ht.mul_self, mul_one, ht, true_and, not_lt]
  constructor
  · exact le_of_lt
  · exact (lt_of_le_of_ne' · (ht.length_mul_left_ne w))

theorem not_isRightInversion_mul_left_iff {w : W} :
    ¬cs.IsRightInversion (w * t) t ↔ cs.IsRightInversion w t :=
  ht.isRightInversion_mul_left_iff.not_left

theorem isLeftInversion_mul_right_iff {w : W} :
    cs.IsLeftInversion (t * w) t ↔ ¬cs.IsLeftInversion w t := by
  rw [← isRightInversion_inv_iff, ← isRightInversion_inv_iff, mul_inv_rev, ht.inv,
    ht.isRightInversion_mul_left_iff]

theorem not_isLeftInversion_mul_right_iff {w : W} :
    ¬cs.IsLeftInversion (t * w) t ↔ cs.IsLeftInversion w t :=
  ht.isLeftInversion_mul_right_iff.not_left

end IsReflection

@[simp]
theorem isRightInversion_simple_iff_isRightDescent (w : W) (i : B) :
    cs.IsRightInversion w (s i) ↔ cs.IsRightDescent w i := by
  simp [IsRightInversion, IsRightDescent, cs.isReflection_simple i]

@[simp]
theorem isLeftInversion_simple_iff_isLeftDescent (w : W) (i : B) :
    cs.IsLeftInversion w (s i) ↔ cs.IsLeftDescent w i := by
  simp [IsLeftInversion, IsLeftDescent, cs.isReflection_simple i]

/-- The right inversion sequence of `ω`. The right inversion sequence of a word
$s_{i_1} \cdots s_{i_\ell}$ is the sequence
$$s_{i_\ell}\cdots s_{i_1}\cdots s_{i_\ell}, \ldots,
    s_{i_{\ell}}s_{i_{\ell - 1}}s_{i_{\ell - 2}}s_{i_{\ell - 1}}s_{i_\ell}, \ldots,
    s_{i_{\ell}}s_{i_{\ell - 1}}s_{i_\ell}, s_{i_\ell}.$$
-/
def rightInvSeq (ω : List B) : List W :=
  match ω with
  | []          => []
  | i :: ω      => (π ω)⁻¹ * (s i) * (π ω) :: rightInvSeq ω

/-- The left inversion sequence of `ω`. The left inversion sequence of a word
$s_{i_1} \cdots s_{i_\ell}$ is the sequence
$$s_{i_1}, s_{i_1}s_{i_2}s_{i_1}, s_{i_1}s_{i_2}s_{i_3}s_{i_2}s_{i_1}, \ldots,
    s_{i_1}\cdots s_{i_\ell}\cdots s_{i_1}.$$
-/
def leftInvSeq (ω : List B) : List W :=
  match ω with
  | []          => []
  | i :: ω      => s i :: List.map (MulAut.conj (s i)) (leftInvSeq ω)

local prefix:100 "ris" => cs.rightInvSeq
local prefix:100 "lis" => cs.leftInvSeq

@[simp] theorem rightInvSeq_nil : ris [] = [] := rfl

@[simp] theorem leftInvSeq_nil : lis [] = [] := rfl

@[simp] theorem rightInvSeq_singleton (i : B) : ris [i] = [s i] := by simp [rightInvSeq]

@[simp] theorem leftInvSeq_singleton (i : B) : lis [i] = [s i] := rfl

theorem rightInvSeq_concat (ω : List B) (i : B) :
    ris (ω.concat i) = (List.map (MulAut.conj (s i)) (ris ω)).concat (s i) := by
  induction ω with
  | nil => simp
  | cons j ω ih =>
    dsimp [rightInvSeq, concat]
    rw [ih]
    simp only [concat_eq_append, wordProd_append, wordProd_cons, wordProd_nil, mul_one, mul_inv_rev,
      inv_simple, cons_append, cons.injEq, and_true]
    group

private theorem leftInvSeq_eq_reverse_rightInvSeq_reverse (ω : List B) :
    lis ω = (ris ω.reverse).reverse := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [leftInvSeq, reverse_cons, ← concat_eq_append, rightInvSeq_concat, ih]
    simp [map_reverse]

theorem leftInvSeq_concat (ω : List B) (i : B) :
    lis (ω.concat i) = (lis ω).concat ((π ω) * (s i) * (π ω)⁻¹) := by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse, rightInvSeq]

theorem rightInvSeq_reverse (ω : List B) :
    ris (ω.reverse) = (lis ω).reverse := by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse]

theorem leftInvSeq_reverse (ω : List B) :
    lis (ω.reverse) = (ris ω).reverse := by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse]

@[simp] theorem length_rightInvSeq (ω : List B) : (ris ω).length = ω.length := by
  induction ω with
  | nil => simp
  | cons i ω ih => simpa [rightInvSeq]

@[simp] theorem length_leftInvSeq (ω : List B) : (lis ω).length = ω.length := by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse]

theorem getD_rightInvSeq (ω : List B) (j : ℕ) :
    (ris ω).getD j 1 =
      (π (ω.drop (j + 1)))⁻¹
        * (Option.map (cs.simple) ω[j]?).getD 1
        * π (ω.drop (j + 1)) := by
  induction ω generalizing j with
  | nil => simp
  | cons i ω ih =>
    dsimp only [rightInvSeq]
    rcases j with _ | j'
    · simp [getD_cons_zero]
    · simp only [getD_eq_getElem?_getD] at ih
      simp [getD_cons_succ, ih j']

lemma getElem_rightInvSeq (ω : List B) (j : ℕ) (h : j < ω.length) :
    (ris ω)[j]'(by simp[h]) =
    (π (ω.drop (j + 1)))⁻¹
      * (Option.map (cs.simple) ω[j]?).getD 1
      * π (ω.drop (j + 1)) := by
  rw [← List.getD_eq_getElem (ris ω) 1, getD_rightInvSeq]

theorem getD_leftInvSeq (ω : List B) (j : ℕ) :
    (lis ω).getD j 1 =
      π (ω.take j)
        * (Option.map (cs.simple) ω[j]?).getD 1
        * (π (ω.take j))⁻¹ := by
  induction ω generalizing j with
  | nil => simp
  | cons i ω ih =>
    dsimp [leftInvSeq]
    rcases j with _ | j'
    · simp [getD_cons_zero]
    · rw [getD_cons_succ]
      rw [(by simp : 1 = ⇑(MulAut.conj (s i)) 1)]
      rw [getD_map]
      rw [ih j']
      simp [← mul_assoc, wordProd_cons]

lemma getElem_leftInvSeq (ω : List B) (j : ℕ) (h : j < ω.length) :
    (lis ω)[j]'(by simp[h]) =
    cs.wordProd (List.take j ω) * s ω[j] * (cs.wordProd (List.take j ω))⁻¹ := by
  rw [← List.getD_eq_getElem (lis ω) 1, getD_leftInvSeq]
  simp [h]

theorem getD_rightInvSeq_mul_self (ω : List B) (j : ℕ) :
    ((ris ω).getD j 1) * ((ris ω).getD j 1) = 1 := by
  simp_rw [getD_rightInvSeq, mul_assoc]
  rcases em (j < ω.length) with hj | nhj
  · rw [getElem?_eq_getElem hj]
    simp [← mul_assoc]
  · rw [getElem?_eq_none_iff.mpr (by omega)]
    simp

theorem getD_leftInvSeq_mul_self (ω : List B) (j : ℕ) :
    ((lis ω).getD j 1) * ((lis ω).getD j 1) = 1 := by
  simp_rw [getD_leftInvSeq, mul_assoc]
  rcases em (j < ω.length) with hj | nhj
  · rw [getElem?_eq_getElem hj]
    simp [← mul_assoc]
  · rw [getElem?_eq_none_iff.mpr (by omega)]
    simp

theorem rightInvSeq_drop (ω : List B) (j : ℕ) :
    ris (ω.drop j) = (ris ω).drop j := by
  induction j generalizing ω with
  | zero => simp
  | succ j ih₁ =>
    induction ω with
    | nil => simp
    | cons k ω _ => rw [drop_succ_cons, ih₁ ω, rightInvSeq, drop_succ_cons]

theorem leftInvSeq_take (ω : List B) (j : ℕ) :
    lis (ω.take j) = (lis ω).take j := by
  simp only [leftInvSeq_eq_reverse_rightInvSeq_reverse]
  rw [List.take_reverse]
  nth_rw 1 [← List.reverse_reverse ω]
  rw [List.take_reverse]
  simp [rightInvSeq_drop]

theorem isReflection_of_mem_rightInvSeq (ω : List B) {t : W} (ht : t ∈ ris ω) :
    cs.IsReflection t := by
  induction ω with
  | nil => simp at ht
  | cons i ω ih =>
    dsimp [rightInvSeq] at ht
    rcases ht with _ | ⟨_, mem⟩
    · use (π ω)⁻¹, i
      group
    · exact ih mem

theorem isReflection_of_mem_leftInvSeq (ω : List B) {t : W} (ht : t ∈ lis ω) :
    cs.IsReflection t := by
  simp only [leftInvSeq_eq_reverse_rightInvSeq_reverse, mem_reverse] at ht
  exact cs.isReflection_of_mem_rightInvSeq ω.reverse ht

theorem wordProd_mul_getD_rightInvSeq (ω : List B) (j : ℕ) :
    π ω * ((ris ω).getD j 1) = π (ω.eraseIdx j) := by
  rw [getD_rightInvSeq, eraseIdx_eq_take_drop_succ]
  nth_rw 1 [← take_append_drop (j + 1) ω]
  rw [take_succ]
  obtain lt | le := lt_or_ge j ω.length
  · simp only [getElem?_eq_getElem lt, wordProd_append, wordProd_cons, mul_assoc]
    simp
  · simp only [getElem?_eq_none le]
    simp

theorem getD_leftInvSeq_mul_wordProd (ω : List B) (j : ℕ) :
    ((lis ω).getD j 1) * π ω = π (ω.eraseIdx j) := by
  rw [getD_leftInvSeq, eraseIdx_eq_take_drop_succ]
  nth_rw 4 [← take_append_drop (j + 1) ω]
  rw [take_succ]
  obtain lt | le := lt_or_ge j ω.length
  · simp only [getElem?_eq_getElem lt, wordProd_append, wordProd_cons, mul_assoc]
    simp
  · simp only [getElem?_eq_none le]
    simp

theorem isRightInversion_of_mem_rightInvSeq {ω : List B} (hω : cs.IsReduced ω) {t : W}
    (ht : t ∈ ris ω) : cs.IsRightInversion (π ω) t := by
  constructor
  · exact cs.isReflection_of_mem_rightInvSeq ω ht
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ht
    rw [← List.getD_eq_getElem _ 1 hj, wordProd_mul_getD_rightInvSeq]
    rw [cs.length_rightInvSeq] at hj
    calc
      ℓ (π (ω.eraseIdx j))
      _ ≤ (ω.eraseIdx j).length   := cs.length_wordProd_le _
      _ < ω.length                := by rw [← List.length_eraseIdx_add_one hj]; exact lt_add_one _
      _ = ℓ (π ω)                 := hω.symm

theorem isLeftInversion_of_mem_leftInvSeq {ω : List B} (hω : cs.IsReduced ω) {t : W}
    (ht : t ∈ lis ω) : cs.IsLeftInversion (π ω) t := by
  constructor
  · exact cs.isReflection_of_mem_leftInvSeq ω ht
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ht
    rw [← List.getD_eq_getElem _ 1 hj, getD_leftInvSeq_mul_wordProd]
    rw [cs.length_leftInvSeq] at hj
    calc
      ℓ (π (ω.eraseIdx j))
      _ ≤ (ω.eraseIdx j).length   := cs.length_wordProd_le _
      _ < ω.length                := by rw [← List.length_eraseIdx_add_one hj]; exact lt_add_one _
      _ = ℓ (π ω)                 := hω.symm

theorem prod_rightInvSeq (ω : List B) : prod (ris ω) = (π ω)⁻¹ := by
  induction ω with
  | nil => simp
  | cons i ω ih => simp [rightInvSeq, ih, wordProd_cons]

theorem prod_leftInvSeq (ω : List B) : prod (lis ω) = (π ω)⁻¹ := by
  simp only [leftInvSeq_eq_reverse_rightInvSeq_reverse, prod_reverse_noncomm, inv_inj]
  have : List.map (fun x ↦ x⁻¹) (ris ω.reverse) = ris ω.reverse := calc
    List.map (fun x ↦ x⁻¹) (ris ω.reverse)
    _ = List.map id (ris ω.reverse)             := by
        apply List.map_congr_left
        intro t ht
        exact (cs.isReflection_of_mem_rightInvSeq _ ht).inv
    _ = ris ω.reverse                           := map_id _
  rw [this]
  nth_rw 2 [← reverse_reverse ω]
  rw [wordProd_reverse]
  exact cs.prod_rightInvSeq _

theorem IsReduced.nodup_rightInvSeq {ω : List B} (rω : cs.IsReduced ω) : List.Nodup (ris ω) := by
  apply List.nodup_iff_getElem?_ne_getElem?.mpr
  intro j j' j_lt_j' j'_lt_length (dup : (rightInvSeq cs ω)[j]? = (rightInvSeq cs ω)[j']?)
  show False
  replace j'_lt_length : j' < List.length ω := by simpa using j'_lt_length
  rw [getElem?_eq_getElem (by simp; omega), getElem?_eq_getElem (by simp; omega)] at dup
  apply Option.some_injective at dup
  rw [← getD_eq_getElem _ 1, ← getD_eq_getElem _ 1] at dup
  set! t := (ris ω).getD j 1 with h₁
  set! t' := (ris (ω.eraseIdx j)).getD (j' - 1) 1 with h₂
  have h₃ : t' = (ris ω).getD j' 1                    := by
    rw [h₂, cs.getD_rightInvSeq, cs.getD_rightInvSeq,
      (Nat.sub_add_cancel (by omega) : j' - 1 + 1 = j'), eraseIdx_eq_take_drop_succ,
      drop_append_eq_append_drop, drop_of_length_le (by simp [j_lt_j'.le]), length_take,
      drop_drop, nil_append, min_eq_left_of_lt (j_lt_j'.trans j'_lt_length), Nat.add_comm,
      ← add_assoc, Nat.sub_add_cancel (by omega), mul_left_inj, mul_right_inj]
    congr 2
    show (List.take j ω ++ List.drop (j + 1) ω)[j' - 1]? = ω[j']?
    rw [getElem?_append_right (by simp [Nat.le_sub_one_of_lt j_lt_j']), getElem?_drop]
    congr
    show j + 1 + (j' - 1 - List.length (List.take j ω)) = j'
    rw [length_take]
    omega
  have h₄ : t * t' = 1                                := by
    rw [h₁, h₃, dup]
    exact cs.getD_rightInvSeq_mul_self _ _
  have h₅ := calc
    π ω   = π ω * t * t'                              := by rw [mul_assoc, h₄]; group
    _     = (π (ω.eraseIdx j)) * t'                   :=
        congrArg (· * t') (cs.wordProd_mul_getD_rightInvSeq _ _)
    _     = π ((ω.eraseIdx j).eraseIdx (j' - 1))      :=
        cs.wordProd_mul_getD_rightInvSeq _ _
  have h₆ := calc
    ω.length = ℓ (π ω)                                    := rω.symm
    _        = ℓ (π ((ω.eraseIdx j).eraseIdx (j' - 1)))   := congrArg cs.length h₅
    _        ≤ ((ω.eraseIdx j).eraseIdx (j' - 1)).length  := cs.length_wordProd_le _
  have h₇ := add_le_add_right (add_le_add_right h₆ 1) 1
  have h₈ : j' - 1 < List.length (eraseIdx ω j)           := by
    apply (@Nat.add_lt_add_iff_right 1).mp
    rw [Nat.sub_add_cancel (by omega)]
    rw [length_eraseIdx_add_one (by omega)]
    omega
  rw [length_eraseIdx_add_one h₈] at h₇
  rw [length_eraseIdx_add_one (by omega)] at h₇
  omega

theorem IsReduced.nodup_leftInvSeq {ω : List B} (rω : cs.IsReduced ω) : List.Nodup (lis ω) := by
  simp only [leftInvSeq_eq_reverse_rightInvSeq_reverse, nodup_reverse]
  apply nodup_rightInvSeq
  rwa [isReduced_reverse_iff]

lemma getElem_succ_leftInvSeq_alternatingWord
    (i j : B) (p k : ℕ) (h : k + 1 < 2 * p) :
    (lis (alternatingWord i j (2 * p)))[k + 1]'(by simpa using h) =
    MulAut.conj (s i) ((lis (alternatingWord j i (2 * p)))[k]'(by simp; omega)) := by
  rw [cs.getElem_leftInvSeq (alternatingWord i j (2 * p)) (k + 1) (by simp[h]),
    cs.getElem_leftInvSeq (alternatingWord j i (2 * p)) k (by simp[h]; omega)]
  simp only [MulAut.conj, listTake_succ_alternatingWord i j p k h, cs.wordProd_cons, mul_assoc,
    mul_inv_rev, inv_simple, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.coe_mk, Equiv.coe_fn_mk,
    mul_right_inj, mul_left_inj]
  rw [getElem_alternatingWord_swapIndices i j (2 * p) k]
  omega

theorem getElem_leftInvSeq_alternatingWord
    (i j : B) (p k : ℕ) (h : k < 2 * p) :
    (lis (alternatingWord i j (2 * p)))[k]'(by simp; omega) =
    π alternatingWord j i (2 * k + 1) := by
  induction k generalizing i j with
  | zero =>
    simp only [CoxeterSystem.getElem_leftInvSeq cs (alternatingWord i j (2 * p)) 0 (by simp [h]),
      take_zero, wordProd_nil, one_mul, inv_one, mul_one, alternatingWord, concat_eq_append,
      nil_append, wordProd_singleton]
    apply congr_arg
    simp only [getElem_alternatingWord i j (2 * p) 0 (by simp [h]), add_zero, even_two,
      Even.mul_right, ↓reduceIte]
  | succ k hk =>
    simp only [getElem_succ_leftInvSeq_alternatingWord cs i j p k h, hk _ _ (by omega),
      MulAut.conj_apply, inv_simple, alternatingWord_succ' j i, even_two, Even.mul_right,
      ↓reduceIte, wordProd_cons]
    rw [(by ring: 2 * (k + 1) = 2 * k + 1 + 1), alternatingWord_succ j i, wordProd_concat]
    simp [mul_assoc]

end CoxeterSystem
