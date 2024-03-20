/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee
-/
import Mathlib.GroupTheory.Coxeter.Length

/-!
# Reflections, inversions, and inversion sequences
Throughout this file, `B` is a type and `M : Matrix B B ℕ` is a Coxeter matrix.
`cs : CoxeterSystem M W` is a Coxeter system; that is, `W` is a group, and `cs` holds the data
of a group isomorphism `W ≃* Matrix.CoxeterGroup M`, where `Matrix.CoxeterGroup M` refers to
the quotient of the free group on `B` by the Coxeter relations given by the matrix `M`. See
`Mathlib.GroupTheory.Coxeter.Basic` for more details.

We define a *reflection* to be an element of the form
$t = u s_i u^{-1}$, where $u \in W$ and $s_i$ is a simple reflection. We say that a reflection $t$
is a *left inversion* of an element $w \in W$ if $\ell(t w) < \ell (w)$, and we say it is a
*right inversion* of $w$ if $\ell(w t) > \ell(w)$. Here $\ell$ is the length function
(see `Mathlib.GroupTheory.Coxeter.Length`).

Given a word, we define its *left inversion sequence* and its *right inversion sequence*. We prove
that if a word is reduced, then both of its inversion sequences contain no duplicates.
In fact, the right (respectively, left) inversion sequence of a reduced word for $w$ consists of all
of the right (respectively, left) inversions of $w$ in some order, but we do not prove that in this
file.

## Main definitions
* `cs.IsReflection`
* `cs.IsLeftInversion`
* `cs.IsRightInversion`
* `cs.leftInvSeq`
* `cs.rightInvSeq`

## References
* [A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*](bjorner2005)
-/

noncomputable section

namespace CoxeterSystem

open List Matrix Function CoxeterSystem

variable {B : Type*} [DecidableEq B]
variable {M : Matrix B B ℕ}
variable {W : Type*} [Group W]
variable (cs : CoxeterSystem M W)

local prefix:100 "s" => cs.simpleReflection
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length

/-- The proposition that `t` is a reflection of the Coxeter system `cs`; i.e., it is of the form
$w s_i w^{-1}$, where $w \in W$ and $s_i$ is a simple reflection. -/
def IsReflection (t : W) : Prop := ∃ w : W, ∃ i : B, t = w * s i * w⁻¹

/-- The set of all reflections of the Coxeter group `W`. -/
def reflections : Set W := {t : W | cs.IsReflection t}

theorem isReflection_simple (i : B) : cs.IsReflection (s i) := by use 1, i; simp

theorem pow_two_eq_one_of_isReflection {t : W} (rt : cs.IsReflection t) : t ^ 2 = 1 := by
  rcases rt with ⟨w, i, rfl⟩
  simp

theorem inv_reflection_eq {t : W} (rt : cs.IsReflection t) : t⁻¹ = t := by
  rcases rt with ⟨w, i, rfl⟩
  group
  simp

alias inv_eq_self_of_isReflection := inv_reflection_eq

theorem length_reflection_odd {t : W} (rt : cs.IsReflection t) : Odd (ℓ t) := by
  rw [Nat.odd_iff]
  rcases rt with ⟨w, i, rfl⟩
  rw [length_mul_mod_two, Nat.add_mod, length_mul_mod_two, ← Nat.add_mod,
      length_simple, length_inv, add_comm, ← add_assoc, ← two_mul, Nat.mul_add_mod]
  norm_num

alias odd_length_of_isReflection := length_reflection_odd

theorem isReflection_conjugate_iff (w t : W) :
    cs.IsReflection (w * t * w⁻¹) ↔ cs.IsReflection t := by
  constructor
  · rintro ⟨u, i, hi⟩
    use w⁻¹ * u, i
    apply mul_left_cancel (a := w)
    apply mul_right_cancel (b := w⁻¹)
    rw [hi]
    group
  · rintro ⟨u, i, rfl⟩
    use w * u, i
    group

/-- The proposition that `t` is a right inversion of `w`; i.e., `t` is a reflection and
$\ell (w t) < \ell(w)$. -/
def IsRightInversion (w t : W) : Prop := cs.IsReflection t ∧ ℓ (w * t) < ℓ w
/-- The proposition that `t` is a left inversion of `w`; i.e., `t` is a reflection and
$\ell (t w) < \ell(w)$. -/
def IsLeftInversion (w t : W) : Prop := cs.IsReflection t ∧ ℓ (t * w) < ℓ w

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
  induction' ω with j ω ih
  · simp
  · dsimp [rightInvSeq]
    rw [ih]
    simp only [concat_eq_append, wordProd_append, wordProd_cons, wordProd_nil, mul_one, mul_inv_rev,
      simple_inv, cons_append, cons.injEq, and_true]
    group

theorem leftInvSeq_concat (ω : List B) (i : B) :
    lis (ω.concat i) = (lis ω).concat ((π ω) * (s i) * (π ω)⁻¹) := by
  induction' ω with j ω ih
  · simp
  · dsimp [leftInvSeq]
    rw [ih]
    simp only [concat_eq_append, map_append, map_cons, _root_.map_mul, MulAut.conj_apply,
      simple_inv, map_inv, mul_inv_rev, map_nil, wordProd_cons, cons_append, cons.injEq,
      append_cancel_left_eq, and_true, true_and]
    group
    simp [mul_assoc]

private theorem leftInvSeq_eq_reverse_rightInvSeq_reverse (ω : List B) :
    lis ω = (ris ω.reverse).reverse := by
  induction' ω with i ω ih
  · simp
  · rw [leftInvSeq, reverse_cons, ← concat_eq_append, rightInvSeq_concat, ih]
    simp [map_reverse]

theorem rightInvSeq_reverse (ω : List B) :
    ris (ω.reverse) = (lis ω).reverse := by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse]

theorem leftInvSeq_reverse (ω : List B) :
    lis (ω.reverse) = (ris ω).reverse := by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse]

@[simp] theorem length_rightInvSeq (ω : List B) : (ris ω).length = ω.length := by
  induction' ω with i ω ih
  · simp
  · simpa [rightInvSeq]

@[simp] theorem length_leftInvSeq (ω : List B) : (lis ω).length = ω.length := by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse]

theorem getD_rightInvSeq (ω : List B) (j : ℕ) :
    (ris ω).getD j 1 = (π (ω.drop (j + 1)))⁻¹
        * (Option.map (cs.simpleReflection) (ω.get? j)).getD 1
        * π (ω.drop (j + 1)) := by
  induction' ω with i ω ih generalizing j
  · simp
  · dsimp only [rightInvSeq]
    rcases j with _ | j'
    · simp [getD_cons_zero]
    · simp [getD_cons_succ]
      rw [ih j']

theorem getD_leftInvSeq (ω : List B) (j : ℕ) :
    (lis ω).getD j 1 = π (ω.take j)
        * (Option.map (cs.simpleReflection) (ω.get? j)).getD 1
        * (π (ω.take j))⁻¹ := by
  induction' ω with i ω ih generalizing j
  · simp
  · dsimp [leftInvSeq]
    rcases j with _ | j'
    · simp [getD_cons_zero]
    · rw [getD_cons_succ]
      rw [(by simp : 1 = ⇑(MulAut.conj (simpleReflection cs i)) 1)]
      rw [getD_map]
      rw [ih j']
      simp [← mul_assoc]

theorem getD_rightInvSeq_mul_self (ω : List B) (j : ℕ) :
    ((ris ω).getD j 1) * ((ris ω).getD j 1) = 1 := by
  simp [getD_rightInvSeq, mul_assoc]
  rcases em (j < ω.length) with hj | nhj
  · rw [get?_eq_get hj]
    simp [← mul_assoc]
  · rw [get?_eq_none.mpr (by linarith)]
    simp

theorem getD_leftInvSeq_mul_self (ω : List B) (j : ℕ) :
    ((lis ω).getD j 1) * ((lis ω).getD j 1) = 1 := by
  simp [getD_leftInvSeq, mul_assoc]
  rcases em (j < ω.length) with hj | nhj
  · rw [get?_eq_get hj]
    simp [← mul_assoc]
  · rw [get?_eq_none.mpr (by linarith)]
    simp

theorem rightInvSeq_drop (ω : List B) (j : ℕ) :
    ris (ω.drop j) = (ris ω).drop j := by
  induction' j with j ih₁ generalizing ω
  · simp
  · induction' ω with k ω _
    · simp
    · rw [drop_succ_cons, ih₁ ω, rightInvSeq, drop_succ_cons]

theorem leftInvSeq_take (ω : List B) (j : ℕ) :
    lis (ω.take j) = (lis ω).take j := by
  rcases em (j ≤ ω.length) with le | gt
  · simp only [leftInvSeq_eq_reverse_rightInvSeq_reverse]
    rw [List.reverse_take j (by simpa)]
    nth_rw 1 [← List.reverse_reverse ω]
    rw [List.reverse_take j (by simpa)]
    simp [rightInvSeq_drop]
  · have : ω.length ≤ j := by linarith
    rw [take_length_le this, take_length_le (by simpa)]

theorem isReflection_of_mem_rightInvSeq (ω : List B) (t : W) (ht : t ∈ ris ω) :
    cs.IsReflection t := by
  induction' ω with i ω ih
  · simp at ht
  · dsimp [rightInvSeq] at ht
    rcases ht with _ | ⟨_, mem⟩
    · use (π ω)⁻¹, i
      group
    · exact ih mem

theorem isReflection_of_mem_leftInvSeq (ω : List B) (t : W) (ht : t ∈ lis ω) :
    cs.IsReflection t := by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse] at ht
  exact cs.isReflection_of_mem_rightInvSeq ω.reverse t ht

theorem wordProd_mul_getD_rightInvSeq (ω : List B) (j : ℕ) :
    π ω * ((ris ω).getD j 1) = π (ω.eraseIdx j) := by
  rw [getD_rightInvSeq, eraseIdx_eq_take_drop_succ]
  nth_rw 1 [← take_append_drop (j + 1) ω]
  rw [take_succ]
  simp [mul_assoc]
  simp [← mul_assoc]
  rcases em (j < ω.length) with hj | nhj
  · rw [get?_eq_get hj]
    simp
  · rw [get?_eq_none.mpr (by linarith)]
    simp

theorem getD_leftInvSeq_mul_wordProd (ω : List B) (j : ℕ) :
    ((lis ω).getD j 1) * π ω = π (ω.eraseIdx j) := by
  rw [getD_leftInvSeq, eraseIdx_eq_take_drop_succ]
  nth_rw 4 [← take_append_drop (j + 1) ω]
  rw [take_succ]
  simp [mul_assoc]
  simp [← mul_assoc]
  rcases em (j < ω.length) with hj | nhj
  · rw [get?_eq_get hj]
    simp
  · rw [get?_eq_none.mpr (by linarith)]
    simp

theorem prod_rightInvSeq (ω : List B) : prod (ris ω) = (π ω)⁻¹ := by
  induction' ω with i ω ih
  · simp
  · simp [rightInvSeq, ih]

theorem prod_leftInvSeq (ω : List B) : prod (lis ω) = (π ω)⁻¹ := by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse, prod_reverse_noncomm]
  have : List.map (fun x ↦ x⁻¹) (ris ω.reverse) = ris ω.reverse := calc
    List.map (fun x ↦ x⁻¹) (ris ω.reverse)
    _ = List.map id (ris ω.reverse)             := by
        apply List.map_congr
        intro t ht
        exact cs.inv_reflection_eq (cs.isReflection_of_mem_rightInvSeq _ t ht)
    _ = ris ω.reverse                           := map_id _
  rw [this]
  nth_rw 2 [← reverse_reverse ω]
  rw [wordProd_reverse]
  exact cs.prod_rightInvSeq _

theorem nodup_rightInvSeq_of_reduced {ω : List B} (rω : cs.IsReduced ω) : List.Nodup (ris ω) := by
  apply List.nodup_iff_get?_ne_get?.mpr
  intro j j' j_lt_j' j'_lt_length dup
  -- dup : get? (rightInvSeq cs ω) j = get? (rightInvSeq cs ω) j'
  -- ⊢ False

  simp at j'_lt_length
  -- j'_lt_length: j' < List.length ω

  rw [get?_eq_get (by simp; linarith), get?_eq_get (by simp; linarith)] at dup
  apply Option.some_injective at dup
  rw [← getD_eq_get _ 1, ← getD_eq_get _ 1] at dup

  set! t := (ris ω).getD j 1 with h₁
  set! t' := (ris (ω.eraseIdx j)).getD (j' - 1) 1 with h₂

  have h₃ : t' = (ris ω).getD j' 1                    := by
    rw [h₂]
    rw [cs.getD_rightInvSeq, cs.getD_rightInvSeq]
    rw [(Nat.sub_add_cancel (by linarith) : j' - 1 + 1 = j')]
    rw [eraseIdx_eq_take_drop_succ]
    rw [drop_append_eq_append_drop]
    rw [drop_length_le (by simp; left; linarith)]
    rw [length_take, drop_drop, nil_append]
    rw [min_eq_left_of_lt (j_lt_j'.trans j'_lt_length)]
    rw [Nat.succ_eq_add_one, ← add_assoc, Nat.sub_add_cancel (by linarith)]
    rw [mul_left_inj, mul_right_inj]
    congr 2
    -- ⊢ get? (take j ω ++ drop (j + 1) ω) (j' - 1) = get? ω j'
    rw [get?_append_right (by simp; left; exact Nat.le_sub_one_of_lt j_lt_j')]
    rw [get?_drop]
    congr
    -- ⊢ j + 1 + (j' - 1 - List.length (take j ω)) = j'
    rw [length_take]
    rw [min_eq_left_of_lt (j_lt_j'.trans j'_lt_length)]
    rw [Nat.sub_sub, add_comm 1, Nat.add_sub_cancel' (by linarith)]

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
    rw [Nat.sub_add_cancel (by linarith)]
    rw [length_eraseIdx_add_one (by linarith)]
    linarith

  rw [length_eraseIdx_add_one h₈] at h₇
  rw [length_eraseIdx_add_one (by linarith)] at h₇
  linarith

theorem nodup_leftInvSeq_of_reduced {ω : List B} (rω : cs.IsReduced ω) : List.Nodup (lis ω) := by
  simp only [leftInvSeq_eq_reverse_rightInvSeq_reverse, nodup_reverse]
  apply nodup_rightInvSeq_of_reduced
  rwa [isReduced_reverse]

end CoxeterSystem

end
