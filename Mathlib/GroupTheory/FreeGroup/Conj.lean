/-
Copyright (c) 2026 Omar Muhammad, Arjun Sheth, Vivek Rajesh Joshi, T V H Prathamesh,
Rishi Vyas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Omar Muhammad, Arjun Sheth, Vivek Rajesh Joshi, T V H Prathamesh, Rishi Vyas
-/
module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.Data.List.Rotate
public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

import Mathlib.Tactic.Group

/-!
# Conjugacy in free groups

Two elements of a free group are conjugate if and only if the cyclic reductions of their reduced
words are cyclic permutations of each other.

## Main results

* `FreeGroup.isConj_iff_isRotated`: `x` and `y` are conjugate iff
  `reduceCyclically x.toWord ~r reduceCyclically y.toWord`.
* `FreeGroup.isConj_mk_iff`: the same, for words that are not necessarily reduced.

The resulting `DecidableRel IsConj` instance is in
`Mathlib.GroupTheory.FreeGroup.ReduceCyclicallyDirect`.
-/

@[expose] public section

open List

namespace FreeGroup

variable {α : Type*} {L L₁ L₂ : List (α × Bool)}

/-- Cyclically permuting a word gives a conjugate element. -/
theorem isConj_mk_of_isRotated (h : L₁ ~r L₂) : IsConj (mk L₁) (mk L₂) := by
  obtain ⟨n, rfl⟩ := h
  rw [rotate_eq_drop_append_take_mod, isConj_iff]
  refine ⟨(mk (L₁.take (n % L₁.length)))⁻¹, ?_⟩
  have h₁ : mk L₁ = mk (L₁.take (n % L₁.length)) * mk (L₁.drop (n % L₁.length)) := by
    rw [mul_mk, take_append_drop]
  rw [h₁, ← mul_mk]
  group

theorem isReduced_concat_iff {a : α × Bool} :
    IsReduced (L ++ [a]) ↔ IsReduced L ∧ ∀ b ∈ L.getLast?, b.1 = a.1 → b.2 = a.2 := by
  simp [IsReduced, isChain_append]

theorem isCyclicallyReduced_iff_isReduced_append_self :
    IsCyclicallyReduced L ↔ IsReduced (L ++ L) := by
  simp [isCyclicallyReduced_iff, IsReduced, isChain_append]

theorem isCyclicallyReduced_append_comm :
    IsCyclicallyReduced (L₁ ++ L₂) ↔ IsCyclicallyReduced (L₂ ++ L₁) := by
  suffices ∀ {L₁ L₂ : List (α × Bool)}, IsCyclicallyReduced (L₁ ++ L₂) →
      IsCyclicallyReduced (L₂ ++ L₁) from ⟨this, this⟩
  intro L₁ L₂ h
  rw [isCyclicallyReduced_iff_isReduced_append_self] at h ⊢
  by_cases hn : L₁ ++ L₂ = []
  · simp_all
  exact (h.append_overlap h hn).infix ⟨L₁, L₂, by simp⟩

theorem IsCyclicallyReduced.rotate (h : IsCyclicallyReduced L) (n : ℕ) :
    IsCyclicallyReduced (L.rotate n) := by
  rw [rotate_eq_drop_append_take_mod, isCyclicallyReduced_append_comm, take_append_drop]
  exact h

theorem _root_.List.IsRotated.isCyclicallyReduced_iff (h : L₁ ~r L₂) :
    IsCyclicallyReduced L₁ ↔ IsCyclicallyReduced L₂ := by
  refine ⟨fun h₁ ↦ ?_, fun h₂ ↦ ?_⟩
  · obtain ⟨n, rfl⟩ := h
    exact h₁.rotate n
  · obtain ⟨n, rfl⟩ := h.symm
    exact h₂.rotate n

theorem IsCyclicallyReduced.of_isRotated (h : IsCyclicallyReduced L₁) (hr : L₁ ~r L₂) :
    IsCyclicallyReduced L₂ :=
  hr.isCyclicallyReduced_iff.1 h

variable [DecidableEq α]

theorem IsReduced.toWord_mk (h : IsReduced L) : (mk L).toWord = L := by
  rw [FreeGroup.toWord_mk, h.reduce_eq]

theorem IsCyclicallyReduced.reduceCyclically_eq (h : IsCyclicallyReduced L) :
    reduceCyclically L = L := by
  induction L using List.bidirectionalRec with
  | nil => simp
  | singleton => simp
  | cons_append a L b _ =>
    rw [reduceCyclically.cons_append, ite_eq_right]
    · simp
    · rw [← cons_append, isCyclicallyReduced_cons_append_iff] at h
      rintro ⟨h₁, h₂⟩
      rw [h.2 h₁] at h₂
      cases a.2 <;> simp at h₂

theorem reduceCyclically.append_append_invRev (L₁ L₂ : List (α × Bool)) :
    reduceCyclically (L₁ ++ L₂ ++ invRev L₁) = reduceCyclically L₂ := by
  induction L₁ with
  | nil => simp
  | cons a L₁ ih =>
    have : a :: L₁ ++ L₂ ++ invRev (a :: L₁) =
        a :: ((L₁ ++ L₂ ++ invRev L₁) ++ [(a.1, !a.2)]) := by
      simp [invRev]
    rw [this, reduceCyclically.cons_append, ite_eq_left (by simp), ih]

/-- Every word is conjugate to its cyclic reduction. -/
theorem isConj_mk_reduceCyclically (L : List (α × Bool)) :
    IsConj (mk (reduceCyclically L)) (mk L) := by
  rw [isConj_iff]
  refine ⟨mk (reduceCyclically.conjugator L), ?_⟩
  conv_rhs => rw [← reduceCyclically.conj_conjugator_reduceCyclically L]
  rw [inv_mk, mul_mk, mul_mk]

omit [DecidableEq α] in
private theorem noncancel_iff_ne_inv {a b : α × Bool} :
    (a.1 = b.1 → a.2 = b.2) ↔ b ≠ (a.1, !a.2) := by
  obtain ⟨a₁, a₂⟩ := a
  obtain ⟨b₁, b₂⟩ := b
  cases a₂ <;> cases b₂ <;> grind only

omit [DecidableEq α] in
private theorem noncancel_inv_iff_ne {a b : α × Bool} :
    (b.1 = a.1 → b.2 = !a.2) ↔ b ≠ a := by
  grind only

/-- For a letter `a`, the cyclic reduction of `a x a⁻¹` is a rotation of the cyclic reduction
of `x`. -/
private theorem isRotated_reduceCyclically_toWord_conj_letter (a : α × Bool) (x : FreeGroup α) :
    reduceCyclically (mk [a] * x * (mk [a])⁻¹).toWord ~r reduceCyclically x.toWord := by
  obtain ⟨L, hL, rfl⟩ : ∃ L, IsReduced L ∧ mk L = x :=
    ⟨x.toWord, isReduced_toWord, mk_toWord⟩
  rw [hL.toWord_mk]
  set a' : α × Bool := (a.1, !a.2) with ha'
  have hinv : (mk [a])⁻¹ = mk [a'] := by simp [inv_mk, invRev, ha']
  rw [hinv]
  have hcancel_left {b : α × Bool} : (a.1 = b.1 → a.2 = b.2) ↔ b ≠ a' :=
    noncancel_iff_ne_inv
  have hcancel_right {b : α × Bool} : (b.1 = a'.1 → b.2 = a'.2) ↔ b ≠ a := by
    rw [ha']; exact noncancel_inv_iff_ne (a := a)
  rcases L.eq_nil_or_concat' with rfl | ⟨M, c, rfl⟩
  · rw [← hinv, show mk ([] : List (α × Bool)) = 1 from rfl, mul_one, mul_inv_cancel]
    simp
  rcases M with _ | ⟨b, M⟩
  · -- single letter
    simp only [nil_append] at hL ⊢
    by_cases hc : c = a'
    · subst c
      rw [show mk [a] * mk [a'] * mk [a'] = mk [a'] by rw [← hinv]; group]
      simp
    by_cases hc' : c = a
    · subst c
      rw [show mk [a] * mk [a] * mk [a'] = mk [a] by rw [← hinv]; group]
      simp
    have hred : IsReduced [a, c, a'] := by
      simp only [isReduced_cons_cons, IsReduced.singleton, and_true]
      exact ⟨hcancel_left.2 hc, hcancel_right.2 hc'⟩
    rw [mul_mk, mul_mk, IsReduced.toWord_mk (by simpa using hred)]
    rw [show [a] ++ [c] ++ [a'] = a :: ([c] ++ [a']) by rfl, reduceCyclically.cons_append,
      ite_eq_left (by simp [ha'])]
  · -- at least two letters
    by_cases hb : b = a'
    · subst b
      by_cases hc : c = a
      · -- both ends cancel
        subst c
        have hM : IsReduced M := hL.infix ⟨[a'], [a], by simp⟩
        rw [show mk [a] * mk (a' :: M ++ [a]) * mk [a'] = mk M by
          rw [show a' :: M ++ [a] = [a'] ++ M ++ [a] by rfl, ← mul_mk, ← mul_mk, ← hinv]
          group]
        rw [hM.toWord_mk, cons_append, reduceCyclically.cons_append, ite_eq_left (by simp [ha'])]
      · -- only the first letter cancels
        have hcyc : IsCyclicallyReduced (a' :: M ++ [c]) := by
          rw [cons_append, ← cons_append, isCyclicallyReduced_cons_append_iff]
          exact ⟨hL, hcancel_right.2 hc⟩
        have hrot : a' :: M ++ [c] ~r M ++ [c] ++ [a'] := by
          rw [cons_append]; exact (isRotated_concat _ _).symm
        rw [show mk [a] * mk (a' :: M ++ [c]) * mk [a'] = mk (M ++ [c] ++ [a']) by
          rw [show a' :: M ++ [c] = [a'] ++ (M ++ [c]) by rfl, ← mul_mk, ← mul_mk,
            ← mul_mk, ← hinv]; simp only [← mul_mk]; group]
        rw [(hcyc.of_isRotated hrot).isReduced.toWord_mk,
          (hcyc.of_isRotated hrot).reduceCyclically_eq, hcyc.reduceCyclically_eq]
        exact hrot.symm
    · by_cases hc : c = a
      · -- only the last letter cancels
        subst c
        have hcyc : IsCyclicallyReduced (b :: M ++ [a]) := by
          rw [cons_append, ← cons_append, isCyclicallyReduced_cons_append_iff]
          exact ⟨hL, fun h₁ ↦ (hcancel_left (b := b)).2 hb h₁⟩
        have hrot : b :: M ++ [a] ~r a :: b :: M := isRotated_concat _ _
        rw [show mk [a] * mk (b :: M ++ [a]) * mk [a'] = mk (a :: b :: M) by
          rw [show a :: b :: M = [a] ++ (b :: M) by rfl, ← mul_mk, ← mul_mk, ← hinv]; group]
        rw [(hcyc.of_isRotated hrot).isReduced.toWord_mk,
          (hcyc.of_isRotated hrot).reduceCyclically_eq, hcyc.reduceCyclically_eq]
        exact hrot.symm
      · -- nothing cancels
        have hred : IsReduced (a :: (b :: M ++ [c] ++ [a'])) := by
          have h₁ : IsReduced (a :: (b :: M ++ [c])) := by
            rw [cons_append, isReduced_cons_cons]
            exact ⟨hcancel_left.2 hb, hL⟩
          have h₂ : IsReduced (b :: M ++ [c] ++ [a']) := by
            refine isReduced_concat_iff.2 ⟨hL, fun d hd ↦ ?_⟩
            rw [show (b :: M ++ [c]).getLast? = some c from getLast?_concat ..] at hd
            simp only [Option.mem_def, Option.some.injEq] at hd
            subst hd
            exact hcancel_right.2 hc
          exact IsReduced.append_overlap (L₁ := [a]) h₁ h₂ (by simp)
        rw [mul_mk, mul_mk, show [a] ++ (b :: M ++ [c]) ++ [a'] =
          a :: (b :: M ++ [c] ++ [a']) by rfl, hred.toWord_mk,
          reduceCyclically.cons_append, ite_eq_left (by simp [ha'])]

/-- The cyclic reduction of `c x c⁻¹` is a rotation of the cyclic reduction of `x`. -/
theorem isRotated_reduceCyclically_toWord_conj {c x : FreeGroup α} :
    reduceCyclically (c * x * c⁻¹).toWord ~r reduceCyclically x.toWord := by
  obtain ⟨L, rfl⟩ : ∃ L, mk L = c := ⟨c.toWord, mk_toWord⟩
  induction L with
  | nil => simpa [show mk ([] : List (α × Bool)) = 1 from rfl] using IsRotated.refl _
  | cons a L ih =>
    have : mk (a :: L) * x * (mk (a :: L))⁻¹ =
        mk [a] * (mk L * x * (mk L)⁻¹) * (mk [a])⁻¹ := by
      rw [show a :: L = [a] ++ L by rfl, ← mul_mk]
      group
    rw [this]
    exact (isRotated_reduceCyclically_toWord_conj_letter a _).trans ih

/-- **Conjugacy criterion for free groups**: two elements are conjugate iff the cyclic reductions
of their reduced words are cyclic permutations of each other. -/
theorem isConj_iff_isRotated {x y : FreeGroup α} :
    IsConj x y ↔ reduceCyclically x.toWord ~r reduceCyclically y.toWord := by
  refine ⟨fun h ↦ ?_, fun hr ↦ ?_⟩
  · obtain ⟨c, rfl⟩ := isConj_iff.1 h
    exact isRotated_reduceCyclically_toWord_conj.symm
  · have hx := isConj_mk_reduceCyclically x.toWord
    have hy := isConj_mk_reduceCyclically y.toWord
    rw [mk_toWord] at hx hy
    exact (hx.symm.trans (isConj_mk_of_isRotated hr)).trans hy

/-- Version of `isConj_iff_isRotated` for words that are not necessarily reduced. -/
theorem isConj_mk_iff :
    IsConj (mk L₁) (mk L₂) ↔
      reduceCyclically (reduce L₁) ~r reduceCyclically (reduce L₂) := by
  simp only [isConj_iff_isRotated, FreeGroup.toWord_mk]

end FreeGroup
