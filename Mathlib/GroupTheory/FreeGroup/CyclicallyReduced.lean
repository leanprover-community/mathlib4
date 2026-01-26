/-
Copyright (c) 2025 Bernhard Reinke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amir Livne Bar-on, Bernhard Reinke
-/
module

public import Mathlib.Data.List.Induction
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.Tactic.Group

/-!
This file defines some extra lemmas for free groups, in particular about cyclically reduced words.
We show that free groups are (strongly) torsion-free in the sense of `IsMulTorsionFree`, i.e.,
taking powers by every non-zero element `n : ℕ` is injective.

## Main declarations

* `FreeGroup.IsCyclicallyReduced`: the predicate for cyclically reduced words

-/

@[expose] public section
open List

universe u

variable {α : Type u}
namespace FreeGroup

variable {L L₁ L₂ L₃ : List (α × Bool)}

/-- Predicate asserting that the word `L` is cyclically reduced, i.e., it is reduced and furthermore
the first and the last letter of the word do not cancel. The empty word is by convention also
cyclically reduced. -/
@[to_additive /-- Predicate asserting that the word `L` is cyclically reduced, i.e., it is reduced
and furthermore the first and the last letter of the word do not cancel. The empty word is by
convention also cyclically reduced. -/]
def IsCyclicallyReduced (L : List (α × Bool)) : Prop :=
  IsReduced L ∧ ∀ a ∈ L.getLast?, ∀ b ∈ L.head?, a.1 = b.1 → a.2 = b.2

@[to_additive]
theorem isCyclicallyReduced_iff :
    IsCyclicallyReduced L ↔
    IsReduced L ∧ ∀ a ∈ L.getLast?, ∀ b ∈ L.head?, a.1 = b.1 → a.2 = b.2 := Iff.rfl

@[to_additive]
theorem isCyclicallyReduced_cons_append_iff {a b : α × Bool} :
    IsCyclicallyReduced (b :: L ++ [a]) ↔
    IsReduced (b :: L ++ [a]) ∧ (a.1 = b.1 → a.2 = b.2) := by
  rw [isCyclicallyReduced_iff, List.getLast?_concat]
  simp

namespace IsCyclicallyReduced

@[to_additive (attr := simp)]
protected theorem nil : IsCyclicallyReduced ([] : List (α × Bool)) := by
  simp [IsCyclicallyReduced]

@[to_additive (attr := simp)]
protected theorem singleton {x : (α × Bool)} : IsCyclicallyReduced [x] := by
  simp [IsCyclicallyReduced]


@[to_additive]
theorem isReduced (h : IsCyclicallyReduced L) : IsReduced L := h.1

@[to_additive]
theorem flatten_replicate (h : IsCyclicallyReduced L) (n : ℕ) :
    IsCyclicallyReduced (List.replicate n L).flatten := by match n, L with
  | 0, _ => simp
  | n + 1, [] => simp
  | n + 1, (head :: tail) =>
    rw [isCyclicallyReduced_iff, IsReduced, List.isChain_flatten (by simp)]
    refine ⟨⟨by simpa [IsReduced] using h.isReduced, List.isChain_replicate_of_rel _ h.2⟩,
      fun _ ha _ hb ↦ ?_⟩
    rw [Option.mem_def, List.getLast?_flatten_replicate (h := by simp +arith)] at ha
    rw [Option.mem_def, List.head?_flatten_replicate (h := by simp +arith)] at hb
    exact h.2 _ ha _ hb

end IsCyclicallyReduced

@[to_additive]
theorem IsReduced.append_flatten_replicate_append (h₁ : IsCyclicallyReduced L₂)
    (h₂ : IsReduced (L₁ ++ L₂ ++ L₃)) {n : ℕ} (hn : n ≠ 0) :
  IsReduced (L₁ ++ (List.replicate n L₂).flatten ++ L₃) := by
  match n with
  | 0 => contradiction
  | n + 1 =>
    if h : L₂ = [] then simp_all else
    have h' : (replicate (n + 1) L₂).flatten ≠ [] := by simp [h]
    refine IsReduced.append_overlap ?_ ?_ (hn := h')
    · rw [replicate_succ, flatten_cons, ← append_assoc]
      refine IsReduced.append_overlap (h₂.infix ⟨[], L₃, by simp⟩) ?_ h
      rw [← flatten_cons, ← replicate_succ]
      exact (h₁.flatten_replicate _).isReduced
    · rw [replicate_succ', flatten_concat]
      refine IsReduced.append_overlap ?_ (h₂.infix ⟨L₁, [], by simp⟩) h
      rw [← flatten_concat, ← replicate_succ']
      exact (h₁.flatten_replicate _).isReduced

/-- This function produces a subword of a word `L` by cancelling the first and last letters of `L`
as long as possible. If `L` is reduced, the resulting word will be cyclically reduced. -/
@[to_additive /-- This function produces a subword of a word `L` by cancelling the first and last
letters of `L` as long as possible. If `L` is reduced, the resulting word will be cyclically
reduced. -/]
def reduceCyclically [DecidableEq α] : List (α × Bool) → List (α × Bool) :=
  List.bidirectionalRec
    (nil := [])
    (singleton := fun x => [x])
    (cons_append := fun a L b rC => if b.1 = a.1 ∧ (!b.2) = a.2 then rC else a :: L ++ [b])

namespace reduceCyclically
variable [DecidableEq α]

@[to_additive (attr := simp)]
protected theorem nil : reduceCyclically ([] : List (α × Bool)) = [] := by simp [reduceCyclically]

@[to_additive (attr := simp)]
protected theorem singleton {a : α × Bool} : reduceCyclically [a] = [a] := by
  simp [reduceCyclically]

@[to_additive]
protected theorem cons_append {a b : α × Bool} (L : List (α × Bool)) :
    reduceCyclically (a :: (L ++ [b])) =
    if b.1 = a.1 ∧ (!b.2) = a.2 then reduceCyclically L else a :: L ++ [b] := by
  simp [reduceCyclically]


@[to_additive]
theorem isCyclicallyReduced (h : IsReduced L) : IsCyclicallyReduced (reduceCyclically L) := by
  induction L using List.bidirectionalRec
  case nil => simp
  case singleton => simp
  case cons_append a l b ih =>
    rw [reduceCyclically.cons_append]
    split
    case isTrue => exact ih (h.infix ⟨[a], [b], rfl⟩)
    case isFalse h' =>
      rw [isCyclicallyReduced_cons_append_iff]
      exact ⟨h, by simpa using h'⟩

/-- Partner function to `reduceCyclically`.
See `reduceCyclically.conj_conjugator_reduceCyclically`. -/
@[to_additive /-- Partner function to `reduceCyclically`.
See `reduceCyclically.conj_conjugator_reduceCyclically`. -/]
def conjugator : List (α × Bool) → List (α × Bool) :=
  List.bidirectionalRec
    (nil := [])
    (singleton := fun _ => [])
    (cons_append := fun a _ b rCC => if b.1 = a.1 ∧ (!b.2) = a.2 then a :: rCC else [] )

@[to_additive (attr := simp)]
protected theorem conjugator.nil : conjugator ([] : List (α × Bool)) = [] := by simp [conjugator]

@[to_additive (attr := simp)]
protected theorem conjugator.singleton {a : α × Bool} : conjugator [a] = [] := by simp [conjugator]

@[to_additive]
protected theorem conjugator.cons_append {a b : α × Bool} (L : List (α × Bool)) :
    conjugator (a :: (L ++ [b])) = if b.1 = a.1 ∧ (!b.2) = a.2 then a :: conjugator L else [] := by
  simp [conjugator]

@[to_additive]
theorem conj_conjugator_reduceCyclically (L : List (α × Bool)) :
    conjugator L ++ reduceCyclically L ++ invRev (conjugator L) = L := by
  induction L using List.bidirectionalRec
  case nil => simp
  case singleton => simp
  case cons_append a l b eq =>
    rw [reduceCyclically.cons_append, conjugator.cons_append]
    split
    case isTrue h =>
      nth_rw 4 [← eq]
      simp [invRev, h.1.symm, h.2.symm]
    case isFalse => simp

@[to_additive]
theorem reduce_flatten_replicate_succ (h : IsReduced L) (n : ℕ) :
    reduce (List.replicate (n + 1) L).flatten = conjugator L ++
    (List.replicate (n + 1) (reduceCyclically L)).flatten ++ invRev (conjugator L) := by
  induction n
  case zero =>
    simpa [← append_assoc, conj_conjugator_reduceCyclically, ← isReduced_iff_reduce_eq]
  case succ n ih =>
    rw [replicate_succ, flatten_cons, ← reduce_append_reduce_reduce, ih, h.reduce_eq]
    nth_rewrite 1 [← conj_conjugator_reduceCyclically L]
    have {L₁ L₂ L₃ L₄ L₅ : List (α × Bool)} : reduce (L₁ ++ L₂ ++ invRev L₃ ++ (L₃ ++ L₄ ++ L₅)) =
        reduce (L₁ ++ (L₂ ++ L₄) ++ L₅) := by
      apply reduce.sound
      repeat rw [← mul_mk]
      rw [← inv_mk]
      group
    rw [this, ← flatten_cons, ← replicate_succ, ← isReduced_iff_reduce_eq]
    apply IsReduced.append_flatten_replicate_append (hn := by simp)
    · exact isCyclicallyReduced h
    · rwa [conj_conjugator_reduceCyclically]

@[to_additive]
theorem reduce_flatten_replicate (h : IsReduced L) (n : ℕ) :
    reduce (List.replicate n L).flatten = if n = 0 then [] else conjugator L ++
    (List.replicate n (reduceCyclically L)).flatten ++ invRev (conjugator L) :=
  match n with
  | 0 => by simp
  | n + 1 => reduce_flatten_replicate_succ h n

end reduceCyclically

section IsMulTorsionFree
open reduceCyclically

/-- Free groups are torsion-free, i.e., taking powers is injective. Our proof idea is as follows:
if `x ^ n = y ^ n`, then also `x ^ (2 * n) = y ^ (2 * n)`. We then compare the reduced words
representing the powers in terms of the cyclic reductions of `x.toWord` and `y.toWord` using
`reduce_flatten_replicate`. We conclude that the cyclic reductions of `x.toWord` and `y.toWord` must
have the same length, and in fact they have to agree. -/
@[to_additive /-- Free additive groups are torsion free, i.e., scalar multiplication by every
non-zero element `n : ℕ` is injective. See the instance for free groups for an overview over the
proof. -/]
instance : IsMulTorsionFree (FreeGroup α) where
  pow_left_injective n hn x y heq := by
    classical
    let f (a : FreeGroup α) (n : ℕ) : ℕ :=
        (conjugator a.toWord).length + (n * (reduceCyclically a.toWord).length +
          (conjugator a.toWord).length)
    let g (a : FreeGroup α) (k : ℕ) : List (α × Bool) :=
        conjugator a.toWord ++ ((replicate k (reduceCyclically a.toWord)).flatten ++
          invRev (conjugator a.toWord))
    have heq₂ : x ^ (2 * n) = y ^ (2 * n) := by simp_rw [mul_comm, pow_mul, heq]
    replace heq : g x n = g y n := by
      simpa [toWord_pow, reduce_flatten_replicate, isReduced_toWord, hn] using congr_arg toWord heq
    replace heq₂ : g x (2 * n) = g y (2 * n) := by
      simpa [toWord_pow, reduce_flatten_replicate, isReduced_toWord, hn] using congr_arg toWord heq₂
    have leq : f x n = f y n := by simpa [g] using congr_arg List.length heq
    have leq₂ : f x (2 * n) = f y (2 * n) := by simpa [g] using congr_arg List.length heq₂
    obtain ⟨hc, heq'⟩ := List.append_inj heq (by grind)
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
    have hm : reduceCyclically x.toWord = reduceCyclically y.toWord := by
      simp only [replicate_succ, flatten_cons, append_assoc] at heq'
      exact (List.append_inj heq' <| mul_left_cancel₀ hn <| by grind).1
    have := congr_arg mk <| (conj_conjugator_reduceCyclically x.toWord).symm
    rwa [hc, hm, conj_conjugator_reduceCyclically, mk_toWord, mk_toWord] at this

end IsMulTorsionFree
end FreeGroup
