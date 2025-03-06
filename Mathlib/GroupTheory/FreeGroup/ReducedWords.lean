/-
Copyright (c) 2025 Bernhard Reinke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amir Livne Bar-on, Bernhard Reinke
-/

import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Tactic.Linarith

import Mathlib.Data.List.Chain
import Mathlib.Data.List.Lemmas
import Mathlib.GroupTheory.OrderOfElement

/-!
This file defines some extra lemmas for free groups, in particular about (cyclically) reduced words.

## Main declarations

* `FreeGroup.Red.reduced`: the predicate for reduced words
* `FreeGroup.Red.cyclicallyReduced`: the predicate for cyclically reduced words

## Main statements
* `FreeGroup.infinite_order`: : nontrivial elements of a free group have infinite order
* `FreeGroup.zpow_left_injective`: taking n-th powers is an injective function on the free group

-/
open List

universe u

variable {α : Type u}
namespace FreeGroup

variable {L L₁ L₂ : List (α × Bool)}


namespace Red

@[to_additive]
def reduced (L : List (α × Bool)) : Prop := List.Chain' (fun a b => ¬(a.1 = b.1 ∧ (!a.2) = b.2)) L

@[to_additive (attr := simp)]
theorem reduced_nil : reduced ([] : List (α × Bool)) := List.chain'_nil

@[to_additive (attr := simp)]
theorem reduced_singleton {a : (α × Bool)} : reduced [a] := List.chain'_singleton a

@[to_additive (attr := simp)]
theorem reduced_cons {a b: (α × Bool)} :
    reduced (a :: b :: L) ↔ ¬(a.1 = b.1 ∧ (!a.2) = b.2) ∧ reduced (b :: L) :=
  List.chain'_cons

@[to_additive]
theorem not_step_reduced : reduced L₁ → ¬ Step L₁ L₂
| red, step => by induction step; simp [reduced] at red

@[to_additive]
theorem not_step_reduced_iff : reduced L₁ ↔ ∀ L₂, ¬ Step L₁ L₂ where
  mp h _ := not_step_reduced h
  mpr hL := by
    induction L₁ with
    | nil => exact reduced_nil
    | cons x l ih =>
      cases l with
      | nil => exact reduced_singleton
      | cons y l' =>
        rw [reduced_cons]
        constructor
        · intro ⟨eq1, eq2⟩
          obtain ⟨x1, x2⟩ := x
          obtain ⟨y1, y2⟩ := y
          simp only at eq1 eq2
          apply hL l'
          rw [eq1, ← eq2]
          apply Step.cons_not
        · apply ih
          intro L₂ step
          apply hL (x :: L₂)
          exact Step.cons step

@[to_additive]
theorem reduced_infix : reduced L₂ → L₁ <:+: L₂ → reduced L₁ := Chain'.infix

@[to_additive]
theorem reduced_min (h : reduced L₁) : Red L₁ L₂ ↔ L₂ = L₁ :=
  Relation.reflTransGen_iff_eq fun _ => not_step_reduced h

@[to_additive]
theorem reduced_cons_append_chain {x : α × Bool} {L₁ L₂ : List (α × Bool)} (h : L₁ ≠ []) :
    reduced (x :: L₁) → reduced (L₁ ++ L₂) → reduced (x :: L₁ ++ L₂) := by
  intro h1 h2
  induction L₁
  · contradiction
  · apply reduced_cons.mp at h1
    apply reduced_cons.mpr
    tauto

@[to_additive]
theorem reduced_append_chain {L₁ L₂ L₃ : List (α × Bool)} (h : L₂ ≠ []) :
    reduced (L₁ ++ L₂) → reduced (L₂ ++ L₃) → reduced (L₁ ++ L₂ ++ L₃) := by
  intro h1 h2
  induction L₁
  case nil => simp [h2]
  case cons head tail ih =>
    refine reduced_cons_append_chain (by simp [h]) h1 (ih (reduced_infix h1 ⟨[head], [], by simp⟩))

@[to_additive]
def cyclicallyReduced (L : List (α × Bool)) : Prop :=
  reduced L ∧ ∀ a ∈ L.getLast?, ∀ b ∈ L.head?, ¬(a.1 = b.1 ∧ (!a.2) = b.2)

@[to_additive (attr := simp)]
theorem cyclicallyReduced_nil : cyclicallyReduced ([] : List (α × Bool)) := by
  simp [cyclicallyReduced]

@[to_additive (attr := simp)]
theorem cyclicallyReduced_singleton {x : (α × Bool )} : cyclicallyReduced [x] := by
  simp [cyclicallyReduced]

@[to_additive]
theorem cyclicallyReduced_iff : cyclicallyReduced L ↔ reduced L ∧ ∀ a ∈ L.getLast?, ∀ b ∈ L.head?,
¬(a.1 = b.1 ∧ (!a.2) = b.2) := by rfl

@[to_additive]
theorem cyclicallyReduced_cons_append {a b : α × Bool} :
    cyclicallyReduced (b :: L ++ [a]) ↔
    reduced (b :: L ++ [a]) ∧ ¬(a.1 = b.1 ∧ (!a.2) = b.2) := by
  rw [cyclicallyReduced_iff,List.getLast?_concat]
  simp

@[to_additive]
theorem reduced_of_cyclicallyReduced (L : List (α × Bool)) : cyclicallyReduced L → reduced L :=
  fun h => h.1

@[to_additive]
theorem cyclicallyReduced_flatten_replicate (n : ℕ) (L : List (α × Bool))
    (h : cyclicallyReduced L) : cyclicallyReduced (List.replicate n L).flatten := by match n, L with
  | 0, _ => simp
  | n + 1, [] => simp
  | n + 1, (head::tail) =>
    unfold cyclicallyReduced at *
    unfold reduced at *
    rw [List.chain'_flatten (by simp)]
    constructor
    · constructor
      · simp only [List.mem_replicate, ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero,
        and_false, not_false_eq_true, true_and, Bool.not_eq_eq_eq_not, not_and, Bool.not_eq_not,
        forall_eq] at *
        apply h.1
      · apply List.chain'_replicate_of_rel _ h.2
    · intro a ha b hb
      simp only [Option.mem_def] at ha hb
      rw [List.getLast?_flatten_replicate (h := by simp +arith)] at ha
      rw [List.head?_flatten_replicate (h := by simp +arith)] at hb
      apply h.2 _ ha _ hb

variable [DecidableEq α]

@[to_additive]
theorem reduced_iff_eq_reduce : reduced L ↔ reduce L = L := by
  constructor
  · intro h
    rw [← reduced_min h]
    exact reduce.red
  · intro h
    unfold reduced
    rw [List.chain'_iff_forall_rel_of_append_cons_cons]
    intro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ l₁ l₂ hl hx
    simp only at hl hx
    rw [hx.1, ← hx.2] at hl
    nth_rw 2 [hl] at h
    apply reduce.not h

end Red

variable [DecidableEq α]

@[to_additive]
theorem reduced_toWord {x : FreeGroup α} : Red.reduced (x.toWord) := by
  rw [Red.reduced_iff_eq_reduce]
  simp

@[to_additive]
def reduceCyclically : List (α × Bool) → List (α × Bool) :=
  List.bidirectionalRec
    (nil := [])
    (singleton := fun x => [x])
    (cons_append := fun a l b rC => if (b.1 = a.1 ∧ (!b.2) = a.2) then rC else (a :: l ++ [b]))

@[to_additive]
def reduceCyclicallyConjugator : List (α × Bool) → List (α × Bool) := List.bidirectionalRec
  (nil := [])
  (singleton := fun _ => [])
  (cons_append := fun a _ b rCC => if (b.1 = a.1 ∧ (!b.2) = a.2) then a :: rCC else [] )

@[to_additive (attr := simp)]
theorem reduceCyclically_nil : reduceCyclically ([] : List (α × Bool)) = [] :=
  by simp [reduceCyclically]

@[to_additive (attr := simp)]
theorem reduceCyclically_singleton {a : α × Bool} : reduceCyclically [a] = [a] :=
  by simp [reduceCyclically]

@[to_additive (attr := simp)]
theorem reduceCyclicallyConjugator_nil : reduceCyclicallyConjugator ([] : List (α × Bool)) = [] :=
  by simp [reduceCyclicallyConjugator]

@[to_additive (attr := simp)]
theorem reduceCyclicallyConjugator_singleton {a : α × Bool} : reduceCyclicallyConjugator [a] = [] :=
  by simp [reduceCyclicallyConjugator]

@[to_additive]
theorem reduceCyclically_cons_append {a b : α × Bool} (l : List (α × Bool)) :
    reduceCyclically (a :: (l ++ [b])) =
    if (b.1 = a.1 ∧ (!b.2) = a.2) then reduceCyclically l else (a :: l ++ [b]) := by
  simp [reduceCyclically]

@[to_additive]
theorem reduceCyclicallyConjugator_cons_append {a b : α × Bool} (l : List (α × Bool)) :
    reduceCyclicallyConjugator (a :: (l ++ [b])) =
    if (b.1 = a.1 ∧ (!b.2) = a.2) then a :: reduceCyclicallyConjugator l else [] := by
  simp [reduceCyclicallyConjugator]

@[to_additive]
theorem reduceCyclically_conjugation (w : List (α × Bool)) : w = reduceCyclicallyConjugator w ++
    reduceCyclically w ++ invRev (reduceCyclicallyConjugator w) := by
  induction w using List.bidirectionalRec
  case nil => simp
  case singleton => simp
  case cons_append a l b eq =>
    rw [reduceCyclically_cons_append, reduceCyclicallyConjugator_cons_append]
    split
    case isTrue h =>
      nth_rw 1 [eq]
      simp [invRev, h.1.symm, h.2.symm]
    case isFalse => simp

@[to_additive]
theorem reduceCyclically_sound (w : List (α × Bool)) :
    Red.reduced w → Red.cyclicallyReduced (reduceCyclically w) := by
  induction w using List.bidirectionalRec
  case nil => simp
  case singleton => simp
  case cons_append a l b ih =>
    intro h
    rw [reduceCyclically_cons_append]
    split
    case isTrue =>
      apply ih
      apply Red.reduced_infix h
      exists [a], [b]
    case isFalse h =>
      rw [Red.cyclicallyReduced_cons_append]
      trivial

@[to_additive]
theorem reduced_flatten_replicate (n : ℕ) (hn : n ≠ 0) (L₁ L₂ L₃ : List (α × Bool))
    (h1 : Red.cyclicallyReduced L₂) (h2 : Red.reduced (L₁ ++ L₂ ++ L₃))
    : Red.reduced (L₁ ++ (List.replicate n L₂).flatten ++ L₃) := by
  match n with
  | 0 => contradiction
  | n + 1 =>
    if h : L₂ = [] then simp_all else
    have h' : (replicate (n + 1) L₂).flatten ≠ [] := by simp [h]
    apply Red.reduced_append_chain h'
    · rw [replicate_succ, flatten_cons, ←append_assoc]
      apply Red.reduced_append_chain h
      · exact Red.reduced_infix h2 ⟨[], L₃, by simp⟩
      · rw [←flatten_cons, ←replicate_succ]
        apply Red.reduced_of_cyclicallyReduced
        apply Red.cyclicallyReduced_flatten_replicate _ _ h1
    · rw [replicate_succ', flatten_concat]
      apply Red.reduced_append_chain h
      · rw [←flatten_concat, ←replicate_succ']
        apply Red.reduced_of_cyclicallyReduced
        apply Red.cyclicallyReduced_flatten_replicate _ _ h1
      · exact Red.reduced_infix h2 ⟨L₁, [], by simp⟩

@[to_additive]
theorem reduce_flatten_replicate' (n : ℕ) (L : List (α × Bool)) (h : Red.reduced L) :
    reduce (List.replicate (n + 1) L).flatten = reduceCyclicallyConjugator L ++ (List.replicate
    (n + 1) (reduceCyclically L)).flatten ++ invRev (reduceCyclicallyConjugator L) := by
  induction n
  case zero =>
    simpa [←append_assoc, ←reduceCyclically_conjugation, ←Red.reduced_iff_eq_reduce]
  case succ n ih =>
    rw [replicate_succ, flatten_cons, reduce_append, ih, Red.reduced_iff_eq_reduce.mp h]
    nth_rewrite 1 [reduceCyclically_conjugation L]
    have {L₁ L₂ L₃ L₄ L₅ : List (α × Bool)} : reduce (L₁ ++ L₂ ++ invRev L₃ ++ (L₃ ++ L₄ ++ L₅)) =
        reduce (L₁ ++ (L₂ ++ L₄) ++ L₅) := by
      nth_rewrite 1 [append_assoc]
      nth_rewrite 2 [←append_assoc, ←append_assoc]
      nth_rewrite 1 [reduce_append]
      nth_rewrite 3 [reduce_append]
      nth_rewrite 4 [reduce_append]
      simp [reduce_invRev_left_cancel, ←reduce_append]
    rw [this, ←flatten_cons, ←replicate_succ, ←Red.reduced_iff_eq_reduce]
    apply reduced_flatten_replicate _ (by simp) ..
    · apply reduceCyclically_sound _ h
    · rwa [←reduceCyclically_conjugation]

@[to_additive]
theorem reduce_flatten_replicate {n : ℕ} {L : List (α × Bool)} (hn : n ≠ 0) (h : Red.reduced L) :
    reduce (List.replicate n L).flatten = reduceCyclicallyConjugator L ++
    (List.replicate n (reduceCyclically L)).flatten ++ invRev (reduceCyclicallyConjugator L) :=
  match n with
  | 0 => by contradiction
  | n + 1 => reduce_flatten_replicate' n L h

@[to_additive FreeAdditiveGroup.nsmul_right_inj]
theorem pow_left_inj {x y : FreeGroup α} {n : ℕ} (hn : n ≠ 0) : x ^ n = y ^ n ↔ x = y := by
  refine ⟨fun heq => ?_, congr_arg (· ^ n)⟩

  have heq2 : x ^ (2 * n) = y ^ (2 * n) := by
    apply_fun (· ^ 2) at heq
    rwa [mul_comm, pow_mul, pow_mul]
  have hn2 : 2 * n ≠ 0 := by simp [hn]

  apply_fun toWord at heq heq2
  rw [toWord_pow, toWord_pow] at heq heq2
  rw [reduce_flatten_replicate hn x.reduced_toWord, reduce_flatten_replicate hn y.reduced_toWord]
    at heq
  rw [reduce_flatten_replicate hn2 x.reduced_toWord, reduce_flatten_replicate hn2 y.reduced_toWord]
    at heq2

  have leq := congr_arg List.length heq
  have leq2 := congr_arg List.length heq2
  simp [length_append] at leq leq2

  have hm : (reduceCyclically x.toWord).length = (reduceCyclically y.toWord).length := by
    apply Nat.mul_left_cancel (Nat.ne_zero_iff_zero_lt.mp hn)
    linarith

  have hc : reduceCyclicallyConjugator x.toWord = reduceCyclicallyConjugator y.toWord := by
    have : (reduceCyclicallyConjugator x.toWord).length =
      (reduceCyclicallyConjugator y.toWord).length :=
      by linarith
    apply_fun (·.take (reduceCyclicallyConjugator x.toWord).length) at heq
    rwa [append_assoc, take_left' rfl, this, append_assoc, take_left' rfl] at heq

  have hm : reduceCyclically x.toWord = reduceCyclically y.toWord := by
    simp [hc] at heq
    apply_fun (·.take (reduceCyclically x.toWord).length) at heq
    match n with
    | 0 => contradiction
    | n + 1 =>
      rw [replicate_succ, flatten_cons, take_left' rfl] at heq
      rwa [replicate_succ, flatten_cons, hm, take_left' rfl] at heq

  have := congr_arg mk <| reduceCyclically_conjugation x.toWord
  rwa [hc, hm, ←reduceCyclically_conjugation, mk_toWord, mk_toWord] at this

@[to_additive FreeAdditiveGroup.nsmul_right_injective]
theorem pow_left_injective {n : ℕ} (hn : n ≠ 0) :
    Function.Injective ((· ^ n) : FreeGroup α → FreeGroup α) := fun _ _ => (pow_left_inj hn).mp

@[to_additive FreeAdditiveGroup.zsmul_right_inj]
theorem zpow_left_inj {x y : FreeGroup α} {n : ℤ} (hn : n ≠ 0) : x ^ n = y ^ n ↔ x = y := by
  nth_rw 2 [← pow_left_inj (Int.natAbs_ne_zero.mpr hn)]
  rcases Int.natAbs_eq n with h | h
  · rw [h, Int.natAbs_ofNat, zpow_natCast, zpow_natCast]
  · rw [h, Int.natAbs_neg, Int.natAbs_ofNat, zpow_neg, zpow_neg, inv_inj, zpow_natCast,
    zpow_natCast]

@[to_additive FreeAdditiveGroup.zsmul_right_injective]
theorem zpow_left_injective {n : ℤ} (hn : n ≠ 0) :
    Function.Injective ((· ^ n) : FreeGroup α → FreeGroup α) := fun _ _ => (zpow_left_inj hn).mp

@[to_additive]
theorem infinite_order (x : FreeGroup α) (hx : x ≠ 1) : ¬IsOfFinOrder x := by
  rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨n, hn, eq⟩
  rw [← one_pow n, pow_left_inj (by omega)] at eq
  exact hx eq

@[to_additive]
theorem ne_inv_of_ne_one {x : FreeGroup α} (hx : x ≠ 1) : x ≠ x⁻¹ := by
  apply_fun (fun r => x*r)
  simp only [mul_inv_cancel, ne_eq]
  intro eq
  apply infinite_order x hx
  rw [isOfFinOrder_iff_pow_eq_one]
  use 2, (by decide)
  rw [← eq]
  exact pow_two x

end FreeGroup
