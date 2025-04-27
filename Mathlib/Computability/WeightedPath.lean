/-
Copyright (c) 2025 Rudy Peterson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rudy Peterson
-/
import Mathlib.Tactic.Ring

/-!
# Weighted Paths

A path `π` is a finite sequence of transitions/arcs in a state machine. This file defines weighted
paths for weighted finite state machines (FSMs). A transition in a weighted state machine is
comprised of the incoming state `s₁ ∈ σ`, a character `a ∈ α`, a weight `w ∈ κ`, and the outgoing
state `s₂ ∈ σ`.

## Implementation details

`WeightedPath α κ s₁ s₂` is a dependent type representing paths from `s₁ ∈ σ` to `s₂ ∈ σ`. The
indices ensure that the other constructions and operations (concatenation, reversal, etc.) are still
valid paths.

## References

* [R. Cotterell, A. Steve, A. Butoi, A. Opedal, and F. Nowak, *Advanced Formal Language Theory:
  Regular Languages*][cotterell]
* <https://drive.google.com/file/d/1wXv-e5tL6WxwK7vzBuVSDySYjkuoGW7f/view>
-/

universe k u v

/-- A weighted path `π : WeightedPath α κ s₁ s₂` represents a sequence of transitions in a weighted
FSM starting from `s₁ ∈ σ` ending at `s₂ ∈ σ`. -/
inductive WeightedPath (α : Type u) (κ : Type k) {σ : Type v} : σ → σ → Type (max u v k) where
  | last (s : σ) : WeightedPath α κ s s
  | arc (s₁ s₂ s₃ : σ) (a : α) (w : κ) (π : WeightedPath α κ s₂ s₃) : WeightedPath α κ s₁ s₃

namespace WeightedPath

variable {α : Type u} {σ : Type v} {κ : Type k}

/-- `π.length` is the number of transitions in `π`. -/
@[simp]
def length {s₁ s₃ : σ} : WeightedPath α κ s₁ s₃ → Nat
  | last _ => 0
  | arc _ _ _ _ _ π => 1 + π.length

/-- `π₁.concat π₂` is the sequence of transitions in `π₁` concatenated with `π₂`. -/
@[simp]
def concat {s₁ s₂ s₃ : σ} : WeightedPath α κ s₁ s₂ → WeightedPath α κ s₂ s₃ → WeightedPath α κ s₁ s₃
  | last _, π₂ => π₂
  | arc s₁ s s₂ a w π₁, π₂ => arc s₁ s s₃ a w (π₁.concat π₂)

/-- `π.reverse` reverses the sequence of transitions in `π`. -/
@[simp]
def reverse {s₁ s₃ : σ} : WeightedPath α κ s₁ s₃ → WeightedPath α κ s₃ s₁
  | last _ => last _
  | arc s₁ s₂ s₃ a w π => concat π.reverse (arc s₂ s₁ s₁ a w (last s₁))

/-- `π.yield` computes the string of the path `π`. -/
@[simp]
def yield {s₁ s₃ : σ} : WeightedPath α κ s₁ s₃ → List α
  | last _ => []
  | arc _ _ _ a _ π => a :: π.yield

lemma concat_assoc {s₁ s₂ s₃ s₄ : σ}
  (π₁ : WeightedPath α κ s₁ s₂) (π₂ : WeightedPath α κ s₂ s₃) (π₃ : WeightedPath α κ s₃ s₄) :
    (π₁.concat π₂).concat π₃ = π₁.concat (π₂.concat π₃) := by
  revert s₃ s₄ π₂ π₃
  induction π₁ <;> intros s₃ s₄ π₂ π₃
  case last _ =>
    simp
  case arc _ s _ a w π₁ ih =>
    simp [ih]

lemma concat_last {s₁ s₃ : σ} (π : WeightedPath α κ s₁ s₃) : π.concat (last _) = π := by
  induction π
  case last _ =>
    simp
  case arc _ s₂ _ a w π ih =>
    simp [ih]

lemma length_concat {s₁ s₂ s₃ : σ} (π₁ : WeightedPath α κ s₁ s₂) (π₂ : WeightedPath α κ s₂ s₃) :
    (π₁.concat π₂).length = π₁.length + π₂.length := by
  revert π₂
  induction π₁ <;> intro π₂
  case last _ =>
    simp
  case arc _ s _ a w π₁ ih =>
    simp [ih]
    ring

lemma length_reverse {s₁ s₃ : σ} (π : WeightedPath α κ s₁ s₃) : π.reverse.length = π.length := by
  induction π
  case last _ =>
    simp
  case arc _ s₂ _ a w π ih =>
    simp [length_concat, ih]
    ring

lemma reverse_concat {s₁ s₂ s₃ : σ} (π₁ : WeightedPath α κ s₁ s₂) (π₂ : WeightedPath α κ s₂ s₃) :
    (π₁.concat π₂).reverse = π₂.reverse.concat π₁.reverse := by
  revert s₃ π₂
  induction π₁ <;> intros s₃ π₂
  case last _ =>
    simp [concat_last]
  case arc _ s _ a w π₁ ih =>
    simp [ih, concat_assoc]

lemma reverse_involutive {s₁ s₃ : σ} (π : WeightedPath α κ s₁ s₃) : π.reverse.reverse = π := by
  induction π
  case last _ =>
    simp
  case arc s1 s₂ s3 a w π ih =>
    simp
    have h : arc s₂ s1 _ a w (last _) = (arc s1 _ s₂ a w (last _)).reverse := by simp
    rw [h]
    simp [reverse_concat, ih]

lemma yield_concat {s₁ s₂ s₃ : σ} (π₁ : WeightedPath α κ s₁ s₂) (π₂ : WeightedPath α κ s₂ s₃) :
    (π₁.concat π₂).yield = π₁.yield ++ π₂.yield := by
  revert π₂
  induction π₁ <;> intros π₂
  case last _ =>
    simp
  case arc _ s _ a w ih =>
    simp [ih]

lemma yield_reverse {s₁ s₃ : σ} (π : WeightedPath α κ s₁ s₃) :
    π.reverse.yield = π.yield.reverse := by
  induction π
  case last _ =>
    simp
  case arc _ s₂ _ a w π ih =>
    simp [yield_concat, ih]

/-- `π.innerWeight` multiplies the weights in order of all transitions in `π`. -/
@[simp]
def innerWeight [W : Semiring κ] {s₁ s₃ : σ} : WeightedPath α κ s₁ s₃ → κ
  | last _ => 1
  | arc _ _ _ _ w π => w * π.innerWeight

lemma innerWeight_concat [W : Semiring κ] {s₁ s₂ s₃ : σ}
  (π₁ : WeightedPath α κ s₁ s₂) (π₂ : WeightedPath α κ s₂ s₃) :
    (π₁.concat π₂).innerWeight = π₁.innerWeight * π₂.innerWeight := by
  revert π₂
  induction π₁ <;> intro π₂
  case last _ =>
    simp
  case arc _ s _ a w π₁ ih =>
    simp [ih, W.mul_assoc]

lemma innerWeight_reverse [W : CommSemiring κ] {s₁ s₃ : σ} (π : WeightedPath α κ s₁ s₃) :
    π.reverse.innerWeight = π.innerWeight := by
  induction π
  case last _ =>
    simp
  case arc _ s₂ _ a w π ih =>
    simp [innerWeight_concat, ih, W.mul_comm]

section foldr

universe b

variable {β : Type b} (f : σ → α → κ → σ → β → β) (init : β)

/-- `foldr f init π` folds `f` over `π` right-associatively. -/
@[simp]
def foldr {s₁ s₃ : σ} : WeightedPath α κ s₁ s₃ → β
  | last _ => init
  | arc _ s₂ _ a w π => f s₁ a w s₂ π.foldr

end foldr

lemma foldr_length {s₁ s₃ : σ} (π : WeightedPath α κ s₁ s₃) :
    foldr (fun _ _ _ _ ↦ Nat.succ) 0 π = π.length := by
  induction π
  case last _ =>
    simp
  case arc _ s₂ _ a w π ih =>
    simp [ih]
    ring

lemma foldr_yield {s₁ s₃ : σ} (π : WeightedPath α κ s₁ s₃) :
    foldr (fun _ a _ _ ↦ List.cons a) [] π = π.yield := by
  induction π
  case last _ =>
    simp
  case arc _ s₂ _ a w π ih =>
    simp [ih]

lemma foldr_innerWeight [W : Semiring κ] {s₁ s₃ : σ} (π : WeightedPath α κ s₁ s₃) :
    foldr (fun _ _ w _ ↦ W.mul w) 1 π = π.innerWeight := by
  induction π
  case last _ =>
    simp
  case arc _ s₂ _ a w π ih =>
    simp [ih]
    rfl

section All

variable (P : σ → α → κ → σ → Prop)

/-- `All P π` holds when `P` holds for every transition in `π`. -/
@[simp]
def All {s₁ s₂ : σ} : WeightedPath α κ s₁ s₂ → Prop
  | last _ => True
  | arc s₁ s₂ s₃ a w π => P s₁ a w s₂ ∧ All π

end All

section AllLemmas

variable (P : σ → α → κ → σ → Prop)

lemma All_concat {s₁ s₂ s₃ : σ}
  (π₁ : WeightedPath α κ s₁ s₂) (π₂ : WeightedPath α κ s₂ s₃) :
    All P (π₁.concat π₂) ↔ All P π₁ ∧ All P π₂ := by
  revert s₃ π₂
  induction π₁ <;> intros s₃ π₂
  case last _ =>
    simp
  case arc _ s _ a w π₁ ih =>
    simp [ih, and_assoc]

lemma All_reverse {s₁ s₂ : σ} (π : WeightedPath α κ s₁ s₂) :
    All P π.reverse ↔ All (fun s₂ a w s₁ => P s₁ a w s₂) π := by
  induction π
  case last _ =>
    simp
  case arc _ s _ a w π ih =>
    simp [All_concat, ih, and_comm]

end AllLemmas

end WeightedPath
