/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib

@[simp]
theorem Stream'.zip_cons {α β δ : Type*} (f : α → β → δ) (a : α) (b : β)
    (s₁ : Stream' α) (s₂ : Stream' β) :
    (Stream'.cons a s₁).zip f (.cons b s₂) = .cons (f a b) (s₁.zip f s₂) := by
  ext n
  cases n with
  | zero => simp
  | succ => simp

def zeros : Stream' ℕ := Stream'.cons 0 zeros

def Stream'.add (x y : Stream' ℕ) : Stream' ℕ :=
  x.zip (· + ·) y

@[simp]
theorem Stream'.add_cons (a b : ℕ) (as bs : Stream' ℕ) :
    (Stream'.cons a as).add (.cons b bs) = .cons (a + b) (as.add bs) := by
  simp [add]

def fibInv (s : Stream' ℕ) : Prop :=
  ∃ a b c, s = (Stream'.cons a s).add (Stream'.cons b (Stream'.cons c s))

theorem Fib_live (s : Stream' ℕ) (h : fibInv s) :
    ∃ x t, s = .cons x t ∧ fibInv t := by
  obtain ⟨a, b, c, hs⟩ := h
  use ?_, ?_
  constructor
  · rw [hs]
    simp only [Stream'.add_cons]
    rfl
  change fibInv (s.add (.cons c s))
  use s.head, c, s.head
  conv_lhs => rw [← Stream'.cons_head_tail s]
  simp [-Stream'.eta]
  congr 1
  conv_lhs => rw [hs]; simp
  congr
  rw [hs]
  simp

def Fib : Stream' ℕ :=
  (Stream'.cons 0 Fib).add (Stream'.cons 0 (Stream'.cons 1 Fib))

/-! ### Semantic productive corecursion via a terminating search

A seed dynamics `Step α β` either *emits* a value together with a new seed, or *silently*
advances to a new seed. Productivity is **well-foundedness of the silent-step relation** — the
search between two emissions terminates. This is a semantic condition, not syntactic
guardedness: for `primes` it is literally the infinitude of primes.

The stream is the outer corecursion (`build`) over the inner well-founded search (`find`):
mixed induction–coinduction (`νX. μY. (α × X) ⊕ Y`). `find` recurses on the productivity
witness exactly as well-founded recursion recurses on an `Acc` proof; `build` is the `corec`. -/

namespace SearchCorec

variable {α β : Type*}

/-- One step of seed dynamics: emit a value with the next seed (`Sum.inl`), or silently
advance to a new seed (`Sum.inr`). -/
abbrev Step (α β : Type*) := β → (α × β) ⊕ β

/-- `Silent step s' s` : seed `s` silently advances to `s'` without emitting. Productivity of
the corecursion is exactly `WellFounded (Silent step)`. -/
def Silent (step : Step α β) (s' s : β) : Prop := step s = Sum.inr s'

/-- Run silent steps from `s` until the first emission, returning the emitted value and the
seed that follows it. The productivity witness `wf` certifies the search terminates. -/
def find (step : Step α β) (wf : WellFounded (Silent step)) (s : β) : α × β :=
  wf.fix (C := fun _ => α × β)
    (fun s ih => match h : step s with
      | Sum.inl as => as
      | Sum.inr s' => ih s' h) s

theorem find_emit {step : Step α β} {wf : WellFounded (Silent step)} {s : β} {a : α} {s' : β}
    (h : step s = Sum.inl (a, s')) : find step wf s = (a, s') := by
  unfold find
  rw [wf.fix_eq]
  split <;> simp_all

theorem find_skip {step : Step α β} {wf : WellFounded (Silent step)} {s s' : β}
    (h : step s = Sum.inr s') : find step wf s = find step wf s' := by
  unfold find
  conv_lhs => rw [wf.fix_eq]
  split
  · simp_all
  · rename_i heq
    rw [h, Sum.inr.injEq] at heq
    rw [heq]

/-- The stream produced by corecursion: read off heads by running the search `find`. -/
def build (step : Step α β) (wf : WellFounded (Silent step)) : β → Stream' α :=
  Stream'.corec (fun s => (find step wf s).1) (fun s => (find step wf s).2)

theorem build_emit {step : Step α β} {wf : WellFounded (Silent step)} {s : β} {a : α} {s' : β}
    (h : step s = Sum.inl (a, s')) :
    build step wf s = Stream'.cons a (build step wf s') := by
  unfold build
  rw [Stream'.corec_eq]
  simp only [find_emit h]

theorem build_skip {step : Step α β} {wf : WellFounded (Silent step)} {s s' : β}
    (h : step s = Sum.inr s') : build step wf s = build step wf s' := by
  unfold build
  conv_lhs => rw [Stream'.corec_eq]
  conv_rhs => rw [Stream'.corec_eq]
  simp only [find_skip h]

end SearchCorec

open SearchCorec

/-! ### `evens`: productive with a *bounded* search (at most one silent step). -/

/-- Seed dynamics for `evens`: at an even `n`, emit `n` and continue from `n+1`; at an odd `n`,
silently advance to `n+1`. -/
def evensStep : Step ℕ ℕ := fun n => if n % 2 = 0 then Sum.inl (n, n + 1) else Sum.inr (n + 1)

theorem evens_wf : WellFounded (Silent evensStep) := by
  have hsub : Subrelation (Silent evensStep) (InvImage (· < ·) (fun n : ℕ => n % 2)) := by
    intro s' s h
    simp only [Silent, evensStep] at h
    split at h
    · simp at h
    · rename_i hodd
      simp only [Sum.inr.injEq] at h
      subst h
      change (s + 1) % 2 < s % 2
      omega
  exact hsub.wf (InvImage.wf _ Nat.lt_wfRel.wf)

/-- The stream of even numbers `≥ n`. -/
def evens (n : ℕ) : Stream' ℕ := build evensStep evens_wf n

/-- `evens` satisfies its intended (non-terminating) recursive equation. -/
theorem evens_eq (n : ℕ) :
    evens n = if n % 2 = 0 then Stream'.cons n (evens (n + 1)) else evens (n + 1) := by
  unfold evens
  by_cases h : n % 2 = 0
  · have hs : evensStep n = Sum.inl (n, n + 1) := by simp [evensStep, h]
    rw [if_pos h, build_emit hs]
  · have hs : evensStep n = Sum.inr (n + 1) := by simp [evensStep, h]
    rw [if_neg h, build_skip hs]

/-! ### `primes`: productive with an *unbounded* search. Productivity is a genuine theorem —
the infinitude of primes (`Nat.exists_infinite_primes`). -/

/-- Seed dynamics for `primes`: at a prime `n`, emit `n`; otherwise silently advance. -/
def primesStep : Step ℕ ℕ := fun n => if n.Prime then Sum.inl (n, n + 1) else Sum.inr (n + 1)

theorem primes_wf : WellFounded (Silent primesStep) := by
  have hsub : Subrelation (Silent primesStep)
      (InvImage (· < ·) (fun n : ℕ => Nat.find (Nat.exists_infinite_primes n) - n)) := by
    intro s' s h
    simp only [Silent, primesStep] at h
    split at h
    · simp at h
    · rename_i hns
      simp only [Sum.inr.injEq] at h
      subst h
      change Nat.find (Nat.exists_infinite_primes (s + 1)) - (s + 1)
           < Nat.find (Nat.exists_infinite_primes s) - s
      have h1 := Nat.find_spec (Nat.exists_infinite_primes s)
      have h6 := Nat.find_spec (Nat.exists_infinite_primes (s + 1))
      have h1' : s ≤ Nat.find (Nat.exists_infinite_primes s) := h1.1
      have h6' : s + 1 ≤ Nat.find (Nat.exists_infinite_primes (s + 1)) := h6.1
      have h3 : Nat.find (Nat.exists_infinite_primes s) ≠ s := by
        rintro he; rw [he] at h1; exact hns h1.2
      have h5 : Nat.find (Nat.exists_infinite_primes (s + 1))
          ≤ Nat.find (Nat.exists_infinite_primes s) :=
        Nat.find_min' (Nat.exists_infinite_primes (s + 1)) ⟨by omega, h1.2⟩
      omega
  exact hsub.wf (InvImage.wf _ Nat.lt_wfRel.wf)

/-- The stream of primes `≥ n`. -/
def primes (n : ℕ) : Stream' ℕ := build primesStep primes_wf n

/-- `primes` satisfies its intended (non-terminating) recursive equation. -/
theorem primes_eq (n : ℕ) :
    primes n = if n.Prime then Stream'.cons n (primes (n + 1)) else primes (n + 1) := by
  unfold primes
  by_cases h : n.Prime
  · have hs : primesStep n = Sum.inl (n, n + 1) := by simp [primesStep, h]
    rw [if_pos h, build_emit hs]
  · have hs : primesStep n = Sum.inr (n + 1) := by simp [primesStep, h]
    rw [if_neg h, build_skip hs]

/-! ### The *contractive* case is the special case "no silent steps".

`fib` carries the finite state `(a, b)` and always emits, so `Silent` is the empty relation
and productivity is trivial. This is the same `build` combinator with a synthesized state seed. -/

/-- Seed dynamics for the Fibonacci stream: from state `(a, b)` emit `a`, advance to `(b, a+b)`.
There is never a silent step. -/
def fibStep : Step ℕ (ℕ × ℕ) := fun (a, b) => Sum.inl (a, (b, a + b))

theorem fib_wf : WellFounded (Silent fibStep) := by
  refine ⟨fun p => ⟨p, fun q h => ?_⟩⟩
  obtain ⟨a, b⟩ := p
  simp [Silent, fibStep] at h

/-- The Fibonacci stream starting from the pair `(a, b)`. -/
def fib (a b : ℕ) : Stream' ℕ := build fibStep fib_wf (a, b)

/-- `fib` satisfies the state-machine equation, with no productivity side condition. -/
theorem fib_eq (a b : ℕ) : fib a b = Stream'.cons a (fib b (a + b)) := by
  unfold fib
  exact build_emit rfl

/-! ### `merge`: contractive (always emits), seed is the pair of streams. -/

/-- Seed dynamics for `merge`: emit the smaller head, advance that stream. Always emits. -/
def mergeStep : Step ℕ (Stream' ℕ × Stream' ℕ) := fun (xs, ys) =>
  if xs.head ≤ ys.head then Sum.inl (xs.head, (xs.tail, ys)) else Sum.inl (ys.head, (xs, ys.tail))

theorem mergeStep_wf : WellFounded (Silent mergeStep) := by
  constructor
  rintro ⟨xs, ys⟩
  refine Acc.intro _ (fun q h => ?_)
  simp only [Silent, mergeStep] at h
  split at h <;> simp at h

/-- The merge of two streams. -/
def merge (xs ys : Stream' ℕ) : Stream' ℕ := build mergeStep mergeStep_wf (xs, ys)

theorem merge_eq (xs ys : Stream' ℕ) :
    merge xs ys = if xs.head ≤ ys.head then Stream'.cons xs.head (merge xs.tail ys)
      else Stream'.cons ys.head (merge xs ys.tail) := by
  unfold merge
  by_cases h : xs.head ≤ ys.head
  · have hs : mergeStep (xs, ys) = Sum.inl (xs.head, (xs.tail, ys)) := by simp [mergeStep, h]
    rw [if_pos h, build_emit hs]
  · have hs : mergeStep (xs, ys) = Sum.inl (ys.head, (xs, ys.tail)) := by simp [mergeStep, h]
    rw [if_neg h, build_emit hs]

theorem merge_head (xs ys : Stream' ℕ) :
    (merge xs ys).head = if xs.head ≤ ys.head then xs.head else ys.head := by
  by_cases h : xs.head ≤ ys.head
  · rw [merge_eq, if_pos h, if_pos h, Stream'.head_cons]
  · rw [merge_eq, if_neg h, if_neg h, Stream'.head_cons]

theorem merge_tail (xs ys : Stream' ℕ) :
    (merge xs ys).tail = if xs.head ≤ ys.head then merge xs.tail ys else merge xs ys.tail := by
  by_cases h : xs.head ≤ ys.head
  · rw [merge_eq, if_pos h, if_pos h, Stream'.tail_cons]
  · rw [merge_eq, if_neg h, if_neg h, Stream'.tail_cons]

/-! ### `mulMerge`: the self-reference sits under `merge` (a *causal* combinator), so the seed
must be a syntactic expression tree of `merge`s ending in a `mulMerge`. The defining equation is
recovered by a bisimulation, `mulMergeSt (mrg a b) = merge a (mulMergeSt b)`. -/

/-- States reachable from `mulMerge`: a stack of pending `merge` buffers (`mrg`) on top of a
`mulMerge` of two streams (`mul`). -/
inductive MulSt where
  | mul : Stream' ℕ → Stream' ℕ → MulSt
  | mrg : Stream' ℕ → MulSt → MulSt

/-- One emission step on a `MulSt`. Structural recursion on the state (each `mrg` peeks the head
of its sub-state); always emits, so the search never stalls. -/
def mulStep : MulSt → ℕ × MulSt
  | .mul xs ys => (xs.head * ys.head, .mrg (xs.tail.map (fun x => x * ys.head)) (.mul xs ys.tail))
  | .mrg a b =>
    if a.head ≤ (mulStep b).1 then (a.head, .mrg a.tail b)
    else ((mulStep b).1, .mrg a (mulStep b).2)

theorem mulStep_mul (xs ys : Stream' ℕ) :
    mulStep (.mul xs ys) =
      (xs.head * ys.head, .mrg (xs.tail.map (fun x => x * ys.head)) (.mul xs ys.tail)) := by
  simp only [mulStep]

theorem mulStep_mrg (a : Stream' ℕ) (b : MulSt) :
    mulStep (.mrg a b) = if a.head ≤ (mulStep b).1 then (a.head, .mrg a.tail b)
      else ((mulStep b).1, .mrg a (mulStep b).2) := by
  simp only [mulStep]

/-- Seed dynamics for `mulMerge`: run `mulStep`; it always emits. -/
def mulMergeStep : Step ℕ MulSt := fun st => Sum.inl (mulStep st)

theorem mulMergeStep_wf : WellFounded (Silent mulMergeStep) := by
  constructor
  intro p
  refine Acc.intro _ (fun q h => ?_)
  simp [Silent, mulMergeStep] at h

/-- The stream denoted by a `MulSt` state. -/
def mulMergeSt (st : MulSt) : Stream' ℕ := build mulMergeStep mulMergeStep_wf st

/-- The "sorted products" stream: `xs.head * ys.head`, then merge the rest. -/
def mulMerge (xs ys : Stream' ℕ) : Stream' ℕ := mulMergeSt (.mul xs ys)

theorem mulMergeSt_eq (st : MulSt) :
    mulMergeSt st = Stream'.cons (mulStep st).1 (mulMergeSt (mulStep st).2) := by
  unfold mulMergeSt
  exact build_emit rfl

theorem mulMergeSt_head (st : MulSt) : (mulMergeSt st).head = (mulStep st).1 := by
  rw [mulMergeSt_eq, Stream'.head_cons]

theorem mulMergeSt_tail (st : MulSt) : (mulMergeSt st).tail = mulMergeSt (mulStep st).2 := by
  rw [mulMergeSt_eq, Stream'.tail_cons]

/-- Key bisimulation: a `mrg` state denotes exactly the `merge` of its buffer with the rest.
This is where "self-reference under the causal combinator `merge`" is discharged. -/
theorem mulMergeSt_mrg (a : Stream' ℕ) (b : MulSt) :
    mulMergeSt (.mrg a b) = merge a (mulMergeSt b) := by
  refine Stream'.eq_of_bisim
    (fun s1 s2 => ∃ a b, s1 = mulMergeSt (.mrg a b) ∧ s2 = merge a (mulMergeSt b))
    ?_ ⟨a, b, rfl, rfl⟩
  rintro _ _ ⟨a, b, rfl, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [mulMergeSt_head, merge_head, mulMergeSt_head, mulStep_mrg]
    split_ifs <;> rfl
  · rw [mulMergeSt_tail, merge_tail, mulMergeSt_head]
    by_cases hle : a.head ≤ (mulStep b).1
    · rw [if_pos hle]
      refine ⟨a.tail, b, ?_, rfl⟩
      rw [mulStep_mrg, if_pos hle]
    · rw [if_neg hle, mulMergeSt_tail]
      refine ⟨a, (mulStep b).2, ?_, rfl⟩
      rw [mulStep_mrg, if_neg hle]

/-- `mulMerge` satisfies its intended (non-terminating) recursive equation. -/
theorem mulMerge_eq (xs ys : Stream' ℕ) :
    mulMerge xs ys = Stream'.cons (xs.head * ys.head)
      (merge (xs.tail.map (fun x => x * ys.head)) (mulMerge xs ys.tail)) := by
  unfold mulMerge
  rw [mulMergeSt_eq (.mul xs ys), mulStep_mul]
  dsimp only
  rw [mulMergeSt_mrg]
