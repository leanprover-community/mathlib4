module

public import Mathlib.Tactic.Simproc.ExistsAndEq

universe u v

variable (α : Type u) (β : Type v)

example (P Q : α → Prop) (a : α) (hp : P a) (hq : Q a) :
    ∃ b : α, (P b ∧ b = a) ∧ Q b := by
  simp only [existsAndEq]
  guard_target = (P a ∧ True) ∧ Q a
  exact ⟨⟨hp, trivial⟩, hq⟩

example (a : α) : ∃ b : α, b = a := by
  simp only [existsAndEq]

/--
error: `simp` made no progress
-/
#guard_msgs in
example (f : α → α) : ∃ a : α, a = f a := by
  simp only [existsAndEq]

/--
error: `simp` made no progress
-/
#guard_msgs in
example {β : α → Type v} (a : α) :
    ∃ x, ∃ y : β x, x = a := by
  simp only [existsAndEq]

example (f : β → α) {P Q : β → Prop} :
    (∃ y b, P b ∧ f b = y ∧ Q b) ↔ ∃ b, P b ∧ Q b := by
  simp only [existsAndEq, true_and]

example (f : β → α) {P Q : β → Prop} :
    (∃ x b, P b ∧ (∃ c, f c = x) ∧ (∃ d, Q d ∧ f d = x) ∧ Q b) =
    ∃ b c, P b ∧ f c = f c ∧ (∃ d, Q d ∧ f d = f c) ∧ Q b := by
  simp only [existsAndEq]

example (f : β → α) {P : α → Prop} :
    (∃ a, P a ∧ ∃ b, a = f b) ↔ ∃ b, P (f b) := by
  simp only [existsAndEq, and_true]

-- The simproc should not trigger on `a = a'` when `a'` depends on `a`
/--
error: `simp` made no progress
-/
#guard_msgs in
example {α : Type} : ∃ a : α, ∃ b : α → α, b a = a := by
  simp only [existsAndEq]

-- lemmas like `Subtype.exists` and `Prod.exists` prevent `existsAndEq`
-- from working as a post simproc, so it is a pre simproc.
/--
error: unsolved goals
α : Type u
β : Type v
P Q : α × β → Prop
a : α × β
⊢ (∃ a_1 b, (P (a_1, b) ∧ (a_1, b) = a) ∧ Q (a_1, b)) ↔ P a ∧ Q a
-/
#guard_msgs in
set_option linter.unusedSimpArgs false in
example (P Q : α × β → Prop) (a : α × β) :
    (∃ b : (α × β), (P b ∧ b = a) ∧ Q b) ↔ P a ∧ Q a := by
  simp only [Prod.exists, existsAndEq]

example (P Q : α × β → Prop) (a : α × β) :
    (∃ b : (α × β), (P b ∧ b = a) ∧ Q b) ↔ P a ∧ Q a := by
  simp

-- # Metavariables in goals

-- The simproc must return a closed proof even when the goal contains metavariables, which is what
-- `aesop` presents to it: here the goal is `∃ a : Nat, a = Nat.succ ?b ∧ 0 < ?b`.
open Lean Meta Qq in
#eval show MetaM Unit from do
  let b : Q(Nat) ← mkFreshExprMVarQ q(Nat)
  let e : Q(Prop) := q(∃ a : Nat, a = Nat.succ $b ∧ 0 < $b)
  let simprocs ← ({} : Simprocs).add ``ExistsAndEq.existsAndEq (post := false)
  let (r, _) ← Simp.main e (← Simp.mkContext) (methods := Simp.mkDefaultMethodsCore #[simprocs])
  let some pf := r.proof? | throwError "the simproc did not fire"
  let pf ← instantiateMVars pf
  let leftover := (← getMVars pf).filter (· != b.mvarId!)
  unless leftover.isEmpty do
    throwError "metavariables left in the proof: {leftover.map mkMVar}\n{pf}"

-- Metavariables may depend on each other: here `?f : Nat → ?β`, and `?β` occurs in the goal too
-- (as it arises when `simpa using` simplifies the type of a term whose implicit arguments are not
-- determined yet). They have to be handled consistently.
example : ∃ (β : Type) (f : Nat → β), ∃ b, f 0 = b := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left 2
  simp only [existsAndEq]
  · exact Nat
  · exact id

-- # Equations in binder types of dependent quantifiers

example (a' : α) (P : (a : α) → a = a' → Prop) :
    (∃ a : α, ∃ (h : a = a'), P a h) ↔ ∃ (h : a' = a'), P a' h := by
  simp only [existsAndEq]

example (a' : α) (Q : α → Prop) (P : (a : α) → a = a' ∧ Q a → Prop) :
    (∃ a : α, ∃ (h : a = a' ∧ Q a), P a h) ↔ ∃ (h : a' = a' ∧ Q a'), P a' h := by
  simp only [existsAndEq]

example (a' : α) (Q R : α → Prop) (P : (a : α) → Q a ∧ a = a' ∧ R a → Prop) :
    (∃ a : α, ∃ (h : Q a ∧ a = a' ∧ R a), P a h) ↔
      ∃ (h : Q a' ∧ a' = a' ∧ R a'), P a' h := by
  simp only [existsAndEq]

example (f : β → α) (Q : β → Prop) (P : (a : α) → (∃ b : β, Q b ∧ a = f b) → Prop) :
    (∃ a : α, ∃ (h : ∃ b : β, Q b ∧ a = f b), P a h) ↔
      ∃ b : β, ∃ (h : Q b ∧ f b = f b), P (f b) ⟨b, h⟩ := by
  simp only [existsAndEq]

example (a' : α) (R Q : α → Prop) (S : (a : α) → a = a' ∧ Q a → Prop) :
    (∃ a : α, R a ∧ ∃ (h : a = a' ∧ Q a), S a h) ↔
      R a' ∧ ∃ (h : a' = a' ∧ Q a'), S a' h := by
  simp only [existsAndEq]

example (a' : α) (Q : α → Prop) (S : (a : α) → a = a' ∧ Q a → Prop)
    (P : (a : α) → (∃ h : a = a' ∧ Q a, S a h) → Prop) :
    (∃ a : α, ∃ (h : ∃ h' : a = a' ∧ Q a, S a h'), P a h) ↔
      ∃ (h : ∃ h' : a' = a' ∧ Q a', S a' h'), P a' h := by
  simp only [existsAndEq]

-- From https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/potential.20simp_procs/near/617574483
example (f : Nat → Nat) (hf : ∀ x, f x < 5)
    (g : (n : Nat) → n < 5 → Nat)
    (hfg : ∀ x, g (f x) (hf x) = x)
    (c : Nat) (s : Nat → Prop) :
    (∃ x, ∃ h : ∃ y, s y ∧ f y = x, g x (by grind) = c) ↔ s c := by
   -- The body depends on `h` so `exists_prop` is not applicable
  fail_if_success simp only [exists_prop]
  simp only [existsAndEq]
  guard_target = (∃ y, ∃ _ : s y ∧ True, g (f y) (hf y) = c) ↔ s c
  grind

-- # `forallImpEq`

example (P Q : α → Prop) (a : α) :
    (∀ b : α, P b → b = a → Q b) ↔ (P a → a = a → Q a) := by
  simp only [forallImpEq]

example (P Q : α → Prop) (a : α) :
    (∀ b : α, P b → a = b → Q b) ↔ (P a → a = a → Q a) := by
  simp only [forallImpEq]

example (P : α → Prop) (a : α) (h : P a) : ∀ b : α, b = a → P b := by
  simp only [forallImpEq]
  exact fun _ ↦ h

/--
error: `simp` made no progress
-/
#guard_msgs in
example (f : α → α) (P : α → Prop) : ∀ a : α, a = f a → P a := by
  simp only [forallImpEq]

-- The hypothesis must be a hypothesis, not hidden under a negation or a premise.
/--
error: `simp` made no progress
-/
#guard_msgs in
example (P : α → Prop) (a' : α) : ∀ a : α, ((a = a' → False) → P a) := by
  simp only [forallImpEq]

-- `a'` can't depend on a binder that stays in place
/--
error: `simp` made no progress
-/
#guard_msgs in
example {γ : α → Type v} (f : ∀ a, γ a → α) (P : α → Prop) :
    ∀ a : α, ∀ c : γ a, a = f a c → P a := by
  simp only [forallImpEq]

-- nor on a binder whose type depends on a binder that stays in place
/--
error: `simp` made no progress
-/
#guard_msgs in
example {γ : α → Type v} (δ : ∀ a, γ a → Type v) (f : ∀ a c, δ a c → α) (P : α → Prop) :
    ∀ a : α, ∀ c : γ a, ∀ d : δ a c, a = f a c d → P a := by
  simp only [forallImpEq]

example (f : β → α) (P Q : α → Prop) :
    (∀ a, P a → ∀ b, a = f b → Q a) ↔ ∀ b, P (f b) → f b = f b → Q (f b) := by
  simp only [forallImpEq]

example (f : β → α) (P Q : α → Prop) :
    (∀ a, P a → ∀ b, f b = a → Q a) ↔ ∀ b, P (f b) → Q (f b) := by
  simp only [forallImpEq, true_implies]

example (f : β → α) (P : β → Prop) (Q : α → Prop) :
    (∀ a b, P b → f b = a → Q a) ↔ ∀ b, P b → Q (f b) := by
  simp only [forallImpEq, true_implies]

-- Binders that don't depend on `a` are moved to the front, keeping their order.
example (f : β → β → α) (P : α → β → Prop) (Q : α → Prop) :
    (∀ a b, P a b → ∀ c, a = f b c → Q a) = ∀ b c, P (f b c) b → f b c = f b c → Q (f b c) := by
  simp only [forallImpEq]

-- The hypothesis can be used by the rest of the statement.
example (a' : α) (P : (a : α) → a = a' → Prop) :
    (∀ a : α, ∀ (h : a = a'), P a h) ↔ ∀ (h : a' = a'), P a' h := by
  simp only [forallImpEq]

example (a' : α) (P : (a : α) → a' = a → Prop) :
    (∀ a : α, ∀ (h : a' = a), P a h) ↔ ∀ (h : a' = a'), P a' h := by
  simp only [forallImpEq]

-- Binders that depend on `a` stay in place.
example {γ : α → Type v} (a' : α) (P : (a : α) → γ a → Prop) :
    (∀ a : α, ∀ c : γ a, a = a' → P a c) ↔ ∀ c : γ a', a' = a' → P a' c := by
  simp only [forallImpEq]

example {γ : α → Type v} (f : β → α) (P : (a : α) → γ a → β → Prop) :
    (∀ a : α, ∀ c : γ a, ∀ b, a = f b → P a c b) ↔ ∀ b, ∀ c : γ (f b), f b = f b → P (f b) c b := by
  simp only [forallImpEq]

-- Implicit and instance binders
example (P : α → Prop) (a' : α) :
    (∀ {a : α}, a = a' → P a) ↔ (a' = a' → P a') := by
  simp only [forallImpEq]

-- Interaction with `simp`
example (s : α → Prop) (f : α → β) (P : β → Prop) :
    (∀ b, ∀ a, s a → f a = b → P b) ↔ ∀ a, s a → P (f a) := by
  simp

example (P Q : α × β → Prop) (a : α × β) :
    (∀ b : α × β, P b → b = a → Q b) ↔ (P a → Q a) := by
  simp

-- # Metavariables in goals

open Lean Meta Qq in
#eval show MetaM Unit from do
  let b : Q(Nat) ← mkFreshExprMVarQ q(Nat)
  let e : Q(Prop) := q(∀ a : Nat, a = Nat.succ $b → 0 < $b)
  let simprocs ← ({} : Simprocs).add ``ForallImpEq.forallImpEq (post := false)
  let (r, _) ← Simp.main e (← Simp.mkContext) (methods := Simp.mkDefaultMethodsCore #[simprocs])
  let some pf := r.proof? | throwError "the simproc did not fire"
  let pf ← instantiateMVars pf
  let leftover := (← getMVars pf).filter (· != b.mvarId!)
  unless leftover.isEmpty do
    throwError "metavariables left in the proof: {leftover.map mkMVar}\n{pf}"
