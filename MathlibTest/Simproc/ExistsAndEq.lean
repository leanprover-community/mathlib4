import Mathlib.Tactic.Simproc.ExistsAndEq

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

/-! ### Equations in binder types of dependent quantifiers

`∃ h : T, body` behaves like `T ∧ body`, except that `body` may refer to the proof `h`. When the
equation is found inside `T`, the quantifier stays in place and `a` is substituted in `T` as
everywhere else. A quantifier inside `T` that `a'` depends on is moved to the front, and the proof
that `body` expects is rebuilt from the remaining one by putting the witness back (the *anchor*). -/

-- the binder type is exactly the equation
example (a' : α) (P : (a : α) → a = a' → Prop) :
    (∃ a : α, ∃ (h : a = a'), P a h) ↔ ∃ (h : a' = a'), P a' h := by
  simp only [existsAndEq]

example (a' : α) (P : (a : α) → a' = a → Prop) :
    (∃ a : α, ∃ (h : a' = a), P a h) ↔ ∃ (h : a' = a'), P a' h := by
  simp only [existsAndEq]

-- the equation stays in the binder type, next to the other conjuncts
example (a' : α) (Q : α → Prop) (P : (a : α) → a = a' ∧ Q a → Prop) :
    (∃ a : α, ∃ (h : a = a' ∧ Q a), P a h) ↔ ∃ (h : a' = a' ∧ Q a'), P a' h := by
  simp only [existsAndEq]

example (a' : α) (Q : α → Prop) (P : (a : α) → Q a ∧ a' = a → Prop) :
    (∃ a : α, ∃ (h : Q a ∧ a' = a), P a h) ↔ ∃ (h : Q a' ∧ a' = a'), P a' h := by
  simp only [existsAndEq]

-- conjuncts on both sides of the equation are preserved
example (a' : α) (Q R : α → Prop) (P : (a : α) → Q a ∧ a = a' ∧ R a → Prop) :
    (∃ a : α, ∃ (h : Q a ∧ a = a' ∧ R a), P a h) ↔
      ∃ (h : Q a' ∧ a' = a' ∧ R a'), P a' h := by
  simp only [existsAndEq]

-- a quantifier inside the binder type is moved outside, since `a'` may depend on its variable;
-- its witness is put back into the proof that the body expects
example (f : β → α) (Q : β → Prop) (P : (a : α) → (∃ b : β, Q b ∧ a = f b) → Prop) :
    (∃ a : α, ∃ (h : ∃ b : β, Q b ∧ a = f b), P a h) ↔
      ∃ b : β, ∃ (h : Q b ∧ f b = f b), P (f b) ⟨b, h⟩ := by
  simp only [existsAndEq]

-- ... also when the binder type is the quantified equation alone
example (f : β → α) (P : (a : α) → (∃ b : β, a = f b) → Prop) :
    (∃ a : α, ∃ (h : ∃ b : β, a = f b), P a h) ↔
      ∃ b : β, ∃ (h : f b = f b), P (f b) ⟨b, h⟩ := by
  simp only [existsAndEq]

-- combined with hoisting on the main path
example (f : β → α) (Q : α → Prop) (P : (a : α) → (b : β) → a = f b ∧ Q a → Prop) :
    (∃ a : α, ∃ b : β, ∃ (h : a = f b ∧ Q a), P a b h) ↔
      ∃ b : β, ∃ (h : f b = f b ∧ Q (f b)), P (f b) b h := by
  simp only [existsAndEq]

-- conjunctions on the main path are traversed as well
example (a' : α) (R Q : α → Prop) (S : (a : α) → a = a' ∧ Q a → Prop) :
    (∃ a : α, R a ∧ ∃ (h : a = a' ∧ Q a), S a h) ↔
      R a' ∧ ∃ (h : a' = a' ∧ Q a'), S a' h := by
  simp only [existsAndEq]

-- binder types of nested dependent quantifiers are searched as well
example (a' : α) (Q : α → Prop) (S : (a : α) → a = a' ∧ Q a → Prop)
    (P : (a : α) → (∃ h : a = a' ∧ Q a, S a h) → Prop) :
    (∃ a : α, ∃ (h : ∃ h' : a = a' ∧ Q a, S a h'), P a h) ↔
      ∃ (h : ∃ h' : a' = a' ∧ Q a', S a' h'), P a' h := by
  simp only [existsAndEq]

-- the rewrite composes with the default simp set
example (a' : α) (Q : α → Prop) (P : (a : α) → a = a' ∧ Q a → Prop) :
    (∃ a : α, ∃ (h : a = a' ∧ Q a), P a h) ↔ ∃ (h : a' = a' ∧ Q a'), P a' h := by
  simp

-- The simproc is not applicable when the binder type provides no usable equation.
/--
error: `simp` made no progress
-/
#guard_msgs in
example (Q : α → Prop) (P : (a : α) → Q a → Prop) :
    ∃ a : α, ∃ (h : Q a), P a h := by
  simp only [existsAndEq]

/--
error: `simp` made no progress
-/
#guard_msgs in
example (f : α → α) (P : (a : α) → a = f a → Prop) :
    ∃ a : α, ∃ (h : a = f a), P a h := by
  simp only [existsAndEq]

-- The body of a quantifier whose binder type mentions `a` is not entered: `∃ h : Q a, ⋯` cannot
-- be moved outside, so an equation in its body cannot eliminate `∃ a`.
/--
error: `simp` made no progress
-/
#guard_msgs in
example (a' : α) (Q : α → Prop) (P : (a : α) → Q a → Prop) :
    ∃ a : α, ∃ (h : Q a), P a h ∧ a = a' := by
  simp only [existsAndEq]
