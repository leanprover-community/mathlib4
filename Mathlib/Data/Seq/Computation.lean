/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Coinductive formalization of unbounded computations.
-/
import Mathlib.Data.Stream.Init
import Mathlib.Tactic.Common

#align_import data.seq.computation from "leanprover-community/mathlib"@"1f0096e6caa61e9c849ec2adbd227e960e9dff58"

/-!
# Coinductive formalization of unbounded computations.

This file provides a `Computation` type where `Computation α` is the type of
unbounded computations returning `α`.
-/

open Function

universe u v w

/-
coinductive Computation (α : Type u) : Type u
| pure : α → Computation α
| think : Computation α → Computation α
-/
/-- `Computation α` is the type of unbounded computations returning `α`.
  An element of `Computation α` is an infinite sequence of `Option α` such
  that if `f n = some a` for some `n` then it is constantly `some a` after that. -/
def Computation (α : Type u) : Type u :=
  { f : Stream' (Option α) // ∀ ⦃n a⦄, f n = some a → f (n + 1) = some a }
#align computation Computation

namespace Computation

variable {α : Type u} {β : Type v} {γ : Type w}

-- constructors
/-- `pure a` is the computation that immediately terminates with result `a`. -/
-- Porting note: `return` is reserved, so changed to `pure`
def pure (a : α) : Computation α :=
  ⟨Stream'.const (some a), fun _ _ => id⟩
#align computation.return Computation.pure

instance : CoeTC α (Computation α) :=
  ⟨pure⟩

-- note [use has_coe_t]
/-- `think c` is the computation that delays for one "tick" and then performs
  computation `c`. -/
def think (c : Computation α) : Computation α :=
  ⟨Stream'.cons none c.1, fun n a h => by
    cases' n with n
    · contradiction
    · exact c.2 h⟩
#align computation.think Computation.think

/-- `thinkN c n` is the computation that delays for `n` ticks and then performs
  computation `c`. -/
def thinkN (c : Computation α) : ℕ → Computation α
  | 0 => c
  | n + 1 => think (thinkN c n)
set_option linter.uppercaseLean3 false in
#align computation.thinkN Computation.thinkN

-- check for immediate result
/-- `head c` is the first step of computation, either `some a` if `c = pure a`
  or `none` if `c = think c'`. -/
def head (c : Computation α) : Option α :=
  c.1.head
#align computation.head Computation.head

-- one step of computation
/-- `tail c` is the remainder of computation, either `c` if `c = pure a`
  or `c'` if `c = think c'`. -/
def tail (c : Computation α) : Computation α :=
  ⟨c.1.tail, fun _ _ h => c.2 h⟩
#align computation.tail Computation.tail

/-- `empty α` is the computation that never returns, an infinite sequence of
  `think`s. -/
def empty (α) : Computation α :=
  ⟨Stream'.const none, fun _ _ => id⟩
#align computation.empty Computation.empty

instance : Inhabited (Computation α) :=
  ⟨empty _⟩

/-- `runFor c n` evaluates `c` for `n` steps and returns the result, or `none`
  if it did not terminate after `n` steps. -/
def runFor : Computation α → ℕ → Option α :=
  Subtype.val
#align computation.run_for Computation.runFor

/-- `destruct c` is the destructor for `Computation α` as a coinductive type.
  It returns `inl a` if `c = pure a` and `inr c'` if `c = think c'`. -/
def destruct (c : Computation α) : Sum α (Computation α) :=
  match c.1 0 with
  | none => Sum.inr (tail c)
  | some a => Sum.inl a
#align computation.destruct Computation.destruct

/-- `run c` is an unsound meta function that runs `c` to completion, possibly
  resulting in an infinite loop in the VM. -/
unsafe def run : Computation α → α
  | c =>
    match destruct c with
    | Sum.inl a => a
    | Sum.inr ca => run ca
#align computation.run Computation.run

theorem destruct_eq_pure {s : Computation α} {a : α} : destruct s = Sum.inl a → s = pure a := by
  dsimp [destruct]
  induction' f0 : s.1 0 with _ <;> intro h
  · contradiction
  · apply Subtype.eq
    funext n
    induction' n with n IH
    · injection h with h'
      rwa [h'] at f0
    · exact s.2 IH
#align computation.destruct_eq_ret Computation.destruct_eq_pure

theorem destruct_eq_think {s : Computation α} {s'} : destruct s = Sum.inr s' → s = think s' := by
  dsimp [destruct]
  induction' f0 : s.1 0 with a' <;> intro h
  · injection h with h'
    rw [← h']
    cases' s with f al
    apply Subtype.eq
    dsimp [think, tail]
    rw [← f0]
    exact (Stream'.eta f).symm
  · contradiction
#align computation.destruct_eq_think Computation.destruct_eq_think

@[simp]
theorem destruct_pure (a : α) : destruct (pure a) = Sum.inl a :=
  rfl
#align computation.destruct_ret Computation.destruct_pure

@[simp]
theorem destruct_think : ∀ s : Computation α, destruct (think s) = Sum.inr s
  | ⟨_, _⟩ => rfl
#align computation.destruct_think Computation.destruct_think

@[simp]
theorem destruct_empty : destruct (empty α) = Sum.inr (empty α) :=
  rfl
#align computation.destruct_empty Computation.destruct_empty

@[simp]
theorem head_pure (a : α) : head (pure a) = some a :=
  rfl
#align computation.head_ret Computation.head_pure

@[simp]
theorem head_think (s : Computation α) : head (think s) = none :=
  rfl
#align computation.head_think Computation.head_think

@[simp]
theorem head_empty : head (empty α) = none :=
  rfl
#align computation.head_empty Computation.head_empty

@[simp]
theorem tail_pure (a : α) : tail (pure a) = pure a :=
  rfl
#align computation.tail_ret Computation.tail_pure

@[simp]
theorem tail_think (s : Computation α) : tail (think s) = s := by
  cases' s with f al; apply Subtype.eq; dsimp [tail, think]
#align computation.tail_think Computation.tail_think

@[simp]
theorem tail_empty : tail (empty α) = empty α :=
  rfl
#align computation.tail_empty Computation.tail_empty

theorem think_empty : empty α = think (empty α) :=
  destruct_eq_think destruct_empty
#align computation.think_empty Computation.think_empty

/-- Recursion principle for computations, compare with `List.recOn`. -/
def recOn {C : Computation α → Sort v} (s : Computation α) (h1 : ∀ a, C (pure a))
    (h2 : ∀ s, C (think s)) : C s :=
  match H : destruct s with
  | Sum.inl v => by
    rw [destruct_eq_pure H]
    apply h1
  | Sum.inr v => match v with
    | ⟨a, s'⟩ => by
      rw [destruct_eq_think H]
      apply h2
#align computation.rec_on Computation.recOn

/-- Corecursor constructor for `corec`-/
def Corec.f (f : β → Sum α β) : Sum α β → Option α × Sum α β
  | Sum.inl a => (some a, Sum.inl a)
  | Sum.inr b =>
    (match f b with
      | Sum.inl a => some a
      | Sum.inr _ => none,
      f b)
set_option linter.uppercaseLean3 false in
#align computation.corec.F Computation.Corec.f

/-- `corec f b` is the corecursor for `Computation α` as a coinductive type.
  If `f b = inl a` then `corec f b = pure a`, and if `f b = inl b'` then
  `corec f b = think (corec f b')`. -/
def corec (f : β → Sum α β) (b : β) : Computation α := by
  refine ⟨Stream'.corec' (Corec.f f) (Sum.inr b), fun n a' h => ?_⟩
  rw [Stream'.corec'_eq]
  change Stream'.corec' (Corec.f f) (Corec.f f (Sum.inr b)).2 n = some a'
  revert h; generalize Sum.inr b = o; revert o
  induction' n with n IH <;> intro o
  · change (Corec.f f o).1 = some a' → (Corec.f f (Corec.f f o).2).1 = some a'
    cases' o with _ b <;> intro h
    · exact h
    unfold Corec.f at *; split <;> simp_all
  · rw [Stream'.corec'_eq (Corec.f f) (Corec.f f o).2, Stream'.corec'_eq (Corec.f f) o]
    exact IH (Corec.f f o).2
#align computation.corec Computation.corec

/-- left map of `⊕` -/
def lmap (f : α → β) : Sum α γ → Sum β γ
  | Sum.inl a => Sum.inl (f a)
  | Sum.inr b => Sum.inr b
#align computation.lmap Computation.lmap

/-- right map of `⊕` -/
def rmap (f : β → γ) : Sum α β → Sum α γ
  | Sum.inl a => Sum.inl a
  | Sum.inr b => Sum.inr (f b)
#align computation.rmap Computation.rmap

attribute [simp] lmap rmap

-- Porting note: this was far less painful in mathlib3. There seem to be two issues;
-- firstly, in mathlib3 we have `corec.F._match_1` and it's the obvious map α ⊕ β → option α.
-- In mathlib4 we have `Corec.f.match_1` and it's something completely different.
-- Secondly, the proof that `Stream'.corec' (Corec.f f) (Sum.inr b) 0` is this function
-- evaluated at `f b`, used to be `rfl` and now is `cases, rfl`.
@[simp]
theorem corec_eq (f : β → Sum α β) (b : β) : destruct (corec f b) = rmap (corec f) (f b) := by
  dsimp [corec, destruct]
  rw [show Stream'.corec' (Corec.f f) (Sum.inr b) 0 =
    Sum.rec Option.some (fun _ ↦ none) (f b) by
    dsimp [Corec.f, Stream'.corec', Stream'.corec, Stream'.map, Stream'.get, Stream'.iterate]
    match (f b) with
    | Sum.inl x => rfl
    | Sum.inr x => rfl
    ]
  induction' h : f b with a b'; · rfl
  dsimp [Corec.f, destruct]
  apply congr_arg; apply Subtype.eq
  dsimp [corec, tail]
  rw [Stream'.corec'_eq, Stream'.tail_cons]
  dsimp [Corec.f]; rw [h]
#align computation.corec_eq Computation.corec_eq

section Bisim

variable (R : Computation α → Computation α → Prop)

/-- bisimilarity relation-/
local infixl:50 " ~ " => R

/-- Bisimilarity over a sum of `Computation`s-/
def BisimO : Sum α (Computation α) → Sum α (Computation α) → Prop
  | Sum.inl a, Sum.inl a' => a = a'
  | Sum.inr s, Sum.inr s' => R s s'
  | _, _ => False
#align computation.bisim_o Computation.BisimO

attribute [simp] BisimO

/-- Attribute expressing bisimilarity over two `Computation`s-/
def IsBisimulation :=
  ∀ ⦃s₁ s₂⦄, s₁ ~ s₂ → BisimO R (destruct s₁) (destruct s₂)
#align computation.is_bisimulation Computation.IsBisimulation

-- If two computations are bisimilar, then they are equal
theorem eq_of_bisim (bisim : IsBisimulation R) {s₁ s₂} (r : s₁ ~ s₂) : s₁ = s₂ := by
  apply Subtype.eq
  apply Stream'.eq_of_bisim fun x y => ∃ s s' : Computation α, s.1 = x ∧ s'.1 = y ∧ R s s'
  · dsimp [Stream'.IsBisimulation]
    intro t₁ t₂ e
    match t₁, t₂, e with
    | _, _, ⟨s, s', rfl, rfl, r⟩ =>
      suffices head s = head s' ∧ R (tail s) (tail s') from
        And.imp id (fun r => ⟨tail s, tail s', by cases s; rfl, by cases s'; rfl, r⟩) this
      have h := bisim r; revert r h
      apply recOn s _ _ <;> intro r' <;> apply recOn s' _ _ <;> intro a' r h
      · constructor <;> dsimp at h
        · rw [h]
        · rw [h] at r
          rw [tail_pure, tail_pure,h]
          assumption
      · rw [destruct_pure, destruct_think] at h
        exact False.elim h
      · rw [destruct_pure, destruct_think] at h
        exact False.elim h
      · simp_all
  · exact ⟨s₁, s₂, rfl, rfl, r⟩
#align computation.eq_of_bisim Computation.eq_of_bisim

end Bisim

-- It's more of a stretch to use ∈ for this relation, but it
-- asserts that the computation limits to the given value.
/-- Assertion that a `Computation` limits to a given value-/
protected def Mem (a : α) (s : Computation α) :=
  some a ∈ s.1
#align computation.mem Computation.Mem

instance : Membership α (Computation α) :=
  ⟨Computation.Mem⟩

theorem le_stable (s : Computation α) {a m n} (h : m ≤ n) : s.1 m = some a → s.1 n = some a := by
  cases' s with f al
  induction' h with n _ IH
  exacts [id, fun h2 => al (IH h2)]
#align computation.le_stable Computation.le_stable

theorem mem_unique {s : Computation α} {a b : α} : a ∈ s → b ∈ s → a = b
  | ⟨m, ha⟩, ⟨n, hb⟩ => by
    injection
      (le_stable s (le_max_left m n) ha.symm).symm.trans (le_stable s (le_max_right m n) hb.symm)
#align computation.mem_unique Computation.mem_unique

theorem Mem.left_unique : Relator.LeftUnique ((· ∈ ·) : α → Computation α → Prop) := fun _ _ _ =>
  mem_unique
#align computation.mem.left_unique Computation.Mem.left_unique

/-- `Terminates s` asserts that the computation `s` eventually terminates with some value. -/
class Terminates (s : Computation α) : Prop where
  /-- assertion that there is some term `a` such that the `Computation` terminates -/
  term : ∃ a, a ∈ s
#align computation.terminates Computation.Terminates

theorem terminates_iff (s : Computation α) : Terminates s ↔ ∃ a, a ∈ s :=
  ⟨fun h => h.1, Terminates.mk⟩
#align computation.terminates_iff Computation.terminates_iff

theorem terminates_of_mem {s : Computation α} {a : α} (h : a ∈ s) : Terminates s :=
  ⟨⟨a, h⟩⟩
#align computation.terminates_of_mem Computation.terminates_of_mem

theorem terminates_def (s : Computation α) : Terminates s ↔ ∃ n, (s.1 n).isSome :=
  ⟨fun ⟨⟨a, n, h⟩⟩ =>
    ⟨n, by
      dsimp [Stream'.get] at h
      rw [← h]
      exact rfl⟩,
    fun ⟨n, h⟩ => ⟨⟨Option.get _ h, n, (Option.eq_some_of_isSome h).symm⟩⟩⟩
#align computation.terminates_def Computation.terminates_def

theorem ret_mem (a : α) : a ∈ pure a :=
  Exists.intro 0 rfl
#align computation.ret_mem Computation.ret_mem

theorem eq_of_pure_mem {a a' : α} (h : a' ∈ pure a) : a' = a :=
  mem_unique h (ret_mem _)
#align computation.eq_of_ret_mem Computation.eq_of_pure_mem

instance ret_terminates (a : α) : Terminates (pure a) :=
  terminates_of_mem (ret_mem _)
#align computation.ret_terminates Computation.ret_terminates

theorem think_mem {s : Computation α} {a} : a ∈ s → a ∈ think s
  | ⟨n, h⟩ => ⟨n + 1, h⟩
#align computation.think_mem Computation.think_mem

instance think_terminates (s : Computation α) : ∀ [Terminates s], Terminates (think s)
  | ⟨⟨a, n, h⟩⟩ => ⟨⟨a, n + 1, h⟩⟩
#align computation.think_terminates Computation.think_terminates

theorem of_think_mem {s : Computation α} {a} : a ∈ think s → a ∈ s
  | ⟨n, h⟩ => by
    cases' n with n'
    · contradiction
    · exact ⟨n', h⟩
#align computation.of_think_mem Computation.of_think_mem

theorem of_think_terminates {s : Computation α} : Terminates (think s) → Terminates s
  | ⟨⟨a, h⟩⟩ => ⟨⟨a, of_think_mem h⟩⟩
#align computation.of_think_terminates Computation.of_think_terminates

theorem not_mem_empty (a : α) : a ∉ empty α := fun ⟨n, h⟩ => by contradiction
#align computation.not_mem_empty Computation.not_mem_empty

theorem not_terminates_empty : ¬Terminates (empty α) := fun ⟨⟨a, h⟩⟩ => not_mem_empty a h
#align computation.not_terminates_empty Computation.not_terminates_empty

theorem eq_empty_of_not_terminates {s} (H : ¬Terminates s) : s = empty α := by
  apply Subtype.eq; funext n
  induction' h : s.val n with _; · rfl
  refine absurd ?_ H; exact ⟨⟨_, _, h.symm⟩⟩
#align computation.eq_empty_of_not_terminates Computation.eq_empty_of_not_terminates

theorem thinkN_mem {s : Computation α} {a} : ∀ n, a ∈ thinkN s n ↔ a ∈ s
  | 0 => Iff.rfl
  | n + 1 => Iff.trans ⟨of_think_mem, think_mem⟩ (thinkN_mem n)
set_option linter.uppercaseLean3 false in
#align computation.thinkN_mem Computation.thinkN_mem

instance thinkN_terminates (s : Computation α) : ∀ [Terminates s] (n), Terminates (thinkN s n)
  | ⟨⟨a, h⟩⟩, n => ⟨⟨a, (thinkN_mem n).2 h⟩⟩
set_option linter.uppercaseLean3 false in
#align computation.thinkN_terminates Computation.thinkN_terminates

theorem of_thinkN_terminates (s : Computation α) (n) : Terminates (thinkN s n) → Terminates s
  | ⟨⟨a, h⟩⟩ => ⟨⟨a, (thinkN_mem _).1 h⟩⟩
set_option linter.uppercaseLean3 false in
#align computation.of_thinkN_terminates Computation.of_thinkN_terminates

/-- `Promises s a`, or `s ~> a`, asserts that although the computation `s`
  may not terminate, if it does, then the result is `a`. -/
def Promises (s : Computation α) (a : α) : Prop :=
  ∀ ⦃a'⦄, a' ∈ s → a = a'
#align computation.promises Computation.Promises

/-- `Promises s a`, or `s ~> a`, asserts that although the computation `s`
  may not terminate, if it does, then the result is `a`. -/
scoped infixl:50 " ~> " => Promises

theorem mem_promises {s : Computation α} {a : α} : a ∈ s → s ~> a := fun h _ => mem_unique h
#align computation.mem_promises Computation.mem_promises

theorem empty_promises (a : α) : empty α ~> a := fun _ h => absurd h (not_mem_empty _)
#align computation.empty_promises Computation.empty_promises

section get

variable (s : Computation α) [h : Terminates s]

/-- `length s` gets the number of steps of a terminating computation -/
def length : ℕ :=
  Nat.find ((terminates_def _).1 h)
#align computation.length Computation.length

/-- `get s` returns the result of a terminating computation -/
def get : α :=
  Option.get _ (Nat.find_spec <| (terminates_def _).1 h)
#align computation.get Computation.get

theorem get_mem : get s ∈ s :=
  Exists.intro (length s) (Option.eq_some_of_isSome _).symm
#align computation.get_mem Computation.get_mem

theorem get_eq_of_mem {a} : a ∈ s → get s = a :=
  mem_unique (get_mem _)
#align computation.get_eq_of_mem Computation.get_eq_of_mem

theorem mem_of_get_eq {a} : get s = a → a ∈ s := by intro h; rw [← h]; apply get_mem
#align computation.mem_of_get_eq Computation.mem_of_get_eq

@[simp]
theorem get_think : get (think s) = get s :=
  get_eq_of_mem _ <|
    let ⟨n, h⟩ := get_mem s
    ⟨n + 1, h⟩
#align computation.get_think Computation.get_think

@[simp]
theorem get_thinkN (n) : get (thinkN s n) = get s :=
  get_eq_of_mem _ <| (thinkN_mem _).2 (get_mem _)
set_option linter.uppercaseLean3 false in
#align computation.get_thinkN Computation.get_thinkN

theorem get_promises : s ~> get s := fun _ => get_eq_of_mem _
#align computation.get_promises Computation.get_promises

theorem mem_of_promises {a} (p : s ~> a) : a ∈ s := by
  cases' h with h
  cases' h with a' h
  rw [p h]
  exact h
#align computation.mem_of_promises Computation.mem_of_promises

theorem get_eq_of_promises {a} : s ~> a → get s = a :=
  get_eq_of_mem _ ∘ mem_of_promises _
#align computation.get_eq_of_promises Computation.get_eq_of_promises

end get

/-- `Results s a n` completely characterizes a terminating computation:
  it asserts that `s` terminates after exactly `n` steps, with result `a`. -/
def Results (s : Computation α) (a : α) (n : ℕ) :=
  ∃ h : a ∈ s, @length _ s (terminates_of_mem h) = n
#align computation.results Computation.Results

theorem results_of_terminates (s : Computation α) [_T : Terminates s] :
    Results s (get s) (length s) :=
  ⟨get_mem _, rfl⟩
#align computation.results_of_terminates Computation.results_of_terminates

theorem results_of_terminates' (s : Computation α) [T : Terminates s] {a} (h : a ∈ s) :
    Results s a (length s) := by rw [← get_eq_of_mem _ h]; apply results_of_terminates
#align computation.results_of_terminates' Computation.results_of_terminates'

theorem Results.mem {s : Computation α} {a n} : Results s a n → a ∈ s
  | ⟨m, _⟩ => m
#align computation.results.mem Computation.Results.mem

theorem Results.terminates {s : Computation α} {a n} (h : Results s a n) : Terminates s :=
  terminates_of_mem h.mem
#align computation.results.terminates Computation.Results.terminates

theorem Results.length {s : Computation α} {a n} [_T : Terminates s] : Results s a n → length s = n
  | ⟨_, h⟩ => h
#align computation.results.length Computation.Results.length

theorem Results.val_unique {s : Computation α} {a b m n} (h1 : Results s a m) (h2 : Results s b n) :
    a = b :=
  mem_unique h1.mem h2.mem
#align computation.results.val_unique Computation.Results.val_unique

theorem Results.len_unique {s : Computation α} {a b m n} (h1 : Results s a m) (h2 : Results s b n) :
    m = n := by haveI := h1.terminates; haveI := h2.terminates; rw [← h1.length, h2.length]
#align computation.results.len_unique Computation.Results.len_unique

theorem exists_results_of_mem {s : Computation α} {a} (h : a ∈ s) : ∃ n, Results s a n :=
  haveI := terminates_of_mem h
  ⟨_, results_of_terminates' s h⟩
#align computation.exists_results_of_mem Computation.exists_results_of_mem

@[simp]
theorem get_pure (a : α) : get (pure a) = a :=
  get_eq_of_mem _ ⟨0, rfl⟩
#align computation.get_ret Computation.get_pure

@[simp]
theorem length_pure (a : α) : length (pure a) = 0 :=
  let h := Computation.ret_terminates a
  Nat.eq_zero_of_le_zero <| Nat.find_min' ((terminates_def (pure a)).1 h) rfl
#align computation.length_ret Computation.length_pure

theorem results_pure (a : α) : Results (pure a) a 0 :=
  ⟨ret_mem a, length_pure _⟩
#align computation.results_ret Computation.results_pure

@[simp]
theorem length_think (s : Computation α) [h : Terminates s] : length (think s) = length s + 1 := by
  apply le_antisymm
  · exact Nat.find_min' _ (Nat.find_spec ((terminates_def _).1 h))
  · have : (Option.isSome ((think s).val (length (think s))) : Prop) :=
      Nat.find_spec ((terminates_def _).1 s.think_terminates)
    revert this; cases' length (think s) with n <;> intro this
    · simp [think, Stream'.cons] at this
    · apply Nat.succ_le_succ
      apply Nat.find_min'
      apply this
#align computation.length_think Computation.length_think

theorem results_think {s : Computation α} {a n} (h : Results s a n) : Results (think s) a (n + 1) :=
  haveI := h.terminates
  ⟨think_mem h.mem, by rw [length_think, h.length]⟩
#align computation.results_think Computation.results_think

theorem of_results_think {s : Computation α} {a n} (h : Results (think s) a n) :
    ∃ m, Results s a m ∧ n = m + 1 := by
  haveI := of_think_terminates h.terminates
  have := results_of_terminates' _ (of_think_mem h.mem)
  exact ⟨_, this, Results.len_unique h (results_think this)⟩
#align computation.of_results_think Computation.of_results_think

@[simp]
theorem results_think_iff {s : Computation α} {a n} : Results (think s) a (n + 1) ↔ Results s a n :=
  ⟨fun h => by
    let ⟨n', r, e⟩ := of_results_think h
    injection e with h'; rwa [h'], results_think⟩
#align computation.results_think_iff Computation.results_think_iff

theorem results_thinkN {s : Computation α} {a m} :
    ∀ n, Results s a m → Results (thinkN s n) a (m + n)
  | 0, h => h
  | n + 1, h => results_think (results_thinkN n h)
set_option linter.uppercaseLean3 false in
#align computation.results_thinkN Computation.results_thinkN

theorem results_thinkN_pure (a : α) (n) : Results (thinkN (pure a) n) a n := by
  have := results_thinkN n (results_pure a); rwa [Nat.zero_add] at this
set_option linter.uppercaseLean3 false in
#align computation.results_thinkN_ret Computation.results_thinkN_pure

@[simp]
theorem length_thinkN (s : Computation α) [_h : Terminates s] (n) :
    length (thinkN s n) = length s + n :=
  (results_thinkN n (results_of_terminates _)).length
set_option linter.uppercaseLean3 false in
#align computation.length_thinkN Computation.length_thinkN

theorem eq_thinkN {s : Computation α} {a n} (h : Results s a n) : s = thinkN (pure a) n := by
  revert s
  induction' n with n IH <;> intro s <;> apply recOn s (fun a' => _) fun s => _ <;> intro a h
  · rw [← eq_of_pure_mem h.mem]
    rfl
  · cases' of_results_think h with n h
    cases h
    contradiction
  · have := h.len_unique (results_pure _)
    contradiction
  · rw [IH (results_think_iff.1 h)]
    rfl
set_option linter.uppercaseLean3 false in
#align computation.eq_thinkN Computation.eq_thinkN

theorem eq_thinkN' (s : Computation α) [_h : Terminates s] :
    s = thinkN (pure (get s)) (length s) :=
  eq_thinkN (results_of_terminates _)
set_option linter.uppercaseLean3 false in
#align computation.eq_thinkN' Computation.eq_thinkN'

/-- Recursor based on membership-/
def memRecOn {C : Computation α → Sort v} {a s} (M : a ∈ s) (h1 : C (pure a))
    (h2 : ∀ s, C s → C (think s)) : C s := by
  haveI T := terminates_of_mem M
  rw [eq_thinkN' s, get_eq_of_mem s M]
  generalize length s = n
  induction' n with n IH; exacts [h1, h2 _ IH]
#align computation.mem_rec_on Computation.memRecOn

/-- Recursor based on assertion of `Terminates`-/
def terminatesRecOn
    {C : Computation α → Sort v}
    (s) [Terminates s]
    (h1 : ∀ a, C (pure a))
    (h2 : ∀ s, C s → C (think s)) : C s :=
  memRecOn (get_mem s) (h1 _) h2
#align computation.terminates_rec_on Computation.terminatesRecOn

/-- Map a function on the result of a computation. -/
def map (f : α → β) : Computation α → Computation β
  | ⟨s, al⟩ =>
    ⟨s.map fun o => Option.casesOn o none (some ∘ f), fun n b => by
      dsimp [Stream'.map, Stream'.get]
      induction' e : s n with a <;> intro h
      · contradiction
      · rw [al e]; exact h⟩
#align computation.map Computation.map

/-- bind over a `Sum` of `Computation`-/
def Bind.g : Sum β (Computation β) → Sum β (Sum (Computation α) (Computation β))
  | Sum.inl b => Sum.inl b
  | Sum.inr cb' => Sum.inr <| Sum.inr cb'
set_option linter.uppercaseLean3 false in
#align computation.bind.G Computation.Bind.g

/-- bind over a function mapping `α` to a `Computation`-/
def Bind.f (f : α → Computation β) :
    Sum (Computation α) (Computation β) → Sum β (Sum (Computation α) (Computation β))
  | Sum.inl ca =>
    match destruct ca with
    | Sum.inl a => Bind.g <| destruct (f a)
    | Sum.inr ca' => Sum.inr <| Sum.inl ca'
  | Sum.inr cb => Bind.g <| destruct cb
set_option linter.uppercaseLean3 false in
#align computation.bind.F Computation.Bind.f

/-- Compose two computations into a monadic `bind` operation. -/
def bind (c : Computation α) (f : α → Computation β) : Computation β :=
  corec (Bind.f f) (Sum.inl c)
#align computation.bind Computation.bind

instance : Bind Computation :=
  ⟨@bind⟩

theorem has_bind_eq_bind {β} (c : Computation α) (f : α → Computation β) : c >>= f = bind c f :=
  rfl
#align computation.has_bind_eq_bind Computation.has_bind_eq_bind

/-- Flatten a computation of computations into a single computation. -/
def join (c : Computation (Computation α)) : Computation α :=
  c >>= id
#align computation.join Computation.join

@[simp]
theorem map_pure (f : α → β) (a) : map f (pure a) = pure (f a) :=
  rfl
#align computation.map_ret Computation.map_pure

@[simp]
theorem map_think (f : α → β) : ∀ s, map f (think s) = think (map f s)
  | ⟨s, al⟩ => by apply Subtype.eq; dsimp [think, map]; rw [Stream'.map_cons]
#align computation.map_think Computation.map_think

@[simp]
theorem destruct_map (f : α → β) (s) : destruct (map f s) = lmap f (rmap (map f) (destruct s)) := by
  apply s.recOn <;> intro <;> simp
#align computation.destruct_map Computation.destruct_map

@[simp]
theorem map_id : ∀ s : Computation α, map id s = s
  | ⟨f, al⟩ => by
    apply Subtype.eq; simp only [map, comp_apply, id_eq]
    have e : @Option.rec α (fun _ => Option α) none some = id := by ext ⟨⟩ <;> rfl
    have h : ((fun x: Option α => x) = id) := rfl
    simp [e, h, Stream'.map_id]
#align computation.map_id Computation.map_id

theorem map_comp (f : α → β) (g : β → γ) : ∀ s : Computation α, map (g ∘ f) s = map g (map f s)
  | ⟨s, al⟩ => by
    apply Subtype.eq; dsimp [map]
    apply congr_arg fun f : _ → Option γ => Stream'.map f s
    ext ⟨⟩ <;> rfl
#align computation.map_comp Computation.map_comp

@[simp]
theorem ret_bind (a) (f : α → Computation β) : bind (pure a) f = f a := by
  apply
    eq_of_bisim fun c₁ c₂ => c₁ = bind (pure a) f ∧ c₂ = f a ∨ c₁ = corec (Bind.f f) (Sum.inr c₂)
  · intro c₁ c₂ h
    match c₁, c₂, h with
    | _, _, Or.inl ⟨rfl, rfl⟩ =>
      simp only [BisimO, bind, Bind.f, corec_eq, rmap, destruct_pure]
      cases' destruct (f a) with b cb <;> simp [Bind.g]
    | _, c, Or.inr rfl =>
      simp only [BisimO, Bind.f, corec_eq, rmap]
      cases' destruct c with b cb <;> simp [Bind.g]
  · simp
#align computation.ret_bind Computation.ret_bind

@[simp]
theorem think_bind (c) (f : α → Computation β) : bind (think c) f = think (bind c f) :=
  destruct_eq_think <| by simp [bind, Bind.f]
#align computation.think_bind Computation.think_bind

@[simp]
theorem bind_pure (f : α → β) (s) : bind s (pure ∘ f) = map f s := by
  apply eq_of_bisim fun c₁ c₂ => c₁ = c₂ ∨ ∃ s, c₁ = bind s (pure ∘ f) ∧ c₂ = map f s
  · intro c₁ c₂ h
    match c₁, c₂, h with
    | _, c₂, Or.inl (Eq.refl _) => cases' destruct c₂ with b cb <;> simp
    | _, _, Or.inr ⟨s, rfl, rfl⟩ =>
      apply recOn s <;> intro s <;> simp
      exact Or.inr ⟨s, rfl, rfl⟩
  · exact Or.inr ⟨s, rfl, rfl⟩
#align computation.bind_ret Computation.bind_pure

-- Porting note: used to use `rw [bind_pure]`
@[simp]
theorem bind_pure' (s : Computation α) : bind s pure = s := by
  apply eq_of_bisim fun c₁ c₂ => c₁ = c₂ ∨ ∃ s, c₁ = bind s pure ∧ c₂ = s
  · intro c₁ c₂ h
    match c₁, c₂, h with
    | _, c₂, Or.inl (Eq.refl _) => cases' destruct c₂ with b cb <;> simp
    | _, _, Or.inr ⟨s, rfl, rfl⟩ =>
      apply recOn s <;> intro s <;> simp
  · exact Or.inr ⟨s, rfl, rfl⟩
#align computation.bind_ret' Computation.bind_pure'

@[simp]
theorem bind_assoc (s : Computation α) (f : α → Computation β) (g : β → Computation γ) :
    bind (bind s f) g = bind s fun x : α => bind (f x) g := by
  apply
    eq_of_bisim fun c₁ c₂ =>
      c₁ = c₂ ∨ ∃ s, c₁ = bind (bind s f) g ∧ c₂ = bind s fun x : α => bind (f x) g
  · intro c₁ c₂ h
    match c₁, c₂, h with
    | _, c₂, Or.inl (Eq.refl _) => cases' destruct c₂ with b cb <;> simp
    | _, _, Or.inr ⟨s, rfl, rfl⟩ =>
      apply recOn s <;> intro s <;> simp
      · generalize f s = fs
        apply recOn fs <;> intro t <;> simp
        · cases' destruct (g t) with b cb <;> simp
      · exact Or.inr ⟨s, rfl, rfl⟩
  · exact Or.inr ⟨s, rfl, rfl⟩
#align computation.bind_assoc Computation.bind_assoc

theorem results_bind {s : Computation α} {f : α → Computation β} {a b m n} (h1 : Results s a m)
    (h2 : Results (f a) b n) : Results (bind s f) b (n + m) := by
  have := h1.mem; revert m
  apply memRecOn this _ fun s IH => _
  · intro _ h1
    rw [ret_bind]
    rw [h1.len_unique (results_pure _)]
    exact h2
  · intro _ h3 _ h1
    rw [think_bind]
    cases' of_results_think h1 with m' h
    cases' h with h1 e
    rw [e]
    exact results_think (h3 h1)
#align computation.results_bind Computation.results_bind

theorem mem_bind {s : Computation α} {f : α → Computation β} {a b} (h1 : a ∈ s) (h2 : b ∈ f a) :
    b ∈ bind s f :=
  let ⟨_, h1⟩ := exists_results_of_mem h1
  let ⟨_, h2⟩ := exists_results_of_mem h2
  (results_bind h1 h2).mem
#align computation.mem_bind Computation.mem_bind

instance terminates_bind (s : Computation α) (f : α → Computation β) [Terminates s]
    [Terminates (f (get s))] : Terminates (bind s f) :=
  terminates_of_mem (mem_bind (get_mem s) (get_mem (f (get s))))
#align computation.terminates_bind Computation.terminates_bind

@[simp]
theorem get_bind (s : Computation α) (f : α → Computation β) [Terminates s]
    [Terminates (f (get s))] : get (bind s f) = get (f (get s)) :=
  get_eq_of_mem _ (mem_bind (get_mem s) (get_mem (f (get s))))
#align computation.get_bind Computation.get_bind

@[simp]
theorem length_bind (s : Computation α) (f : α → Computation β) [_T1 : Terminates s]
    [_T2 : Terminates (f (get s))] : length (bind s f) = length (f (get s)) + length s :=
  (results_of_terminates _).len_unique <|
    results_bind (results_of_terminates _) (results_of_terminates _)
#align computation.length_bind Computation.length_bind

theorem of_results_bind {s : Computation α} {f : α → Computation β} {b k} :
    Results (bind s f) b k → ∃ a m n, Results s a m ∧ Results (f a) b n ∧ k = n + m := by
  induction' k with n IH generalizing s <;> apply recOn s (fun a => _) fun s' => _ <;> intro e h
  · simp only [ret_bind, Nat.zero_eq] at h
    exact ⟨e, _, _, results_pure _, h, rfl⟩
  · have := congr_arg head (eq_thinkN h)
    contradiction
  · simp only [ret_bind] at h
    exact ⟨e, _, n + 1, results_pure _, h, rfl⟩
  · simp only [think_bind, results_think_iff] at h
    let ⟨a, m, n', h1, h2, e'⟩ := IH h
    rw [e']
    exact ⟨a, m.succ, n', results_think h1, h2, rfl⟩
#align computation.of_results_bind Computation.of_results_bind

theorem exists_of_mem_bind {s : Computation α} {f : α → Computation β} {b} (h : b ∈ bind s f) :
    ∃ a ∈ s, b ∈ f a :=
  let ⟨_, h⟩ := exists_results_of_mem h
  let ⟨a, _, _, h1, h2, _⟩ := of_results_bind h
  ⟨a, h1.mem, h2.mem⟩
#align computation.exists_of_mem_bind Computation.exists_of_mem_bind

theorem bind_promises {s : Computation α} {f : α → Computation β} {a b} (h1 : s ~> a)
    (h2 : f a ~> b) : bind s f ~> b := fun b' bB => by
  rcases exists_of_mem_bind bB with ⟨a', a's, ba'⟩
  rw [← h1 a's] at ba'; exact h2 ba'
#align computation.bind_promises Computation.bind_promises

instance monad : Monad Computation where
  map := @map
  pure := @pure
  bind := @bind

instance : LawfulMonad Computation := LawfulMonad.mk'
  (id_map := @map_id)
  (bind_pure_comp := @bind_pure)
  (pure_bind := @ret_bind)
  (bind_assoc := @bind_assoc)

theorem has_map_eq_map {β} (f : α → β) (c : Computation α) : f <$> c = map f c :=
  rfl
#align computation.has_map_eq_map Computation.has_map_eq_map

@[simp]
theorem pure_def (a) : (return a : Computation α) = pure a :=
  rfl
#align computation.return_def Computation.pure_def

@[simp]
theorem map_pure' {α β} : ∀ (f : α → β) (a), f <$> pure a = pure (f a) :=
  map_pure
#align computation.map_ret' Computation.map_pure'

@[simp]
theorem map_think' {α β} : ∀ (f : α → β) (s), f <$> think s = think (f <$> s) :=
  map_think
#align computation.map_think' Computation.map_think'

theorem mem_map (f : α → β) {a} {s : Computation α} (m : a ∈ s) : f a ∈ map f s := by
  rw [← bind_pure]; apply mem_bind m; apply ret_mem
#align computation.mem_map Computation.mem_map

theorem exists_of_mem_map {f : α → β} {b : β} {s : Computation α} (h : b ∈ map f s) :
    ∃ a, a ∈ s ∧ f a = b := by
  rw [← bind_pure] at h
  let ⟨a, as, fb⟩ := exists_of_mem_bind h
  exact ⟨a, as, mem_unique (ret_mem _) fb⟩
#align computation.exists_of_mem_map Computation.exists_of_mem_map

instance terminates_map (f : α → β) (s : Computation α) [Terminates s] : Terminates (map f s) := by
  rw [← bind_pure]; exact terminates_of_mem (mem_bind (get_mem s) (get_mem (f (get s))))
#align computation.terminates_map Computation.terminates_map

theorem terminates_map_iff (f : α → β) (s : Computation α) : Terminates (map f s) ↔ Terminates s :=
  ⟨fun ⟨⟨_, h⟩⟩ =>
    let ⟨_, h1, _⟩ := exists_of_mem_map h
    ⟨⟨_, h1⟩⟩,
    @Computation.terminates_map _ _ _ _⟩
#align computation.terminates_map_iff Computation.terminates_map_iff

-- Parallel computation
/-- `c₁ <|> c₂` calculates `c₁` and `c₂` simultaneously, returning
  the first one that gives a result. -/
def orElse (c₁ : Computation α) (c₂ : Unit → Computation α) : Computation α :=
  @Computation.corec α (Computation α × Computation α)
    (fun ⟨c₁, c₂⟩ =>
      match destruct c₁ with
      | Sum.inl a => Sum.inl a
      | Sum.inr c₁' =>
        match destruct c₂ with
        | Sum.inl a => Sum.inl a
        | Sum.inr c₂' => Sum.inr (c₁', c₂'))
    (c₁, c₂ ())
#align computation.orelse Computation.orElse

instance instAlternativeComputation : Alternative Computation :=
  { Computation.monad with
    orElse := @orElse
    failure := @empty }

-- Porting note: Added unfolds as the code does not work without it
@[simp]
theorem ret_orElse (a : α) (c₂ : Computation α) : (pure a <|> c₂) = pure a :=
  destruct_eq_pure <| by
    unfold_projs
    simp [orElse]
#align computation.ret_orelse Computation.ret_orElse

-- Porting note: Added unfolds as the code does not work without it
@[simp]
theorem orElse_pure (c₁ : Computation α) (a : α) : (think c₁ <|> pure a) = pure a :=
  destruct_eq_pure <| by
    unfold_projs
    simp [orElse]
#align computation.orelse_ret Computation.orElse_pure

-- Porting note: Added unfolds as the code does not work without it
@[simp]
theorem orElse_think (c₁ c₂ : Computation α) : (think c₁ <|> think c₂) = think (c₁ <|> c₂) :=
  destruct_eq_think <| by
    unfold_projs
    simp [orElse]
#align computation.orelse_think Computation.orElse_think

@[simp]
theorem empty_orElse (c) : (empty α <|> c) = c := by
  apply eq_of_bisim (fun c₁ c₂ => (empty α <|> c₂) = c₁) _ rfl
  intro s' s h; rw [← h]
  apply recOn s <;> intro s <;> rw [think_empty] <;> simp
  rw [← think_empty]
#align computation.empty_orelse Computation.empty_orElse

@[simp]
theorem orElse_empty (c : Computation α) : (c <|> empty α) = c := by
  apply eq_of_bisim (fun c₁ c₂ => (c₂ <|> empty α) = c₁) _ rfl
  intro s' s h; rw [← h]
  apply recOn s <;> intro s <;> rw [think_empty] <;> simp
  rw [← think_empty]
#align computation.orelse_empty Computation.orElse_empty

/-- `c₁ ~ c₂` asserts that `c₁` and `c₂` either both terminate with the same result,
  or both loop forever. -/
def Equiv (c₁ c₂ : Computation α) : Prop :=
  ∀ a, a ∈ c₁ ↔ a ∈ c₂
#align computation.equiv Computation.Equiv

/-- equivalence relation for computations-/
scoped infixl:50 " ~ " => Equiv

@[refl]
theorem Equiv.refl (s : Computation α) : s ~ s := fun _ => Iff.rfl
#align computation.equiv.refl Computation.Equiv.refl

@[symm]
theorem Equiv.symm {s t : Computation α} : s ~ t → t ~ s := fun h a => (h a).symm
#align computation.equiv.symm Computation.Equiv.symm

@[trans]
theorem Equiv.trans {s t u : Computation α} : s ~ t → t ~ u → s ~ u := fun h1 h2 a =>
  (h1 a).trans (h2 a)
#align computation.equiv.trans Computation.Equiv.trans

theorem Equiv.equivalence : Equivalence (@Equiv α) :=
  ⟨@Equiv.refl _, @Equiv.symm _, @Equiv.trans _⟩
#align computation.equiv.equivalence Computation.Equiv.equivalence

theorem equiv_of_mem {s t : Computation α} {a} (h1 : a ∈ s) (h2 : a ∈ t) : s ~ t := fun a' =>
  ⟨fun ma => by rw [mem_unique ma h1]; exact h2, fun ma => by rw [mem_unique ma h2]; exact h1⟩
#align computation.equiv_of_mem Computation.equiv_of_mem

theorem terminates_congr {c₁ c₂ : Computation α} (h : c₁ ~ c₂) : Terminates c₁ ↔ Terminates c₂ := by
  simp only [terminates_iff, exists_congr h]
#align computation.terminates_congr Computation.terminates_congr

theorem promises_congr {c₁ c₂ : Computation α} (h : c₁ ~ c₂) (a) : c₁ ~> a ↔ c₂ ~> a :=
  forall_congr' fun a' => imp_congr (h a') Iff.rfl
#align computation.promises_congr Computation.promises_congr

theorem get_equiv {c₁ c₂ : Computation α} (h : c₁ ~ c₂) [Terminates c₁] [Terminates c₂] :
    get c₁ = get c₂ :=
  get_eq_of_mem _ <| (h _).2 <| get_mem _
#align computation.get_equiv Computation.get_equiv

theorem think_equiv (s : Computation α) : think s ~ s := fun _ => ⟨of_think_mem, think_mem⟩
#align computation.think_equiv Computation.think_equiv

theorem thinkN_equiv (s : Computation α) (n) : thinkN s n ~ s := fun _ => thinkN_mem n
set_option linter.uppercaseLean3 false in
#align computation.thinkN_equiv Computation.thinkN_equiv

theorem bind_congr {s1 s2 : Computation α} {f1 f2 : α → Computation β} (h1 : s1 ~ s2)
    (h2 : ∀ a, f1 a ~ f2 a) : bind s1 f1 ~ bind s2 f2 := fun b =>
  ⟨fun h =>
    let ⟨a, ha, hb⟩ := exists_of_mem_bind h
    mem_bind ((h1 a).1 ha) ((h2 a b).1 hb),
    fun h =>
    let ⟨a, ha, hb⟩ := exists_of_mem_bind h
    mem_bind ((h1 a).2 ha) ((h2 a b).2 hb)⟩
#align computation.bind_congr Computation.bind_congr

theorem equiv_pure_of_mem {s : Computation α} {a} (h : a ∈ s) : s ~ pure a :=
  equiv_of_mem h (ret_mem _)
#align computation.equiv_ret_of_mem Computation.equiv_pure_of_mem

/-- `LiftRel R ca cb` is a generalization of `Equiv` to relations other than
  equality. It asserts that if `ca` terminates with `a`, then `cb` terminates with
  some `b` such that `R a b`, and if `cb` terminates with `b` then `ca` terminates
  with some `a` such that `R a b`. -/
def LiftRel (R : α → β → Prop) (ca : Computation α) (cb : Computation β) : Prop :=
  (∀ {a}, a ∈ ca → ∃ b, b ∈ cb ∧ R a b) ∧ ∀ {b}, b ∈ cb → ∃ a, a ∈ ca ∧ R a b
#align computation.lift_rel Computation.LiftRel

theorem LiftRel.swap (R : α → β → Prop) (ca : Computation α) (cb : Computation β) :
    LiftRel (swap R) cb ca ↔ LiftRel R ca cb :=
  @and_comm _ _
#align computation.lift_rel.swap Computation.LiftRel.swap

theorem lift_eq_iff_equiv (c₁ c₂ : Computation α) : LiftRel (· = ·) c₁ c₂ ↔ c₁ ~ c₂ :=
  ⟨fun ⟨h1, h2⟩ a =>
    ⟨fun a1 => by let ⟨b, b2, ab⟩ := h1 a1; rwa [ab],
     fun a2 => by let ⟨b, b1, ab⟩ := h2 a2; rwa [← ab]⟩,
    fun e => ⟨fun {a} a1 => ⟨a, (e _).1 a1, rfl⟩, fun {a} a2 => ⟨a, (e _).2 a2, rfl⟩⟩⟩
#align computation.lift_eq_iff_equiv Computation.lift_eq_iff_equiv

theorem LiftRel.refl (R : α → α → Prop) (H : Reflexive R) : Reflexive (LiftRel R) := fun _ =>
  ⟨fun {a} as => ⟨a, as, H a⟩, fun {b} bs => ⟨b, bs, H b⟩⟩
#align computation.lift_rel.refl Computation.LiftRel.refl

theorem LiftRel.symm (R : α → α → Prop) (H : Symmetric R) : Symmetric (LiftRel R) :=
  fun _ _ ⟨l, r⟩ =>
  ⟨fun {_} a2 =>
    let ⟨b, b1, ab⟩ := r a2
    ⟨b, b1, H ab⟩,
    fun {_} a1 =>
    let ⟨b, b2, ab⟩ := l a1
    ⟨b, b2, H ab⟩⟩
#align computation.lift_rel.symm Computation.LiftRel.symm

theorem LiftRel.trans (R : α → α → Prop) (H : Transitive R) : Transitive (LiftRel R) :=
  fun _ _ _ ⟨l1, r1⟩ ⟨l2, r2⟩ =>
  ⟨fun {_} a1 =>
    let ⟨_, b2, ab⟩ := l1 a1
    let ⟨c, c3, bc⟩ := l2 b2
    ⟨c, c3, H ab bc⟩,
    fun {_} c3 =>
    let ⟨_, b2, bc⟩ := r2 c3
    let ⟨a, a1, ab⟩ := r1 b2
    ⟨a, a1, H ab bc⟩⟩
#align computation.lift_rel.trans Computation.LiftRel.trans

theorem LiftRel.equiv (R : α → α → Prop) : Equivalence R → Equivalence (LiftRel R)
  | ⟨refl, symm, trans⟩ => ⟨LiftRel.refl R refl, by apply LiftRel.symm; apply symm,
    by apply LiftRel.trans; apply trans⟩
  -- Porting note: The code above was:
  -- | ⟨refl, symm, trans⟩ => ⟨LiftRel.refl R refl, LiftRel.symm R symm, LiftRel.trans R trans⟩
  --
  -- The code fails to identify `symm` as being symmetric.
#align computation.lift_rel.equiv Computation.LiftRel.equiv

theorem LiftRel.imp {R S : α → β → Prop} (H : ∀ {a b}, R a b → S a b) (s t) :
    LiftRel R s t → LiftRel S s t
  | ⟨l, r⟩ =>
    ⟨fun {_} as =>
      let ⟨b, bt, ab⟩ := l as
      ⟨b, bt, H ab⟩,
      fun {_} bt =>
      let ⟨a, as, ab⟩ := r bt
      ⟨a, as, H ab⟩⟩
#align computation.lift_rel.imp Computation.LiftRel.imp

theorem terminates_of_liftRel {R : α → β → Prop} {s t} :
    LiftRel R s t → (Terminates s ↔ Terminates t)
  | ⟨l, r⟩ =>
    ⟨fun ⟨⟨_, as⟩⟩ =>
      let ⟨b, bt, _⟩ := l as
      ⟨⟨b, bt⟩⟩,
      fun ⟨⟨_, bt⟩⟩ =>
      let ⟨a, as, _⟩ := r bt
      ⟨⟨a, as⟩⟩⟩
#align computation.terminates_of_lift_rel Computation.terminates_of_liftRel

theorem rel_of_liftRel {R : α → β → Prop} {ca cb} :
    LiftRel R ca cb → ∀ {a b}, a ∈ ca → b ∈ cb → R a b
  | ⟨l, _⟩, a, b, ma, mb => by
    let ⟨b', mb', ab'⟩ := l ma
    rw [mem_unique mb mb']; exact ab'
#align computation.rel_of_lift_rel Computation.rel_of_liftRel

theorem liftRel_of_mem {R : α → β → Prop} {a b ca cb} (ma : a ∈ ca) (mb : b ∈ cb) (ab : R a b) :
    LiftRel R ca cb :=
  ⟨fun {a'} ma' => by rw [mem_unique ma' ma]; exact ⟨b, mb, ab⟩, fun {b'} mb' => by
    rw [mem_unique mb' mb]; exact ⟨a, ma, ab⟩⟩
#align computation.lift_rel_of_mem Computation.liftRel_of_mem

theorem exists_of_liftRel_left {R : α → β → Prop} {ca cb} (H : LiftRel R ca cb) {a} (h : a ∈ ca) :
    ∃ b, b ∈ cb ∧ R a b :=
  H.left h
#align computation.exists_of_lift_rel_left Computation.exists_of_liftRel_left

theorem exists_of_liftRel_right {R : α → β → Prop} {ca cb} (H : LiftRel R ca cb) {b} (h : b ∈ cb) :
    ∃ a, a ∈ ca ∧ R a b :=
  H.right h
#align computation.exists_of_lift_rel_right Computation.exists_of_liftRel_right

theorem liftRel_def {R : α → β → Prop} {ca cb} :
    LiftRel R ca cb ↔ (Terminates ca ↔ Terminates cb) ∧ ∀ {a b}, a ∈ ca → b ∈ cb → R a b :=
  ⟨fun h =>
    ⟨terminates_of_liftRel h, fun {a b} ma mb => by
      let ⟨b', mb', ab⟩ := h.left ma
      rwa [mem_unique mb mb']⟩,
    fun ⟨l, r⟩ =>
    ⟨fun {a} ma =>
      let ⟨⟨b, mb⟩⟩ := l.1 ⟨⟨_, ma⟩⟩
      ⟨b, mb, r ma mb⟩,
      fun {b} mb =>
      let ⟨⟨a, ma⟩⟩ := l.2 ⟨⟨_, mb⟩⟩
      ⟨a, ma, r ma mb⟩⟩⟩
#align computation.lift_rel_def Computation.liftRel_def

theorem liftRel_bind {δ} (R : α → β → Prop) (S : γ → δ → Prop) {s1 : Computation α}
    {s2 : Computation β} {f1 : α → Computation γ} {f2 : β → Computation δ} (h1 : LiftRel R s1 s2)
    (h2 : ∀ {a b}, R a b → LiftRel S (f1 a) (f2 b)) : LiftRel S (bind s1 f1) (bind s2 f2) :=
  let ⟨l1, r1⟩ := h1
  ⟨fun {_} cB =>
    let ⟨_, a1, c₁⟩ := exists_of_mem_bind cB
    let ⟨_, b2, ab⟩ := l1 a1
    let ⟨l2, _⟩ := h2 ab
    let ⟨_, d2, cd⟩ := l2 c₁
    ⟨_, mem_bind b2 d2, cd⟩,
    fun {_} dB =>
    let ⟨_, b1, d1⟩ := exists_of_mem_bind dB
    let ⟨_, a2, ab⟩ := r1 b1
    let ⟨_, r2⟩ := h2 ab
    let ⟨_, c₂, cd⟩ := r2 d1
    ⟨_, mem_bind a2 c₂, cd⟩⟩
#align computation.lift_rel_bind Computation.liftRel_bind

@[simp]
theorem liftRel_pure_left (R : α → β → Prop) (a : α) (cb : Computation β) :
    LiftRel R (pure a) cb ↔ ∃ b, b ∈ cb ∧ R a b :=
  ⟨fun ⟨l, _⟩ => l (ret_mem _), fun ⟨b, mb, ab⟩ =>
    ⟨fun {a'} ma' => by rw [eq_of_pure_mem ma']; exact ⟨b, mb, ab⟩, fun {b'} mb' =>
      ⟨_, ret_mem _, by rw [mem_unique mb' mb]; exact ab⟩⟩⟩
#align computation.lift_rel_return_left Computation.liftRel_pure_left

@[simp]
theorem liftRel_pure_right (R : α → β → Prop) (ca : Computation α) (b : β) :
    LiftRel R ca (pure b) ↔ ∃ a, a ∈ ca ∧ R a b := by rw [LiftRel.swap, liftRel_pure_left]
#align computation.lift_rel_return_right Computation.liftRel_pure_right

-- Porting note: `simpNF` wants to simplify based on `liftRel_pure_right` but point is to prove
-- a general invariant on `LiftRel`
@[simp, nolint simpNF]
theorem liftRel_pure (R : α → β → Prop) (a : α) (b : β) :
    LiftRel R (pure a) (pure b) ↔ R a b := by
  rw [liftRel_pure_left]
  exact ⟨fun ⟨b', mb', ab'⟩ => by rwa [eq_of_pure_mem mb'] at ab', fun ab => ⟨_, ret_mem _, ab⟩⟩
#align computation.lift_rel_return Computation.liftRel_pure

@[simp]
theorem liftRel_think_left (R : α → β → Prop) (ca : Computation α) (cb : Computation β) :
    LiftRel R (think ca) cb ↔ LiftRel R ca cb :=
  and_congr (forall_congr' fun _ => imp_congr ⟨of_think_mem, think_mem⟩ Iff.rfl)
    (forall_congr' fun _ =>
      imp_congr Iff.rfl <| exists_congr fun _ => and_congr ⟨of_think_mem, think_mem⟩ Iff.rfl)
#align computation.lift_rel_think_left Computation.liftRel_think_left

@[simp]
theorem liftRel_think_right (R : α → β → Prop) (ca : Computation α) (cb : Computation β) :
    LiftRel R ca (think cb) ↔ LiftRel R ca cb := by
  rw [← LiftRel.swap R, ← LiftRel.swap R]; apply liftRel_think_left
#align computation.lift_rel_think_right Computation.liftRel_think_right

theorem liftRel_mem_cases {R : α → β → Prop} {ca cb} (Ha : ∀ a ∈ ca, LiftRel R ca cb)
    (Hb : ∀ b ∈ cb, LiftRel R ca cb) : LiftRel R ca cb :=
  ⟨fun {_} ma => (Ha _ ma).left ma, fun {_} mb => (Hb _ mb).right mb⟩
#align computation.lift_rel_mem_cases Computation.liftRel_mem_cases

theorem liftRel_congr {R : α → β → Prop} {ca ca' : Computation α} {cb cb' : Computation β}
    (ha : ca ~ ca') (hb : cb ~ cb') : LiftRel R ca cb ↔ LiftRel R ca' cb' :=
  and_congr
    (forall_congr' fun _ => imp_congr (ha _) <| exists_congr fun _ => and_congr (hb _) Iff.rfl)
    (forall_congr' fun _ => imp_congr (hb _) <| exists_congr fun _ => and_congr (ha _) Iff.rfl)
#align computation.lift_rel_congr Computation.liftRel_congr

theorem liftRel_map {δ} (R : α → β → Prop) (S : γ → δ → Prop) {s1 : Computation α}
    {s2 : Computation β} {f1 : α → γ} {f2 : β → δ} (h1 : LiftRel R s1 s2)
    (h2 : ∀ {a b}, R a b → S (f1 a) (f2 b)) : LiftRel S (map f1 s1) (map f2 s2) := by
  -- Porting note: The line below was:
  -- rw [← bind_pure, ← bind_pure]; apply lift_rel_bind _ _ h1; simp; exact @h2
  --
  -- The code fails to work on the last exact.
  rw [← bind_pure, ← bind_pure]; apply liftRel_bind _ _ h1
  simp only [comp_apply, liftRel_pure_right]
  intros a b h; exact ⟨f1 a, ⟨ret_mem _, @h2 a b h⟩⟩
#align computation.lift_rel_map Computation.liftRel_map

-- Porting note: deleted initial arguments `(_R : α → α → Prop) (_S : β → β → Prop)`: unused
theorem map_congr {s1 s2 : Computation α} {f : α → β}
    (h1 : s1 ~ s2) : map f s1 ~ map f s2 := by
  rw [← lift_eq_iff_equiv]
  exact liftRel_map Eq _ ((lift_eq_iff_equiv _ _).2 h1) fun {a} b => congr_arg _
#align computation.map_congr Computation.map_congr

/-- Alternate definition of `LiftRel` over relations between `Computation`s-/
def LiftRelAux (R : α → β → Prop) (C : Computation α → Computation β → Prop) :
    Sum α (Computation α) → Sum β (Computation β) → Prop
  | Sum.inl a, Sum.inl b => R a b
  | Sum.inl a, Sum.inr cb => ∃ b, b ∈ cb ∧ R a b
  | Sum.inr ca, Sum.inl b => ∃ a, a ∈ ca ∧ R a b
  | Sum.inr ca, Sum.inr cb => C ca cb
#align computation.lift_rel_aux Computation.LiftRelAux

variable {R : α → β → Prop} {C : Computation α → Computation β → Prop}

-- Porting note: was attribute [simp] LiftRelAux
-- but right now `simp` on defs is a Lean 4 catastrophe
-- Instead we add the equation lemmas and tag them @[simp]
@[simp] lemma liftRelAux_inl_inl {a : α} {b : β} :
  LiftRelAux R C (Sum.inl a) (Sum.inl b) = R a b := rfl
@[simp] lemma liftRelAux_inl_inr {a : α} {cb} :
    LiftRelAux R C (Sum.inl a) (Sum.inr cb) = ∃ b, b ∈ cb ∧ R a b :=
  rfl
@[simp] lemma liftRelAux_inr_inl {b : β} {ca} :
    LiftRelAux R C (Sum.inr ca) (Sum.inl b) = ∃ a, a ∈ ca ∧ R a b :=
  rfl
@[simp] lemma liftRelAux_inr_inr {ca cb} :
    LiftRelAux R C (Sum.inr ca) (Sum.inr cb) = C ca cb :=
  rfl

@[simp]
theorem LiftRelAux.ret_left (R : α → β → Prop) (C : Computation α → Computation β → Prop) (a cb) :
    LiftRelAux R C (Sum.inl a) (destruct cb) ↔ ∃ b, b ∈ cb ∧ R a b := by
  apply cb.recOn (fun b => _) fun cb => _
  · intro b
    exact
      ⟨fun h => ⟨_, ret_mem _, h⟩, fun ⟨b', mb, h⟩ => by rw [mem_unique (ret_mem _) mb]; exact h⟩
  · intro
    rw [destruct_think]
    exact ⟨fun ⟨b, h, r⟩ => ⟨b, think_mem h, r⟩, fun ⟨b, h, r⟩ => ⟨b, of_think_mem h, r⟩⟩
#align computation.lift_rel_aux.ret_left Computation.LiftRelAux.ret_left

theorem LiftRelAux.swap (R : α → β → Prop) (C) (a b) :
    LiftRelAux (swap R) (swap C) b a = LiftRelAux R C a b := by
  cases' a with a ca <;> cases' b with b cb <;> simp only [LiftRelAux]
#align computation.lift_rel_aux.swap Computation.LiftRelAux.swap

@[simp]
theorem LiftRelAux.ret_right (R : α → β → Prop) (C : Computation α → Computation β → Prop) (b ca) :
    LiftRelAux R C (destruct ca) (Sum.inl b) ↔ ∃ a, a ∈ ca ∧ R a b := by
  rw [← LiftRelAux.swap, LiftRelAux.ret_left]
#align computation.lift_rel_aux.ret_right Computation.LiftRelAux.ret_right

theorem LiftRelRec.lem {R : α → β → Prop} (C : Computation α → Computation β → Prop)
    (H : ∀ {ca cb}, C ca cb → LiftRelAux R C (destruct ca) (destruct cb)) (ca cb) (Hc : C ca cb) (a)
    (ha : a ∈ ca) : LiftRel R ca cb := by
  revert cb
  refine memRecOn (C := (fun ca ↦ ∀ (cb : Computation β), C ca cb → LiftRel R ca cb))
    ha ?_ (fun ca' IH => ?_) <;> intro cb Hc <;> have h := H Hc
  · simp only [destruct_pure, LiftRelAux.ret_left] at h
    simp [h]
  · simp only [liftRel_think_left]
    revert h
    apply cb.recOn (fun b => _) fun cb' => _ <;> intros _ h <;> simp at h <;> simp [h]
    exact IH _ h
#align computation.lift_rel_rec.lem Computation.LiftRelRec.lem

theorem liftRel_rec {R : α → β → Prop} (C : Computation α → Computation β → Prop)
    (H : ∀ {ca cb}, C ca cb → LiftRelAux R C (destruct ca) (destruct cb)) (ca cb) (Hc : C ca cb) :
    LiftRel R ca cb :=
  liftRel_mem_cases (LiftRelRec.lem C (@H) ca cb Hc) fun b hb =>
    (LiftRel.swap _ _ _).2 <|
      LiftRelRec.lem (swap C) (fun {_ _} h => cast (LiftRelAux.swap _ _ _ _).symm <| H h) cb ca Hc b
        hb
#align computation.lift_rel_rec Computation.liftRel_rec

end Computation
