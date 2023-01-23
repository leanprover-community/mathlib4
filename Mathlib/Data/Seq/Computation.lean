/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Coinductive formalization of unbounded computations.

! This file was ported from Lean 3 source module data.seq.computation
! leanprover-community/mathlib commit 1f0096e6caa61e9c849ec2adbd227e960e9dff58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Stream.Init
import Mathbin.Tactic.Basic

open Function

universe u v w

/-
coinductive computation (α : Type u) : Type u
| return : α → computation α
| think : computation α → computation α
-/
/-- `computation α` is the type of unbounded computations returning `α`.
  An element of `computation α` is an infinite sequence of `option α` such
  that if `f n = some a` for some `n` then it is constantly `some a` after that. -/
def Computation (α : Type u) : Type u :=
  { f : Stream' (Option α) // ∀ ⦃n a⦄, f n = some a → f (n + 1) = some a }
#align computation Computation

namespace Computation

variable {α : Type u} {β : Type v} {γ : Type w}

-- constructors
/-- `return a` is the computation that immediately terminates with result `a`. -/
def return (a : α) : Computation α :=
  ⟨Stream'.const (some a), fun n a' => id⟩
#align computation.return Computation.return

instance : CoeTC α (Computation α) :=
  ⟨return⟩

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
-- note [use has_coe_t]
/-- `think c` is the computation that delays for one "tick" and then performs
  computation `c`. -/
def think (c : Computation α) : Computation α :=
  ⟨none::c.1, fun n a h => by
    cases' n with n
    contradiction
    exact c.2 h⟩
#align computation.think Computation.think

/-- `thinkN c n` is the computation that delays for `n` ticks and then performs
  computation `c`. -/
def thinkN (c : Computation α) : ℕ → Computation α
  | 0 => c
  | n + 1 => think (thinkN n)
#align computation.thinkN Computation.thinkN

-- check for immediate result
/-- `head c` is the first step of computation, either `some a` if `c = return a`
  or `none` if `c = think c'`. -/
def head (c : Computation α) : Option α :=
  c.1.head
#align computation.head Computation.head

-- one step of computation
/-- `tail c` is the remainder of computation, either `c` if `c = return a`
  or `c'` if `c = think c'`. -/
def tail (c : Computation α) : Computation α :=
  ⟨c.1.tail, fun n a h => c.2 h⟩
#align computation.tail Computation.tail

/-- `empty α` is the computation that never returns, an infinite sequence of
  `think`s. -/
def empty (α) : Computation α :=
  ⟨Stream'.const none, fun n a' => id⟩
#align computation.empty Computation.empty

instance : Inhabited (Computation α) :=
  ⟨empty _⟩

/-- `run_for c n` evaluates `c` for `n` steps and returns the result, or `none`
  if it did not terminate after `n` steps. -/
def runFor : Computation α → ℕ → Option α :=
  Subtype.val
#align computation.run_for Computation.runFor

/-- `destruct c` is the destructor for `computation α` as a coinductive type.
  It returns `inl a` if `c = return a` and `inr c'` if `c = think c'`. -/
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
#align computation.run computation.run

theorem destruct_eq_ret {s : Computation α} {a : α} : destruct s = Sum.inl a → s = return a :=
  by
  dsimp [destruct]
  induction' f0 : s.1 0 with <;> intro h
  · contradiction
  · apply Subtype.eq
    funext n
    induction' n with n IH
    · injection h with h'
      rwa [h'] at f0
    · exact s.2 IH
#align computation.destruct_eq_ret Computation.destruct_eq_ret

theorem destruct_eq_think {s : Computation α} {s'} : destruct s = Sum.inr s' → s = think s' :=
  by
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
theorem destruct_ret (a : α) : destruct (return a) = Sum.inl a :=
  rfl
#align computation.destruct_ret Computation.destruct_ret

@[simp]
theorem destruct_think : ∀ s : Computation α, destruct (think s) = Sum.inr s
  | ⟨f, al⟩ => rfl
#align computation.destruct_think Computation.destruct_think

@[simp]
theorem destruct_empty : destruct (empty α) = Sum.inr (empty α) :=
  rfl
#align computation.destruct_empty Computation.destruct_empty

@[simp]
theorem head_ret (a : α) : head (return a) = some a :=
  rfl
#align computation.head_ret Computation.head_ret

@[simp]
theorem head_think (s : Computation α) : head (think s) = none :=
  rfl
#align computation.head_think Computation.head_think

@[simp]
theorem head_empty : head (empty α) = none :=
  rfl
#align computation.head_empty Computation.head_empty

@[simp]
theorem tail_ret (a : α) : tail (return a) = return a :=
  rfl
#align computation.tail_ret Computation.tail_ret

@[simp]
theorem tail_think (s : Computation α) : tail (think s) = s := by
  cases' s with f al <;> apply Subtype.eq <;> dsimp [tail, think] <;> rw [Stream'.tail_cons]
#align computation.tail_think Computation.tail_think

@[simp]
theorem tail_empty : tail (empty α) = empty α :=
  rfl
#align computation.tail_empty Computation.tail_empty

theorem think_empty : empty α = think (empty α) :=
  destruct_eq_think destruct_empty
#align computation.think_empty Computation.think_empty

/-- Recursion principle for computations, compare with `list.rec_on`. -/
def recOn {C : Computation α → Sort v} (s : Computation α) (h1 : ∀ a, C (return a))
    (h2 : ∀ s, C (think s)) : C s :=
  by
  induction' H : destruct s with v v
  · rw [destruct_eq_ret H]
    apply h1
  · cases' v with a s'
    rw [destruct_eq_think H]
    apply h2
#align computation.rec_on Computation.recOn

def Corec.f (f : β → Sum α β) : Sum α β → Option α × Sum α β
  | Sum.inl a => (some a, Sum.inl a)
  | Sum.inr b =>
    (match f b with
      | Sum.inl a => some a
      | Sum.inr b' => none,
      f b)
#align computation.corec.F Computation.Corec.f

/-- `corec f b` is the corecursor for `computation α` as a coinductive type.
  If `f b = inl a` then `corec f b = return a`, and if `f b = inl b'` then
  `corec f b = think (corec f b')`. -/
def corec (f : β → Sum α β) (b : β) : Computation α :=
  by
  refine' ⟨Stream'.corec' (corec.F f) (Sum.inr b), fun n a' h => _⟩
  rw [Stream'.corec'_eq]
  change Stream'.corec' (corec.F f) (corec.F f (Sum.inr b)).2 n = some a'
  revert h; generalize Sum.inr b = o; revert o
  induction' n with n IH <;> intro o
  · change (corec.F f o).1 = some a' → (corec.F f (corec.F f o).2).1 = some a'
    cases' o with a b <;> intro h
    · exact h
    dsimp [corec.F] at h
    dsimp [corec.F]
    cases' f b with a b'
    · exact h
    · contradiction
  · rw [Stream'.corec'_eq (corec.F f) (corec.F f o).2, Stream'.corec'_eq (corec.F f) o]
    exact IH (corec.F f o).2
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

@[simp]
theorem corec_eq (f : β → Sum α β) (b : β) : destruct (corec f b) = rmap (corec f) (f b) :=
  by
  dsimp [corec, destruct]
  change Stream'.corec' (corec.F f) (Sum.inr b) 0 with corec.F._match_1 (f b)
  induction' h : f b with a b'; · rfl
  dsimp [corec.F, destruct]
  apply congr_arg; apply Subtype.eq
  dsimp [corec, tail]
  rw [Stream'.corec'_eq, Stream'.tail_cons]
  dsimp [corec.F]; rw [h]
#align computation.corec_eq Computation.corec_eq

section Bisim

variable (R : Computation α → Computation α → Prop)

-- mathport name: «expr ~ »
local infixl:50 " ~ " => R

def BisimO : Sum α (Computation α) → Sum α (Computation α) → Prop
  | Sum.inl a, Sum.inl a' => a = a'
  | Sum.inr s, Sum.inr s' => R s s'
  | _, _ => False
#align computation.bisim_o Computation.BisimO

attribute [simp] bisim_o

def IsBisimulation :=
  ∀ ⦃s₁ s₂⦄, s₁ ~ s₂ → BisimO R (destruct s₁) (destruct s₂)
#align computation.is_bisimulation Computation.IsBisimulation

-- If two computations are bisimilar, then they are equal
theorem eq_of_bisim (bisim : IsBisimulation R) {s₁ s₂} (r : s₁ ~ s₂) : s₁ = s₂ :=
  by
  apply Subtype.eq
  apply Stream'.eq_of_bisim fun x y => ∃ s s' : Computation α, s.1 = x ∧ s'.1 = y ∧ R s s'
  dsimp [Stream'.IsBisimulation]
  intro t₁ t₂ e
  exact
    match t₁, t₂, e with
    | _, _, ⟨s, s', rfl, rfl, r⟩ =>
      by
      suffices head s = head s' ∧ R (tail s) (tail s') from
        And.imp id (fun r => ⟨tail s, tail s', by cases s <;> rfl, by cases s' <;> rfl, r⟩) this
      have := bisim r; revert r this
      apply rec_on s _ _ <;> intros <;> apply rec_on s' _ _ <;> intros <;> intro r this
      · constructor
        dsimp at this
        rw [this]
        assumption
      · rw [destruct_ret, destruct_think] at this
        exact False.elim this
      · rw [destruct_ret, destruct_think] at this
        exact False.elim this
      · simp at this
        simp [*]
  exact ⟨s₁, s₂, rfl, rfl, r⟩
#align computation.eq_of_bisim Computation.eq_of_bisim

end Bisim

-- It's more of a stretch to use ∈ for this relation, but it
-- asserts that the computation limits to the given value.
protected def Mem (a : α) (s : Computation α) :=
  some a ∈ s.1
#align computation.mem Computation.Mem

instance : Membership α (Computation α) :=
  ⟨Computation.Mem⟩

theorem le_stable (s : Computation α) {a m n} (h : m ≤ n) : s.1 m = some a → s.1 n = some a :=
  by
  cases' s with f al
  induction' h with n h IH
  exacts[id, fun h2 => al (IH h2)]
#align computation.le_stable Computation.le_stable

theorem mem_unique {s : Computation α} {a b : α} : a ∈ s → b ∈ s → a = b
  | ⟨m, ha⟩, ⟨n, hb⟩ => by
    injection
      (le_stable s (le_max_left m n) ha.symm).symm.trans (le_stable s (le_max_right m n) hb.symm)
#align computation.mem_unique Computation.mem_unique

theorem Mem.leftUnique : Relator.LeftUnique ((· ∈ ·) : α → Computation α → Prop) := fun a s b =>
  mem_unique
#align computation.mem.left_unique Computation.Mem.leftUnique

/-- `terminates s` asserts that the computation `s` eventually terminates with some value. -/
class Terminates (s : Computation α) : Prop where
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
      dsimp [Stream'.nth] at h
      rw [← h]
      exact rfl⟩,
    fun ⟨n, h⟩ => ⟨⟨Option.get h, n, (Option.eq_some_of_isSome h).symm⟩⟩⟩
#align computation.terminates_def Computation.terminates_def

theorem ret_mem (a : α) : a ∈ return a :=
  Exists.intro 0 rfl
#align computation.ret_mem Computation.ret_mem

theorem eq_of_ret_mem {a a' : α} (h : a' ∈ return a) : a' = a :=
  mem_unique h (ret_mem _)
#align computation.eq_of_ret_mem Computation.eq_of_ret_mem

instance ret_terminates (a : α) : Terminates (return a) :=
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
    contradiction
    exact ⟨n', h⟩
#align computation.of_think_mem Computation.of_think_mem

theorem of_think_terminates {s : Computation α} : Terminates (think s) → Terminates s
  | ⟨⟨a, h⟩⟩ => ⟨⟨a, of_think_mem h⟩⟩
#align computation.of_think_terminates Computation.of_think_terminates

theorem not_mem_empty (a : α) : a ∉ empty α := fun ⟨n, h⟩ => by clear _fun_match <;> contradiction
#align computation.not_mem_empty Computation.not_mem_empty

theorem not_terminates_empty : ¬Terminates (empty α) := fun ⟨⟨a, h⟩⟩ => not_mem_empty a h
#align computation.not_terminates_empty Computation.not_terminates_empty

theorem eq_empty_of_not_terminates {s} (H : ¬Terminates s) : s = empty α :=
  by
  apply Subtype.eq; funext n
  induction' h : s.val n with ; · rfl
  refine' absurd _ H; exact ⟨⟨_, _, h.symm⟩⟩
#align computation.eq_empty_of_not_terminates Computation.eq_empty_of_not_terminates

theorem thinkN_mem {s : Computation α} {a} : ∀ n, a ∈ thinkN s n ↔ a ∈ s
  | 0 => Iff.rfl
  | n + 1 => Iff.trans ⟨of_think_mem, think_mem⟩ (thinkN_mem n)
#align computation.thinkN_mem Computation.thinkN_mem

instance thinkN_terminates (s : Computation α) : ∀ [Terminates s] (n), Terminates (thinkN s n)
  | ⟨⟨a, h⟩⟩, n => ⟨⟨a, (thinkN_mem n).2 h⟩⟩
#align computation.thinkN_terminates Computation.thinkN_terminates

theorem of_thinkN_terminates (s : Computation α) (n) : Terminates (thinkN s n) → Terminates s
  | ⟨⟨a, h⟩⟩ => ⟨⟨a, (thinkN_mem _).1 h⟩⟩
#align computation.of_thinkN_terminates Computation.of_thinkN_terminates

/-- `promises s a`, or `s ~> a`, asserts that although the computation `s`
  may not terminate, if it does, then the result is `a`. -/
def Promises (s : Computation α) (a : α) : Prop :=
  ∀ ⦃a'⦄, a' ∈ s → a = a'
#align computation.promises Computation.Promises

-- mathport name: «expr ~> »
infixl:50 " ~> " => Promises

theorem mem_promises {s : Computation α} {a : α} : a ∈ s → s ~> a := fun h a' => mem_unique h
#align computation.mem_promises Computation.mem_promises

theorem empty_promises (a : α) : empty α ~> a := fun a' h => absurd h (not_mem_empty _)
#align computation.empty_promises Computation.empty_promises

section get

variable (s : Computation α) [h : Terminates s]

include s h

/-- `length s` gets the number of steps of a terminating computation -/
def length : ℕ :=
  Nat.find ((terminates_def _).1 h)
#align computation.length Computation.length

/-- `get s` returns the result of a terminating computation -/
def get : α :=
  Option.get (Nat.find_spec <| (terminates_def _).1 h)
#align computation.get Computation.get

theorem get_mem : get s ∈ s :=
  Exists.intro (length s) (Option.eq_some_of_isSome _).symm
#align computation.get_mem Computation.get_mem

theorem get_eq_of_mem {a} : a ∈ s → get s = a :=
  mem_unique (get_mem _)
#align computation.get_eq_of_mem Computation.get_eq_of_mem

theorem mem_of_get_eq {a} : get s = a → a ∈ s := by intro h <;> rw [← h] <;> apply get_mem
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
#align computation.get_thinkN Computation.get_thinkN

theorem get_promises : s ~> get s := fun a => get_eq_of_mem _
#align computation.get_promises Computation.get_promises

theorem mem_of_promises {a} (p : s ~> a) : a ∈ s :=
  by
  cases h
  cases' h with a' h
  rw [p h]
  exact h
#align computation.mem_of_promises Computation.mem_of_promises

theorem get_eq_of_promises {a} : s ~> a → get s = a :=
  get_eq_of_mem _ ∘ mem_of_promises _
#align computation.get_eq_of_promises Computation.get_eq_of_promises

end get

/-- `results s a n` completely characterizes a terminating computation:
  it asserts that `s` terminates after exactly `n` steps, with result `a`. -/
def Results (s : Computation α) (a : α) (n : ℕ) :=
  ∃ h : a ∈ s, @length _ s (terminates_of_mem h) = n
#align computation.results Computation.Results

theorem results_of_terminates (s : Computation α) [T : Terminates s] :
    Results s (get s) (length s) :=
  ⟨get_mem _, rfl⟩
#align computation.results_of_terminates Computation.results_of_terminates

theorem results_of_terminates' (s : Computation α) [T : Terminates s] {a} (h : a ∈ s) :
    Results s a (length s) := by rw [← get_eq_of_mem _ h] <;> apply results_of_terminates
#align computation.results_of_terminates' Computation.results_of_terminates'

theorem Results.mem {s : Computation α} {a n} : Results s a n → a ∈ s
  | ⟨m, _⟩ => m
#align computation.results.mem Computation.Results.mem

theorem Results.terminates {s : Computation α} {a n} (h : Results s a n) : Terminates s :=
  terminates_of_mem h.Mem
#align computation.results.terminates Computation.Results.terminates

theorem Results.length {s : Computation α} {a n} [T : Terminates s] : Results s a n → length s = n
  | ⟨_, h⟩ => h
#align computation.results.length Computation.Results.length

theorem Results.val_unique {s : Computation α} {a b m n} (h1 : Results s a m) (h2 : Results s b n) :
    a = b :=
  mem_unique h1.Mem h2.Mem
#align computation.results.val_unique Computation.Results.val_unique

theorem Results.len_unique {s : Computation α} {a b m n} (h1 : Results s a m) (h2 : Results s b n) :
    m = n := by haveI := h1.terminates <;> haveI := h2.terminates <;> rw [← h1.length, h2.length]
#align computation.results.len_unique Computation.Results.len_unique

theorem exists_results_of_mem {s : Computation α} {a} (h : a ∈ s) : ∃ n, Results s a n :=
  haveI := terminates_of_mem h
  ⟨_, results_of_terminates' s h⟩
#align computation.exists_results_of_mem Computation.exists_results_of_mem

@[simp]
theorem get_ret (a : α) : get (return a) = a :=
  get_eq_of_mem _ ⟨0, rfl⟩
#align computation.get_ret Computation.get_ret

@[simp]
theorem length_ret (a : α) : length (return a) = 0 :=
  let h := Computation.ret_terminates a
  Nat.eq_zero_of_le_zero <| Nat.find_min' ((terminates_def (return a)).1 h) rfl
#align computation.length_ret Computation.length_ret

theorem results_ret (a : α) : Results (return a) a 0 :=
  ⟨_, length_ret _⟩
#align computation.results_ret Computation.results_ret

@[simp]
theorem length_think (s : Computation α) [h : Terminates s] : length (think s) = length s + 1 :=
  by
  apply le_antisymm
  · exact Nat.find_min' _ (Nat.find_spec ((terminates_def _).1 h))
  · have : (Option.isSome ((think s).val (length (think s))) : Prop) :=
      Nat.find_spec ((terminates_def _).1 s.think_terminates)
    cases' length (think s) with n
    · contradiction
    · apply Nat.succ_le_succ
      apply Nat.find_min'
      apply this
#align computation.length_think Computation.length_think

theorem results_think {s : Computation α} {a n} (h : Results s a n) : Results (think s) a (n + 1) :=
  haveI := h.terminates
  ⟨think_mem h.mem, by rw [length_think, h.length]⟩
#align computation.results_think Computation.results_think

theorem of_results_think {s : Computation α} {a n} (h : Results (think s) a n) :
    ∃ m, Results s a m ∧ n = m + 1 :=
  by
  haveI := of_think_terminates h.terminates
  have := results_of_terminates' _ (of_think_mem h.mem)
  exact ⟨_, this, results.len_unique h (results_think this)⟩
#align computation.of_results_think Computation.of_results_think

@[simp]
theorem results_think_iff {s : Computation α} {a n} : Results (think s) a (n + 1) ↔ Results s a n :=
  ⟨fun h => by
    let ⟨n', r, e⟩ := of_results_think h
    injection e with h' <;> rwa [h'], results_think⟩
#align computation.results_think_iff Computation.results_think_iff

theorem results_thinkN {s : Computation α} {a m} :
    ∀ n, Results s a m → Results (thinkN s n) a (m + n)
  | 0, h => h
  | n + 1, h => results_think (results_thinkN n h)
#align computation.results_thinkN Computation.results_thinkN

theorem results_thinkN_ret (a : α) (n) : Results (thinkN (return a) n) a n := by
  have := results_thinkN n (results_ret a) <;> rwa [Nat.zero_add] at this
#align computation.results_thinkN_ret Computation.results_thinkN_ret

@[simp]
theorem length_thinkN (s : Computation α) [h : Terminates s] (n) :
    length (thinkN s n) = length s + n :=
  (results_thinkN n (results_of_terminates _)).length
#align computation.length_thinkN Computation.length_thinkN

theorem eq_thinkN {s : Computation α} {a n} (h : Results s a n) : s = thinkN (return a) n :=
  by
  revert s
  induction' n with n IH <;> intro s <;> apply rec_on s (fun a' => _) fun s => _ <;> intro h
  · rw [← eq_of_ret_mem h.mem]
    rfl
  · cases' of_results_think h with n h
    cases h
    contradiction
  · have := h.len_unique (results_ret _)
    contradiction
  · rw [IH (results_think_iff.1 h)]
    rfl
#align computation.eq_thinkN Computation.eq_thinkN

theorem eq_thinkN' (s : Computation α) [h : Terminates s] :
    s = thinkN (return (get s)) (length s) :=
  eq_thinkN (results_of_terminates _)
#align computation.eq_thinkN' Computation.eq_thinkN'

def memRecOn {C : Computation α → Sort v} {a s} (M : a ∈ s) (h1 : C (return a))
    (h2 : ∀ s, C s → C (think s)) : C s :=
  by
  haveI T := terminates_of_mem M
  rw [eq_thinkN' s, get_eq_of_mem s M]
  generalize length s = n
  induction' n with n IH; exacts[h1, h2 _ IH]
#align computation.mem_rec_on Computation.memRecOn

def terminatesRecOn {C : Computation α → Sort v} (s) [Terminates s] (h1 : ∀ a, C (return a))
    (h2 : ∀ s, C s → C (think s)) : C s :=
  memRecOn (get_mem s) (h1 _) h2
#align computation.terminates_rec_on Computation.terminatesRecOn

/-- Map a function on the result of a computation. -/
def map (f : α → β) : Computation α → Computation β
  | ⟨s, al⟩ =>
    ⟨s.map fun o => Option.casesOn o none (some ∘ f), fun n b =>
      by
      dsimp [Stream'.map, Stream'.nth]
      induction' e : s n with a <;> intro h
      · contradiction; · rw [al e, ← h]⟩
#align computation.map Computation.map

def Bind.g : Sum β (Computation β) → Sum β (Sum (Computation α) (Computation β))
  | Sum.inl b => Sum.inl b
  | Sum.inr cb' => Sum.inr <| Sum.inr cb'
#align computation.bind.G Computation.Bind.g

def Bind.f (f : α → Computation β) :
    Sum (Computation α) (Computation β) → Sum β (Sum (Computation α) (Computation β))
  | Sum.inl ca =>
    match destruct ca with
    | Sum.inl a => bind.G <| destruct (f a)
    | Sum.inr ca' => Sum.inr <| Sum.inl ca'
  | Sum.inr cb => bind.G <| destruct cb
#align computation.bind.F Computation.Bind.f

/-- Compose two computations into a monadic `bind` operation. -/
def bind (c : Computation α) (f : α → Computation β) : Computation β :=
  corec (Bind.f f) (Sum.inl c)
#align computation.bind Computation.bind

instance : Bind Computation :=
  ⟨@bind⟩

theorem hasBind_eq_bind {β} (c : Computation α) (f : α → Computation β) : c >>= f = bind c f :=
  rfl
#align computation.has_bind_eq_bind Computation.hasBind_eq_bind

/-- Flatten a computation of computations into a single computation. -/
def join (c : Computation (Computation α)) : Computation α :=
  c >>= id
#align computation.join Computation.join

@[simp]
theorem map_ret (f : α → β) (a) : map f (return a) = return (f a) :=
  rfl
#align computation.map_ret Computation.map_ret

@[simp]
theorem map_think (f : α → β) : ∀ s, map f (think s) = think (map f s)
  | ⟨s, al⟩ => by apply Subtype.eq <;> dsimp [think, map] <;> rw [Stream'.map_cons]
#align computation.map_think Computation.map_think

@[simp]
theorem destruct_map (f : α → β) (s) : destruct (map f s) = lmap f (rmap (map f) (destruct s)) := by
  apply s.rec_on <;> intro <;> simp
#align computation.destruct_map Computation.destruct_map

@[simp]
theorem map_id : ∀ s : Computation α, map id s = s
  | ⟨f, al⟩ => by
    apply Subtype.eq <;> simp [map, Function.comp]
    have e : @Option.rec α (fun _ => Option α) none some = id := by ext ⟨⟩ <;> rfl
    simp [e, Stream'.map_id]
#align computation.map_id Computation.map_id

theorem map_comp (f : α → β) (g : β → γ) : ∀ s : Computation α, map (g ∘ f) s = map g (map f s)
  | ⟨s, al⟩ => by
    apply Subtype.eq <;> dsimp [map]
    rw [Stream'.map_map]
    apply congr_arg fun f : _ → Option γ => Stream'.map f s
    ext ⟨⟩ <;> rfl
#align computation.map_comp Computation.map_comp

@[simp]
theorem ret_bind (a) (f : α → Computation β) : bind (return a) f = f a :=
  by
  apply
    eq_of_bisim fun c₁ c₂ => c₁ = bind (return a) f ∧ c₂ = f a ∨ c₁ = corec (bind.F f) (Sum.inr c₂)
  · intro c₁ c₂ h
    exact
      match c₁, c₂, h with
      | _, _, Or.inl ⟨rfl, rfl⟩ => by
        simp [bind, bind.F]
        cases' destruct (f a) with b cb <;> simp [bind.G]
      | _, c, Or.inr rfl => by
        simp [bind.F]
        cases' destruct c with b cb <;> simp [bind.G]
  · simp
#align computation.ret_bind Computation.ret_bind

@[simp]
theorem think_bind (c) (f : α → Computation β) : bind (think c) f = think (bind c f) :=
  destruct_eq_think <| by simp [bind, bind.F]
#align computation.think_bind Computation.think_bind

@[simp]
theorem bind_ret (f : α → β) (s) : bind s (return ∘ f) = map f s :=
  by
  apply eq_of_bisim fun c₁ c₂ => c₁ = c₂ ∨ ∃ s, c₁ = bind s (return ∘ f) ∧ c₂ = map f s
  · intro c₁ c₂ h
    exact
      match c₁, c₂, h with
      | _, _, Or.inl (Eq.refl c) => by cases' destruct c with b cb <;> simp
      | _, _, Or.inr ⟨s, rfl, rfl⟩ =>
        by
        apply rec_on s <;> intro s <;> simp
        exact Or.inr ⟨s, rfl, rfl⟩
  · exact Or.inr ⟨s, rfl, rfl⟩
#align computation.bind_ret Computation.bind_ret

@[simp]
theorem bind_ret' (s : Computation α) : bind s return = s := by
  rw [bind_ret] <;> change fun x : α => x with @id α <;> rw [map_id]
#align computation.bind_ret' Computation.bind_ret'

@[simp]
theorem bind_assoc (s : Computation α) (f : α → Computation β) (g : β → Computation γ) :
    bind (bind s f) g = bind s fun x : α => bind (f x) g :=
  by
  apply
    eq_of_bisim fun c₁ c₂ =>
      c₁ = c₂ ∨ ∃ s, c₁ = bind (bind s f) g ∧ c₂ = bind s fun x : α => bind (f x) g
  · intro c₁ c₂ h
    exact
      match c₁, c₂, h with
      | _, _, Or.inl (Eq.refl c) => by cases' destruct c with b cb <;> simp
      | _, _, Or.inr ⟨s, rfl, rfl⟩ =>
        by
        apply rec_on s <;> intro s <;> simp
        · generalize f s = fs
          apply rec_on fs <;> intro t <;> simp
          · cases' destruct (g t) with b cb <;> simp
        · exact Or.inr ⟨s, rfl, rfl⟩
  · exact Or.inr ⟨s, rfl, rfl⟩
#align computation.bind_assoc Computation.bind_assoc

theorem results_bind {s : Computation α} {f : α → Computation β} {a b m n} (h1 : Results s a m)
    (h2 : Results (f a) b n) : Results (bind s f) b (n + m) :=
  by
  have := h1.mem; revert m
  apply mem_rec_on this _ fun s IH => _ <;> intro m h1
  · rw [ret_bind]
    rw [h1.len_unique (results_ret _)]
    exact h2
  · rw [think_bind]
    cases' of_results_think h1 with m' h
    cases' h with h1 e
    rw [e]
    exact results_think (IH h1)
#align computation.results_bind Computation.results_bind

theorem mem_bind {s : Computation α} {f : α → Computation β} {a b} (h1 : a ∈ s) (h2 : b ∈ f a) :
    b ∈ bind s f :=
  let ⟨m, h1⟩ := exists_results_of_mem h1
  let ⟨n, h2⟩ := exists_results_of_mem h2
  (results_bind h1 h2).Mem
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
theorem length_bind (s : Computation α) (f : α → Computation β) [T1 : Terminates s]
    [T2 : Terminates (f (get s))] : length (bind s f) = length (f (get s)) + length s :=
  (results_of_terminates _).len_unique <|
    results_bind (results_of_terminates _) (results_of_terminates _)
#align computation.length_bind Computation.length_bind

theorem of_results_bind {s : Computation α} {f : α → Computation β} {b k} :
    Results (bind s f) b k → ∃ a m n, Results s a m ∧ Results (f a) b n ∧ k = n + m :=
  by
  induction' k with n IH generalizing s <;> apply rec_on s (fun a => _) fun s' => _ <;> intro e
  · simp [thinkN] at e
    refine' ⟨a, _, _, results_ret _, e, rfl⟩
  · have := congr_arg head (eq_thinkN e)
    contradiction
  · simp at e
    refine' ⟨a, _, n + 1, results_ret _, e, rfl⟩
  · simp at e
    exact by
      let ⟨a, m, n', h1, h2, e'⟩ := IH e
      rw [e'] <;> exact ⟨a, m.succ, n', results_think h1, h2, rfl⟩
#align computation.of_results_bind Computation.of_results_bind

theorem exists_of_mem_bind {s : Computation α} {f : α → Computation β} {b} (h : b ∈ bind s f) :
    ∃ a ∈ s, b ∈ f a :=
  let ⟨k, h⟩ := exists_results_of_mem h
  let ⟨a, m, n, h1, h2, e⟩ := of_results_bind h
  ⟨a, h1.Mem, h2.Mem⟩
#align computation.exists_of_mem_bind Computation.exists_of_mem_bind

theorem bind_promises {s : Computation α} {f : α → Computation β} {a b} (h1 : s ~> a)
    (h2 : f a ~> b) : bind s f ~> b := fun b' bB =>
  by
  rcases exists_of_mem_bind bB with ⟨a', a's, ba'⟩
  rw [← h1 a's] at ba'; exact h2 ba'
#align computation.bind_promises Computation.bind_promises

instance : Monad Computation where
  map := @map
  pure := @return
  bind := @bind

instance : LawfulMonad Computation where
  id_map := @map_id
  bind_pure_comp_eq_map := @bind_ret
  pure_bind := @ret_bind
  bind_assoc := @bind_assoc

theorem has_map_eq_map {β} (f : α → β) (c : Computation α) : f <$> c = map f c :=
  rfl
#align computation.has_map_eq_map Computation.has_map_eq_map

@[simp]
theorem return_def (a) : (return a : Computation α) = return a :=
  rfl
#align computation.return_def Computation.return_def

@[simp]
theorem map_ret' {α β} : ∀ (f : α → β) (a), f <$> return a = return (f a) :=
  map_ret
#align computation.map_ret' Computation.map_ret'

@[simp]
theorem map_think' {α β} : ∀ (f : α → β) (s), f <$> think s = think (f <$> s) :=
  map_think
#align computation.map_think' Computation.map_think'

theorem mem_map (f : α → β) {a} {s : Computation α} (m : a ∈ s) : f a ∈ map f s := by
  rw [← bind_ret] <;> apply mem_bind m <;> apply ret_mem
#align computation.mem_map Computation.mem_map

theorem exists_of_mem_map {f : α → β} {b : β} {s : Computation α} (h : b ∈ map f s) :
    ∃ a, a ∈ s ∧ f a = b := by
  rw [← bind_ret] at h <;>
    exact
      let ⟨a, as, fb⟩ := exists_of_mem_bind h
      ⟨a, as, mem_unique (ret_mem _) fb⟩
#align computation.exists_of_mem_map Computation.exists_of_mem_map

instance terminates_map (f : α → β) (s : Computation α) [Terminates s] : Terminates (map f s) := by
  rw [← bind_ret] <;> infer_instance
#align computation.terminates_map Computation.terminates_map

theorem terminates_map_iff (f : α → β) (s : Computation α) : Terminates (map f s) ↔ Terminates s :=
  ⟨fun ⟨⟨a, h⟩⟩ =>
    let ⟨b, h1, _⟩ := exists_of_mem_map h
    ⟨⟨_, h1⟩⟩,
    @Computation.terminates_map _ _ _ _⟩
#align computation.terminates_map_iff Computation.terminates_map_iff

-- Parallel computation
/-- `c₁ <|> c₂` calculates `c₁` and `c₂` simultaneously, returning
  the first one that gives a result. -/
def orelse (c₁ c₂ : Computation α) : Computation α :=
  @Computation.corec α (Computation α × Computation α)
    (fun ⟨c₁, c₂⟩ =>
      match destruct c₁ with
      | Sum.inl a => Sum.inl a
      | Sum.inr c₁' =>
        match destruct c₂ with
        | Sum.inl a => Sum.inl a
        | Sum.inr c₂' => Sum.inr (c₁', c₂'))
    (c₁, c₂)
#align computation.orelse Computation.orelse

instance : Alternative Computation :=
  { Computation.monad with
    orelse := @orelse
    failure := @empty }

@[simp]
theorem ret_orelse (a : α) (c₂ : Computation α) : (return a <|> c₂) = return a :=
  destruct_eq_ret <| by unfold HasOrelse.orelse <;> simp [orelse]
#align computation.ret_orelse Computation.ret_orelse

@[simp]
theorem orelse_ret (c₁ : Computation α) (a : α) : (think c₁ <|> return a) = return a :=
  destruct_eq_ret <| by unfold HasOrelse.orelse <;> simp [orelse]
#align computation.orelse_ret Computation.orelse_ret

@[simp]
theorem orelse_think (c₁ c₂ : Computation α) : (think c₁ <|> think c₂) = think (c₁ <|> c₂) :=
  destruct_eq_think <| by unfold HasOrelse.orelse <;> simp [orelse]
#align computation.orelse_think Computation.orelse_think

@[simp]
theorem empty_orelse (c) : (empty α <|> c) = c :=
  by
  apply eq_of_bisim (fun c₁ c₂ => (Empty α <|> c₂) = c₁) _ rfl
  intro s' s h; rw [← h]
  apply rec_on s <;> intro s <;> rw [think_empty] <;> simp
  rw [← think_empty]
#align computation.empty_orelse Computation.empty_orelse

@[simp]
theorem orelse_empty (c : Computation α) : (c <|> empty α) = c :=
  by
  apply eq_of_bisim (fun c₁ c₂ => (c₂ <|> Empty α) = c₁) _ rfl
  intro s' s h; rw [← h]
  apply rec_on s <;> intro s <;> rw [think_empty] <;> simp
  rw [← think_empty]
#align computation.orelse_empty Computation.orelse_empty

/-- `c₁ ~ c₂` asserts that `c₁` and `c₂` either both terminate with the same result,
  or both loop forever. -/
def Equiv (c₁ c₂ : Computation α) : Prop :=
  ∀ a, a ∈ c₁ ↔ a ∈ c₂
#align computation.equiv Computation.Equiv

-- mathport name: «expr ~ »
infixl:50 " ~ " => Equiv

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
  ⟨fun ma => by rw [mem_unique ma h1] <;> exact h2, fun ma => by rw [mem_unique ma h2] <;> exact h1⟩
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

theorem think_equiv (s : Computation α) : think s ~ s := fun a => ⟨of_think_mem, think_mem⟩
#align computation.think_equiv Computation.think_equiv

theorem thinkN_equiv (s : Computation α) (n) : thinkN s n ~ s := fun a => thinkN_mem n
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

theorem equiv_ret_of_mem {s : Computation α} {a} (h : a ∈ s) : s ~ return a :=
  equiv_of_mem h (ret_mem _)
#align computation.equiv_ret_of_mem Computation.equiv_ret_of_mem

/-- `lift_rel R ca cb` is a generalization of `equiv` to relations other than
  equality. It asserts that if `ca` terminates with `a`, then `cb` terminates with
  some `b` such that `R a b`, and if `cb` terminates with `b` then `ca` terminates
  with some `a` such that `R a b`. -/
def LiftRel (R : α → β → Prop) (ca : Computation α) (cb : Computation β) : Prop :=
  (∀ {a}, a ∈ ca → ∃ b, b ∈ cb ∧ R a b) ∧ ∀ {b}, b ∈ cb → ∃ a, a ∈ ca ∧ R a b
#align computation.lift_rel Computation.LiftRel

theorem LiftRel.swap (R : α → β → Prop) (ca : Computation α) (cb : Computation β) :
    LiftRel (swap R) cb ca ↔ LiftRel R ca cb :=
  and_comm' _ _
#align computation.lift_rel.swap Computation.LiftRel.swap

theorem lift_eq_iff_equiv (c₁ c₂ : Computation α) : LiftRel (· = ·) c₁ c₂ ↔ c₁ ~ c₂ :=
  ⟨fun ⟨h1, h2⟩ a =>
    ⟨fun a1 => by
      let ⟨b, b2, ab⟩ := h1 a1
      rwa [ab], fun a2 => by
      let ⟨b, b1, ab⟩ := h2 a2
      rwa [← ab]⟩,
    fun e => ⟨fun a a1 => ⟨a, (e _).1 a1, rfl⟩, fun a a2 => ⟨a, (e _).2 a2, rfl⟩⟩⟩
#align computation.lift_eq_iff_equiv Computation.lift_eq_iff_equiv

theorem LiftRel.refl (R : α → α → Prop) (H : Reflexive R) : Reflexive (LiftRel R) := fun s =>
  ⟨fun a as => ⟨a, as, H a⟩, fun b bs => ⟨b, bs, H b⟩⟩
#align computation.lift_rel.refl Computation.LiftRel.refl

theorem LiftRel.symm (R : α → α → Prop) (H : Symmetric R) : Symmetric (LiftRel R) :=
  fun s1 s2 ⟨l, r⟩ =>
  ⟨fun a a2 =>
    let ⟨b, b1, ab⟩ := r a2
    ⟨b, b1, H ab⟩,
    fun a a1 =>
    let ⟨b, b2, ab⟩ := l a1
    ⟨b, b2, H ab⟩⟩
#align computation.lift_rel.symm Computation.LiftRel.symm

theorem LiftRel.trans (R : α → α → Prop) (H : Transitive R) : Transitive (LiftRel R) :=
  fun s1 s2 s3 ⟨l1, r1⟩ ⟨l2, r2⟩ =>
  ⟨fun a a1 =>
    let ⟨b, b2, ab⟩ := l1 a1
    let ⟨c, c3, bc⟩ := l2 b2
    ⟨c, c3, H ab bc⟩,
    fun c c3 =>
    let ⟨b, b2, bc⟩ := r2 c3
    let ⟨a, a1, ab⟩ := r1 b2
    ⟨a, a1, H ab bc⟩⟩
#align computation.lift_rel.trans Computation.LiftRel.trans

theorem LiftRel.equiv (R : α → α → Prop) : Equivalence R → Equivalence (LiftRel R)
  | ⟨refl, symm, trans⟩ => ⟨LiftRel.refl R refl, LiftRel.symm R symm, LiftRel.trans R trans⟩
#align computation.lift_rel.equiv Computation.LiftRel.equiv

theorem LiftRel.imp {R S : α → β → Prop} (H : ∀ {a b}, R a b → S a b) (s t) :
    LiftRel R s t → LiftRel S s t
  | ⟨l, r⟩ =>
    ⟨fun a as =>
      let ⟨b, bt, ab⟩ := l as
      ⟨b, bt, H ab⟩,
      fun b bt =>
      let ⟨a, as, ab⟩ := r bt
      ⟨a, as, H ab⟩⟩
#align computation.lift_rel.imp Computation.LiftRel.imp

theorem terminates_of_liftRel {R : α → β → Prop} {s t} :
    LiftRel R s t → (Terminates s ↔ Terminates t)
  | ⟨l, r⟩ =>
    ⟨fun ⟨⟨a, as⟩⟩ =>
      let ⟨b, bt, ab⟩ := l as
      ⟨⟨b, bt⟩⟩,
      fun ⟨⟨b, bt⟩⟩ =>
      let ⟨a, as, ab⟩ := r bt
      ⟨⟨a, as⟩⟩⟩
#align computation.terminates_of_lift_rel Computation.terminates_of_liftRel

theorem rel_of_liftRel {R : α → β → Prop} {ca cb} :
    LiftRel R ca cb → ∀ {a b}, a ∈ ca → b ∈ cb → R a b
  | ⟨l, r⟩, a, b, ma, mb => by
    let ⟨b', mb', ab'⟩ := l ma
    rw [mem_unique mb mb'] <;> exact ab'
#align computation.rel_of_lift_rel Computation.rel_of_liftRel

theorem liftRel_of_mem {R : α → β → Prop} {a b ca cb} (ma : a ∈ ca) (mb : b ∈ cb) (ab : R a b) :
    LiftRel R ca cb :=
  ⟨fun a' ma' => by rw [mem_unique ma' ma] <;> exact ⟨b, mb, ab⟩, fun b' mb' => by
    rw [mem_unique mb' mb] <;> exact ⟨a, ma, ab⟩⟩
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
    ⟨terminates_of_liftRel h, fun a b ma mb =>
      by
      let ⟨b', mb', ab⟩ := h.left ma
      rwa [mem_unique mb mb']⟩,
    fun ⟨l, r⟩ =>
    ⟨fun a ma =>
      let ⟨⟨b, mb⟩⟩ := l.1 ⟨⟨_, ma⟩⟩
      ⟨b, mb, r ma mb⟩,
      fun b mb =>
      let ⟨⟨a, ma⟩⟩ := l.2 ⟨⟨_, mb⟩⟩
      ⟨a, ma, r ma mb⟩⟩⟩
#align computation.lift_rel_def Computation.liftRel_def

theorem liftRel_bind {δ} (R : α → β → Prop) (S : γ → δ → Prop) {s1 : Computation α}
    {s2 : Computation β} {f1 : α → Computation γ} {f2 : β → Computation δ} (h1 : LiftRel R s1 s2)
    (h2 : ∀ {a b}, R a b → LiftRel S (f1 a) (f2 b)) : LiftRel S (bind s1 f1) (bind s2 f2) :=
  let ⟨l1, r1⟩ := h1
  ⟨fun c cB =>
    let ⟨a, a1, c₁⟩ := exists_of_mem_bind cB
    let ⟨b, b2, ab⟩ := l1 a1
    let ⟨l2, r2⟩ := h2 ab
    let ⟨d, d2, cd⟩ := l2 c₁
    ⟨_, mem_bind b2 d2, cd⟩,
    fun d dB =>
    let ⟨b, b1, d1⟩ := exists_of_mem_bind dB
    let ⟨a, a2, ab⟩ := r1 b1
    let ⟨l2, r2⟩ := h2 ab
    let ⟨c, c₂, cd⟩ := r2 d1
    ⟨_, mem_bind a2 c₂, cd⟩⟩
#align computation.lift_rel_bind Computation.liftRel_bind

@[simp]
theorem liftRel_return_left (R : α → β → Prop) (a : α) (cb : Computation β) :
    LiftRel R (return a) cb ↔ ∃ b, b ∈ cb ∧ R a b :=
  ⟨fun ⟨l, r⟩ => l (ret_mem _), fun ⟨b, mb, ab⟩ =>
    ⟨fun a' ma' => by rw [eq_of_ret_mem ma'] <;> exact ⟨b, mb, ab⟩, fun b' mb' =>
      ⟨_, ret_mem _, by rw [mem_unique mb' mb] <;> exact ab⟩⟩⟩
#align computation.lift_rel_return_left Computation.liftRel_return_left

@[simp]
theorem liftRel_return_right (R : α → β → Prop) (ca : Computation α) (b : β) :
    LiftRel R ca (return b) ↔ ∃ a, a ∈ ca ∧ R a b := by rw [lift_rel.swap, lift_rel_return_left]
#align computation.lift_rel_return_right Computation.liftRel_return_right

@[simp]
theorem liftRel_return (R : α → β → Prop) (a : α) (b : β) :
    LiftRel R (return a) (return b) ↔ R a b := by
  rw [lift_rel_return_left] <;>
    exact ⟨fun ⟨b', mb', ab'⟩ => by rwa [eq_of_ret_mem mb'] at ab', fun ab => ⟨_, ret_mem _, ab⟩⟩
#align computation.lift_rel_return Computation.liftRel_return

@[simp]
theorem liftRel_think_left (R : α → β → Prop) (ca : Computation α) (cb : Computation β) :
    LiftRel R (think ca) cb ↔ LiftRel R ca cb :=
  and_congr (forall_congr' fun b => imp_congr ⟨of_think_mem, think_mem⟩ Iff.rfl)
    (forall_congr' fun b =>
      imp_congr Iff.rfl <| exists_congr fun b => and_congr ⟨of_think_mem, think_mem⟩ Iff.rfl)
#align computation.lift_rel_think_left Computation.liftRel_think_left

@[simp]
theorem liftRel_think_right (R : α → β → Prop) (ca : Computation α) (cb : Computation β) :
    LiftRel R ca (think cb) ↔ LiftRel R ca cb := by
  rw [← lift_rel.swap R, ← lift_rel.swap R] <;> apply lift_rel_think_left
#align computation.lift_rel_think_right Computation.liftRel_think_right

theorem liftRel_mem_cases {R : α → β → Prop} {ca cb} (Ha : ∀ a ∈ ca, LiftRel R ca cb)
    (Hb : ∀ b ∈ cb, LiftRel R ca cb) : LiftRel R ca cb :=
  ⟨fun a ma => (Ha _ ma).left ma, fun b mb => (Hb _ mb).right mb⟩
#align computation.lift_rel_mem_cases Computation.liftRel_mem_cases

theorem liftRel_congr {R : α → β → Prop} {ca ca' : Computation α} {cb cb' : Computation β}
    (ha : ca ~ ca') (hb : cb ~ cb') : LiftRel R ca cb ↔ LiftRel R ca' cb' :=
  and_congr
    (forall_congr' fun a => imp_congr (ha _) <| exists_congr fun b => and_congr (hb _) Iff.rfl)
    (forall_congr' fun b => imp_congr (hb _) <| exists_congr fun a => and_congr (ha _) Iff.rfl)
#align computation.lift_rel_congr Computation.liftRel_congr

theorem liftRel_map {δ} (R : α → β → Prop) (S : γ → δ → Prop) {s1 : Computation α}
    {s2 : Computation β} {f1 : α → γ} {f2 : β → δ} (h1 : LiftRel R s1 s2)
    (h2 : ∀ {a b}, R a b → S (f1 a) (f2 b)) : LiftRel S (map f1 s1) (map f2 s2) := by
  rw [← bind_ret, ← bind_ret] <;> apply lift_rel_bind _ _ h1 <;> simp <;> exact @h2
#align computation.lift_rel_map Computation.liftRel_map

theorem map_congr (R : α → α → Prop) (S : β → β → Prop) {s1 s2 : Computation α} {f : α → β}
    (h1 : s1 ~ s2) : map f s1 ~ map f s2 := by
  rw [← lift_eq_iff_equiv] <;>
    exact lift_rel_map Eq _ ((lift_eq_iff_equiv _ _).2 h1) fun a b => congr_arg _
#align computation.map_congr Computation.map_congr

def LiftRelAux (R : α → β → Prop) (C : Computation α → Computation β → Prop) :
    Sum α (Computation α) → Sum β (Computation β) → Prop
  | Sum.inl a, Sum.inl b => R a b
  | Sum.inl a, Sum.inr cb => ∃ b, b ∈ cb ∧ R a b
  | Sum.inr ca, Sum.inl b => ∃ a, a ∈ ca ∧ R a b
  | Sum.inr ca, Sum.inr cb => C ca cb
#align computation.lift_rel_aux Computation.LiftRelAux

attribute [simp] lift_rel_aux

@[simp]
theorem LiftRelAux.ret_left (R : α → β → Prop) (C : Computation α → Computation β → Prop) (a cb) :
    LiftRelAux R C (Sum.inl a) (destruct cb) ↔ ∃ b, b ∈ cb ∧ R a b :=
  by
  apply cb.rec_on (fun b => _) fun cb => _
  ·
    exact
      ⟨fun h => ⟨_, ret_mem _, h⟩, fun ⟨b', mb, h⟩ => by rw [mem_unique (ret_mem _) mb] <;> exact h⟩
  · rw [destruct_think]
    exact ⟨fun ⟨b, h, r⟩ => ⟨b, think_mem h, r⟩, fun ⟨b, h, r⟩ => ⟨b, of_think_mem h, r⟩⟩
#align computation.lift_rel_aux.ret_left Computation.LiftRelAux.ret_left

theorem LiftRelAux.swap (R : α → β → Prop) (C) (a b) :
    LiftRelAux (swap R) (swap C) b a = LiftRelAux R C a b := by
  cases' a with a ca <;> cases' b with b cb <;> simp only [lift_rel_aux]
#align computation.lift_rel_aux.swap Computation.LiftRelAux.swap

@[simp]
theorem LiftRelAux.ret_right (R : α → β → Prop) (C : Computation α → Computation β → Prop) (b ca) :
    LiftRelAux R C (destruct ca) (Sum.inl b) ↔ ∃ a, a ∈ ca ∧ R a b := by
  rw [← lift_rel_aux.swap, lift_rel_aux.ret_left]
#align computation.lift_rel_aux.ret_right Computation.LiftRelAux.ret_right

theorem LiftRelRec.lem {R : α → β → Prop} (C : Computation α → Computation β → Prop)
    (H : ∀ {ca cb}, C ca cb → LiftRelAux R C (destruct ca) (destruct cb)) (ca cb) (Hc : C ca cb) (a)
    (ha : a ∈ ca) : LiftRel R ca cb := by
  revert cb; refine' mem_rec_on ha _ fun ca' IH => _ <;> intro cb Hc <;> have h := H Hc
  · simp at h
    simp [h]
  · have h := H Hc
    simp
    revert h
    apply cb.rec_on (fun b => _) fun cb' => _ <;> intro h <;> simp at h <;> simp [h]
    exact IH _ h
#align computation.lift_rel_rec.lem Computation.LiftRelRec.lem

theorem liftRel_rec {R : α → β → Prop} (C : Computation α → Computation β → Prop)
    (H : ∀ {ca cb}, C ca cb → LiftRelAux R C (destruct ca) (destruct cb)) (ca cb) (Hc : C ca cb) :
    LiftRel R ca cb :=
  liftRel_mem_cases (LiftRelRec.lem C (@H) ca cb Hc) fun b hb =>
    (LiftRel.swap _ _ _).2 <|
      LiftRelRec.lem (swap C) (fun cb ca h => cast (LiftRelAux.swap _ _ _ _).symm <| H h) cb ca Hc b
        hb
#align computation.lift_rel_rec Computation.liftRel_rec

end Computation

