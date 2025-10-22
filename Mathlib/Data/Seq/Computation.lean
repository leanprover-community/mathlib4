/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Nat.Find
import Mathlib.Data.Stream.Init
import Mathlib.Tactic.Common

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

namespace Computation

variable {α : Type u} {β : Type v} {γ : Type w}

-- constructors
/-- `pure a` is the computation that immediately terminates with result `a`. -/
def pure (a : α) : Computation α :=
  ⟨Stream'.const (some a), fun _ _ => id⟩

instance : CoeTC α (Computation α) :=
  ⟨pure⟩

-- note [use has_coe_t]
/-- `think c` is the computation that delays for one "tick" and then performs
  computation `c`. -/
def think (c : Computation α) : Computation α :=
  ⟨Stream'.cons none c.1, fun n a h => by
    rcases n with - | n
    · contradiction
    · exact c.2 h⟩

/-- `thinkN c n` is the computation that delays for `n` ticks and then performs
  computation `c`. -/
def thinkN (c : Computation α) : ℕ → Computation α
  | 0 => c
  | n + 1 => think (thinkN c n)

-- check for immediate result
/-- `head c` is the first step of computation, either `some a` if `c = pure a`
  or `none` if `c = think c'`. -/
def head (c : Computation α) : Option α :=
  c.1.head

-- one step of computation
/-- `tail c` is the remainder of computation, either `c` if `c = pure a`
  or `c'` if `c = think c'`. -/
def tail (c : Computation α) : Computation α :=
  ⟨c.1.tail, fun _ _ h => c.2 h⟩

/-- `empty α` is the computation that never returns, an infinite sequence of
  `think`s. -/
def empty (α) : Computation α :=
  ⟨Stream'.const none, fun _ _ => id⟩

instance : Inhabited (Computation α) :=
  ⟨empty _⟩

/-- `runFor c n` evaluates `c` for `n` steps and returns the result, or `none`
  if it did not terminate after `n` steps. -/
def runFor : Computation α → ℕ → Option α :=
  Subtype.val

/-- `destruct c` is the destructor for `Computation α` as a coinductive type.
  It returns `inl a` if `c = pure a` and `inr c'` if `c = think c'`. -/
def destruct (c : Computation α) : α ⊕ (Computation α) :=
  match c.1 0 with
  | none => Sum.inr (tail c)
  | some a => Sum.inl a

/-- `run c` is an unsound meta function that runs `c` to completion, possibly
  resulting in an infinite loop in the VM. -/
unsafe def run : Computation α → α
  | c =>
    match destruct c with
    | Sum.inl a => a
    | Sum.inr ca => run ca

theorem destruct_eq_pure {s : Computation α} {a : α} : destruct s = Sum.inl a → s = pure a := by
  dsimp [destruct]
  cases f0 : s.1 0 <;> intro h
  · contradiction
  · apply Subtype.eq
    funext n
    induction n with
    | zero => injection h with h'; rwa [h'] at f0
    | succ n IH => exact s.2 IH

theorem destruct_eq_think {s : Computation α} {s'} : destruct s = Sum.inr s' → s = think s' := by
  dsimp [destruct]
  rcases f0 : s.1 0 with - | a' <;> intro h
  · injection h with h'
    rw [← h']
    obtain ⟨f, al⟩ := s
    apply Subtype.eq
    dsimp [think, tail]
    rw [← f0]
    exact (Stream'.eta f).symm
  · contradiction

@[simp]
theorem destruct_pure (a : α) : destruct (pure a) = Sum.inl a :=
  rfl

@[simp]
theorem destruct_think : ∀ s : Computation α, destruct (think s) = Sum.inr s
  | ⟨_, _⟩ => rfl

@[simp]
theorem destruct_empty : destruct (empty α) = Sum.inr (empty α) :=
  rfl

@[simp]
theorem head_pure (a : α) : head (pure a) = some a :=
  rfl

@[simp]
theorem head_think (s : Computation α) : head (think s) = none :=
  rfl

@[simp]
theorem head_empty : head (empty α) = none :=
  rfl

@[simp]
theorem tail_pure (a : α) : tail (pure a) = pure a :=
  rfl

@[simp]
theorem tail_think (s : Computation α) : tail (think s) = s := rfl

@[simp]
theorem tail_empty : tail (empty α) = empty α :=
  rfl

theorem think_empty : empty α = think (empty α) :=
  destruct_eq_think destruct_empty

/-- Recursion principle for computations, compare with `List.recOn`. -/
@[elab_as_elim]
def recOn {motive : Computation α → Sort v} (s : Computation α) (pure : ∀ a, motive (pure a))
    (think : ∀ s, motive (think s)) : motive s :=
  match H : destruct s with
  | Sum.inl v => by
    rw [destruct_eq_pure H]
    apply pure
  | Sum.inr v => match v with
    | ⟨a, s'⟩ => by
      rw [destruct_eq_think H]
      apply think

/-- Corecursor constructor for `corec` -/
def Corec.f (f : β → α ⊕ β) : α ⊕ β → Option α × (α ⊕ β)
  | Sum.inl a => (some a, Sum.inl a)
  | Sum.inr b =>
    (match f b with
      | Sum.inl a => some a
      | Sum.inr _ => none,
      f b)

/-- `corec f b` is the corecursor for `Computation α` as a coinductive type.
  If `f b = inl a` then `corec f b = pure a`, and if `f b = inl b'` then
  `corec f b = think (corec f b')`. -/
def corec (f : β → α ⊕ β) (b : β) : Computation α := by
  refine ⟨Stream'.corec' (Corec.f f) (Sum.inr b), fun n a' h => ?_⟩
  rw [Stream'.corec'_eq]
  change Stream'.corec' (Corec.f f) (Corec.f f (Sum.inr b)).2 n = some a'
  revert h; generalize Sum.inr b = o
  induction n generalizing o with
  | zero =>
    change (Corec.f f o).1 = some a' → (Corec.f f (Corec.f f o).2).1 = some a'
    rcases o with _ | b <;> intro h
    · exact h
    unfold Corec.f at *; split <;> simp_all
  | succ n IH =>
    rw [Stream'.corec'_eq (Corec.f f) (Corec.f f o).2, Stream'.corec'_eq (Corec.f f) o]
    exact IH (Corec.f f o).2

/-- left map of `⊕` -/
def lmap (f : α → β) : α ⊕ γ → β ⊕ γ
  | Sum.inl a => Sum.inl (f a)
  | Sum.inr b => Sum.inr b

/-- right map of `⊕` -/
def rmap (f : β → γ) : α ⊕ β → α ⊕ γ
  | Sum.inl a => Sum.inl a
  | Sum.inr b => Sum.inr (f b)

attribute [simp] lmap rmap

@[simp]
theorem corec_eq (f : β → α ⊕ β) (b : β) : destruct (corec f b) = rmap (corec f) (f b) := by
  dsimp [corec, destruct]
  rw [show Stream'.corec' (Corec.f f) (Sum.inr b) 0 =
    Sum.rec Option.some (fun _ ↦ none) (f b) by
    dsimp [Corec.f, Stream'.corec', Stream'.corec, Stream'.map, Stream'.get, Stream'.iterate]
    match (f b) with
    | Sum.inl x => rfl
    | Sum.inr x => rfl
    ]
  rcases h : f b with a | b'; · rfl
  dsimp [Corec.f, destruct]
  apply congr_arg; apply Subtype.eq
  dsimp [corec, tail]
  rw [Stream'.corec'_eq, Stream'.tail_cons]
  dsimp [Corec.f]; rw [h]

section Bisim

variable (R : Computation α → Computation α → Prop)

/-- bisimilarity relation -/
local infixl:50 " ~ " => R

/-- Bisimilarity over a sum of `Computation`s -/
def BisimO : α ⊕ (Computation α) → α ⊕ (Computation α) → Prop
  | Sum.inl a, Sum.inl a' => a = a'
  | Sum.inr s, Sum.inr s' => R s s'
  | _, _ => False

attribute [simp] BisimO
attribute [nolint simpNF] BisimO.eq_3

/-- Attribute expressing bisimilarity over two `Computation`s -/
def IsBisimulation :=
  ∀ ⦃s₁ s₂⦄, s₁ ~ s₂ → BisimO R (destruct s₁) (destruct s₂)

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
      refine recOn s ?_ ?_ <;> intro r' <;> refine recOn s' ?_ ?_ <;> intro a' r h
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

end Bisim

-- It's more of a stretch to use ∈ for this relation, but it
-- asserts that the computation limits to the given value.
/-- Assertion that a `Computation` limits to a given value -/
protected def Mem (s : Computation α) (a : α) :=
  some a ∈ s.1

instance : Membership α (Computation α) :=
  ⟨Computation.Mem⟩

theorem le_stable (s : Computation α) {a m n} (h : m ≤ n) : s.1 m = some a → s.1 n = some a := by
  obtain ⟨f, al⟩ := s
  induction h with
  | refl => exact id
  | step _ IH => exact fun h2 ↦ al (IH h2)

theorem mem_unique {s : Computation α} {a b : α} : a ∈ s → b ∈ s → a = b
  | ⟨m, ha⟩, ⟨n, hb⟩ => by
    injection
      (le_stable s (le_max_left m n) ha.symm).symm.trans (le_stable s (le_max_right m n) hb.symm)

theorem Mem.left_unique : Relator.LeftUnique ((· ∈ ·) : α → Computation α → Prop) := fun _ _ _ =>
  mem_unique

/-- `Terminates s` asserts that the computation `s` eventually terminates with some value. -/
class Terminates (s : Computation α) : Prop where
  /-- assertion that there is some term `a` such that the `Computation` terminates -/
  term : ∃ a, a ∈ s

theorem terminates_iff (s : Computation α) : Terminates s ↔ ∃ a, a ∈ s :=
  ⟨fun h => h.1, Terminates.mk⟩

theorem terminates_of_mem {s : Computation α} {a : α} (h : a ∈ s) : Terminates s :=
  ⟨⟨a, h⟩⟩

theorem terminates_def (s : Computation α) : Terminates s ↔ ∃ n, (s.1 n).isSome :=
  ⟨fun ⟨⟨a, n, h⟩⟩ =>
    ⟨n, by
      dsimp [Stream'.get] at h
      rw [← h]
      exact rfl⟩,
    fun ⟨n, h⟩ => ⟨⟨Option.get _ h, n, (Option.eq_some_of_isSome h).symm⟩⟩⟩

theorem ret_mem (a : α) : a ∈ pure a :=
  Exists.intro 0 rfl

theorem eq_of_pure_mem {a a' : α} (h : a' ∈ pure a) : a' = a :=
  mem_unique h (ret_mem _)

@[simp]
theorem mem_pure_iff (a b : α) : a ∈ pure b ↔ a = b :=
  ⟨eq_of_pure_mem, fun h => h ▸ ret_mem _⟩

instance ret_terminates (a : α) : Terminates (pure a) :=
  terminates_of_mem (ret_mem _)

theorem think_mem {s : Computation α} {a} : a ∈ s → a ∈ think s
  | ⟨n, h⟩ => ⟨n + 1, h⟩

instance think_terminates (s : Computation α) : ∀ [Terminates s], Terminates (think s)
  | ⟨⟨a, n, h⟩⟩ => ⟨⟨a, n + 1, h⟩⟩

theorem of_think_mem {s : Computation α} {a} : a ∈ think s → a ∈ s
  | ⟨n, h⟩ => by
    rcases n with - | n'
    · contradiction
    · exact ⟨n', h⟩

theorem of_think_terminates {s : Computation α} : Terminates (think s) → Terminates s
  | ⟨⟨a, h⟩⟩ => ⟨⟨a, of_think_mem h⟩⟩

theorem notMem_empty (a : α) : a ∉ empty α := fun ⟨n, h⟩ => by contradiction

@[deprecated (since := "2025-05-23")] alias not_mem_empty := notMem_empty

theorem not_terminates_empty : ¬Terminates (empty α) := fun ⟨⟨a, h⟩⟩ => notMem_empty a h

theorem eq_empty_of_not_terminates {s} (H : ¬Terminates s) : s = empty α := by
  apply Subtype.eq; funext n
  rcases h : s.val n; · rfl
  refine absurd ?_ H; exact ⟨⟨_, _, h.symm⟩⟩

theorem thinkN_mem {s : Computation α} {a} : ∀ n, a ∈ thinkN s n ↔ a ∈ s
  | 0 => Iff.rfl
  | n + 1 => Iff.trans ⟨of_think_mem, think_mem⟩ (thinkN_mem n)

instance thinkN_terminates (s : Computation α) : ∀ [Terminates s] (n), Terminates (thinkN s n)
  | ⟨⟨a, h⟩⟩, n => ⟨⟨a, (thinkN_mem n).2 h⟩⟩

theorem of_thinkN_terminates (s : Computation α) (n) : Terminates (thinkN s n) → Terminates s
  | ⟨⟨a, h⟩⟩ => ⟨⟨a, (thinkN_mem _).1 h⟩⟩

/-- `Promises s a`, or `s ~> a`, asserts that although the computation `s`
  may not terminate, if it does, then the result is `a`. -/
def Promises (s : Computation α) (a : α) : Prop :=
  ∀ ⦃a'⦄, a' ∈ s → a = a'

/-- `Promises s a`, or `s ~> a`, asserts that although the computation `s`
  may not terminate, if it does, then the result is `a`. -/
scoped infixl:50 " ~> " => Promises

theorem mem_promises {s : Computation α} {a : α} : a ∈ s → s ~> a := fun h _ => mem_unique h

theorem empty_promises (a : α) : empty α ~> a := fun _ h => absurd h (notMem_empty _)

section get

variable (s : Computation α) [h : Terminates s]

/-- `length s` gets the number of steps of a terminating computation -/
def length : ℕ :=
  Nat.find ((terminates_def _).1 h)

/-- `get s` returns the result of a terminating computation -/
def get : α :=
  Option.get _ (Nat.find_spec <| (terminates_def _).1 h)

theorem get_mem : get s ∈ s :=
  Exists.intro (length s) (Option.eq_some_of_isSome _).symm

theorem get_eq_of_mem {a} : a ∈ s → get s = a :=
  mem_unique (get_mem _)

theorem mem_of_get_eq {a} : get s = a → a ∈ s := by intro h; rw [← h]; apply get_mem

@[simp]
theorem get_think : get (think s) = get s :=
  get_eq_of_mem _ <|
    let ⟨n, h⟩ := get_mem s
    ⟨n + 1, h⟩

@[simp]
theorem get_thinkN (n) : get (thinkN s n) = get s :=
  get_eq_of_mem _ <| (thinkN_mem _).2 (get_mem _)

theorem get_promises : s ~> get s := fun _ => get_eq_of_mem _

theorem mem_of_promises {a} (p : s ~> a) : a ∈ s := by
  obtain ⟨h⟩ := h
  obtain ⟨a', h⟩ := h
  rw [p h]
  exact h

theorem get_eq_of_promises {a} : s ~> a → get s = a :=
  get_eq_of_mem _ ∘ mem_of_promises _

end get

/-- `Results s a n` completely characterizes a terminating computation:
  it asserts that `s` terminates after exactly `n` steps, with result `a`. -/
def Results (s : Computation α) (a : α) (n : ℕ) :=
  ∃ h : a ∈ s, @length _ s (terminates_of_mem h) = n

theorem results_of_terminates (s : Computation α) [_T : Terminates s] :
    Results s (get s) (length s) :=
  ⟨get_mem _, rfl⟩

theorem results_of_terminates' (s : Computation α) [T : Terminates s] {a} (h : a ∈ s) :
    Results s a (length s) := by rw [← get_eq_of_mem _ h]; apply results_of_terminates

theorem Results.mem {s : Computation α} {a n} : Results s a n → a ∈ s
  | ⟨m, _⟩ => m

theorem Results.terminates {s : Computation α} {a n} (h : Results s a n) : Terminates s :=
  terminates_of_mem h.mem

theorem Results.length {s : Computation α} {a n} [_T : Terminates s] : Results s a n → length s = n
  | ⟨_, h⟩ => h

theorem Results.val_unique {s : Computation α} {a b m n} (h1 : Results s a m) (h2 : Results s b n) :
    a = b :=
  mem_unique h1.mem h2.mem

theorem Results.len_unique {s : Computation α} {a b m n} (h1 : Results s a m) (h2 : Results s b n) :
    m = n := by haveI := h1.terminates; haveI := h2.terminates; rw [← h1.length, h2.length]

theorem exists_results_of_mem {s : Computation α} {a} (h : a ∈ s) : ∃ n, Results s a n :=
  haveI := terminates_of_mem h
  ⟨_, results_of_terminates' s h⟩

@[simp]
theorem get_pure (a : α) : get (pure a) = a :=
  get_eq_of_mem _ ⟨0, rfl⟩

@[simp]
theorem length_pure (a : α) : length (pure a) = 0 :=
  let h := Computation.ret_terminates a
  Nat.eq_zero_of_le_zero <| Nat.find_min' ((terminates_def (pure a)).1 h) rfl

theorem results_pure (a : α) : Results (pure a) a 0 :=
  ⟨ret_mem a, length_pure _⟩

@[simp]
theorem length_think (s : Computation α) [h : Terminates s] : length (think s) = length s + 1 := by
  apply le_antisymm
  · exact Nat.find_min' _ (Nat.find_spec ((terminates_def _).1 h))
  · have : (Option.isSome ((think s).val (length (think s))) : Prop) :=
      Nat.find_spec ((terminates_def _).1 s.think_terminates)
    revert this; rcases length (think s) with - | n <;> intro this
    · simp [think, Stream'.cons] at this
    · apply Nat.succ_le_succ
      apply Nat.find_min'
      apply this

theorem results_think {s : Computation α} {a n} (h : Results s a n) : Results (think s) a (n + 1) :=
  haveI := h.terminates
  ⟨think_mem h.mem, by rw [length_think, h.length]⟩

theorem of_results_think {s : Computation α} {a n} (h : Results (think s) a n) :
    ∃ m, Results s a m ∧ n = m + 1 := by
  haveI := of_think_terminates h.terminates
  have := results_of_terminates' _ (of_think_mem h.mem)
  exact ⟨_, this, Results.len_unique h (results_think this)⟩

@[simp]
theorem results_think_iff {s : Computation α} {a n} : Results (think s) a (n + 1) ↔ Results s a n :=
  ⟨fun h => by
    let ⟨n', r, e⟩ := of_results_think h
    injection e with h'; rwa [h'], results_think⟩

theorem results_thinkN {s : Computation α} {a m} :
    ∀ n, Results s a m → Results (thinkN s n) a (m + n)
  | 0, h => h
  | n + 1, h => results_think (results_thinkN n h)

theorem results_thinkN_pure (a : α) (n) : Results (thinkN (pure a) n) a n := by
  have := results_thinkN n (results_pure a); rwa [Nat.zero_add] at this

@[simp]
theorem length_thinkN (s : Computation α) [_h : Terminates s] (n) :
    length (thinkN s n) = length s + n :=
  (results_thinkN n (results_of_terminates _)).length

theorem eq_thinkN {s : Computation α} {a n} (h : Results s a n) : s = thinkN (pure a) n := by
  induction n generalizing s with | zero | succ n IH <;>
  induction s using recOn with | pure a' | think s
  · rw [← eq_of_pure_mem h.mem]
    rfl
  · obtain ⟨n, h⟩ := of_results_think h
    cases h
    contradiction
  · have := h.len_unique (results_pure _)
    contradiction
  · rw [IH (results_think_iff.1 h)]
    rfl

theorem eq_thinkN' (s : Computation α) [_h : Terminates s] :
    s = thinkN (pure (get s)) (length s) :=
  eq_thinkN (results_of_terminates _)

/-- Recursor based on membership -/
def memRecOn {C : Computation α → Sort v} {a s} (M : a ∈ s) (h1 : C (pure a))
    (h2 : ∀ s, C s → C (think s)) : C s := by
  haveI T := terminates_of_mem M
  rw [eq_thinkN' s, get_eq_of_mem s M]
  generalize length s = n
  induction n with | zero => exact h1 | succ n IH => exact h2 _ IH

/-- Recursor based on assertion of `Terminates` -/
def terminatesRecOn
    {C : Computation α → Sort v}
    (s) [Terminates s]
    (h1 : ∀ a, C (pure a))
    (h2 : ∀ s, C s → C (think s)) : C s :=
  memRecOn (get_mem s) (h1 _) h2

/-- Map a function on the result of a computation. -/
def map (f : α → β) : Computation α → Computation β
  | ⟨s, al⟩ =>
    ⟨s.map fun o => Option.casesOn o none (some ∘ f), fun n b => by
      dsimp [Stream'.map, Stream'.get]
      rcases e : s n with - | a <;> intro h
      · contradiction
      · rw [al e]; exact h⟩

/-- bind over a `Sum` of `Computation` -/
def Bind.g : β ⊕ Computation β → β ⊕ (Computation α ⊕ Computation β)
  | Sum.inl b => Sum.inl b
  | Sum.inr cb' => Sum.inr <| Sum.inr cb'

/-- bind over a function mapping `α` to a `Computation` -/
def Bind.f (f : α → Computation β) :
    Computation α ⊕ Computation β → β ⊕ (Computation α ⊕ Computation β)
  | Sum.inl ca =>
    match destruct ca with
    | Sum.inl a => Bind.g <| destruct (f a)
    | Sum.inr ca' => Sum.inr <| Sum.inl ca'
  | Sum.inr cb => Bind.g <| destruct cb

/-- Compose two computations into a monadic `bind` operation. -/
def bind (c : Computation α) (f : α → Computation β) : Computation β :=
  corec (Bind.f f) (Sum.inl c)

instance : Bind Computation :=
  ⟨@bind⟩

theorem has_bind_eq_bind {β} (c : Computation α) (f : α → Computation β) : c >>= f = bind c f :=
  rfl

/-- Flatten a computation of computations into a single computation. -/
def join (c : Computation (Computation α)) : Computation α :=
  c >>= id

@[simp]
theorem map_pure (f : α → β) (a) : map f (pure a) = pure (f a) :=
  rfl

@[simp]
theorem map_think (f : α → β) : ∀ s, map f (think s) = think (map f s)
  | ⟨s, al⟩ => by apply Subtype.eq; dsimp [think, map]; rw [Stream'.map_cons]

@[simp]
theorem destruct_map (f : α → β) (s) : destruct (map f s) = lmap f (rmap (map f) (destruct s)) := by
  induction s using recOn <;> simp

@[simp]
theorem map_id : ∀ s : Computation α, map id s = s
  | ⟨f, al⟩ => by
    apply Subtype.eq; simp only [map, comp_apply, id_eq]
    have e : @Option.rec α (fun _ => Option α) none some = id := by ext ⟨⟩ <;> rfl
    have h : ((fun x : Option α => x) = id) := rfl
    simp [e, h, Stream'.map_id]

theorem map_comp (f : α → β) (g : β → γ) : ∀ s : Computation α, map (g ∘ f) s = map g (map f s)
  | ⟨s, al⟩ => by
    apply Subtype.eq; dsimp [map]
    apply congr_arg fun f : _ → Option γ => Stream'.map f s
    ext ⟨⟩ <;> rfl

@[simp]
theorem ret_bind (a) (f : α → Computation β) : bind (pure a) f = f a := by
  apply
    eq_of_bisim fun c₁ c₂ => c₁ = bind (pure a) f ∧ c₂ = f a ∨ c₁ = corec (Bind.f f) (Sum.inr c₂)
  · intro c₁ c₂ h
    match c₁, c₂, h with
    | _, _, Or.inl ⟨rfl, rfl⟩ =>
      simp only [BisimO, bind, Bind.f, corec_eq, rmap, destruct_pure]
      rcases destruct (f a) with b | cb <;> simp [Bind.g]
    | _, c, Or.inr rfl =>
      simp only [BisimO, Bind.f, corec_eq, rmap]
      rcases destruct c with b | cb <;> simp [Bind.g]
  · simp

@[simp]
theorem think_bind (c) (f : α → Computation β) : bind (think c) f = think (bind c f) :=
  destruct_eq_think <| by simp [bind, Bind.f]

@[simp]
theorem bind_pure (f : α → β) (s) : bind s (pure ∘ f) = map f s := by
  apply eq_of_bisim fun c₁ c₂ => c₁ = c₂ ∨ ∃ s, c₁ = bind s (pure ∘ f) ∧ c₂ = map f s
  · intro c₁ c₂ h
    match c₁, c₂, h with
    | _, c₂, Or.inl (Eq.refl _) => rcases destruct c₂ with b | cb <;> simp
    | _, _, Or.inr ⟨s, rfl, rfl⟩ =>
      induction s using recOn with
      | pure s => simp
      | think s => simpa using Or.inr ⟨s, rfl, rfl⟩
  · exact Or.inr ⟨s, rfl, rfl⟩

@[simp]
theorem bind_pure' (s : Computation α) : bind s pure = s := by
  simpa using bind_pure id s

@[simp]
theorem bind_assoc (s : Computation α) (f : α → Computation β) (g : β → Computation γ) :
    bind (bind s f) g = bind s fun x : α => bind (f x) g := by
  apply
    eq_of_bisim fun c₁ c₂ =>
      c₁ = c₂ ∨ ∃ s, c₁ = bind (bind s f) g ∧ c₂ = bind s fun x : α => bind (f x) g
  · intro c₁ c₂ h
    match c₁, c₂, h with
    | _, c₂, Or.inl (Eq.refl _) => rcases destruct c₂ with b | cb <;> simp
    | _, _, Or.inr ⟨s, rfl, rfl⟩ =>
      induction s using recOn with
      | pure s =>
        simp only [BisimO, ret_bind]; generalize f s = fs
        induction fs using recOn with
        | pure t => rw [ret_bind]; rcases destruct (g t) with b | cb <;> simp
        | think => simp
      | think s => simpa [BisimO] using Or.inr ⟨s, rfl, rfl⟩
  · exact Or.inr ⟨s, rfl, rfl⟩

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
    obtain ⟨m', h⟩ := of_results_think h1
    obtain ⟨h1, e⟩ := h
    rw [e]
    exact results_think (h3 h1)

theorem mem_bind {s : Computation α} {f : α → Computation β} {a b} (h1 : a ∈ s) (h2 : b ∈ f a) :
    b ∈ bind s f :=
  let ⟨_, h1⟩ := exists_results_of_mem h1
  let ⟨_, h2⟩ := exists_results_of_mem h2
  (results_bind h1 h2).mem

instance terminates_bind (s : Computation α) (f : α → Computation β) [Terminates s]
    [Terminates (f (get s))] : Terminates (bind s f) :=
  terminates_of_mem (mem_bind (get_mem s) (get_mem (f (get s))))

@[simp]
theorem get_bind (s : Computation α) (f : α → Computation β) [Terminates s]
    [Terminates (f (get s))] : get (bind s f) = get (f (get s)) :=
  get_eq_of_mem _ (mem_bind (get_mem s) (get_mem (f (get s))))

@[simp]
theorem length_bind (s : Computation α) (f : α → Computation β) [_T1 : Terminates s]
    [_T2 : Terminates (f (get s))] : length (bind s f) = length (f (get s)) + length s :=
  (results_of_terminates _).len_unique <|
    results_bind (results_of_terminates _) (results_of_terminates _)

theorem of_results_bind {s : Computation α} {f : α → Computation β} {b k} :
    Results (bind s f) b k → ∃ a m n, Results s a m ∧ Results (f a) b n ∧ k = n + m := by
  induction k generalizing s with | zero | succ n IH <;>
  induction s using recOn with intro h | pure a | think s'
  · simp only [ret_bind] at h
    exact ⟨_, _, _, results_pure _, h, rfl⟩
  · have := congr_arg head (eq_thinkN h)
    contradiction
  · simp only [ret_bind] at h
    exact ⟨_, _, n + 1, results_pure _, h, rfl⟩
  · simp only [think_bind, results_think_iff] at h
    let ⟨a, m, n', h1, h2, e'⟩ := IH h
    rw [e']
    exact ⟨a, m.succ, n', results_think h1, h2, rfl⟩

theorem exists_of_mem_bind {s : Computation α} {f : α → Computation β} {b} (h : b ∈ bind s f) :
    ∃ a ∈ s, b ∈ f a :=
  let ⟨_, h⟩ := exists_results_of_mem h
  let ⟨a, _, _, h1, h2, _⟩ := of_results_bind h
  ⟨a, h1.mem, h2.mem⟩

theorem bind_promises {s : Computation α} {f : α → Computation β} {a b} (h1 : s ~> a)
    (h2 : f a ~> b) : bind s f ~> b := fun b' bB => by
  rcases exists_of_mem_bind bB with ⟨a', a's, ba'⟩
  rw [← h1 a's] at ba'; exact h2 ba'

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

@[simp]
theorem pure_def (a) : (return a : Computation α) = pure a :=
  rfl

@[simp]
theorem map_pure' {α β} : ∀ (f : α → β) (a), f <$> pure a = pure (f a) :=
  map_pure

@[simp]
theorem map_think' {α β} : ∀ (f : α → β) (s), f <$> think s = think (f <$> s) :=
  map_think

theorem mem_map (f : α → β) {a} {s : Computation α} (m : a ∈ s) : f a ∈ map f s := by
  rw [← bind_pure]; apply mem_bind m; apply ret_mem

theorem exists_of_mem_map {f : α → β} {b : β} {s : Computation α} (h : b ∈ map f s) :
    ∃ a, a ∈ s ∧ f a = b := by
  rw [← bind_pure] at h
  let ⟨a, as, fb⟩ := exists_of_mem_bind h
  exact ⟨a, as, mem_unique (ret_mem _) fb⟩

instance terminates_map (f : α → β) (s : Computation α) [Terminates s] : Terminates (map f s) := by
  rw [← bind_pure]; exact terminates_of_mem (mem_bind (get_mem s) (get_mem (α := β) (f (get s))))

theorem terminates_map_iff (f : α → β) (s : Computation α) : Terminates (map f s) ↔ Terminates s :=
  ⟨fun ⟨⟨_, h⟩⟩ =>
    let ⟨_, h1, _⟩ := exists_of_mem_map h
    ⟨⟨_, h1⟩⟩,
    @Computation.terminates_map _ _ _ _⟩

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

instance instAlternativeComputation : Alternative Computation :=
  { Computation.monad with
    orElse := @orElse
    failure := @empty }

@[simp]
theorem ret_orElse (a : α) (c₂ : Computation α) : (pure a <|> c₂) = pure a :=
  destruct_eq_pure <| by
    unfold_projs
    simp [orElse]

@[simp]
theorem orElse_pure (c₁ : Computation α) (a : α) : (think c₁ <|> pure a) = pure a :=
  destruct_eq_pure <| by
    unfold_projs
    simp [orElse]

@[simp]
theorem orElse_think (c₁ c₂ : Computation α) : (think c₁ <|> think c₂) = think (c₁ <|> c₂) :=
  destruct_eq_think <| by
    unfold_projs
    simp [orElse]

@[simp]
theorem empty_orElse (c) : (empty α <|> c) = c := by
  apply eq_of_bisim (fun c₁ c₂ => (empty α <|> c₂) = c₁) _ rfl
  intro s' s h; rw [← h]
  induction s using recOn with rw [think_empty]
  | pure s => simp
  | think s => simp only [BisimO, orElse_think, destruct_think]; rw [← think_empty]

@[simp]
theorem orElse_empty (c : Computation α) : (c <|> empty α) = c := by
  apply eq_of_bisim (fun c₁ c₂ => (c₂ <|> empty α) = c₁) _ rfl
  intro s' s h; rw [← h]
  induction s using recOn with rw [think_empty]
  | pure s => simp
  | think s => simp only [BisimO, orElse_think, destruct_think]; rw [← think_empty]

/-- `c₁ ~ c₂` asserts that `c₁` and `c₂` either both terminate with the same result,
  or both loop forever. -/
def Equiv (c₁ c₂ : Computation α) : Prop :=
  ∀ a, a ∈ c₁ ↔ a ∈ c₂

/-- equivalence relation for computations -/
scoped infixl:50 " ~ " => Equiv

@[refl]
theorem Equiv.refl (s : Computation α) : s ~ s := fun _ => Iff.rfl

@[symm]
theorem Equiv.symm {s t : Computation α} : s ~ t → t ~ s := fun h a => (h a).symm

@[trans]
theorem Equiv.trans {s t u : Computation α} : s ~ t → t ~ u → s ~ u := fun h1 h2 a =>
  (h1 a).trans (h2 a)

theorem Equiv.equivalence : Equivalence (@Equiv α) :=
  ⟨@Equiv.refl _, @Equiv.symm _, @Equiv.trans _⟩

theorem equiv_of_mem {s t : Computation α} {a} (h1 : a ∈ s) (h2 : a ∈ t) : s ~ t := fun a' =>
  ⟨fun ma => by rw [mem_unique ma h1]; exact h2, fun ma => by rw [mem_unique ma h2]; exact h1⟩

theorem terminates_congr {c₁ c₂ : Computation α} (h : c₁ ~ c₂) : Terminates c₁ ↔ Terminates c₂ := by
  simp only [terminates_iff, exists_congr h]

theorem promises_congr {c₁ c₂ : Computation α} (h : c₁ ~ c₂) (a) : c₁ ~> a ↔ c₂ ~> a :=
  forall_congr' fun a' => imp_congr (h a') Iff.rfl

theorem get_equiv {c₁ c₂ : Computation α} (h : c₁ ~ c₂) [Terminates c₁] [Terminates c₂] :
    get c₁ = get c₂ :=
  get_eq_of_mem _ <| (h _).2 <| get_mem _

theorem think_equiv (s : Computation α) : think s ~ s := fun _ => ⟨of_think_mem, think_mem⟩

theorem thinkN_equiv (s : Computation α) (n) : thinkN s n ~ s := fun _ => thinkN_mem n

theorem bind_congr {s1 s2 : Computation α} {f1 f2 : α → Computation β} (h1 : s1 ~ s2)
    (h2 : ∀ a, f1 a ~ f2 a) : bind s1 f1 ~ bind s2 f2 := fun b =>
  ⟨fun h =>
    let ⟨a, ha, hb⟩ := exists_of_mem_bind h
    mem_bind ((h1 a).1 ha) ((h2 a b).1 hb),
    fun h =>
    let ⟨a, ha, hb⟩ := exists_of_mem_bind h
    mem_bind ((h1 a).2 ha) ((h2 a b).2 hb)⟩

theorem equiv_pure_of_mem {s : Computation α} {a} (h : a ∈ s) : s ~ pure a :=
  equiv_of_mem h (ret_mem _)

/-- `LiftRel R ca cb` is a generalization of `Equiv` to relations other than
  equality. It asserts that if `ca` terminates with `a`, then `cb` terminates with
  some `b` such that `R a b`, and if `cb` terminates with `b` then `ca` terminates
  with some `a` such that `R a b`. -/
def LiftRel (R : α → β → Prop) (ca : Computation α) (cb : Computation β) : Prop :=
  (∀ {a}, a ∈ ca → ∃ b, b ∈ cb ∧ R a b) ∧ ∀ {b}, b ∈ cb → ∃ a, a ∈ ca ∧ R a b

theorem LiftRel.swap (R : α → β → Prop) (ca : Computation α) (cb : Computation β) :
    LiftRel (swap R) cb ca ↔ LiftRel R ca cb :=
  @and_comm _ _

theorem lift_eq_iff_equiv (c₁ c₂ : Computation α) : LiftRel (· = ·) c₁ c₂ ↔ c₁ ~ c₂ :=
  ⟨fun ⟨h1, h2⟩ a =>
    ⟨fun a1 => by let ⟨b, b2, ab⟩ := h1 a1; rwa [ab],
     fun a2 => by let ⟨b, b1, ab⟩ := h2 a2; rwa [← ab]⟩,
    fun e => ⟨fun {a} a1 => ⟨a, (e _).1 a1, rfl⟩, fun {a} a2 => ⟨a, (e _).2 a2, rfl⟩⟩⟩

theorem LiftRel.refl (R : α → α → Prop) (H : Reflexive R) : Reflexive (LiftRel R) := fun _ =>
  ⟨fun {a} as => ⟨a, as, H a⟩, fun {b} bs => ⟨b, bs, H b⟩⟩

theorem LiftRel.symm (R : α → α → Prop) (H : Symmetric R) : Symmetric (LiftRel R) :=
  fun _ _ ⟨l, r⟩ =>
  ⟨fun {_} a2 =>
    let ⟨b, b1, ab⟩ := r a2
    ⟨b, b1, H ab⟩,
    fun {_} a1 =>
    let ⟨b, b2, ab⟩ := l a1
    ⟨b, b2, H ab⟩⟩

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

theorem LiftRel.equiv (R : α → α → Prop) : Equivalence R → Equivalence (LiftRel R)
  | ⟨refl, symm, trans⟩ => ⟨LiftRel.refl R refl, @LiftRel.symm _ R @symm, @LiftRel.trans _ R @trans⟩

theorem LiftRel.imp {R S : α → β → Prop} (H : ∀ {a b}, R a b → S a b) (s t) :
    LiftRel R s t → LiftRel S s t
  | ⟨l, r⟩ =>
    ⟨fun {_} as =>
      let ⟨b, bt, ab⟩ := l as
      ⟨b, bt, H ab⟩,
      fun {_} bt =>
      let ⟨a, as, ab⟩ := r bt
      ⟨a, as, H ab⟩⟩

theorem terminates_of_liftRel {R : α → β → Prop} {s t} :
    LiftRel R s t → (Terminates s ↔ Terminates t)
  | ⟨l, r⟩ =>
    ⟨fun ⟨⟨_, as⟩⟩ =>
      let ⟨b, bt, _⟩ := l as
      ⟨⟨b, bt⟩⟩,
      fun ⟨⟨_, bt⟩⟩ =>
      let ⟨a, as, _⟩ := r bt
      ⟨⟨a, as⟩⟩⟩

theorem rel_of_liftRel {R : α → β → Prop} {ca cb} :
    LiftRel R ca cb → ∀ {a b}, a ∈ ca → b ∈ cb → R a b
  | ⟨l, _⟩, a, b, ma, mb => by
    let ⟨b', mb', ab'⟩ := l ma
    rw [mem_unique mb mb']; exact ab'

theorem liftRel_of_mem {R : α → β → Prop} {a b ca cb} (ma : a ∈ ca) (mb : b ∈ cb) (ab : R a b) :
    LiftRel R ca cb :=
  ⟨fun {a'} ma' => by rw [mem_unique ma' ma]; exact ⟨b, mb, ab⟩, fun {b'} mb' => by
    rw [mem_unique mb' mb]; exact ⟨a, ma, ab⟩⟩

theorem exists_of_liftRel_left {R : α → β → Prop} {ca cb} (H : LiftRel R ca cb) {a} (h : a ∈ ca) :
    ∃ b, b ∈ cb ∧ R a b :=
  H.left h

theorem exists_of_liftRel_right {R : α → β → Prop} {ca cb} (H : LiftRel R ca cb) {b} (h : b ∈ cb) :
    ∃ a, a ∈ ca ∧ R a b :=
  H.right h

theorem liftRel_def {R : α → β → Prop} {ca cb} :
    LiftRel R ca cb ↔ (Terminates ca ↔ Terminates cb) ∧ ∀ {a b}, a ∈ ca → b ∈ cb → R a b :=
  ⟨fun h =>
    ⟨terminates_of_liftRel h, fun {a b} ma mb => by
      let ⟨b', mb', ab⟩ := h.left ma
      rwa [mem_unique mb mb']⟩,
    fun ⟨l, r⟩ =>
    ⟨fun {_} ma =>
      let ⟨⟨b, mb⟩⟩ := l.1 ⟨⟨_, ma⟩⟩
      ⟨b, mb, r ma mb⟩,
      fun {_} mb =>
      let ⟨⟨a, ma⟩⟩ := l.2 ⟨⟨_, mb⟩⟩
      ⟨a, ma, r ma mb⟩⟩⟩

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

@[simp]
theorem liftRel_pure_left (R : α → β → Prop) (a : α) (cb : Computation β) :
    LiftRel R (pure a) cb ↔ ∃ b, b ∈ cb ∧ R a b :=
  ⟨fun ⟨l, _⟩ => l (ret_mem _), fun ⟨b, mb, ab⟩ =>
    ⟨fun {a'} ma' => by rw [eq_of_pure_mem ma']; exact ⟨b, mb, ab⟩, fun {b'} mb' =>
      ⟨_, ret_mem _, by rw [mem_unique mb' mb]; exact ab⟩⟩⟩

@[simp]
theorem liftRel_pure_right (R : α → β → Prop) (ca : Computation α) (b : β) :
    LiftRel R ca (pure b) ↔ ∃ a, a ∈ ca ∧ R a b := by rw [LiftRel.swap, liftRel_pure_left]

theorem liftRel_pure (R : α → β → Prop) (a : α) (b : β) :
    LiftRel R (pure a) (pure b) ↔ R a b := by
  simp

@[simp]
theorem liftRel_think_left (R : α → β → Prop) (ca : Computation α) (cb : Computation β) :
    LiftRel R (think ca) cb ↔ LiftRel R ca cb :=
  and_congr (forall_congr' fun _ => imp_congr ⟨of_think_mem, think_mem⟩ Iff.rfl)
    (forall_congr' fun _ =>
      imp_congr Iff.rfl <| exists_congr fun _ => and_congr ⟨of_think_mem, think_mem⟩ Iff.rfl)

@[simp]
theorem liftRel_think_right (R : α → β → Prop) (ca : Computation α) (cb : Computation β) :
    LiftRel R ca (think cb) ↔ LiftRel R ca cb := by
  rw [← LiftRel.swap R, ← LiftRel.swap R]; apply liftRel_think_left

theorem liftRel_mem_cases {R : α → β → Prop} {ca cb} (Ha : ∀ a ∈ ca, LiftRel R ca cb)
    (Hb : ∀ b ∈ cb, LiftRel R ca cb) : LiftRel R ca cb :=
  ⟨fun {_} ma => (Ha _ ma).left ma, fun {_} mb => (Hb _ mb).right mb⟩

theorem liftRel_congr {R : α → β → Prop} {ca ca' : Computation α} {cb cb' : Computation β}
    (ha : ca ~ ca') (hb : cb ~ cb') : LiftRel R ca cb ↔ LiftRel R ca' cb' :=
  and_congr
    (forall_congr' fun _ => imp_congr (ha _) <| exists_congr fun _ => and_congr (hb _) Iff.rfl)
    (forall_congr' fun _ => imp_congr (hb _) <| exists_congr fun _ => and_congr (ha _) Iff.rfl)

theorem liftRel_map {δ} (R : α → β → Prop) (S : γ → δ → Prop) {s1 : Computation α}
    {s2 : Computation β} {f1 : α → γ} {f2 : β → δ} (h1 : LiftRel R s1 s2)
    (h2 : ∀ {a b}, R a b → S (f1 a) (f2 b)) : LiftRel S (map f1 s1) (map f2 s2) := by
  rw [← bind_pure, ← bind_pure]; apply liftRel_bind _ _ h1; simpa

theorem map_congr {s1 s2 : Computation α} {f : α → β}
    (h1 : s1 ~ s2) : map f s1 ~ map f s2 := by
  rw [← lift_eq_iff_equiv]
  exact liftRel_map Eq _ ((lift_eq_iff_equiv _ _).2 h1) fun {a} b => congr_arg _

/-- Alternate definition of `LiftRel` over relations between `Computation`s -/
def LiftRelAux (R : α → β → Prop) (C : Computation α → Computation β → Prop) :
    α ⊕ (Computation α) → β ⊕ (Computation β) → Prop
  | Sum.inl a, Sum.inl b => R a b
  | Sum.inl a, Sum.inr cb => ∃ b, b ∈ cb ∧ R a b
  | Sum.inr ca, Sum.inl b => ∃ a, a ∈ ca ∧ R a b
  | Sum.inr ca, Sum.inr cb => C ca cb

variable {R : α → β → Prop} {C : Computation α → Computation β → Prop}

@[simp] lemma liftRelAux_inl_inl {a : α} {b : β} : LiftRelAux R C (Sum.inl a) (Sum.inl b) = R a b :=
  rfl
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
  induction cb using recOn with
  | pure b =>
    exact
      ⟨fun h => ⟨_, ret_mem _, h⟩, fun ⟨b', mb, h⟩ => by rw [mem_unique (ret_mem _) mb]; exact h⟩
  | think cb =>
    rw [destruct_think]
    exact ⟨fun ⟨b, h, r⟩ => ⟨b, think_mem h, r⟩, fun ⟨b, h, r⟩ => ⟨b, of_think_mem h, r⟩⟩

theorem LiftRelAux.swap (R : α → β → Prop) (C) (a b) :
    LiftRelAux (swap R) (swap C) b a = LiftRelAux R C a b := by
  rcases a with a | ca <;> rcases b with b | cb <;> simp only [LiftRelAux]

@[simp]
theorem LiftRelAux.ret_right (R : α → β → Prop) (C : Computation α → Computation β → Prop) (b ca) :
    LiftRelAux R C (destruct ca) (Sum.inl b) ↔ ∃ a, a ∈ ca ∧ R a b := by
  rw [← LiftRelAux.swap, LiftRelAux.ret_left]

theorem LiftRelRec.lem {R : α → β → Prop} (C : Computation α → Computation β → Prop)
    (H : ∀ {ca cb}, C ca cb → LiftRelAux R C (destruct ca) (destruct cb)) (ca cb) (Hc : C ca cb) (a)
    (ha : a ∈ ca) : LiftRel R ca cb := by
  revert cb
  refine memRecOn (C := (fun ca ↦ ∀ (cb : Computation β), C ca cb → LiftRel R ca cb))
    ha ?_ (fun ca' IH => ?_) <;> intro cb Hc <;> have h := H Hc
  · simp only [destruct_pure, LiftRelAux.ret_left] at h
    simp [h]
  · simp only [liftRel_think_left]
    induction cb using recOn with
    | pure b => simpa using h
    | think cb => simpa [h] using IH _ h

theorem liftRel_rec {R : α → β → Prop} (C : Computation α → Computation β → Prop)
    (H : ∀ {ca cb}, C ca cb → LiftRelAux R C (destruct ca) (destruct cb)) (ca cb) (Hc : C ca cb) :
    LiftRel R ca cb :=
  liftRel_mem_cases (LiftRelRec.lem C (@H) ca cb Hc) fun b hb =>
    (LiftRel.swap _ _ _).2 <|
      LiftRelRec.lem (swap C) (fun {_ _} h => cast (LiftRelAux.swap _ _ _ _).symm <| H h) cb ca Hc b
        hb

end Computation
