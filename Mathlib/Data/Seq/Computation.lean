/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Coinductive formalization of unbounded computations.
-/
import Mathlib.Data.Nat.Order.Lemmas
import Mathlib.Tactic.DefEqTransformations

#align_import data.seq.computation from "leanprover-community/mathlib"@"1f0096e6caa61e9c849ec2adbd227e960e9dff58"

/-!
# Coinductive formalization of unbounded computations.

This file provides a `Computation` type where `Computation α` is the type of
unbounded computations returning `α`.
-/

open Function

universe u v w

/-- This type is used to represent unbounded computations in the runtime. -/
unsafe inductive ComputationImpl (α : Type u)
  /-- `pure a` is the computation that immediately terminates with result `a`. -/
  | pure (a : α) : ComputationImpl α
  /-- `think t` is the computation that delays for one "tick" and then evaluate the thunk of
  computation `t`. -/
  | think (t : Thunk (ComputationImpl α)) : ComputationImpl α

namespace ComputationImpl

variable {α : Type u} {β : Type v} {γ : Type w}

/-- `dest c` is the destructor for `ComputationImpl α` as a coinductive type.
  It returns `inl a` if `c = pure a` and `inr c'.get` if `c = think c'`. -/
@[inline]
unsafe def dest : (c : ComputationImpl α) → α ⊕ ComputationImpl α
  | pure a => Sum.inl a
  | think t => Sum.inr (Thunk.get t)

/-- Corecursor for the computation. -/
@[specialize]
unsafe def corec (f : β → α ⊕ β) (b : β) : ComputationImpl α :=
  match f b with
  | Sum.inl a => pure a
  | Sum.inr b => think ⟨fun _ => corec f b⟩

/-- Corecursor where it is possible to return a fully formed value at any point of the
computation. -/
@[specialize]
unsafe def corec' (f : β → ComputationImpl α ⊕ α ⊕ β) (b : β) : ComputationImpl α :=
  match f b with
  | Sum.inl c => c
  | Sum.inr (Sum.inl a) => pure a
  | Sum.inr (Sum.inr b) => think ⟨fun _ => corec' f b⟩

end ComputationImpl

open ComputationImpl

/-- `Computation α` is the type of unbounded computations returning `α`.
  This type has special support in the runtime. -/
@[opaque_repr]
structure Computation (α : Type u) where
  /-- Convert a `ℕ → Option α` into a `Computation α`. Consider using other functions like `corec`
  before use this. -/
  mk ::
  /-- `runFor c n` evaluates `c` for `n` steps and returns the result, or `none`
  if it did not terminate after `n` steps. -/
  runFor : ℕ → Option α
  /-- If `runFor s n = some a` for some `n` then it is constantly `some a` after that. -/
  succ_stable : ∀ ⦃n a⦄, runFor n = some a → runFor (n + 1) = some a
#align computation Computation
#align computation.run_for Computation.runFor

namespace Computation

variable {α : Type u} {β : Type v} {γ : Type w}

@[ext]
protected theorem ext {c₁ c₂ : Computation α} (h : ∀ n, runFor c₁ n = runFor c₂ n) : c₁ = c₂ := by
  cases c₁; cases c₂
  congr; funext n; apply h

-- constructors

/-- `pure a` is the computation that immediately terminates with result `a`. -/
@[inline]
unsafe def pureUnsafe (a : α) : Computation α :=
  unsafeCast (ComputationImpl.pure a)

-- Porting note: `return` is reserved, so changed to `pure`
@[inherit_doc pureUnsafe, implemented_by pureUnsafe]
def pure (a : α) : Computation α where
  runFor _ := some a
  succ_stable _ _ h := h
#align computation.return Computation.pure

@[simp]
theorem runFor_pure (a : α) (n : ℕ) : runFor (pure a) n = some a :=
  rfl

instance : CoeTC α (Computation α) :=
  ⟨pure⟩

-- note [use has_coe_t]

/-- `think c` is the computation that delays for one "tick" and then performs
  computation `c`. -/
@[inline]
unsafe def thinkUnsafe (c : Computation α) : Computation α :=
  unsafeCast (think (Thunk.pure (unsafeCast c : ComputationImpl α)))

@[inherit_doc thinkUnsafe, implemented_by thinkUnsafe]
def think (c : Computation α) : Computation α where
  runFor
  | 0     => none
  | n + 1 => runFor c n
  succ_stable
  | _ + 1, _, h => succ_stable c h
#align computation.think Computation.think

/-- `thinkN c n` is the computation that delays for `n` ticks and then performs
  computation `c`. -/
@[simp]
def thinkN (c : Computation α) : ℕ → Computation α
  | 0     => c
  | n + 1 => think (thinkN c n)
set_option linter.uppercaseLean3 false in
#align computation.thinkN Computation.thinkN

/-- Tail recursive version of `thinkN`. -/
@[simp]
def thinkNTR (c : Computation α) : ℕ → Computation α
  | 0     => c
  | n + 1 => thinkNTR (think c) n

@[csimp]
theorem thinkN_eq_thinkNTR : @thinkN.{u} = @thinkNTR.{u} := by
  funext α c n
  induction n generalizing c with
  | zero => rfl
  | succ n hn =>
    simp [← hn]; clear hn
    induction n with
    | zero => rfl
    | succ n hn => simp [hn]

-- check for immediate result
/-- `head c` is the first step of computation, either `some a` if `c = pure a`
  or `none` if `c = think c'`. -/
noncomputable def head (c : Computation α) : Option α :=
  runFor c 0
#align computation.head Computation.head

theorem runFor_zero (c : Computation α) : runFor c 0 = head c :=
  rfl

-- one step of computation
/-- `tail c` is the remainder of computation, either `c` if `c = pure a`
  or `c'` if `c = think c'`. -/
noncomputable def tail (c : Computation α) : Computation α where
  runFor n := runFor c (n + 1)
  succ_stable _ _ h := succ_stable c h
#align computation.tail Computation.tail

theorem runFor_succ (c : Computation α) (n : ℕ) : runFor c (n + 1) = runFor (tail c) n :=
  rfl

/-- `dest c` is the destructor for `Computation α` as a coinductive type.
  It returns `inl a` if `c = pure a` and `inr c'` if `c = think c'`. -/
@[inline]
unsafe def destUnsafe (c : Computation α) : α ⊕ Computation α :=
  unsafeCast (dest (unsafeCast c) : α ⊕ ComputationImpl α)

@[inherit_doc destUnsafe, implemented_by destUnsafe]
def dest (c : Computation α) : α ⊕ (Computation α) :=
  Option.elim (head c) (Sum.inr (tail c)) Sum.inl
#align computation.destruct Computation.dest

/-- `run c` is an unsound meta function that runs `c` to completion, possibly
  resulting in an infinite loop in the runtime. -/
unsafe def run (c : Computation α) : α :=
  Sum.elim id run (dest c)
#align computation.run Computation.run

theorem dest_eq_pure {s : Computation α} {a : α} : (hs : dest s = Sum.inl a) → s = pure a := by
  unfold dest
  cases hhs : head s with intro hs
  | none => contradiction
  | some b =>
    ext1 n
    induction n with
    | zero =>
      injection hs with hs
      rwa [hs] at hhs
    | succ n hn =>
      exact succ_stable s hn
#align computation.destruct_eq_ret Computation.dest_eq_pure

theorem dest_eq_think {s : Computation α} {s'} : (hs : dest s = Sum.inr s') → s = think s' := by
  unfold dest
  cases hhs : head s with intro hs
  | none =>
    ext1 n
    cases n with
    | zero => exact hhs
    | succ n =>
      simp at hs
      subst hs
      rfl
  | some b => contradiction
#align computation.destruct_eq_think Computation.dest_eq_think

@[simp]
theorem dest_pure (a : α) : dest (pure a) = Sum.inl a :=
  rfl
#align computation.destruct_ret Computation.dest_pure

@[simp]
theorem dest_think (s : Computation α) : dest (think s) = Sum.inr s := by
  cases s; rfl
#align computation.destruct_think Computation.dest_think

@[simp]
theorem head_pure (a : α) : head (pure a) = some a :=
  rfl
#align computation.head_ret Computation.head_pure

@[simp]
theorem head_think (s : Computation α) : head (think s) = none :=
  rfl
#align computation.head_think Computation.head_think

@[simp]
theorem tail_pure (a : α) : tail (pure a) = pure a :=
  rfl
#align computation.tail_ret Computation.tail_pure

@[simp]
theorem tail_think (s : Computation α) : tail (think s) = s := by
  ext1 (_ | _) <;> rfl
#align computation.tail_think Computation.tail_think

/-- Recursion principle for computations, compare with `List.recOn`. -/
@[elab_as_elim]
def recOn' {C : Computation α → Sort v} (s : Computation α) (pure : ∀ a, C (pure a))
    (think : ∀ s, C (think s)) : C s :=
  match H : dest s with
  | Sum.inl v => cast (congr_arg C (dest_eq_pure H)).symm (pure v)
  | Sum.inr v => cast (congr_arg C (dest_eq_think H)).symm (think v)
#align computation.rec_on Computation.recOn'

theorem dest_injective : Injective (dest : Computation α → α ⊕ Computation α) := by
  intro c₁ c₂ hc
  cases c₂ using recOn' with
  | pure a => rw [dest_pure] at hc; exact dest_eq_pure hc
  | think c₂ => rw [dest_think] at hc; exact dest_eq_think hc

@[inherit_doc head, simp]
def headComputable (c : Computation α) : Option α :=
  Sum.getLeft? (dest c)

@[csimp]
theorem head_eq_headComputable : @head.{u} = @headComputable.{u} := by
  funext α c
  cases c using recOn' <;> simp

@[inherit_doc tail, simp]
def tailComputable (c : Computation α) : Computation α :=
  Sum.elim pure id (dest c)

@[csimp]
theorem tail_eq_tailComputable : @tail.{u} = @tailComputable.{u} := by
  funext α c
  cases c using recOn' <;> simp

@[inherit_doc runFor, simp]
def runForComputable (c : Computation α) (n : ℕ) : Option α :=
  Sum.getLeft? (loop c n)
where
  @[inherit_doc runFor, simp]
  loop (c : Computation α) : ℕ → α ⊕ Computation α
    | 0     => dest c
    | n + 1 => Sum.elim Sum.inl (fun c => loop c n) (dest c)

@[csimp]
theorem runFor_eq_runForComputable : @runFor.{u} = @runForComputable.{u} := by
  funext α c n
  unfold runForComputable
  induction n generalizing c with
  | zero => cases c using recOn' <;> simp [runFor_zero]
  | succ n hn => cases c using recOn' <;> simp [runFor_succ (think _), hn]

/-- The implemention of `Computation.casesOn`. -/
@[inline]
protected def casesOnComputable {α : Type u} {motive : Computation α → Sort*}
    (c : Computation α)
    (mk : (runFor : ℕ → Option α) →
      (succ_stable : ∀ ⦃n a⦄, runFor n = some a → runFor (n + 1) = some a) →
      motive (mk runFor succ_stable)) : motive c :=
  mk (runFor c) (succ_stable c)

@[csimp]
theorem casesOn_eq_casesOnComputable :
    @Computation.casesOn.{v, u} = @Computation.casesOnComputable.{v, u} :=
  rfl

set_option linter.uppercaseLean3 false in
#noalign computation.corec.F

/-- `corec f b` is the corecursor for `Computation α` as a coinductive type.
  If `f b = inl a` then `corec f b = pure a`, and if `f b = inl b'` then
  `corec f b = think (corec f b')`. -/
@[specialize]
unsafe def corecUnsafe (f : β → α ⊕ β) (b : β) : Computation α :=
  unsafeCast (corec f b)

@[inherit_doc corecUnsafe, implemented_by corecUnsafe]
def corec (f : β → α ⊕ β) (b : β) : Computation α where
  runFor n := Sum.getLeft? ((Sum.elim Sum.inl f)^[n] (f b))
  succ_stable n a h := by
    simp at h
    simp [iterate_succ', h, - iterate_succ]
#align computation.corec Computation.corec

@[simp]
theorem runFor_corec (f : β → α ⊕ β) (b : β) (n : ℕ) :
    runFor (corec f b) n = Sum.getLeft? ((Sum.elim Sum.inl f)^[n] (f b)) :=
  rfl

@[simp]
theorem dest_corec (f : β → α ⊕ β) (b : β) : dest (corec f b) = Sum.map id (corec f) (f b) := by
  cases hb : f b <;> simp [corec, dest, head, tail, hb]
#align computation.corec_eq Computation.dest_corec

@[inherit_doc mk, nolint unusedArguments, specialize, simp]
def mkComputable (f : ℕ → Option α) (_ : ∀ ⦃n a⦄, f n = some a → f (n + 1) = some a) :
    Computation α :=
  corec (fun n => Option.elim (f n) (Sum.inr (n + 1)) Sum.inl) 0

@[csimp]
theorem mk_eq_mkComputable : @mk.{u} = @mkComputable.{u} := by
  funext α f hf
  ext1 n
  simp [- Option.elim]; symm
  induction n with
  | zero => cases f 0 <;> simp
  | succ n hn =>
    cases hfn : f n with
    | none =>
      clear hn
      suffices he :
          (Sum.elim Sum.inl fun n ↦ Option.elim (f n) (Sum.inr (n + 1)) Sum.inl)^[n]
            (Option.elim (f 0) (Sum.inr 1) Sum.inl) = Sum.inr (n + 1) by
        simp [iterate_succ', he, hfn, - iterate_succ, Option.elim_none, - Option.elim]
        cases f (n + 1) <;> simp
      induction n with
      | zero => simp [hfn]
      | succ n hn =>
        cases hfn' : f n with
        | none =>
          simp [iterate_succ', hn hfn', hfn, Option.elim_none, - iterate_succ, - Option.elim]
        | some a => simp [hf hfn'] at hfn
    | some a =>
      simp [hfn, - Option.elim] at hn
      simp [iterate_succ', hn, hf hfn, - iterate_succ, - Option.elim]

#noalign computation.lmap

#noalign computation.rmap

/-- `empty` is the computation that never returns, an infinite sequence of
  `think`s. -/
noncomputable def empty : Computation α where
  runFor _ := none
  succ_stable _ _ h := h
#align computation.empty Computation.empty

@[inherit_doc empty, simp]
def emptyComputable : Computation α :=
  corec Sum.inr ()

@[csimp]
theorem empty_eq_emptyComputable : @empty.{u} = @emptyComputable.{u} := by
  funext α
  simp [empty, corec]

instance : EmptyCollection (Computation α) where
  emptyCollection := empty

@[simp]
theorem runFor_empty (n : ℕ) : runFor (∅ : Computation α) n = none :=
  rfl

@[simp]
theorem empty_eq_empty : (empty : Computation α) = ∅ :=
  rfl

instance : Inhabited (Computation α) :=
  ⟨∅⟩

@[simp]
theorem dest_empty : dest (∅ : Computation α) = Sum.inr ∅ :=
  rfl
#align computation.destruct_empty Computation.dest_empty

@[simp]
theorem head_empty : head (∅ : Computation α) = none :=
  rfl
#align computation.head_empty Computation.head_empty

@[simp]
theorem tail_empty : tail (∅ : Computation α) = ∅ :=
  rfl
#align computation.tail_empty Computation.tail_empty

theorem think_empty : (∅ : Computation α) = think ∅ :=
  dest_eq_think dest_empty
#align computation.think_empty Computation.think_empty

section Bisim

variable (R : Computation α → Computation α → Prop)

/-- Bisimilarity over a sum of `Computation`s-/
def BisimO : α ⊕ Computation α → α ⊕ Computation α → Prop
  | Sum.inl a, Sum.inl a' => a = a'
  | Sum.inr s, Sum.inr s' => R s s'
  | _, _ => False
#align computation.bisim_o Computation.BisimO

attribute [simp] BisimO

/-- Attribute expressing bisimilarity over two `Computation`s -/
def IsBisimulation :=
  ∀ ⦃s₁ s₂⦄, R s₁ s₂ → BisimO R (dest s₁) (dest s₂)
#align computation.is_bisimulation Computation.IsBisimulation

-- If two computations are bisimilar, then they are equal
theorem eq_of_bisim (bisim : IsBisimulation R) {s₁ s₂} (r : R s₁ s₂) : s₁ = s₂ := by
  ext1 n
  induction n generalizing s₁ s₂ with
  | zero =>
    specialize bisim r
    match hs₁ : dest s₁, hs₂ : dest s₂, bisim with
    | Sum.inl a, Sum.inl _, rfl =>
      simp [dest_eq_pure hs₁, dest_eq_pure hs₂]
    | Sum.inr s₁', Sum.inr s₂', _ =>
      simp [dest_eq_think hs₁, dest_eq_think hs₂, runFor_zero]
  | succ n hn =>
    specialize bisim r
    match hs₁ : dest s₁, hs₂ : dest s₂, bisim with
    | Sum.inl a, Sum.inl _, rfl =>
      simp [dest_eq_pure hs₁, dest_eq_pure hs₂]
    | Sum.inr s₁', Sum.inr s₂', r =>
      simp [dest_eq_think hs₁, dest_eq_think hs₂, hn r, runFor_succ]
#align computation.eq_of_bisim Computation.eq_of_bisim

end Bisim

-- It's more of a stretch to use ∈ for this relation, but it
-- asserts that the computation limits to the given value.
/-- Assertion that a `Computation` limits to a given value-/
protected def Mem (a : α) (s : Computation α) :=
  ∃ n, runFor s n = some a
#align computation.mem Computation.Mem

instance : Membership α (Computation α) :=
  ⟨Computation.Mem⟩

theorem mem_def (a : α) (s : Computation α) : a ∈ s ↔ ∃ n, runFor s n = some a :=
  Iff.rfl

theorem le_stable (s : Computation α) {a m n} (h : m ≤ n) :
    runFor s m = some a → runFor s n = some a := by
  cases' s with f al
  induction' h with n _ IH
  exacts [id, fun h2 => al (IH h2)]
#align computation.le_stable Computation.le_stable

theorem mem_unique {s : Computation α} {a b : α} : a ∈ s → b ∈ s → a = b
  | ⟨m, ha⟩, ⟨n, hb⟩ => by
    injection
      (le_stable s (le_max_left m n) ha).symm.trans (le_stable s (le_max_right m n) hb)
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

theorem terminates_def (s : Computation α) : Terminates s ↔ ∃ n, (runFor s n).isSome :=
  ⟨fun ⟨⟨a, n, h⟩⟩ =>
    ⟨n, by
      rw [h]
      exact rfl⟩,
    fun ⟨n, h⟩ => ⟨⟨Option.get _ h, n, Option.eq_some_of_isSome h⟩⟩⟩
#align computation.terminates_def Computation.terminates_def

theorem mem_pure (a : α) : a ∈ pure a :=
  Exists.intro 0 rfl
#align computation.ret_mem Computation.mem_pure

theorem eq_of_mem_pure {a a' : α} (h : a' ∈ pure a) : a = a' :=
  mem_unique (mem_pure _) h
#align computation.eq_of_ret_mem Computation.eq_of_mem_pureₓ

@[simp]
theorem mem_pure_iff {a a' : α} : a' ∈ pure a ↔ a = a' :=
  ⟨eq_of_mem_pure, fun h => h ▸ mem_pure a⟩

instance pure_terminates (a : α) : Terminates (pure a) :=
  terminates_of_mem (mem_pure _)
#align computation.ret_terminates Computation.pure_terminates

theorem mem_think {s : Computation α} {a} : a ∈ s → a ∈ think s
  | ⟨n, h⟩ => ⟨n + 1, h⟩
#align computation.think_mem Computation.mem_think

instance think_terminates (s : Computation α) : ∀ [Terminates s], Terminates (think s)
  | ⟨⟨a, n, h⟩⟩ => ⟨⟨a, n + 1, h⟩⟩
#align computation.think_terminates Computation.think_terminates

theorem of_mem_think {s : Computation α} {a} : a ∈ think s → a ∈ s
  | ⟨n, h⟩ => by
    cases' n with n'
    · contradiction
    · exact ⟨n', h⟩
#align computation.of_think_mem Computation.of_mem_think

@[simp]
theorem mem_think_iff {s : Computation α} {a} : a ∈ think s ↔ a ∈ s :=
  ⟨of_mem_think, mem_think⟩

theorem of_think_terminates {s : Computation α} : Terminates (think s) → Terminates s
  | ⟨⟨a, h⟩⟩ => ⟨⟨a, of_mem_think h⟩⟩
#align computation.of_think_terminates Computation.of_think_terminates

theorem not_mem_empty (a : α) : a ∉ (∅ : Computation α) := fun ⟨n, h⟩ => by contradiction
#align computation.not_mem_empty Computation.not_mem_empty

theorem not_terminates_empty : ¬Terminates (∅ : Computation α) := fun ⟨⟨a, h⟩⟩ => not_mem_empty a h
#align computation.not_terminates_empty Computation.not_terminates_empty

theorem eq_empty_of_not_terminates {s : Computation α} (H : ¬Terminates s) : s = ∅ := by
  ext1 n
  induction' h : runFor s n with _; · rfl
  refine absurd ?_ H; exact ⟨⟨_, _, h⟩⟩
#align computation.eq_empty_of_not_terminates Computation.eq_empty_of_not_terminates

@[simp]
theorem mem_thinkN {s : Computation α} {a} : ∀ n, a ∈ thinkN s n ↔ a ∈ s
  | 0 => Iff.rfl
  | n + 1 => Iff.trans mem_think_iff (mem_thinkN n)
set_option linter.uppercaseLean3 false in
#align computation.thinkN_mem Computation.mem_thinkN

instance thinkN_terminates (s : Computation α) : ∀ [Terminates s] (n), Terminates (thinkN s n)
  | ⟨⟨a, h⟩⟩, n => ⟨⟨a, (mem_thinkN n).2 h⟩⟩
set_option linter.uppercaseLean3 false in
#align computation.thinkN_terminates Computation.thinkN_terminates

theorem of_thinkN_terminates (s : Computation α) (n) : Terminates (thinkN s n) → Terminates s
  | ⟨⟨a, h⟩⟩ => ⟨⟨a, (mem_thinkN _).1 h⟩⟩
set_option linter.uppercaseLean3 false in
#align computation.of_thinkN_terminates Computation.of_thinkN_terminates

theorem terminates_iff_acc {c : Computation α} :
    Terminates c ↔ Acc (fun c₁ c₂ => dest c₂ = Sum.inr c₁) c := by
  constructor
  · intro hc
    simp only [terminates_iff, mem_def] at hc
    rcases hc with ⟨a, n, hc⟩
    induction n generalizing c with
    | zero =>
      cases c using recOn' with
      | pure a =>
        simp at hc; subst hc
        constructor; intro c' hc'
        simp at hc'
      | think c => simp [runFor_zero] at hc
    | succ n hn =>
      cases c using recOn' with
      | pure a =>
        simp at hc; subst hc
        constructor; intro c' hc'
        simp at hc'
      | think c =>
        simp [runFor_succ] at hc
        constructor; intro c' hc'
        simp at hc'; subst hc'
        exact hn hc
  · intro hc
    induction hc with
    | intro c' hc'₂ hc' =>
      clear c hc'₂
      cases c' using recOn' with
      | pure a => apply pure_terminates
      | think c' =>
        refine @think_terminates _ _ (hc' c' ?_)
        simp

/-- `Promises s a`, or `s ~> a`, asserts that although the computation `s`
  may not terminate, if it does, then the result is `a`. -/
def Promises (s : Computation α) (a : α) : Prop :=
  ∀ ⦃a'⦄, a' ∈ s → a = a'
#align computation.promises Computation.Promises

/-- `Promises s a`, or `s ~> a`, asserts that although the computation `s`
  may not terminate, if it does, then the result is `a`. -/
infixl:50 " ~> " => Promises

theorem mem_promises {s : Computation α} {a : α} : a ∈ s → s ~> a := fun h _ => mem_unique h
#align computation.mem_promises Computation.mem_promises

theorem empty_promises (a : α) : ∅ ~> a := fun _ h => absurd h (not_mem_empty _)
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
  Exists.intro (length s) (Option.eq_some_of_isSome _)
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
  get_eq_of_mem _ <| (mem_thinkN _).2 (get_mem _)
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
  let h := Computation.pure_terminates a
  Nat.eq_zero_of_le_zero <| Nat.find_min' ((terminates_def (pure a)).1 h) rfl
#align computation.length_ret Computation.length_pure

@[simp]
theorem results_pure (a : α) : Results (pure a) a 0 :=
  ⟨mem_pure a, length_pure _⟩
#align computation.results_ret Computation.results_pure

@[simp]
theorem length_think (s : Computation α) [h : Terminates s] : length (think s) = length s + 1 := by
  apply le_antisymm
  · exact Nat.find_min' _ (Nat.find_spec ((terminates_def _).1 h))
  · have : (Option.isSome (runFor (think s) (length (think s))) : Prop) :=
      Nat.find_spec ((terminates_def _).1 s.think_terminates)
    revert this; cases' length (think s) with n <;> intro this
    · simp [runFor_zero] at this
    · apply Nat.succ_le_succ
      apply Nat.find_min'
      apply this
#align computation.length_think Computation.length_think

theorem results_think {s : Computation α} {a n} (h : Results s a n) : Results (think s) a (n + 1) :=
  haveI := h.terminates
  ⟨mem_think h.mem, by rw [length_think, h.length]⟩
#align computation.results_think Computation.results_think

theorem of_results_think {s : Computation α} {a n} (h : Results (think s) a n) :
    ∃ m, Results s a m ∧ n = m + 1 := by
  haveI := of_think_terminates h.terminates
  have := results_of_terminates' _ (of_mem_think h.mem)
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
  induction' n with n IH generalizing s <;> induction' s using recOn' with a s
  · rw [← eq_of_mem_pure h.mem]
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

/-- Corecursive verseion of `length` and `get`. -/
@[inline, simp]
def lengthGetCorec (c : Computation α) [h : Terminates c] : ℕ × α :=
  loop (terminates_iff_acc.mp h) 0
where
  /-- The mail loop for `lengthGetCorec`. -/
  loop {c : Computation α} (hc : Acc (fun c₁ c₂ => dest c₂ = Sum.inr c₁) c) (n : ℕ) : ℕ × α :=
    Acc.rec
      (fun c _ F n =>
        match hc : dest c with
        | Sum.inl a => (n, a)
        | Sum.inr c => F c hc (n + 1))
      hc n

theorem lengthGetCorec.loop_intro {c : Computation α}
    (hc : ∀ c', dest c = Sum.inr c' → Acc (fun c₁ c₂ => dest c₂ = Sum.inr c₁) c') (n : ℕ) :
    loop (Acc.intro c hc) n =
      match hc' : dest c with
      | Sum.inl a => (n, a)
      | Sum.inr c => loop (hc c hc') (n + 1) :=
  rfl

theorem lengthGetCorec.loop_eq {c : Computation α}
    (hc : Acc (fun c₁ c₂ => dest c₂ = Sum.inr c₁) c) (n : ℕ) :
    loop hc n =
      (@length _ c (terminates_iff_acc.mpr hc) + n, @get _ c (terminates_iff_acc.mpr hc)) := by
  induction hc generalizing n with
  | intro c hh hc =>
    rw [lengthGetCorec.loop_intro hh]
    split
    next a ha =>
      replace ha := dest_eq_pure ha; subst ha
      simp
    next c' hc' =>
      replace hc' := dest_eq_think hc'; subst hc'
      have htc' := terminates_iff_acc.mpr (hh c' (dest_think c'))
      simp [hc, Nat.add_assoc, Nat.add_comm n 1]

/-- Corecursive version of `length`. -/
@[inline, simp]
def lengthCorec (c : Computation α) [h : Terminates c] : ℕ :=
  (@lengthGetCorec _ c h).1

@[csimp]
theorem length_eq_lengthCorec : @length.{u} = @lengthCorec.{u} := by
  funext α c h
  simp [lengthGetCorec.loop_eq]

/-- Corecursive version of `get`. -/
@[inline, simp]
def getCorec (c : Computation α) [h : Terminates c] : α :=
  (@lengthGetCorec _ c h).2

@[csimp]
theorem get_eq_getCorec : @get.{u} = @getCorec.{u} := by
  funext α c h
  simp [lengthGetCorec.loop_eq]

/-- Recursor based on membership -/
@[elab_as_elim]
def memRecOn {a} {C : (s : Computation α) → a ∈ s → Sort v} {s} (M : a ∈ s)
    (mem_pure : C (pure a) (mem_pure a))
    (mem_think : {s : _} → (h : a ∈ s) → C s h → C (think s) (mem_think h)) : C s M := by
  haveI T := terminates_of_mem M
  have M' := M
  revert M
  rw [eq_thinkN' s, get_eq_of_mem s M']
  generalize length s = n
  intro M
  change C (thinkN (pure a) n) ((mem_thinkN (n := n)).mpr (Computation.mem_pure a))
  clear M M'
  induction' n with n IH; exacts [mem_pure, mem_think _ IH]
#align computation.mem_rec_on Computation.memRecOnₓ

/-- Recursor based on assertion of `Terminates` -/
@[elab_as_elim]
def terminatesRecOn
    {C : (s : Computation α) → Terminates s → Sort v} {s} (M : Terminates s)
    (pure_terminates : (a : _) → C (pure a) (pure_terminates a))
    (think_terminates :
      (s : _) → (h : Terminates s) → C s h → C (think s) (@think_terminates _ _ h)) : C s M :=
  memRecOn (C := fun s' h => C s' (terminates_of_mem h)) (get_mem s) (pure_terminates (get s))
    (fun {s'} h ih => think_terminates s' (terminates_of_mem h) ih)
#align computation.terminates_rec_on Computation.terminatesRecOnₓ

/-- Map a function on the result of a computation. -/
def map (f : α → β) (c : Computation α) : Computation β where
  runFor n := Option.map f (runFor c n)
  succ_stable n a h := by
    rw [Option.map_eq_some'] at h ⊢
    rcases h with ⟨b, hb, rfl⟩
    exact ⟨b, succ_stable c hb, rfl⟩
#align computation.map Computation.map

@[simp]
theorem runFor_map (f : α → β) (c : Computation α) (n : ℕ) :
    runFor (map f c) n = Option.map f (runFor c n) :=
  rfl

@[simp]
theorem map_pure (f : α → β) (a) : map f (pure a) = pure (f a) :=
  rfl
#align computation.map_ret Computation.map_pure

@[simp]
theorem map_think (f : α → β) (s) : map f (think s) = think (map f s) := by
  ext1 (_ | _) <;> rfl
#align computation.map_think Computation.map_think

@[simp]
theorem dest_map (f : α → β) (s) : dest (map f s) = Sum.map f (map f) (dest s) := by
  induction s using recOn' <;> simp
#align computation.destruct_map Computation.dest_map

@[inherit_doc map, inline]
def mapComputable (f : α → β) (c : Computation α) : Computation β :=
  corec (Sum.map f id ∘ dest) c

@[csimp]
theorem map_eq_mapComputable : @map.{u, v} = @mapComputable.{u, v} := by
  funext α β f c
  refine eq_of_bisim (fun c₁ c₂ => ∃ c, c₁ = map f c ∧ c₂ = corec (Sum.map f id ∘ dest) c)
    ?_ ⟨c, rfl, rfl⟩; clear c
  rintro _ _ ⟨c, rfl, rfl⟩
  induction c using recOn' with
  | pure a => simp
  | think c => simp; exists c

@[simp]
theorem map_id (c : Computation α) : map id c = c := by
  ext1 n; simp
#align computation.map_id Computation.map_id

@[simp]
theorem map_map (g : β → γ) (f : α → β) (c : Computation α) : map g (map f c) = map (g ∘ f) c := by
  ext1 n; simp
#align computation.map_comp Computation.map_map

/-- Corecursor where it is possible to return a fully formed value at any point of the
computation. -/
@[inline]
unsafe def corec'Unsafe (f : β → Computation α ⊕ α ⊕ β) (b : β) : Computation α :=
  unsafeCast (corec' (unsafeCast f) b : ComputationImpl α)

@[inherit_doc corec'Unsafe, implemented_by corec'Unsafe]
def corec' (f : β → Computation α ⊕ α ⊕ β) (b : β) : Computation α :=
  corec
    (Sum.elim (Sum.map id Sum.inl ∘ dest) (Sum.map id Sum.inr) ∘ Sum.elim Sum.inl f)
    (Sum.inr b)

@[simp]
theorem dest_corec' (f : β → Computation α ⊕ α ⊕ β) (b : β) :
    dest (corec' f b) = Sum.elim dest (Sum.map id (corec' f)) (f b) := by
  simp (config := { unfoldPartialApp := true }) [corec']
  rcases f b with (c | a | b) <;> simp
  rcases dest c with (a | c') <;> simp; clear c
  refine eq_of_bisim
    (fun c₁ c₂ =>
      c₁ = corec
        (Sum.elim (Sum.map id Sum.inl ∘ dest) (Sum.map id Sum.inr) ∘ Sum.elim Sum.inl f)
        (Sum.inl c₂))
    ?_ rfl; clear c'
  rintro _ c rfl
  simp; cases dest c <;> simp

set_option linter.uppercaseLean3 false in
#noalign computation.bind.G

set_option linter.uppercaseLean3 false in
#noalign computation.bind.F

/-- Compose two computations into a monadic `bind` operation. -/
@[inline]
def bind (c : Computation α) (f : α → Computation β) : Computation β :=
  corec' (Sum.elim (Sum.inl ∘ f) (Sum.inr ∘ Sum.inr) ∘ dest) c
#align computation.bind Computation.bind

instance : Bind Computation :=
  ⟨@bind⟩

@[simp]
theorem bind_eq_bind {β} (c : Computation α) (f : α → Computation β) : c >>= f = bind c f :=
  rfl
#align computation.has_bind_eq_bind Computation.bind_eq_bind

/-- Flatten a computation of computations into a single computation. -/
def join (c : Computation (Computation α)) : Computation α :=
  bind c id
#align computation.join Computation.join

@[simp]
theorem pure_bind (a) (f : α → Computation β) : bind (pure a) f = f a := by
  apply dest_injective
  simp [bind]
#align computation.ret_bind Computation.pure_bind

@[simp]
theorem think_bind (c) (f : α → Computation β) : bind (think c) f = think (bind c f) := by
  apply dest_eq_think
  simp [bind]
#align computation.think_bind Computation.think_bind

@[simp]
theorem bind_pure (f : α → β) (s) : bind s (pure ∘ f) = map f s := by
  apply eq_of_bisim fun c₁ c₂ => c₁ = c₂ ∨ ∃ s, c₁ = bind s (pure ∘ f) ∧ c₂ = map f s
  · intro c₁ c₂ h
    exact
      match c₁, c₂, h with
      | _, c₂, Or.inl (Eq.refl _) => by cases' dest c₂ with b cb <;> simp
      | _, _, Or.inr ⟨s, rfl, rfl⟩ => by
        induction' s using recOn' with _ s <;> simp
        exact Or.inr ⟨s, rfl, rfl⟩
  · exact Or.inr ⟨s, rfl, rfl⟩
#align computation.bind_ret Computation.bind_pure

-- Porting note: used to use `rw [bind_pure]`
@[simp]
theorem bind_pure' (s : Computation α) : bind s pure = s := by
  apply eq_of_bisim fun c₁ c₂ => c₁ = c₂ ∨ ∃ s, c₁ = bind s pure ∧ c₂ = s
  · intro c₁ c₂ h
    exact
      match c₁, c₂, h with
      | _, c₂, Or.inl (Eq.refl _) => by cases' dest c₂ with b cb <;> simp
      | _, _, Or.inr ⟨s, rfl, rfl⟩ => by
        induction' s using recOn' with _ s <;> simp
  · exact Or.inr ⟨s, rfl, rfl⟩
#align computation.bind_ret' Computation.bind_pure'

@[simp]
theorem bind_assoc (s : Computation α) (f : α → Computation β) (g : β → Computation γ) :
    bind (bind s f) g = bind s fun x : α => bind (f x) g := by
  apply
    eq_of_bisim fun c₁ c₂ =>
      c₁ = c₂ ∨ ∃ s, c₁ = bind (bind s f) g ∧ c₂ = bind s fun x : α => bind (f x) g
  · intro c₁ c₂ h
    exact
      match c₁, c₂, h with
      | _, c₂, Or.inl (Eq.refl _) => by cases' dest c₂ with b cb <;> simp
      | _, _, Or.inr ⟨s, rfl, rfl⟩ => by
        induction' s using recOn' with a s <;> simp
        · generalize f a = fs
          induction' fs using recOn' with b _ <;> simp
          · cases' dest (g b) with b cb <;> simp
        · exact Or.inr ⟨s, rfl, rfl⟩
  · exact Or.inr ⟨s, rfl, rfl⟩
#align computation.bind_assoc Computation.bind_assoc

theorem results_bind {s : Computation α} {f : α → Computation β} {a b m n} (h1 : Results s a m)
    (h2 : Results (f a) b n) : Results (bind s f) b (n + m) := by
  induction h1.mem using memRecOn generalizing m with
  | mem_pure =>
    rw [pure_bind]
    rw [h1.len_unique (results_pure _)]
    exact h2
  | mem_think _ h3 =>
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
  induction' k with n IH generalizing s <;> induction' s using recOn' with a s' <;> intro h
  · simp [thinkN] at h
    exact ⟨a, _, _, results_pure _, h, rfl⟩
  · have := congr_arg head (eq_thinkN h)
    contradiction
  · simp at h
    exact ⟨a, _, n + 1, results_pure _, h, rfl⟩
  · simp at h
    exact by
      let ⟨a, m, n', h1, h2, e'⟩ := IH h
      rw [e']; exact ⟨a, m.succ, n', results_think h1, h2, rfl⟩
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
  (pure_bind := @pure_bind)
  (bind_assoc := @bind_assoc)

@[simp]
theorem map_eq_map {β} (f : α → β) (c : Computation α) : f <$> c = map f c :=
  rfl
#align computation.has_map_eq_map Computation.map_eq_map

@[simp]
theorem pure_def (a) : (Pure.pure a : Computation α) = pure a :=
  rfl
#align computation.return_def Computation.pure_def

theorem map_pure' {α β} : ∀ (f : α → β) (a), f <$> pure a = pure (f a) :=
  map_pure
#align computation.map_ret' Computation.map_pure'

theorem map_think' {α β} : ∀ (f : α → β) (s), f <$> think s = think (f <$> s) :=
  map_think
#align computation.map_think' Computation.map_think'

theorem mem_map (f : α → β) {a} {s : Computation α} (m : a ∈ s) : f a ∈ map f s := by
  rw [← bind_pure]; apply mem_bind m; apply mem_pure
#align computation.mem_map Computation.mem_map

theorem exists_of_mem_map {f : α → β} {b : β} {s : Computation α} (h : b ∈ map f s) :
    ∃ a, a ∈ s ∧ f a = b := by
  rw [← bind_pure] at h
  exact
    let ⟨a, as, fb⟩ := exists_of_mem_bind h
    ⟨a, as, mem_unique (mem_pure _) fb⟩
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
      match dest c₁ with
      | Sum.inl a => Sum.inl a
      | Sum.inr c₁' =>
        match dest c₂ with
        | Sum.inl a => Sum.inl a
        | Sum.inr c₂' => Sum.inr (c₁', c₂'))
    (c₁, c₂ ())
#align computation.orelse Computation.orElse

instance instAlternativeComputation : Alternative Computation :=
  { Computation.monad with
    orElse := @orElse
    failure := ∅ }

@[simp]
theorem failure_eq_empty : (failure : Computation α) = ∅ :=
  rfl

-- Porting note: Added unfolds as the code does not work without it
@[simp]
theorem pure_orElse (a : α) (c₂ : Computation α) : (pure a <|> c₂) = pure a :=
  dest_eq_pure <| by
    unfold_projs
    simp [orElse]
#align computation.ret_orelse Computation.pure_orElse

-- Porting note: Added unfolds as the code does not work without it
@[simp]
theorem orElse_pure (c₁ : Computation α) (a : α) : (think c₁ <|> pure a) = pure a :=
  dest_eq_pure <| by
    unfold_projs
    simp [orElse]
#align computation.orelse_ret Computation.orElse_pure

-- Porting note: Added unfolds as the code does not work without it
@[simp]
theorem orElse_think (c₁ c₂ : Computation α) : (think c₁ <|> think c₂) = think (c₁ <|> c₂) :=
  dest_eq_think <| by
    unfold_projs
    simp [orElse]
#align computation.orelse_think Computation.orElse_think

@[simp]
theorem empty_orElse (c : Computation α) : (∅ <|> c) = c := by
  apply eq_of_bisim (fun c₁ c₂ => (∅ <|> c₂) = c₁) _ rfl
  intro s' s h; rw [← h]
  induction s using recOn' <;> rw [think_empty] <;> simp
  rw [← think_empty]
#align computation.empty_orelse Computation.empty_orElse

@[simp]
theorem orElse_empty (c : Computation α) : (c <|> ∅) = c := by
  apply eq_of_bisim (fun c₁ c₂ => (c₂ <|> ∅) = c₁) _ rfl
  intro s' s h; rw [← h]
  induction s using recOn' <;> rw [think_empty] <;> simp
  rw [← think_empty]
#align computation.orelse_empty Computation.orElse_empty

/-- `Equiv c₁ c₂` asserts that `c₁` and `c₂` either both terminate with the same result,
  or both loop forever. -/
def Equiv (c₁ c₂ : Computation α) : Prop :=
  ∀ a, a ∈ c₁ ↔ a ∈ c₂
#align computation.equiv Computation.Equiv

theorem Equiv.refl (s : Computation α) : Equiv s s := fun _ => Iff.rfl
#align computation.equiv.refl Computation.Equiv.refl

theorem Equiv.symm {s t : Computation α} : Equiv s t → Equiv t s := fun h a => (h a).symm
#align computation.equiv.symm Computation.Equiv.symm

theorem Equiv.trans {s t u : Computation α} : Equiv s t → Equiv t u → Equiv s u := fun h1 h2 a =>
  (h1 a).trans (h2 a)
#align computation.equiv.trans Computation.Equiv.trans

theorem Equiv.equivalence : Equivalence (@Equiv α) :=
  ⟨@Equiv.refl _, @Equiv.symm _, @Equiv.trans _⟩
#align computation.equiv.equivalence Computation.Equiv.equivalence

instance : Setoid (Computation α) where
  r     := Equiv
  iseqv := Equiv.equivalence

theorem equiv_of_mem {s t : Computation α} {a} (h1 : a ∈ s) (h2 : a ∈ t) : s ≈ t := fun a' =>
  ⟨fun ma => by rw [mem_unique ma h1]; exact h2, fun ma => by rw [mem_unique ma h2]; exact h1⟩
#align computation.equiv_of_mem Computation.equiv_of_mem

theorem terminates_congr {c₁ c₂ : Computation α} (h : c₁ ≈ c₂) : Terminates c₁ ↔ Terminates c₂ := by
  simp only [terminates_iff, exists_congr h]
#align computation.terminates_congr Computation.terminates_congr

theorem promises_congr {c₁ c₂ : Computation α} (h : c₁ ≈ c₂) (a) : c₁ ~> a ↔ c₂ ~> a :=
  forall_congr' fun a' => imp_congr (h a') Iff.rfl
#align computation.promises_congr Computation.promises_congr

theorem get_equiv {c₁ c₂ : Computation α} (h : c₁ ≈ c₂) [Terminates c₁] [Terminates c₂] :
    get c₁ = get c₂ :=
  get_eq_of_mem _ <| (h _).2 <| get_mem _
#align computation.get_equiv Computation.get_equiv

theorem think_equiv (s : Computation α) : think s ≈ s := fun _ => mem_think_iff
#align computation.think_equiv Computation.think_equiv

theorem thinkN_equiv (s : Computation α) (n) : thinkN s n ≈ s := fun _ => mem_thinkN n
set_option linter.uppercaseLean3 false in
#align computation.thinkN_equiv Computation.thinkN_equiv

theorem bind_congr {s1 s2 : Computation α} {f1 f2 : α → Computation β} (h1 : s1 ≈ s2)
    (h2 : ∀ a, f1 a ≈ f2 a) : bind s1 f1 ≈ bind s2 f2 := fun b =>
  ⟨fun h =>
    let ⟨a, ha, hb⟩ := exists_of_mem_bind h
    mem_bind ((h1 a).1 ha) ((h2 a b).1 hb),
    fun h =>
    let ⟨a, ha, hb⟩ := exists_of_mem_bind h
    mem_bind ((h1 a).2 ha) ((h2 a b).2 hb)⟩
#align computation.bind_congr Computation.bind_congr

theorem equiv_pure_of_mem {s : Computation α} {a} (h : a ∈ s) : s ≈ pure a :=
  equiv_of_mem h (mem_pure _)
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

theorem lift_eq_iff_equiv (c₁ c₂ : Computation α) : LiftRel (· = ·) c₁ c₂ ↔ c₁ ≈ c₂ :=
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
  ⟨fun ⟨l, _⟩ => l (mem_pure _), fun ⟨b, mb, ab⟩ =>
    ⟨fun {a'} ma' => by rw [← eq_of_mem_pure ma']; exact ⟨b, mb, ab⟩, fun {b'} mb' =>
      ⟨_, mem_pure _, by rw [mem_unique mb' mb]; exact ab⟩⟩⟩
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
  exact ⟨fun ⟨b', mb', ab'⟩ => by rwa [← eq_of_mem_pure mb'] at ab', fun ab => ⟨_, mem_pure _, ab⟩⟩
#align computation.lift_rel_return Computation.liftRel_pure

@[simp]
theorem liftRel_think_left (R : α → β → Prop) (ca : Computation α) (cb : Computation β) :
    LiftRel R (think ca) cb ↔ LiftRel R ca cb :=
  and_congr (forall_congr' fun _ => imp_congr mem_think_iff Iff.rfl)
    (forall_congr' fun _ =>
      imp_congr Iff.rfl <| exists_congr fun _ => and_congr mem_think_iff Iff.rfl)
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
    (ha : ca ≈ ca') (hb : cb ≈ cb') : LiftRel R ca cb ↔ LiftRel R ca' cb' :=
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
  simp; exact h2
#align computation.lift_rel_map Computation.liftRel_map

-- Porting note: deleted initial arguments `(_R : α → α → Prop) (_S : β → β → Prop)`: unused
theorem map_congr {s1 s2 : Computation α} {f : α → β}
    (h1 : s1 ≈ s2) : map f s1 ≈ map f s2 := by
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
theorem LiftRelAux.pure_left (R : α → β → Prop) (C : Computation α → Computation β → Prop) (a cb) :
    LiftRelAux R C (Sum.inl a) (dest cb) ↔ ∃ b, b ∈ cb ∧ R a b := by
  induction cb using recOn' with
  | pure b =>
    exact
      ⟨fun h => ⟨_, mem_pure _, h⟩, fun ⟨b', mb, h⟩ => by rw [mem_unique (mem_pure _) mb]; exact h⟩
  | think _ =>
    rw [dest_think]
    exact ⟨fun ⟨b, h, r⟩ => ⟨b, mem_think h, r⟩, fun ⟨b, h, r⟩ => ⟨b, of_mem_think h, r⟩⟩
#align computation.lift_rel_aux.ret_left Computation.LiftRelAux.pure_left

theorem LiftRelAux.swap (R : α → β → Prop) (C) (a b) :
    LiftRelAux (swap R) (swap C) b a = LiftRelAux R C a b := by
  cases' a with a ca <;> cases' b with b cb <;> simp only [LiftRelAux]
#align computation.lift_rel_aux.swap Computation.LiftRelAux.swap

@[simp]
theorem LiftRelAux.pure_right (R : α → β → Prop) (C : Computation α → Computation β → Prop) (b ca) :
    LiftRelAux R C (dest ca) (Sum.inl b) ↔ ∃ a, a ∈ ca ∧ R a b := by
  rw [← LiftRelAux.swap, LiftRelAux.pure_left]
#align computation.lift_rel_aux.ret_right Computation.LiftRelAux.pure_right

theorem LiftRelRec.lem {R : α → β → Prop} (C : Computation α → Computation β → Prop)
    (H : ∀ {ca cb}, C ca cb → LiftRelAux R C (dest ca) (dest cb)) (ca cb) (Hc : C ca cb) (a)
    (ha : a ∈ ca) : LiftRel R ca cb := by
  induction' ha using memRecOn with ca' _ IH generalizing cb <;> have h := H Hc
  · simp at h
    simp [h]
  · simp only [liftRel_think_left]
    induction cb using recOn' <;> simp at h <;> simp [h]
    exact IH _ h
#align computation.lift_rel_rec.lem Computation.LiftRelRec.lem

theorem liftRel_rec {R : α → β → Prop} (C : Computation α → Computation β → Prop)
    (H : ∀ {ca cb}, C ca cb → LiftRelAux R C (dest ca) (dest cb)) (ca cb) (Hc : C ca cb) :
    LiftRel R ca cb :=
  liftRel_mem_cases (LiftRelRec.lem C (@H) ca cb Hc) fun b hb =>
    (LiftRel.swap _ _ _).2 <|
      LiftRelRec.lem (swap C) (fun {_ _} h => cast (LiftRelAux.swap _ _ _ _).symm <| H h) cb ca Hc b
        hb
#align computation.lift_rel_rec Computation.liftRel_rec

end Computation
