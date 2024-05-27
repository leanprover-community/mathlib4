/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Data.LazyList
import Mathlib.Data.Stream
import Mathlib.Data.List.Basic
import Mathlib.Data.Seq.Computation

#align_import data.seq.seq from "leanprover-community/mathlib"@"a7e36e48519ab281320c4d192da6a7b348ce40ad"

/-!
# Possibly infinite lists

This file provides a `Seq' α` type representing possibly infinite lists
(referred here as sequences).
It is encoded as a function of options such that if `get s n = none`, then
`get s m = none` for all `m ≥ n` in the kernel, but a lazily evaluated list in the runtime.

Note that we already have `Seq` to represent an notation class, hence the awkward naming.
-/

open Function

universe u v w

namespace LazyList

variable {α : Type u} {β : Type v} {δ : Type w}

/-- Destructor for a lazy list, resulting in either `none` (for `nil`) or
  `some (a, l.get)` (for `cons a l`). -/
@[inline]
def dest : (l : LazyList α) → Option (α × LazyList α)
  | nil      => none
  | cons a t => some (a, Thunk.get t)

/-- Corecursor for `LazyList α` as a coinductive type. Iterates `f` to produce new elements
  of the sequence until `none` is obtained. -/
@[specialize]
unsafe def corec (f : β → Option (α × β)) (b : β) : LazyList α :=
  match f b with
  | none        => nil
  | some (a, b) => cons a ⟨fun _ => corec f b⟩

/-- Corecursor where it is possible to return a fully formed value at any point of the
computation. -/
@[specialize]
unsafe def corec' (f : β → LazyList α ⊕ Option (α × β)) (b : β) : LazyList α :=
  match f b with
  | Sum.inl c => c
  | Sum.inr none => nil
  | Sum.inr (some (a, b)) => cons a ⟨fun _ => corec' f b⟩

end LazyList

open LazyList

#noalign stream.is_seq

/-- `Seq' α` is the type of possibly infinite lists (referred here as sequences).
This type has special support in the runtime. -/
@[opaque_repr]
structure Seq' (α : Type u) : Type u where
  /-- Convert a `ℕ → Option α` into a `Seq' α`. Consider using other functions like `corec`
  before use this. -/
  mk ::
  /-- Get the nth element of a sequence (if it exists) -/
  get? : ℕ → Option α
  /-- `get? s n = none` implies `get? s (n + 1) = none`. -/
  succ_stable : ∀ ⦃n⦄, get? n = none → get? (n + 1) = none
#align stream.seq Seq'
#align stream.seq.nth Seq'.get?

/-- `Seq1 α` is the type of nonempty sequences. -/
structure Seq1 (α : Type u) : Type u where
  /-- Head of an nonempty sequence. -/
  head : α
  /-- Tail of an nonempty sequence. -/
  tail : Seq' α
#align stream.seq1 Seq1

namespace Seq'

variable {α : Type u} {β : Type v} {γ : Type w}

/-- The empty sequence. -/
@[inline]
unsafe def nilUnsafe : Seq' α :=
  unsafeCast (nil : LazyList α)

@[inherit_doc nilUnsafe, implemented_by nilUnsafe]
def nil : Seq' α where
  get? _ := none
  succ_stable _ _ := rfl
#align stream.seq.nil Seq'.nil

instance : Inhabited (Seq' α) :=
  ⟨nil⟩

/-- Prepend an element to a sequence -/
@[inline]
unsafe def consUnsafe (a : α) (s : Seq' α) : Seq' α :=
  unsafeCast (cons a (Thunk.pure (unsafeCast s)))

@[inherit_doc consUnsafe, implemented_by consUnsafe]
def cons (a : α) (s : Seq' α) : Seq' α where
  get?
  | 0     => some a
  | n + 1 => get? s n
  succ_stable
  | _ + 1, h => succ_stable s h
#align stream.seq.cons Seq'.cons

/-- Prepend an element to a s**e**quence -/
infixr:67 " ::ₑ " => cons

#noalign stream.seq.val_cons

#noalign stream.seq.nth_mk

@[simp]
theorem get?_nil (n : ℕ) : get? (nil : Seq' α) n = none :=
  rfl
#align stream.seq.nth_nil Seq'.get?_nil

@[simp]
theorem get?_cons_zero (a : α) (s : Seq' α) : get? (a ::ₑ s) 0 = some a :=
  rfl
#align stream.seq.nth_cons_zero Seq'.get?_cons_zero

@[simp]
theorem get?_cons_succ (a : α) (s : Seq' α) (n : ℕ) : get? (a ::ₑ s) (n + 1) = get? s n :=
  rfl
#align stream.seq.nth_cons_succ Seq'.get?_cons_succ

@[ext]
protected theorem ext {s t : Seq' α} (h : ∀ n : ℕ, s.get? n = t.get? n) : s = t := by
  cases s; cases t
  congr; funext n; apply h
#align stream.seq.ext Seq'.ext

theorem cons_injective2 : Function.Injective2 (cons : α → Seq' α → Seq' α) := fun x y s t h =>
  ⟨by rw [← Option.some_inj, ← get?_cons_zero, h, get?_cons_zero],
    Seq'.ext fun n => by simp_rw [← get?_cons_succ x s n, h, get?_cons_succ]⟩
#align stream.seq.cons_injective2 Seq'.cons_injective2

@[simp]
theorem cons_inj {a b : α} {s t : Seq' α} : a ::ₑ s = b ::ₑ t ↔ a = b ∧ s = t :=
  cons_injective2.eq_iff

theorem cons_left_injective (s : Seq' α) : Function.Injective (· ::ₑ s) :=
  cons_injective2.left _
#align stream.seq.cons_left_injective Seq'.cons_left_injective

theorem cons_right_injective (x : α) : Function.Injective (x ::ₑ ·) :=
  cons_injective2.right _
#align stream.seq.cons_right_injective Seq'.cons_right_injective

/-- A sequence has terminated at position `n` if the value at position `n` equals `none`. -/
def TerminatedAt (s : Seq' α) (n : ℕ) : Prop :=
  s.get? n = none
#align stream.seq.terminated_at Seq'.TerminatedAt

@[simp]
theorem nil_terminatedAt (n : ℕ) : (nil : Seq' α).TerminatedAt n :=
  rfl

@[simp]
theorem not_cons_terminatedAt_zero (a : α) (s : Seq' α) : ¬(a ::ₑ s).TerminatedAt 0 :=
  Option.some_ne_none a

@[simp]
theorem cons_terminatedAt_succ (a : α) (s : Seq' α) (n : ℕ) :
    (a ::ₑ s).TerminatedAt (n + 1) ↔ s.TerminatedAt n :=
  Iff.rfl

#noalign stream.seq.omap

/-- Get the first element of a sequence -/
noncomputable def head (s : Seq' α) : Option α :=
  get? s 0
#align stream.seq.head Seq'.head

theorem get?_zero (s : Seq' α) : get? s 0 = head s :=
  rfl

/-- Get the tail of a sequence (or `nil` if the sequence is `nil`) -/
noncomputable def tail (s : Seq' α) : Seq' α where
  get? n := get? s (n + 1)
  succ_stable _ h := succ_stable s h
#align stream.seq.tail Seq'.tail

/-- member definition for `Seq`-/
protected def Mem (a : α) (s : Seq' α) :=
  ∃ n, get? s n = a
#align stream.seq.mem Seq'.Mem

instance : Membership α (Seq' α) :=
  ⟨Seq'.Mem⟩

theorem mem_def (a : α) (s : Seq' α) : a ∈ s ↔ ∃ n, get? s n = a :=
  Iff.rfl

theorem le_stable (s : Seq' α) {m n} (h : m ≤ n) : s.get? m = none → s.get? n = none := by
  cases' s with f al
  induction' h with n _ IH
  exacts [id, fun h2 => al (IH h2)]
#align stream.seq.le_stable Seq'.le_stable

/-- If a sequence terminated at position `n`, it also terminated at `m ≥ n`. -/
theorem terminated_stable : ∀ (s : Seq' α) {m n : ℕ}, m ≤ n → s.TerminatedAt m → s.TerminatedAt n :=
  le_stable
#align stream.seq.terminated_stable Seq'.terminated_stable

/-- If `s.get? n = some aₙ` for some value `aₙ`, then there is also some value `aₘ` such
that `s.get? = some aₘ` for `m ≤ n`.
-/
theorem ge_stable (s : Seq' α) {aₙ : α} {n m : ℕ} (m_le_n : m ≤ n)
    (s_get?_eq_some : s.get? n = some aₙ) : ∃ aₘ : α, s.get? m = some aₘ :=
  have : s.get? n ≠ none := by simp [s_get?_eq_some]
  have : s.get? m ≠ none := mt (s.le_stable m_le_n) this
  Option.ne_none_iff_exists'.mp this
#align stream.seq.ge_stable Seq'.ge_stable

@[simp]
theorem not_mem_nil (a : α) : a ∉ (nil : Seq' α) := fun ⟨_, (h : none = some a)⟩ => by injection h
#align stream.seq.not_mem_nil Seq'.not_mem_nil

theorem mem_cons (a : α) (s : Seq' α) : a ∈ a ::ₑ s :=
  ⟨0, rfl⟩
#align stream.seq.mem_cons Seq'.mem_cons

theorem mem_cons_of_mem (y : α) {a : α} {s : Seq' α} : a ∈ s → a ∈ y ::ₑ s
  | ⟨n, h⟩ => ⟨n + 1, h⟩
#align stream.seq.mem_cons_of_mem Seq'.mem_cons_of_mem

theorem eq_or_mem_of_mem_cons {a b : α} {s : Seq' α} : a ∈ b ::ₑ s → a = b ∨ a ∈ s
  | ⟨0, h⟩ => Or.inl (Option.some_injective _ h.symm)
  | ⟨n + 1, h⟩ => Or.inr ⟨n, h⟩
#align stream.seq.eq_or_mem_of_mem_cons Seq'.eq_or_mem_of_mem_cons

@[simp]
theorem mem_cons_iff {a b : α} {s : Seq' α} : a ∈ b ::ₑ s ↔ a = b ∨ a ∈ s :=
  ⟨eq_or_mem_of_mem_cons, by rintro (rfl | m) <;> [apply mem_cons; exact mem_cons_of_mem _ m]⟩
#align stream.seq.mem_cons_iff Seq'.mem_cons_iff

/-- Destructor for a sequence, resulting in either `none` (for `nil`) or
  `some (a, s)` (for `a ::ₑ s`). -/
@[inline]
unsafe def destUnsafe (s : Seq' α) : Option (α × Seq' α) :=
  unsafeCast (dest (unsafeCast s : LazyList α))

@[inherit_doc destUnsafe, implemented_by destUnsafe]
def dest (s : Seq' α) : Option (α × Seq' α) :=
  Option.map ((·, s.tail)) (head s)
#align stream.seq.destruct Seq'.dest

theorem dest_eq_nil {s : Seq' α} : dest s = none → s = nil := by
  dsimp [dest]
  induction' f0 : head s <;> intro h
  · ext1 n
    induction' n with n IH
    exacts [f0, s.2 IH]
  · contradiction
#align stream.seq.destruct_eq_nil Seq'.dest_eq_nil

theorem dest_eq_cons {s : Seq' α} {a s'} : dest s = some (a, s') → s = a ::ₑ s' := by
  dsimp [dest]
  induction' f0 : head s with a' <;> intro h
  · contradiction
  · cases' s with f hf
    injections _ h1 h2
    rw [← h2]
    ext1 n
    dsimp [tail, cons]
    rw [h1] at f0
    rw [← f0]
    cases n <;> rfl
#align stream.seq.destruct_eq_cons Seq'.dest_eq_cons

@[simp]
theorem dest_nil : dest (nil : Seq' α) = none :=
  rfl
#align stream.seq.destruct_nil Seq'.dest_nil

@[simp]
theorem dest_cons (a : α) (s) : dest (a ::ₑ s) = some (a, s) := by
  unfold cons dest
  apply congr_arg fun s => some (a, s)
  ext1 n; dsimp [tail]
#align stream.seq.destruct_cons Seq'.dest_cons

theorem head_eq_dest (s : Seq' α) : head s = Option.map Prod.fst (dest s) := by
  unfold dest; cases head s <;> rfl
#align stream.seq.head_eq_destruct Seq'.head_eq_dest

@[simp]
theorem head_nil : head (nil : Seq' α) = none :=
  rfl
#align stream.seq.head_nil Seq'.head_nil

@[simp]
theorem head_cons (a : α) (s) : head (a ::ₑ s) = some a := by
  rw [head_eq_dest, dest_cons, Option.map_some']
#align stream.seq.head_cons Seq'.head_cons

@[simp]
theorem tail_nil : tail (nil : Seq' α) = nil :=
  rfl
#align stream.seq.tail_nil Seq'.tail_nil

@[simp]
theorem tail_cons (a : α) (s) : tail (a ::ₑ s) = s := by
  cases' s with f al
  ext1 n
  dsimp [tail, cons]
#align stream.seq.tail_cons Seq'.tail_cons

theorem get?_succ (s : Seq' α) (n) : get? s (n + 1) = get? (tail s) n :=
  rfl
#align stream.seq.nth_tail Seq'.get?_succ

/-- Recursion principle for sequences, compare with `List.recOn`. -/
@[elab_as_elim]
def recOn' {C : Seq' α → Sort v} (s : Seq' α) (nil : C nil) (cons : ∀ x s, C (x ::ₑ s)) : C s :=
  match H : dest s with
  | none => cast (congr_arg C (dest_eq_nil H)).symm nil
  | some (a, s') => cast (congr_arg C (dest_eq_cons H)).symm (cons a s')
#align stream.seq.rec_on Seq'.recOn'

@[simp]
theorem recOn'_nil {C : Seq' α → Sort v} (nil : C nil) (cons : ∀ x s, C (x ::ₑ s)) :
    recOn' (C := C) Seq'.nil nil cons = nil :=
  rfl

@[simp]
theorem recOn'_cons {C : Seq' α → Sort v} (a : α) (s : Seq' α) (nil : C nil)
    (cons : ∀ x s, C (x ::ₑ s)) : recOn' (C := C) (a ::ₑ s) nil cons = cons a s :=
  rfl

theorem dest_injective : Injective (dest : Seq' α → Option (α × Seq' α)) := by
  intro s₁ s₂ hs
  cases s₂ using recOn' with
  | nil => rw [dest_nil] at hs; exact dest_eq_nil hs
  | cons a s₂ => rw [dest_cons] at hs; exact dest_eq_cons hs

@[elab_as_elim]
theorem mem_rec_on {a} {C : (s : Seq' α) → a ∈ s → Prop} {s} (M : a ∈ s)
    (mem_cons : ∀ s, C (a ::ₑ s) (mem_cons a s))
    (mem_cons_of_mem : ∀ (y) {s} (h : a ∈ s), C s h → C (y ::ₑ s) (mem_cons_of_mem y h)) :
    C s M := by
  cases M with
  | intro k e =>
    induction k generalizing s with
    | zero =>
      induction s using recOn' with
      | nil => injection e
      | cons b s' =>
        injection e with e'
        induction e'
        exact mem_cons s'
    | succ k IH =>
      induction s using recOn' with
      | nil => injection e
      | cons b s' =>
        rw [get?_cons_succ] at e
        exact mem_cons_of_mem b _ (IH e)
#align stream.seq.mem_rec_on Seq'.mem_rec_onₓ

def All (p : α → Prop) (s : Seq' α) :=
  ∃ (q : Seq' α → Prop), q s ∧
    ∀ {s}, q s → match dest s with | none => True | some (a, s) => p a ∧ q s

theorem all_iff (p : α → Prop) (s : Seq' α) : All p s ↔ ∀ a ∈ s, p a := by
  constructor
  · rintro ⟨q, hs, hq⟩ a ha
    induction ha using mem_rec_on with
    | mem_cons s =>
      exact (hq hs).1
    | @mem_cons_of_mem b s _ hs₂ =>
      exact hs₂ (hq hs).2
  · intro hs
    refine ⟨fun s => ∀ {a}, a ∈ s → p a, @(hs), ?_⟩
    intro s hs
    cases s using recOn' with
    | nil => constructor
    | cons a s => exact ⟨hs (mem_cons a s), fun {b} hb => hs (mem_cons_of_mem a hb)⟩

@[inherit_doc head]
def headComputable (s : Seq' α) : Option α :=
  Option.map Prod.fst (dest s)

@[csimp]
theorem head_eq_headComputable : @head.{u} = @headComputable.{u} := by
  funext α s
  rw [headComputable, head_eq_dest]

theorem tail_eq_dest (s : Seq' α) : tail s = Option.elim (dest s) nil Prod.snd := by
  cases s using recOn' <;> simp

@[inherit_doc tail]
def tailComputable (s : Seq' α) : Seq' α :=
  Option.elim (dest s) nil Prod.snd

@[csimp]
theorem tail_eq_tailComputable : @tail.{u} = @tailComputable.{u} := by
  funext α s
  rw [tailComputable, tail_eq_dest]

@[inherit_doc get?, simp]
def get?Computable (s : Seq' α) : ℕ → Option α
  | 0     => head s
  | n + 1 => Option.elim (dest s) none (fun (_, s) => get?Computable s n)

@[csimp]
theorem get?_eq_get?Computable : @get?.{u} = @get?Computable.{u} := by
  funext α s n
  induction n generalizing s with
  | zero => cases s using recOn' <;> simp
  | succ n hn => cases s using recOn' <;> simp [hn]

/-- The implemention of `Seq'.casesOn`. -/
@[inline]
protected def casesOnComputable {α : Type u} {motive : Seq' α → Sort*}
    (s : Seq' α)
    (mk : (get? : ℕ → Option α) →
      (succ_stable : ∀ ⦃n⦄, get? n = none → get? (n + 1) = none) →
      motive (mk get? succ_stable)) : motive s :=
  mk (get? s) (succ_stable s)

@[csimp]
theorem casesOn_eq_casesOnComputable :
    @Seq'.casesOn.{v, u} = @Seq'.casesOnComputable.{v, u} :=
  rfl

/-- It is decidable whether a sequence terminates at a given position. -/
instance terminatedAtDecidable (s : Seq' α) (n : ℕ) : Decidable (s.TerminatedAt n) :=
  decidable_of_iff' (s.get? n).isNone <| by unfold TerminatedAt; cases s.get? n <;> simp
#align stream.seq.terminated_at_decidable Seq'.terminatedAtDecidable

theorem not_terminatedAt_iff {s : Seq' α} {n : ℕ} : ¬s.TerminatedAt n ↔ (s.get? n).isSome := by
  simp only [TerminatedAt, ← Ne.eq_def, Option.ne_none_iff_isSome]

instance : GetElem (Seq' α) ℕ α (fun s n => ¬s.TerminatedAt n) where
  getElem s n h := Option.get (get? s n) (not_terminatedAt_iff.mp h)

@[simp]
theorem getElem?_eq_get? (s : Seq' α) (n : ℕ) : s[n]? = get? s n := by
  simp [getElem?, getElem, not_terminatedAt_iff, Option.isNone_iff_eq_none, eq_comm (a := none)]

theorem get?_eq_getElem {s : Seq' α} {n : ℕ} (h : ¬s.TerminatedAt n) : get? s n = some (s[n]'h) :=
  Option.some_get _ |>.symm

/-- A sequence terminates if there is some position `n` at which it has terminated. -/
def Terminates (s : Seq' α) : Prop :=
  ∃ n : ℕ, s.TerminatedAt n
#align stream.seq.terminates Seq'.Terminates

theorem terminates_of_terminatedAt {s : Seq' α} {n : ℕ} (h : s.TerminatedAt n) : s.Terminates :=
  Exists.intro n h

@[simp]
theorem nil_terminates : (nil : Seq' α).Terminates :=
  terminates_of_terminatedAt <| nil_terminatedAt 0

@[simp]
theorem cons_terminates {a : α} {s : Seq' α} : (a ::ₑ s).Terminates ↔ s.Terminates := by
  unfold Terminates; nth_rw 1 [← Nat.or_exists_succ]; simp

theorem terminates_iff_acc {s : Seq' α} :
    Terminates s ↔ Acc (fun s₁ s₂ => ∃ a, dest s₂ = some (a, s₁)) s := by
  constructor
  · intro hs; unfold Terminates TerminatedAt at hs
    rcases hs with ⟨n, hs⟩
    induction n generalizing s with
    | zero =>
      cases s using recOn' <;> simp at hs
      constructor; simp
    | succ n hn =>
      cases s using recOn' <;> simp at hs
      case nil => constructor; simp
      case cons a s => constructor; simp [hn hs]
  · intro hs
    induction hs with
    | intro s' hs'₂ hs' =>
      clear s hs'₂
      cases s' using recOn' with
      | nil => simp
      | cons a s' => simp [hs' s' ⟨a, rfl⟩]

theorem not_terminates_iff {s : Seq' α} : ¬s.Terminates ↔ ∀ n, (s.get? n).isSome := by
  simp only [Terminates, not_terminatedAt_iff, not_exists]
#align stream.seq.not_terminates_iff Seq'.not_terminates_iff

set_option linter.uppercaseLean3 false in
#noalign stream.seq.corec.F

/-- Corecursor for `Seq' α` as a coinductive type. Iterates `f` to produce new elements
  of the sequence until `none` is obtained. -/
unsafe def corecUnsafe (f : β → Option (α × β)) (b : β) : Seq' α :=
  unsafeCast (corec f b)

@[inherit_doc corecUnsafe, implemented_by corecUnsafe]
def corec (f : β → Option (α × β)) (b : β) : Seq' α where
  get? n := Option.map Prod.fst ((fun o => Option.bind o (f ∘ Prod.snd))^[n] (f b))
  succ_stable n h := by
    simp at h
    simp [iterate_succ', h, - iterate_succ]
#align stream.seq.corec Seq'.corec

@[simp]
theorem get?_corec (f : β → Option (α × β)) (b : β) (n : ℕ) :
    get? (corec f b) n = Option.map Prod.fst ((fun o => Option.bind o (f ∘ Prod.snd))^[n] (f b)) :=
  rfl

@[simp]
theorem dest_corec (f : β → Option (α × β)) (b : β) :
    dest (corec f b) = Option.map (Prod.map id (corec f)) (f b) := by
  rcases hb : f b with (_ | ⟨_, _⟩) <;> simp [corec, dest, head, tail, hb]
#align stream.seq.corec_eq Seq'.dest_corec

@[simp]
theorem head_corec (f : β → Option (α × β)) (b : β) :
    head (corec f b) = Option.map Prod.fst (f b) := by
  rcases hb : f b with (_ | ⟨_, _⟩) <;> simp [head_eq_dest, hb]

section Bisim

variable (R : Seq' α → Seq' α → Prop)

/-- Bisimilarity relation over `Option` of `α × Seq' α`-/
def BisimO : Option (α × Seq' α) → Option (α × Seq' α) → Prop
  | none, none => True
  | some (a, s), some (a', s') => a = a' ∧ R s s'
  | _, _ => False
#align stream.seq.bisim_o Seq'.BisimO

attribute [simp] BisimO

/-- a relation is bisimilar if it meets the `BisimO` test-/
def IsBisimulation :=
  ∀ ⦃s₁ s₂⦄, R s₁ s₂ → BisimO R (dest s₁) (dest s₂)
#align stream.seq.is_bisimulation Seq'.IsBisimulation

-- If two streams are bisimilar, then they are equal
theorem eq_of_bisim (bisim : IsBisimulation R) {s₁ s₂} (r : R s₁ s₂) : s₁ = s₂ := by
  ext1 n
  induction n generalizing s₁ s₂ with
  | zero =>
    specialize bisim r
    match hs₁ : dest s₁, hs₂ : dest s₂, bisim with
    | none, none, True.intro =>
      simp [dest_eq_nil hs₁, dest_eq_nil hs₂]
    | some (a₁, s₁'), some (a₂, s₂'), And.intro ha _ =>
      simp [dest_eq_cons hs₁, dest_eq_cons hs₂, ha]
  | succ n hn =>
    specialize bisim r
    match hs₁ : dest s₁, hs₂ : dest s₂, bisim with
    | none, none, True.intro =>
      simp [dest_eq_nil hs₁, dest_eq_nil hs₂]
    | some (a₁, s₁'), some (a₂, s₂'), And.intro ha hs' =>
      simp [dest_eq_cons hs₁, dest_eq_cons hs₂, ha, hn hs']
#align stream.seq.eq_of_bisim Seq'.eq_of_bisim

end Bisim

theorem coinduction {s₁ s₂ : Seq' α} (hh : head s₁ = head s₂)
    (ht : ∀ (β : Type u) (fr : Seq' α → β), fr s₁ = fr s₂ → fr (tail s₁) = fr (tail s₂)) :
    s₁ = s₂ :=
  eq_of_bisim
    (fun s₁ s₂ =>
      head s₁ = head s₂ ∧
        ∀ (β : Type u) (fr : Seq' α → β), fr s₁ = fr s₂ → fr (tail s₁) = fr (tail s₂))
    (by
      rintro s₁ s₂ ⟨hh, ht⟩
      cases s₁ using recOn' <;> cases s₂ using recOn' <;> simp at hh
      case nil.nil =>
        simp
      case cons.cons a₁ s₁ a₂ s₂ =>
        simp
        constructor
        · exact hh
        · constructor
          · specialize ht (Option α) head
            simp at ht
            exact ht hh
          · intro β fr
            specialize ht β (fr ∘ tail)
            simp at ht
            exact ht)
    ⟨hh, ht⟩
#align stream.seq.coinduction Seq'.coinduction

theorem coinduction2 (s) (f g : α → Seq' β)
    (H : ∀ s,
      BisimO (fun s₁ s₂ => ∃ s, s₁ = f s ∧ s₂ = g s)
        (dest (f s)) (dest (g s))) :
    f s = g s := by
  refine eq_of_bisim (fun s₁ s₂ => ∃ s, s₁ = f s ∧ s₂ = g s) ?_ ⟨s, rfl, rfl⟩
  intro s1 s2 h; rcases h with ⟨s, h1, h2⟩
  rw [h1, h2]; apply H
#align stream.seq.coinduction2 Seq'.coinduction2

@[inherit_doc mk, nolint unusedArguments, specialize, simp]
def mkComputable (f : ℕ → Option α) (_ : ∀ ⦃n⦄, f n = none → f (n + 1) = none) : Seq' α :=
  corec (fun n => Option.map ((·, n + 1)) (f n)) 0

@[csimp]
theorem mk_eq_mkComputable : @mk.{u} = @mkComputable.{u} := by
  funext α f hf
  ext1 n
  simp; symm
  induction n with
  | zero => cases f 0 <;> simp
  | succ n hn =>
    cases hfn : f n with
    | none =>
      simp [hfn] at hn
      simp [iterate_succ', hn, hf hfn, - iterate_succ]
    | some a =>
      clear hn
      simp [iterate_succ', hfn, - iterate_succ]
      suffices he :
          ((fun o ↦ o.bind (fun p ↦ Option.map (fun x ↦ (x, p.2 + 1)) (f p.2)))^[n]
            (Option.map (fun x ↦ (x, 1)) (f 0))) = some (a, n + 1) by
        simp [iterate_succ', he, hfn, - iterate_succ]
        cases f (n + 1) <;> simp
      induction n generalizing a with
      | zero => simp [hfn]
      | succ n hn =>
        cases hfn' : f n with
        | none => simp [hf hfn'] at hfn
        | some a =>
          simp [iterate_succ', hn a hfn', hfn, - iterate_succ]

/-- Embed a list as a sequence -/
@[coe]
def ofList : (l : List α) → Seq' α
  | [] => nil
  | a :: l => a ::ₑ ofList l
#align stream.seq.of_list Seq'.ofList

instance coeList : Coe (List α) (Seq' α) :=
  ⟨ofList⟩
#align stream.seq.coe_list Seq'.coeList

@[simp, norm_cast]
theorem ofList_nil : (↑([] : List α) : Seq' α) = nil :=
  rfl
#align stream.seq.of_list_nil Seq'.ofList_nil

@[simp, norm_cast]
theorem ofList_cons (a : α) (l : List α) : (↑(a :: l) : Seq' α) = a ::ₑ ↑l :=
  rfl
#align stream.seq.of_list_cons Seq'.ofList_cons

@[simp, norm_cast]
theorem get?_ofList (l : List α) (n : ℕ) : get? (↑l : Seq' α) n = List.get? l n := by
  induction l generalizing n with
  | nil => simp
  | cons a l hl =>
    cases n with
    | zero => simp
    | succ n => simp [hl]
#align stream.seq.of_list_nth Seq'.get?_ofList

theorem ofList_injective : Function.Injective ((↑) : List α → Seq' α) := by
  intro l₁ l₂ h
  ext1 n
  rw [← get?_ofList, ← get?_ofList, h]

@[simp, norm_cast]
theorem ofList_inj {l₁ l₂ : List α} : (↑l₁ : Seq' α) = ↑l₂ ↔ l₁ = l₂ :=
  ofList_injective.eq_iff

theorem ofList_terminatedAt_length (l : List α) : (↑l : Seq' α).TerminatedAt l.length := by
  simp [TerminatedAt]

@[simp]
theorem ofList_terminatedAt_iff {l : List α} {n : ℕ} :
    (↑l : Seq' α).TerminatedAt n ↔ l.length ≤ n := by
  rw [TerminatedAt, get?_ofList, List.get?_eq_none]

@[simp]
theorem ofList_terminates (l : List α) : (↑l : Seq' α).Terminates :=
  Exists.intro l.length <| ofList_terminatedAt_length l

/-- Embed an infinite stream as a sequence -/
@[coe]
def ofStream (s : Stream' α) : Seq' α :=
  corec (some ∘ Stream'.dest) s
#align stream.seq.of_stream Seq'.ofStream

instance coeStream : Coe (Stream' α) (Seq' α) :=
  ⟨ofStream⟩
#align stream.seq.coe_stream Seq'.coeStream

@[simp]
theorem dest_ofStream (s : Stream' α) :
    dest (↑s : Seq' α) = some (Stream'.head s, ↑(Stream'.tail s)) := by
  simp [ofStream]

@[simp]
theorem head_ofStream (s : Stream' α) : head (↑s : Seq' α) = some (Stream'.head s) := by
  simp [ofStream]

@[simp]
theorem tail_ofStream (s : Stream' α) : tail (↑s : Seq' α) = ↑(Stream'.tail s) := by
  simp [tail_eq_dest, ofStream]

@[simp, norm_cast]
theorem ofStream_get? (s : Stream' α) (n : ℕ) : (↑s : Seq' α).get? n = some (s.get n) := by
  induction n generalizing s with
  | zero => simp [Stream'.get_zero, get?_zero]
  | succ n hn => simp [Stream'.get_succ, get?_succ, hn]

theorem ofStream_injective : Function.Injective ((↑) : Stream' α → Seq' α) := by
  intro s₁ s₂ h
  ext1 n
  rw [← Option.some_inj, ← ofStream_get?, ← ofStream_get?, h]

@[simp, norm_cast]
theorem ofStream_inj {s₁ s₂ : Stream' α} : (↑s₁ : Seq' α) = ↑s₂ ↔ s₁ = s₂ :=
  ofStream_injective.eq_iff

@[simp]
theorem not_ofStream_terminatedAt (s : Stream' α) (n : ℕ) : ¬(↑s : Seq' α).TerminatedAt n := by
  simp [TerminatedAt]

@[simp]
theorem not_ofStream_terminates (s : Stream' α) : ¬(↑s : Seq' α).Terminates :=
  fun ⟨n, h⟩ => not_ofStream_terminatedAt s n h

/-- Embed a `LazyList α` as a sequence. Note that even though this
  is non-meta, it will produce infinite sequences if used with
  cyclic `LazyList`s created by meta constructions. -/
unsafe def ofLazyListUnsafe : LazyList α → Seq' α :=
  unsafeCast

@[inherit_doc ofLazyListUnsafe, implemented_by ofLazyListUnsafe]
def ofLazyList : LazyList α → Seq' α :=
  corec fun
        | LazyList.nil => none
        | LazyList.cons a l' => some (a, l'.get)
#align stream.seq.of_lazy_list Seq'.ofLazyList

instance coeLazyList : Coe (LazyList α) (Seq' α) :=
  ⟨ofLazyList⟩
#align stream.seq.coe_lazy_list Seq'.coeLazyList

/-- Translate a sequence into a `LazyList`. Since `LazyList` and `List`
  are isomorphic as non-meta types, this function is necessarily meta. -/
unsafe def toLazyList : Seq' α → LazyList α :=
  unsafeCast
#align stream.seq.to_lazy_list Seq'.toLazyList

/-- Translate a sequence to a list. This function will run forever if
  run on an infinite sequence. -/
unsafe def forceToList (s : Seq' α) : List α :=
  (toLazyList s).toList
#align stream.seq.force_to_list Seq'.forceToList


#align stream.seq.nats Stream'.nats

#align stream.seq.nats_nth Stream'.get_nats

/-- Corecursor where it is possible to return a fully formed value at any point of the
computation. -/
@[inline]
unsafe def corec'Unsafe (f : β → Seq' α ⊕ Option (α × β)) (b : β) : Seq' α :=
  unsafeCast (corec' (unsafeCast f) b : LazyList α)

@[inherit_doc corec'Unsafe, implemented_by corec'Unsafe]
def corec' (f : β → Seq' α ⊕ Option (α × β)) (b : β) : Seq' α :=
  corec
    (Sum.elim (Option.map (Prod.map id Sum.inl) ∘ dest) (Option.map (Prod.map id Sum.inr)) ∘
      Sum.elim Sum.inl f)
    (Sum.inr b)

@[simp]
theorem dest_corec' (f : β → Seq' α ⊕ Option (α × β)) (b : β) :
    dest (corec' f b) = Sum.elim dest (Option.map (Prod.map id (corec' f))) (f b) := by
  simp (config := { unfoldPartialApp := true }) [corec']
  rcases f b with (s | _ | ⟨a, b⟩) <;> simp
  rcases dest s with (_ | ⟨a, s'⟩) <;> simp; clear s
  refine eq_of_bisim
    (fun s₁ s₂ =>
      s₁ = corec
        (Sum.elim (Option.map (Prod.map id Sum.inl) ∘ dest) (Option.map (Prod.map id Sum.inr)) ∘
          Sum.elim Sum.inl f)
        (Sum.inl s₂))
    ?_ rfl; clear s'
  rintro _ s rfl
  simp; rcases dest s with (_ | ⟨_, _⟩) <;> simp

/-- Map a function over a sequence. -/
def map (f : α → β) (s : Seq' α) : Seq' β where
  get? n := Option.map f (get? s n)
  succ_stable n h := by
    simp at h
    simp [succ_stable s h]
#align stream.seq.map Seq'.map

@[simp]
theorem map_get? (f : α → β) (s n) : get? (map f s) n = Option.map f (get? s n) :=
  rfl
#align stream.seq.map_nth Seq'.map_get?

@[simp]
theorem map_nil (f : α → β) : map f nil = nil :=
  rfl
#align stream.seq.map_nil Seq'.map_nil

@[simp]
theorem map_cons (f : α → β) (a s) : map f (a ::ₑ s) = f a ::ₑ map f s := by
  ext1 (_ | _) <;> rfl
#align stream.seq.map_cons Seq'.map_cons

@[simp]
theorem map_id (s : Seq' α) : map id s = s := by
  ext1 _; simp
#align stream.seq.map_id Seq'.map_id

@[simp]
theorem head_map (f : α → β) (s) : head (map f s) = Option.map f (head s) :=
  rfl

@[simp]
theorem tail_map (f : α → β) (s) : tail (map f s) = map f (tail s) :=
  rfl
#align stream.seq.map_tail Seq'.tail_map

@[simp]
theorem dest_map (f : α → β) (s) : dest (map f s) = Option.map (Prod.map f (map f)) (dest s) := by
  cases s using recOn' <;> simp

@[simp]
theorem map_map (g : β → γ) (f : α → β) (s : Seq' α) : map g (map f s) = map (g ∘ f) s := by
  ext1 _; simp
#align stream.seq.map_comp Seq'.map_map

@[simp]
theorem map_terminatedAt (f : α → β) (s n) : (map f s).TerminatedAt n ↔ s.TerminatedAt n := by
  simp [TerminatedAt]

@[simp]
theorem map_terminates (f : α → β) (s) : (map f s).Terminates ↔ s.Terminates := by
  simp [Terminates]

@[inherit_doc map, inline]
def mapComputable (f : α → β) (s : Seq' α) : Seq' β :=
  corec (Option.map (Prod.map f id) ∘ dest) s

@[csimp]
theorem map_eq_mapComputable : @map.{u, v} = @mapComputable.{u, v} := by
  funext α β f s
  refine eq_of_bisim
    (fun s₁ s₂ => ∃ s, s₁ = map f s ∧ s₂ = corec (Option.map (Prod.map f id) ∘ dest) s)
    ?_ ⟨s, rfl, rfl⟩; clear s
  rintro _ _ ⟨s, rfl, rfl⟩
  cases s using recOn' <;> simp
  next _ s => exists s

/-- Flatten a sequence of sequences. (It is required that the
  sequences be nonempty to ensure productivity; in the case
  of an infinite sequence of `nil`, the first element is never
  generated.) -/
def join : Seq' (Seq1 α) → Seq' α :=
  corec fun S =>
    match dest S with
    | none => none
    | some (⟨a, s⟩, S') =>
      some
        (a,
          match dest s with
          | none => S'
          | some (b, s') => ⟨b, s'⟩ ::ₑ S')
#align stream.seq.join Seq'.join

/-- Remove the first `n` elements from the sequence. -/
@[simp]
def drop : ℕ → Seq' α → Seq' α
  | 0    , s => s
  | n + 1, s => drop n (tail s)
#align stream.seq.drop Seq'.dropₓ

@[simp]
theorem drop_nil : ∀ n, drop n (nil : Seq' α) = nil
  | 0     => rfl
  | n + 1 => by rw [drop, tail_nil, drop_nil n]

theorem drop_add (m) : ∀ (n) (s : Seq' α), drop (m + n) s = drop m (drop n s)
  | 0    , _ => rfl
  | n + 1, s => drop_add m n (tail s)
#align stream.seq.dropn_add Seq'.drop_addₓ

theorem tail_drop (n) (s : Seq' α) : tail (drop n s) = drop (n + 1) s := by
  rw [add_comm]; symm; apply drop_add
#align stream.seq.dropn_tail Seq'.tail_dropₓ

@[simp]
theorem head_drop (n) (s : Seq' α) : head (drop n s) = get? s n := by
  induction' n with n IH generalizing s; · rfl
  rw [get?_succ, drop]; apply IH
#align stream.seq.head_dropn Seq'.head_dropₓ

/-- Take the first `n` elements of the sequence (producing a list) -/
def take : ℕ → Seq' α → List α
  | 0    , _ => []
  | n + 1, s =>
    match dest s with
    | none => []
    | some (x, r) => x :: take n r
#align stream.seq.take Seq'.take

@[simp]
theorem take_zero (s : Seq' α) : take 0 s = [] :=
  rfl

@[simp]
theorem take_succ_cons (n : ℕ) (a : α) (s : Seq' α) : take (n + 1) (a ::ₑ s) = a :: take n s :=
  rfl

@[simp]
theorem take_nil (n : ℕ) : take n (nil : Seq' α) = [] := by
  cases n <;> rfl

/-- Tail recursive version of `take`. -/
@[inline, simp]
def takeTR (n : ℕ) (s : Seq' α) : List α :=
  go s n #[]
where
  /-- Auxiliary for `takeTR`: `takeTR.go s n acc = Array.data acc ++ take n s`. -/
  @[specialize, simp]
  go (s : Seq' α) (n : ℕ) (acc : Array α) : List α :=
    match n with
    | 0     => Array.data acc
    | n + 1 =>
      match dest s with
      | none => Array.data acc
      | some (a, s) => go s n (Array.push acc a)

@[csimp] theorem take_eq_takeTR : @take = @takeTR := by
  funext α n s
  suffices ∀ acc, takeTR.go s n acc = acc.data ++ take n s from
    (this #[]).symm
  intro acc
  induction n generalizing s acc with
  | zero => simp
  | succ n hn => cases s using recOn' <;> simp [hn]

@[simp]
theorem get?_take :
    ∀ (m n : ℕ) (s : Seq' α), List.get? (take n s) m = if m < n then get? s m else none
  | 0     , 0     , s => rfl
  | 0     , n' + 1, s => by
    cases s using recOn' <;> simp
  | m' + 1, 0     , s => rfl
  | m' + 1, n' + 1, s => by
    cases s using recOn' with
    | nil       => simp
    | cons a s' => simp [get?_take m' n' s']

theorem take_stable {s : Seq' α} {m n} (hs : s.TerminatedAt m) (hmn : m ≤ n) :
    take n s = take m s := by
  ext1 k
  by_cases hk : k < m
  case pos => simp [hk, lt_of_lt_of_le hk hmn]
  case neg => simp [hk, le_stable s (not_lt.mp hk) hs]

@[simp]
theorem take_map (n : ℕ) (f : α → β) (s : Seq' α) : take n (map f s) = List.map f (take n s) := by
  ext1 m
  by_cases hm : m < n <;> simp [hm]

theorem take_succ (n : ℕ) (s : Seq' α) :
    take (n + 1) s = take n s ++ Option.toList (get? s n) := by
  induction n generalizing s with
  | zero => cases s using recOn' <;> simp [get?_zero]
  | succ n hn => cases s using recOn' <;> simp [get?_succ, ↓take_succ_cons, hn]

/-- Split a sequence at `n`, producing a finite initial segment
  and an infinite tail. -/
def splitAt : ℕ → Seq' α → List α × Seq' α
  | 0, s => ([], s)
  | n + 1, s =>
    match dest s with
    | none => ([], nil)
    | some (x, s') =>
      let (l, r) := splitAt n s'
      (x :: l, r)
#align stream.seq.split_at Seq'.splitAt

@[simp]
theorem splitAt_eq_take_drop : ∀ (n : ℕ) (s : Seq' α), splitAt n s = (take n s, drop n s)
  | 0    , s => rfl
  | n + 1, s => by
    simp [splitAt, take]
    induction s using recOn' with
    | nil       => simp
    | cons a s' => simp [splitAt_eq_take_drop n s']

section ZipWith

/-- Combine two sequences with a function -/
def zipWith (f : α → β → γ) (s₁ : Seq' α) (s₂ : Seq' β) : Seq' γ where
  get? n := Option.map₂ f (get? s₁ n) (get? s₂ n)
  succ_stable n h := by
    simp at h
    cases h with
    | inl h => simp [succ_stable s₁ h]
    | inr h => simp [succ_stable s₂ h]
#align stream.seq.zip_with Seq'.zipWith

@[simp]
theorem get?_zipWith (f : α → β → γ) (s s' n) :
    get? (zipWith f s s') n = Option.map₂ f (get? s n) (get? s' n) :=
  rfl
#align stream.seq.nth_zip_with Seq'.get?_zipWith

@[simp]
theorem head_zipWith (f : α → β → γ) (s s') :
    head (zipWith f s s') = Option.map₂ f (head s) (head s') :=
  rfl

@[simp]
theorem tail_zipWith (f : α → β → γ) (s s') :
    tail (zipWith f s s') = zipWith f (tail s) (tail s') :=
  rfl

@[simp]
theorem zipWith_nil_left (f : α → β → γ) (s') : zipWith f nil s' = nil := by
  ext1; simp

@[simp]
theorem zipWith_nil_right (f : α → β → γ) (s) : zipWith f s nil = nil := by
  ext1; simp

@[simp]
theorem zipWith_cons (f : α → β → γ) (a s b s') :
    zipWith f (a ::ₑ s) (b ::ₑ s') = f a b ::ₑ zipWith f s s' := by
  ext1 (_ | _) <;> simp

@[simp]
theorem dest_zipWith (f : α → β → γ) (s s') :
    dest (zipWith f s s') =
      Option.map₂ (fun (a, s) (b, s') => (f a b, zipWith f s s')) (dest s) (dest s') := by
  cases s using recOn' <;> cases s' using recOn' <;> simp

end ZipWith

@[inherit_doc zipWith, inline]
def zipWithComputable (f : α → β → γ) (s₁ : Seq' α) (s₂ : Seq' β) : Seq' γ :=
  corec (fun (s₁, s₂) =>
      Option.map₂ (fun (a, s) (b, s') => (f a b, (s, s'))) (dest s₁) (dest s₂))
    (s₁, s₂)

@[csimp]
theorem zipWith_eq_zipWithComputable : @zipWith.{u, v, w} = @zipWithComputable.{u, v, w} := by
  funext α β γ f s₁ s₂
  refine eq_of_bisim
    (fun s₁ s₂ => ∃ s₃ s₄, s₁ = zipWith f s₃ s₄ ∧
      s₂ = corec (fun (s₁, s₂) =>
          Option.map₂ (fun (a, s) (b, s') => (f a b, (s, s'))) (dest s₁) (dest s₂))
        (s₃, s₄))
    ?_ ⟨s₁, s₂, rfl, rfl⟩; clear s₁ s₂
  rintro _ _ ⟨s₁, s₂, rfl, rfl⟩
  cases s₁ using recOn' <;> cases s₂ using recOn' <;> simp
  next _ s₁ _ s₂ => exists s₁, s₂

/-- Pair two sequences into a sequence of pairs -/
def zip : Seq' α → Seq' β → Seq' (α × β) :=
  zipWith Prod.mk
#align stream.seq.zip Seq'.zip

@[simp]
theorem get?_zip (s : Seq' α) (t : Seq' β) (n : ℕ) :
    get? (zip s t) n = Option.map₂ Prod.mk (get? s n) (get? t n) :=
  get?_zipWith _ _ _ _
#align stream.seq.nth_zip Seq'.get?_zip

@[simp]
theorem head_zip (s : Seq' α) (s' : Seq' β) :
    head (zip s s') = Option.map₂ Prod.mk (head s) (head s') :=
  head_zipWith _ _ _

@[simp]
theorem tail_zip (s : Seq' α) (s' : Seq' β) :
    tail (zip s s') = zip (tail s) (tail s') :=
  tail_zipWith _ _ _

@[simp]
theorem zip_nil_left (s' : Seq' β) : zip (nil : Seq' α) s' = nil :=
  zipWith_nil_left _ _

@[simp]
theorem zip_nil_right (s : Seq' α) : zip s (nil : Seq' β) = nil :=
  zipWith_nil_right _ _

@[simp]
theorem zip_cons (a : α) (s : Seq' α) (b : β) (s' : Seq' β) :
    zip (a ::ₑ s) (b ::ₑ s') = (a, b) ::ₑ zip s s' :=
  zipWith_cons _ _ _ _ _

@[simp]
theorem dest_zip  (s : Seq' α) (s' : Seq' β) :
    dest (zip s s') =
      Option.map₂ (fun (a, s) (b, s') => ((a, b), zip s s')) (dest s) (dest s') :=
  dest_zipWith _ _ _

/-- Like `enum` but it allows you to specify the initial index. -/
def enumFrom (n : ℕ) (s : Seq' α) : Seq' (ℕ × α) :=
  Seq'.zip ↑(Stream'.iota n) s

/-- Enumerate a sequence by tagging each element with its index. -/
def enum (s : Seq' α) : Seq' (ℕ × α) :=
  enumFrom 0 s
#align stream.seq.enum Seq'.enum

@[simp]
theorem get?_enumFrom (m : ℕ) (s : Seq' α) (n : ℕ) :
    get? (enumFrom m s) n = Option.map (Prod.mk (m + n)) (get? s n) := by
  simp [enumFrom]

@[simp]
theorem get?_enum (s : Seq' α) (n : ℕ) : get? (enum s) n = Option.map (Prod.mk n) (get? s n) := by
  simp [enum]
#align stream.seq.nth_enum Seq'.get?_enum

@[simp]
theorem enumFrom_nil (n : ℕ) : enumFrom n (nil : Seq' α) = nil := by
  simp [enumFrom]

@[simp]
theorem enum_nil : enum (nil : Seq' α) = nil := by
  simp [enum]
#align stream.seq.enum_nil Seq'.enum_nil

/-- Separate a sequence of pairs into two sequences -/
def unzip (s : Seq' (α × β)) : Seq' α × Seq' β :=
  (map Prod.fst s, map Prod.snd s)
#align stream.seq.unzip Seq'.unzip

/-- Convert a sequence which is known to terminate into a list -/
def toList (s : Seq' α) (hs : s.Terminates) : List α :=
  take (Nat.find hs) s
#align stream.seq.to_list Seq'.toList

@[simp]
theorem get?_toList {s : Seq' α} (hs : s.Terminates) (n : ℕ) :
    List.get? (toList s hs) n = get? s n := by
  simp [toList]
  intro m hmn ht
  symm; exact Seq'.terminated_stable s hmn ht

@[simp]
theorem toList_nil (hn : (nil : Seq' α).Terminates) : toList nil hn = [] := by
  ext1; simp

@[simp]
theorem toList_cons {a : α} {s : Seq' α} (has : (a ::ₑ s).Terminates) :
    toList (a ::ₑ s) has = a :: toList s (cons_terminates.mp has) := by
  ext1 (_ | _) <;> simp

@[simp, norm_cast]
theorem toList_ofList {l : List α} (hl : (↑l : Seq' α).Terminates) : toList ↑l hl = l := by
  ext1 n; rw [get?_toList, get?_ofList]

@[simp, norm_cast]
theorem ofList_toList {s : Seq' α} (hs : s.Terminates) : (toList s hs : List α) = s := by
  ext1 n; rw [get?_ofList, get?_toList]

@[simp]
theorem mem_ofList {a : α} {l : List α} : a ∈ (↑l : Seq' α) ↔ a ∈ l := by
  rw [mem_def, List.mem_iff_get?]; simp

/-- Corecursive verseion of `toList`. -/
@[inline, simp]
def toListCorec (s : Seq' α) (hs : s.Terminates) : List α :=
  loop (terminates_iff_acc.mp hs) #[]
where
  /-- The mail loop for `toListCorec`. -/
  loop {s : Seq' α} (hs : Acc (fun s₁ s₂ => ∃ a, dest s₂ = some (a, s₁)) s) (ar : Array α) :
      List α :=
    Acc.rec
      (fun s _ F ar =>
        match hs : dest s with
        | none => Array.data ar
        | some (a, s) => F s ⟨a, hs⟩ (Array.push ar a))
      hs ar

theorem toListCorec.loop_intro {s : Seq' α}
    (hs : ∀ s', (∃ a, dest s = some (a, s')) →
      Acc (fun s₁ s₂ => ∃ a, dest s₂ = some (a, s₁)) s') (ar : Array α) :
    loop (Acc.intro s hs) ar =
      match hs' : dest s with
      | none => Array.data ar
      | some (a, s) => loop (hs s ⟨a, hs'⟩) (Array.push ar a) :=
  rfl

theorem toListCorec.loop_eq {s : Seq' α}
    (hs : Acc (fun s₁ s₂ => ∃ a, dest s₂ = some (a, s₁)) s) (ar : Array α) :
    loop hs ar =
      Array.data ar ++ toList s (terminates_iff_acc.mpr hs) := by
  induction hs generalizing ar with
  | intro s hh hs =>
    rw [toListCorec.loop_intro hh]
    split
    next hn =>
      replace hn := dest_eq_nil hn; subst hn
      simp
    next a s' hs' =>
      replace hs' := dest_eq_cons hs'; subst hs'
      simp [hs]

@[csimp]
theorem toList_eq_toListCorec : @toList.{u} = @toListCorec.{u} := by
  funext α s hs
  simp [toListCorec.loop_eq]

instance : CanLift (Seq' α) (List α) (↑) (·.Terminates) where
  prf s h := ⟨toList s h, ofList_toList h⟩

/-- Convert a sequence which is known not to terminate into a stream -/
def toStream (s : Seq' α) (hs : ¬s.Terminates) : Stream' α :=
  Stream'.corec' (α := { s : Seq' α // ¬s.Terminates })
    (fun ⟨s, hs⟩ =>
      recOn' s (absurd nil_terminates)
        (fun a s' has' => (a, ⟨s', mt cons_terminates.mpr has'⟩))
        hs)
    ⟨s, hs⟩
#align stream.seq.to_stream Seq'.toStream

@[simp]
theorem get_toStream {s : Seq' α} (hs : ¬s.Terminates) (n : ℕ) :
    Stream'.get (toStream s hs) n = Option.get (get? s n) (not_terminates_iff.mp hs n) := by
  induction n generalizing s hs with
  | zero =>
    cases s using recOn' with
    | nil       => simp at hs
    | cons a s' => simp [Stream'.get_zero, toStream]
  | succ n hn =>
    cases s using recOn' with
    | nil       => simp at hs
    | cons a s' =>
      simp [toStream]
      apply hn

@[simp, norm_cast]
theorem toStream_ofStream {s : Stream' α} (h : ¬(↑s : Seq' α).Terminates) : toStream ↑s h = s := by
  ext1 n; simp

@[simp, norm_cast]
theorem ofStream_toStream {s : Seq' α} (h : ¬s.Terminates) : (toStream s h : Seq' α) = s := by
  ext1 n; rw [ofStream_get?, get_toStream, Option.some_get]

@[simp]
theorem mem_ofStream {a : α} {s : Stream' α} : a ∈ (↑s : Seq' α) ↔ a ∈ s := by
  rw [mem_def, Stream'.mem_def, Stream'.any_def]; simp [eq_comm (a := a)]

instance : CanLift (Seq' α) (Stream' α) (↑) (¬·.Terminates) where
  prf s h := ⟨toStream s h, ofStream_toStream h⟩

/-- Convert a sequence into either a list or a stream depending on whether
  it is finite or infinite. (Without decidability of the infiniteness predicate,
  this is not constructively possible.) -/
@[simp]
def toListOrStream (s : Seq' α) [Decidable s.Terminates] : List α ⊕ Stream' α :=
  if h : s.Terminates then Sum.inl (toList s h) else Sum.inr (toStream s h)
#align stream.seq.to_list_or_stream Seq'.toListOrStream

open Classical in
/-- `Seq' α` is (noncomputably) equivalent to `List α ⊕ Stream' α` -/
@[simps]
noncomputable def _root_.Equiv.seqEquivListSumStream : Seq' α ≃ List α ⊕ Stream' α where
  toFun s := toListOrStream s
  invFun := Sum.elim (↑) (↑)
  left_inv s := by by_cases h : s.Terminates <;> simp [h]
  right_inv s := by cases s <;> simp

/-- Append two sequences. If `s₁` is infinite, then `s₁ ++ s₂ = s₁`,
  otherwise it puts `s₂` at the location of the `nil` in `s₁`. -/
def append (s₁ s₂ : Seq' α) : Seq' α :=
  corec' (fun s => Option.elim (dest s) (Sum.inl s₂) (Sum.inr ∘ some)) s₁
#align stream.seq.append Seq'.append

instance : Append (Seq' α) where
  append := append

theorem append_def (s₁ s₂ : Seq' α) :
    s₁ ++ s₂ = corec' (fun s => Option.elim (dest s) (Sum.inl s₂) (Sum.inr ∘ some)) s₁ :=
  rfl

@[simp]
theorem nil_append (s : Seq' α) : nil ++ s = s := by
  apply dest_injective
  simp [append_def]
#align stream.seq.nil_append Seq'.nil_append

@[simp]
theorem cons_append (a : α) (s t) : a ::ₑ s ++ t = a ::ₑ (s ++ t) := by
  apply dest_eq_cons
  simp [append_def]
#align stream.seq.cons_append Seq'.cons_append

@[simp]
theorem append_nil (s : Seq' α) : s ++ nil = s := by
  apply coinduction2 s; intro s
  induction s using recOn' <;> simp
#align stream.seq.append_nil Seq'.append_nil

@[simp]
theorem append_assoc (s t u : Seq' α) : s ++ t ++ u = s ++ (t ++ u) := by
  apply eq_of_bisim fun s1 s2 => ∃ s t u, s1 = s ++ t ++ u ∧ s2 = s ++ (t ++ u)
  · intro s1 s2 h
    exact
      match s1, s2, h with
      | _, _, ⟨s, t, u, rfl, rfl⟩ => by
        induction' s using recOn' with _ s <;> simp
        · induction' t using recOn' with _ t <;> simp
          · induction' u using recOn' with _ u <;> simp
            · refine' ⟨nil, nil, u, _, _⟩ <;> simp
          · refine' ⟨nil, t, u, _, _⟩ <;> simp
        · exact ⟨s, t, u, rfl, rfl⟩
  · exact ⟨s, t, u, rfl, rfl⟩
#align stream.seq.append_assoc Seq'.append_assoc

@[simp]
theorem map_id' (s : Seq' α) : map (fun a => a) s = s := map_id s

theorem map_injective {f : α → β} (hf : Function.Injective f) : Function.Injective (map f) := by
  intro s₁ s₂ hs
  ext1 n
  replace hs := congr_arg (fun s => get? s n) hs
  simp only [map_get?] at hs
  exact Option.map_injective hf hs

@[simp]
theorem map_append (f : α → β) (s t) : map f (s ++ t) = map f s ++ map f t := by
  apply
    eq_of_bisim (fun s1 s2 => ∃ s t, s1 = map f (s ++ t) ∧ s2 = map f s ++ map f t) _
      ⟨s, t, rfl, rfl⟩
  intro s1 s2 h
  exact
    match s1, s2, h with
    | _, _, ⟨s, t, rfl, rfl⟩ => by
      induction' s using recOn' with _ s <;> simp
      · induction' t using recOn' with _ t <;> simp
        refine' ⟨nil, t, _, _⟩ <;> simp
      · exact ⟨s, t, rfl, rfl⟩
#align stream.seq.map_append Seq'.map_append

instance : Functor Seq' where map := @map

theorem map_congr {f g : α → β} {s : Seq' α} : (∀ a ∈ s, f a = g a) → map f s = map g s :=
  fun h => Seq'.ext fun n => Option.map_congr (fun a ha => h a ⟨n, ha⟩)

instance : LawfulFunctor Seq' where
  id_map := @map_id
  comp_map _ _ _ := Eq.symm (map_map _ _ _)
  map_const := rfl

@[simp]
theorem map_eq_map {α β : Type u} (f : α → β) : Functor.map f = map f :=
  rfl

@[simp, norm_cast]
theorem ofList_map (f : α → β) (l : List α) : (↑(List.map f l) : Seq' β) = map f ↑l := by
  ext1 n; simp

@[simp, norm_cast]
theorem ofStream_map (f : α → β) (s : Stream' α) : (↑(Stream'.map f s) : Seq' β) = map f ↑s := by
  ext1 n; simp

@[simp]
theorem join_nil : join nil = (nil : Seq' α) :=
  dest_eq_nil rfl
#align stream.seq.join_nil Seq'.join_nil

--@[simp] -- Porting note: simp can prove: `join_cons` is more general
theorem join_cons_nil (a : α) (S) : join (⟨a, nil⟩ ::ₑ S) = a ::ₑ join S :=
  dest_eq_cons <| by simp [join]
#align stream.seq.join_cons_nil Seq'.join_cons_nil

--@[simp] -- Porting note: simp can prove: `join_cons` is more general
theorem join_cons_cons (a b : α) (s S) :
    join (⟨a, b ::ₑ s⟩ ::ₑ S) = a ::ₑ join (⟨b, s⟩ ::ₑ S) :=
  dest_eq_cons <| by simp [join]
#align stream.seq.join_cons_cons Seq'.join_cons_cons

@[simp]
theorem join_cons (a : α) (s S) : join (⟨a, s⟩ ::ₑ S) = a ::ₑ (s ++ (join S)) := by
  apply
    eq_of_bisim
      (fun s1 s2 => s1 = s2 ∨ ∃ a s S, s1 = join (⟨a, s⟩ ::ₑ S) ∧ s2 = a ::ₑ (s ++ (join S)))
      _ (Or.inr ⟨a, s, S, rfl, rfl⟩)
  intro s1 s2 h
  exact
    match s1, s2, h with
    | s, _, Or.inl <| Eq.refl s => by
      induction s using recOn' <;> simp
    | _, _, Or.inr ⟨a, s, S, rfl, rfl⟩ => by
      induction s using recOn' with
      | nil =>
        simp [join_cons_cons, join_cons_nil]
      | cons x s =>
        simp [join_cons_cons, join_cons_nil]
        refine' Or.inr ⟨x, s, S, rfl, rfl, rfl⟩
#align stream.seq.join_cons Seq'.join_cons

@[simp]
theorem join_append (S T : Seq' (Seq1 α)) : join (S ++ T) = join S ++ join T := by
  apply
    eq_of_bisim fun s1 s2 =>
      ∃ s S T, s1 = s ++ join (S ++ T) ∧ s2 = s ++ (join S ++ join T)
  · intro s1 s2 h
    exact
      match s1, s2, h with
      | _, _, ⟨s, S, T, rfl, rfl⟩ => by
        induction' s using recOn' with _ s <;> simp
        · induction' S using recOn' with s S <;> simp
          · induction' T using recOn' with s T
            · simp
            · cases' s with a s; simp only [join_cons, dest_cons, true_and]
              refine' ⟨s, nil, T, _, _⟩ <;> simp
          · cases' s with a s
            simpa using ⟨s, S, T, rfl, rfl⟩
        · exact ⟨s, S, T, rfl, rfl⟩
  · refine' ⟨nil, S, T, _, _⟩ <;> simp
#align stream.seq.join_append Seq'.join_append

@[simp, norm_cast]
theorem ofStream_cons (a : α) (s) : (↑(a ::ₛ s) : Seq' α) = a ::ₑ ↑s := by
  ext1 (_ | _) <;> rfl
#align stream.seq.of_stream_cons Seq'.ofStream_cons

@[simp, norm_cast]
theorem ofList_append (l l' : List α) : (↑(l ++ l' : List α) : Seq' α) = (↑l : Seq' α) ++ ↑l' := by
  induction l <;> simp [*]
#align stream.seq.of_list_append Seq'.ofList_append

@[simp, norm_cast]
theorem ofStream_append (l : List α) (s : Stream' α) :
    (↑(l ++ s : Stream' α) : Seq' α) = (↑l : Seq' α) ++ ↑s := by
  induction l <;> simp [*, Stream'.nil_append, Stream'.cons_append]
#align stream.seq.of_stream_append Seq'.ofStream_append

/-- Convert a sequence into a list, embedded in a computation to allow for
  the possibility of infinite sequences (in which case the computation
  never returns anything). -/
def toList' {α} (s : Seq' α) : Computation (List α) :=
  Computation.corec
    (fun (l, s) =>
      match dest s with
      | none => Sum.inl l.reverse
      | some (a, s') => Sum.inr (a :: l, s'))
    ([], s)
#align stream.seq.to_list' Seq'.toList'

/-- Embed a sequence into a stream. -/
def toStream' : (s : Seq' α) → Stream' (Option α) :=
  Stream'.corec''
    (fun s =>
      match dest s with
      | none => Sum.inl (Stream'.const none)
      | some (a, s) => Sum.inr (some a, s))

@[simp]
theorem head_toStream' (s : Seq' α) : Stream'.head (toStream' s) = head s := by
  cases s using recOn' <;> simp [toStream']

@[simp]
theorem tail_toStream' (s : Seq' α) :
    Stream'.tail (toStream' s) =
      Option.elim (dest s) (Stream'.const none) (toStream' ∘ Prod.snd) := by
  cases s using recOn' <;> simp [toStream']

@[simp]
theorem get_toStream' (s : Seq' α) (n : ℕ) : Stream'.get (toStream' s) n = get? s n := by
  induction n generalizing s with
  | zero => simp [Stream'.get_zero, get?_zero]
  | succ n hn => cases s using recOn' <;> simp [Stream'.get_succ, get?_succ, hn]

@[simp]
theorem toStream'_nil : toStream' (nil : Seq' α) = Stream'.const none := by
  apply Stream'.dest_injective
  simp

@[simp]
theorem toStream'_cons (a : α) (s : Seq' α) : toStream' (a ::ₑ s) = some a ::ₛ toStream' s := by
  apply Stream'.dest_injective
  simp

/-- Tails of a sequences, starting with `s`. -/
def tails (s : Seq' α) : Stream' (Seq' α) :=
  Stream'.iterate tail s

@[simp]
theorem head_tails (s : Seq' α) : Stream'.head (tails s) = s :=
  Stream'.head_iterate tail s

@[simp]
theorem tail_tails (s : Seq' α) : Stream'.tail (tails s) = tails (tail s) :=
  Stream'.tail_iterate tail s

theorem tails_eq (s : Seq' α) : tails s = s ::ₛ tails (tail s) := by
  apply Stream'.dest_eq_cons
  simp

@[simp]
theorem get_tails (n : ℕ) (s : Seq' α) : Stream'.get (tails s) n = drop n s := by
  induction n generalizing s with
  | zero => simp [Stream'.get_zero]
  | succ n hn => simp [Stream'.get_succ, hn]

/-- An auxiliary definition for `inits`. -/
def initsCore (l : List α) (s : Seq' α) : Stream' (List α) :=
  Stream'.corec''
    (fun (l', s') =>
      match dest s' with
      | none => Sum.inl (Stream'.const l')
      | some (a, s') => Sum.inr (l', (l' ++ [a], s')))
    (l, s)

/-- Initial segments of a sequence. -/
def inits (s : Seq' α) : Stream' (List α) :=
  initsCore [] s

@[simp]
theorem head_initsCore (l : List α) (s : Seq' α) : Stream'.head (initsCore l s) = l := by
  cases s using recOn' <;> simp [initsCore]

@[simp]
theorem tail_initsCore (l : List α) (s : Seq' α) :
    Stream'.tail (initsCore l s) =
      Option.elim (dest s) (Stream'.const l) (fun (a, s') => initsCore (l ++ [a]) s') := by
  cases s using recOn' <;> simp [initsCore]

@[simp]
theorem initsCore_nil (l : List α) : initsCore l nil = Stream'.const l := by
  apply Stream'.dest_injective
  simp

@[simp]
theorem initsCore_cons (l : List α) (a : α) (s : Seq' α) :
    initsCore l (a ::ₑ s) = l ::ₛ initsCore (l ++ [a]) s := by
  apply Stream'.dest_injective
  simp

@[simp]
theorem cons_get_initsCore (a : α) (n : ℕ) (l : List α) (s : Seq' α) :
    Stream'.get (initsCore (a :: l) s) n = a :: Stream'.get (initsCore l s) n := by
  induction n generalizing l s with
  | zero => simp [Stream'.get_zero]
  | succ n hn => cases s using recOn' <;> simp [Stream'.get_succ, hn]

@[simp]
theorem get_inits (n : ℕ) (s : Seq' α) : Stream'.get (inits s) n = take n s := by
  unfold inits
  induction n generalizing s with
  | zero => simp [Stream'.get_zero]
  | succ n hn => cases s using recOn' <;> simp [Stream'.get_succ, hn]

theorem mem_map_of_mem (f : α → β) {a : α} {s : Seq' α} (ha : a ∈ s) : f a ∈ map f s := by
  simp [mem_def] at ha ⊢
  cases ha with | intro n ha => exists n, a
#align stream.seq.mem_map Seq'.mem_map_of_mem

theorem exists_of_mem_map {f} {b : β} {s : Seq' α} (hb : b ∈ map f s) : ∃ a, a ∈ s ∧ f a = b := by
  simp [mem_def] at hb ⊢
  rcases hb with ⟨n, a, ha, rfl⟩
  exact ⟨a, ⟨n, ha⟩, rfl⟩
#align stream.seq.exists_of_mem_map Seq'.exists_of_mem_map

@[simp]
theorem mem_map {b : β} {f : α → β} {s : Seq' α} : b ∈ map f s ↔ ∃ a, a ∈ s ∧ f a = b where
  mp  := exists_of_mem_map
  mpr := by rintro ⟨b, h, rfl⟩; exact mem_map_of_mem f h

theorem of_mem_append {s₁ s₂ : Seq' α} {a : α} (h : a ∈ s₁ ++ s₂) : a ∈ s₁ ∨ a ∈ s₂ := by
  generalize e : s₁ ++ s₂ = ss at h
  induction h using mem_rec_on generalizing s₁ with
  | mem_cons s' =>
    induction s₁ using recOn' with
    | nil =>
      simp at e
      simp [e]
    | cons c t₁ =>
      simp at e
      simp [e]
  | @mem_cons_of_mem b s' m o =>
    induction s₁ using recOn' with
    | nil =>
      simp at e
      simp [e, m]
    | cons c t₁ =>
      simp at e
      rcases e with ⟨rfl, e⟩
      simp [o e, or_assoc]
#align stream.seq.of_mem_append Seq'.of_mem_append

theorem mem_append_left {s₁ s₂ : Seq' α} {a : α} (h : a ∈ s₁) : a ∈ s₁ ++ s₂ := by
  induction h using mem_rec_on <;> simp [*]
#align stream.seq.mem_append_left Seq'.mem_append_left

@[simp]
theorem enum_cons (s : Seq' α) (x : α) :
    enum (x ::ₑ s) = (0, x) ::ₑ map (Prod.map Nat.succ id) (enum s) := by
  ext ⟨n⟩ : 1
  · simp
  · simp only [get?_enum, get?_cons_succ, map_get?, Option.map_map]
    congr
#align stream.seq.enum_cons Seq'.enum_cons

end Seq'

namespace Seq1

variable {α : Type u} {β : Type v} {γ : Type w}

open Seq'

/-- Convert a `Seq1` to a sequence. -/
@[coe]
def toSeq : Seq1 α → Seq' α
  | ⟨a, s⟩ => a ::ₑ s
#align stream.seq1.to_seq Seq1.toSeq

instance coeSeq : Coe (Seq1 α) (Seq' α) :=
  ⟨toSeq⟩
#align stream.seq1.coe_seq Seq1.coeSeq

/-- Map a function on a `Seq1` -/
def map (f : α → β) : Seq1 α → Seq1 β
  | ⟨a, s⟩ => ⟨f a, Seq'.map f s⟩
#align stream.seq1.map Seq1.map

-- Porting note (#10756): new theorem.
@[simp]
theorem map_mk {f : α → β} {a s} : map f ⟨a, s⟩ = ⟨f a, Seq'.map f s⟩ :=
  rfl

@[simp]
theorem map_id : ∀ s : Seq1 α, map id s = s
  | ⟨a, s⟩ => by simp [map]
#align stream.seq1.map_id Seq1.map_id

/-- Flatten a nonempty sequence of nonempty sequences -/
def join : Seq1 (Seq1 α) → Seq1 α
  | ⟨⟨a, s⟩, S⟩ =>
    match dest s with
    | none => ⟨a, Seq'.join S⟩
    | some (b, s') => ⟨a, Seq'.join (⟨b, s'⟩ ::ₑ S)⟩
#align stream.seq1.join Seq1.join

@[simp]
theorem join_nil (a : α) (S) : join ⟨⟨a, nil⟩, S⟩ = ⟨a, Seq'.join S⟩ :=
  rfl
#align stream.seq1.join_nil Seq1.join_nil

@[simp]
theorem join_cons (a b : α) (s S) :
    join ⟨⟨a, b ::ₑ s⟩, S⟩ = ⟨a, Seq'.join (⟨b, s⟩ ::ₑ S)⟩ := by
  simp [join]
#align stream.seq1.join_cons Seq1.join_cons

/-- The `pure` operator for the `Seq1` monad,
  which produces a singleton sequence. -/
def pure (a : α) : Seq1 α :=
  ⟨a, nil⟩
#align stream.seq1.ret Seq1.pure

instance [Inhabited α] : Inhabited (Seq1 α) :=
  ⟨pure default⟩

/-- The `bind` operator for the `Seq1` monad,
  which maps `f` on each element of `s` and appends the results together.
  (Not all of `s` may be evaluated, because the first few elements of `s`
  may already produce an infinite result.) -/
def bind (s : Seq1 α) (f : α → Seq1 β) : Seq1 β :=
  join (map f s)
#align stream.seq1.bind Seq1.bind

@[simp]
theorem join_map_pure (s : Seq' α) : Seq'.join (Seq'.map pure s) = s := by
  apply coinduction2 s; intro s; induction s using recOn' <;> simp [pure]
#align stream.seq1.join_map_ret Seq1.join_map_pure

@[simp]
theorem bind_pure (f : α → β) : ∀ s, bind s (pure ∘ f) = map f s
  | ⟨a, s⟩ => by
    simp [bind, map, pure, ← map_map pure, - map_map]
#align stream.seq1.bind_ret Seq1.bind_pure

@[simp]
theorem pure_bind (a : α) (f : α → Seq1 β) : bind (pure a) f = f a := by
  simp [pure, bind, map]
  cases' f a with a s
  induction s using recOn' <;> simp
#align stream.seq1.ret_bind Seq1.pure_bind

@[simp]
theorem map_join' (f : α → β) (S) : Seq'.map f (Seq'.join S) = Seq'.join (Seq'.map (map f) S) := by
  apply
    Seq'.eq_of_bisim fun s1 s2 =>
      ∃ s S,
        s1 = s ++ Seq'.map f (Seq'.join S) ∧ s2 = s ++ Seq'.join (Seq'.map (map f) S)
  · intro s1 s2 h
    exact
      match s1, s2, h with
      | _, _, ⟨s, S, rfl, rfl⟩ => by
        induction' s using recOn' with _ s <;> simp
        · induction' S using recOn' with x S <;> simp
          · cases' x with a s
            simpa [map] using ⟨_, _, rfl, rfl⟩
        · exact ⟨s, S, rfl, rfl⟩
  · refine' ⟨nil, S, _, _⟩ <;> simp
#align stream.seq1.map_join' Seq1.map_join'

@[simp]
theorem map_join (f : α → β) : ∀ S, map f (join S) = join (map (map f) S)
  | ⟨⟨a, s⟩, S⟩ => by induction s using recOn' <;> simp [map]
#align stream.seq1.map_join Seq1.map_join

@[simp]
theorem join_join (SS : Seq' (Seq1 (Seq1 α))) :
    Seq'.join (Seq'.join SS) = Seq'.join (Seq'.map join SS) := by
  apply
    Seq'.eq_of_bisim fun s1 s2 =>
      ∃ s SS,
        s1 = s ++ Seq'.join (Seq'.join SS) ∧ s2 = s ++ Seq'.join (Seq'.map join SS)
  · intro s1 s2 h
    exact
      match s1, s2, h with
      | _, _, ⟨s, SS, rfl, rfl⟩ => by
        induction' s using recOn' with _ s <;> simp
        · induction' SS using recOn' with S SS <;> simp
          · cases' S with s S; cases' s with x s
            simp only [Seq'.join_cons, join_append, dest_cons]
            induction' s using recOn' with x s <;> simp
            · exact ⟨_, _, rfl, rfl⟩
            · refine' ⟨x ::ₑ (s ++ Seq'.join S), SS, _, _⟩ <;> simp
        · exact ⟨s, SS, rfl, rfl⟩
  · refine' ⟨nil, SS, _, _⟩ <;> simp
#align stream.seq1.join_join Seq1.join_join

@[simp]
theorem bind_assoc (s : Seq1 α) (f : α → Seq1 β) (g : β → Seq1 γ) :
    bind (bind s f) g = bind s fun x : α => bind (f x) g := by
  cases' s with a s
  -- porting note (#10745): was `simp [bind, map]`.
  simp only [bind, map_mk, map_join]
  rw [map_map]
  simp only [show (fun x => join (map g (f x))) = join ∘ (map g ∘ f) from rfl]
  rw [← map_map join]
  generalize Seq'.map (map g ∘ f) s = SS
  rcases map g (f a) with ⟨⟨a, s⟩, S⟩
  induction' s using recOn' with x s_1 <;> induction' S using recOn' with x_1 s_2 <;> simp
  · cases' x_1 with x t
    induction t using recOn' <;> simp
  · cases' x_1 with y t; simp
#align stream.seq1.bind_assoc Seq1.bind_assoc

instance monad : Monad Seq1 where
  map := @map
  pure := @pure
  bind := @bind
#align stream.seq1.monad Seq1.monad

instance lawfulMonad : LawfulMonad Seq1 := LawfulMonad.mk'
  (id_map := @map_id)
  (bind_pure_comp := @bind_pure)
  (pure_bind := @pure_bind)
  (bind_assoc := @bind_assoc)
#align stream.seq1.is_lawful_monad Seq1.lawfulMonad

end Seq1
