/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Option.NAry
import Mathlib.Data.Sequence.Computation
import Batteries.Data.LazyList

/-!
# Possibly infinite lists

This file provides a `Sequence α` type representing possibly infinite lists
(referred here as sequences). It is encoded as an infinite stream of options such that if
`f n = none`, then `f m = none` for all `m ≥ n`.
-/

open scoped Stream'

universe u v w

/-
coinductive Sequence (α : Type u) : Type u
| nil : Sequence α
| cons : α → Sequence α → Sequence α
-/
/-- A stream `s : Option α` is a sequence if `s.get n = none` implies `s.get (n + 1) = none`.
-/
def Stream'.IsSequence {α : Type u} (s : Stream' (Option α)) : Prop :=
  ∀ {n : ℕ}, s n = none → s (n + 1) = none

/-- `Sequence α` is the type of possibly infinite lists (referred here as sequences).
  It is encoded as an infinite stream of options such that if `f n = none`, then
  `f m = none` for all `m ≥ n`. -/
def Sequence (α : Type u) : Type u :=
  { f : Stream' (Option α) // f.IsSequence }

/-- `Sequence1 α` is the type of nonempty sequences. -/
def Sequence1 (α) :=
  α × Sequence α

namespace Sequence

variable {α : Type u} {β : Type v} {γ : Type w}

/-- The empty sequence -/
def nil : Sequence α :=
  ⟨Stream'.const none, fun {_} _ => rfl⟩

instance : Inhabited (Sequence α) :=
  ⟨nil⟩

/-- Prepend an element to a sequence -/
def cons (a : α) (s : Sequence α) : Sequence α :=
  ⟨some a::s.1, by
    rintro (n | _) h
    · contradiction
    · exact s.2 h⟩

@[simp]
theorem val_cons (s : Sequence α) (x : α) : (cons x s).val = some x::s.val :=
  rfl

/-- Get the nth element of a sequence (if it exists) -/
def get? : Sequence α → ℕ → Option α :=
  Subtype.val

@[simp]
theorem get?_mk (f hf) : @get? α ⟨f, hf⟩ = f :=
  rfl

@[simp]
theorem get?_nil (n : ℕ) : (@nil α).get? n = none :=
  rfl

@[simp]
theorem get?_cons_zero (a : α) (s : Sequence α) : (cons a s).get? 0 = some a :=
  rfl

@[simp]
theorem get?_cons_succ (a : α) (s : Sequence α) (n : ℕ) : (cons a s).get? (n + 1) = s.get? n :=
  rfl

@[ext]
protected theorem ext {s t : Sequence α} (h : ∀ n : ℕ, s.get? n = t.get? n) : s = t :=
  Subtype.eq <| funext h

theorem cons_injective2 : Function.Injective2 (cons : α → Sequence α → Sequence α) :=
  fun x y s t h =>
    ⟨by rw [← Option.some_inj, ← get?_cons_zero, h, get?_cons_zero],
      Sequence.ext fun n => by simp_rw [← get?_cons_succ x s n, h, get?_cons_succ]⟩

theorem cons_left_injective (s : Sequence α) : Function.Injective fun x => cons x s :=
  cons_injective2.left _

theorem cons_right_injective (x : α) : Function.Injective (cons x) :=
  cons_injective2.right _

/-- A sequence has terminated at position `n` if the value at position `n` equals `none`. -/
def TerminatedAt (s : Sequence α) (n : ℕ) : Prop :=
  s.get? n = none

/-- It is decidable whether a sequence terminates at a given position. -/
instance terminatedAtDecidable (s : Sequence α) (n : ℕ) : Decidable (s.TerminatedAt n) :=
  decidable_of_iff' (s.get? n).isNone <| by unfold TerminatedAt; cases s.get? n <;> simp

/-- A sequence terminates if there is some position `n` at which it has terminated. -/
def Terminates (s : Sequence α) : Prop :=
  ∃ n : ℕ, s.TerminatedAt n

theorem not_terminates_iff {s : Sequence α} : ¬s.Terminates ↔ ∀ n, (s.get? n).isSome := by
  simp only [Terminates, TerminatedAt, ← Ne.eq_def, Option.ne_none_iff_isSome, not_exists, iff_self]

/-- Functorial action of the functor `Option (α × _)` -/
@[simp]
def omap (f : β → γ) : Option (α × β) → Option (α × γ)
  | none => none
  | some (a, b) => some (a, f b)

/-- Get the first element of a sequence -/
def head (s : Sequence α) : Option α :=
  get? s 0

/-- Get the tail of a sequence (or `nil` if the sequence is `nil`) -/
def tail (s : Sequence α) : Sequence α :=
  ⟨s.1.tail, fun n' => by
    cases' s with f al
    exact al n'⟩

/-- member definition for `Sequence`-/
protected def Mem (a : α) (s : Sequence α) :=
  some a ∈ s.1

instance : Membership α (Sequence α) :=
  ⟨Sequence.Mem⟩

theorem le_stable (s : Sequence α) {m n} (h : m ≤ n) : s.get? m = none → s.get? n = none := by
  cases' s with f al
  induction' h with n _ IH
  exacts [id, fun h2 => al (IH h2)]

/-- If a sequence terminated at position `n`, it also terminated at `m ≥ n`. -/
theorem terminated_stable :
    ∀ (s : Sequence α) {m n : ℕ}, m ≤ n → s.TerminatedAt m → s.TerminatedAt n :=
  le_stable

/-- If `s.get? n = some aₙ` for some value `aₙ`, then there is also some value `aₘ` such
that `s.get? = some aₘ` for `m ≤ n`.
-/
theorem ge_stable (s : Sequence α) {aₙ : α} {n m : ℕ} (m_le_n : m ≤ n)
    (s_nth_eq_some : s.get? n = some aₙ) : ∃ aₘ : α, s.get? m = some aₘ :=
  have : s.get? n ≠ none := by simp [s_nth_eq_some]
  have : s.get? m ≠ none := mt (s.le_stable m_le_n) this
  Option.ne_none_iff_exists'.mp this

theorem not_mem_nil (a : α) : a ∉ @nil α := fun ⟨_, (h : some a = none)⟩ => by injection h

theorem mem_cons (a : α) : ∀ s : Sequence α, a ∈ cons a s
  | ⟨_, _⟩ => Stream'.mem_cons (some a) _

theorem mem_cons_of_mem (y : α) {a : α} : ∀ {s : Sequence α}, a ∈ s → a ∈ cons y s
  | ⟨_, _⟩ => Stream'.mem_cons_of_mem (some y)

theorem eq_or_mem_of_mem_cons {a b : α} : ∀ {s : Sequence α}, a ∈ cons b s → a = b ∨ a ∈ s
  | ⟨f, al⟩, h => (Stream'.eq_or_mem_of_mem_cons h).imp_left fun h => by injection h

@[simp]
theorem mem_cons_iff {a b : α} {s : Sequence α} : a ∈ cons b s ↔ a = b ∨ a ∈ s :=
  ⟨eq_or_mem_of_mem_cons, by rintro (rfl | m) <;> [apply mem_cons; exact mem_cons_of_mem _ m]⟩

/-- Destructor for a sequence, resulting in either `none` (for `nil`) or
  `some (a, s)` (for `cons a s`). -/
def destruct (s : Sequence α) : Option (Sequence1 α) :=
  (fun a' => (a', s.tail)) <$> get? s 0

theorem destruct_eq_nil {s : Sequence α} : destruct s = none → s = nil := by
  dsimp [destruct]
  induction' f0 : get? s 0 <;> intro h
  · apply Subtype.eq
    funext n
    induction' n with n IH
    exacts [f0, s.2 IH]
  · contradiction

theorem destruct_eq_cons {s : Sequence α} {a s'} : destruct s = some (a, s') → s = cons a s' := by
  dsimp [destruct]
  induction' f0 : get? s 0 with a' <;> intro h
  · contradiction
  · cases' s with f al
    injections _ h1 h2
    rw [← h2]
    apply Subtype.eq
    dsimp [tail, cons]
    rw [h1] at f0
    rw [← f0]
    exact (Stream'.eta f).symm

@[simp]
theorem destruct_nil : destruct (nil : Sequence α) = none :=
  rfl

@[simp]
theorem destruct_cons (a : α) : ∀ s, destruct (cons a s) = some (a, s)
  | ⟨f, al⟩ => by
    unfold cons destruct Functor.map
    apply congr_arg fun s => some (a, s)
    apply Subtype.eq; dsimp [tail]

-- Porting note: needed universe annotation to avoid universe issues
theorem head_eq_destruct (s : Sequence α) : head.{u} s = Prod.fst.{u} <$> destruct.{u} s := by
  unfold destruct head; cases get? s 0 <;> rfl

@[simp]
theorem head_nil : head (nil : Sequence α) = none :=
  rfl

@[simp]
theorem head_cons (a : α) (s) : head (cons a s) = some a := by
  rw [head_eq_destruct, destruct_cons, Option.map_eq_map, Option.map_some']

@[simp]
theorem tail_nil : tail (nil : Sequence α) = nil :=
  rfl

@[simp]
theorem tail_cons (a : α) (s) : tail (cons a s) = s := by
  cases' s with f al
  apply Subtype.eq
  dsimp [tail, cons]

@[simp]
theorem get?_tail (s : Sequence α) (n) : get? (tail s) n = get? s (n + 1) :=
  rfl

/-- Recursion principle for sequences, compare with `List.recOn`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
def recOn {C : Sequence α → Sort v} (s : Sequence α) (nil : C nil) (cons : ∀ x s, C (cons x s)) :
    C s := by
  cases' H : destruct s with v
  · rw [destruct_eq_nil H]
    apply nil
  · cases' v with a s'
    rw [destruct_eq_cons H]
    apply cons

@[elab_as_elim]
theorem mem_rec_on {a} {C : (s : Sequence α) → a ∈ s → Prop} {s} (M : a ∈ s)
    (mem_cons : ∀ s, C (cons a s) (mem_cons a s))
    (mem_cons_of_mem : ∀ (y) {s} (h : a ∈ s), C s h → C (cons y s) (mem_cons_of_mem y h)) :
    C s M := by
  change ∃ n, some a = get? s n at M
  cases M with
  | intro k e =>
    induction k generalizing s with
    | zero =>
      induction s with
      | nil => injection e
      | cons b s' =>
        injection e with e'
        induction e'
        exact mem_cons s'
    | succ k IH =>
      induction s with
      | nil => injection e
      | cons b s' =>
        rw [get?_cons_succ] at e
        exact mem_cons_of_mem b _ (IH e)

/-- Corecursor over pairs of `Option` values-/
def Corec.f (f : β → Option (α × β)) : Option β → Option α × Option β
  | none => (none, none)
  | some b =>
    match f b with
    | none => (none, none)
    | some (a, b') => (some a, some b')

/-- Corecursor for `Sequence α` as a coinductive type. Iterates `f` to produce new elements
  of the sequence until `none` is obtained. -/
def corec (f : β → Option (α × β)) (b : β) : Sequence α := by
  refine ⟨Stream'.corec' (Corec.f f) (some b), fun {n} h => ?_⟩
  rw [Stream'.corec'_eq]
  change Stream'.corec' (Corec.f f) (Corec.f f (some b)).2 n = none
  revert h; generalize some b = o; revert o
  induction' n with n IH <;> intro o
  · change (Corec.f f o).1 = none → (Corec.f f (Corec.f f o).2).1 = none
    cases' o with b <;> intro h
    · rfl
    dsimp [Corec.f] at h
    dsimp [Corec.f]
    revert h; cases' h₁ : f b with s <;> intro h
    · rfl
    · cases' s with a b'
      contradiction
  · rw [Stream'.corec'_eq (Corec.f f) (Corec.f f o).2, Stream'.corec'_eq (Corec.f f) o]
    exact IH (Corec.f f o).2

@[simp]
theorem corec_eq (f : β → Option (α × β)) (b : β) :
    destruct (corec f b) = omap (corec f) (f b) := by
  dsimp [corec, destruct, get]
  -- Porting note: next two lines were `change`...`with`...
  have h : Stream'.corec' (Corec.f f) (some b) 0 = (Corec.f f (some b)).1 := rfl
  rw [h]
  dsimp [Corec.f]
  induction' h : f b with s; · rfl
  cases' s with a b'; dsimp [Corec.f]
  apply congr_arg fun b' => some (a, b')
  apply Subtype.eq
  dsimp [corec, tail]
  rw [Stream'.corec'_eq, Stream'.tail_cons]
  dsimp [Corec.f]; rw [h]

section Bisim

variable (R : Sequence α → Sequence α → Prop)

local infixl:50 " ~ " => R

/-- Bisimilarity relation over `Option` of `Sequence1 α`-/
def BisimO : Option (Sequence1 α) → Option (Sequence1 α) → Prop
  | none, none => True
  | some (a, s), some (a', s') => a = a' ∧ R s s'
  | _, _ => False

attribute [simp] BisimO

/-- a relation is bisimilar if it meets the `BisimO` test-/
def IsBisimulation :=
  ∀ ⦃s₁ s₂⦄, s₁ ~ s₂ → BisimO R (destruct s₁) (destruct s₂)

-- If two streams are bisimilar, then they are equal
theorem eq_of_bisim (bisim : IsBisimulation R) {s₁ s₂} (r : s₁ ~ s₂) : s₁ = s₂ := by
  apply Subtype.eq
  apply Stream'.eq_of_bisim fun x y => ∃ s s' : Sequence α, s.1 = x ∧ s'.1 = y ∧ R s s'
  · dsimp [Stream'.IsBisimulation]
    rintro t₁ t₂ ⟨s, s', rfl, rfl, r⟩
    next =>
      suffices head s = head s' ∧ R (tail s) (tail s') from
        And.imp id (fun r => ⟨tail s, tail s', rfl, rfl, r⟩) this
      have := bisim r
      cases s <;> cases s'
      case nil.nil =>
        constructor
        · rfl
        · assumption
      case nil.cons x s | cons.nil x s =>
        rw [destruct_nil, destruct_cons] at this
        exact False.elim this
      case cons.cons x s x' s' =>
        rw [destruct_cons, destruct_cons] at this
        rw [head_cons, head_cons, tail_cons, tail_cons]
        cases' this with h1 h2
        constructor
        · rw [h1]
        · exact h2
  · exact ⟨s₁, s₂, rfl, rfl, r⟩

end Bisim

section All

/-
This section enables to handle `∀ a ∈ (s : Seq' α), p s` as a following coinductive proposition:
```lean
coinductive All {α : Type u} (p : α → Prop) : Seq' α → Prop
  | nil : All p nil
  | cons {a s} : p a → All p s → All p (cons a s)
```
-/

theorem all_nil (p : α → Prop) : ∀ a ∈ (nil : Sequence α), p a :=
  fun a ha => absurd ha (not_mem_nil a)

theorem all_cons {p : α → Prop} {a : α} {s : Sequence α} :
    (∀ b ∈ cons a s, p b) ↔ p a ∧ ∀ b ∈ s, p b := by
  simp only [mem_cons_iff, forall_eq_or_imp]

theorem all_coind {p : α → Prop} (P : Sequence α → Prop)
    (cons : ∀ ⦃a s⦄, P (cons a s) → p a ∧ P s) {s} (hs : P s) : ∀ a ∈ s, p a := by
  intro a ha
  induction ha using mem_rec_on with specialize cons hs
  | mem_cons s =>
    exact cons.1
  | @mem_cons_of_mem y s _ hs₂ =>
    exact hs₂ cons.2

end All

theorem coinduction :
    ∀ {s₁ s₂ : Sequence α}, head s₁ = head s₂ →
      (∀ (β : Type u) (fr : Sequence α → β), fr s₁ = fr s₂ → fr (tail s₁) = fr (tail s₂)) → s₁ = s₂
  | _, _, hh, ht =>
    Subtype.eq (Stream'.coinduction hh fun β fr => ht β fun s => fr s.1)

theorem coinduction2 (s) (f g : Sequence α → Sequence β)
    (H :
      ∀ s,
        BisimO (fun s1 s2 : Sequence β => ∃ s : Sequence α, s1 = f s ∧ s2 = g s) (destruct (f s))
          (destruct (g s))) :
    f s = g s := by
  refine eq_of_bisim (fun s1 s2 => ∃ s, s1 = f s ∧ s2 = g s) ?_ ⟨s, rfl, rfl⟩
  intro s1 s2 h; rcases h with ⟨s, h1, h2⟩
  rw [h1, h2]; apply H

/-- Embed a list as a sequence -/
@[coe]
def ofList (l : List α) : Sequence α :=
  ⟨List.get? l, fun {n} h => by
    rw [List.get?_eq_none] at h ⊢
    exact h.trans (Nat.le_succ n)⟩

instance coeList : Coe (List α) (Sequence α) :=
  ⟨ofList⟩

@[simp]
theorem ofList_nil : ofList [] = (nil : Sequence α) :=
  rfl

@[simp]
theorem ofList_get (l : List α) (n : ℕ) : (ofList l).get? n = l.get? n :=
  rfl

@[simp]
theorem ofList_cons (a : α) (l : List α) : ofList (a::l) = cons a (ofList l) := by
  ext1 (_ | n) <;> rfl

/-- Embed an infinite stream as a sequence -/
@[coe]
def ofStream (s : Stream' α) : Sequence α :=
  ⟨s.map some, fun {n} h => by contradiction⟩

instance coeStream : Coe (Stream' α) (Sequence α) :=
  ⟨ofStream⟩

section LazyList

set_option linter.deprecated false

/-- Embed a `LazyList α` as a sequence. Note that even though this
  is non-meta, it will produce infinite sequences if used with
  cyclic `LazyList`s created by meta constructions. -/
@[deprecated (since := "2024-07-22")]
def ofLazyList : LazyList α → Sequence α :=
  corec fun l =>
    match l with
    | LazyList.nil => none
    | LazyList.cons a l' => some (a, l'.get)

@[deprecated (since := "2024-07-22")]
instance coeLazyList : Coe (LazyList α) (Sequence α) :=
  ⟨ofLazyList⟩

/-- Translate a sequence into a `LazyList`. Since `LazyList` and `List`
  are isomorphic as non-meta types, this function is necessarily meta. -/
@[deprecated (since := "2024-07-22")]
unsafe def toLazyList : Sequence α → LazyList α
  | s =>
    match destruct s with
    | none => LazyList.nil
    | some (a, s') => LazyList.cons a (toLazyList s')

end LazyList

/-- Translate a sequence to a list. This function will run forever if
  run on an infinite sequence. -/
unsafe def forceToList : Sequence α → List α
  | s =>
    match destruct s with
    | none => []
    | some (a, s') => a :: forceToList s'

/-- The sequence of natural numbers some 0, some 1, ... -/
def nats : Sequence ℕ :=
  Stream'.nats

@[simp]
theorem nats_get? (n : ℕ) : nats.get? n = some n :=
  rfl

/-- Append two sequences. If `s₁` is infinite, then `s₁ ++ s₂ = s₁`,
  otherwise it puts `s₂` at the location of the `nil` in `s₁`. -/
def append (s₁ s₂ : Sequence α) : Sequence α :=
  @corec α (Sequence α × Sequence α)
    (fun ⟨s₁, s₂⟩ =>
      match destruct s₁ with
      | none => omap (fun s₂ => (nil, s₂)) (destruct s₂)
      | some (a, s₁') => some (a, s₁', s₂))
    (s₁, s₂)

/-- Map a function over a sequence. -/
def map (f : α → β) : Sequence α → Sequence β
  | ⟨s, al⟩ =>
    ⟨s.map (Option.map f), fun {n} => by
      dsimp [Stream'.map, Stream'.get]
      induction' e : s n with e <;> intro
      · rw [al e]
        assumption
      · contradiction⟩

/-- Partial map. If `f : Π a, P a → β` is a partial function defined on
  `a : α` satisfying `P`, then `pmap f s h` is essentially the same as `map f s`
  but is defined only when all members of `l` satisfy `P`, using the proof
  to apply `f`. -/
def pmap {P : α → Prop} (f : ∀ a, P a → β) (s : Sequence α) (H : ∀ a ∈ s, P a) : Sequence β :=
  ⟨s.val.pmap (Option.pmap f) (fun o ho a ha => ha.symm.rec (H a) ho), fun {n} => by
    simpa only [Stream'.pmap, Option.pmap_eq_none_iff] using s.property⟩

/-- Flatten a sequence of sequences. (It is required that the
  sequences be nonempty to ensure productivity; in the case
  of an infinite sequence of `nil`, the first element is never
  generated.) -/
def join : Sequence (Sequence1 α) → Sequence α :=
  corec fun S =>
    match destruct S with
    | none => none
    | some ((a, s), S') =>
      some
        (a,
          match destruct s with
          | none => S'
          | some s' => cons s' S')

/-- Remove the first `n` elements from the sequence. -/
def drop (s : Sequence α) : ℕ → Sequence α
  | 0 => s
  | n + 1 => tail (drop s n)

attribute [simp] drop

/-- Take the first `n` elements of the sequence (producing a list) -/
def take : ℕ → Sequence α → List α
  | 0, _ => []
  | n + 1, s =>
    match destruct s with
    | none => []
    | some (x, r) => List.cons x (take n r)

/-- Split a sequence at `n`, producing a finite initial segment
  and an infinite tail. -/
def splitAt : ℕ → Sequence α → List α × Sequence α
  | 0, s => ([], s)
  | n + 1, s =>
    match destruct s with
    | none => ([], nil)
    | some (x, s') =>
      let (l, r) := splitAt n s'
      (List.cons x l, r)

section ZipWith

/-- Combine two sequences with a function -/
def zipWith (f : α → β → γ) (s₁ : Sequence α) (s₂ : Sequence β) : Sequence γ :=
  ⟨fun n => Option.map₂ f (s₁.get? n) (s₂.get? n), fun {_} hn =>
    Option.map₂_eq_none_iff.2 <| (Option.map₂_eq_none_iff.1 hn).imp s₁.2 s₂.2⟩

variable {s : Sequence α} {s' : Sequence β} {n : ℕ}

@[simp]
theorem get?_zipWith (f : α → β → γ) (s s' n) :
    (zipWith f s s').get? n = Option.map₂ f (s.get? n) (s'.get? n) :=
  rfl

end ZipWith

/-- Pair two sequences into a sequence of pairs -/
def zip : Sequence α → Sequence β → Sequence (α × β) :=
  zipWith Prod.mk

theorem get?_zip (s : Sequence α) (t : Sequence β) (n : ℕ) :
    get? (zip s t) n = Option.map₂ Prod.mk (get? s n) (get? t n) :=
  get?_zipWith _ _ _ _

/-- Separate a sequence of pairs into two sequences -/
def unzip (s : Sequence (α × β)) : Sequence α × Sequence β :=
  (map Prod.fst s, map Prod.snd s)

/-- Enumerate a sequence by tagging each element with its index. -/
def enum (s : Sequence α) : Sequence (ℕ × α) :=
  Sequence.zip nats s

@[simp]
theorem get?_enum (s : Sequence α) (n : ℕ) : get? (enum s) n = Option.map (Prod.mk n) (get? s n) :=
  get?_zip _ _ _

@[simp]
theorem enum_nil : enum (nil : Sequence α) = nil :=
  rfl

/-- Convert a sequence which is known to terminate into a list -/
def toList (s : Sequence α) (h : s.Terminates) : List α :=
  take (Nat.find h) s

/-- Convert a sequence which is known not to terminate into a stream -/
def toStream (s : Sequence α) (h : ¬s.Terminates) : Stream' α := fun n =>
  Option.get _ <| not_terminates_iff.1 h n

/-- Convert a sequence into either a list or a stream depending on whether
  it is finite or infinite. (Without decidability of the infiniteness predicate,
  this is not constructively possible.) -/
def toListOrStream (s : Sequence α) [Decidable s.Terminates] : List α ⊕ Stream' α :=
  if h : s.Terminates then Sum.inl (toList s h) else Sum.inr (toStream s h)

@[simp]
theorem nil_append (s : Sequence α) : append nil s = s := by
  apply coinduction2; intro s
  dsimp [append]; rw [corec_eq]
  dsimp [append]
  cases s with
  | nil => trivial
  | cons x s =>
    rw [destruct_cons]
    dsimp
    exact ⟨rfl, s, rfl, rfl⟩

@[simp]
theorem cons_append (a : α) (s t) : append (cons a s) t = cons a (append s t) :=
  destruct_eq_cons <| by
    dsimp [append]; rw [corec_eq]
    dsimp [append]; rw [destruct_cons]

@[simp]
theorem append_nil (s : Sequence α) : append s nil = s := by
  apply coinduction2 s; intro s
  cases s with
  | nil => trivial
  | cons x s =>
    rw [cons_append, destruct_cons, destruct_cons]
    dsimp
    exact ⟨rfl, s, rfl, rfl⟩

@[simp]
theorem append_assoc (s t u : Sequence α) : append (append s t) u = append s (append t u) := by
  apply eq_of_bisim fun s1 s2 => ∃ s t u, s1 = append (append s t) u ∧ s2 = append s (append t u)
  · rintro s1 s2 ⟨s, t, u, rfl, rfl⟩
    cases s with simp
    | nil =>
      cases t with simp
      | nil =>
        cases u with simp
        | cons _ u =>
          refine ⟨nil, nil, u, ?_, ?_⟩ <;> simp
      | cons _ t =>
        refine ⟨nil, t, u, ?_, ?_⟩ <;> simp
    | cons _ s =>
      exact ⟨s, t, u, rfl, rfl⟩
  · exact ⟨s, t, u, rfl, rfl⟩

@[simp]
theorem map_nil (f : α → β) : map f nil = nil :=
  rfl

@[simp]
theorem map_cons (f : α → β) (a) : ∀ s, map f (cons a s) = cons (f a) (map f s)
  | ⟨s, al⟩ => by apply Subtype.eq; dsimp [cons, map]; rw [Stream'.map_cons]; rfl

@[simp]
theorem map_id : ∀ s : Sequence α, map id s = s
  | ⟨s, al⟩ => by
    apply Subtype.eq; dsimp [map]
    rw [Option.map_id, Stream'.map_id]

@[simp]
theorem map_tail (f : α → β) : ∀ s, map f (tail s) = tail (map f s)
  | ⟨s, al⟩ => by apply Subtype.eq; dsimp [tail, map]

theorem map_comp (f : α → β) (g : β → γ) : ∀ s : Sequence α, map (g ∘ f) s = map g (map f s)
  | ⟨s, al⟩ => by
    apply Subtype.eq; dsimp [map]
    apply congr_arg fun f : _ → Option γ => Stream'.map f s
    ext ⟨⟩ <;> rfl

@[simp]
theorem map_append (f : α → β) (s t) : map f (append s t) = append (map f s) (map f t) := by
  apply
    eq_of_bisim (fun s1 s2 => ∃ s t, s1 = map f (append s t) ∧ s2 = append (map f s) (map f t)) _
      ⟨s, t, rfl, rfl⟩
  rintro s1 s2 ⟨s, t, rfl, rfl⟩
  cases s with simp
  | nil =>
    cases t with simp
    | cons _ t =>
      refine ⟨nil, t, ?_, ?_⟩ <;> simp
  | cons _ s =>
    exact ⟨s, t, rfl, rfl⟩

@[simp]
theorem map_get? (f : α → β) : ∀ s n, get? (map f s) n = (get? s n).map f
  | ⟨_, _⟩, _ => rfl

instance : Functor Sequence where map := @map

instance : LawfulFunctor Sequence where
  id_map := @map_id
  comp_map := @map_comp
  map_const := rfl

@[simp]
theorem join_nil : join nil = (nil : Sequence α) :=
  destruct_eq_nil rfl

--@[simp] -- Porting note: simp can prove: `join_cons` is more general
theorem join_cons_nil (a : α) (S) : join (cons (a, nil) S) = cons a (join S) :=
  destruct_eq_cons <| by simp [join]

--@[simp] -- Porting note: simp can prove: `join_cons` is more general
theorem join_cons_cons (a b : α) (s S) :
    join (cons (a, cons b s) S) = cons a (join (cons (b, s) S)) :=
  destruct_eq_cons <| by simp [join]

@[simp]
theorem join_cons (a : α) (s S) : join (cons (a, s) S) = cons a (append s (join S)) := by
  apply
    eq_of_bisim
      (fun s1 s2 => s1 = s2 ∨ ∃ a s S, s1 = join (cons (a, s) S) ∧ s2 = cons a (append s (join S)))
      _ (Or.inr ⟨a, s, S, rfl, rfl⟩)
  rintro s1 s2 (rfl | ⟨a, s, S, rfl, rfl⟩)
  · cases s1 with
    | nil => trivial
    | cons x s =>
      rw [destruct_cons]
      exact ⟨rfl, Or.inl rfl⟩
  · cases s with
    | nil => simp [join_cons_cons, join_cons_nil]
    | cons x s =>
      simpa [join_cons_cons, join_cons_nil] using Or.inr ⟨x, s, S, rfl, rfl⟩

@[simp]
theorem join_append (S T : Sequence (Sequence1 α)) :
    join (append S T) = append (join S) (join T) := by
  apply
    eq_of_bisim fun s1 s2 =>
      ∃ s S T, s1 = append s (join (append S T)) ∧ s2 = append s (append (join S) (join T))
  · rintro s1 s2 ⟨s, S, T, rfl, rfl⟩
    cases s with simp
    | nil =>
      cases S with simp
      | nil =>
        cases T with
        | nil => simp
        | cons s T =>
          cases' s with a s; simp only [join_cons, destruct_cons, true_and]
          refine ⟨s, nil, T, ?_, ?_⟩ <;> simp
      | cons s S =>
        cases' s with a s
        simpa using ⟨s, S, T, rfl, rfl⟩
    | cons _ s =>
      exact ⟨s, S, T, rfl, rfl⟩
  · refine ⟨nil, S, T, ?_, ?_⟩ <;> simp

@[simp]
theorem ofStream_cons (a : α) (s) : ofStream (a::s) = cons a (ofStream s) := by
  apply Subtype.eq; simp only [ofStream, cons]; rw [Stream'.map_cons]

@[simp]
theorem ofList_append (l l' : List α) : ofList (l ++ l') = append (ofList l) (ofList l') := by
  induction l <;> simp [*]

@[simp]
theorem ofStream_append (l : List α) (s : Stream' α) :
    ofStream (l ++ₛ s) = append (ofList l) (ofStream s) := by
  induction l <;> simp [*, Stream'.nil_append_stream, Stream'.cons_append_stream]

/-- Convert a sequence into a list, embedded in a computation to allow for
  the possibility of infinite sequences (in which case the computation
  never returns anything). -/
def toList' {α} (s : Sequence α) : Computation (List α) :=
  @Computation.corec (List α) (List α × Sequence α)
    (fun ⟨l, s⟩ =>
      match destruct s with
      | none => Sum.inl l.reverse
      | some (a, s') => Sum.inr (a::l, s'))
    ([], s)

theorem dropn_add (s : Sequence α) (m) : ∀ n, drop s (m + n) = drop (drop s m) n
  | 0 => rfl
  | n + 1 => congr_arg tail (dropn_add s _ n)

theorem dropn_tail (s : Sequence α) (n) : drop (tail s) n = drop s (n + 1) := by
  rw [Nat.add_comm]; symm; apply dropn_add

@[simp]
theorem head_dropn (s : Sequence α) (n) : head (drop s n) = get? s n := by
  induction' n with n IH generalizing s; · rfl
  rw [← get?_tail, ← dropn_tail]; apply IH

theorem mem_map (f : α → β) {a : α} : ∀ {s : Sequence α}, a ∈ s → f a ∈ map f s
  | ⟨_, _⟩ => Stream'.mem_map (Option.map f)

theorem exists_of_mem_map {f} {b : β} : ∀ {s : Sequence α}, b ∈ map f s → ∃ a, a ∈ s ∧ f a = b :=
  fun {s} h => by match s with
  | ⟨g, al⟩ =>
    let ⟨o, om, oe⟩ := @Stream'.exists_of_mem_map _ _ (Option.map f) (some b) g h
    cases' o with a
    · injection oe
    · injection oe with h'; exact ⟨a, om, h'⟩

theorem of_mem_append {s₁ s₂ : Sequence α} {a : α} (h : a ∈ append s₁ s₂) : a ∈ s₁ ∨ a ∈ s₂ := by
  generalize e : append s₁ s₂ = ss at h
  induction h using mem_rec_on generalizing s₁ with
  | mem_cons s' =>
    induction s₁ with
    | nil =>
      rw [nil_append] at e; subst e
      right; exact mem_cons a s'
    | cons c t₁ =>
      have : c = a ∧ append t₁ s₂ = s' := by simpa using congr_arg destruct e
      clear e; rcases this with ⟨rfl, rfl⟩
      left; exact mem_cons c t₁
  | @mem_cons_of_mem b s' m o =>
    induction s₁ with
    | nil =>
      rw [nil_append] at e; subst e
      right; exact mem_cons_of_mem b m
    | cons c t₁ =>
      have : c = b ∧ append t₁ s₂ = s' := by simpa using congr_arg destruct e
      clear e; rcases this with ⟨rfl, rfl⟩
      exact (o rfl).imp_left (mem_cons_of_mem c)

theorem mem_append_left {s₁ s₂ : Sequence α} {a : α} (h : a ∈ s₁) : a ∈ append s₁ s₂ := by
  induction h using mem_rec_on <;> simp [*]

@[simp]
theorem enum_cons (s : Sequence α) (x : α) :
    enum (cons x s) = cons (0, x) (map (Prod.map Nat.succ id) (enum s)) := by
  ext ⟨n⟩ : 1
  · simp
  · simp only [get?_enum, get?_cons_succ, map_get?, Option.map_map]
    congr

end Sequence

namespace Sequence1

variable {α : Type u} {β : Type v} {γ : Type w}

open Sequence

/-- Convert a `Sequence1` to a sequence. -/
def toSeq : Sequence1 α → Sequence α
  | (a, s) => Sequence.cons a s

instance coeSeq : Coe (Sequence1 α) (Sequence α) :=
  ⟨toSeq⟩

/-- Map a function on a `Sequence1` -/
def map (f : α → β) : Sequence1 α → Sequence1 β
  | (a, s) => (f a, Sequence.map f s)

theorem map_pair {f : α → β} {a s} : map f (a, s) = (f a, Sequence.map f s) := rfl

theorem map_id : ∀ s : Sequence1 α, map id s = s
  | ⟨a, s⟩ => by simp [map]

/-- Flatten a nonempty sequence of nonempty sequences -/
def join : Sequence1 (Sequence1 α) → Sequence1 α
  | ((a, s), S) =>
    match destruct s with
    | none => (a, Sequence.join S)
    | some s' => (a, Sequence.join (Sequence.cons s' S))

@[simp]
theorem join_nil (a : α) (S) : join ((a, nil), S) = (a, Sequence.join S) :=
  rfl

@[simp]
theorem join_cons (a b : α) (s S) :
    join ((a, Sequence.cons b s), S) = (a, Sequence.join (Sequence.cons (b, s) S)) := by
  dsimp [join]; rw [destruct_cons]

/-- The `return` operator for the `Sequence1` monad,
  which produces a singleton sequence. -/
def ret (a : α) : Sequence1 α :=
  (a, nil)

instance [Inhabited α] : Inhabited (Sequence1 α) :=
  ⟨ret default⟩

/-- The `bind` operator for the `Sequence1` monad,
  which maps `f` on each element of `s` and appends the results together.
  (Not all of `s` may be evaluated, because the first few elements of `s`
  may already produce an infinite result.) -/
def bind (s : Sequence1 α) (f : α → Sequence1 β) : Sequence1 β :=
  join (map f s)

@[simp]
theorem join_map_ret (s : Sequence α) : Sequence.join (Sequence.map ret s) = s := by
  apply coinduction2 s; intro s; cases s <;> simp [ret]

@[simp]
theorem bind_ret (f : α → β) : ∀ s, bind s (ret ∘ f) = map f s
  | ⟨a, s⟩ => by
    dsimp [bind, map]
    -- Porting note: Was `rw [map_comp]; simp [Function.comp, ret]`
    rw [map_comp, ret]
    simp

@[simp]
theorem ret_bind (a : α) (f : α → Sequence1 β) : bind (ret a) f = f a := by
  simp only [bind, map, ret.eq_1, map_nil]
  cases' f a with a s
  cases s <;> simp

@[simp]
theorem map_join' (f : α → β) (S) :
    Sequence.map f (Sequence.join S) = Sequence.join (Sequence.map (map f) S) := by
  apply
    Sequence.eq_of_bisim fun s1 s2 =>
      ∃ s S,
        s1 = Sequence.append s (Sequence.map f (Sequence.join S)) ∧
          s2 = append s (Sequence.join (Sequence.map (map f) S))
  · rintro s1 s2 ⟨s, S, rfl, rfl⟩
    cases s with simp
    | nil =>
      cases S with simp
      | cons x S =>
        cases' x with a s
        simpa [map] using ⟨_, _, rfl, rfl⟩
    | cons _ s =>
      exact ⟨s, S, rfl, rfl⟩
  · refine ⟨nil, S, ?_, ?_⟩ <;> simp

@[simp]
theorem map_join (f : α → β) : ∀ S, map f (join S) = join (map (map f) S)
  | ((a, s), S) => by cases s <;> simp [map]

@[simp]
theorem join_join (SS : Sequence (Sequence1 (Sequence1 α))) :
    Sequence.join (Sequence.join SS) = Sequence.join (Sequence.map join SS) := by
  apply
    Sequence.eq_of_bisim fun s1 s2 =>
      ∃ s SS,
        s1 = Sequence.append s (Sequence.join (Sequence.join SS)) ∧
          s2 = Sequence.append s (Sequence.join (Sequence.map join SS))
  · rintro s1 s2 ⟨s, SS, rfl, rfl⟩
    cases s with simp
    | nil =>
      cases SS with simp
      | cons S SS =>
        cases' S with s S; cases' s with x s
        simp only [Sequence.join_cons, join_append, destruct_cons]
        cases s with simp
        | nil => exact ⟨_, _, rfl, rfl⟩
        | cons x s =>
          refine ⟨Sequence.cons x (append s (Sequence.join S)), SS, ?_, ?_⟩ <;> simp
    | cons _ s =>
      exact ⟨s, SS, rfl, rfl⟩
  · refine ⟨nil, SS, ?_, ?_⟩ <;> simp

@[simp]
theorem bind_assoc (s : Sequence1 α) (f : α → Sequence1 β) (g : β → Sequence1 γ) :
    bind (bind s f) g = bind s fun x : α => bind (f x) g := by
  cases' s with a s
  -- porting note (#10745): was `simp [bind, map]`.
  simp only [bind, map_pair, map_join]
  rw [← map_comp]
  simp only [show (fun x => join (map g (f x))) = join ∘ (map g ∘ f) from rfl]
  rw [map_comp _ join]
  generalize Sequence.map (map g ∘ f) s = SS
  rcases map g (f a) with ⟨⟨a, s⟩, S⟩
  cases s <;> cases S <;> simp
  next x_1 _ =>
    cases' x_1 with x t
    cases t <;> simp
  next _ _ x_1 _ =>
    cases' x_1 with y t; simp

instance monad : Monad Sequence1 where
  map := @map
  pure := @ret
  bind := @bind

instance lawfulMonad : LawfulMonad Sequence1 := LawfulMonad.mk'
  (id_map := @map_id)
  (bind_pure_comp := @bind_ret)
  (pure_bind := @ret_bind)
  (bind_assoc := @bind_assoc)

end Sequence1
