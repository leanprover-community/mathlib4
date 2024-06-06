/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Data.LazyList
import Mathlib.Data.Option.NAry
import Mathlib.Data.Seq.Computation

#align_import data.seq.seq from "leanprover-community/mathlib"@"a7e36e48519ab281320c4d192da6a7b348ce40ad"

/-!
# Possibly infinite lists

This file provides a `Seq α` type representing possibly infinite lists (referred here as sequences).
  It is encoded as an infinite stream of options such that if `f n = none`, then
  `f m = none` for all `m ≥ n`.
-/

namespace Stream'

universe u v w

/-
coinductive seq (α : Type u) : Type u
| nil : seq α
| cons : α → seq α → seq α
-/
/-- A stream `s : Option α` is a sequence if `s.get n = none` implies `s.get (n + 1) = none`.
-/
def IsSeq {α : Type u} (s : Stream' (Option α)) : Prop :=
  ∀ {n : ℕ}, s n = none → s (n + 1) = none
#align stream.is_seq Stream'.IsSeq

/-- `Seq α` is the type of possibly infinite lists (referred here as sequences).
  It is encoded as an infinite stream of options such that if `f n = none`, then
  `f m = none` for all `m ≥ n`. -/
def Seq (α : Type u) : Type u :=
  { f : Stream' (Option α) // f.IsSeq }
#align stream.seq Stream'.Seq

/-- `Seq1 α` is the type of nonempty sequences. -/
def Seq1 (α) :=
  α × Seq α
#align stream.seq1 Stream'.Seq1

namespace Seq

variable {α : Type u} {β : Type v} {γ : Type w}

/-- The empty sequence -/
def nil : Seq α :=
  ⟨Stream'.const none, fun {_} _ => rfl⟩
#align stream.seq.nil Stream'.Seq.nil

instance : Inhabited (Seq α) :=
  ⟨nil⟩

/-- Prepend an element to a sequence -/
def cons (a : α) (s : Seq α) : Seq α :=
  ⟨some a::s.1, by
    rintro (n | _) h
    · contradiction
    · exact s.2 h⟩
#align stream.seq.cons Stream'.Seq.cons

@[simp]
theorem val_cons (s : Seq α) (x : α) : (cons x s).val = some x::s.val :=
  rfl
#align stream.seq.val_cons Stream'.Seq.val_cons

/-- Get the nth element of a sequence (if it exists) -/
def get? : Seq α → ℕ → Option α :=
  Subtype.val
#align stream.seq.nth Stream'.Seq.get?

@[simp]
theorem get?_mk (f hf) : @get? α ⟨f, hf⟩ = f :=
  rfl
#align stream.seq.nth_mk Stream'.Seq.get?_mk

@[simp]
theorem get?_nil (n : ℕ) : (@nil α).get? n = none :=
  rfl
#align stream.seq.nth_nil Stream'.Seq.get?_nil

@[simp]
theorem get?_cons_zero (a : α) (s : Seq α) : (cons a s).get? 0 = some a :=
  rfl
#align stream.seq.nth_cons_zero Stream'.Seq.get?_cons_zero

@[simp]
theorem get?_cons_succ (a : α) (s : Seq α) (n : ℕ) : (cons a s).get? (n + 1) = s.get? n :=
  rfl
#align stream.seq.nth_cons_succ Stream'.Seq.get?_cons_succ

@[ext]
protected theorem ext {s t : Seq α} (h : ∀ n : ℕ, s.get? n = t.get? n) : s = t :=
  Subtype.eq <| funext h
#align stream.seq.ext Stream'.Seq.ext

theorem cons_injective2 : Function.Injective2 (cons : α → Seq α → Seq α) := fun x y s t h =>
  ⟨by rw [← Option.some_inj, ← get?_cons_zero, h, get?_cons_zero],
    Seq.ext fun n => by simp_rw [← get?_cons_succ x s n, h, get?_cons_succ]⟩
#align stream.seq.cons_injective2 Stream'.Seq.cons_injective2

theorem cons_left_injective (s : Seq α) : Function.Injective fun x => cons x s :=
  cons_injective2.left _
#align stream.seq.cons_left_injective Stream'.Seq.cons_left_injective

theorem cons_right_injective (x : α) : Function.Injective (cons x) :=
  cons_injective2.right _
#align stream.seq.cons_right_injective Stream'.Seq.cons_right_injective

/-- A sequence has terminated at position `n` if the value at position `n` equals `none`. -/
def TerminatedAt (s : Seq α) (n : ℕ) : Prop :=
  s.get? n = none
#align stream.seq.terminated_at Stream'.Seq.TerminatedAt

/-- It is decidable whether a sequence terminates at a given position. -/
instance terminatedAtDecidable (s : Seq α) (n : ℕ) : Decidable (s.TerminatedAt n) :=
  decidable_of_iff' (s.get? n).isNone <| by unfold TerminatedAt; cases s.get? n <;> simp
#align stream.seq.terminated_at_decidable Stream'.Seq.terminatedAtDecidable

/-- A sequence terminates if there is some position `n` at which it has terminated. -/
def Terminates (s : Seq α) : Prop :=
  ∃ n : ℕ, s.TerminatedAt n
#align stream.seq.terminates Stream'.Seq.Terminates

theorem not_terminates_iff {s : Seq α} : ¬s.Terminates ↔ ∀ n, (s.get? n).isSome := by
  simp only [Terminates, TerminatedAt, ← Ne.eq_def, Option.ne_none_iff_isSome, not_exists, iff_self]
#align stream.seq.not_terminates_iff Stream'.Seq.not_terminates_iff

/-- Functorial action of the functor `Option (α × _)` -/
@[simp]
def omap (f : β → γ) : Option (α × β) → Option (α × γ)
  | none => none
  | some (a, b) => some (a, f b)
#align stream.seq.omap Stream'.Seq.omap

/-- Get the first element of a sequence -/
def head (s : Seq α) : Option α :=
  get? s 0
#align stream.seq.head Stream'.Seq.head

/-- Get the tail of a sequence (or `nil` if the sequence is `nil`) -/
def tail (s : Seq α) : Seq α :=
  ⟨s.1.tail, fun n' => by
    cases' s with f al
    exact al n'⟩
#align stream.seq.tail Stream'.Seq.tail

/-- member definition for `Seq`-/
protected def Mem (a : α) (s : Seq α) :=
  some a ∈ s.1
#align stream.seq.mem Stream'.Seq.Mem

instance : Membership α (Seq α) :=
  ⟨Seq.Mem⟩

theorem le_stable (s : Seq α) {m n} (h : m ≤ n) : s.get? m = none → s.get? n = none := by
  cases' s with f al
  induction' h with n _ IH
  exacts [id, fun h2 => al (IH h2)]
#align stream.seq.le_stable Stream'.Seq.le_stable

/-- If a sequence terminated at position `n`, it also terminated at `m ≥ n`. -/
theorem terminated_stable : ∀ (s : Seq α) {m n : ℕ}, m ≤ n → s.TerminatedAt m → s.TerminatedAt n :=
  le_stable
#align stream.seq.terminated_stable Stream'.Seq.terminated_stable

/-- If `s.get? n = some aₙ` for some value `aₙ`, then there is also some value `aₘ` such
that `s.get? = some aₘ` for `m ≤ n`.
-/
theorem ge_stable (s : Seq α) {aₙ : α} {n m : ℕ} (m_le_n : m ≤ n)
    (s_nth_eq_some : s.get? n = some aₙ) : ∃ aₘ : α, s.get? m = some aₘ :=
  have : s.get? n ≠ none := by simp [s_nth_eq_some]
  have : s.get? m ≠ none := mt (s.le_stable m_le_n) this
  Option.ne_none_iff_exists'.mp this
#align stream.seq.ge_stable Stream'.Seq.ge_stable

theorem not_mem_nil (a : α) : a ∉ @nil α := fun ⟨_, (h : some a = none)⟩ => by injection h
#align stream.seq.not_mem_nil Stream'.Seq.not_mem_nil

theorem mem_cons (a : α) : ∀ s : Seq α, a ∈ cons a s
  | ⟨_, _⟩ => Stream'.mem_cons (some a) _
#align stream.seq.mem_cons Stream'.Seq.mem_cons

theorem mem_cons_of_mem (y : α) {a : α} : ∀ {s : Seq α}, a ∈ s → a ∈ cons y s
  | ⟨_, _⟩ => Stream'.mem_cons_of_mem (some y)
#align stream.seq.mem_cons_of_mem Stream'.Seq.mem_cons_of_mem

theorem eq_or_mem_of_mem_cons {a b : α} : ∀ {s : Seq α}, a ∈ cons b s → a = b ∨ a ∈ s
  | ⟨f, al⟩, h => (Stream'.eq_or_mem_of_mem_cons h).imp_left fun h => by injection h
#align stream.seq.eq_or_mem_of_mem_cons Stream'.Seq.eq_or_mem_of_mem_cons

@[simp]
theorem mem_cons_iff {a b : α} {s : Seq α} : a ∈ cons b s ↔ a = b ∨ a ∈ s :=
  ⟨eq_or_mem_of_mem_cons, by rintro (rfl | m) <;> [apply mem_cons; exact mem_cons_of_mem _ m]⟩
#align stream.seq.mem_cons_iff Stream'.Seq.mem_cons_iff

/-- Destructor for a sequence, resulting in either `none` (for `nil`) or
  `some (a, s)` (for `cons a s`). -/
def destruct (s : Seq α) : Option (Seq1 α) :=
  (fun a' => (a', s.tail)) <$> get? s 0
#align stream.seq.destruct Stream'.Seq.destruct

theorem destruct_eq_nil {s : Seq α} : destruct s = none → s = nil := by
  dsimp [destruct]
  induction' f0 : get? s 0 <;> intro h
  · apply Subtype.eq
    funext n
    induction' n with n IH
    exacts [f0, s.2 IH]
  · contradiction
#align stream.seq.destruct_eq_nil Stream'.Seq.destruct_eq_nil

theorem destruct_eq_cons {s : Seq α} {a s'} : destruct s = some (a, s') → s = cons a s' := by
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
#align stream.seq.destruct_eq_cons Stream'.Seq.destruct_eq_cons

@[simp]
theorem destruct_nil : destruct (nil : Seq α) = none :=
  rfl
#align stream.seq.destruct_nil Stream'.Seq.destruct_nil

@[simp]
theorem destruct_cons (a : α) : ∀ s, destruct (cons a s) = some (a, s)
  | ⟨f, al⟩ => by
    unfold cons destruct Functor.map
    apply congr_arg fun s => some (a, s)
    apply Subtype.eq; dsimp [tail]
#align stream.seq.destruct_cons Stream'.Seq.destruct_cons

-- Porting note: needed universe annotation to avoid universe issues
theorem head_eq_destruct (s : Seq α) : head.{u} s = Prod.fst.{u} <$> destruct.{u} s := by
  unfold destruct head; cases get? s 0 <;> rfl
#align stream.seq.head_eq_destruct Stream'.Seq.head_eq_destruct

@[simp]
theorem head_nil : head (nil : Seq α) = none :=
  rfl
#align stream.seq.head_nil Stream'.Seq.head_nil

@[simp]
theorem head_cons (a : α) (s) : head (cons a s) = some a := by
  rw [head_eq_destruct, destruct_cons, Option.map_eq_map, Option.map_some']
#align stream.seq.head_cons Stream'.Seq.head_cons

@[simp]
theorem tail_nil : tail (nil : Seq α) = nil :=
  rfl
#align stream.seq.tail_nil Stream'.Seq.tail_nil

@[simp]
theorem tail_cons (a : α) (s) : tail (cons a s) = s := by
  cases' s with f al
  apply Subtype.eq
  dsimp [tail, cons]
#align stream.seq.tail_cons Stream'.Seq.tail_cons

@[simp]
theorem get?_tail (s : Seq α) (n) : get? (tail s) n = get? s (n + 1) :=
  rfl
#align stream.seq.nth_tail Stream'.Seq.get?_tail

/-- Recursion principle for sequences, compare with `List.recOn`. -/
def recOn {C : Seq α → Sort v} (s : Seq α) (h1 : C nil) (h2 : ∀ x s, C (cons x s)) :
    C s := by
  cases' H : destruct s with v
  · rw [destruct_eq_nil H]
    apply h1
  · cases' v with a s'
    rw [destruct_eq_cons H]
    apply h2
#align stream.seq.rec_on Stream'.Seq.recOn

theorem mem_rec_on {C : Seq α → Prop} {a s} (M : a ∈ s)
    (h1 : ∀ b s', a = b ∨ C s' → C (cons b s')) : C s := by
  cases' M with k e; unfold Stream'.get at e
  induction' k with k IH generalizing s
  · have TH : s = cons a (tail s) := by
      apply destruct_eq_cons
      unfold destruct get? Functor.map
      rw [← e]
      rfl
    rw [TH]
    apply h1 _ _ (Or.inl rfl)
  -- Porting note: had to reshuffle `intro`
  revert e; apply s.recOn _ fun b s' => _
  · intro e; injection e
  · intro b s' e
    have h_eq : (cons b s').val (Nat.succ k) = s'.val k := by cases s'; rfl
    rw [h_eq] at e
    apply h1 _ _ (Or.inr (IH e))
#align stream.seq.mem_rec_on Stream'.Seq.mem_rec_on

/-- Corecursor over pairs of `Option` values-/
def Corec.f (f : β → Option (α × β)) : Option β → Option α × Option β
  | none => (none, none)
  | some b =>
    match f b with
    | none => (none, none)
    | some (a, b') => (some a, some b')
set_option linter.uppercaseLean3 false in
#align stream.seq.corec.F Stream'.Seq.Corec.f

/-- Corecursor for `Seq α` as a coinductive type. Iterates `f` to produce new elements
  of the sequence until `none` is obtained. -/
def corec (f : β → Option (α × β)) (b : β) : Seq α := by
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
    revert h; cases' h₁: f b with s <;> intro h
    · rfl
    · cases' s with a b'
      contradiction
  · rw [Stream'.corec'_eq (Corec.f f) (Corec.f f o).2, Stream'.corec'_eq (Corec.f f) o]
    exact IH (Corec.f f o).2
#align stream.seq.corec Stream'.Seq.corec

@[simp]
theorem corec_eq (f : β → Option (α × β)) (b : β) :
    destruct (corec f b) = omap (corec f) (f b) := by
  dsimp [corec, destruct, get]
  -- Porting note: next two lines were `change`...`with`...
  have h: Stream'.corec' (Corec.f f) (some b) 0 = (Corec.f f (some b)).1 := rfl
  rw [h]
  dsimp [Corec.f]
  induction' h : f b with s; · rfl
  cases' s with a b'; dsimp [Corec.f]
  apply congr_arg fun b' => some (a, b')
  apply Subtype.eq
  dsimp [corec, tail]
  rw [Stream'.corec'_eq, Stream'.tail_cons]
  dsimp [Corec.f]; rw [h]
#align stream.seq.corec_eq Stream'.Seq.corec_eq

section Bisim

variable (R : Seq α → Seq α → Prop)

local infixl:50 " ~ " => R

/-- Bisimilarity relation over `Option` of `Seq1 α`-/
def BisimO : Option (Seq1 α) → Option (Seq1 α) → Prop
  | none, none => True
  | some (a, s), some (a', s') => a = a' ∧ R s s'
  | _, _ => False
#align stream.seq.bisim_o Stream'.Seq.BisimO

attribute [simp] BisimO

/-- a relation is bisimilar if it meets the `BisimO` test-/
def IsBisimulation :=
  ∀ ⦃s₁ s₂⦄, s₁ ~ s₂ → BisimO R (destruct s₁) (destruct s₂)
#align stream.seq.is_bisimulation Stream'.Seq.IsBisimulation

-- If two streams are bisimilar, then they are equal
theorem eq_of_bisim (bisim : IsBisimulation R) {s₁ s₂} (r : s₁ ~ s₂) : s₁ = s₂ := by
  apply Subtype.eq
  apply Stream'.eq_of_bisim fun x y => ∃ s s' : Seq α, s.1 = x ∧ s'.1 = y ∧ R s s'
  · dsimp [Stream'.IsBisimulation]
    intro t₁ t₂ e
    exact
    match t₁, t₂, e with
    | _, _, ⟨s, s', rfl, rfl, r⟩ => by
      suffices head s = head s' ∧ R (tail s) (tail s') from
        And.imp id (fun r => ⟨tail s, tail s', by cases s; rfl, by cases s'; rfl, r⟩) this
      have := bisim r; revert r this
      apply recOn s _ _ <;> apply recOn s' _ _
      · intro r _
        constructor
        · rfl
        · assumption
      · intro x s _ this
        rw [destruct_nil, destruct_cons] at this
        exact False.elim this
      · intro x s _ this
        rw [destruct_nil, destruct_cons] at this
        exact False.elim this
      · intro x s x' s' _ this
        rw [destruct_cons, destruct_cons] at this
        rw [head_cons, head_cons, tail_cons, tail_cons]
        cases' this with h1 h2
        constructor
        · rw [h1]
        · exact h2
  · exact ⟨s₁, s₂, rfl, rfl, r⟩
#align stream.seq.eq_of_bisim Stream'.Seq.eq_of_bisim

end Bisim

theorem coinduction :
    ∀ {s₁ s₂ : Seq α},
      head s₁ = head s₂ →
        (∀ (β : Type u) (fr : Seq α → β), fr s₁ = fr s₂ → fr (tail s₁) = fr (tail s₂)) → s₁ = s₂
  | _, _, hh, ht =>
    Subtype.eq (Stream'.coinduction hh fun β fr => ht β fun s => fr s.1)
#align stream.seq.coinduction Stream'.Seq.coinduction

theorem coinduction2 (s) (f g : Seq α → Seq β)
    (H :
      ∀ s,
        BisimO (fun s1 s2 : Seq β => ∃ s : Seq α, s1 = f s ∧ s2 = g s) (destruct (f s))
          (destruct (g s))) :
    f s = g s := by
  refine eq_of_bisim (fun s1 s2 => ∃ s, s1 = f s ∧ s2 = g s) ?_ ⟨s, rfl, rfl⟩
  intro s1 s2 h; rcases h with ⟨s, h1, h2⟩
  rw [h1, h2]; apply H
#align stream.seq.coinduction2 Stream'.Seq.coinduction2

/-- Embed a list as a sequence -/
@[coe]
def ofList (l : List α) : Seq α :=
  ⟨List.get? l, fun {n} h => by
    rw [List.get?_eq_none] at h ⊢
    exact h.trans (Nat.le_succ n)⟩
#align stream.seq.of_list Stream'.Seq.ofList

instance coeList : Coe (List α) (Seq α) :=
  ⟨ofList⟩
#align stream.seq.coe_list Stream'.Seq.coeList

@[simp]
theorem ofList_nil : ofList [] = (nil : Seq α) :=
  rfl
#align stream.seq.of_list_nil Stream'.Seq.ofList_nil

@[simp]
theorem ofList_get (l : List α) (n : ℕ) : (ofList l).get? n = l.get? n :=
  rfl
#align stream.seq.of_list_nth Stream'.Seq.ofList_get

@[simp]
theorem ofList_cons (a : α) (l : List α) : ofList (a::l) = cons a (ofList l) := by
  ext1 (_ | n) <;> rfl
#align stream.seq.of_list_cons Stream'.Seq.ofList_cons

/-- Embed an infinite stream as a sequence -/
@[coe]
def ofStream (s : Stream' α) : Seq α :=
  ⟨s.map some, fun {n} h => by contradiction⟩
#align stream.seq.of_stream Stream'.Seq.ofStream

instance coeStream : Coe (Stream' α) (Seq α) :=
  ⟨ofStream⟩
#align stream.seq.coe_stream Stream'.Seq.coeStream

/-- Embed a `LazyList α` as a sequence. Note that even though this
  is non-meta, it will produce infinite sequences if used with
  cyclic `LazyList`s created by meta constructions. -/
def ofLazyList : LazyList α → Seq α :=
  corec fun l =>
    match l with
    | LazyList.nil => none
    | LazyList.cons a l' => some (a, l'.get)
#align stream.seq.of_lazy_list Stream'.Seq.ofLazyList

instance coeLazyList : Coe (LazyList α) (Seq α) :=
  ⟨ofLazyList⟩
#align stream.seq.coe_lazy_list Stream'.Seq.coeLazyList

/-- Translate a sequence into a `LazyList`. Since `LazyList` and `List`
  are isomorphic as non-meta types, this function is necessarily meta. -/
unsafe def toLazyList : Seq α → LazyList α
  | s =>
    match destruct s with
    | none => LazyList.nil
    | some (a, s') => LazyList.cons a (toLazyList s')
#align stream.seq.to_lazy_list Stream'.Seq.toLazyList

/-- Translate a sequence to a list. This function will run forever if
  run on an infinite sequence. -/
unsafe def forceToList (s : Seq α) : List α :=
  (toLazyList s).toList
#align stream.seq.force_to_list Stream'.Seq.forceToList

/-- The sequence of natural numbers some 0, some 1, ... -/
def nats : Seq ℕ :=
  Stream'.nats
#align stream.seq.nats Stream'.Seq.nats

@[simp]
theorem nats_get? (n : ℕ) : nats.get? n = some n :=
  rfl
#align stream.seq.nats_nth Stream'.Seq.nats_get?

/-- Append two sequences. If `s₁` is infinite, then `s₁ ++ s₂ = s₁`,
  otherwise it puts `s₂` at the location of the `nil` in `s₁`. -/
def append (s₁ s₂ : Seq α) : Seq α :=
  @corec α (Seq α × Seq α)
    (fun ⟨s₁, s₂⟩ =>
      match destruct s₁ with
      | none => omap (fun s₂ => (nil, s₂)) (destruct s₂)
      | some (a, s₁') => some (a, s₁', s₂))
    (s₁, s₂)
#align stream.seq.append Stream'.Seq.append

/-- Map a function over a sequence. -/
def map (f : α → β) : Seq α → Seq β
  | ⟨s, al⟩ =>
    ⟨s.map (Option.map f), fun {n} => by
      dsimp [Stream'.map, Stream'.get]
      induction' e : s n with e <;> intro
      · rw [al e]
        assumption
      · contradiction⟩
#align stream.seq.map Stream'.Seq.map

/-- Flatten a sequence of sequences. (It is required that the
  sequences be nonempty to ensure productivity; in the case
  of an infinite sequence of `nil`, the first element is never
  generated.) -/
def join : Seq (Seq1 α) → Seq α :=
  corec fun S =>
    match destruct S with
    | none => none
    | some ((a, s), S') =>
      some
        (a,
          match destruct s with
          | none => S'
          | some s' => cons s' S')
#align stream.seq.join Stream'.Seq.join

/-- Remove the first `n` elements from the sequence. -/
def drop (s : Seq α) : ℕ → Seq α
  | 0 => s
  | n + 1 => tail (drop s n)
#align stream.seq.drop Stream'.Seq.drop

attribute [simp] drop

/-- Take the first `n` elements of the sequence (producing a list) -/
def take : ℕ → Seq α → List α
  | 0, _ => []
  | n + 1, s =>
    match destruct s with
    | none => []
    | some (x, r) => List.cons x (take n r)
#align stream.seq.take Stream'.Seq.take

/-- Split a sequence at `n`, producing a finite initial segment
  and an infinite tail. -/
def splitAt : ℕ → Seq α → List α × Seq α
  | 0, s => ([], s)
  | n + 1, s =>
    match destruct s with
    | none => ([], nil)
    | some (x, s') =>
      let (l, r) := splitAt n s'
      (List.cons x l, r)
#align stream.seq.split_at Stream'.Seq.splitAt

section ZipWith

/-- Combine two sequences with a function -/
def zipWith (f : α → β → γ) (s₁ : Seq α) (s₂ : Seq β) : Seq γ :=
  ⟨fun n => Option.map₂ f (s₁.get? n) (s₂.get? n), fun {_} hn =>
    Option.map₂_eq_none_iff.2 <| (Option.map₂_eq_none_iff.1 hn).imp s₁.2 s₂.2⟩
#align stream.seq.zip_with Stream'.Seq.zipWith

variable {s : Seq α} {s' : Seq β} {n : ℕ}

@[simp]
theorem get?_zipWith (f : α → β → γ) (s s' n) :
    (zipWith f s s').get? n = Option.map₂ f (s.get? n) (s'.get? n) :=
  rfl
#align stream.seq.nth_zip_with Stream'.Seq.get?_zipWith

end ZipWith

/-- Pair two sequences into a sequence of pairs -/
def zip : Seq α → Seq β → Seq (α × β) :=
  zipWith Prod.mk
#align stream.seq.zip Stream'.Seq.zip

theorem get?_zip (s : Seq α) (t : Seq β) (n : ℕ) :
    get? (zip s t) n = Option.map₂ Prod.mk (get? s n) (get? t n) :=
  get?_zipWith _ _ _ _
#align stream.seq.nth_zip Stream'.Seq.get?_zip

/-- Separate a sequence of pairs into two sequences -/
def unzip (s : Seq (α × β)) : Seq α × Seq β :=
  (map Prod.fst s, map Prod.snd s)
#align stream.seq.unzip Stream'.Seq.unzip

/-- Enumerate a sequence by tagging each element with its index. -/
def enum (s : Seq α) : Seq (ℕ × α) :=
  Seq.zip nats s
#align stream.seq.enum Stream'.Seq.enum

@[simp]
theorem get?_enum (s : Seq α) (n : ℕ) : get? (enum s) n = Option.map (Prod.mk n) (get? s n) :=
  get?_zip _ _ _
#align stream.seq.nth_enum Stream'.Seq.get?_enum

@[simp]
theorem enum_nil : enum (nil : Seq α) = nil :=
  rfl
#align stream.seq.enum_nil Stream'.Seq.enum_nil

/-- Convert a sequence which is known to terminate into a list -/
def toList (s : Seq α) (h : s.Terminates) : List α :=
  take (Nat.find h) s
#align stream.seq.to_list Stream'.Seq.toList

/-- Convert a sequence which is known not to terminate into a stream -/
def toStream (s : Seq α) (h : ¬s.Terminates) : Stream' α := fun n =>
  Option.get _ <| not_terminates_iff.1 h n
#align stream.seq.to_stream Stream'.Seq.toStream

/-- Convert a sequence into either a list or a stream depending on whether
  it is finite or infinite. (Without decidability of the infiniteness predicate,
  this is not constructively possible.) -/
def toListOrStream (s : Seq α) [Decidable s.Terminates] : Sum (List α) (Stream' α) :=
  if h : s.Terminates then Sum.inl (toList s h) else Sum.inr (toStream s h)
#align stream.seq.to_list_or_stream Stream'.Seq.toListOrStream

@[simp]
theorem nil_append (s : Seq α) : append nil s = s := by
  apply coinduction2; intro s
  dsimp [append]; rw [corec_eq]
  dsimp [append]; apply recOn s _ _
  · trivial
  · intro x s
    rw [destruct_cons]
    dsimp
    exact ⟨rfl, s, rfl, rfl⟩
#align stream.seq.nil_append Stream'.Seq.nil_append

@[simp]
theorem cons_append (a : α) (s t) : append (cons a s) t = cons a (append s t) :=
  destruct_eq_cons <| by
    dsimp [append]; rw [corec_eq]
    dsimp [append]; rw [destruct_cons]
#align stream.seq.cons_append Stream'.Seq.cons_append

@[simp]
theorem append_nil (s : Seq α) : append s nil = s := by
  apply coinduction2 s; intro s
  apply recOn s _ _
  · trivial
  · intro x s
    rw [cons_append, destruct_cons, destruct_cons]
    dsimp
    exact ⟨rfl, s, rfl, rfl⟩
#align stream.seq.append_nil Stream'.Seq.append_nil

@[simp]
theorem append_assoc (s t u : Seq α) : append (append s t) u = append s (append t u) := by
  apply eq_of_bisim fun s1 s2 => ∃ s t u, s1 = append (append s t) u ∧ s2 = append s (append t u)
  · intro s1 s2 h
    exact
      match s1, s2, h with
      | _, _, ⟨s, t, u, rfl, rfl⟩ => by
        apply recOn s <;> simp
        · apply recOn t <;> simp
          · apply recOn u <;> simp
            · intro _ u
              refine ⟨nil, nil, u, ?_, ?_⟩ <;> simp
          · intro _ t
            refine ⟨nil, t, u, ?_, ?_⟩ <;> simp
        · intro _ s
          exact ⟨s, t, u, rfl, rfl⟩
  · exact ⟨s, t, u, rfl, rfl⟩
#align stream.seq.append_assoc Stream'.Seq.append_assoc

@[simp]
theorem map_nil (f : α → β) : map f nil = nil :=
  rfl
#align stream.seq.map_nil Stream'.Seq.map_nil

@[simp]
theorem map_cons (f : α → β) (a) : ∀ s, map f (cons a s) = cons (f a) (map f s)
  | ⟨s, al⟩ => by apply Subtype.eq; dsimp [cons, map]; rw [Stream'.map_cons]; rfl
#align stream.seq.map_cons Stream'.Seq.map_cons

@[simp]
theorem map_id : ∀ s : Seq α, map id s = s
  | ⟨s, al⟩ => by
    apply Subtype.eq; dsimp [map]
    rw [Option.map_id, Stream'.map_id]
#align stream.seq.map_id Stream'.Seq.map_id

@[simp]
theorem map_tail (f : α → β) : ∀ s, map f (tail s) = tail (map f s)
  | ⟨s, al⟩ => by apply Subtype.eq; dsimp [tail, map]
#align stream.seq.map_tail Stream'.Seq.map_tail

theorem map_comp (f : α → β) (g : β → γ) : ∀ s : Seq α, map (g ∘ f) s = map g (map f s)
  | ⟨s, al⟩ => by
    apply Subtype.eq; dsimp [map]
    apply congr_arg fun f : _ → Option γ => Stream'.map f s
    ext ⟨⟩ <;> rfl
#align stream.seq.map_comp Stream'.Seq.map_comp

@[simp]
theorem map_append (f : α → β) (s t) : map f (append s t) = append (map f s) (map f t) := by
  apply
    eq_of_bisim (fun s1 s2 => ∃ s t, s1 = map f (append s t) ∧ s2 = append (map f s) (map f t)) _
      ⟨s, t, rfl, rfl⟩
  intro s1 s2 h
  exact
    match s1, s2, h with
    | _, _, ⟨s, t, rfl, rfl⟩ => by
      apply recOn s <;> simp
      · apply recOn t <;> simp
        · intro _ t
          refine ⟨nil, t, ?_, ?_⟩ <;> simp
      · intro _ s
        exact ⟨s, t, rfl, rfl⟩
#align stream.seq.map_append Stream'.Seq.map_append

@[simp]
theorem map_get? (f : α → β) : ∀ s n, get? (map f s) n = (get? s n).map f
  | ⟨_, _⟩, _ => rfl
#align stream.seq.map_nth Stream'.Seq.map_get?

instance : Functor Seq where map := @map

instance : LawfulFunctor Seq where
  id_map := @map_id
  comp_map := @map_comp
  map_const := rfl

@[simp]
theorem join_nil : join nil = (nil : Seq α) :=
  destruct_eq_nil rfl
#align stream.seq.join_nil Stream'.Seq.join_nil

--@[simp] -- Porting note: simp can prove: `join_cons` is more general
theorem join_cons_nil (a : α) (S) : join (cons (a, nil) S) = cons a (join S) :=
  destruct_eq_cons <| by simp [join]
#align stream.seq.join_cons_nil Stream'.Seq.join_cons_nil

--@[simp] -- Porting note: simp can prove: `join_cons` is more general
theorem join_cons_cons (a b : α) (s S) :
    join (cons (a, cons b s) S) = cons a (join (cons (b, s) S)) :=
  destruct_eq_cons <| by simp [join]
#align stream.seq.join_cons_cons Stream'.Seq.join_cons_cons

@[simp]
theorem join_cons (a : α) (s S) : join (cons (a, s) S) = cons a (append s (join S)) := by
  apply
    eq_of_bisim
      (fun s1 s2 => s1 = s2 ∨ ∃ a s S, s1 = join (cons (a, s) S) ∧ s2 = cons a (append s (join S)))
      _ (Or.inr ⟨a, s, S, rfl, rfl⟩)
  intro s1 s2 h
  exact
    match s1, s2, h with
    | s, _, Or.inl <| Eq.refl s => by
      apply recOn s; · trivial
      · intro x s
        rw [destruct_cons]
        exact ⟨rfl, Or.inl rfl⟩
    | _, _, Or.inr ⟨a, s, S, rfl, rfl⟩ => by
      apply recOn s
      · simp [join_cons_cons, join_cons_nil]
      · intro x s
        simpa [join_cons_cons, join_cons_nil] using Or.inr ⟨x, s, S, rfl, rfl⟩
#align stream.seq.join_cons Stream'.Seq.join_cons

@[simp]
theorem join_append (S T : Seq (Seq1 α)) : join (append S T) = append (join S) (join T) := by
  apply
    eq_of_bisim fun s1 s2 =>
      ∃ s S T, s1 = append s (join (append S T)) ∧ s2 = append s (append (join S) (join T))
  · intro s1 s2 h
    exact
      match s1, s2, h with
      | _, _, ⟨s, S, T, rfl, rfl⟩ => by
        apply recOn s <;> simp
        · apply recOn S <;> simp
          · apply recOn T
            · simp
            · intro s T
              cases' s with a s; simp only [join_cons, destruct_cons, true_and]
              refine ⟨s, nil, T, ?_, ?_⟩ <;> simp
          · intro s S
            cases' s with a s
            simpa using ⟨s, S, T, rfl, rfl⟩
        · intro _ s
          exact ⟨s, S, T, rfl, rfl⟩
  · refine ⟨nil, S, T, ?_, ?_⟩ <;> simp
#align stream.seq.join_append Stream'.Seq.join_append

@[simp]
theorem ofStream_cons (a : α) (s) : ofStream (a::s) = cons a (ofStream s) := by
  apply Subtype.eq; simp only [ofStream, cons]; rw [Stream'.map_cons]
#align stream.seq.of_stream_cons Stream'.Seq.ofStream_cons

@[simp]
theorem ofList_append (l l' : List α) : ofList (l ++ l') = append (ofList l) (ofList l') := by
  induction l <;> simp [*]
#align stream.seq.of_list_append Stream'.Seq.ofList_append

@[simp]
theorem ofStream_append (l : List α) (s : Stream' α) :
    ofStream (l ++ₛ s) = append (ofList l) (ofStream s) := by
  induction l <;> simp [*, Stream'.nil_append_stream, Stream'.cons_append_stream]
#align stream.seq.of_stream_append Stream'.Seq.ofStream_append

/-- Convert a sequence into a list, embedded in a computation to allow for
  the possibility of infinite sequences (in which case the computation
  never returns anything). -/
def toList' {α} (s : Seq α) : Computation (List α) :=
  @Computation.corec (List α) (List α × Seq α)
    (fun ⟨l, s⟩ =>
      match destruct s with
      | none => Sum.inl l.reverse
      | some (a, s') => Sum.inr (a::l, s'))
    ([], s)
#align stream.seq.to_list' Stream'.Seq.toList'

theorem dropn_add (s : Seq α) (m) : ∀ n, drop s (m + n) = drop (drop s m) n
  | 0 => rfl
  | n + 1 => congr_arg tail (dropn_add s _ n)
#align stream.seq.dropn_add Stream'.Seq.dropn_add

theorem dropn_tail (s : Seq α) (n) : drop (tail s) n = drop s (n + 1) := by
  rw [Nat.add_comm]; symm; apply dropn_add
#align stream.seq.dropn_tail Stream'.Seq.dropn_tail

@[simp]
theorem head_dropn (s : Seq α) (n) : head (drop s n) = get? s n := by
  induction' n with n IH generalizing s; · rfl
  rw [← get?_tail, ← dropn_tail]; apply IH
#align stream.seq.head_dropn Stream'.Seq.head_dropn

theorem mem_map (f : α → β) {a : α} : ∀ {s : Seq α}, a ∈ s → f a ∈ map f s
  | ⟨_, _⟩ => Stream'.mem_map (Option.map f)
#align stream.seq.mem_map Stream'.Seq.mem_map

theorem exists_of_mem_map {f} {b : β} : ∀ {s : Seq α}, b ∈ map f s → ∃ a, a ∈ s ∧ f a = b :=
  fun {s} h => by match s with
  | ⟨g, al⟩ =>
    let ⟨o, om, oe⟩ := @Stream'.exists_of_mem_map _ _ (Option.map f) (some b) g h
    cases' o with a
    · injection oe
    · injection oe with h'; exact ⟨a, om, h'⟩
#align stream.seq.exists_of_mem_map Stream'.Seq.exists_of_mem_map

theorem of_mem_append {s₁ s₂ : Seq α} {a : α} (h : a ∈ append s₁ s₂) : a ∈ s₁ ∨ a ∈ s₂ := by
  have := h; revert this
  generalize e : append s₁ s₂ = ss; intro h; revert s₁
  apply mem_rec_on h _
  intro b s' o s₁
  apply s₁.recOn _ fun c t₁ => _
  · intro m _
    apply Or.inr
    simpa using m
  · intro c t₁ m e
    have this := congr_arg destruct e
    cases' show a = c ∨ a ∈ append t₁ s₂ by simpa using m with e' m
    · rw [e']
      exact Or.inl (mem_cons _ _)
    · cases' show c = b ∧ append t₁ s₂ = s' by simpa with i1 i2
      cases' o with e' IH
      · simp [i1, e']
      · exact Or.imp_left (mem_cons_of_mem _) (IH m i2)
#align stream.seq.of_mem_append Stream'.Seq.of_mem_append

theorem mem_append_left {s₁ s₂ : Seq α} {a : α} (h : a ∈ s₁) : a ∈ append s₁ s₂ := by
  apply mem_rec_on h; intros; simp [*]
#align stream.seq.mem_append_left Stream'.Seq.mem_append_left

@[simp]
theorem enum_cons (s : Seq α) (x : α) :
    enum (cons x s) = cons (0, x) (map (Prod.map Nat.succ id) (enum s)) := by
  ext ⟨n⟩ : 1
  · simp
  · simp only [get?_enum, get?_cons_succ, map_get?, Option.map_map]
    congr
#align stream.seq.enum_cons Stream'.Seq.enum_cons

end Seq

namespace Seq1

variable {α : Type u} {β : Type v} {γ : Type w}

open Stream'.Seq

/-- Convert a `Seq1` to a sequence. -/
def toSeq : Seq1 α → Seq α
  | (a, s) => Seq.cons a s
#align stream.seq1.to_seq Stream'.Seq1.toSeq

instance coeSeq : Coe (Seq1 α) (Seq α) :=
  ⟨toSeq⟩
#align stream.seq1.coe_seq Stream'.Seq1.coeSeq

/-- Map a function on a `Seq1` -/
def map (f : α → β) : Seq1 α → Seq1 β
  | (a, s) => (f a, Seq.map f s)
#align stream.seq1.map Stream'.Seq1.map

-- Porting note (#10756): new theorem.
theorem map_pair {f : α → β} {a s} : map f (a, s) = (f a, Seq.map f s) := rfl

theorem map_id : ∀ s : Seq1 α, map id s = s
  | ⟨a, s⟩ => by simp [map]
#align stream.seq1.map_id Stream'.Seq1.map_id

/-- Flatten a nonempty sequence of nonempty sequences -/
def join : Seq1 (Seq1 α) → Seq1 α
  | ((a, s), S) =>
    match destruct s with
    | none => (a, Seq.join S)
    | some s' => (a, Seq.join (Seq.cons s' S))
#align stream.seq1.join Stream'.Seq1.join

@[simp]
theorem join_nil (a : α) (S) : join ((a, nil), S) = (a, Seq.join S) :=
  rfl
#align stream.seq1.join_nil Stream'.Seq1.join_nil

@[simp]
theorem join_cons (a b : α) (s S) :
    join ((a, Seq.cons b s), S) = (a, Seq.join (Seq.cons (b, s) S)) := by
  dsimp [join]; rw [destruct_cons]
#align stream.seq1.join_cons Stream'.Seq1.join_cons

/-- The `return` operator for the `Seq1` monad,
  which produces a singleton sequence. -/
def ret (a : α) : Seq1 α :=
  (a, nil)
#align stream.seq1.ret Stream'.Seq1.ret

instance [Inhabited α] : Inhabited (Seq1 α) :=
  ⟨ret default⟩

/-- The `bind` operator for the `Seq1` monad,
  which maps `f` on each element of `s` and appends the results together.
  (Not all of `s` may be evaluated, because the first few elements of `s`
  may already produce an infinite result.) -/
def bind (s : Seq1 α) (f : α → Seq1 β) : Seq1 β :=
  join (map f s)
#align stream.seq1.bind Stream'.Seq1.bind

@[simp]
theorem join_map_ret (s : Seq α) : Seq.join (Seq.map ret s) = s := by
  apply coinduction2 s; intro s; apply recOn s <;> simp [ret]
#align stream.seq1.join_map_ret Stream'.Seq1.join_map_ret

@[simp]
theorem bind_ret (f : α → β) : ∀ s, bind s (ret ∘ f) = map f s
  | ⟨a, s⟩ => by
    dsimp [bind, map]
    -- Porting note: Was `rw [map_comp]; simp [Function.comp, ret]`
    rw [map_comp, ret]
    simp
#align stream.seq1.bind_ret Stream'.Seq1.bind_ret

@[simp]
theorem ret_bind (a : α) (f : α → Seq1 β) : bind (ret a) f = f a := by
  simp only [bind, map, ret.eq_1, map_nil]
  cases' f a with a s
  apply recOn s <;> intros <;> simp
#align stream.seq1.ret_bind Stream'.Seq1.ret_bind

@[simp]
theorem map_join' (f : α → β) (S) : Seq.map f (Seq.join S) = Seq.join (Seq.map (map f) S) := by
  apply
    Seq.eq_of_bisim fun s1 s2 =>
      ∃ s S,
        s1 = Seq.append s (Seq.map f (Seq.join S)) ∧ s2 = append s (Seq.join (Seq.map (map f) S))
  · intro s1 s2 h
    exact
      match s1, s2, h with
      | _, _, ⟨s, S, rfl, rfl⟩ => by
        apply recOn s <;> simp
        · apply recOn S <;> simp
          · intro x S
            cases' x with a s
            simpa [map] using ⟨_, _, rfl, rfl⟩
        · intro _ s
          exact ⟨s, S, rfl, rfl⟩
  · refine ⟨nil, S, ?_, ?_⟩ <;> simp
#align stream.seq1.map_join' Stream'.Seq1.map_join'

@[simp]
theorem map_join (f : α → β) : ∀ S, map f (join S) = join (map (map f) S)
  | ((a, s), S) => by apply recOn s <;> intros <;> simp [map]
#align stream.seq1.map_join Stream'.Seq1.map_join

@[simp]
theorem join_join (SS : Seq (Seq1 (Seq1 α))) :
    Seq.join (Seq.join SS) = Seq.join (Seq.map join SS) := by
  apply
    Seq.eq_of_bisim fun s1 s2 =>
      ∃ s SS,
        s1 = Seq.append s (Seq.join (Seq.join SS)) ∧ s2 = Seq.append s (Seq.join (Seq.map join SS))
  · intro s1 s2 h
    exact
      match s1, s2, h with
      | _, _, ⟨s, SS, rfl, rfl⟩ => by
        apply recOn s <;> simp
        · apply recOn SS <;> simp
          · intro S SS
            cases' S with s S; cases' s with x s
            simp only [Seq.join_cons, join_append, destruct_cons]
            apply recOn s <;> simp
            · exact ⟨_, _, rfl, rfl⟩
            · intro x s
              refine ⟨Seq.cons x (append s (Seq.join S)), SS, ?_, ?_⟩ <;> simp
        · intro _ s
          exact ⟨s, SS, rfl, rfl⟩
  · refine ⟨nil, SS, ?_, ?_⟩ <;> simp
#align stream.seq1.join_join Stream'.Seq1.join_join

@[simp]
theorem bind_assoc (s : Seq1 α) (f : α → Seq1 β) (g : β → Seq1 γ) :
    bind (bind s f) g = bind s fun x : α => bind (f x) g := by
  cases' s with a s
  -- porting note (#10745): was `simp [bind, map]`.
  simp only [bind, map_pair, map_join]
  rw [← map_comp]
  simp only [show (fun x => join (map g (f x))) = join ∘ (map g ∘ f) from rfl]
  rw [map_comp _ join]
  generalize Seq.map (map g ∘ f) s = SS
  rcases map g (f a) with ⟨⟨a, s⟩, S⟩
  -- Porting note: Instead of `apply recOn s <;> intros`, `induction'` are used to
  --   give names to variables.
  induction' s using recOn with x s_1 <;> induction' S using recOn with x_1 s_2 <;> simp
  · cases' x_1 with x t
    apply recOn t <;> intros <;> simp
  · cases' x_1 with y t; simp
#align stream.seq1.bind_assoc Stream'.Seq1.bind_assoc

instance monad : Monad Seq1 where
  map := @map
  pure := @ret
  bind := @bind
#align stream.seq1.monad Stream'.Seq1.monad

instance lawfulMonad : LawfulMonad Seq1 := LawfulMonad.mk'
  (id_map := @map_id)
  (bind_pure_comp := @bind_ret)
  (pure_bind := @ret_bind)
  (bind_assoc := @bind_assoc)
#align stream.seq1.is_lawful_monad Stream'.Seq1.lawfulMonad

end Seq1

end Stream'
