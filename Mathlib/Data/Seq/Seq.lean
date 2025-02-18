/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Option.NAry
import Mathlib.Data.Seq.Computation
import Mathlib.Data.List.Basic

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

/-- `Seq α` is the type of possibly infinite lists (referred here as sequences).
  It is encoded as an infinite stream of options such that if `f n = none`, then
  `f m = none` for all `m ≥ n`. -/
def Seq (α : Type u) : Type u :=
  { f : Stream' (Option α) // f.IsSeq }

/-- `Seq1 α` is the type of nonempty sequences. -/
def Seq1 (α) :=
  α × Seq α

namespace Seq

variable {α : Type u} {β : Type v} {γ : Type w}

/-- The empty sequence -/
def nil : Seq α :=
  ⟨Stream'.const none, fun {_} _ => rfl⟩

instance : Inhabited (Seq α) :=
  ⟨nil⟩

/-- Prepend an element to a sequence -/
def cons (a : α) (s : Seq α) : Seq α :=
  ⟨some a::s.1, by
    rintro (n | _) h
    · contradiction
    · exact s.2 h⟩

@[simp]
theorem val_cons (s : Seq α) (x : α) : (cons x s).val = some x::s.val :=
  rfl

/-- Get the nth element of a sequence (if it exists) -/
def get? : Seq α → ℕ → Option α :=
  Subtype.val

@[simp]
theorem get?_mk (f hf) : @get? α ⟨f, hf⟩ = f :=
  rfl

@[simp]
theorem get?_nil (n : ℕ) : (@nil α).get? n = none :=
  rfl

@[simp]
theorem get?_cons_zero (a : α) (s : Seq α) : (cons a s).get? 0 = some a :=
  rfl

@[simp]
theorem get?_cons_succ (a : α) (s : Seq α) (n : ℕ) : (cons a s).get? (n + 1) = s.get? n :=
  rfl

@[ext]
protected theorem ext {s t : Seq α} (h : ∀ n : ℕ, s.get? n = t.get? n) : s = t :=
  Subtype.eq <| funext h

theorem cons_injective2 : Function.Injective2 (cons : α → Seq α → Seq α) := fun x y s t h =>
  ⟨by rw [← Option.some_inj, ← get?_cons_zero, h, get?_cons_zero],
    Seq.ext fun n => by simp_rw [← get?_cons_succ x s n, h, get?_cons_succ]⟩

theorem cons_left_injective (s : Seq α) : Function.Injective fun x => cons x s :=
  cons_injective2.left _

theorem cons_right_injective (x : α) : Function.Injective (cons x) :=
  cons_injective2.right _

/-- A sequence has terminated at position `n` if the value at position `n` equals `none`. -/
def TerminatedAt (s : Seq α) (n : ℕ) : Prop :=
  s.get? n = none

/-- It is decidable whether a sequence terminates at a given position. -/
instance terminatedAtDecidable (s : Seq α) (n : ℕ) : Decidable (s.TerminatedAt n) :=
  decidable_of_iff' (s.get? n).isNone <| by unfold TerminatedAt; cases s.get? n <;> simp

/-- A sequence terminates if there is some position `n` at which it has terminated. -/
def Terminates (s : Seq α) : Prop :=
  ∃ n : ℕ, s.TerminatedAt n

theorem not_terminates_iff {s : Seq α} : ¬s.Terminates ↔ ∀ n, (s.get? n).isSome := by
  simp only [Terminates, TerminatedAt, ← Ne.eq_def, Option.ne_none_iff_isSome, not_exists, iff_self]

/-- Functorial action of the functor `Option (α × _)` -/
@[simp]
def omap (f : β → γ) : Option (α × β) → Option (α × γ)
  | none => none
  | some (a, b) => some (a, f b)

/-- Get the first element of a sequence -/
def head (s : Seq α) : Option α :=
  get? s 0

/-- Get the tail of a sequence (or `nil` if the sequence is `nil`) -/
def tail (s : Seq α) : Seq α :=
  ⟨s.1.tail, fun n' => by
    cases' s with f al
    exact al n'⟩

/-- member definition for `Seq`-/
protected def Mem (s : Seq α) (a : α) :=
  some a ∈ s.1

instance : Membership α (Seq α) :=
  ⟨Seq.Mem⟩

theorem le_stable (s : Seq α) {m n} (h : m ≤ n) : s.get? m = none → s.get? n = none := by
  cases' s with f al
  induction' h with n _ IH
  exacts [id, fun h2 => al (IH h2)]

/-- If a sequence terminated at position `n`, it also terminated at `m ≥ n`. -/
theorem terminated_stable : ∀ (s : Seq α) {m n : ℕ}, m ≤ n → s.TerminatedAt m → s.TerminatedAt n :=
  le_stable

/-- If `s.get? n = some aₙ` for some value `aₙ`, then there is also some value `aₘ` such
that `s.get? = some aₘ` for `m ≤ n`.
-/
theorem ge_stable (s : Seq α) {aₙ : α} {n m : ℕ} (m_le_n : m ≤ n)
    (s_nth_eq_some : s.get? n = some aₙ) : ∃ aₘ : α, s.get? m = some aₘ :=
  have : s.get? n ≠ none := by simp [s_nth_eq_some]
  have : s.get? m ≠ none := mt (s.le_stable m_le_n) this
  Option.ne_none_iff_exists'.mp this

theorem not_mem_nil (a : α) : a ∉ @nil α := fun ⟨_, (h : some a = none)⟩ => by injection h

theorem mem_cons (a : α) : ∀ s : Seq α, a ∈ cons a s
  | ⟨_, _⟩ => Stream'.mem_cons (some a) _

theorem mem_cons_of_mem (y : α) {a : α} : ∀ {s : Seq α}, a ∈ s → a ∈ cons y s
  | ⟨_, _⟩ => Stream'.mem_cons_of_mem (some y)

theorem eq_or_mem_of_mem_cons {a b : α} : ∀ {s : Seq α}, a ∈ cons b s → a = b ∨ a ∈ s
  | ⟨_, _⟩, h => (Stream'.eq_or_mem_of_mem_cons h).imp_left fun h => by injection h

@[simp]
theorem mem_cons_iff {a b : α} {s : Seq α} : a ∈ cons b s ↔ a = b ∨ a ∈ s :=
  ⟨eq_or_mem_of_mem_cons, by rintro (rfl | m) <;> [apply mem_cons; exact mem_cons_of_mem _ m]⟩

/-- Destructor for a sequence, resulting in either `none` (for `nil`) or
  `some (a, s)` (for `cons a s`). -/
def destruct (s : Seq α) : Option (Seq1 α) :=
  (fun a' => (a', s.tail)) <$> get? s 0

theorem destruct_eq_nil {s : Seq α} : destruct s = none → s = nil := by
  dsimp [destruct]
  induction' f0 : get? s 0 <;> intro h
  · apply Subtype.eq
    funext n
    induction' n with n IH
    exacts [f0, s.2 IH]
  · contradiction

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

@[simp]
theorem destruct_nil : destruct (nil : Seq α) = none :=
  rfl

@[simp]
theorem destruct_cons (a : α) : ∀ s, destruct (cons a s) = some (a, s)
  | ⟨f, al⟩ => by
    unfold cons destruct Functor.map
    apply congr_arg fun s => some (a, s)
    apply Subtype.eq; dsimp [tail]

-- Porting note: needed universe annotation to avoid universe issues
theorem head_eq_destruct (s : Seq α) : head.{u} s = Prod.fst.{u} <$> destruct.{u} s := by
  unfold destruct head; cases get? s 0 <;> rfl

@[simp]
theorem head_nil : head (nil : Seq α) = none :=
  rfl

@[simp]
theorem head_cons (a : α) (s) : head (cons a s) = some a := by
  rw [head_eq_destruct, destruct_cons, Option.map_eq_map, Option.map_some']

@[simp]
theorem tail_nil : tail (nil : Seq α) = nil :=
  rfl

@[simp]
theorem tail_cons (a : α) (s) : tail (cons a s) = s := by
  cases' s with f al
  apply Subtype.eq
  dsimp [tail, cons]

@[simp]
theorem get?_tail (s : Seq α) (n) : get? (tail s) n = get? s (n + 1) :=
  rfl

/-- Recursion principle for sequences, compare with `List.recOn`. -/
@[cases_eliminator]
def recOn {motive : Seq α → Sort v} (s : Seq α) (nil : motive nil)
    (cons : ∀ x s, motive (cons x s)) :
    motive s := by
  rcases H : destruct s with - | v
  · rw [destruct_eq_nil H]
    apply nil
  · cases' v with a s'
    rw [destruct_eq_cons H]
    apply cons

theorem mem_rec_on {C : Seq α → Prop} {a s} (M : a ∈ s)
    (h1 : ∀ b s', a = b ∨ C s' → C (cons b s')) : C s := by
  obtain ⟨k, e⟩ := M; unfold Stream'.get at e
  induction' k with k IH generalizing s
  · have TH : s = cons a (tail s) := by
      apply destruct_eq_cons
      unfold destruct get? Functor.map
      rw [← e]
      rfl
    rw [TH]
    apply h1 _ _ (Or.inl rfl)
  -- Porting note: had to reshuffle `intro`
  cases' s with b s'
  · injection e
  · have h_eq : (cons b s').val (Nat.succ k) = s'.val k := by cases s' using Subtype.recOn; rfl
    rw [h_eq] at e
    apply h1 _ _ (Or.inr (IH e))

/-- Corecursor over pairs of `Option` values -/
def Corec.f (f : β → Option (α × β)) : Option β → Option α × Option β
  | none => (none, none)
  | some b =>
    match f b with
    | none => (none, none)
    | some (a, b') => (some a, some b')

/-- Corecursor for `Seq α` as a coinductive type. Iterates `f` to produce new elements
  of the sequence until `none` is obtained. -/
def corec (f : β → Option (α × β)) (b : β) : Seq α := by
  refine ⟨Stream'.corec' (Corec.f f) (some b), fun {n} h => ?_⟩
  rw [Stream'.corec'_eq]
  change Stream'.corec' (Corec.f f) (Corec.f f (some b)).2 n = none
  revert h; generalize some b = o; revert o
  induction' n with n IH <;> intro o
  · change (Corec.f f o).1 = none → (Corec.f f (Corec.f f o).2).1 = none
    rcases o with - | b <;> intro h
    · rfl
    dsimp [Corec.f] at h
    dsimp [Corec.f]
    revert h; rcases h₁ : f b with - | s <;> intro h
    · rfl
    · obtain ⟨a, b'⟩ := s
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
  obtain ⟨a, b'⟩ := s; dsimp [Corec.f]
  apply congr_arg fun b' => some (a, b')
  apply Subtype.eq
  dsimp [corec, tail]
  rw [Stream'.corec'_eq, Stream'.tail_cons]
  dsimp [Corec.f]; rw [h]

section Bisim

variable (R : Seq α → Seq α → Prop)

local infixl:50 " ~ " => R

/-- Bisimilarity relation over `Option` of `Seq1 α`-/
def BisimO : Option (Seq1 α) → Option (Seq1 α) → Prop
  | none, none => True
  | some (a, s), some (a', s') => a = a' ∧ R s s'
  | _, _ => False

attribute [simp] BisimO
attribute [nolint simpNF] BisimO.eq_3

/-- a relation is bisimilar if it meets the `BisimO` test -/
def IsBisimulation :=
  ∀ ⦃s₁ s₂⦄, s₁ ~ s₂ → BisimO R (destruct s₁) (destruct s₂)

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
        And.imp id (fun r => ⟨tail s, tail s', by cases s using Subtype.recOn; rfl,
          by cases s' using Subtype.recOn; rfl, r⟩) this
      have := bisim r; revert r this
      cases' s with x s <;> cases' s' with x' s'
      · intro r _
        constructor
        · rfl
        · assumption
      · intro _ this
        rw [destruct_nil, destruct_cons] at this
        exact False.elim this
      · intro _ this
        rw [destruct_nil, destruct_cons] at this
        exact False.elim this
      · intro _ this
        rw [destruct_cons, destruct_cons] at this
        rw [head_cons, head_cons, tail_cons, tail_cons]
        cases' this with h1 h2
        constructor
        · rw [h1]
        · exact h2
  · exact ⟨s₁, s₂, rfl, rfl, r⟩

end Bisim

theorem coinduction :
    ∀ {s₁ s₂ : Seq α},
      head s₁ = head s₂ →
        (∀ (β : Type u) (fr : Seq α → β), fr s₁ = fr s₂ → fr (tail s₁) = fr (tail s₂)) → s₁ = s₂
  | _, _, hh, ht =>
    Subtype.eq (Stream'.coinduction hh fun β fr => ht β fun s => fr s.1)

theorem coinduction2 (s) (f g : Seq α → Seq β)
    (H :
      ∀ s,
        BisimO (fun s1 s2 : Seq β => ∃ s : Seq α, s1 = f s ∧ s2 = g s) (destruct (f s))
          (destruct (g s))) :
    f s = g s := by
  refine eq_of_bisim (fun s1 s2 => ∃ s, s1 = f s ∧ s2 = g s) ?_ ⟨s, rfl, rfl⟩
  intro s1 s2 h; rcases h with ⟨s, h1, h2⟩
  rw [h1, h2]; apply H

/-- Embed a list as a sequence -/
@[coe]
def ofList (l : List α) : Seq α :=
  ⟨List.get? l, fun {n} h => by
    rw [List.get?_eq_none_iff] at h ⊢
    exact h.trans (Nat.le_succ n)⟩

instance coeList : Coe (List α) (Seq α) :=
  ⟨ofList⟩

@[simp]
theorem ofList_nil : ofList [] = (nil : Seq α) :=
  rfl

@[simp]
theorem ofList_get (l : List α) (n : ℕ) : (ofList l).get? n = l.get? n :=
  rfl

@[simp]
theorem ofList_cons (a : α) (l : List α) : ofList (a::l) = cons a (ofList l) := by
  ext1 (_ | n) <;> rfl

theorem ofList_injective : Function.Injective (ofList : List α → _) :=
  fun _ _ h => List.ext_get? fun _ => congr_fun (Subtype.ext_iff.1 h) _

/-- Embed an infinite stream as a sequence -/
@[coe]
def ofStream (s : Stream' α) : Seq α :=
  ⟨s.map some, fun {n} h => by contradiction⟩

instance coeStream : Coe (Stream' α) (Seq α) :=
  ⟨ofStream⟩

section MLList

/-- Embed a `MLList α` as a sequence. Note that even though this
  is non-meta, it will produce infinite sequences if used with
  cyclic `MLList`s created by meta constructions. -/
def ofMLList : MLList Id α → Seq α :=
  corec fun l =>
    match l.uncons with
    | .none => none
    | .some (a, l') => some (a, l')

instance coeMLList : Coe (MLList Id α) (Seq α) :=
  ⟨ofMLList⟩

/-- Translate a sequence into a `MLList`. -/
unsafe def toMLList : Seq α → MLList Id α
  | s =>
    match destruct s with
    | none => .nil
    | some (a, s') => .cons a (toMLList s')

end MLList

/-- Translate a sequence to a list. This function will run forever if
  run on an infinite sequence. -/
unsafe def forceToList (s : Seq α) : List α :=
  (toMLList s).force

/-- The sequence of natural numbers some 0, some 1, ... -/
def nats : Seq ℕ :=
  Stream'.nats

@[simp]
theorem nats_get? (n : ℕ) : nats.get? n = some n :=
  rfl

/-- Append two sequences. If `s₁` is infinite, then `s₁ ++ s₂ = s₁`,
  otherwise it puts `s₂` at the location of the `nil` in `s₁`. -/
def append (s₁ s₂ : Seq α) : Seq α :=
  @corec α (Seq α × Seq α)
    (fun ⟨s₁, s₂⟩ =>
      match destruct s₁ with
      | none => omap (fun s₂ => (nil, s₂)) (destruct s₂)
      | some (a, s₁') => some (a, s₁', s₂))
    (s₁, s₂)

/-- Map a function over a sequence. -/
def map (f : α → β) : Seq α → Seq β
  | ⟨s, al⟩ =>
    ⟨s.map (Option.map f), fun {n} => by
      dsimp [Stream'.map, Stream'.get]
      induction' e : s n with e <;> intro
      · rw [al e]
        assumption
      · contradiction⟩

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

/-- Remove the first `n` elements from the sequence. -/
def drop (s : Seq α) : ℕ → Seq α
  | 0 => s
  | n + 1 => tail (drop s n)

attribute [simp] drop

/-- Take the first `n` elements of the sequence (producing a list) -/
def take : ℕ → Seq α → List α
  | 0, _ => []
  | n + 1, s =>
    match destruct s with
    | none => []
    | some (x, r) => List.cons x (take n r)

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

section ZipWith

/-- Combine two sequences with a function -/
def zipWith (f : α → β → γ) (s₁ : Seq α) (s₂ : Seq β) : Seq γ :=
  ⟨fun n => Option.map₂ f (s₁.get? n) (s₂.get? n), fun {_} hn =>
    Option.map₂_eq_none_iff.2 <| (Option.map₂_eq_none_iff.1 hn).imp s₁.2 s₂.2⟩

@[simp]
theorem get?_zipWith (f : α → β → γ) (s s' n) :
    (zipWith f s s').get? n = Option.map₂ f (s.get? n) (s'.get? n) :=
  rfl

end ZipWith

/-- Pair two sequences into a sequence of pairs -/
def zip : Seq α → Seq β → Seq (α × β) :=
  zipWith Prod.mk

theorem get?_zip (s : Seq α) (t : Seq β) (n : ℕ) :
    get? (zip s t) n = Option.map₂ Prod.mk (get? s n) (get? t n) :=
  get?_zipWith _ _ _ _

/-- Separate a sequence of pairs into two sequences -/
def unzip (s : Seq (α × β)) : Seq α × Seq β :=
  (map Prod.fst s, map Prod.snd s)

/-- Enumerate a sequence by tagging each element with its index. -/
def enum (s : Seq α) : Seq (ℕ × α) :=
  Seq.zip nats s

@[simp]
theorem get?_enum (s : Seq α) (n : ℕ) : get? (enum s) n = Option.map (Prod.mk n) (get? s n) :=
  get?_zip _ _ _

@[simp]
theorem enum_nil : enum (nil : Seq α) = nil :=
  rfl

/-- The length of a terminating sequence. -/
def length (s : Seq α) (h : s.Terminates) : ℕ :=
  Nat.find h

/-- Convert a sequence which is known to terminate into a list -/
def toList (s : Seq α) (h : s.Terminates) : List α :=
  take (length s h) s

/-- Convert a sequence which is known not to terminate into a stream -/
def toStream (s : Seq α) (h : ¬s.Terminates) : Stream' α := fun n =>
  Option.get _ <| not_terminates_iff.1 h n

/-- Convert a sequence into either a list or a stream depending on whether
  it is finite or infinite. (Without decidability of the infiniteness predicate,
  this is not constructively possible.) -/
def toListOrStream (s : Seq α) [Decidable s.Terminates] : List α ⊕ Stream' α :=
  if h : s.Terminates then Sum.inl (toList s h) else Sum.inr (toStream s h)

@[simp]
theorem nil_append (s : Seq α) : append nil s = s := by
  apply coinduction2; intro s
  dsimp [append]; rw [corec_eq]
  dsimp [append]
  cases' s with x s
  · trivial
  · rw [destruct_cons]
    dsimp
    exact ⟨rfl, s, rfl, rfl⟩

@[simp]
theorem getElem?_take : ∀ (n k : ℕ) (s : Seq α),
    (s.take k)[n]? = if n < k then s.get? n else none
  | n, 0, s => by simp [take]
  | n, k+1, s => by
    rw [take]
    cases h : destruct s with
    | none =>
      simp [destruct_eq_nil h]
    | some a =>
      match a with
      | (x, r) =>
        rw [destruct_eq_cons h]
        match n with
        | 0 => simp
        | n+1 => simp [List.get?_cons_succ, Nat.add_lt_add_iff_right, get?_cons_succ, getElem?_take]

theorem terminatedAt_ofList (l : List α) :
    (ofList l).TerminatedAt l.length := by
  simp [ofList, TerminatedAt]

theorem terminates_ofList (l : List α) : (ofList l).Terminates :=
  ⟨_, terminatedAt_ofList l⟩

theorem terminatedAt_nil : TerminatedAt (nil : Seq α) 0 := rfl

@[simp]
theorem terminates_nil : Terminates (nil : Seq α) := ⟨0, rfl⟩

@[simp]
theorem length_nil : length (nil : Seq α) terminates_nil = 0 := rfl

@[simp]
theorem get?_zero_eq_none {s : Seq α} : s.get? 0 = none ↔ s = nil := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  ext1 n
  exact le_stable s (Nat.zero_le _) h

@[simp] theorem length_eq_zero {s : Seq α} {h : s.Terminates} :
    s.length h = 0 ↔ s = nil := by
  simp [length, TerminatedAt]

theorem terminatedAt_zero_iff {s : Seq α} : s.TerminatedAt 0 ↔ s = nil := by
  refine ⟨?_, ?_⟩
  · intro h
    ext n
    rw [le_stable _ (Nat.zero_le _) h]
    simp
  · rintro rfl
    simp [TerminatedAt]

/-- The statement of `length_le_iff'` does not assume that the sequence terminates. For a
simpler statement of the theorem where the sequence is known to terminate see `length_le_iff` -/
theorem length_le_iff' {s : Seq α} {n : ℕ} :
    (∃ h, s.length h ≤ n) ↔ s.TerminatedAt n := by
  simp only [length, Nat.find_le_iff, TerminatedAt, Terminates, exists_prop]
  refine ⟨?_, ?_⟩
  · rintro ⟨_, k, hkn, hk⟩
    exact le_stable s hkn hk
  · intro hn
    exact ⟨⟨n, hn⟩, ⟨n, le_rfl, hn⟩⟩

/-- The statement of `length_le_iff` assumes that the sequence terminates. For a
statement of the where the sequence is not known to terminate see `length_le_iff'` -/
theorem length_le_iff {s : Seq α} {n : ℕ} {h : s.Terminates} :
    s.length h ≤ n ↔ s.TerminatedAt n := by
  rw [← length_le_iff']; simp [h]

/-- The statement of `lt_length_iff'` does not assume that the sequence terminates. For a
simpler statement of the theorem where the sequence is known to terminate see `lt_length_iff` -/
theorem lt_length_iff' {s : Seq α} {n : ℕ} :
    (∀ h : s.Terminates, n < s.length h) ↔ ∃ a, a ∈ s.get? n := by
  simp only [Terminates, TerminatedAt, length, Nat.lt_find_iff, forall_exists_index, Option.mem_def,
    ← Option.ne_none_iff_exists', ne_eq]
  refine ⟨?_, ?_⟩
  · intro h hn
    exact h n hn n le_rfl hn
  · intro hn _ _ k hkn hk
    exact hn <| le_stable s hkn hk

/-- The statement of `length_le_iff` assumes that the sequence terminates. For a
statement of the where the sequence is not known to terminate see `length_le_iff'` -/
theorem lt_length_iff {s : Seq α} {n : ℕ} {h : s.Terminates} :
    n < s.length h ↔ ∃ a, a ∈ s.get? n := by
  rw [← lt_length_iff']; simp [h]

theorem length_take_of_le_length {s : Seq α} {n : ℕ}
    (hle : ∀ h : s.Terminates, n ≤ s.length h) : (s.take n).length = n := by
  induction n generalizing s with
  | zero => simp [take]
  | succ n ih =>
      rw [take, destruct]
      let ⟨a, ha⟩ := lt_length_iff'.1 (fun ht => lt_of_lt_of_le (Nat.succ_pos _) (hle ht))
      simp [Option.mem_def.1 ha]
      rw [ih]
      intro h
      simp only [length, tail, Nat.le_find_iff, TerminatedAt, get?_mk, Stream'.tail]
      intro m hmn hs
      have := lt_length_iff'.1 (fun ht => (Nat.lt_of_succ_le (hle ht)))
      rw [le_stable s (Nat.succ_le_of_lt hmn) hs] at this
      simp at this

@[simp]
theorem length_toList (s : Seq α) (h : s.Terminates) : (toList s h).length = length s h := by
  rw [toList, length_take_of_le_length]
  intro _
  exact le_rfl

@[simp]
theorem getElem?_toList (s : Seq α) (h : s.Terminates) (n : ℕ) : (toList s h)[n]? = s.get? n := by
  ext k
  simp only [ofList, toList, get?_mk, Option.mem_def, getElem?_take, Nat.lt_find_iff, length,
    Option.ite_none_right_eq_some, and_iff_right_iff_imp, TerminatedAt, List.get?_eq_getElem?]
  intro h m hmn
  let ⟨a, ha⟩ := ge_stable s hmn h
  simp [ha]

@[simp]
theorem ofList_toList (s : Seq α) (h : s.Terminates) :
    ofList (toList s h) = s := by
  ext n; simp [ofList, List.get?_eq_getElem?]

@[simp]
theorem toList_ofList (l : List α) : toList (ofList l) (terminates_ofList l) = l :=
  ofList_injective (by simp)

@[simp]
theorem toList_nil : toList (nil : Seq α) ⟨0, terminatedAt_zero_iff.2 rfl⟩ = [] := by
  ext; simp [nil, toList, const]

theorem getLast?_toList (s : Seq α) (h : s.Terminates) :
    (toList s h).getLast? = s.get? (s.length h - 1) := by
  rw [List.getLast?_eq_getElem?, getElem?_toList, length_toList]

@[simp]
theorem cons_append (a : α) (s t) : append (cons a s) t = cons a (append s t) :=
  destruct_eq_cons <| by
    dsimp [append]; rw [corec_eq]
    dsimp [append]; rw [destruct_cons]

@[simp]
theorem append_nil (s : Seq α) : append s nil = s := by
  apply coinduction2 s; intro s
  cases' s with x s
  · trivial
  · rw [cons_append, destruct_cons, destruct_cons]
    dsimp
    exact ⟨rfl, s, rfl, rfl⟩

@[simp]
theorem append_assoc (s t u : Seq α) : append (append s t) u = append s (append t u) := by
  apply eq_of_bisim fun s1 s2 => ∃ s t u, s1 = append (append s t) u ∧ s2 = append s (append t u)
  · intro s1 s2 h
    exact
      match s1, s2, h with
      | _, _, ⟨s, t, u, rfl, rfl⟩ => by
        cases' s with _ s <;> simp
        · cases' t with _ t <;> simp
          · cases' u with _ u <;> simp
            · refine ⟨nil, nil, u, ?_, ?_⟩ <;> simp
          · refine ⟨nil, t, u, ?_, ?_⟩ <;> simp
        · exact ⟨s, t, u, rfl, rfl⟩
  · exact ⟨s, t, u, rfl, rfl⟩

@[simp]
theorem map_nil (f : α → β) : map f nil = nil :=
  rfl

@[simp]
theorem map_cons (f : α → β) (a) : ∀ s, map f (cons a s) = cons (f a) (map f s)
  | ⟨s, al⟩ => by apply Subtype.eq; dsimp [cons, map]; rw [Stream'.map_cons]; rfl

@[simp]
theorem map_id : ∀ s : Seq α, map id s = s
  | ⟨s, al⟩ => by
    apply Subtype.eq; dsimp [map]
    rw [Option.map_id, Stream'.map_id]

@[simp]
theorem map_tail (f : α → β) : ∀ s, map f (tail s) = tail (map f s)
  | ⟨s, al⟩ => by apply Subtype.eq; dsimp [tail, map]

theorem map_comp (f : α → β) (g : β → γ) : ∀ s : Seq α, map (g ∘ f) s = map g (map f s)
  | ⟨s, al⟩ => by
    apply Subtype.eq; dsimp [map]
    apply congr_arg fun f : _ → Option γ => Stream'.map f s
    ext ⟨⟩ <;> rfl

@[simp]
theorem map_append (f : α → β) (s t) : map f (append s t) = append (map f s) (map f t) := by
  apply
    eq_of_bisim (fun s1 s2 => ∃ s t, s1 = map f (append s t) ∧ s2 = append (map f s) (map f t)) _
      ⟨s, t, rfl, rfl⟩
  intro s1 s2 h
  exact
    match s1, s2, h with
    | _, _, ⟨s, t, rfl, rfl⟩ => by
      cases' s with _ s <;> simp
      · cases' t with _ t <;> simp
        · refine ⟨nil, t, ?_, ?_⟩ <;> simp
      · exact ⟨s, t, rfl, rfl⟩

@[simp]
theorem map_get? (f : α → β) : ∀ s n, get? (map f s) n = (get? s n).map f
  | ⟨_, _⟩, _ => rfl

@[simp]
theorem terminatedAt_map_iff {f : α → β} {s : Seq α} {n : ℕ} :
    (map f s).TerminatedAt n ↔ s.TerminatedAt n := by
  simp [TerminatedAt]

@[simp]
theorem terminates_map_iff {f : α → β} {s : Seq α}  :
    (map f s).Terminates ↔ s.Terminates := by
  simp [Terminates]

@[simp]
theorem length_map {s : Seq α} {f : α → β} (h : (s.map f).Terminates) :
    (s.map f).length h = s.length (terminates_map_iff.1 h) := by
  rw [length]
  congr
  ext
  simp

instance : Functor Seq where map := @map

instance : LawfulFunctor Seq where
  id_map := @map_id
  comp_map := @map_comp
  map_const := rfl

@[simp]
theorem join_nil : join nil = (nil : Seq α) :=
  destruct_eq_nil rfl

-- Not a simp lemmas as `join_cons` is more general
theorem join_cons_nil (a : α) (S) : join (cons (a, nil) S) = cons a (join S) :=
  destruct_eq_cons <| by simp [join]

-- Not a simp lemmas as `join_cons` is more general
theorem join_cons_cons (a b : α) (s S) :
    join (cons (a, cons b s) S) = cons a (join (cons (b, s) S)) :=
  destruct_eq_cons <| by simp [join]

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
      cases' s with x s; · trivial
      · rw [destruct_cons]
        exact ⟨rfl, Or.inl rfl⟩
    | _, _, Or.inr ⟨a, s, S, rfl, rfl⟩ => by
      cases' s with x s
      · simp [join_cons_cons, join_cons_nil]
      · simpa [join_cons_cons, join_cons_nil] using Or.inr ⟨x, s, S, rfl, rfl⟩

@[simp]
theorem join_append (S T : Seq (Seq1 α)) : join (append S T) = append (join S) (join T) := by
  apply
    eq_of_bisim fun s1 s2 =>
      ∃ s S T, s1 = append s (join (append S T)) ∧ s2 = append s (append (join S) (join T))
  · intro s1 s2 h
    exact
      match s1, s2, h with
      | _, _, ⟨s, S, T, rfl, rfl⟩ => by
        cases' s with _ s <;> simp
        · cases' S with s S <;> simp
          · cases' T with s T
            · simp
            · cases' s with a s; simp only [join_cons, destruct_cons, true_and]
              refine ⟨s, nil, T, ?_, ?_⟩ <;> simp
          · cases' s with a s
            simpa using ⟨s, S, T, rfl, rfl⟩
        · exact ⟨s, S, T, rfl, rfl⟩
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
def toList' {α} (s : Seq α) : Computation (List α) :=
  @Computation.corec (List α) (List α × Seq α)
    (fun ⟨l, s⟩ =>
      match destruct s with
      | none => Sum.inl l.reverse
      | some (a, s') => Sum.inr (a::l, s'))
    ([], s)

theorem dropn_add (s : Seq α) (m) : ∀ n, drop s (m + n) = drop (drop s m) n
  | 0 => rfl
  | n + 1 => congr_arg tail (dropn_add s _ n)

theorem dropn_tail (s : Seq α) (n) : drop (tail s) n = drop s (n + 1) := by
  rw [Nat.add_comm]; symm; apply dropn_add

@[simp]
theorem head_dropn (s : Seq α) (n) : head (drop s n) = get? s n := by
  induction' n with n IH generalizing s; · rfl
  rw [← get?_tail, ← dropn_tail]; apply IH

theorem mem_map (f : α → β) {a : α} : ∀ {s : Seq α}, a ∈ s → f a ∈ map f s
  | ⟨_, _⟩ => Stream'.mem_map (Option.map f)

theorem exists_of_mem_map {f} {b : β} : ∀ {s : Seq α}, b ∈ map f s → ∃ a, a ∈ s ∧ f a = b :=
  fun {s} h => by match s with
  | ⟨g, al⟩ =>
    let ⟨o, om, oe⟩ := @Stream'.exists_of_mem_map _ _ (Option.map f) (some b) g h
    rcases o with - | a
    · injection oe
    · injection oe with h'; exact ⟨a, om, h'⟩

theorem of_mem_append {s₁ s₂ : Seq α} {a : α} (h : a ∈ append s₁ s₂) : a ∈ s₁ ∨ a ∈ s₂ := by
  have := h; revert this
  generalize e : append s₁ s₂ = ss; intro h; revert s₁
  apply mem_rec_on h _
  intro b s' o s₁
  cases' s₁ with c t₁
  · intro m _
    apply Or.inr
    simpa using m
  · intro m e
    have this := congr_arg destruct e
    rcases show a = c ∨ a ∈ append t₁ s₂ by simpa using m with e' | m
    · rw [e']
      exact Or.inl (mem_cons _ _)
    · obtain ⟨i1, i2⟩ := show c = b ∧ append t₁ s₂ = s' by simpa
      rcases o with e' | IH
      · simp [i1, e']
      · exact Or.imp_left (mem_cons_of_mem _) (IH m i2)

theorem mem_append_left {s₁ s₂ : Seq α} {a : α} (h : a ∈ s₁) : a ∈ append s₁ s₂ := by
  apply mem_rec_on h; intros; simp [*]

@[simp]
theorem enum_cons (s : Seq α) (x : α) :
    enum (cons x s) = cons (0, x) (map (Prod.map Nat.succ id) (enum s)) := by
  ext ⟨n⟩ : 1
  · simp
  · simp only [get?_enum, get?_cons_succ, map_get?, Option.map_map]
    congr

end Seq

namespace Seq1

variable {α : Type u} {β : Type v} {γ : Type w}

open Stream'.Seq

/-- Convert a `Seq1` to a sequence. -/
def toSeq : Seq1 α → Seq α
  | (a, s) => Seq.cons a s

instance coeSeq : Coe (Seq1 α) (Seq α) :=
  ⟨toSeq⟩

/-- Map a function on a `Seq1` -/
def map (f : α → β) : Seq1 α → Seq1 β
  | (a, s) => (f a, Seq.map f s)

theorem map_pair {f : α → β} {a s} : map f (a, s) = (f a, Seq.map f s) := rfl

theorem map_id : ∀ s : Seq1 α, map id s = s
  | ⟨a, s⟩ => by simp [map]

/-- Flatten a nonempty sequence of nonempty sequences -/
def join : Seq1 (Seq1 α) → Seq1 α
  | ((a, s), S) =>
    match destruct s with
    | none => (a, Seq.join S)
    | some s' => (a, Seq.join (Seq.cons s' S))

@[simp]
theorem join_nil (a : α) (S) : join ((a, nil), S) = (a, Seq.join S) :=
  rfl

@[simp]
theorem join_cons (a b : α) (s S) :
    join ((a, Seq.cons b s), S) = (a, Seq.join (Seq.cons (b, s) S)) := by
  dsimp [join]; rw [destruct_cons]

/-- The `return` operator for the `Seq1` monad,
  which produces a singleton sequence. -/
def ret (a : α) : Seq1 α :=
  (a, nil)

instance [Inhabited α] : Inhabited (Seq1 α) :=
  ⟨ret default⟩

/-- The `bind` operator for the `Seq1` monad,
  which maps `f` on each element of `s` and appends the results together.
  (Not all of `s` may be evaluated, because the first few elements of `s`
  may already produce an infinite result.) -/
def bind (s : Seq1 α) (f : α → Seq1 β) : Seq1 β :=
  join (map f s)

@[simp]
theorem join_map_ret (s : Seq α) : Seq.join (Seq.map ret s) = s := by
  apply coinduction2 s; intro s; cases s <;> simp [ret]

@[simp]
theorem bind_ret (f : α → β) : ∀ s, bind s (ret ∘ f) = map f s
  | ⟨a, s⟩ => by
    dsimp [bind, map]
    -- Porting note: Was `rw [map_comp]; simp [Function.comp, ret]`
    rw [map_comp, ret]
    simp

@[simp]
theorem ret_bind (a : α) (f : α → Seq1 β) : bind (ret a) f = f a := by
  simp only [bind, map, ret.eq_1, map_nil]
  cases' f a with a s
  cases s <;> simp

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
        cases' s with _ s <;> simp
        · cases' S with x S <;> simp
          · cases' x with a s
            simpa [map] using ⟨_, _, rfl, rfl⟩
        · exact ⟨s, S, rfl, rfl⟩
  · refine ⟨nil, S, ?_, ?_⟩ <;> simp

@[simp]
theorem map_join (f : α → β) : ∀ S, map f (join S) = join (map (map f) S)
  | ((a, s), S) => by cases s <;> simp [map]

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
        cases' s with _ s <;> simp
        · cases' SS with S SS <;> simp
          · cases' S with s S; cases' s with x s
            simp only [Seq.join_cons, join_append, destruct_cons]
            cases' s with x s <;> simp
            · exact ⟨_, _, rfl, rfl⟩
            · refine ⟨Seq.cons x (append s (Seq.join S)), SS, ?_, ?_⟩ <;> simp
        · exact ⟨s, SS, rfl, rfl⟩
  · refine ⟨nil, SS, ?_, ?_⟩ <;> simp

@[simp]
theorem bind_assoc (s : Seq1 α) (f : α → Seq1 β) (g : β → Seq1 γ) :
    bind (bind s f) g = bind s fun x : α => bind (f x) g := by
  cases' s with a s
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10745): was `simp [bind, map]`.
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
    cases t <;> simp
  · cases' x_1 with y t; simp

instance monad : Monad Seq1 where
  map := @map
  pure := @ret
  bind := @bind

instance lawfulMonad : LawfulMonad Seq1 := LawfulMonad.mk'
  (id_map := @map_id)
  (bind_pure_comp := @bind_ret)
  (pure_bind := @ret_bind)
  (bind_assoc := @bind_assoc)

end Seq1

end Stream'
