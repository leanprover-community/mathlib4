/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Option.NAry
import Mathlib.Data.Seq.Computation

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

/-- Get the nth element of a sequence (if it exists) -/
def get? : Seq α → ℕ → Option α :=
  Subtype.val

@[simp]
theorem val_eq_get (s : Seq α) (n : ℕ) : s.val n = s.get? n := by
  rfl

@[simp]
theorem get?_mk (f hf) : @get? α ⟨f, hf⟩ = f :=
  rfl

theorem le_stable (s : Seq α) {m n} (h : m ≤ n) : s.get? m = none → s.get? n = none := by
  obtain ⟨f, al⟩ := s
  induction' h with n _ IH
  exacts [id, fun h2 => al (IH h2)]

/-- If `s.get? n = some aₙ` for some value `aₙ`, then there is also some value `aₘ` such
that `s.get? = some aₘ` for `m ≤ n`.
-/
theorem ge_stable (s : Seq α) {aₙ : α} {n m : ℕ} (m_le_n : m ≤ n)
    (s_nth_eq_some : s.get? n = some aₙ) : ∃ aₘ : α, s.get? m = some aₘ :=
  have : s.get? n ≠ none := by simp [s_nth_eq_some]
  have : s.get? m ≠ none := mt (s.le_stable m_le_n) this
  Option.ne_none_iff_exists'.mp this

@[ext]
protected theorem ext {s t : Seq α} (h : ∀ n : ℕ, s.get? n = t.get? n) : s = t :=
  Subtype.eq <| funext h

/-!
### Constructors
-/

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

@[simp]
theorem get?_nil (n : ℕ) : (@nil α).get? n = none :=
  rfl

@[simp]
theorem get?_zero_eq_none {s : Seq α} : s.get? 0 = none ↔ s = nil := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  ext1 n
  exact le_stable s (Nat.zero_le _) h

@[simp]
theorem get?_cons_zero (a : α) (s : Seq α) : (cons a s).get? 0 = some a :=
  rfl

@[simp]
theorem get?_cons_succ (a : α) (s : Seq α) (n : ℕ) : (cons a s).get? (n + 1) = s.get? n :=
  rfl

@[simp]
theorem cons_ne_nil {x : α} {s : Seq α} : (cons x s) ≠ .nil := by
  intro h
  simpa using congrArg (·.get? 0) h

@[simp]
theorem nil_ne_cons {x : α} {s : Seq α} : .nil ≠ (cons x s) := cons_ne_nil.symm

theorem cons_injective2 : Function.Injective2 (cons : α → Seq α → Seq α) := fun x y s t h =>
  ⟨by rw [← Option.some_inj, ← get?_cons_zero, h, get?_cons_zero],
    Seq.ext fun n => by simp_rw [← get?_cons_succ x s n, h, get?_cons_succ]⟩

theorem cons_left_injective (s : Seq α) : Function.Injective fun x => cons x s :=
  cons_injective2.left _

theorem cons_right_injective (x : α) : Function.Injective (cons x) :=
  cons_injective2.right _

theorem cons_eq_cons {x x' : α} {s s' : Seq α} :
    (cons x s = cons x' s') ↔ (x = x' ∧ s = s') := by
  constructor
  · apply cons_injective2
  · intro ⟨_, _⟩
    congr

/-!
### Destructors
-/

/-- Get the first element of a sequence -/
def head (s : Seq α) : Option α :=
  get? s 0

/-- Get the tail of a sequence (or `nil` if the sequence is `nil`) -/
def tail (s : Seq α) : Seq α :=
  ⟨s.1.tail, fun n' => by
    obtain ⟨f, al⟩ := s
    exact al n'⟩

/-- Destructor for a sequence, resulting in either `none` (for `nil`) or
  `some (a, s)` (for `cons a s`). -/
def destruct (s : Seq α) : Option (Seq1 α) :=
  (fun a' => (a', s.tail)) <$> get? s 0

-- Porting note: needed universe annotation to avoid universe issues
theorem head_eq_destruct (s : Seq α) : head.{u} s = Prod.fst.{u} <$> destruct.{u} s := by
  unfold destruct head; cases get? s 0 <;> rfl

@[simp]
theorem get?_tail (s : Seq α) (n) : get? (tail s) n = get? s (n + 1) :=
  rfl

@[simp]
theorem destruct_nil : destruct (nil : Seq α) = none :=
  rfl

@[simp]
theorem destruct_cons (a : α) : ∀ s, destruct (cons a s) = some (a, s)
  | ⟨f, al⟩ => by
    unfold cons destruct Functor.map
    apply congr_arg fun s => some (a, s)
    apply Subtype.eq; dsimp [tail]

theorem destruct_eq_none {s : Seq α} : destruct s = none → s = nil := by
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
  · obtain ⟨f, al⟩ := s
    injections _ h1 h2
    rw [← h2]
    apply Subtype.eq
    dsimp [tail, cons]
    rw [h1] at f0
    rw [← f0]
    exact (Stream'.eta f).symm

@[simp]
theorem head_nil : head (nil : Seq α) = none :=
  rfl

@[simp]
theorem head_cons (a : α) (s) : head (cons a s) = some a := by
  rw [head_eq_destruct, destruct_cons, Option.map_eq_map, Option.map_some]

@[simp]
theorem tail_nil : tail (nil : Seq α) = nil :=
  rfl

@[simp]
theorem tail_cons (a : α) (s) : tail (cons a s) = s := by
  obtain ⟨f, al⟩ := s
  apply Subtype.eq
  dsimp [tail, cons]

theorem head_eq_some {s : Seq α} {x : α} (h : s.head = some x) :
    s = cons x s.tail := by
  ext1 n
  cases n <;> simp only [get?_cons_zero, get?_cons_succ, get?_tail]
  exact h

theorem head_eq_none {s : Seq α} (h : s.head = none) : s = nil :=
  get?_zero_eq_none.mp h

@[simp]
theorem head_eq_none_iff {s : Seq α} : s.head = none ↔ s = nil := by
  constructor
  · apply head_eq_none
  · intro h
    simp [h]

/-!
### Recursion and corecursion principles
-/

/-- Recursion principle for sequences, compare with `List.recOn`. -/
@[cases_eliminator]
def recOn {motive : Seq α → Sort v} (s : Seq α) (nil : motive nil)
    (cons : ∀ x s, motive (cons x s)) :
    motive s := by
  rcases H : destruct s with - | v
  · rw [destruct_eq_none H]
    apply nil
  · obtain ⟨a, s'⟩ := v
    rw [destruct_eq_cons H]
    apply cons

/-- Functorial action of the functor `Option (α × _)` -/
@[simp]
def omap (f : β → γ) : Option (α × β) → Option (α × γ)
  | none => none
  | some (a, b) => some (a, f b)

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
  rw [show Stream'.corec' (Corec.f f) (some b) 0 = (Corec.f f (some b)).1 from rfl]
  dsimp [Corec.f]
  induction' h : f b with s; · rfl
  obtain ⟨a, b'⟩ := s; dsimp [Corec.f]
  apply congr_arg fun b' => some (a, b')
  apply Subtype.eq
  dsimp [corec, tail]
  rw [Stream'.corec'_eq, Stream'.tail_cons]
  dsimp [Corec.f]; rw [h]

theorem corec_nil (f : β → Option (α × β)) (b : β)
    (h : f b = .none) : corec f b = nil := by
  apply destruct_eq_none
  simp [h]

theorem corec_cons {f : β → Option (α × β)} {b : β} {x : α} {s : β}
    (h : f b = .some (x, s)) : corec f b = cons x (corec f s) := by
  apply destruct_eq_cons
  simp [h]

/-!
### Bisimulation
-/

section Bisim

variable (R : Seq α → Seq α → Prop)

local infixl:50 " ~ " => R

/-- Bisimilarity relation over `Option` of `Seq1 α` -/
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
      cases s <;> cases s'
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
        obtain ⟨h1, h2⟩ := this
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

/-!
### Termination
-/

/-- A sequence has terminated at position `n` if the value at position `n` equals `none`. -/
def TerminatedAt (s : Seq α) (n : ℕ) : Prop :=
  s.get? n = none

/-- It is decidable whether a sequence terminates at a given position. -/
instance terminatedAtDecidable (s : Seq α) (n : ℕ) : Decidable (s.TerminatedAt n) :=
  decidable_of_iff' (s.get? n).isNone <| by unfold TerminatedAt; cases s.get? n <;> simp

/-- A sequence terminates if there is some position `n` at which it has terminated. -/
def Terminates (s : Seq α) : Prop :=
  ∃ n : ℕ, s.TerminatedAt n

/-- The length of a terminating sequence. -/
def length (s : Seq α) (h : s.Terminates) : ℕ :=
  Nat.find h

/-- If a sequence terminated at position `n`, it also terminated at `m ≥ n`. -/
theorem terminated_stable : ∀ (s : Seq α) {m n : ℕ}, m ≤ n → s.TerminatedAt m → s.TerminatedAt n :=
  le_stable

theorem not_terminates_iff {s : Seq α} : ¬s.Terminates ↔ ∀ n, (s.get? n).isSome := by
  simp only [Terminates, TerminatedAt, ← Ne.eq_def, Option.ne_none_iff_isSome, not_exists, iff_self]

@[simp]
theorem terminatedAt_nil {n : ℕ} : TerminatedAt (nil : Seq α) n := rfl

@[simp]
theorem cons_not_terminatedAt_zero {x : α} {s : Seq α} :
    ¬(cons x s).TerminatedAt 0 := by
  simp [TerminatedAt]

@[simp]
theorem cons_terminatedAt_succ_iff {x : α} {s : Seq α} {n : ℕ} :
    (cons x s).TerminatedAt (n + 1) ↔ s.TerminatedAt n := by
  simp [TerminatedAt]

@[simp]
theorem terminates_nil : Terminates (nil : Seq α) := ⟨0, rfl⟩

@[simp]
theorem terminates_cons_iff {x : α} {s : Seq α} :
    (cons x s).Terminates ↔ s.Terminates := by
  constructor <;> intro ⟨n, h⟩
  · exact ⟨n, cons_terminatedAt_succ_iff.mp (terminated_stable _ (Nat.le_succ _) h)⟩
  · exact ⟨n + 1, cons_terminatedAt_succ_iff.mpr h⟩

@[simp]
theorem length_nil : length (nil : Seq α) terminates_nil = 0 := rfl

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

/-!
### Membership
-/

/-- member definition for `Seq` -/
protected def Mem (s : Seq α) (a : α) :=
  some a ∈ s.1

instance : Membership α (Seq α) :=
  ⟨Seq.Mem⟩

-- Cannot be @[simp] because `n` can not be inferred by `simp`.
theorem get?_mem {s : Seq α} {n : ℕ} {x : α} (h : s.get? n = .some x) : x ∈ s := ⟨n, h.symm⟩

theorem notMem_nil (a : α) : a ∉ @nil α := fun ⟨_, (h : some a = none)⟩ => by injection h

@[deprecated (since := "2025-05-23")] alias not_mem_nil := notMem_nil

theorem mem_cons (a : α) : ∀ s : Seq α, a ∈ cons a s
  | ⟨_, _⟩ => Stream'.mem_cons (some a) _

theorem mem_cons_of_mem (y : α) {a : α} : ∀ {s : Seq α}, a ∈ s → a ∈ cons y s
  | ⟨_, _⟩ => Stream'.mem_cons_of_mem (some y)

theorem eq_or_mem_of_mem_cons {a b : α} : ∀ {s : Seq α}, a ∈ cons b s → a = b ∨ a ∈ s
  | ⟨_, _⟩, h => (Stream'.eq_or_mem_of_mem_cons h).imp_left fun h => by injection h

@[simp]
theorem mem_cons_iff {a b : α} {s : Seq α} : a ∈ cons b s ↔ a = b ∨ a ∈ s :=
  ⟨eq_or_mem_of_mem_cons, by rintro (rfl | m) <;> [apply mem_cons; exact mem_cons_of_mem _ m]⟩

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
  cases s with
  | nil => injection e
  | cons b s' =>
    have h_eq : (cons b s').val (Nat.succ k) = s'.val k := by cases s' using Subtype.recOn; rfl
    rw [h_eq] at e
    apply h1 _ _ (Or.inr (IH e))

/-!
### Converting from/to other types
-/

/-- Embed a list as a sequence -/
@[coe]
def ofList (l : List α) : Seq α :=
  ⟨(l[·]?), fun {n} h => by
    rw [List.getElem?_eq_none_iff] at h ⊢
    exact Nat.le_succ_of_le h⟩

instance coeList : Coe (List α) (Seq α) :=
  ⟨ofList⟩

@[simp]
theorem ofList_nil : ofList [] = (nil : Seq α) :=
  rfl

@[simp]
theorem ofList_get? (l : List α) (n : ℕ) : (ofList l).get? n = l[n]? :=
  rfl

@[deprecated (since := "2025-02-21")]
alias ofList_get := ofList_get?

@[simp]
theorem ofList_cons (a : α) (l : List α) : ofList (a::l) = cons a (ofList l) := by
  ext1 (_ | n) <;> simp

theorem ofList_injective : Function.Injective (ofList : List α → _) :=
  fun _ _ h => List.ext_getElem? fun _ => congr_fun (Subtype.ext_iff.1 h) _

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

/-- Take the first `n` elements of the sequence (producing a list) -/
def take : ℕ → Seq α → List α
  | 0, _ => []
  | n + 1, s =>
    match destruct s with
    | none => []
    | some (x, r) => List.cons x (take n r)

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

/-!
### Operations on sequences
-/

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

/-- Combine two sequences with a function -/
def zipWith (f : α → β → γ) (s₁ : Seq α) (s₂ : Seq β) : Seq γ :=
  ⟨fun n => Option.map₂ f (s₁.get? n) (s₂.get? n), fun {_} hn =>
    Option.map₂_eq_none_iff.2 <| (Option.map₂_eq_none_iff.1 hn).imp s₁.2 s₂.2⟩

/-- Pair two sequences into a sequence of pairs -/
def zip : Seq α → Seq β → Seq (α × β) :=
  zipWith Prod.mk

/-- Separate a sequence of pairs into two sequences -/
def unzip (s : Seq (α × β)) : Seq α × Seq β :=
  (map Prod.fst s, map Prod.snd s)

/-- The sequence of natural numbers some 0, some 1, ... -/
def nats : Seq ℕ :=
  Stream'.nats

/-- Enumerate a sequence by tagging each element with its index. -/
def enum (s : Seq α) : Seq (ℕ × α) :=
  Seq.zip nats s

/-- Folds a sequence using `f`, producing a sequence of intermediate values, i.e.
`[init, f init s.head, f (f init s.head) s.tail.head, ...]`. -/
def fold (s : Seq α) (init : β) (f : β → α → β) : Seq β :=
  let f : β × Seq α → Option (β × (β × Seq α)) := fun (acc, x) =>
    match destruct x with
    | none => .none
    | some (x, s) => .some (f acc x, f acc x, s)
  cons init <| corec f (init, s)

section OfStream

@[simp]
theorem ofStream_cons (a : α) (s) : ofStream (a::s) = cons a (ofStream s) := by
  apply Subtype.eq; simp only [ofStream, cons]; rw [Stream'.map_cons]

end OfStream

section OfList

theorem terminatedAt_ofList (l : List α) :
    (ofList l).TerminatedAt l.length := by
  simp [ofList, TerminatedAt]

theorem terminates_ofList (l : List α) : (ofList l).Terminates :=
  ⟨_, terminatedAt_ofList l⟩

end OfList

section Take

@[simp]
theorem take_nil {n : ℕ} : (nil (α := α)).take n = List.nil := by
  cases n <;> rfl

@[simp]
theorem take_zero {s : Seq α} : s.take 0 = [] := by
  cases s <;> rfl

@[simp]
theorem take_succ_cons {n : ℕ} {x : α} {s : Seq α} :
    (cons x s).take (n + 1) = x :: s.take n := by
  rfl

@[simp]
theorem getElem?_take : ∀ (n k : ℕ) (s : Seq α),
    (s.take k)[n]? = if n < k then s.get? n else none
  | n, 0, s => by simp [take]
  | n, k+1, s => by
    rw [take]
    cases h : destruct s with
    | none =>
      simp [destruct_eq_none h]
    | some a =>
      match a with
      | (x, r) =>
        rw [destruct_eq_cons h]
        match n with
        | 0 => simp
        | n+1 =>
          simp [List.getElem?_cons_succ, Nat.add_lt_add_iff_right, getElem?_take]

theorem get?_mem_take {s : Seq α} {m n : ℕ} (h_mn : m < n) {x : α}
    (h_get : s.get? m = .some x) : x ∈ s.take n := by
  induction m generalizing n s with
  | zero =>
    obtain ⟨l, hl⟩ := Nat.exists_add_one_eq.mpr h_mn
    rw [← hl, take, head_eq_some h_get]
    simp
  | succ k ih =>
    obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_lt h_mn
    subst hl
    have : ∃ y, s.get? 0 = .some y := by
      apply ge_stable _ _ h_get
      simp
    obtain ⟨y, hy⟩ := this
    rw [take, head_eq_some hy]
    simp
    right
    apply ih (by omega)
    rwa [get?_tail]

theorem length_take_le {s : Seq α} {n : ℕ} : (s.take n).length ≤ n := by
  induction n generalizing s with
  | zero => simp
  | succ m ih =>
    rw [take]
    cases s.destruct with
    | none => simp
    | some v =>
      obtain ⟨x, r⟩ := v
      simpa using ih

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

end Take

section ToList

@[simp]
theorem length_toList (s : Seq α) (h : s.Terminates) : (toList s h).length = length s h := by
  rw [toList, length_take_of_le_length]
  intro _
  exact le_rfl

@[simp]
theorem getElem?_toList (s : Seq α) (h : s.Terminates) (n : ℕ) : (toList s h)[n]? = s.get? n := by
  ext k
  simp only [ofList, toList, get?_mk, Option.mem_def, getElem?_take, Nat.lt_find_iff, length,
    Option.ite_none_right_eq_some, and_iff_right_iff_imp, TerminatedAt]
  intro h m hmn
  let ⟨a, ha⟩ := ge_stable s hmn h
  simp [ha]

@[simp]
theorem ofList_toList (s : Seq α) (h : s.Terminates) :
    ofList (toList s h) = s := by
  ext n; simp [ofList]

@[simp]
theorem toList_ofList (l : List α) : toList (ofList l) (terminates_ofList l) = l :=
  ofList_injective (by simp)

@[simp]
theorem toList_nil : toList (nil : Seq α) ⟨0, terminatedAt_zero_iff.2 rfl⟩ = [] := by
  ext; simp [nil, toList, const]

theorem getLast?_toList (s : Seq α) (h : s.Terminates) :
    (toList s h).getLast? = s.get? (s.length h - 1) := by
  rw [List.getLast?_eq_getElem?, getElem?_toList, length_toList]

end ToList

section Append

@[simp]
theorem cons_append (a : α) (s t) : append (cons a s) t = cons a (append s t) :=
  destruct_eq_cons <| by
    dsimp [append]; rw [corec_eq]
    dsimp [append]; rw [destruct_cons]

@[simp]
theorem nil_append (s : Seq α) : append nil s = s := by
  apply coinduction2; intro s
  dsimp [append]; rw [corec_eq]
  dsimp [append]
  cases s
  · trivial
  · rw [destruct_cons]
    dsimp
    exact ⟨rfl, _, rfl, rfl⟩

@[simp]
theorem append_nil (s : Seq α) : append s nil = s := by
  apply coinduction2 s; intro s
  cases s
  · trivial
  · rw [cons_append, destruct_cons, destruct_cons]
    dsimp
    exact ⟨rfl, _, rfl, rfl⟩

@[simp]
theorem append_assoc (s t u : Seq α) : append (append s t) u = append s (append t u) := by
  apply eq_of_bisim fun s1 s2 => ∃ s t u, s1 = append (append s t) u ∧ s2 = append s (append t u)
  · intro s1 s2 h
    exact
      match s1, s2, h with
      | _, _, ⟨s, t, u, rfl, rfl⟩ => by
        cases s <;> simp
        case nil =>
          cases t <;> simp
          case nil =>
            cases u <;> simp
            case cons _ u => refine ⟨nil, nil, u, ?_, ?_⟩ <;> simp
          case cons _ t => refine ⟨nil, t, u, ?_, ?_⟩ <;> simp
        case cons _ s => exact ⟨s, t, u, rfl, rfl⟩
  · exact ⟨s, t, u, rfl, rfl⟩

theorem of_mem_append {s₁ s₂ : Seq α} {a : α} (h : a ∈ append s₁ s₂) : a ∈ s₁ ∨ a ∈ s₂ := by
  have := h; revert this
  generalize e : append s₁ s₂ = ss; intro h; revert s₁
  apply mem_rec_on h _
  intro b s' o s₁
  cases s₁ with
  | nil =>
    intro m _
    apply Or.inr
    simpa using m
  | cons c t₁ =>
    intro m e
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
theorem ofList_append (l l' : List α) : ofList (l ++ l') = append (ofList l) (ofList l') := by
  induction l <;> simp [*]

@[simp]
theorem ofStream_append (l : List α) (s : Stream' α) :
    ofStream (l ++ₛ s) = append (ofList l) (ofStream s) := by
  induction l <;> simp [*, Stream'.nil_append_stream, Stream'.cons_append_stream]

end Append

section Map

@[simp]
theorem map_get? (f : α → β) : ∀ s n, get? (map f s) n = (get? s n).map f
  | ⟨_, _⟩, _ => rfl

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
theorem terminatedAt_map_iff {f : α → β} {s : Seq α} {n : ℕ} :
    (map f s).TerminatedAt n ↔ s.TerminatedAt n := by
  simp [TerminatedAt]

@[simp]
theorem terminates_map_iff {f : α → β} {s : Seq α} :
    (map f s).Terminates ↔ s.Terminates := by
  simp [Terminates]

@[simp]
theorem length_map {s : Seq α} {f : α → β} (h : (s.map f).Terminates) :
    (s.map f).length h = s.length (terminates_map_iff.1 h) := by
  rw [length]
  congr
  ext
  simp

theorem mem_map (f : α → β) {a : α} : ∀ {s : Seq α}, a ∈ s → f a ∈ map f s
  | ⟨_, _⟩ => Stream'.mem_map (Option.map f)

theorem exists_of_mem_map {f} {b : β} : ∀ {s : Seq α}, b ∈ map f s → ∃ a, a ∈ s ∧ f a = b :=
  fun {s} h => by match s with
  | ⟨g, al⟩ =>
    let ⟨o, om, oe⟩ := @Stream'.exists_of_mem_map _ _ (Option.map f) (some b) g h
    rcases o with - | a
    · injection oe
    · injection oe with h'; exact ⟨a, om, h'⟩

@[simp]
theorem map_append (f : α → β) (s t) : map f (append s t) = append (map f s) (map f t) := by
  apply
    eq_of_bisim (fun s1 s2 => ∃ s t, s1 = map f (append s t) ∧ s2 = append (map f s) (map f t)) _
      ⟨s, t, rfl, rfl⟩
  intro s1 s2 h
  exact
    match s1, s2, h with
    | _, _, ⟨s, t, rfl, rfl⟩ => by
      cases s <;> simp
      case nil =>
        cases t <;> simp
        case cons _ t => refine ⟨nil, t, ?_, ?_⟩ <;> simp
      case cons _ s => exact ⟨s, t, rfl, rfl⟩

end Map

section Join


@[simp]
theorem join_nil : join nil = (nil : Seq α) :=
  destruct_eq_none rfl

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
      cases s; · trivial
      · rw [destruct_cons]
        exact ⟨rfl, Or.inl rfl⟩
    | _, _, Or.inr ⟨a, s, S, rfl, rfl⟩ => by
      cases s
      · simp [join_cons_cons, join_cons_nil]
      · simpa [join_cons_cons, join_cons_nil] using Or.inr ⟨_, _, S, rfl, rfl⟩

@[simp]
theorem join_append (S T : Seq (Seq1 α)) : join (append S T) = append (join S) (join T) := by
  apply
    eq_of_bisim fun s1 s2 =>
      ∃ s S T, s1 = append s (join (append S T)) ∧ s2 = append s (append (join S) (join T))
  · intro s1 s2 h
    exact
      match s1, s2, h with
      | _, _, ⟨s, S, T, rfl, rfl⟩ => by
        cases s <;> simp
        case nil =>
          cases S <;> simp
          case nil =>
            cases T with
            | nil => simp
            | cons s T =>
              obtain ⟨a, s⟩ := s; simp only [join_cons, destruct_cons, true_and]
              refine ⟨s, nil, T, ?_, ?_⟩ <;> simp
          case cons s S =>
            obtain ⟨a, s⟩ := s
            simpa using ⟨s, S, T, rfl, rfl⟩
        case cons _ s => exact ⟨s, S, T, rfl, rfl⟩
  · refine ⟨nil, S, T, ?_, ?_⟩ <;> simp

end Join

section Drop

@[simp]
theorem drop_get? {n m : ℕ} {s : Seq α} : (s.drop n).get? m = s.get? (n + m) := by
  induction n generalizing m with
  | zero => simp [drop]
  | succ k ih =>
    simp [Seq.get?_tail, drop]
    convert ih using 2
    omega

theorem dropn_add (s : Seq α) (m) : ∀ n, drop s (m + n) = drop (drop s m) n
  | 0 => rfl
  | n + 1 => congr_arg tail (dropn_add s _ n)

theorem dropn_tail (s : Seq α) (n) : drop (tail s) n = drop s (n + 1) := by
  rw [Nat.add_comm]; symm; apply dropn_add

@[simp]
theorem head_dropn (s : Seq α) (n) : head (drop s n) = get? s n := by
  induction' n with n IH generalizing s; · rfl
  rw [← get?_tail, ← dropn_tail]; apply IH

@[simp]
theorem drop_succ_cons {x : α} {s : Seq α} {n : ℕ} :
    (cons x s).drop (n + 1) = s.drop n := by
  simp [← dropn_tail]

@[simp]
theorem drop_nil {n : ℕ} : (@nil α).drop n = nil := by
  induction n with
  | zero => simp [drop]
  | succ m ih => simp [← dropn_tail, ih]

theorem take_drop {s : Seq α} {n m : ℕ} :
    (s.take n).drop m = (s.drop m).take (n - m) := by
  induction m generalizing n s with
  | zero => simp [drop]
  | succ k ih =>
    cases s
    · simp
    cases n with
    | zero => simp
    | succ l =>
      simp only [take, destruct_cons, List.drop_succ_cons, Nat.reduceSubDiff]
      rw [ih]
      congr 1
      rw [drop_succ_cons]

end Drop

section ZipWith

@[simp]
theorem get?_zipWith (f : α → β → γ) (s s' n) :
    (zipWith f s s').get? n = Option.map₂ f (s.get? n) (s'.get? n) :=
  rfl

@[simp]
theorem get?_zip (s : Seq α) (t : Seq β) (n : ℕ) :
    get? (zip s t) n = Option.map₂ Prod.mk (get? s n) (get? t n) :=
  get?_zipWith _ _ _ _

@[simp]
theorem nats_get? (n : ℕ) : nats.get? n = some n :=
  rfl

@[simp]
theorem get?_enum (s : Seq α) (n : ℕ) : get? (enum s) n = Option.map (Prod.mk n) (get? s n) :=
  get?_zip _ _ _

@[simp]
theorem zipWith_nil_left {f : α → β → γ} {s} :
    zipWith f nil s = nil :=
  rfl

@[simp]
theorem zipWith_nil_right {f : α → β → γ} {s} :
    zipWith f s nil = nil := by
  ext1
  simp

@[simp]
theorem zipWith_cons_cons {f : α → β → γ} {x s x' s'} :
    zipWith f (cons x s) (cons x' s') = cons (f x x') (zipWith f s s') := by
  ext1 n
  cases n <;> simp

@[simp]
theorem zip_nil_left {s : Seq α} :
    zip (@nil α) s = nil :=
  rfl

@[simp]
theorem zip_nil_right {s : Seq α} :
    zip s (@nil α) = nil :=
  zipWith_nil_right

@[simp]
theorem zip_cons_cons {s s' : Seq α} {x x'} :
    zip (cons x s) (cons x' s') = cons (x, x') (zip s s') :=
  zipWith_cons_cons

@[simp]
theorem enum_nil : enum (nil : Seq α) = nil :=
  rfl

@[simp]
theorem enum_cons (s : Seq α) (x : α) :
    enum (cons x s) = cons (0, x) (map (Prod.map Nat.succ id) (enum s)) := by
  ext ⟨n⟩ : 1
  · simp
  · simp only [get?_enum, get?_cons_succ, map_get?, Option.map_map]
    congr

universe u' v'
variable {α' : Type u'} {β' : Type v'}

theorem zipWith_map (s₁ : Seq α) (s₂ : Seq β) (f₁ : α → α') (f₂ : β → β') (g : α' → β' → γ) :
    zipWith g (s₁.map f₁) (s₂.map f₂) = zipWith (fun a b ↦ g (f₁ a) (f₂ b)) s₁ s₂ := by
  ext1 n
  simp only [get?_zipWith, map_get?]
  cases s₁.get? n <;> cases s₂.get? n <;> simp

theorem zipWith_map_left (s₁ : Seq α) (s₂ : Seq β) (f : α → α') (g : α' → β → γ) :
    zipWith g (s₁.map f) s₂ = zipWith (fun a b ↦ g (f a) b) s₁ s₂ := by
  convert zipWith_map _ _ _ (@id β) _
  simp

theorem zipWith_map_right (s₁ : Seq α) (s₂ : Seq β) (f : β → β') (g : α → β' → γ) :
    zipWith g s₁ (s₂.map f) = zipWith (fun a b ↦ g a (f b)) s₁ s₂ := by
  convert zipWith_map _ _ (@id α) _ _
  simp

theorem zip_map (s₁ : Seq α) (s₂ : Seq β) (f₁ : α → α') (f₂ : β → β') :
    (s₁.map f₁).zip (s₂.map f₂) = (s₁.zip s₂).map (Prod.map f₁ f₂) := by
  ext1 n
  simp
  cases s₁.get? n <;> cases s₂.get? n <;> simp

theorem zip_map_left (s₁ : Seq α) (s₂ : Seq β) (f : α → α') :
    (s₁.map f).zip s₂ = (s₁.zip s₂).map (Prod.map f id) := by
  convert zip_map _ _ _ _
  simp

theorem zip_map_right (s₁ : Seq α) (s₂ : Seq β) (f : β → β') :
    s₁.zip (s₂.map f) = (s₁.zip s₂).map (Prod.map id f) := by
  convert zip_map _ _ _ _
  simp

end ZipWith

section Fold

@[simp]
theorem fold_nil (init : β) (f : β → α → β) :
    nil.fold init f = cons init nil := by
  unfold fold
  simp [corec_nil]

@[simp]
theorem fold_cons (init : β) (f : β → α → β) (x : α) (s : Seq α) :
    (cons x s).fold init f = cons init (s.fold (f init x) f) := by
  unfold fold
  dsimp only
  congr
  rw [corec_cons]
  simp

@[simp]
theorem fold_head (init : β) (f : β → α → β) (s : Seq α) :
    (s.fold init f).head = init := by
  simp [fold]

end Fold

instance : Functor Seq where map := @map

instance : LawfulFunctor Seq where
  id_map := @map_id
  comp_map := @map_comp
  map_const := rfl

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
  | ⟨a, s⟩ => by simp [bind, map, map_comp, ret]

@[simp]
theorem ret_bind (a : α) (f : α → Seq1 β) : bind (ret a) f = f a := by
  simp only [bind, map, ret.eq_1, map_nil]
  obtain ⟨a, s⟩ := f a
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
        cases s <;> simp
        case nil =>
          cases S <;> simp
          case cons x S =>
            obtain ⟨a, s⟩ := x
            simpa [map] using ⟨_, _, rfl, rfl⟩
        case cons _ s => exact ⟨s, S, rfl, rfl⟩
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
        cases s <;> simp
        case nil =>
          cases SS <;> simp
          case cons S SS =>
            obtain ⟨s, S⟩ := S; obtain ⟨x, s⟩ := s
            simp only [Seq.join_cons, join_append, destruct_cons]
            cases s <;> simp
            case nil => exact ⟨_, _, rfl, rfl⟩
            case cons x s => refine ⟨Seq.cons x (append s (Seq.join S)), SS, ?_, ?_⟩ <;> simp
        case cons _ s => exact ⟨s, SS, rfl, rfl⟩
  · refine ⟨nil, SS, ?_, ?_⟩ <;> simp

@[simp]
theorem bind_assoc (s : Seq1 α) (f : α → Seq1 β) (g : β → Seq1 γ) :
    bind (bind s f) g = bind s fun x : α => bind (f x) g := by
  obtain ⟨a, s⟩ := s
  simp only [bind, map_pair, map_join]
  rw [← map_comp]
  simp only [show (fun x => join (map g (f x))) = join ∘ (map g ∘ f) from rfl]
  rw [map_comp _ join]
  generalize Seq.map (map g ∘ f) s = SS
  rcases map g (f a) with ⟨⟨a, s⟩, S⟩
  induction' s using recOn with x s_1 <;> induction' S using recOn with x_1 s_2 <;> simp
  · obtain ⟨x, t⟩ := x_1
    cases t <;> simp
  · obtain ⟨y, t⟩ := x_1; simp

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
