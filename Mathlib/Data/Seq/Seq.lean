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

set_option linter.style.longFile 2000

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
  cases' s with f al
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
    cases' s with f al
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
  · cases' s with f al
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
  rw [head_eq_destruct, destruct_cons, Option.map_eq_map, Option.map_some']

@[simp]
theorem tail_nil : tail (nil : Seq α) = nil :=
  rfl

@[simp]
theorem tail_cons (a : α) (s) : tail (cons a s) = s := by
  cases' s with f al
  apply Subtype.eq
  dsimp [tail, cons]

theorem head_eq_some {s : Seq α} {x : α} (h : s.head = some x) :
    s = cons x s.tail := by
  ext1 n
  cases' n <;> simp
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
  cases' H : destruct s with v
  · rw [destruct_eq_none H]
    apply nil
  · cases' v with a s'
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

/-- If two streams are bisimilar, then they are equal. -/
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

/-- Version of `eq_of_bisim` that looks more like an induction principle. -/
theorem eq_of_bisim' {s₁ s₂ : Seq α}
    (motive : Seq α → Seq α → Prop)
    (h_base : motive s₁ s₂)
    (h_step : ∀ s₁ s₂, motive s₁ s₂ →
      (∃ x s₁' s₂', s₁ = cons x s₁' ∧ s₂ = cons x s₂' ∧ motive s₁' s₂') ∨
      (s₁ = nil ∧ s₂ = nil)) : s₁ = s₂ := by
  apply eq_of_bisim motive _ h_base
  intro s₁ s₂ h
  specialize h_step s₁ s₂ h
  rcases h_step with (h_cons | h_nil)
  · obtain ⟨hd, tl₁, tl₂, h₁, h₂, h_tl⟩ := h_cons
    simpa [h₁, h₂]
  · simp [h_nil.left, h_nil.right]

/-- Version of `eq_of_bisim'` that requires only `s₁ = s₂`
instead of `s₁ = nil ∧ s₂ = nil` in `h_step`. -/
theorem eq_of_bisim_strong {s₁ s₂ : Seq α}
    (motive : Seq α → Seq α → Prop)
    (h_base : motive s₁ s₂)
    (h_step : ∀ s₁ s₂, motive s₁ s₂ →
      (s₁ = s₂) ∨
      (∃ x s₁' s₂', s₁ = cons x s₁' ∧ s₂ = cons x s₂' ∧ (motive s₁' s₂'))): s₁ = s₂ := by
  let motive' : Seq α → Seq α → Prop := fun s₁ s₂ => s₁ = s₂ ∨ motive s₁ s₂
  apply eq_of_bisim' motive'
  · simp [motive']
    tauto
  intro s₁ s₂ ih
  simp only [motive'] at ih ⊢
  rcases ih with (h_eq | ih)
  · subst h_eq
    cases' s₁ with x tl
    · simp
    · simp only [cons_ne_nil, and_self, or_false]
      use x, tl, tl
      simp
  rcases h_step s₁ s₂ ih with (h_eq | h_cons)
  · subst h_eq
    cases' s₁ with x tl
    · simp
    · simp only [cons_ne_nil, and_self, or_false]
      use x, tl, tl
      simp
  · left
    obtain ⟨hd, s₁', s₂', _⟩ := h_cons
    use hd, s₁', s₂'
    tauto

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

/-- member definition for `Seq`-/
protected def Mem (s : Seq α) (a : α) :=
  some a ∈ s.1

instance : Membership α (Seq α) :=
  ⟨Seq.Mem⟩

@[simp]
theorem get?_mem {s : Seq α} {n : ℕ} {x : α} (h : s.get? n = .some x) : x ∈ s := ⟨n, h.symm⟩

@[simp]
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
  cases' s with b s'
  · injection e
  · have h_eq : (cons b s').val (Nat.succ k) = s'.val k := by cases s' using Subtype.recOn; rfl
    rw [h_eq] at e
    apply h1 _ _ (Or.inr (IH e))

/-!
### Converting from/to other types
-/

/-- Embed a list as a sequence -/
@[coe]
def ofList (l : List α) : Seq α :=
  ⟨List.get? l, fun {n} h => by
    rw [List.get?_eq_none] at h ⊢
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

@[deprecated (since := "2024-07-26")] alias ofLazyList := ofMLList

instance coeMLList : Coe (MLList Id α) (Seq α) :=
  ⟨ofMLList⟩

@[deprecated (since := "2024-07-26")] alias coeLazyList := coeMLList

/-- Translate a sequence into a `MLList`. -/
unsafe def toMLList : Seq α → MLList Id α
  | s =>
    match destruct s with
    | none => .nil
    | some (a, s') => .cons a (toMLList s')

@[deprecated (since := "2024-07-26")] alias toLazyList := toMLList

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

/-- Apply `f` to the nth element of the list, if it exists, replacing that element
with the result. -/
def modify (s : Seq α) (n : ℕ) (f : α → α) : Seq α where
  val := fun i =>
    if i = n then
      (s.val i).map f
    else
      s.val i
  property := by
    simp only [IsSeq]
    intro i h
    split_ifs with h_if
    · split_ifs at h
      · omega
      · rw [s.property h]
        rfl
    · split_ifs at h with h_if'
      · simp only [Option.map_eq_none'] at h
        exact s.property h
      · exact s.property h

/-- `s.set n a` sets the value of sequence `s` at (zero-based) index `n` to `a`. -/
def set (s : Seq α) (n : ℕ) (a : α) : Seq α :=
  modify s n (fun _ ↦ a)

/-!
### Predicates on sequences
-/

-- Note: without `irreducible` attribute it is inconvenient to apply lemmas about it, because Lean
-- eagerly unfolds `All` and unifyes `p x` with the goal (even if the goal is in form `s.All p`).
/-- `s.All p` means that the predicate `p` is true on each element of `s`. -/
@[irreducible]
def All (s : Seq α) (p : α → Prop) : Prop := ∀ x ∈ s, p x

-- Note: `irreducible` here is necessary for the same reason as for `All` above
/--
`Pairwise R s` means that all the elements with earlier indexes are
`R`-related to all the elements with later indexes.
```
Pairwise R [1, 2, 3] ↔ R 1 2 ∧ R 1 3 ∧ R 2 3
```
For example if `R = (·≠·)` then it asserts `s` has no duplicates,
and if `R = (·<·)` then it asserts that `s` is (strictly) sorted.
-/
@[irreducible]
def Pairwise (R : α → α → Prop) (s : Seq α) : Prop :=
  ∀ i j x y, i < j → s.get? i = .some x → s.get? j = .some y → R x y

/-- `s₁.AtLeastAsLongAs s₂` means that `s₁` has at least as many elements as sequence `s₂`.
In particular, they both may be infinite. -/
def AtLeastAsLongAs (a : Seq α) (b : Seq β) : Prop :=
  ∀ n, a.TerminatedAt n → b.TerminatedAt n

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
        | n+1 => simp [List.get?_cons_succ, Nat.add_lt_add_iff_right, get?_cons_succ, getElem?_take]

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
    simp only [destruct_cons, List.mem_cons]
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
  cases' s with x s
  · trivial
  · rw [destruct_cons]
    dsimp
    exact ⟨rfl, s, rfl, rfl⟩

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
    cases' show a = c ∨ a ∈ append t₁ s₂ by simpa using m with e' m
    · rw [e']
      exact Or.inl (mem_cons _ _)
    · cases' show c = b ∧ append t₁ s₂ = s' by simpa with i1 i2
      cases' o with e' IH
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

theorem mem_map (f : α → β) {a : α} : ∀ {s : Seq α}, a ∈ s → f a ∈ map f s
  | ⟨_, _⟩ => Stream'.mem_map (Option.map f)

theorem exists_of_mem_map {f} {b : β} : ∀ {s : Seq α}, b ∈ map f s → ∃ a, a ∈ s ∧ f a = b :=
  fun {s} h => by match s with
  | ⟨g, al⟩ =>
    let ⟨o, om, oe⟩ := @Stream'.exists_of_mem_map _ _ (Option.map f) (some b) g h
    cases' o with a
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
      cases' s with _ s <;> simp
      · cases' t with _ t <;> simp
        · refine ⟨nil, t, ?_, ?_⟩ <;> simp
      · exact ⟨s, t, rfl, rfl⟩

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
theorem drop_zero {s : Seq α} : s.drop 0 = s := by
  rfl

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
    cases' s with x tl
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
  cases' n <;> simp

@[simp]
theorem zip_nil_left {s : Seq α} :
    zip (@nil β) s = nil :=
  rfl

@[simp]
theorem zip_nil_right {s : Seq α} :
    zip s (@nil β) = nil :=
  zipWith_nil_right

@[simp]
theorem zip_cons_cons {s : Seq α} {s' : Seq β} {x x'} :
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
  simp only [get?_zip, map_get?]
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

section Modify

@[simp]
theorem modify_nil {f : α → α} {n} :
    modify nil n f = nil := by
  simp [modify]
  rfl

@[simp]
theorem set_nil {n : ℕ} {x : α} :
    set nil n x = nil :=
  modify_nil

@[simp]
theorem modify_cons_zero {f : α → α} {hd : α} {tl : Seq α} :
    (cons hd tl).modify 0 f = cons (f hd) tl := by
  ext1 n
  cases n <;> simp [modify]

@[simp]
theorem set_cons_zero {hd hd' : α} {tl : Seq α} :
    (cons hd tl).set 0 hd' = cons hd' tl :=
  modify_cons_zero

@[simp]
theorem modify_cons_succ {hd : α} {f : α → α} {n : ℕ} {tl : Seq α} :
    (cons hd tl).modify (n + 1) f = cons hd (tl.modify n f) := by
  ext1 n
  cases n <;> simp [modify]

@[simp]
theorem set_cons_succ {hd x : α} {n : ℕ} {tl : Seq α} :
    (cons hd tl).set (n + 1) x = cons hd (tl.set n x) :=
  modify_cons_succ

theorem set_get_of_not_terminated {s : Seq α} {x : α} {n : ℕ}
    (h_not_terminated : ¬ s.TerminatedAt n) :
    (s.set n x).get? n = x := by
  simp [set, modify]
  simp [TerminatedAt] at h_not_terminated
  cases h : s.get? n with
  | none => simp [h] at h_not_terminated
  | some => simp

theorem set_get_of_terminated {s : Seq α} {x : α} {n : ℕ}
    (h_terminated : s.TerminatedAt n) :
    (s.set n x).get? n = .none := by
  simp [set, modify]
  simpa [TerminatedAt] using h_terminated

theorem set_get_stable {s : Seq α} {x : α} {n m : ℕ}
    (h : n ≠ m) :
    (s.set m x).get? n = s.get? n := by
  simp [set, modify]
  intro h'
  exact (h h').elim

theorem set_dropn_stable_of_lt {s : Seq α} {m n : ℕ} {x : α}
    (h : m < n) :
    (s.set m x).drop n = s.drop n := by
  ext1 i
  simp only [drop_get?]
  rw [set_get_stable]
  omega

end Modify

section All

@[simp]
theorem All.nil {p : α → Prop} : nil.All p := by
  simp [All]

theorem All.cons {p : α → Prop} {hd : α} {tl : Seq α} (h_hd : p hd) (h_tl : tl.All p) :
    ((cons hd tl).All p) := by
  simp only [All, mem_cons_iff, forall_eq_or_imp] at *
  exact ⟨h_hd, h_tl⟩

@[simp]
theorem All_cons_iff {p : α → Prop} {hd : α} {tl : Seq α} :
    ((cons hd tl).All p) ↔ p hd ∧ tl.All p := by
  simp [All]

theorem All_get {p : α → Prop} {s : Seq α} (h : s.All p) {n : ℕ} {x : α} (hx : s.get? n = .some x) :
    p x := by
  unfold All at h
  exact h _ (get?_mem hx)

theorem All_of_get {p : α → Prop} {s : Seq α} (h : ∀ n x, s.get? n = .some x → p x) :
    s.All p := by
  simp [All, Membership.mem, Seq.Mem, Any, get]
  intro x i hx
  simpa [← hx] using h i

/-- Coinductive principle for `All`. -/
theorem All.coind {s : Seq α} {p : α → Prop}
    (motive : Seq α → Prop) (h_base : motive s)
    (h_cons : ∀ hd tl, motive (.cons hd tl) → p hd ∧ motive tl) : s.All p := by
  apply All_of_get
  intro n
  have : (s.get? n).elim True p ∧ motive (s.drop n) := by
    induction n with
    | zero =>
      cases h1 : get? s 0 with
      | none =>
        constructor
        · simp
        · simpa
      | some hd =>
        simp only [Option.elim_some, drop_zero]
        have := head_eq_some h1
        specialize h_cons hd s.tail (this ▸ h_base)
        constructor
        · exact h_cons.left
        · exact h_base
    | succ m ih =>
      simp at ih
      simp only [drop, ← head_dropn]
      generalize s.drop m = t at ih
      cases' t with hd tl
      · simp [ih.right]
      · simp
        obtain ⟨h1, h2⟩ := ih
        have : motive tl := by
          specialize h_cons hd tl h2
          exact h_cons.right
        constructor
        · cases h_head : tl.head with
          | none => simp
          | some tl_hd =>
            have h_tl_cons := head_eq_some h_head
            specialize h_cons tl_hd tl.tail (h_tl_cons ▸ this)
            simp only [Option.elim_some]
            exact h_cons.left
        · assumption
  intro x hx
  simp only [hx, Option.elim_some] at this
  exact this.left

theorem All_mp {p q : α → Prop} (h : ∀ a, p a → q a) {s : Seq α} (hp : s.All p) :
    s.All q := by
  simp only [All] at hp ⊢
  tauto

theorem map_All_iff {β : Type u} {f : α → β} {p : β → Prop} {s : Seq α} :
    (s.map f).All p ↔ s.All (p ∘ f) := by
  simp [All]
  refine ⟨fun _ _ hx ↦ ?_, fun _ _ hx ↦ ?_⟩
  · solve_by_elim [mem_map f hx]
  · obtain ⟨_, _, hx'⟩ := exists_of_mem_map hx
    rw [← hx']
    solve_by_elim

theorem take_All {s : Seq α} {p : α → Prop} (h_all : s.All p) {n : ℕ} :
    ∀ x ∈ s.take n, p x := by
  intro x hx
  induction n generalizing s with
  | zero => simp [take] at hx
  | succ m ih =>
    cases' s with hd tl
    · simp at hx
    · simp only [take_succ_cons, List.mem_cons, All_cons_iff] at hx h_all
      rcases hx with (hx | hx)
      · exact hx ▸ h_all.left
      · exact ih h_all.right hx

theorem set_All {p : α → Prop} {s : Seq α} (h_all : s.All p) {n : ℕ} {x : α}
    (hx : p x) : (s.set n x).All p := by
  apply All_of_get
  intro m
  by_cases h_nm : n = m
  · subst h_nm
    by_cases h_term : s.TerminatedAt n
    · simp [set_get_of_terminated h_term]
    · simpa [set_get_of_not_terminated h_term]
  · rw [set_get_stable]
    · intro x hx
      exact All_get h_all hx
    · omega

end All

section Pairwise

@[simp]
theorem Pairwise.nil {R : α → α → Prop} : Pairwise R (@nil α) := by
  simp [Pairwise]

theorem Pairwise.cons {R : α → α → Prop} {hd : α} {tl : Seq α}
    (h_lt : tl.All (R hd ·))
    (h_tl : Pairwise R tl) : Pairwise R (cons hd tl) := by
  simp [Pairwise] at *
  intro i j x y h_ij hx hy
  cases j with
  | zero =>
    simp at h_ij
  | succ k =>
    simp at hy
    cases i with
    | zero =>
      simp at hx
      rw [← hx]
      exact All_get h_lt hy
    | succ n =>
      exact h_tl n k x y (by omega) hx hy

theorem Pairwise.cons_elim {R : α → α → Prop} {hd : α} {tl : Seq α}
    (h : Pairwise R (.cons hd tl)) : tl.All (R hd ·) ∧ Pairwise R tl := by
  simp only [Pairwise] at h
  constructor
  · apply All_of_get
    intro n
    specialize h 0 (n + 1) hd
    simp only [Nat.zero_lt_succ, get?_cons_zero, get?_cons_succ, forall_const] at h
    cases' h_tl : tl.get? n with y
    · simp
    · simp [h y h_tl]
  · simp [Pairwise]
    exact fun i j x y h_ij hx hy ↦ h (i + 1) (j + 1) x y (by omega) hx hy

theorem Pairwise.cons_cons_elim_of_trans {R : α → α → Prop} {hd tl_hd : α}
    {tl_tl : Seq α} (h : Pairwise R (.cons hd (.cons tl_hd tl_tl))) :
    R hd tl_hd ∧ Pairwise R (.cons tl_hd tl_tl) := by
  apply Pairwise.cons_elim at h
  rw [All_cons_iff] at h
  tauto

@[simp]
theorem Pairwise_cons_nil {R : α → α → Prop} {hd : α} : Pairwise R (cons hd nil) := by
  apply Pairwise.cons <;> simp

theorem Pairwise_cons_cons_head {R : α → α → Prop} {hd tl_hd : α} {tl_tl : Seq α}
    (h : Pairwise R (cons hd (cons tl_hd tl_tl))) :
    R hd tl_hd := by
  simp only [Pairwise] at h
  simpa using h 0 1 hd tl_hd Nat.one_pos

theorem Pairwise.cons_cons_of_trans {R : α → α → Prop} [IsTrans _ R] {hd tl_hd : α} {tl_tl : Seq α}
    (h_lt : R hd tl_hd)
    (h_tl : Pairwise R (.cons tl_hd tl_tl)) : Pairwise R (.cons hd (.cons tl_hd tl_tl)) := by
  apply Pairwise.cons _ h_tl
  simp only [All_cons_iff]
  refine ⟨h_lt, ?_⟩
  apply All_mp _ h_tl.cons_elim.left
  intro x h
  exact trans_of _ h_lt h

/-- Coinductive principle for `Pairwise`. -/
theorem Pairwise.coind {R : α → α → Prop} {s : Seq α}
    (motive : Seq α → Prop) (h_base : motive s)
    (h_step : ∀ hd tl, motive (.cons hd tl) → tl.All (R hd ·) ∧ motive tl) : Pairwise R s := by
  have h_all : ∀ n, motive (s.drop n) := by
    intro n
    induction n with
    | zero => simpa
    | succ m ih =>
      simp only [drop]
      generalize s.drop m = t at *
      cases' t with hd tl
      · simpa
      · exact (h_step hd tl ih).right
  simp only [Pairwise]
  intro i j x y h_ij hx hy
  replace h_ij := Nat.exists_eq_add_of_lt h_ij
  obtain ⟨k, hj⟩ := h_ij
  rw [Nat.add_assoc, Nat.add_comm] at hj
  subst hj
  rw [show k + 1 + i = i + 1 + k by omega] at hy
  simp only [← head_dropn] at hx
  rw [← head_dropn, dropn_add, drop, head_dropn] at hy
  have := (h_step x (s.drop i).tail (by convert h_all i; rw [head_eq_some hx, tail_cons])).left
  exact All_get this hy


/-- Coinductive principle for `Pairwise` that assumes that `R` is transitive. It allows to prove
`R hd tl.head` instead of `tl.All (R hd ·)` in `h_step`. -/
theorem Pairwise.coind_trans {R : α → α → Prop} [IsTrans _ R] {s : Seq α}
    (motive : Seq α → Prop) (h_base : motive s)
    (h_step : ∀ hd tl, motive (.cons hd tl) → tl.head.elim True (R hd ·) ∧ motive tl) :
    Pairwise R s := by
  have h_all : ∀ n, motive (s.drop n) := by
    intro n
    induction n with
    | zero => simpa
    | succ m ih =>
      simp only [drop]
      generalize s.drop m = t at *
      cases' t with hd tl
      · simpa
      · exact (h_step hd tl ih).right
  simp only [Pairwise]
  intro i j x y h_ij hx hy
  replace h_ij := Nat.exists_eq_add_of_lt h_ij
  obtain ⟨k, hj⟩ := h_ij
  rw [Nat.add_assoc, Nat.add_comm] at hj
  subst hj
  induction k generalizing i x with
  | zero =>
    simp only [← head_dropn] at hx
    rw [Nat.zero_add, Nat.add_comm, ← head_dropn, drop] at hy
    have := (h_step x (s.drop i).tail (by convert h_all i; rw [head_eq_some hx, tail_cons])).left
    simpa only [hy, Option.elim_some] using this
  | succ k ih =>
    obtain ⟨z, hz⟩ := ge_stable (m := i + 1) _ (by omega) hy
    trans z
    · simp only [← head_dropn, drop] at hx hz
      simpa [hz] using
        (h_step x (s.drop i).tail (by convert h_all i; rw [head_eq_some hx, tail_cons])).left
    · exact ih (i + 1) z hz (by convert hy using 2; omega)

theorem Pairwise_tail {R : α → α → Prop} {s : Seq α} (h : s.Pairwise R) :
    s.tail.Pairwise R := by
  cases' s with hd tl
  · simp
  · simp only [tail_cons]
    exact h.cons_elim.right

theorem Pairwise_drop {R : α → α → Prop} {s : Seq α} (h : s.Pairwise R) {n : ℕ} :
    (s.drop n).Pairwise R := by
  induction n with
  | zero => simpa
  | succ m ih =>
    simp only [drop]
    exact Pairwise_tail ih

end Pairwise

section AtLeastAsLongAs

@[simp]
theorem AtLeastAsLongAs.nil {a : Seq α} :
    a.AtLeastAsLongAs (@nil β) := by
  unfold AtLeastAsLongAs
  simp

theorem AtLeastAsLongAs.cons {a_hd : α} {a_tl : Seq α} {b_hd : β} {b_tl : Seq β}
    (h : a_tl.AtLeastAsLongAs b_tl) :
    (Seq.cons a_hd a_tl).AtLeastAsLongAs (Seq.cons b_hd b_tl) := by
  simp only [AtLeastAsLongAs] at *
  intro n
  cases n with
  | zero => simp
  | succ m => simpa using h m

theorem AtLeastAsLongAs.cons_elim {a : Seq α} {hd : β} {tl : Seq β}
    (h : a.AtLeastAsLongAs (.cons hd tl)) : ∃ hd' tl', a = .cons hd' tl' := by
  cases' a with hd' tl'
  · unfold AtLeastAsLongAs at h
    simp only [terminatedAt_nil, forall_const] at h
    specialize h 0
    simp [TerminatedAt] at h
  · use hd', tl'

@[simp]
theorem cons_AtLeastAsLongAs_cons {a_hd : α} {a_tl : Seq α} {b_hd : β}
    {b_tl : Seq β} :
    (cons a_hd a_tl).AtLeastAsLongAs (cons b_hd b_tl) ↔ a_tl.AtLeastAsLongAs b_tl := by
  refine ⟨fun h ↦ ?_, fun h ↦ AtLeastAsLongAs.cons h⟩
  simp [AtLeastAsLongAs] at *
  intro n
  specialize h (n + 1)
  simpa using h

theorem AtLeastAsLongAs_map {α : Type v} {γ : Type w} {f : β → γ} {a : Seq α}
    {b : Seq β} (h : a.AtLeastAsLongAs b):
    a.AtLeastAsLongAs (b.map f) := by
  simp only [AtLeastAsLongAs, terminatedAt_map_iff] at h ⊢
  intro n ha
  simpa [TerminatedAt] using h n ha

/-- Coinductive principle for `AtLeastAsLongAs`. -/
theorem AtLeastAsLongAs.coind {a : Seq α} {b : Seq β}
    (motive : Seq α → Seq β → Prop) (h_base : motive a b)
    (h_step : ∀ a b, motive a b →
      (∀ b_hd b_tl, (b = .cons b_hd b_tl) → ∃ a_hd a_tl, a = .cons a_hd a_tl ∧ motive a_tl b_tl)) :
      a.AtLeastAsLongAs b := by
  simp only [AtLeastAsLongAs, TerminatedAt, ← head_dropn]
  intro n
  have : b.drop n ≠ .nil → motive (a.drop n) (b.drop n) := by
    intro hb
    induction n with
    | zero => simpa
    | succ m ih =>
      simp only [drop] at hb ⊢
      generalize b.drop m = tb at *
      cases' tb with tb_hd tb_tl
      · simp at hb
      · simp at ih
        obtain ⟨a_hd, a_tl, ha, h_tail⟩ := h_step (a.drop m) (.cons tb_hd tb_tl) ih _ _ (by rfl)
        rw [ha]
        simpa
  contrapose
  intro hb
  rw [head_eq_none_iff] at hb
  generalize b.drop n = tb at *
  cases' tb with tb_hd tb_tl
  · simp at hb
  · obtain ⟨a_hd, a_tl, ha, _⟩ := h_step _ _ (this hb) _ _ (by rfl)
    simp [ha]

end AtLeastAsLongAs

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
