/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Seq.Seq
import Mathlib.Util.CompileInductive

/-!
# Partially defined possibly infinite lists

This file provides a `WSeq α` type representing partially defined possibly infinite lists
(referred here as weak sequences).
-/

namespace Stream'

open Function

universe u v w

/-- Weak sequences.

  While the `Seq` structure allows for lists which may not be finite,
  a weak sequence also allows the computation of each element to
  involve an indeterminate amount of computation, including possibly
  an infinite loop. This is represented as a regular `Seq` interspersed
  with `none` elements to indicate that computation is ongoing.

  This model is appropriate for Haskell style lazy lists, and is closed
  under most interesting computation patterns on infinite lists,
  but conversely it is difficult to extract elements from it. -/
def WSeq (α) :=
  Seq (Option α)

namespace WSeq

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Turn a sequence into a weak sequence -/
@[coe]
def ofSeq : Seq α → WSeq α :=
  (· <$> ·) some

/-- Turn a list into a weak sequence -/
@[coe]
def ofList (l : List α) : WSeq α :=
  ofSeq l

/-- Turn a stream into a weak sequence -/
@[coe]
def ofStream (l : Stream' α) : WSeq α :=
  ofSeq l

instance coeSeq : Coe (Seq α) (WSeq α) :=
  ⟨ofSeq⟩

instance coeList : Coe (List α) (WSeq α) :=
  ⟨ofList⟩

instance coeStream : Coe (Stream' α) (WSeq α) :=
  ⟨ofStream⟩

/-- The empty weak sequence -/
def nil : WSeq α :=
  Seq.nil

instance inhabited : Inhabited (WSeq α) :=
  ⟨nil⟩

/-- Prepend an element to a weak sequence -/
def cons (a : α) : WSeq α → WSeq α :=
  Seq.cons (some a)

/-- Compute for one tick, without producing any elements -/
def think : WSeq α → WSeq α :=
  Seq.cons none

/-- Destruct a weak sequence, to (eventually possibly) produce either
  `none` for `nil` or `some (a, s)` if an element is produced. -/
def destruct : WSeq α → Computation (Option (α × WSeq α)) :=
  Computation.corec fun s =>
    match Seq.destruct s with
    | none => Sum.inl none
    | some (none, s') => Sum.inr s'
    | some (some a, s') => Sum.inl (some (a, s'))

/-- Recursion principle for weak sequences, compare with `List.recOn`. -/
def recOn {C : WSeq α → Sort v} (s : WSeq α) (h1 : C nil) (h2 : ∀ x s, C (cons x s))
    (h3 : ∀ s, C (think s)) : C s :=
  Seq.recOn s h1 fun o => Option.recOn o h3 h2

/-- membership for weak sequences -/
protected def Mem (s : WSeq α) (a : α) :=
  Seq.Mem s (some a)

instance membership : Membership α (WSeq α) :=
  ⟨WSeq.Mem⟩

theorem notMem_nil (a : α) : a ∉ @nil α :=
  Seq.notMem_nil (some a)

@[deprecated (since := "2025-05-23")] alias not_mem_nil := notMem_nil

/-- Get the head of a weak sequence. This involves a possibly
  infinite computation. -/
def head (s : WSeq α) : Computation (Option α) :=
  Computation.map (Prod.fst <$> ·) (destruct s)

/-- Encode a computation yielding a weak sequence into additional
  `think` constructors in a weak sequence -/
def flatten : Computation (WSeq α) → WSeq α :=
  Seq.corec fun c =>
    match Computation.destruct c with
    | Sum.inl s => Seq.omap (return ·) (Seq.destruct s)
    | Sum.inr c' => some (none, c')

/-- Get the tail of a weak sequence. This doesn't need a `Computation`
  wrapper, unlike `head`, because `flatten` allows us to hide this
  in the construction of the weak sequence itself. -/
def tail (s : WSeq α) : WSeq α :=
  flatten <| (fun o => Option.recOn o nil Prod.snd) <$> destruct s

/-- drop the first `n` elements from `s`. -/
def drop (s : WSeq α) : ℕ → WSeq α
  | 0 => s
  | n + 1 => tail (drop s n)

/-- Get the nth element of `s`. -/
def get? (s : WSeq α) (n : ℕ) : Computation (Option α) :=
  head (drop s n)

/-- Convert `s` to a list (if it is finite and completes in finite time). -/
def toList (s : WSeq α) : Computation (List α) :=
  @Computation.corec (List α) (List α × WSeq α)
    (fun ⟨l, s⟩ =>
      match Seq.destruct s with
      | none => Sum.inl l.reverse
      | some (none, s') => Sum.inr (l, s')
      | some (some a, s') => Sum.inr (a::l, s'))
    ([], s)

/-- Append two weak sequences. As with `Seq.append`, this may not use
  the second sequence if the first one takes forever to compute -/
def append : WSeq α → WSeq α → WSeq α :=
  Seq.append

/-- Flatten a sequence of weak sequences. (Note that this allows
  empty sequences, unlike `Seq.join`.) -/
def join (S : WSeq (WSeq α)) : WSeq α :=
  Seq.join
    ((fun o : Option (WSeq α) =>
        match o with
        | none => Seq1.ret none
        | some s => (none, s)) <$>
      S)

/-- Map a function over a weak sequence -/
def map (f : α → β) : WSeq α → WSeq β :=
  Seq.map (Option.map f)

/-- The monadic `return a` is a singleton list containing `a`. -/
def ret (a : α) : WSeq α :=
  ofList [a]

/-- Monadic bind operator for weak sequences -/
def bind (s : WSeq α) (f : α → WSeq β) : WSeq β :=
  join (map f s)

/-- Unfortunately, `WSeq` is not a lawful monad, because it does not satisfy the monad laws exactly,
only up to sequence equivalence. Furthermore, even quotienting by the equivalence is not sufficient,
because the join operation involves lists of quotient elements, with a lifted equivalence relation,
and pure quotients cannot handle this type of construction. -/
instance monad : Monad WSeq where
  map := @map
  pure := @ret
  bind := @bind

open Computation

@[simp]
theorem destruct_nil : destruct (nil : WSeq α) = Computation.pure none :=
  Computation.destruct_eq_pure rfl

@[simp]
theorem destruct_cons (a : α) (s) : destruct (cons a s) = Computation.pure (some (a, s)) :=
  Computation.destruct_eq_pure <| by simp [destruct, cons, Computation.rmap]

@[simp]
theorem destruct_think (s : WSeq α) : destruct (think s) = (destruct s).think :=
  Computation.destruct_eq_think <| by simp [destruct, think, Computation.rmap]

@[simp]
theorem seq_destruct_nil : Seq.destruct (nil : WSeq α) = none :=
  Seq.destruct_nil

@[simp]
theorem seq_destruct_cons (a : α) (s) : Seq.destruct (cons a s) = some (some a, s) :=
  Seq.destruct_cons _ _

@[simp]
theorem seq_destruct_think (s : WSeq α) : Seq.destruct (think s) = some (none, s) :=
  Seq.destruct_cons _ _

@[simp]
theorem head_nil : head (nil : WSeq α) = Computation.pure none := by simp [head]

@[simp]
theorem head_cons (a : α) (s) : head (cons a s) = Computation.pure (some a) := by simp [head]

@[simp]
theorem head_think (s : WSeq α) : head (think s) = (head s).think := by simp [head]

@[simp]
theorem flatten_pure (s : WSeq α) : flatten (Computation.pure s) = s := by
  refine Seq.eq_of_bisim (fun s1 s2 => flatten (Computation.pure s2) = s1) ?_ rfl
  intro s' s h
  rw [← h]
  simp only [Seq.BisimO, flatten, Seq.omap, pure_def, Seq.corec_eq, destruct_pure]
  cases Seq.destruct s with
  | none => simp
  | some val =>
    obtain ⟨o, s'⟩ := val
    simp

@[simp]
theorem flatten_think (c : Computation (WSeq α)) : flatten c.think = think (flatten c) :=
  Seq.destruct_eq_cons <| by simp [flatten, think]

@[simp]
theorem destruct_flatten (c : Computation (WSeq α)) : destruct (flatten c) = c >>= destruct := by
  refine
    Computation.eq_of_bisim
      (fun c1 c2 => c1 = c2 ∨ ∃ c, c1 = destruct (flatten c) ∧ c2 = Computation.bind c destruct) ?_
      (Or.inr ⟨c, rfl, rfl⟩)
  intro c1 c2 h
  exact
    match c1, c2, h with
    | c, _, Or.inl rfl => by cases c.destruct <;> simp
    | _, _, Or.inr ⟨c, rfl, rfl⟩ => by
      induction' c using Computation.recOn with a c'
      · simp; cases (destruct a).destruct <;> simp
      · simpa using Or.inr ⟨c', rfl, rfl⟩

theorem head_terminates_iff (s : WSeq α) : Terminates (head s) ↔ Terminates (destruct s) :=
  terminates_map_iff _ (destruct s)

@[simp]
theorem tail_nil : tail (nil : WSeq α) = nil := by simp [tail]

@[simp]
theorem tail_cons (a : α) (s) : tail (cons a s) = s := by simp [tail]

@[simp]
theorem tail_think (s : WSeq α) : tail (think s) = (tail s).think := by simp [tail]

@[simp]
theorem dropn_nil (n) : drop (nil : WSeq α) n = nil := by induction n <;> simp [*, drop]

@[simp]
theorem dropn_cons (a : α) (s) (n) : drop (cons a s) (n + 1) = drop s n := by
  induction n with
  | zero => simp [drop]
  | succ n n_ih =>
    simp [drop, ← n_ih]

@[simp]
theorem dropn_think (s : WSeq α) (n) : drop (think s) n = (drop s n).think := by
  induction n <;> simp [*, drop]

theorem dropn_add (s : WSeq α) (m) : ∀ n, drop s (m + n) = drop (drop s m) n
  | 0 => rfl
  | n + 1 => congr_arg tail (dropn_add s m n)

theorem dropn_tail (s : WSeq α) (n) : drop (tail s) n = drop s (n + 1) := by
  rw [Nat.add_comm]
  symm
  apply dropn_add

theorem get?_add (s : WSeq α) (m n) : get? s (m + n) = get? (drop s m) n :=
  congr_arg head (dropn_add _ _ _)

theorem get?_tail (s : WSeq α) (n) : get? (tail s) n = get? s (n + 1) :=
  congr_arg head (dropn_tail _ _)

@[simp]
theorem join_nil : join nil = (nil : WSeq α) :=
  Seq.join_nil

@[simp]
theorem join_think (S : WSeq (WSeq α)) : join (think S) = think (join S) := by
  simp only [join, think]
  dsimp only [(· <$> ·)]
  simp [join, Seq1.ret]

@[simp]
theorem join_cons (s : WSeq α) (S) : join (cons s S) = think (append s (join S)) := by
  simp only [join, think]
  dsimp only [(· <$> ·)]
  simp [join, cons, append]

@[simp]
theorem nil_append (s : WSeq α) : append nil s = s :=
  Seq.nil_append _

@[simp]
theorem cons_append (a : α) (s t) : append (cons a s) t = cons a (append s t) :=
  Seq.cons_append _ _ _

@[simp]
theorem think_append (s t : WSeq α) : append (think s) t = think (append s t) :=
  Seq.cons_append _ _ _

@[simp]
theorem append_nil (s : WSeq α) : append s nil = s :=
  Seq.append_nil _

@[simp]
theorem append_assoc (s t u : WSeq α) : append (append s t) u = append s (append t u) :=
  Seq.append_assoc _ _ _

/-- auxiliary definition of tail over weak sequences -/
@[simp]
def tail.aux : Option (α × WSeq α) → Computation (Option (α × WSeq α))
  | none => Computation.pure none
  | some (_, s) => destruct s

theorem destruct_tail (s : WSeq α) : destruct (tail s) = destruct s >>= tail.aux := by
  simp only [tail, destruct_flatten, tail.aux]; rw [← bind_pure_comp, LawfulMonad.bind_assoc]
  apply congr_arg; ext1 (_ | ⟨a, s⟩) <;> apply (@pure_bind Computation _ _ _ _ _ _).trans _ <;> simp

/-- auxiliary definition of drop over weak sequences -/
@[simp]
def drop.aux : ℕ → Option (α × WSeq α) → Computation (Option (α × WSeq α))
  | 0 => Computation.pure
  | n + 1 => fun a => tail.aux a >>= drop.aux n

theorem drop.aux_none : ∀ n, @drop.aux α n none = Computation.pure none
  | 0 => rfl
  | n + 1 =>
    show Computation.bind (Computation.pure none) (drop.aux n) = Computation.pure none by
      rw [ret_bind, drop.aux_none n]

theorem destruct_dropn : ∀ (s : WSeq α) (n), destruct (drop s n) = destruct s >>= drop.aux n
  | _, 0 => (bind_pure' _).symm
  | s, n + 1 => by
    rw [← dropn_tail, destruct_dropn _ n, destruct_tail, LawfulMonad.bind_assoc]
    rfl

theorem head_terminates_of_head_tail_terminates (s : WSeq α) [T : Terminates (head (tail s))] :
    Terminates (head s) :=
  (head_terminates_iff _).2 <| by
    rcases (head_terminates_iff _).1 T with ⟨⟨a, h⟩⟩
    simp? [tail] at h says simp only [tail, destruct_flatten, bind_map_left] at h
    rcases exists_of_mem_bind h with ⟨s', h1, _⟩
    exact terminates_of_mem h1

theorem destruct_some_of_destruct_tail_some {s : WSeq α} {a} (h : some a ∈ destruct (tail s)) :
    ∃ a', some a' ∈ destruct s := by
  unfold tail Functor.map at h; simp only [destruct_flatten] at h
  rcases exists_of_mem_bind h with ⟨t, tm, td⟩; clear h
  rcases Computation.exists_of_mem_map tm with ⟨t', ht', ht2⟩; clear tm
  rcases t' with - | t' <;> rw [← ht2] at td <;> simp only [destruct_nil] at td
  · have := mem_unique td (ret_mem _)
    contradiction
  · exact ⟨_, ht'⟩

theorem head_some_of_head_tail_some {s : WSeq α} {a} (h : some a ∈ head (tail s)) :
    ∃ a', some a' ∈ head s := by
  unfold head at h
  rcases Computation.exists_of_mem_map h with ⟨o, md, e⟩; clear h
  rcases o with - | o <;> [injection e; injection e with h']; clear h'
  obtain ⟨a, am⟩ := destruct_some_of_destruct_tail_some md
  exact ⟨_, Computation.mem_map (@Prod.fst α (WSeq α) <$> ·) am⟩

theorem head_some_of_get?_some {s : WSeq α} {a n} (h : some a ∈ get? s n) :
    ∃ a', some a' ∈ head s := by
  induction n generalizing a with
  | zero => exact ⟨_, h⟩
  | succ n IH =>
      let ⟨a', h'⟩ := head_some_of_head_tail_some h
      exact IH h'

theorem get?_terminates_le {s : WSeq α} {m n} (h : m ≤ n) :
    Terminates (get? s n) → Terminates (get? s m) := by
  induction' h with m' _ IH
  exacts [id, fun T => IH (@head_terminates_of_head_tail_terminates _ _ T)]

theorem head_terminates_of_get?_terminates {s : WSeq α} {n} :
    Terminates (get? s n) → Terminates (head s) :=
  get?_terminates_le (Nat.zero_le n)

theorem destruct_terminates_of_get?_terminates {s : WSeq α} {n} (T : Terminates (get? s n)) :
    Terminates (destruct s) :=
  (head_terminates_iff _).1 <| head_terminates_of_get?_terminates T

theorem mem_rec_on {C : WSeq α → Prop} {a s} (M : a ∈ s) (h1 : ∀ b s', a = b ∨ C s' → C (cons b s'))
    (h2 : ∀ s, C s → C (think s)) : C s := by
  apply Seq.mem_rec_on M
  intro o s' h; rcases o with - | b
  · apply h2
    cases h
    · contradiction
    · assumption
  · apply h1
    apply Or.imp_left _ h
    intro h
    injection h

@[simp]
theorem mem_think (s : WSeq α) (a) : a ∈ think s ↔ a ∈ s := by
  obtain ⟨f, al⟩ := s
  change (some (some a) ∈ some none::f) ↔ some (some a) ∈ f
  constructor <;> intro h
  · apply (Stream'.eq_or_mem_of_mem_cons h).resolve_left
    intro
    injections
  · apply Stream'.mem_cons_of_mem _ h

theorem eq_or_mem_iff_mem {s : WSeq α} {a a' s'} :
    some (a', s') ∈ destruct s → (a ∈ s ↔ a = a' ∨ a ∈ s') := by
  generalize e : destruct s = c; intro h
  revert s
  apply Computation.memRecOn h <;> [skip; intro c IH] <;> intro s <;>
    induction' s using WSeq.recOn with x s s <;>
    intro m <;>
    have := congr_arg Computation.destruct m <;>
    simp at this
  · obtain ⟨i1, i2⟩ := this
    rw [i1, i2]
    obtain ⟨f, al⟩ := s'
    dsimp only [cons, Membership.mem, WSeq.Mem, Seq.Mem, Seq.cons]
    have h_a_eq_a' : a = a' ↔ some (some a) = some (some a') := by simp
    rw [h_a_eq_a']
    refine ⟨Stream'.eq_or_mem_of_mem_cons, fun o => ?_⟩
    · rcases o with e | m
      · rw [e]
        apply Stream'.mem_cons
      · exact Stream'.mem_cons_of_mem _ m
  · simp [IH this]

@[simp]
theorem mem_cons_iff (s : WSeq α) (b) {a} : a ∈ cons b s ↔ a = b ∨ a ∈ s :=
  eq_or_mem_iff_mem <| by simp [ret_mem]

theorem mem_cons_of_mem {s : WSeq α} (b) {a} (h : a ∈ s) : a ∈ cons b s :=
  (mem_cons_iff _ _).2 (Or.inr h)

theorem mem_cons (s : WSeq α) (a) : a ∈ cons a s :=
  (mem_cons_iff _ _).2 (Or.inl rfl)

theorem mem_of_mem_tail {s : WSeq α} {a} : a ∈ tail s → a ∈ s := by
  intro h; have := h; obtain ⟨n, e⟩ := h; revert s; simp only [Stream'.get]
  induction' n with n IH <;> intro s <;> induction' s using WSeq.recOn with x s s <;>
    simp <;> intro m e <;>
    injections
  · exact Or.inr m
  · exact Or.inr m
  · apply IH m
    rw [e]
    cases tail s
    rfl

theorem mem_of_mem_dropn {s : WSeq α} {a} : ∀ {n}, a ∈ drop s n → a ∈ s
  | 0, h => h
  | n + 1, h => @mem_of_mem_dropn s a n (mem_of_mem_tail h)

theorem get?_mem {s : WSeq α} {a n} : some a ∈ get? s n → a ∈ s := by
  revert s; induction' n with n IH <;> intro s h
  · rcases Computation.exists_of_mem_map h with ⟨o, h1, h2⟩
    rcases o with - | o
    · injection h2
    injection h2 with h'
    obtain ⟨a', s'⟩ := o
    exact (eq_or_mem_iff_mem h1).2 (Or.inl h'.symm)
  · have := @IH (tail s)
    rw [get?_tail] at this
    exact mem_of_mem_tail (this h)

theorem exists_get?_of_mem {s : WSeq α} {a} (h : a ∈ s) : ∃ n, some a ∈ get? s n := by
  apply mem_rec_on h
  · intro a' s' h
    rcases h with h | h
    · exists 0
      simp only [get?, drop, head_cons]
      rw [h]
      apply ret_mem
    · obtain ⟨n, h⟩ := h
      exists n + 1
      simpa [get?]
  · intro s' h
    obtain ⟨n, h⟩ := h
    exists n
    simp only [get?, dropn_think, head_think]
    apply think_mem h

theorem exists_dropn_of_mem {s : WSeq α} {a} (h : a ∈ s) :
    ∃ n s', some (a, s') ∈ destruct (drop s n) :=
  let ⟨n, h⟩ := exists_get?_of_mem h
  ⟨n, by
    rcases (head_terminates_iff _).1 ⟨⟨_, h⟩⟩ with ⟨⟨o, om⟩⟩
    have := Computation.mem_unique (Computation.mem_map _ om) h
    rcases o with - | o
    · injection this
    injection this with i
    obtain ⟨a', s'⟩ := o
    dsimp at i
    rw [i] at om
    exact ⟨_, om⟩⟩

theorem head_terminates_of_mem {s : WSeq α} {a} (h : a ∈ s) : Terminates (head s) :=
  let ⟨_, h⟩ := exists_get?_of_mem h
  head_terminates_of_get?_terminates ⟨⟨_, h⟩⟩

theorem of_mem_append {s₁ s₂ : WSeq α} {a : α} : a ∈ append s₁ s₂ → a ∈ s₁ ∨ a ∈ s₂ :=
  Seq.of_mem_append

theorem mem_append_left {s₁ s₂ : WSeq α} {a : α} : a ∈ s₁ → a ∈ append s₁ s₂ :=
  Seq.mem_append_left

theorem exists_of_mem_map {f} {b : β} : ∀ {s : WSeq α}, b ∈ map f s → ∃ a, a ∈ s ∧ f a = b
  | ⟨g, al⟩, h => by
    let ⟨o, om, oe⟩ := Seq.exists_of_mem_map h
    rcases o with - | a
    · injection oe
    injection oe with h'
    exact ⟨a, om, h'⟩

@[simp]
theorem ofList_nil : ofList [] = (nil : WSeq α) :=
  rfl

@[simp]
theorem ofList_cons (a : α) (l) : ofList (a::l) = cons a (ofList l) :=
  show Seq.map some (Seq.ofList (a::l)) = Seq.cons (some a) (Seq.map some (Seq.ofList l)) by simp

@[simp]
theorem toList'_nil (l : List α) :
    Computation.corec (fun ⟨l, s⟩ =>
      match Seq.destruct s with
      | none => Sum.inl l.reverse
      | some (none, s') => Sum.inr (l, s')
      | some (some a, s') => Sum.inr (a::l, s')) (l, nil) = Computation.pure l.reverse :=
  destruct_eq_pure rfl

@[simp]
theorem toList'_cons (l : List α) (s : WSeq α) (a : α) :
    Computation.corec (fun ⟨l, s⟩ =>
      match Seq.destruct s with
      | none => Sum.inl l.reverse
      | some (none, s') => Sum.inr (l, s')
      | some (some a, s') => Sum.inr (a::l, s')) (l, cons a s) =
      (Computation.corec (fun ⟨l, s⟩ =>
        match Seq.destruct s with
        | none => Sum.inl l.reverse
        | some (none, s') => Sum.inr (l, s')
        | some (some a, s') => Sum.inr (a::l, s')) (a::l, s)).think :=
  destruct_eq_think <| by simp [toList, cons]

@[simp]
theorem toList'_think (l : List α) (s : WSeq α) :
    Computation.corec (fun ⟨l, s⟩ =>
      match Seq.destruct s with
      | none => Sum.inl l.reverse
      | some (none, s') => Sum.inr (l, s')
      | some (some a, s') => Sum.inr (a::l, s')) (l, think s) =
      (Computation.corec (fun ⟨l, s⟩ =>
        match Seq.destruct s with
        | none => Sum.inl l.reverse
        | some (none, s') => Sum.inr (l, s')
        | some (some a, s') => Sum.inr (a::l, s')) (l, s)).think :=
  destruct_eq_think <| by simp [toList, think]

theorem toList'_map (l : List α) (s : WSeq α) :
    Computation.corec (fun ⟨l, s⟩ =>
      match Seq.destruct s with
      | none => Sum.inl l.reverse
      | some (none, s') => Sum.inr (l, s')
      | some (some a, s') => Sum.inr (a :: l, s')) (l, s) = (l.reverse ++ ·) <$> toList s := by
  refine
    Computation.eq_of_bisim
      (fun c1 c2 =>
        ∃ (l' : List α) (s : WSeq α),
          c1 = Computation.corec (fun ⟨l, s⟩ =>
            match Seq.destruct s with
            | none => Sum.inl l.reverse
            | some (none, s') => Sum.inr (l, s')
            | some (some a, s') => Sum.inr (a::l, s')) (l' ++ l, s) ∧
            c2 = Computation.map (l.reverse ++ ·) (Computation.corec (fun ⟨l, s⟩ =>
              match Seq.destruct s with
              | none => Sum.inl l.reverse
              | some (none, s') => Sum.inr (l, s')
              | some (some a, s') => Sum.inr (a::l, s')) (l', s)))
      ?_ ⟨[], s, rfl, rfl⟩
  intro s1 s2 h; rcases h with ⟨l', s, h⟩; rw [h.left, h.right]
  induction' s using WSeq.recOn with a s s <;> simp [toList, nil, cons, think, length]
  · refine ⟨a::l', s, ?_, ?_⟩ <;> simp
  · refine ⟨l', s, ?_, ?_⟩ <;> simp

@[simp]
theorem toList_cons (a : α) (s) : toList (cons a s) = (List.cons a <$> toList s).think :=
  destruct_eq_think <| by
    unfold toList
    simp only [toList'_cons, Computation.destruct_think, Sum.inr.injEq]
    rw [toList'_map]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
    rfl

@[simp]
theorem toList_nil : toList (nil : WSeq α) = Computation.pure [] :=
  destruct_eq_pure rfl

theorem toList_ofList (l : List α) : l ∈ toList (ofList l) := by
  induction' l with a l IH
  · simp [ret_mem]
  · simpa [ret_mem] using think_mem (Computation.mem_map _ IH)

@[simp]
theorem destruct_ofSeq (s : Seq α) :
    destruct (ofSeq s) = Computation.pure (s.head.map fun a => (a, ofSeq s.tail)) :=
  destruct_eq_pure <| by
    simp only [destruct, Seq.destruct, Option.map_eq_map, ofSeq, Computation.corec_eq, rmap,
      Seq.head]
    rw [show Seq.get? (some <$> s) 0 = some <$> Seq.get? s 0 by apply Seq.map_get?]
    rcases Seq.get? s 0 with - | a
    · rfl
    dsimp only [(· <$> ·)]
    simp [destruct]

@[simp]
theorem head_ofSeq (s : Seq α) : head (ofSeq s) = Computation.pure s.head := by
  simp only [head, Option.map_eq_map, destruct_ofSeq, Computation.map_pure, Option.map_map]
  cases Seq.head s <;> rfl

@[simp]
theorem tail_ofSeq (s : Seq α) : tail (ofSeq s) = ofSeq s.tail := by
  simp only [tail, destruct_ofSeq, map_pure', flatten_pure]
  induction' s using Seq.recOn with x s <;> simp only [ofSeq, Seq.tail_nil, Seq.head_nil,
    Option.map_none, Seq.tail_cons, Seq.head_cons, Option.map_some]
  · rfl

@[simp]
theorem dropn_ofSeq (s : Seq α) : ∀ n, drop (ofSeq s) n = ofSeq (s.drop n)
  | 0 => rfl
  | n + 1 => by
    simp only [drop, Nat.add_eq, Nat.add_zero, Seq.drop]
    rw [dropn_ofSeq s n, tail_ofSeq]

theorem get?_ofSeq (s : Seq α) (n) : get? (ofSeq s) n = Computation.pure (Seq.get? s n) := by
  dsimp [get?]; rw [dropn_ofSeq, head_ofSeq, Seq.head_dropn]

@[simp]
theorem map_nil (f : α → β) : map f nil = nil :=
  rfl

@[simp]
theorem map_cons (f : α → β) (a s) : map f (cons a s) = cons (f a) (map f s) :=
  Seq.map_cons _ _ _

@[simp]
theorem map_think (f : α → β) (s) : map f (think s) = think (map f s) :=
  Seq.map_cons _ _ _

@[simp]
theorem map_id (s : WSeq α) : map id s = s := by simp [map]

@[simp]
theorem map_ret (f : α → β) (a) : map f (ret a) = ret (f a) := by simp [ret]

@[simp]
theorem map_append (f : α → β) (s t) : map f (append s t) = append (map f s) (map f t) :=
  Seq.map_append _ _ _

theorem map_comp (f : α → β) (g : β → γ) (s : WSeq α) : map (g ∘ f) s = map g (map f s) := by
  dsimp [map]; rw [← Seq.map_comp]
  apply congr_fun; apply congr_arg
  ext ⟨⟩ <;> rfl

theorem mem_map (f : α → β) {a : α} {s : WSeq α} : a ∈ s → f a ∈ map f s :=
  Seq.mem_map (Option.map f)

-- The converse is not true without additional assumptions
theorem exists_of_mem_join {a : α} : ∀ {S : WSeq (WSeq α)}, a ∈ join S → ∃ s, s ∈ S ∧ a ∈ s := by
  suffices
    ∀ ss : WSeq α,
      a ∈ ss → ∀ s S, append s (join S) = ss → a ∈ append s (join S) → a ∈ s ∨ ∃ s, s ∈ S ∧ a ∈ s
    from fun S h => (this _ h nil S (by simp) (by simp [h])).resolve_left (notMem_nil _)
  intro ss h; apply mem_rec_on h <;> [intro b ss o; intro ss IH] <;> intro s S
  · induction' s using WSeq.recOn with b' s s <;>
      [induction' S using WSeq.recOn with s S S; skip; skip] <;>
      intro ej m <;> simp at ej <;> have := congr_arg Seq.destruct ej <;>
      simp at this; cases this
    substs b' ss
    simp? at m ⊢ says simp only [cons_append, mem_cons_iff] at m ⊢
    rcases o with e | IH
    · simp [e]
    rcases m with e | m
    · simp [e]
    exact Or.imp_left Or.inr (IH _ _ rfl m)
  · induction' s using WSeq.recOn with b' s s <;>
      [induction' S using WSeq.recOn with s S S; skip; skip] <;>
      intro ej m <;> simp at ej <;> have := congr_arg Seq.destruct ej <;> simp at this <;>
      subst ss
    · apply Or.inr
      simp only [join_cons, nil_append, mem_think, mem_cons_iff, exists_eq_or_imp] at m ⊢
      exact IH s S rfl m
    · apply Or.inr
      simp? at m says simp only [join_think, nil_append, mem_think] at m
      rcases (IH nil S (by simp) (by simp [m])).resolve_left (notMem_nil _) with ⟨s, sS, as⟩
      exact ⟨s, by simp [sS], as⟩
    · simp only [think_append, mem_think] at m IH ⊢
      apply IH _ _ rfl m

theorem exists_of_mem_bind {s : WSeq α} {f : α → WSeq β} {b} (h : b ∈ bind s f) :
    ∃ a ∈ s, b ∈ f a :=
  let ⟨t, tm, bt⟩ := exists_of_mem_join h
  let ⟨a, as, e⟩ := exists_of_mem_map tm
  ⟨a, as, by rwa [e]⟩

theorem destruct_map (f : α → β) (s : WSeq α) :
    destruct (map f s) = Computation.map (Option.map (Prod.map f (map f))) (destruct s) := by
  apply
    Computation.eq_of_bisim fun c1 c2 =>
      ∃ s,
        c1 = destruct (map f s) ∧
          c2 = Computation.map (Option.map (Prod.map f (map f))) (destruct s)
  · intro c1 c2 h
    obtain ⟨s, h⟩ := h
    rw [h.left, h.right]
    induction' s using WSeq.recOn with a s s <;> simp
    exact ⟨s, rfl, rfl⟩
  · exact ⟨s, rfl, rfl⟩

/-- auxiliary definition of `destruct_append` over weak sequences -/
@[simp]
def destruct_append.aux (t : WSeq α) : Option (α × WSeq α) → Computation (Option (α × WSeq α))
  | none => destruct t
  | some (a, s) => Computation.pure (some (a, append s t))

theorem destruct_append (s t : WSeq α) :
    destruct (append s t) = (destruct s).bind (destruct_append.aux t) := by
  apply
    Computation.eq_of_bisim
      (fun c1 c2 =>
        ∃ s t, c1 = destruct (append s t) ∧ c2 = (destruct s).bind (destruct_append.aux t))
      _ ⟨s, t, rfl, rfl⟩
  intro c1 c2 h; rcases h with ⟨s, t, h⟩; rw [h.left, h.right]
  induction' s using WSeq.recOn with a s s <;> simp
  · induction' t using WSeq.recOn with b t t <;> simp
    · refine ⟨nil, t, ?_, ?_⟩ <;> simp
  · exact ⟨s, t, rfl, rfl⟩

/-- auxiliary definition of `destruct_join` over weak sequences -/
@[simp]
def destruct_join.aux : Option (WSeq α × WSeq (WSeq α)) → Computation (Option (α × WSeq α))
  | none => Computation.pure none
  | some (s, S) => (destruct (append s (join S))).think

theorem destruct_join (S : WSeq (WSeq α)) :
    destruct (join S) = (destruct S).bind destruct_join.aux := by
  apply
    Computation.eq_of_bisim
      (fun c1 c2 =>
        c1 = c2 ∨ ∃ S, c1 = destruct (join S) ∧ c2 = (destruct S).bind destruct_join.aux)
      _ (Or.inr ⟨S, rfl, rfl⟩)
  intro c1 c2 h
  exact
    match c1, c2, h with
    | c, _, Or.inl <| rfl => by cases c.destruct <;> simp
    | _, _, Or.inr ⟨S, rfl, rfl⟩ => by
      induction' S using WSeq.recOn with s S S <;> simp
      · refine Or.inr ⟨S, rfl, rfl⟩

@[simp]
theorem map_join (f : α → β) (S) : map f (join S) = join (map (map f) S) := by
  apply
    Seq.eq_of_bisim fun s1 s2 =>
      ∃ s S, s1 = append s (map f (join S)) ∧ s2 = append s (join (map (map f) S))
  · intro s1 s2 h
    exact
      match s1, s2, h with
      | _, _, ⟨s, S, rfl, rfl⟩ => by
        induction' s using WSeq.recOn with a s s <;> simp
        · induction' S using WSeq.recOn with s S S <;> simp
          · exact ⟨map f s, S, rfl, rfl⟩
          · refine ⟨nil, S, ?_, ?_⟩ <;> simp
        · exact ⟨_, _, rfl, rfl⟩
        · exact ⟨_, _, rfl, rfl⟩
  · refine ⟨nil, S, ?_, ?_⟩ <;> simp

end WSeq

end Stream'
