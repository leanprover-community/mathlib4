/-
Copyright (c) 2024 Anthony DeRossi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony DeRossi
-/
import Mathlib.Computability.RegularExpressions
import Mathlib.Computability.EpsilonNFA
import Mathlib.Computability.Language

/-!
# Constructing Automata from Regular Expressions

This file contains a formal definition of [Thompson's method][thompson1968] for constructing a
nondeterministic finite automaton from a regular expression and a proof of its correctness.

## Main definitions

* `RegularExpression.toεNFA`

## References

* [Ken Thompson, *Regular expression search algorithm*][thompson1968]

-/

open Computability List Set εNFA

universe u v
variable {α : Type u} {σ σ₁ σ₂ : Type v} {P Q : RegularExpression α}

namespace RegularExpression

/-- A binary state type representing one initial and one final state -/
inductive BinSt where
  | ini
  | fin

/-- The `εNFA` for `zero` has no transitions. -/
private def zero_step : Empty → Option α → Set Empty
  | _, _ => ∅
private def zero_start : Set Empty := ∅
private def zero_accept : Set Empty := ∅

/-- The `εNFA` for `epsilon` has only an ε-transition from the starting state to the accepting
state. -/
private def epsilon_step : BinSt → Option α → Set (BinSt)
  | .ini, none => {.fin}
  | _, _ => ∅
private def epsilon_start : Set (BinSt) := {.ini}
private def epsilon_accept : Set (BinSt) := {.fin}

/-- The `εNFA` for `char a` has only an `a`-labeled transition from the starting state to the
accepting state. -/
private def char_step (a : α) : BinSt → Option α → Set (BinSt)
  | .ini, some b => {s | s = .fin ∧ a = b}
  | _, _ => ∅
private def char_start : Set (BinSt) := {.ini}
private def char_accept : Set (BinSt) := {.fin}

/-- The `εNFA` for `plus P Q` is constructed using a sum type to embed left and right (from the
`εNFA`s for `P` and `Q` respectively) states. It has separate starting and accepting states, with
ε-transitions from the starting state to the embedded starting states, and from the embedded
accepting states to the accepting state. -/
private def plus_step (M₁ : εNFA α σ₁) (M₂ : εNFA α σ₂) :
    BinSt ⊕ σ₁ ⊕ σ₂ → Option α → Set (BinSt ⊕ σ₁ ⊕ σ₂)
  | .inl .ini, none => .inr '' Sum.elim M₁.start M₂.start
  | .inr (.inl s'), a => .inr ∘ .inl '' M₁.step s' a
      ∪ {s | s = .inl .fin ∧ a = none ∧ s' ∈ M₁.accept}
  | .inr (.inr s'), a => .inr ∘ .inr '' M₂.step s' a
      ∪ {s | s = .inl .fin ∧ a = none ∧ s' ∈ M₂.accept}
  | _, _ => ∅
private def plus_start : Set (BinSt ⊕ σ₁ ⊕ σ₂) := {.inl .ini}
private def plus_accept : Set (BinSt ⊕ σ₁ ⊕ σ₂) := {.inl .fin}

/-- The `εNFA` for `comp P Q` is constructed using a sum type to embed left and right (from the
`εNFA`s for `P` and `Q` respectively) states. The starting and accepting states are the embedded
left-starting and right-accepting states respectively. An ε-transition exists between the embedded
left accepting and right starting states. -/
private def comp_step (M₁ : εNFA α σ₁) (M₂ : εNFA α σ₂) : σ₁ ⊕ σ₂ → Option α → Set (σ₁ ⊕ σ₂)
  | .inl s', a => .inl '' M₁.step s' a ∪ {s | s ∈ .inr '' M₂.start ∧ a = none ∧ s' ∈ M₁.accept}
  | .inr s', a => .inr '' M₂.step s' a
private def comp_start (M₁ : εNFA α σ₁) : Set (σ₁ ⊕ σ₂) := .inl '' M₁.start
private def comp_accept (M₂ : εNFA α σ₂) : Set (σ₁ ⊕ σ₂) := .inr '' M₂.accept

/-- The `εNFA` for `star P` is constructed using a sum type to embed the `εNFA` for `P`, with
ε-transitions from the starting and accepting states to the respective embedded states. Additional
ε-transitions exist between the starting and accepting state (empty matching), and between the
embedded accepting and starting states (repetition). -/
private def star_step (M : εNFA α σ) : BinSt ⊕ σ → Option α → Set (BinSt ⊕ σ)
  | .inl .ini, none => .inr '' M.start ∪ {.inl .fin}
  | .inr s', a => .inr '' M.step s' a
      ∪ {s | (s = .inl .fin ∨ s ∈ .inr '' M.start) ∧ a = none ∧ s' ∈ M.accept}
  | _, _ => ∅
private def star_start : Set (BinSt ⊕ σ) := {.inl .ini}
private def star_accept : Set (BinSt ⊕ σ) := {.inl .fin}

/-- The state type for the `εNFA` constructed by `toεNFA` -/
def St : RegularExpression α → Type
  | 0 => Empty
  | 1 => BinSt
  | char _ => BinSt
  | P + Q => BinSt ⊕ St P ⊕ St Q
  | comp P Q => St P ⊕ St Q
  | star P => BinSt ⊕ St P

/-- Construct an `εNFA` from a `RegularExpression` -/
def toεNFA : (P : RegularExpression α) → εNFA α P.St
  | 0 => ⟨zero_step, zero_start, zero_accept⟩
  | 1 => ⟨epsilon_step, epsilon_start, epsilon_accept⟩
  | char a => ⟨char_step a, char_start, char_accept⟩
  | P + Q => ⟨plus_step P.toεNFA Q.toεNFA, plus_start, plus_accept⟩
  | comp P Q => ⟨comp_step P.toεNFA Q.toεNFA, comp_start P.toεNFA, comp_accept Q.toεNFA⟩
  | star P => ⟨star_step P.toεNFA, star_start, star_accept⟩

lemma zero_accepts : zero.toεNFA.accepts = (0 : Language α) := by
  simp only [accepts, toεNFA, zero_accept, exists_false, false_and, mem_empty_iff_false]
  rfl

lemma epsilon_accepts : epsilon.toεNFA.accepts = (1 : Language α) := by
  ext x
  constructor <;> intro h <;> rw [mem_accepts_iff_exists_path] at *
  · obtain ⟨s₁, s₂, _, _, _, _, h⟩ := h
    substs x s₁ s₂
    rw [Language.one_def, mem_singleton_iff, reduceOption_eq_nil_iff]
    use 1
    cases' h with _ _ _ _ a _ hs h
    cases a <;> cases hs
    cases h <;> trivial
  · subst x
    use .ini, .fin, [none]
    repeat constructor

lemma char_accepts (a : α) : (char a).toεNFA.accepts = {[a]} := by
  ext x
  constructor <;> intro h <;> rw [mem_accepts_iff_exists_path] at *
  · obtain ⟨s₁, s₂, _, _, _, _, h⟩ := h
    substs x s₁ s₂
    rw [mem_singleton_iff, reduceOption_eq_singleton_iff]
    use 0, 0
    cases' h with _ _ _ _ a _ hs h
    cases a <;> cases hs
    cases h <;> subst_eqs <;> trivial
  · subst x
    use .ini, .fin, [a]
    repeat constructor

lemma plus_embed_left (s₁ s₂ : P.St) (x : List (Option α)) :
    P.toεNFA.IsPath s₁ s₂ x ↔ (P + Q).toεNFA.IsPath (.inr (.inl s₁)) (.inr (.inl s₂)) x := by
  induction' x with _ _ ih generalizing s₁
    <;> constructor
    <;> intro h
    <;> cases' h with _ s _ _ _ _ hs h
    <;> (try apply IsPath.nil)
  · apply IsPath.cons
    · left
      use s
    · rwa [Function.comp_apply, ← ih]
  · cases s <;> obtain ⟨_, _, ⟨⟩⟩ | ⟨⟨⟩, _⟩ := hs
    · cases' h with _ s _ _ a _ hs
      cases a <;> cases hs
    · apply IsPath.cons <;> (try rw [ih]) <;> assumption

lemma plus_embed_right (s₁ s₂ : Q.St) (x : List (Option α)) :
    Q.toεNFA.IsPath s₁ s₂ x ↔ (P + Q).toεNFA.IsPath (.inr (.inr s₁)) (.inr (.inr s₂)) x := by
  induction' x with _ _ ih generalizing s₁
    <;> constructor
    <;> intro h
    <;> cases' h with _ s _ _ _ _ hs h
    <;> (try apply IsPath.nil)
  · apply IsPath.cons
    · left
      use s
    · rwa [Function.comp_apply, ← ih]
  · cases s <;> obtain ⟨_, _, ⟨⟩⟩ | ⟨⟨⟩, _⟩ := hs
    · cases' h with _ s _ _ a _ hs
      cases a <;> cases hs
    · apply IsPath.cons <;> (try rw [ih]) <;> assumption

lemma plus_no_cross_left (s : P.St) (t : Q.St) (x : List (Option α)) :
    ¬(P + Q).toεNFA.IsPath (.inr (.inl s)) (.inr (.inr t)) x := by
  intro h
  induction x generalizing s <;> cases' h with _ s _ _ _ _ hs
  obtain ⟨_, _, ⟨⟩⟩ | ⟨⟨⟩, _⟩ := hs <;> tauto

lemma plus_no_cross_right (s : Q.St) (t : P.St) (x : List (Option α)) :
    ¬(P + Q).toεNFA.IsPath (.inr (.inr s)) (.inr (.inl t)) x := by
  intro h
  induction x generalizing s <;> cases' h with _ s _ _ _ _ hs
  obtain ⟨_, _, ⟨⟩⟩ | ⟨⟨⟩, _⟩ := hs <;> tauto

lemma plus_accepts : (P + Q).toεNFA.accepts = P.toεNFA.accepts + Q.toεNFA.accepts := by
  ext x
  constructor <;> intro h <;> rw [mem_accepts_iff_exists_path] at *
  · obtain ⟨s₁, s₂, _, _, _, _, h⟩ := h
    substs x s₁ s₂
    cases' h with _ s _ _ a x hs h
    cases a <;> obtain ⟨_ | _, hs, ⟨⟩⟩ := hs
      <;> [left; right]
      <;> rcases eq_nil_or_concat x with ⟨⟨⟩⟩ | ⟨_, a, ⟨⟩⟩
      <;> (try apply IsPath.eq_of_nil at h; contradiction)
      <;> simp_rw [concat_eq_append, isPath_append, isPath_singleton] at h
      <;> rcases h with ⟨⟨_ | _⟩ | ⟨_ | _⟩, h, hs⟩
      <;> (try apply plus_no_cross_left at h)
      <;> (try apply plus_no_cross_right at h)
      <;> (try contradiction)
      <;> (try cases a <;> obtain ⟨_, _, ⟨⟩⟩ := hs; done)
      <;> obtain ⟨_, _, ⟨⟩⟩ | ⟨_, ⟨⟩, _⟩ := hs
      <;> rw [reduceOption_cons_of_none, reduceOption_concat, Option.toList_none, append_nil,
            mem_accepts_iff_exists_path]
    · rw [← plus_embed_left] at h
      tauto
    · rw [← plus_embed_right] at h
      tauto
  · use .inl .ini, .inl .fin
    rcases h with h | h
      <;> rw [mem_accepts_iff_exists_path] at h
      <;> obtain ⟨s₁, s₂, x', _, _, _, _⟩ := h
      <;> subst x
      <;> use none :: x' ++ [none]
      <;> simp only [reduceOption_append, reduceOption_cons_of_none, reduceOption_nil, append_nil]
      <;> split_ands
      <;> (try trivial)
      <;> rw [isPath_append]
      <;> [use .inr (.inl s₂); use .inr (.inr s₂)]
      <;> constructor
      <;> (try apply IsPath.cons <;> tauto)
      <;> apply IsPath.cons
    · use .inl s₁
      trivial
    · rwa [← plus_embed_left]
    · use .inr s₁
      trivial
    · rwa [← plus_embed_right]

lemma comp_one_way (s : Q.St) (t : P.St) (x : List (Option α)) :
    ¬(comp P Q).toεNFA.IsPath (.inr s) (.inl t) x := by
  intro h
  induction x generalizing s <;> cases' h with _ s _ _ _ _ hs
  obtain ⟨_, _, ⟨⟩⟩ := hs
  tauto

lemma comp_embed_left (s₁ s₂ : P.St) (x : List (Option α)) :
    P.toεNFA.IsPath s₁ s₂ x ↔ (comp P Q).toεNFA.IsPath (.inl s₁) (.inl s₂) x := by
  induction' x with _ _ ih generalizing s₁
    <;> constructor
    <;> intro h
    <;> cases' h with _ s _ _ _ _ hs h
    <;> (try apply IsPath.nil)
  · apply IsPath.cons
    · left
      use s
    · rwa [← ih]
  · obtain ⟨_, _, ⟨⟩⟩ | ⟨⟨_, _, ⟨⟩⟩, _⟩ := hs
    · apply IsPath.cons <;> (try rw [ih]) <;> assumption
    · apply comp_one_way at h
      contradiction

lemma comp_embed_right (s₁ s₂ : Q.St) (x : List (Option α)) :
    Q.toεNFA.IsPath s₁ s₂ x ↔ (comp P Q).toεNFA.IsPath (.inr s₁) (.inr s₂) x := by
  induction' x with _ _ ih generalizing s₁
    <;> constructor
    <;> intro h
    <;> cases' h with _ s _ _ _ _ hs h
    <;> (try apply IsPath.nil)
  · apply IsPath.cons
    · use s
    · rwa [← ih]
  · obtain ⟨_, _, ⟨⟩⟩ := hs
    apply IsPath.cons <;> (try rw [ih]) <;> assumption

lemma comp_split (s₁₁ : P.St) (s₂₂ : Q.St) (x : List (Option α)) :
    (comp P Q).toεNFA.IsPath (.inl s₁₁) (.inr s₂₂) x →
      ∃ s₁₂ s₂₁ x₁ x₂,
        x = x₁ ++ none :: x₂ ∧
        s₁₂ ∈ P.toεNFA.accept ∧
        s₂₁ ∈ Q.toεNFA.start ∧
        (comp P Q).toεNFA.IsPath (.inl s₁₁) (.inl s₁₂) x₁ ∧
        (comp P Q).toεNFA.IsPath (.inr s₂₁) (.inr s₂₂) x₂ := by
  intro h
  cases' x with a x
  · apply IsPath.eq_of_nil at h
    contradiction
  · induction' x with b x ih generalizing s₁₁ a <;> cases' h with _ s _ _ _ _ hs h
    · apply IsPath.eq_of_nil at h
      subst s
      obtain ⟨_, _, ⟨⟩⟩ | ⟨⟨_, _, ⟨⟩⟩, ⟨⟩, _⟩ := hs
      use s₁₁, s₂₂, [], []
      tauto
    · cases' s with _ s
      · obtain ⟨s₁₂, s₂₁, x₁, x₂, _⟩ := ih _ _ h
        use s₁₂, s₂₁, a :: x₁, x₂
        tauto
      · use s₁₁, s, [], b :: x
        split_ands <;> rcases hs with ⟨_, _, ⟨⟩⟩ | ⟨⟨_, _, ⟨⟩⟩, ⟨⟩, _⟩ <;> tauto

lemma comp_accepts : (comp P Q).toεNFA.accepts = P.toεNFA.accepts * Q.toεNFA.accepts := by
  ext x
  constructor <;> intro h
  · rw [mem_accepts_iff_exists_path] at h
    obtain ⟨_, _, _, ⟨s₁₁, _, ⟨⟩⟩, ⟨s₂₂, _, ⟨⟩⟩, ⟨⟩, h⟩ := h
    apply comp_split at h
    obtain ⟨s₁₂, s₂₁, x₁, x₂, ⟨⟩, _, _, h₁, h₂⟩ := h
    rw [← comp_embed_left] at h₁
    rw [← comp_embed_right] at h₂
    rw [Language.mem_mul]
    simp_rw [mem_accepts_iff_exists_path]
    use x₁.reduceOption
    constructor
    · use s₁₁, s₁₂, x₁
    · use x₂.reduceOption
      constructor
      · use s₂₁, s₂₂, x₂
      · rw [reduceOption_append, reduceOption_cons_of_none]
  · rw [Language.mem_mul] at h
    obtain ⟨x₁, h₁, x₂, h₂, ⟨⟩⟩ := h
    rw [mem_accepts_iff_exists_path] at *
    obtain ⟨s₁₁, s₁₂, x₁', _, _, _, _⟩ := h₁
    obtain ⟨_, s₂₂, x₂', _, _, _, _⟩ := h₂
    substs x₁ x₂
    use .inl s₁₁, .inr s₂₂, x₁' ++ none :: x₂'
    split_ands <;> try tauto
    · rw [reduceOption_append, reduceOption_cons_of_none]
    · rw [isPath_append]
      use .inl s₁₂
      constructor
      · rwa [← comp_embed_left]
      · apply IsPath.cons
        · right
          constructor <;> tauto
        · rwa [← comp_embed_right]

lemma step_accept_empty (s : P.St) : s ∈ P.toεNFA.accept → ∀ a, P.toεNFA.step s a = ∅ := by
  intro hs
  induction P
    <;> rcases hs with ⟨_, _, ⟨⟩⟩
    <;> simp only [toεNFA, comp_step, comp_def, image_eq_empty]
    <;> tauto

lemma accept_final (s : P.St) : s ∈ P.toεNFA.accept → ∀ t x, x ≠ [] → ¬P.toεNFA.IsPath s t x := by
  intro hs _ _ hx
  rw [ne_nil_iff_exists_cons] at hx
  obtain ⟨_, _, ⟨⟩⟩ := hx
  intro h
  cases' h with _ _ _ _ _ _ hs'
  rw [step_accept_empty] at hs' <;> assumption

-- N.B. This holds for any `P`, but only the `star P` case is needed.
lemma star_no_restart (s : P.St) (x : List (Option α)) :
    ¬(star P).toεNFA.IsPath (.inr s) (.inl .ini) x := by
  intro h
  cases' x using reverseRecOn with x a
  · apply IsPath.eq_of_nil at h
    contradiction
  · simp_rw [isPath_append, isPath_singleton] at h
    obtain ⟨s, _, hs⟩ := h
    rcases s with ⟨_ | _⟩ | _ <;> cases a <;> obtain ⟨_, _, ⟨⟩⟩ | ⟨⟨⟨⟩⟩ | ⟨_, _, ⟨⟩⟩, _⟩ := hs

lemma star_cons (s : (star P).St) :
    s = .inl .ini ∨ s ∈ .inr '' P.toεNFA.accept →
      ∀ x, (star P).toεNFA.IsPath s (.inl .fin) x →
      ∃ t x',
        x = none :: x' ∧
        (t = .inl .fin ∨ t ∈ .inr '' P.toεNFA.start) ∧
        (star P).toεNFA.IsPath t (.inl .fin) x' := by
  intro hs x h
  obtain ⟨⟨⟩⟩ | ⟨_, _, ⟨⟩⟩ := hs
    <;> cases' x with a x
    <;> (try apply IsPath.eq_of_nil at h)
    <;> cases' h with _ s _ _ _ _ hs
    <;> use s, x
    <;> cases a
    <;> obtain ⟨_, hs, ⟨⟩⟩ | ⟨⟨⟩⟩ := hs
    <;> (try rw [step_accept_empty] at hs)
    <;> tauto

lemma star_concat (s : (star P).St) :
    s ≠ .inl .fin →
      ∀ x, (star P).toεNFA.IsPath s (.inl .fin) x →
      ∃ x', x = x' ++ [none] := by
  intro hs x h
  rcases eq_nil_or_concat' x with ⟨⟨⟩⟩ | ⟨x, a, ⟨⟩⟩
  · apply IsPath.eq_of_nil at h
    contradiction
  · simp_rw [isPath_append, isPath_singleton] at h
    obtain ⟨s, _, hs⟩ := h
    cases a
    · use x
    · rcases s with ⟨_ | _⟩ | _ <;> obtain ⟨_, _, ⟨⟩⟩ | ⟨_, ⟨⟩, _⟩ := hs

lemma star_end (s : (star P).St) :
    s = .inl .ini ∨ s ∈ .inr '' P.toεNFA.accept → (star P).toεNFA.IsPath s (.inl .fin) [none] := by
  rw [isPath_singleton]
  intro h
  rcases h with ⟨⟨⟩, _⟩ | ⟨_, _, ⟨⟩⟩ <;> (try right; constructor) <;> tauto

lemma star_split (s₁ : P.St) (x : List (Option α)) :
    (star P).toεNFA.IsPath (.inr s₁) (.inl .fin) x →
      ∃ s₂ x₁ x',
        x = x₁ ++ x' ∧
        s₂ ∈ P.toεNFA.accept ∧
        P.toεNFA.IsPath s₁ s₂ x₁ ∧
        (star P).toεNFA.IsPath (.inr s₂) (.inl .fin) x' := by
  intro h
  obtain ⟨x, ⟨⟩⟩ := star_concat _ (by tauto) _ h
  simp_rw [isPath_append, isPath_singleton] at h
  obtain ⟨t, h, ht⟩ := h
  rcases t with ⟨_ | _⟩ | t <;> obtain ⟨_, _, ⟨⟩⟩ | ⟨_, _, _⟩ := ht
  · apply star_no_restart at h
    contradiction
  · induction' x with a x ih generalizing s₁
    · apply IsPath.eq_of_nil at h
      cases h
      use t, [], [none]
      split_ands <;> (try apply star_end) <;> tauto
    · cases' h with _ s _ _ _ _ hs h
      rcases hs with ⟨_, _, ⟨⟩⟩ | ⟨⟨⟨⟩⟩ | ⟨_, _, ⟨⟩⟩, _, _⟩
      · apply ih at h
        obtain ⟨s₂, x₁, x', _, _, _, _⟩ := h
        use s₂, a :: x₁, x'
        split_ands <;> (try rw [cons_append]) <;> tauto
      · apply accept_final at h <;> trivial
      · use s₁, [], none :: x ++ [none]
        split_ands <;> (try rw [cons_append, nil_append]) <;> try tauto
        · apply IsPath.cons
          · right
            constructor
            · right
              solve_by_elim
            · trivial
          · simp_rw [append_eq, isPath_append]
            use .inr t
            split_ands <;> (try apply star_end) <;> tauto

lemma star_parts (s : (star P).St) (x : List (Option α)) :
    s = .inl .ini ∨ s ∈ .inr '' P.toεNFA.accept → (star P).toεNFA.IsPath s (.inl .fin) x →
      ∃ xs : List (List α), x.reduceOption = xs.flatten ∧ ∀ y ∈ xs, y ∈ P.toεNFA.accepts := by
  intro hs h
  rcases star_cons _ hs _ h with ⟨_, _, ⟨⟩, ⟨⟨⟩⟩ | ⟨s₁, _, ⟨⟩⟩, h⟩
  · use []
    rw [reduceOption_cons_of_none, flatten_nil]
    cases h <;> tauto
  · obtain ⟨s₂, x₁, _, ⟨⟩, _, _, h'⟩ := star_split _ _ h
    obtain ⟨xs, hx, _⟩ := star_parts (.inr s₂) _ (by tauto) h'
    use x₁.reduceOption :: xs
    rw [reduceOption_cons_of_none, reduceOption_append, flatten_cons, hx]
    have h₁ := (mem_accepts_iff_exists_path _).mpr ⟨s₁, s₂, x₁, (by trivial)⟩
    constructor <;> (try intro _ hy; cases hy) <;> tauto
  termination_by x.length

lemma star_embed (s₁ s₂ : P.St) (x : List (Option α)) :
    P.toεNFA.IsPath s₁ s₂ x → (star P).toεNFA.IsPath (.inr s₁) (.inr s₂) x := by
  induction' x generalizing s₁ <;> intro h <;> cases h <;> (try apply IsPath.cons; left) <;> tauto

lemma star_accepts : (star P).toεNFA.accepts = P.toεNFA.accepts∗ := by
  ext x
  constructor <;> intro h
  · rw [mem_accepts_iff_exists_path] at h
    obtain ⟨_, _, x, ⟨⟩, ⟨⟩, ⟨⟩, h⟩ := h
    exact star_parts _ x (by tauto) h
  · rw [Language.mem_kstar] at h
    obtain ⟨xs, ⟨⟩, hs⟩ := h
    rw [mem_accepts_iff_exists_path]
    use .inl .ini, .inl .fin
    induction' xs with _ _ ih
    · use [none]
      split_ands <;> (try rw [isPath_singleton]; right) <;> rfl
    · simp only [forall_eq_or_imp, mem_cons] at hs
      obtain ⟨h₁, hs⟩ := hs
      rw [mem_accepts_iff_exists_path] at h₁
      obtain ⟨_, s₁₂, x₁, _, _, ⟨⟩, _⟩ := h₁
      obtain ⟨_, _, _, hx₂, h₂⟩ := ih hs
      obtain ⟨_, x₂, ⟨⟩, hs₂₁, _⟩ := star_cons _ (by tauto) _ h₂
      use none :: x₁ ++ none :: x₂
      split_ands <;> try rfl
      · rw [reduceOption_append, reduceOption_cons_of_none, flatten_cons, hx₂]
      · rw [isPath_append]
        use .inr s₁₂
        constructor
          <;> rcases hs₂₁ with ⟨⟨⟩⟩ | ⟨_, _, ⟨⟩⟩
          <;> apply IsPath.cons
          <;> (try assumption)
          <;> (try left; tauto)
          <;> (try right; constructor)
          <;> (try apply star_embed)
          <;> tauto

theorem toεNFA_correct (P : RegularExpression α) :
    P.toεNFA.accepts = P.matches' := by
  induction P with
  | zero => exact zero_accepts
  | epsilon => exact epsilon_accepts
  | char a => exact char_accepts a
  | plus P Q hP hQ =>
    rw [plus_def, matches'_add, ← hP, ← hQ]
    exact plus_accepts
  | comp P Q hP hQ =>
    rw [comp_def, matches'_mul, ← hP, ← hQ]
    exact comp_accepts
  | star P hP =>
    rw [matches'_star, ← hP]
    exact star_accepts

end RegularExpression
