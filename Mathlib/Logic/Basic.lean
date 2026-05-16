/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Mathlib.Lean.Meta.Simp
public import Batteries.Logic
public import Batteries.Util.LibraryNote

public import Mathlib.Tactic.Attr.Register

/-!
# Basic logic properties

This file is one of the earliest imports in mathlib.

## Implementation notes

Theorems that require decidability hypotheses are in the namespace `Decidable`.
Classical versions are in the namespace `Classical`.
-/

@[expose] public section

open Function

section Miscellany

section CommSimproc

open Lean Meta Simp

theorem eq_comm_eq {α : Sort*} (a b : α) : (a = b) = (b = a) := by rw [@eq_comm _ a b]
theorem iff_comm_eq (a b : Prop) : (a ↔ b) = (b ↔ a) := by rw [@iff_comm a b]

/-- On a goal of the form of `x = y`, also try to simplify `y = x`.

If simplifying `y = x` gives `y' = x'` then this simproc returns `x' = y'` (so that the use of
commutativity is transparent), otherwise it returns the result of simplifying `y = x` unmodified.
-/
simproc_decl eqComm (_ = _) := fun e => do
  let_expr Eq _ x y := e | return .continue
  let symmExpr ← mkEq y x
  let r ← withoutTheorems #[`eqComm,
    -- These theorems would cause an infinite loop:
    ``eq_comm, ``Bool.not_eq_eq_eq_not, `inv_eq_iff_eq_inv, `eq_inv_mul_iff_mul_eq,
    `eq_mul_inv_iff_mul_eq, `neg_eq_iff_eq_neg, `Function.Involutive.eq_iff,
    `vadd_eq_iff_eq_neg_vadd, `Equiv.apply_eq_iff_eq_symm_apply,
    -- These theorems aren't commute-resistant (they turn an equality into a non-equality in a
    -- non-commutative way.)
    ``beq_iff_eq, ``funext_iff, ``eq_iff_iff, `Prod.swap_eq_iff_eq_swap, ``left_eq_dite_iff,
    ``right_eq_dite_iff] do
    withTraceNode `Meta.Tactic.simp (fun _ => return m!"commuting equality: {e}") <| simp symmExpr
  -- If no actual progress happened (modulo commutativity), return early.
  match_expr r.expr with
  | Eq _ y' x' =>
    if (y' == y && x' == x) || (y' == x && x' == y) then do
      return .continue none
  | _ => pure ()
  let symmR ← Result.mkEqTrans { expr := symmExpr, proof? := ← mkAppM ``eq_comm_eq #[x, y] } r
  -- If we started with `x = y`, and the result of simplifying `y = x` was `y' = x'`, then we want
  -- to end up with `x' = y'`.
  match_expr r.expr with
  | Eq _ y' x' =>
    return .visit (← symmR.mkEqTrans
      { expr := ← mkEq x' y', proof? := ← mkAppM ``eq_comm_eq #[y', x'] })
  | _ => return .done symmR

/-- On a goal of the form of `x ↔ y`, also try to simplify `y ↔ x`.

If simplifying `y ↔ x` gives `y' ↔ x'` then this simproc returns `x' ↔ y'` (so that the use of
commutativity is transparent), otherwise it returns the result of simplifying `y ↔ x` unmodified.
-/
simproc_decl iffComm (_ ↔ _) := fun e => do
  let_expr Iff x y := e | return .continue
  let symmExpr := .app (.app (.const ``Iff []) y) x
  let r ← withoutTheorems #[`iffComm,
      -- These theorems would cause an infinite loop:
      ``Iff.comm,
      -- These theorems aren't commute-resistant (they turn an iff into a non-iff in a
      -- non-commutative way).
      ``and_congr_left_iff, ``and_congr_right_iff,  ``iff_def, ``iff_def',
      ``iff_iff_implies_and_implies, ``Bool.coe_iff_coe] do
    withTraceNode `Meta.Tactic.simp (fun _ => return m!"commuting iff: {e}") <| simp symmExpr
  -- If no actual progress happened (modulo commutativity), return early.
  if r.expr == symmExpr || r.expr == e then return .continue
  let symmR ← Result.mkEqTrans { expr := symmExpr, proof? := ← mkAppM ``iff_comm_eq #[x, y] } r
  -- If we started with `x ↔ y`, and the result of simplifying `y ↔ x` was `y' ↔ x'`, then we want
  -- to end up with `x' ↔ y'`.
  match_expr r.expr with
  | Iff y' x' =>
    return .visit (← symmR.mkEqTrans
      { expr := .app (.app (.const ``Iff []) x') y', proof? := ← mkAppM ``iff_comm_eq #[y', x'] })
  | _ => return .done symmR

end CommSimproc

-- attribute [refl] HEq.refl -- FIXME This is still rejected after https://github.com/leanprover-community/mathlib4/pull/857

/-- An identity function with its main argument implicit. This will be printed as `hidden` even
if it is applied to a large term, so it can be used for elision,
as done in the `elide` and `unelide` tactics. -/
abbrev hidden {α : Sort*} {a : α} := a

variable {α : Sort*}

instance (priority := 10) decidableEq_of_subsingleton [Subsingleton α] : DecidableEq α :=
  fun a b ↦ isTrue (Subsingleton.elim a b)

instance [Subsingleton α] (p : α → Prop) : Subsingleton (Subtype p) :=
  ⟨fun ⟨x, _⟩ ⟨y, _⟩ ↦ by cases Subsingleton.elim x y; rfl⟩

theorem congr_heq {α β γ : Sort _} {f : α → γ} {g : β → γ} {x : α} {y : β}
    (h₁ : f ≍ g) (h₂ : x ≍ y) : f x = g y := by
  cases h₂; cases h₁; rfl

theorem congr_heq₂ {α α' β β' γ : Sort _} {f : α → α' → γ} {g : β → β' → γ}
    {x : α} {u : α'} {y : β} {v : β'}
    (h₁ : f ≍ g) (h₂ : x ≍ y) (h₃ : u ≍ v) :
    f x u = g y v := by
  cases h₃; cases h₂; cases h₁; rfl

theorem congr_arg_heq {β : α → Sort*} (f : ∀ a, β a) :
    ∀ {a₁ a₂ : α}, a₁ = a₂ → f a₁ ≍ f a₂
  | _, _, rfl => HEq.rfl

theorem dcongr_heq.{u, v}
    {α₁ α₂ : Sort u}
    {β₁ : α₁ → Sort v} {β₂ : α₂ → Sort v}
    {f₁ : ∀ a, β₁ a} {f₂ : ∀ a, β₂ a}
    {a₁ : α₁} {a₂ : α₂}
    (hargs : a₁ ≍ a₂)
    (ht : ∀ t₁ t₂, t₁ ≍ t₂ → β₁ t₁ = β₂ t₂)
    (hf : α₁ = α₂ → β₁ ≍ β₂ → f₁ ≍ f₂) :
    f₁ a₁ ≍ f₂ a₂ := by
  cases hargs
  cases funext fun v => ht v v .rfl
  cases hf rfl .rfl
  rfl

@[simp] theorem eq_iff_eq_cancel_left {b c : α} : (∀ {a}, a = b ↔ a = c) ↔ b = c :=
  ⟨fun h ↦ by rw [← h], fun h a ↦ by rw [h]⟩

@[simp] theorem eq_iff_eq_cancel_right {a b : α} : (∀ {c}, a = c ↔ b = c) ↔ a = b :=
  ⟨fun h ↦ by rw [h], fun h a ↦ by rw [h]⟩

lemma ne_and_eq_iff_right {a b c : α} (h : b ≠ c) : a ≠ b ∧ a = c ↔ a = c :=
  and_iff_right_of_imp (fun h2 => h2.symm ▸ h.symm)

/-- Wrapper for adding elementary propositions to the type class systems.
Warning: this can easily be abused. See the rest of this docstring for details.

Certain propositions should not be treated as a class globally,
but sometimes it is very convenient to be able to use the type class system
in specific circumstances.

For example, `ZMod p` is a field if and only if `p` is a prime number.
In order to be able to find this field instance automatically by type class search,
we have to turn `p.Prime` into an instance implicit assumption.

On the other hand, making `Nat.Prime` a class would require a major refactoring of the library,
and it is questionable whether making `Nat.Prime` a class is desirable at all.
The compromise is to add the assumption `[Fact p.Prime]` to `ZMod.instField`.

In particular, this class is not intended for turning the type class system
into an automated theorem prover for first-order logic. -/
class Fact (p : Prop) : Prop where
  /-- `Fact.out` contains the unwrapped witness for the fact represented by the instance of
  `Fact p`. -/
  out : p

library_note «fact non-instances» /--
In most cases, we should not have global instances of `Fact`; typeclass search is not an
advanced proof search engine, and adding any such instance has the potential to cause
slowdowns everywhere. We instead declare them as lemmata and make them local instances as required.
-/

theorem Fact.elim {p : Prop} (h : Fact p) : p := h.1
theorem fact_iff {p : Prop} : Fact p ↔ p := ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩

instance {p : Prop} [Decidable p] : Decidable (Fact p) :=
  decidable_of_iff _ fact_iff.symm

/-- Swaps two pairs of arguments to a function. -/
abbrev Function.swap₂ {ι₁ ι₂ : Sort*} {κ₁ : ι₁ → Sort*} {κ₂ : ι₂ → Sort*}
    {φ : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → Sort*} (f : ∀ i₁ j₁ i₂ j₂, φ i₁ j₁ i₂ j₂)
    (i₂ j₂ i₁ j₁) : φ i₁ j₁ i₂ j₂ := f i₁ j₁ i₂ j₂

end Miscellany

/-!
### Declarations about propositional connectives
-/

section Propositional

/-! ### Declarations about `implies` -/

alias Iff.imp := imp_congr

@[deprecated (since := "2026-01-30")] alias imp_iff_right_iff := Classical.imp_iff_right_iff
@[deprecated (since := "2026-01-30")] alias and_or_imp := Classical.and_or_imp

/-- Provide modus tollens (`mt`) as dot notation for implications. -/
protected theorem Function.mt {a b : Prop} : (a → b) → ¬b → ¬a := mt

/-! ### Declarations about `not` -/

alias dec_em := Decidable.em

set_option linter.unusedDecidableInType false in
theorem dec_em' (p : Prop) [Decidable p] : ¬p ∨ p := (dec_em p).symm

alias em := Classical.em

theorem em' (p : Prop) : ¬p ∨ p := (em p).symm

theorem or_not {p : Prop} : p ∨ ¬p := em _

theorem Decidable.eq_or_ne {α : Sort*} (x y : α) [Decidable (x = y)] : x = y ∨ x ≠ y :=
  dec_em <| x = y

theorem Decidable.ne_or_eq {α : Sort*} (x y : α) [Decidable (x = y)] : x ≠ y ∨ x = y :=
  dec_em' <| x = y

theorem eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x ≠ y := em <| x = y

theorem ne_or_eq {α : Sort*} (x y : α) : x ≠ y ∨ x = y := em' <| x = y

theorem by_contradiction {p : Prop} : (¬p → False) → p :=
  open scoped Classical in Decidable.byContradiction

theorem by_cases {p q : Prop} (hpq : p → q) (hnpq : ¬p → q) : q :=
  open scoped Classical in if hp : p then hpq hp else hnpq hp

alias by_contra := by_contradiction

library_note «decidable namespace» /--
In most of mathlib, we use the law of excluded middle (LEM) and the axiom of choice (AC) freely.
The `Decidable` namespace contains versions of lemmas from the root namespace that explicitly
attempt to avoid the axiom of choice, usually by adding decidability assumptions on the inputs.

You can check if a lemma uses the axiom of choice by using `#print axioms foo` and seeing if
`Classical.choice` appears in the list.
-/

library_note «decidable arguments» /--
As mathlib is primarily classical,
if the type signature of a `def` or `lemma` does not require any `Decidable` instances to state,
it is preferable not to introduce any `Decidable` instances that are needed in the proof
as arguments, but rather to use the `classical` tactic as needed.

In the other direction, when `Decidable` instances do appear in the type signature,
it is better to use explicitly introduced ones rather than allowing Lean to automatically infer
classical ones, as these may cause instance mismatch errors later.

Various types that (almost) never have provable decidability, such as `ℝ`, `Set α` or `Ideal R`,
are given global `DecidableEq` instances, so that no decidable arguments have to be provided.
-/

export Classical (not_not)

variable {a b : Prop}

theorem of_not_not {a : Prop} : ¬¬a → a := by_contra

theorem not_ne_iff {α : Sort*} {a b : α} : ¬a ≠ b ↔ a = b := not_not

theorem of_not_imp : ¬(a → b) → a := open scoped Classical in Decidable.of_not_imp

alias Not.decidable_imp_symm := Decidable.not_imp_symm

theorem Not.imp_symm : (¬a → b) → ¬b → a := open scoped Classical in Not.decidable_imp_symm

theorem not_imp_comm : ¬a → b ↔ ¬b → a := open scoped Classical in Decidable.not_imp_comm

@[simp] theorem not_imp_self : ¬a → a ↔ a := open scoped Classical in Decidable.not_imp_self

theorem Imp.swap {a b : Sort*} {c : Prop} : a → b → c ↔ b → a → c :=
  ⟨fun h x y ↦ h y x, fun h x y ↦ h y x⟩

alias Iff.not := not_congr

theorem Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b := h.not.trans not_not

theorem Iff.not_right (h : ¬a ↔ b) : a ↔ ¬b := not_not.symm.trans h.not

protected lemma Iff.ne {α β : Sort*} {a b : α} {c d : β} : (a = b ↔ c = d) → (a ≠ b ↔ c ≠ d) :=
  Iff.not

lemma Iff.ne_left {α β : Sort*} {a b : α} {c d : β} : (a = b ↔ c ≠ d) → (a ≠ b ↔ c = d) :=
  Iff.not_left

lemma Iff.ne_right {α β : Sort*} {a b : α} {c d : β} : (a ≠ b ↔ c = d) → (a = b ↔ c ≠ d) :=
  Iff.not_right

/-! ### Declarations about `Xor` -/

/-- `Xor a b` is the exclusive-or of propositions. -/
def Xor (a b : Prop) := (a ∧ ¬b) ∨ (b ∧ ¬a)

@[deprecated (since := "2026-04-27")] alias Xor' := Xor

@[grind =] theorem xor_def {a b : Prop} : Xor a b ↔ (a ∧ ¬b) ∨ (b ∧ ¬a) := Iff.rfl

instance [Decidable a] [Decidable b] : Decidable (Xor a b) := inferInstanceAs (Decidable (Or ..))

@[simp] theorem xor_true : Xor True = Not := by grind

@[simp] theorem xor_false : Xor False = id := by grind

theorem xor_comm (a b : Prop) : Xor a b = Xor b a := by grind

instance : Std.Commutative Xor := ⟨xor_comm⟩

@[simp] theorem xor_self (a : Prop) : Xor a a = False := by grind

@[simp] theorem xor_not_left : Xor (¬a) b ↔ (a ↔ b) := by grind

@[simp] theorem xor_not_right : Xor a (¬b) ↔ (a ↔ b) := by grind

theorem xor_not_not : Xor (¬a) (¬b) ↔ Xor a b := by grind

protected theorem Xor.or (h : Xor a b) : a ∨ b := by grind

@[deprecated (since := "2026-04-27")]
protected alias Xor'.or := Xor.or

/-! ### Declarations about `and` -/

alias Iff.and := and_congr
alias ⟨And.rotate, _⟩ := and_rotate

theorem and_symm_right {α : Sort*} (a b : α) (p : Prop) : p ∧ a = b ↔ p ∧ b = a := by simp [eq_comm]
theorem and_symm_left {α : Sort*} (a b : α) (p : Prop) : a = b ∧ p ↔ b = a ∧ p := by simp [eq_comm]

/-! ### Declarations about `or` -/

alias Iff.or := or_congr
alias ⟨Or.rotate, _⟩ := or_rotate

theorem Or.elim3 {c d : Prop} (h : a ∨ b ∨ c) (ha : a → d) (hb : b → d) (hc : c → d) : d :=
  Or.elim h ha fun h₂ ↦ Or.elim h₂ hb hc

theorem Or.imp3 {d e c f : Prop} (had : a → d) (hbe : b → e) (hcf : c → f) :
    a ∨ b ∨ c → d ∨ e ∨ f :=
  Or.imp had <| Or.imp hbe hcf

export Classical (or_iff_not_imp_left or_iff_not_imp_right)

theorem not_or_of_imp : (a → b) → ¬a ∨ b := open scoped Classical in Decidable.not_or_of_imp

-- See Note [decidable namespace]
protected theorem Decidable.or_not_of_imp [Decidable a] (h : a → b) : b ∨ ¬a :=
  dite _ (Or.inl ∘ h) Or.inr

theorem or_not_of_imp : (a → b) → b ∨ ¬a := open scoped Classical in Decidable.or_not_of_imp

theorem imp_iff_not_or : a → b ↔ ¬a ∨ b := open scoped Classical in Decidable.imp_iff_not_or

theorem imp_iff_or_not {b a : Prop} : b → a ↔ a ∨ ¬b :=
  open scoped Classical in Decidable.imp_iff_or_not

theorem not_imp_not : ¬a → ¬b ↔ b → a := open scoped Classical in Decidable.not_imp_not

@[deprecated Classical.imp_and_neg_imp_iff (since := "2026-01-30")]
theorem imp_and_neg_imp_iff (p q : Prop) : (p → q) ∧ (¬p → q) ↔ q :=
  Classical.imp_and_neg_imp_iff p

/-- Provide the reverse of modus tollens (`mt`) as dot notation for implications. -/
protected theorem Function.mtr : (¬a → ¬b) → b → a := not_imp_not.mp

theorem or_congr_left' {c a b : Prop} (h : ¬c → (a ↔ b)) : a ∨ c ↔ b ∨ c :=
  open scoped Classical in Decidable.or_congr_left' h

theorem or_congr_right' {c : Prop} (h : ¬a → (b ↔ c)) : a ∨ b ↔ a ∨ c :=
  open scoped Classical in Decidable.or_congr_right' h

/-! ### Declarations about distributivity -/

/-! Declarations about `iff` -/

alias Iff.iff := iff_congr

-- @[simp] -- FIXME simp ignores proof rewrites
theorem iff_mpr_iff_true_intro {P : Prop} (h : P) : Iff.mpr (iff_true_intro h) True.intro = h := rfl

theorem imp_or {a b c : Prop} : a → b ∨ c ↔ (a → b) ∨ (a → c) :=
  open scoped Classical in Decidable.imp_or

theorem imp_or' {a : Sort*} {b c : Prop} : a → b ∨ c ↔ (a → b) ∨ (a → c) :=
  open scoped Classical in Decidable.imp_or'

@[deprecated (since := "2026-01-30")] alias not_imp := Classical.not_imp

theorem peirce (a b : Prop) : ((a → b) → a) → a := open scoped Classical in Decidable.peirce _ _

theorem not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b) := open scoped Classical in Decidable.not_iff_not

theorem not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a) := open scoped Classical in Decidable.not_iff_comm

theorem not_iff : ¬(a ↔ b) ↔ (¬a ↔ b) := open scoped Classical in Decidable.not_iff

theorem iff_not_comm : (a ↔ ¬b) ↔ (b ↔ ¬a) := open scoped Classical in Decidable.iff_not_comm

theorem iff_iff_and_or_not_and_not : (a ↔ b) ↔ a ∧ b ∨ ¬a ∧ ¬b :=
  open scoped Classical in Decidable.iff_iff_and_or_not_and_not

theorem iff_iff_not_or_and_or_not : (a ↔ b) ↔ (¬a ∨ b) ∧ (a ∨ ¬b) :=
  open scoped Classical in Decidable.iff_iff_not_or_and_or_not

theorem not_and_not_right : ¬(a ∧ ¬b) ↔ a → b :=
  open scoped Classical in Decidable.not_and_not_right

/-! ### De Morgan's laws -/

/-- One of **de Morgan's laws**: the negation of a conjunction is logically equivalent to the
disjunction of the negations. -/
theorem not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b := open scoped Classical in Decidable.not_and_iff_not_or_not

theorem or_iff_not_and_not : a ∨ b ↔ ¬(¬a ∧ ¬b) :=
  open scoped Classical in Decidable.or_iff_not_not_and_not

theorem and_iff_not_or_not : a ∧ b ↔ ¬(¬a ∨ ¬b) :=
  open scoped Classical in Decidable.and_iff_not_not_or_not

@[simp] theorem not_xor (P Q : Prop) : ¬Xor P Q ↔ (P ↔ Q) := by
  simp only [not_and, Xor, not_or, not_not, ← iff_iff_implies_and_implies]

theorem xor_iff_not_iff (P Q : Prop) : Xor P Q ↔ ¬(P ↔ Q) := (not_xor P Q).not_right

theorem xor_iff_iff_not : Xor a b ↔ (a ↔ ¬b) := by simp only [← @xor_not_right a, not_not]

theorem xor_iff_not_iff' : Xor a b ↔ (¬a ↔ b) := by simp only [← @xor_not_left _ b, not_not]

theorem xor_iff_or_and_not_and (a b : Prop) : Xor a b ↔ (a ∨ b) ∧ (¬(a ∧ b)) := by
  rw [Xor, or_and_right, not_and_or, and_or_left, and_not_self_iff, false_or,
    and_or_left, and_not_self_iff, or_false]

end Propositional

/-! ### Declarations about equality -/

section Equality

-- todo: change name
theorem forall_cond_comm {α} {s : α → Prop} {p : α → α → Prop} :
    (∀ a, s a → ∀ b, s b → p a b) ↔ ∀ a b, s a → s b → p a b :=
  ⟨fun h a b ha hb ↦ h a ha b hb, fun h a ha b hb ↦ h a b ha hb⟩

theorem forall_mem_comm {α β} [Membership α β] {s : β} {p : α → α → Prop} :
    (∀ a (_ : a ∈ s) b (_ : b ∈ s), p a b) ↔ ∀ a b, a ∈ s → b ∈ s → p a b :=
  forall_cond_comm


lemma ne_of_eq_of_ne {α : Sort*} {a b c : α} (h₁ : a = b) (h₂ : b ≠ c) : a ≠ c := h₁.symm ▸ h₂
lemma ne_of_ne_of_eq {α : Sort*} {a b c : α} (h₁ : a ≠ b) (h₂ : b = c) : a ≠ c := h₂ ▸ h₁

alias Eq.trans_ne := ne_of_eq_of_ne
alias Ne.trans_eq := ne_of_ne_of_eq

theorem eq_equivalence {α : Sort*} : Equivalence (@Eq α) :=
  ⟨Eq.refl, @Eq.symm _, @Eq.trans _⟩

-- @[simp] -- FIXME simp ignores proof rewrites
theorem congr_refl_left {α β : Sort*} (f : α → β) {a b : α} (h : a = b) :
    congr (Eq.refl f) h = congr_arg f h := rfl

-- @[simp] -- FIXME simp ignores proof rewrites
theorem congr_refl_right {α β : Sort*} {f g : α → β} (h : f = g) (a : α) :
    congr h (Eq.refl a) = congr_fun h a := rfl

-- @[simp] -- FIXME simp ignores proof rewrites
theorem congr_arg_refl {α β : Sort*} (f : α → β) (a : α) :
    congr_arg f (Eq.refl a) = Eq.refl (f a) :=
  rfl

-- @[simp] -- FIXME simp ignores proof rewrites
theorem congr_fun_rfl {α β : Sort*} (f : α → β) (a : α) : congr_fun (Eq.refl f) a = Eq.refl (f a) :=
  rfl

-- @[simp] -- FIXME simp ignores proof rewrites
theorem congr_fun_congr_arg {α β γ : Sort*} (f : α → β → γ) {a a' : α} (p : a = a') (b : β) :
    congr_fun (congr_arg f p) b = congr_arg (fun a ↦ f a b) p := rfl

theorem rec_heq_of_heq {α β : Sort _} {a b : α} {C : α → Sort*} {x : C a} {y : β}
    (e : a = b) (h : x ≍ y) : e ▸ x ≍ y :=
  eqRec_heq_iff_heq.mpr h

@[simp]
theorem cast_heq_iff_heq {α β γ : Sort _} (e : α = β) (a : α) (c : γ) :
    cast e a ≍ c ↔ a ≍ c := by subst e; rfl

@[simp]
theorem heq_cast_iff_heq {α β γ : Sort _} (e : β = γ) (a : α) (b : β) :
    a ≍ cast e b ↔ a ≍ b := by subst e; rfl

universe u
variable {α β : Sort u} {e : β = α} {a : α} {b : β}

lemma heq_of_eq_cast (e : β = α) : a = cast e b → a ≍ b := by rintro rfl; simp

lemma eq_cast_iff_heq : a = cast e b ↔ a ≍ b := ⟨heq_of_eq_cast _, fun h ↦ by cases h; rfl⟩

lemma heq_iff_exists_eq_cast :
    a ≍ b ↔ ∃ (h : β = α), a = cast h b :=
  ⟨fun h ↦ ⟨type_eq_of_heq h.symm, eq_cast_iff_heq.mpr h⟩,
    by rintro ⟨rfl, h⟩; rw [h, cast_eq]⟩

lemma heq_iff_exists_cast_eq :
    a ≍ b ↔ ∃ (h : α = β), cast h a = b := by
  simp only [heq_comm (a := a), heq_iff_exists_eq_cast, eq_comm]

end Equality

/-! ### Declarations about quantifiers -/
section Quantifiers
section Dependent

variable {α : Sort*} {β : α → Sort*} {γ : ∀ a, β a → Sort*}

theorem forall₂_imp {p q : ∀ a, β a → Prop} (h : ∀ a b, p a b → q a b) :
    (∀ a b, p a b) → ∀ a b, q a b :=
  forall_imp fun i ↦ forall_imp <| h i

theorem forall₃_imp {p q : ∀ a b, γ a b → Prop} (h : ∀ a b c, p a b c → q a b c) :
    (∀ a b c, p a b c) → ∀ a b c, q a b c :=
  forall_imp fun a ↦ forall₂_imp <| h a

theorem Exists₂.imp {p q : ∀ a, β a → Prop} (h : ∀ a b, p a b → q a b) :
    (∃ a b, p a b) → ∃ a b, q a b :=
  Exists.imp fun a ↦ Exists.imp <| h a

theorem Exists₃.imp {p q : ∀ a b, γ a b → Prop} (h : ∀ a b c, p a b c → q a b c) :
    (∃ a b c, p a b c) → ∃ a b c, q a b c :=
  Exists.imp fun a ↦ Exists₂.imp <| h a

end Dependent

variable {α β : Sort*} {p : α → Prop}

@[deprecated (since := "2026-03-25")] alias forall_swap := forall_comm

theorem forall₂_comm
    {ι₁ ι₂ : Sort*} {κ₁ : ι₁ → Sort*} {κ₂ : ι₂ → Sort*} {p : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → Prop} :
    (∀ i₁ j₁ i₂ j₂, p i₁ j₁ i₂ j₂) ↔ ∀ i₂ j₂ i₁ j₁, p i₁ j₁ i₂ j₂ := ⟨swap₂, swap₂⟩

@[deprecated (since := "2026-03-25")] alias forall₂_swap := forall₂_comm

/-- We intentionally restrict the type of `α` in this lemma so that this is a safer to use in simp
than `forall_comm`. -/
theorem imp_forall_iff {α : Type*} {p : Prop} {q : α → Prop} : (p → ∀ x, q x) ↔ ∀ x, p → q x :=
  forall_comm

lemma imp_forall_iff_forall (A : Prop) (B : A → Prop) : (A → ∀ h : A, B h) ↔ ∀ h : A, B h := by
  by_cases h : A <;> simp [h]

@[deprecated (since := "2026-03-25")] alias exists_swap := exists_comm

theorem exists_and_exists_comm {P : α → Prop} {Q : β → Prop} :
    (∃ a, P a) ∧ (∃ b, Q b) ↔ ∃ a b, P a ∧ Q b :=
  ⟨fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ↦ ⟨a, b, ⟨ha, hb⟩⟩, fun ⟨a, b, ⟨ha, hb⟩⟩ ↦ ⟨⟨a, ha⟩, ⟨b, hb⟩⟩⟩

export Classical (not_forall)

theorem not_forall_not : (¬∀ x, ¬p x) ↔ ∃ x, p x :=
  open scoped Classical in Decidable.not_forall_not

export Classical (not_exists_not)

lemma forall_or_exists_not (P : α → Prop) : (∀ a, P a) ∨ ∃ a, ¬P a := by
  rw [← not_forall]; exact em _

lemma exists_or_forall_not (P : α → Prop) : (∃ a, P a) ∨ ∀ a, ¬P a := by
  rw [← not_exists]; exact em _

theorem forall_imp_iff_exists_imp {α : Sort*} {p : α → Prop} {b : Prop} [ha : Nonempty α] :
    (∀ x, p x) → b ↔ ∃ x, p x → b := by
  classical
  let ⟨a⟩ := ha
  refine ⟨fun h ↦ not_forall_not.1 fun h' ↦ ?_, fun ⟨x, hx⟩ h ↦ hx (h x)⟩
  exact if hb : b then h' a fun _ ↦ hb else hb <| h fun x ↦ (Classical.not_imp.1 (h' x)).1

@[mfld_simps]
theorem forall_true_iff : (α → True) ↔ True := imp_true_iff _

-- Unfortunately this causes simp to loop sometimes, so we
-- add the 2 and 3 cases as simp lemmas instead
theorem forall_true_iff' (h : ∀ a, p a ↔ True) : (∀ a, p a) ↔ True :=
  iff_true_intro fun _ ↦ of_iff_true (h _)

-- This is not marked `@[simp]` because `implies_true : (α → True) = True` works
theorem forall₂_true_iff {β : α → Sort*} : (∀ a, β a → True) ↔ True := by simp

-- This is not marked `@[simp]` because `implies_true : (α → True) = True` works
theorem forall₃_true_iff {β : α → Sort*} {γ : ∀ a, β a → Sort*} :
    (∀ (a) (b : β a), γ a b → True) ↔ True := by simp

theorem Decidable.and_forall_ne [DecidableEq α] (a : α) {p : α → Prop} :
    (p a ∧ ∀ b, b ≠ a → p b) ↔ ∀ b, p b := by
  simp only [← @forall_eq _ p a, ← forall_and, ← or_imp, Decidable.em, forall_const]

theorem and_forall_ne (a : α) : (p a ∧ ∀ b, b ≠ a → p b) ↔ ∀ b, p b :=
  open scoped Classical in Decidable.and_forall_ne a

theorem Ne.ne_or_ne {x y : α} (z : α) (h : x ≠ y) : x ≠ z ∨ y ≠ z :=
  not_and_or.1 <| mt (and_imp.2 (· ▸ ·)) h.symm

@[simp]
theorem exists_apply_eq_apply' (f : α → β) (a' : α) : ∃ a, f a' = f a := ⟨a', rfl⟩

@[simp]
lemma exists_apply_eq_apply2 {α β γ} {f : α → β → γ} {a : α} {b : β} : ∃ x y, f x y = f a b :=
  ⟨a, b, rfl⟩

@[simp]
lemma exists_apply_eq_apply2' {α β γ} {f : α → β → γ} {a : α} {b : β} : ∃ x y, f a b = f x y :=
  ⟨a, b, rfl⟩

@[simp]
lemma exists_apply_eq_apply3 {α β γ δ} {f : α → β → γ → δ} {a : α} {b : β} {c : γ} :
    ∃ x y z, f x y z = f a b c :=
  ⟨a, b, c, rfl⟩

@[simp]
lemma exists_apply_eq_apply3' {α β γ δ} {f : α → β → γ → δ} {a : α} {b : β} {c : γ} :
    ∃ x y z, f a b c = f x y z :=
  ⟨a, b, c, rfl⟩

/--
The constant function witnesses that
there exists a function sending a given term to a given term.

This is sometimes useful in `simp` to discharge side conditions.
-/
theorem exists_apply_eq (a : α) (b : β) : ∃ f : α → β, f a = b := ⟨fun _ ↦ b, rfl⟩

@[simp] theorem exists_exists_and_eq_and {f : α → β} {p : α → Prop} {q : β → Prop} :
    (∃ b, (∃ a, p a ∧ f a = b) ∧ q b) ↔ ∃ a, p a ∧ q (f a) :=
  ⟨fun ⟨_, ⟨a, ha, hab⟩, hb⟩ ↦ ⟨a, ha, hab.symm ▸ hb⟩, fun ⟨a, hp, hq⟩ ↦ ⟨f a, ⟨a, hp, rfl⟩, hq⟩⟩

@[simp] theorem exists_exists_eq_and {f : α → β} {p : β → Prop} :
    (∃ b, (∃ a, f a = b) ∧ p b) ↔ ∃ a, p (f a) :=
  ⟨fun ⟨_, ⟨a, ha⟩, hb⟩ ↦ ⟨a, ha.symm ▸ hb⟩, fun ⟨a, ha⟩ ↦ ⟨f a, ⟨a, rfl⟩, ha⟩⟩

@[simp] theorem exists_exists_and_exists_and_eq_and {α β γ : Type*}
    {f : α → β → γ} {p : α → Prop} {q : β → Prop} {r : γ → Prop} :
    (∃ c, (∃ a, p a ∧ ∃ b, q b ∧ f a b = c) ∧ r c) ↔ ∃ a, p a ∧ ∃ b, q b ∧ r (f a b) :=
  ⟨fun ⟨_, ⟨a, ha, b, hb, hab⟩, hc⟩ ↦ ⟨a, ha, b, hb, hab.symm ▸ hc⟩,
    fun ⟨a, ha, b, hb, hab⟩ ↦ ⟨f a b, ⟨a, ha, b, hb, rfl⟩, hab⟩⟩

@[simp] theorem exists_exists_exists_and_eq {α β γ : Type*}
    {f : α → β → γ} {p : γ → Prop} :
    (∃ c, (∃ a, ∃ b, f a b = c) ∧ p c) ↔ ∃ a, ∃ b, p (f a b) :=
  ⟨fun ⟨_, ⟨a, b, hab⟩, hc⟩ ↦ ⟨a, b, hab.symm ▸ hc⟩,
    fun ⟨a, b, hab⟩ ↦ ⟨f a b, ⟨a, b, rfl⟩, hab⟩⟩

theorem forall_apply_eq_imp_iff' {f : α → β} {p : β → Prop} :
    (∀ a b, f a = b → p b) ↔ ∀ a, p (f a) := by simp

theorem forall_eq_apply_imp_iff' {f : α → β} {p : β → Prop} :
    (∀ a b, b = f a → p b) ↔ ∀ a, p (f a) := by simp

theorem exists₂_comm
    {ι₁ ι₂ : Sort*} {κ₁ : ι₁ → Sort*} {κ₂ : ι₂ → Sort*} {p : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → Prop} :
    (∃ i₁ j₁ i₂ j₂, p i₁ j₁ i₂ j₂) ↔ ∃ i₂ j₂ i₁ j₁, p i₁ j₁ i₂ j₂ := by
  simp only [@exists_comm (κ₁ _), @exists_comm ι₁]

theorem And.exists {p q : Prop} {f : p ∧ q → Prop} : (∃ h, f h) ↔ ∃ hp hq, f ⟨hp, hq⟩ :=
  ⟨fun ⟨h, H⟩ ↦ ⟨h.1, h.2, H⟩, fun ⟨hp, hq, H⟩ ↦ ⟨⟨hp, hq⟩, H⟩⟩

theorem forall_or_of_or_forall {α : Sort*} {p : α → Prop} {b : Prop} (h : b ∨ ∀ x, p x) (x : α) :
    b ∨ p x :=
  h.imp_right fun h₂ ↦ h₂ x

-- See Note [decidable namespace]
protected theorem Decidable.forall_or_left {q : Prop} {p : α → Prop} [Decidable q] :
    (∀ x, q ∨ p x) ↔ q ∨ ∀ x, p x :=
  ⟨fun h ↦ if hq : q then Or.inl hq else
    Or.inr fun x ↦ (h x).resolve_left hq, forall_or_of_or_forall⟩

theorem forall_or_left {q} {p : α → Prop} : (∀ x, q ∨ p x) ↔ q ∨ ∀ x, p x :=
  open scoped Classical in Decidable.forall_or_left

-- See Note [decidable namespace]
protected theorem Decidable.forall_or_right {q} {p : α → Prop} [Decidable q] :
    (∀ x, p x ∨ q) ↔ (∀ x, p x) ∨ q := by simp [or_comm, Decidable.forall_or_left]

theorem forall_or_right {q} {p : α → Prop} : (∀ x, p x ∨ q) ↔ (∀ x, p x) ∨ q :=
  open scoped Classical in Decidable.forall_or_right

@[simp]
theorem forall_and_index {p q : Prop} {r : p ∧ q → Prop} :
    (∀ h : p ∧ q, r h) ↔ ∀ (hp : p) (hq : q), r ⟨hp, hq⟩ :=
  ⟨fun h hp hq ↦ h ⟨hp, hq⟩, fun h h1 ↦ h h1.1 h1.2⟩

theorem forall_and_index' {p q : Prop} {r : p → q → Prop} :
    (∀ (hp : p) (hq : q), r hp hq) ↔ ∀ h : p ∧ q, r h.1 h.2 :=
  (forall_and_index (r := fun h => r h.1 h.2)).symm

theorem Exists.fst {b : Prop} {p : b → Prop} : Exists p → b
  | ⟨h, _⟩ => h

theorem Exists.snd {b : Prop} {p : b → Prop} : ∀ h : Exists p, p h.fst
  | ⟨_, h⟩ => h

theorem Prop.exists_iff {p : Prop → Prop} : (∃ h, p h) ↔ p False ∨ p True :=
  ⟨fun ⟨h₁, h₂⟩ ↦ by_cases (fun H : h₁ ↦ .inr <| by simpa only [H] using h₂)
    (fun H ↦ .inl <| by simpa only [H] using h₂), fun h ↦ h.elim (.intro _) (.intro _)⟩

theorem Prop.forall_iff {p : Prop → Prop} : (∀ h, p h) ↔ p False ∧ p True :=
  ⟨fun H ↦ ⟨H _, H _⟩, fun ⟨h₁, h₂⟩ h ↦ by by_cases H : h <;> simpa only [H]⟩

theorem exists_iff_of_forall {p : Prop} {q : p → Prop} (h : ∀ h, q h) : (∃ h, q h) ↔ p :=
  ⟨Exists.fst, fun H ↦ ⟨H, h H⟩⟩

theorem exists_prop_of_false {p : Prop} {q : p → Prop} : ¬p → ¬∃ h' : p, q h' :=
  mt Exists.fst

/- See `IsEmpty.exists_iff` for the `False` version of `exists_true_left`. -/

theorem forall_prop_congr {p p' : Prop} {q q' : p → Prop} (hq : ∀ h, q h ↔ q' h) (hp : p ↔ p') :
    (∀ h, q h) ↔ ∀ h : p', q' (hp.2 h) :=
  ⟨fun h1 h2 ↦ (hq _).1 (h1 (hp.2 h2)), fun h1 h2 ↦ (hq _).2 (h1 (hp.1 h2))⟩

theorem forall_prop_congr' {p p' : Prop} {q q' : p → Prop} (hq : ∀ h, q h ↔ q' h) (hp : p ↔ p') :
    (∀ h, q h) = ∀ h : p', q' (hp.2 h) :=
  propext (forall_prop_congr hq hp)

lemma imp_congr_eq {a b c d : Prop} (h₁ : a = c) (h₂ : b = d) : (a → b) = (c → d) :=
  propext (imp_congr h₁.to_iff h₂.to_iff)

lemma imp_congr_ctx_eq {a b c d : Prop} (h₁ : a = c) (h₂ : c → b = d) : (a → b) = (c → d) :=
  propext (imp_congr_ctx h₁.to_iff fun hc ↦ (h₂ hc).to_iff)

lemma eq_true_intro {a : Prop} (h : a) : a = True := propext (iff_true_intro h)

lemma eq_false_intro {a : Prop} (h : ¬a) : a = False := propext (iff_false_intro h)

-- FIXME: `alias` creates `def Iff.eq := propext` instead of `lemma Iff.eq := propext`
@[nolint defLemma] alias Iff.eq := propext

lemma iff_eq_eq {a b : Prop} : (a ↔ b) = (a = b) := propext ⟨propext, Eq.to_iff⟩

-- They were not used in Lean 3 and there are already lemmas with those names in Lean 4

/-- See `IsEmpty.forall_iff` for the `False` version. -/
@[simp] theorem forall_true_left (p : True → Prop) : (∀ x, p x) ↔ p True.intro :=
  forall_prop_of_true _

@[simp]
lemma Subsingleton.forall₂_iff {ι : Sort*} [Subsingleton ι] (P : ι → ι → Prop) :
    (∀ i j, P i j) ↔ (∀ i, P i i) := by
  refine forall_congr' fun i ↦ ?_
  have : Nonempty ι := ⟨i⟩
  simp [Subsingleton.elim _ i]

end Quantifiers

/-! ### Classical lemmas -/

namespace Classical

-- use shortened names to avoid conflict when classical namespace is open.
/-- Any prop `p` is decidable classically. A shorthand for `Classical.propDecidable`. -/
@[instance_reducible]
noncomputable def dec (p : Prop) : Decidable p := by infer_instance

variable {α : Sort*}

/-- Any predicate `p` is decidable classically. -/
@[implicit_reducible]
noncomputable def decPred (p : α → Prop) : DecidablePred p := by infer_instance

/-- Any relation `p` is decidable classically. -/
@[implicit_reducible]
noncomputable def decRel (p : α → α → Prop) : DecidableRel p := by infer_instance

/-- Any type `α` has decidable equality classically. -/
@[implicit_reducible]
noncomputable def decEq (α : Sort*) : DecidableEq α := by infer_instance

/-- Construct a function from a default value `H0`, and a function to use if there exists a value
satisfying the predicate. -/
noncomputable def existsCases {α C : Sort*} {p : α → Prop} (H0 : C) (H : ∀ a, p a → C) : C :=
  if h : ∃ a, p a then H (Classical.choose h) (Classical.choose_spec h) else H0

theorem some_spec₂ {α : Sort*} {p : α → Prop} {h : ∃ a, p a} (q : α → Prop)
    (hpq : ∀ a, p a → q a) : q (choose h) := hpq _ <| choose_spec _

/-- A version of `byContradiction` that uses types instead of propositions. -/
protected noncomputable def byContradiction' {α : Sort*} (H : ¬(α → False)) : α :=
  Classical.choice <| (peirce _ False) fun h ↦ (H fun a ↦ h ⟨a⟩).elim

/-- `Classical.byContradiction'` is equivalent to lean's axiom `Classical.choice`. -/
def choice_of_byContradiction' {α : Sort*} (contra : ¬(α → False) → α) : Nonempty α → α :=
  fun H ↦ contra H.elim

-- This can be removed after https://github.com/leanprover/lean4/pull/11316
-- arrives in a release candidate.
grind_pattern Exists.choose_spec => P.choose

@[simp] lemma choose_eq (a : α) : @Exists.choose _ (· = a) ⟨a, rfl⟩ = a := @choose_spec _ (· = a) _

@[simp]
lemma choose_eq' (a : α) : @Exists.choose _ (a = ·) ⟨a, rfl⟩ = a :=
  (@choose_spec _ (a = ·) _).symm

alias axiom_of_choice := axiomOfChoice -- TODO: remove? rename in core?
alias by_cases := byCases -- TODO: remove? rename in core?
alias by_contradiction := byContradiction -- TODO: remove? rename in core?

-- The remaining theorems in this section were ported from Lean 3,
-- but are currently unused in Mathlib, so have been deprecated.
-- If any are being used downstream, please remove the deprecation.

alias prop_complete := propComplete -- TODO: remove? rename in core?

end Classical

/-- This function has the same type as `Exists.recOn`, and can be used to case on an equality,
but `Exists.recOn` can only eliminate into Prop, while this version eliminates into any universe
using the axiom of choice. -/
noncomputable def Exists.classicalRecOn {α : Sort*} {p : α → Prop} (h : ∃ a, p a)
    {C : Sort*} (H : ∀ a, p a → C) : C :=
  H (Classical.choose h) (Classical.choose_spec h)

/-! ### Declarations about bounded quantifiers -/
section BoundedQuantifiers

variable {α : Sort*} {r p q : α → Prop} {P Q : ∀ x, p x → Prop}

theorem bex_def : (∃ (x : _) (_ : p x), q x) ↔ ∃ x, p x ∧ q x :=
  ⟨fun ⟨x, px, qx⟩ ↦ ⟨x, px, qx⟩, fun ⟨x, px, qx⟩ ↦ ⟨x, px, qx⟩⟩

theorem BEx.elim {b : Prop} : (∃ x h, P x h) → (∀ a h, P a h → b) → b
  | ⟨a, h₁, h₂⟩, h' => h' a h₁ h₂

theorem BEx.intro (a : α) (h₁ : p a) (h₂ : P a h₁) : ∃ (x : _) (h : p x), P x h :=
  ⟨a, h₁, h₂⟩

theorem BAll.imp_right (H : ∀ x h, P x h → Q x h) (h₁ : ∀ x h, P x h) (x h) : Q x h :=
  H _ _ <| h₁ _ _

theorem BEx.imp_right (H : ∀ x h, P x h → Q x h) : (∃ x h, P x h) → ∃ x h, Q x h
  | ⟨_, _, h'⟩ => ⟨_, _, H _ _ h'⟩

theorem BAll.imp_left (H : ∀ x, p x → q x) (h₁ : ∀ x, q x → r x) (x) (h : p x) : r x :=
  h₁ _ <| H _ h

theorem BEx.imp_left (H : ∀ x, p x → q x) : (∃ (x : _) (_ : p x), r x) → ∃ (x : _) (_ : q x), r x
  | ⟨x, hp, hr⟩ => ⟨x, H _ hp, hr⟩

theorem exists_mem_of_exists (H : ∀ x, p x) : (∃ x, q x) → ∃ (x : _) (_ : p x), q x
  | ⟨x, hq⟩ => ⟨x, H x, hq⟩

theorem exists_of_exists_mem : (∃ (x : _) (_ : p x), q x) → ∃ x, q x
  | ⟨x, _, hq⟩ => ⟨x, hq⟩


theorem not_exists_mem : (¬∃ x h, P x h) ↔ ∀ x h, ¬P x h := exists₂_imp

theorem not_forall₂_of_exists₂_not : (∃ x h, ¬P x h) → ¬∀ x h, P x h
  | ⟨x, h, hp⟩, al => hp <| al x h

-- See Note [decidable namespace]
protected theorem Decidable.not_forall₂ [Decidable (∃ x h, ¬P x h)] [∀ x h, Decidable (P x h)] :
    (¬∀ x h, P x h) ↔ ∃ x h, ¬P x h :=
  ⟨Not.decidable_imp_symm fun nx x h ↦ nx.decidable_imp_symm
    fun h' ↦ ⟨x, h, h'⟩, not_forall₂_of_exists₂_not⟩

theorem not_forall₂ : (¬∀ x h, P x h) ↔ ∃ x h, ¬P x h :=
  open scoped Classical in Decidable.not_forall₂

theorem forall₂_and : (∀ x h, P x h ∧ Q x h) ↔ (∀ x h, P x h) ∧ ∀ x h, Q x h :=
  Iff.trans (forall_congr' fun _ ↦ forall_and) forall_and

theorem forall_and_left [Nonempty α] (q : Prop) (p : α → Prop) :
    (∀ x, q ∧ p x) ↔ (q ∧ ∀ x, p x) := by rw [forall_and, forall_const]

theorem forall_and_right [Nonempty α] (p : α → Prop) (q : Prop) :
    (∀ x, p x ∧ q) ↔ (∀ x, p x) ∧ q := by rw [forall_and, forall_const]

theorem exists_mem_or : (∃ x h, P x h ∨ Q x h) ↔ (∃ x h, P x h) ∨ ∃ x h, Q x h :=
  Iff.trans (exists_congr fun _ ↦ exists_or) exists_or

theorem forall₂_or_left : (∀ x, p x ∨ q x → r x) ↔ (∀ x, p x → r x) ∧ ∀ x, q x → r x :=
  Iff.trans (forall_congr' fun _ ↦ or_imp) forall_and

theorem exists_mem_or_left :
    (∃ (x : _) (_ : p x ∨ q x), r x) ↔ (∃ (x : _) (_ : p x), r x) ∨ ∃ (x : _) (_ : q x), r x := by
  simp only [exists_prop]
  exact Iff.trans (exists_congr fun x ↦ or_and_right) exists_or

end BoundedQuantifiers

section ite

variable {α : Sort*} {σ : α → Sort*} {P Q R : Prop} [Decidable P]
  {a b c : α} {A : P → α} {B : ¬P → α}

theorem dite_eq_iff : dite P A B = c ↔ (∃ h, A h = c) ∨ ∃ h, B h = c := by
  by_cases P <;> simp [*, exists_prop_of_true, exists_prop_of_false]

theorem ite_eq_iff : ite P a b = c ↔ P ∧ a = c ∨ ¬P ∧ b = c :=
  dite_eq_iff.trans <| by rw [exists_prop, exists_prop]

theorem eq_ite_iff : a = ite P b c ↔ P ∧ a = b ∨ ¬P ∧ a = c :=
  eq_comm.trans <| ite_eq_iff.trans <| (Iff.rfl.and eq_comm).or (Iff.rfl.and eq_comm)

theorem dite_eq_iff' : dite P A B = c ↔ (∀ h, A h = c) ∧ ∀ h, B h = c :=
  ⟨fun he ↦ ⟨fun h ↦ (dif_pos h).symm.trans he, fun h ↦ (dif_neg h).symm.trans he⟩, fun he ↦
    (em P).elim (fun h ↦ (dif_pos h).trans <| he.1 h) fun h ↦ (dif_neg h).trans <| he.2 h⟩

theorem ite_eq_iff' : ite P a b = c ↔ (P → a = c) ∧ (¬P → b = c) := dite_eq_iff'

theorem dite_ne_left_iff : dite P (fun _ ↦ a) B ≠ a ↔ ∃ h, a ≠ B h := by
  grind

theorem dite_ne_right_iff : (dite P A fun _ ↦ b) ≠ b ↔ ∃ h, A h ≠ b := by
  simp only [Ne, dite_eq_right_iff, not_forall]

theorem ite_ne_left_iff : ite P a b ≠ a ↔ ¬P ∧ a ≠ b :=
  dite_ne_left_iff.trans <| by rw [exists_prop]

theorem ite_ne_right_iff : ite P a b ≠ b ↔ P ∧ a ≠ b :=
  dite_ne_right_iff.trans <| by rw [exists_prop]

protected theorem Ne.dite_eq_left_iff (h : ∀ h, a ≠ B h) : dite P (fun _ ↦ a) B = a ↔ P :=
  dite_eq_left_iff.trans ⟨fun H ↦ of_not_not fun h' ↦ h h' (H h').symm, fun h H ↦ (H h).elim⟩

protected theorem Ne.dite_eq_right_iff (h : ∀ h, A h ≠ b) : (dite P A fun _ ↦ b) = b ↔ ¬P :=
  dite_eq_right_iff.trans ⟨fun H h' ↦ h h' (H h'), fun h' H ↦ (h' H).elim⟩

protected theorem Ne.ite_eq_left_iff (h : a ≠ b) : ite P a b = a ↔ P :=
  Ne.dite_eq_left_iff fun _ ↦ h

protected theorem Ne.ite_eq_right_iff (h : a ≠ b) : ite P a b = b ↔ ¬P :=
  Ne.dite_eq_right_iff fun _ ↦ h

protected theorem Ne.dite_ne_left_iff (h : ∀ h, a ≠ B h) : dite P (fun _ ↦ a) B ≠ a ↔ ¬P :=
  dite_ne_left_iff.trans <| exists_iff_of_forall h

protected theorem Ne.dite_ne_right_iff (h : ∀ h, A h ≠ b) : (dite P A fun _ ↦ b) ≠ b ↔ P :=
  dite_ne_right_iff.trans <| exists_iff_of_forall h

protected theorem Ne.ite_ne_left_iff (h : a ≠ b) : ite P a b ≠ a ↔ ¬P :=
  Ne.dite_ne_left_iff fun _ ↦ h

protected theorem Ne.ite_ne_right_iff (h : a ≠ b) : ite P a b ≠ b ↔ P :=
  Ne.dite_ne_right_iff fun _ ↦ h

variable (P Q a b)

theorem dite_eq_or_eq : (∃ h, dite P A B = A h) ∨ ∃ h, dite P A B = B h :=
  if h : _ then .inl ⟨h, dif_pos h⟩ else .inr ⟨h, dif_neg h⟩

theorem ite_eq_or_eq : ite P a b = a ∨ ite P a b = b :=
  if h : _ then .inl (if_pos h) else .inr (if_neg h)

/-- A two-argument function applied to two `dite`s is a `dite` of that two-argument function
applied to each of the branches. -/
theorem apply_dite₂ {α β γ : Sort*} (f : α → β → γ) (P : Prop) [Decidable P]
    (a : P → α) (b : ¬P → α) (c : P → β) (d : ¬P → β) :
    f (dite P a b) (dite P c d) = dite P (fun h ↦ f (a h) (c h)) fun h ↦ f (b h) (d h) := by
  by_cases h : P <;> simp [h]

/-- A two-argument function applied to two `ite`s is a `ite` of that two-argument function
applied to each of the branches. -/
theorem apply_ite₂ {α β γ : Sort*} (f : α → β → γ) (P : Prop) [Decidable P] (a b : α) (c d : β) :
    f (ite P a b) (ite P c d) = ite P (f a c) (f b d) :=
  apply_dite₂ f P (fun _ ↦ a) (fun _ ↦ b) (fun _ ↦ c) fun _ ↦ d

/-- A 'dite' producing a `Pi` type `Π a, σ a`, applied to a value `a : α` is a `dite` that applies
either branch to `a`. -/
theorem dite_apply (f : P → ∀ a, σ a) (g : ¬P → ∀ a, σ a) (a : α) :
    (dite P f g) a = dite P (fun h ↦ f h a) fun h ↦ g h a := by by_cases h : P <;> simp [h]

/-- A 'ite' producing a `Pi` type `Π a, σ a`, applied to a value `a : α` is a `ite` that applies
either branch to `a`. -/
theorem ite_apply (f g : ∀ a, σ a) (a : α) : (ite P f g) a = ite P (f a) (g a) :=
  dite_apply P (fun _ ↦ f) (fun _ ↦ g) a

theorem apply_ite_left {α β γ : Sort*} (f : α → β → γ) (P : Prop) [Decidable P]
    (x y : α) (z : β) : f (if P then x else y) z = if P then f x z else f y z := by grind

section
variable [Decidable Q]

theorem ite_and : ite (P ∧ Q) a b = ite P (ite Q a b) b := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]

theorem ite_or : ite (P ∨ Q) a b = ite P a (ite Q a b) := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]

theorem dite_dite_comm {B : Q → α} {C : ¬P → ¬Q → α} (h : P → ¬Q) :
    (if p : P then A p else if q : Q then B q else C p q) =
     if q : Q then B q else if p : P then A p else C p q := by
  grind

theorem ite_ite_comm (h : P → ¬Q) :
    (if P then a else if Q then b else c) =
     if Q then b else if P then a else c :=
  dite_dite_comm P Q h

end

variable {P Q}

theorem ite_prop_iff_or : (if P then Q else R) ↔ (P ∧ Q ∨ ¬P ∧ R) := by
  by_cases p : P <;> simp [p]

theorem dite_prop_iff_or {Q : P → Prop} {R : ¬P → Prop} :
    dite P Q R ↔ (∃ p, Q p) ∨ (∃ p, R p) := by
  by_cases h : P <;> simp [h, exists_prop_of_false, exists_prop_of_true]

-- TODO make this a simp lemma in a future PR
theorem ite_prop_iff_and : (if P then Q else R) ↔ ((P → Q) ∧ (¬P → R)) := by
  by_cases p : P <;> simp [p]

theorem dite_prop_iff_and {Q : P → Prop} {R : ¬P → Prop} :
    dite P Q R ↔ (∀ h, Q h) ∧ (∀ h, R h) := by
  by_cases h : P <;> simp [h, forall_prop_of_false, forall_prop_of_true]

section congr

variable [Decidable Q] {x y u v : α}

theorem if_ctx_congr (h_c : P ↔ Q) (h_t : Q → x = u) (h_e : ¬Q → y = v) : ite P x y = ite Q u v :=
  ite_congr h_c.eq h_t h_e

theorem if_congr (h_c : P ↔ Q) (h_t : x = u) (h_e : y = v) : ite P x y = ite Q u v :=
  if_ctx_congr h_c (fun _ ↦ h_t) (fun _ ↦ h_e)

end congr

theorem Function.Injective.ite {α β : Sort*} {p : β → Prop} [DecidablePred p] {g : β → α}
    (hg : g.Injective) {f : β → α} (hf : f.Injective) (h : ∀ x y, g x = f y → x = y) :
    (fun x ↦ if p x then g x else f x).Injective :=
  fun x y _ ↦ by rcases em (p x) with (hx | hx) <;> rcases em (p y) with (hy | hy) <;> grind

end ite

/-! ### Membership -/

alias Membership.mem.ne_of_notMem := ne_of_mem_of_not_mem
alias Membership.mem.ne_of_notMem' := ne_of_mem_of_not_mem'

section Membership

variable {α β : Type*} [Membership α β] {p : Prop} [Decidable p]

theorem mem_dite {a : α} {s : p → β} {t : ¬p → β} :
    (a ∈ if h : p then s h else t h) ↔ (∀ h, a ∈ s h) ∧ (∀ h, a ∈ t h) := by
  by_cases h : p <;> simp [h]

theorem dite_mem {a : p → α} {b : ¬p → α} {s : β} :
    (if h : p then a h else b h) ∈ s ↔ (∀ h, a h ∈ s) ∧ (∀ h, b h ∈ s) := by
  by_cases h : p <;> simp [h]

theorem mem_ite {a : α} {s t : β} : (a ∈ if p then s else t) ↔ (p → a ∈ s) ∧ (¬p → a ∈ t) :=
  mem_dite

theorem ite_mem {a b : α} {s : β} : (if p then a else b) ∈ s ↔ (p → a ∈ s) ∧ (¬p → b ∈ s) :=
  dite_mem

end Membership

theorem not_beq_of_ne {α : Type*} [BEq α] [LawfulBEq α] {a b : α} (ne : a ≠ b) : ¬(a == b) :=
  fun h => ne (eq_of_beq h)

alias beq_eq_decide := Bool.beq_eq_decide_eq

@[simp] lemma beq_eq_beq {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {a₁ a₂ : α}
    {b₁ b₂ : β} : (a₁ == a₂) = (b₁ == b₂) ↔ (a₁ = a₂ ↔ b₁ = b₂) := by rw [Bool.eq_iff_iff]; simp

@[ext]
theorem beq_ext {α : Type*} (inst1 : BEq α) (inst2 : BEq α)
    (h : ∀ x y, @BEq.beq _ inst1 x y = @BEq.beq _ inst2 x y) :
    inst1 = inst2 := by
  have ⟨beq1⟩ := inst1
  congr
  funext x y
  exact h x y

theorem lawful_beq_subsingleton {α : Type*} (inst1 : BEq α) (inst2 : BEq α)
    [@LawfulBEq α inst1] [@LawfulBEq α inst2] :
    inst1 = inst2 := by
  ext
  simp
