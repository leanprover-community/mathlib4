/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Mathlib.Init.Logic
import Mathlib.Init.Function
import Mathlib.Tactic.Basic
import Std.Util.LibraryNote
import Std.Tactic.Lint.Basic

section needs_better_home
/- This section contains items that have no direct counterpart from Lean 3 / Mathlib 3.
   They should probably probably live elsewhere and maybe in some cases should be removed.
-/

lemma ExistsUnique.exists {p : α → Prop} : (∃! x, p x) → ∃ x, p x | ⟨x, h, _⟩ => ⟨x, h⟩

end needs_better_home

-- Below are items ported from mathlib3/src/logic/basic.lean.

attribute [local instance] Classical.propDecidable

section miscellany

variable {α : Type _} {β : Type _}

/-- An identity function with its main argument implicit. This will be printed as `hidden` even
if it is applied to a large term, so it can be used for elision,
as done in the `elide` and `unelide` tactics. -/
@[reducible] def hidden {α : Sort _} {a : α} := a

end miscellany

/-!
### Declarations about propositional connectives
-/

section propositional
variable {a b c d : Prop}

/-! ### Declarations about `implies` -/

alias imp_and ← imp_and_distrib

/-! ### Declarations about `not` -/

alias Decidable.em ← dec_em

theorem dec_em' (p : Prop) [Decidable p] : ¬p ∨ p := (dec_em p).swap

alias Classical.em ← em

theorem em' (p : Prop) : ¬p ∨ p := (em p).swap

theorem or_not {p : Prop} : p ∨ ¬p := em _

section eq_or_ne

variable {α : Sort _} (x y : α)

theorem Decidable.eq_or_ne [Decidable (x = y)] : x = y ∨ x ≠ y := dec_em $ x = y

theorem Decidable.ne_or_eq [Decidable (x = y)] : x ≠ y ∨ x = y := dec_em' $ x = y

theorem eq_or_ne : x = y ∨ x ≠ y := em $ x = y

theorem ne_or_eq : x ≠ y ∨ x = y := em' $ x = y

end eq_or_ne

theorem by_contradiction {p} : (¬p → False) → p := Decidable.by_contradiction

alias by_contradiction ← by_contra

library_note "decidable namespace" /--
In most of mathlib, we use the law of excluded middle (LEM) and the axiom of choice (AC) freely.
The `decidable` namespace contains versions of lemmas from the root namespace that explicitly
attempt to avoid the axiom of choice, usually by adding decidability assumptions on the inputs.

You can check if a lemma uses the axiom of choice by using `#print axioms foo` and seeing if
`classical.choice` appears in the list.
-/

library_note "decidable arguments" /--
As mathlib is primarily classical,
if the type signature of a `def` or `lemma` does not require any `decidable` instances to state,
it is preferable not to introduce any `decidable` instances that are needed in the proof
as arguments, but rather to use the `classical` tactic as needed.

In the other direction, when `decidable` instances do appear in the type signature,
it is better to use explicitly introduced ones rather than allowing Lean to automatically infer
classical ones, as these may cause instance mismatch errors later.
-/

/-- The Double Negation Theorem: `¬ ¬ P` is equivalent to `P`.
The left-to-right direction, double negation elimination (DNE),
is classically true but not constructively. -/
@[simp] theorem not_not : ¬¬a ↔ a := Decidable.not_not

theorem not_ne_iff {a b : α} : ¬a ≠ b ↔ a = b := not_not

theorem of_not_not : ¬¬a → a := by_contra
theorem of_not_imp : ¬ (a → b) → a := Decidable.of_not_imp

alias Decidable.not_imp_symm ← Not.decidable_imp_symm

theorem Not.imp_symm : (¬a → b) → ¬b → a := Not.decidable_imp_symm
theorem not_imp_comm : (¬a → b) ↔ (¬b → a) := Decidable.not_imp_comm
@[simp] theorem not_imp_self : (¬a → a) ↔ a := Decidable.not_imp_self

/-! ### Declarations about `xor` -/

@[simp] theorem xor_true : xor True = Not := by simp [xor]

@[simp] theorem xor_false : xor False = id := by ext; simp [xor]

theorem xor_comm (a b) : xor a b = xor b a := by simp [xor, and_comm, or_comm]

-- TODO is_commutative instance

@[simp] theorem xor_self (a : Prop) : xor a a = False := by simp [xor]

/-! ### Declarations about `and` -/

theorem and_symm_right (a b : α) (p : Prop) : p ∧ a = b ↔ p ∧ b = a := by simp [eq_comm]
theorem and_symm_left (a b : α) (p : Prop) : a = b ∧ p ↔ b = a ∧ p := by simp [eq_comm]

alias and_right_comm ← And.right_comm
alias and_rotate ← And.rotate
alias and_congr_right_iff ← And.congr_right_iff
alias and_congr_left_iff ← And.congr_left_iff

/-! ### Declarations about `or` -/

alias or_right_comm ← Or.right_comm

theorem or_of_or_of_imp_of_imp (h₁ : a ∨ b) (h₂ : a → c) (h₃ : b → d) : c ∨ d := Or.imp h₂ h₃ h₁
theorem or_of_or_of_imp_left (h₁ : a ∨ c) (h : a → b) : b ∨ c := Or.imp_left h h₁
theorem or_of_or_of_imp_right (h₁ : c ∨ a) (h : a → b) : c ∨ b := Or.imp_right h h₁

theorem Or.elim3 (h : a ∨ b ∨ c) (ha : a → d) (hb : b → d) (hc : c → d) : d :=
  h.elim ha fun h₂ => h₂.elim hb hc

theorem Or.imp3 (had : a → d) (hbe : b → e) (hcf : c → f) : a ∨ b ∨ c → d ∨ e ∨ f :=
  .imp had <| .imp hbe hcf

alias or_imp ← or_imp_distrib

theorem or_iff_not_imp_left : a ∨ b ↔ (¬ a → b) := Decidable.or_iff_not_imp_left
theorem or_iff_not_imp_right : a ∨ b ↔ (¬ b → a) := Decidable.or_iff_not_imp_right
theorem not_imp_not : (¬ a → ¬ b) ↔ (b → a) := Decidable.not_imp_not

/-! ### Declarations about distributivity -/

alias and_or_left ← and_or_distrib_left
alias and_or_right ← and_or_distrib_right
alias or_and_left ← or_and_distrib_left
alias or_and_right ← or_and_distrib_right

/-! Declarations about `iff` -/

lemma iff_mpr_iff_true_intro {P : Prop} (h : P) : Iff.mpr (iff_true_intro h) True.intro = h := rfl

theorem not_or_of_imp : (a → b) → ¬ a ∨ b := Decidable.not_or_of_imp
theorem imp_iff_not_or : (a → b) ↔ (¬ a ∨ b) := Decidable.imp_iff_not_or
theorem imp_iff_or_not : b → a ↔ a ∨ ¬b := Decidable.imp_iff_or_not

alias Decidable.imp_or ← Decidable.imp_or_distrib
alias Decidable.imp_or' ← Decidable.imp_or_distrib'

theorem imp_or_distrib : (a → b ∨ c) ↔ (a → b) ∨ (a → c) := Decidable.imp_or_distrib
theorem imp_or_distrib' : (a → b ∨ c) ↔ (a → b) ∨ (a → c) := Decidable.imp_or_distrib'
theorem not_imp : ¬(a → b) ↔ a ∧ ¬b := Decidable.not_imp
theorem peirce (a b : Prop) : ((a → b) → a) → a := Decidable.peirce _ _
theorem not_iff_not : (¬ a ↔ ¬ b) ↔ (a ↔ b) := Decidable.not_iff_not
theorem not_iff_comm : (¬ a ↔ b) ↔ (¬ b ↔ a) := Decidable.not_iff_comm
theorem not_iff : ¬ (a ↔ b) ↔ (¬ a ↔ b) := Decidable.not_iff
theorem iff_not_comm : (a ↔ ¬ b) ↔ (b ↔ ¬ a) := Decidable.iff_not_comm
theorem iff_iff_and_or_not_and_not : (a ↔ b) ↔ (a ∧ b) ∨ (¬ a ∧ ¬ b) :=
  Decidable.iff_iff_and_or_not_and_not
theorem iff_iff_not_or_and_or_not : (a ↔ b) ↔ ((¬a ∨ b) ∧ (a ∨ ¬b)) :=
  Decidable.iff_iff_not_or_and_or_not
theorem not_and_not_right : ¬(a ∧ ¬b) ↔ (a → b) := Decidable.not_and_not_right

/-! ### De Morgan's laws -/

alias Decidable.not_and ← Decidable.not_and_distrib
alias Decidable.not_and' ← Decidable.not_and_distrib'

/-- One of de Morgan's laws: the negation of a conjunction is logically equivalent to the
disjunction of the negations. -/
theorem not_and_distrib : ¬ (a ∧ b) ↔ ¬a ∨ ¬b := Decidable.not_and_distrib

alias not_or ← not_or_distrib

theorem or_iff_not_and_not : a ∨ b ↔ ¬ (¬a ∧ ¬b) := Decidable.or_iff_not_and_not
theorem and_iff_not_or_not : a ∧ b ↔ ¬ (¬ a ∨ ¬ b) := Decidable.and_iff_not_or_not
@[simp] theorem imp_iff_right_iff : (a → b ↔ b) ↔ a ∨ b := Decidable.imp_iff_right_iff
@[simp] theorem and_or_imp : a ∧ b ∨ (a → c) ↔ a → b ∨ c := Decidable.and_or_imp
theorem or_congr_left' (h : ¬c → (a ↔ b)) : a ∨ c ↔ b ∨ c := Decidable.or_congr_left' h
theorem or_congr_right' (h : ¬a → (b ↔ c)) : a ∨ b ↔ a ∨ c := Decidable.or_congr_right' h

end propositional

/-! ### Declarations about equality -/

section equality

variable {α : Sort _} {a b : α}

alias congrArg₂ ← congr_arg2

end equality

/-! ### Declarations about quantifiers -/

section quantifiers
variable {α : Sort _} {β : Sort _} {p q : α → Prop} {b : Prop}

alias Exists.imp' ← exists_imp_exists'
alias exists_imp ← exists_imp_distrib
alias exists_imp ↔ _ not_exists_of_forall_not

protected theorem Decidable.not_forall {p : α → Prop}
  [Decidable (∃ x, ¬ p x)] [∀ x, Decidable (p x)] : (¬ ∀ x, p x) ↔ ∃ x, ¬ p x :=
⟨Not.decidable_imp_symm $ λ nx x => Not.decidable_imp_symm (λ h => ⟨x, h⟩) nx,
 not_forall_of_exists_not⟩

@[simp] theorem not_forall {p : α → Prop} : (¬ ∀ x, p x) ↔ ∃ x, ¬ p x := Decidable.not_forall

alias forall_and ← forall_and_distrib
alias exists_and_left ← exists_and_distrib_left
alias exists_and_right ← exists_and_distrib_right

end quantifiers

/-- In classical logic, we can decide a proposition. -/
noncomputable def Classical.dec (p : Prop) : Decidable p := inferInstance

theorem forall_true_iff : α → True ↔ True := iff_true_intro fun _ => trivial

theorem forall_prop_of_false {p : Prop} {q : p → Prop} (hn : ¬p) : (∀ h' : p, q h') ↔ True :=
  iff_true_intro fun h => hn.elim h

open Function

theorem forall_swap {p : α → β → Prop} : (∀ x y, p x y) ↔ ∀ y x, p x y := ⟨swap, swap⟩

/-! ### Declarations about bounded quantifiers -/

section BoundedQuantifiers

variable {α} {p q r : α → Prop} {P Q : ∀ x, p x → Prop}

theorem Ball.imp_right (H : ∀ x h, P x h → Q x h) (h₁ : ∀ x h, P x h) (x h) : Q x h :=
  H _ _ <| h₁ _ _

theorem Ball.imp_left (H : ∀ x, p x → q x) (h₁ : ∀ x, q x → r x) (x) (h : p x) : r x :=
  h₁ _ <| H _ h

end BoundedQuantifiers
