/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Mathlib.Init.Logic
import Mathlib.Init.Function
import Mathlib.Tactic.Basic
import Mathlib.Util.LibraryNote
import Mathlib.Tactic.Lint.Basic

section needs_better_home
/- This section contains items that have no direct counterpart from Lean 3 / Mathlib 3.
   They should probably probably live elsewhere and maybe in some cases should be removed.
-/

-- TODO(Jeremy): where is the best place to put these?
lemma EqIffBeqTrue [DecidableEq α] {a b : α} : a = b ↔ ((a == b) = true) :=
⟨decide_eq_true, of_decide_eq_true⟩

lemma NeqIffBeqFalse [DecidableEq α] {a b : α} : a ≠ b ↔ ((a == b) = false) :=
⟨decide_eq_false, of_decide_eq_false⟩

lemma decide_eq_true_iff (p : Prop) [Decidable p] : (decide p = true) ↔ p :=
⟨of_decide_eq_true, decide_eq_true⟩

lemma decide_eq_false_iff_not (p : Prop) [Decidable p] : (decide p = false) ↔ ¬ p :=
⟨of_decide_eq_false, decide_eq_false⟩

lemma not_not_em (a : Prop) : ¬¬(a ∨ ¬a) := fun H => H (Or.inr fun h => H (Or.inl h))

lemma not_not_not : ¬¬¬a ↔ ¬a := ⟨mt not_not_intro, not_not_intro⟩

lemma or_left_comm : a ∨ (b ∨ c) ↔ b ∨ (a ∨ c) :=
by rw [← or_assoc, ← or_assoc, @or_comm a b]

lemma ExistsUnique.exists {p : α → Prop} : (∃! x, p x) → ∃ x, p x | ⟨x, h, _⟩ => ⟨x, h⟩

lemma Decidable.not_and [Decidable p] [Decidable q] : ¬ (p ∧ q) ↔ ¬ p ∨ ¬ q := not_and_iff_or_not _ _

@[inline] def Or.by_cases' [Decidable q] (h : p ∨ q) (h₁ : p → α) (h₂ : q → α) : α :=
if hq : q then h₂ hq else h₁ (h.resolve_right hq)

lemma Exists.nonempty {p : α → Prop} : (∃ x, p x) → Nonempty α | ⟨x, _⟩ => ⟨x⟩

lemma ite_id [h : Decidable c] {α} (t : α) : (if c then t else t) = t := by cases h <;> rfl

end needs_better_home

-- Below are items ported from mathlib3/src/logic/basic.lean.

attribute [local instance] Classical.propDecidable

section miscellany

variable {α : Type _} {β : Type _}

/-- An identity function with its main argument implicit. This will be printed as `hidden` even
if it is applied to a large term, so it can be used for elision,
as done in the `elide` and `unelide` tactics. -/
@[reducible] def hidden {α : Sort _} {a : α} := a

/-- Ex falso, the nondependent eliminator for the `empty` type. -/
def Empty.elim {C : Sort _} : Empty → C := λ e => match e with.

instance : Subsingleton Empty := ⟨λa => a.elim⟩

lemma ne_comm {α} {a b : α} : a ≠ b ↔ b ≠ a := ⟨Ne.symm, Ne.symm⟩

end miscellany

/-!
### Declarations about propositional connectives
-/

theorem false_ne_true : False ≠ True
| h => h.symm ▸ trivial

section propositional
variable {a b c d : Prop}

/-! ### Declarations about `implies` -/

theorem iff_of_eq (e : a = b) : a ↔ b := e ▸ Iff.rfl

theorem iff_iff_eq : (a ↔ b) ↔ a = b := ⟨propext, iff_of_eq⟩

@[simp] lemma eq_iff_iff {p q : Prop} : (p = q) ↔ (p ↔ q) := iff_iff_eq.symm

@[simp] theorem imp_self : (a → a) ↔ True := iff_true_intro id

@[nolint unusedArguments]
theorem imp_intro {α β : Prop} (h : α) : β → α := λ _ => h

theorem imp_false : (a → False) ↔ ¬ a := Iff.rfl

theorem imp_and_distrib {α} : (α → b ∧ c) ↔ (α → b) ∧ (α → c) :=
⟨λ h => ⟨λ ha => (h ha).left, λ ha=> (h ha).right⟩,
 λ h ha => ⟨h.left ha, h.right ha⟩⟩

@[simp] theorem and_imp : (a ∧ b → c) ↔ (a → b → c) :=
Iff.intro (λ h ha hb => h ⟨ha, hb⟩) (λ h ⟨ha, hb⟩ => h ha hb)

theorem iff_def : (a ↔ b) ↔ (a → b) ∧ (b → a) :=
iff_iff_implies_and_implies _ _

theorem iff_def' : (a ↔ b) ↔ (b → a) ∧ (a → b) :=
iff_def.trans And.comm

theorem imp_true_iff {α : Sort _} : (α → True) ↔ True :=
iff_true_intro $ λ_ => trivial

theorem imp_iff_right (ha : a) : (a → b) ↔ b :=
⟨λf => f ha, imp_intro⟩

/-! ### Declarations about `not` -/

theorem not_not_of_not_imp : ¬(a → b) → ¬¬a :=
mt Not.elim

theorem not_of_not_imp {a : Prop} : ¬(a → b) → ¬b :=
mt imp_intro

theorem dec_em (p : Prop) [Decidable p] : p ∨ ¬p := Decidable.em p

theorem dec_em' (p : Prop) [Decidable p] : ¬p ∨ p := (dec_em p).swap

theorem em (p : Prop) : p ∨ ¬p := Classical.em _

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

-- alias by_contradiction ← by_contra
theorem by_contra {p} : (¬p → False) → p := Decidable.by_contradiction

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

-- See Note [decidable namespace]
protected theorem Decidable.not_not [Decidable a] : ¬¬a ↔ a :=
Iff.intro Decidable.by_contradiction not_not_intro

/-- The Double Negation Theorem: `¬ ¬ P` is equivalent to `P`.
The left-to-right direction, double negation elimination (DNE),
is classically true but not constructively. -/
@[simp] theorem not_not : ¬¬a ↔ a := Decidable.not_not

theorem of_not_not : ¬¬a → a := by_contra

-- See Note [decidable namespace]
protected theorem Decidable.of_not_imp [Decidable a] (h : ¬ (a → b)) : a :=
Decidable.by_contradiction (not_not_of_not_imp h)

theorem of_not_imp : ¬ (a → b) → a := Decidable.of_not_imp

-- See Note [decidable namespace]
protected theorem Decidable.not_imp_symm [Decidable a] (h : ¬a → b) (hb : ¬b) : a :=
Decidable.by_contradiction $ hb ∘ h

theorem Not.decidable_imp_symm [Decidable a] : (¬a → b) → ¬b → a := Decidable.not_imp_symm

theorem Not.imp_symm : (¬a → b) → ¬b → a := Not.decidable_imp_symm

-- See Note [decidable namespace]
protected theorem Decidable.not_imp_comm [Decidable a] [Decidable b] : (¬a → b) ↔ (¬b → a) :=
⟨Not.decidable_imp_symm, Not.decidable_imp_symm⟩

theorem not_imp_comm : (¬a → b) ↔ (¬b → a) := Decidable.not_imp_comm

@[simp] theorem imp_not_self : (a → ¬a) ↔ ¬a := ⟨λ h ha => h ha ha, λ h _ => h⟩

theorem Decidable.not_imp_self [Decidable a] : (¬a → a) ↔ a :=
by have := @imp_not_self (¬a); rwa [Decidable.not_not] at this

@[simp] theorem not_imp_self : (¬a → a) ↔ a := Decidable.not_imp_self

theorem imp.swap : (a → b → c) ↔ (b → a → c) :=
⟨Function.swap, Function.swap⟩

theorem imp_not_comm : (a → ¬b) ↔ (b → ¬a) :=
imp.swap

instance Decidable.predToBool {α : Type u} (p : α → Prop) [DecidablePred p] : CoeDep (α → Prop) p (α → Bool) where
  coe := fun b => decide $ p b

/-! ### Declarations about `xor` -/

@[simp] theorem xor_true : xor True = Not := by simp [xor]

@[simp] theorem xor_false : xor False = id := by ext; simp [xor]

theorem xor_comm (a b) : xor a b = xor b a := by simp [xor, and_comm, or_comm]

-- TODO is_commutative instance

@[simp] theorem xor_self (a : Prop) : xor a a = False := by simp [xor]

/-! ### Declarations about `and` -/

theorem and_symm_right (a b : α) (p : Prop) : p ∧ a = b <-> p ∧ b = a :=
Iff.intro
  (fun ⟨hp, a_eq_b⟩ => ⟨hp, a_eq_b.symm⟩)
  (fun ⟨hp, b_eq_a⟩ => ⟨hp, b_eq_a.symm⟩)

theorem and_symm_left (a b : α) (p : Prop) : a = b ∧ p <-> b = a ∧ p :=
Iff.intro
  (fun ⟨a_eq_b, hp⟩ => ⟨a_eq_b.symm, hp⟩)
  (fun ⟨b_eq_a, hp⟩ => ⟨b_eq_a.symm, hp⟩)


theorem and_congr_left (h : c → (a ↔ b)) : a ∧ c ↔ b ∧ c :=
And.comm.trans $ (and_congr_right h).trans And.comm

theorem and_congr_left' (h : a ↔ b) : a ∧ c ↔ b ∧ c := and_congr h Iff.rfl

theorem and_congr_right' (h : b ↔ c) : a ∧ b ↔ a ∧ c := and_congr Iff.rfl h

theorem not_and_of_not_left (b : Prop) : ¬a → ¬(a ∧ b) :=
mt And.left

theorem not_and_of_not_right (a : Prop) {b : Prop} : ¬b → ¬(a ∧ b) :=
mt And.right

theorem And.imp_left (h : a → b) : a ∧ c → b ∧ c :=
And.imp h id

theorem And.imp_right (h : a → b) : c ∧ a → c ∧ b :=
And.imp id h

lemma And.right_comm : (a ∧ b) ∧ c ↔ (a ∧ c) ∧ b :=
by simp only [And.left_comm, And.comm]; exact Iff.rfl

lemma And.rotate : a ∧ b ∧ c ↔ b ∧ c ∧ a :=
by simp only [And.left_comm, And.comm]; exact Iff.rfl

theorem and_not_self_iff (a : Prop) : a ∧ ¬ a ↔ False :=
Iff.intro (λ h => (h.right) (h.left)) (λ h => h.elim)

theorem not_and_self_iff (a : Prop) : ¬ a ∧ a ↔ False :=
Iff.intro (λ ⟨hna, ha⟩ => hna ha) False.elim

theorem and_iff_left_of_imp {a b : Prop} (h : a → b) : (a ∧ b) ↔ a :=
Iff.intro And.left (λ ha => ⟨ha, h ha⟩)

theorem and_iff_right_of_imp {a b : Prop} (h : b → a) : (a ∧ b) ↔ b :=
Iff.intro And.right (λ hb => ⟨h hb, hb⟩)

@[simp] theorem and_iff_left_iff_imp {a b : Prop} : ((a ∧ b) ↔ a) ↔ (a → b) :=
⟨λ h ha => (h.2 ha).2, and_iff_left_of_imp⟩

@[simp] theorem and_iff_right_iff_imp {a b : Prop} : ((a ∧ b) ↔ b) ↔ (b → a) :=
⟨λ h ha => (h.2 ha).1, and_iff_right_of_imp⟩

@[simp] lemma iff_self_and {p q : Prop} : (p ↔ p ∧ q) ↔ (p → q) :=
by rw [@Iff.comm p, and_iff_left_iff_imp]

@[simp] lemma iff_and_self {p q : Prop} : (p ↔ q ∧ p) ↔ (p → q) :=
by rw [and_comm, iff_self_and]

@[simp] lemma And.congr_right_iff : (a ∧ b ↔ a ∧ c) ↔ (a → (b ↔ c)) :=
⟨λ h ha => by simp [ha] at h; exact h, and_congr_right⟩

@[simp] lemma And.congr_left_iff : (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b) :=
by simp only [And.comm, ← And.congr_right_iff]; exact Iff.rfl

@[simp] lemma and_self_left : a ∧ a ∧ b ↔ a ∧ b :=
⟨λ h => ⟨h.1, h.2.2⟩, λ h => ⟨h.1, h.1, h.2⟩⟩

@[simp] lemma and_self_right : (a ∧ b) ∧ b ↔ a ∧ b :=
⟨λ h => ⟨h.1.1, h.2⟩, λ h => ⟨⟨h.1, h.2⟩, h.2⟩⟩

/-! ### Declarations about `or` -/

theorem or_congr_left (h : a ↔ b) : a ∨ c ↔ b ∨ c := or_congr h Iff.rfl

theorem or_congr_right (h : b ↔ c) : a ∨ b ↔ a ∨ c := or_congr Iff.rfl h

theorem or.right_comm : (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b := by rw [or_assoc, or_assoc, or_comm b]

theorem or_of_or_of_imp_of_imp (h₁ : a ∨ b) (h₂ : a → c) (h₃ : b → d) : c ∨ d :=
Or.imp h₂ h₃ h₁

theorem or_of_or_of_imp_left (h₁ : a ∨ c) (h : a → b) : b ∨ c :=
Or.imp_left h h₁

theorem or_of_or_of_imp_right (h₁ : c ∨ a) (h : a → b) : c ∨ b :=
Or.imp_right h h₁

theorem Or.elim3 (h : a ∨ b ∨ c) (ha : a → d) (hb : b → d) (hc : c → d) : d :=
Or.elim h ha (λ h₂ => Or.elim h₂ hb hc)

theorem or_imp_distrib : (a ∨ b → c) ↔ (a → c) ∧ (b → c) :=
⟨fun h => ⟨fun ha => h (Or.inl ha), fun hb => h (Or.inr hb)⟩,
  fun ⟨ha, hb⟩ => Or.rec ha hb⟩

-- See Note [decidable namespace]
protected theorem Decidable.or_iff_not_imp_left [Decidable a] : a ∨ b ↔ (¬ a → b) :=
⟨Or.resolve_left, λ h => dite _ Or.inl (Or.inr ∘ h)⟩

theorem or_iff_not_imp_left : a ∨ b ↔ (¬ a → b) := Decidable.or_iff_not_imp_left

-- See Note [decidable namespace]
protected theorem Decidable.or_iff_not_imp_right [Decidable b] : a ∨ b ↔ (¬ b → a) :=
Or.comm.trans Decidable.or_iff_not_imp_left

theorem or_iff_not_imp_right : a ∨ b ↔ (¬ b → a) := Decidable.or_iff_not_imp_right

-- See Note [decidable namespace]
protected theorem Decidable.not_imp_not [Decidable a] : (¬ a → ¬ b) ↔ (b → a) :=
⟨λ h hb => Decidable.by_contradiction $ λ na => h na hb, mt⟩

theorem not_imp_not : (¬ a → ¬ b) ↔ (b → a) := Decidable.not_imp_not

@[simp] theorem or_iff_left_iff_imp : (a ∨ b ↔ a) ↔ (b → a) :=
⟨λ h hb => h.1 (Or.inr hb), or_iff_left_of_imp⟩

@[simp] theorem or_iff_right_iff_imp : (a ∨ b ↔ b) ↔ (a → b) :=
by rw [or_comm, or_iff_left_iff_imp]

/-! ### Declarations about distributivity -/

/-- `∧` distributes over `∨` (on the left). -/
theorem and_or_distrib_left : a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c) :=
⟨λ ⟨ha, hbc⟩ => hbc.imp (And.intro ha) (And.intro ha),
 Or.rec (And.imp_right Or.inl) (And.imp_right Or.inr)⟩

/-- `∧` distributes over `∨` (on the right). -/
theorem or_and_distrib_right : (a ∨ b) ∧ c ↔ (a ∧ c) ∨ (b ∧ c) :=
(And.comm.trans and_or_distrib_left).trans (or_congr And.comm And.comm)

/-- `∨` distributes over `∧` (on the left). -/
theorem or_and_distrib_left : a ∨ (b ∧ c) ↔ (a ∨ b) ∧ (a ∨ c) :=
⟨Or.rec (λha => And.intro (Or.inl ha) (Or.inl ha)) (And.imp Or.inr Or.inr),
 And.rec $ Or.rec (imp_intro ∘ Or.inl) (Or.imp_right ∘ And.intro)⟩

/-- `∨` distributes over `∧` (on the right). -/
theorem and_or_distrib_right : (a ∧ b) ∨ c ↔ (a ∨ c) ∧ (b ∨ c) :=
(Or.comm.trans or_and_distrib_left).trans (and_congr Or.comm Or.comm)

@[simp] lemma or_self_left : a ∨ a ∨ b ↔ a ∨ b :=
⟨λ h => h.elim Or.inl id, λ h => h.elim Or.inl (Or.inr ∘ Or.inr)⟩

@[simp] lemma or_self_right : (a ∨ b) ∨ b ↔ a ∨ b :=
⟨λ h => h.elim id Or.inr, λ h => h.elim (Or.inl ∘ Or.inl) Or.inr⟩

/-! Declarations about `iff` -/

theorem iff_of_true (ha : a) (hb : b) : a ↔ b :=
⟨λ_ => hb, λ _ => ha⟩

theorem iff_of_false (ha : ¬a) (hb : ¬b) : a ↔ b :=
⟨ha.elim, hb.elim⟩

theorem iff_true_left (ha : a) : (a ↔ b) ↔ b :=
⟨λ h => h.1 ha, iff_of_true ha⟩

theorem iff_true_right (ha : a) : (b ↔ a) ↔ b :=
Iff.comm.trans (iff_true_left ha)

theorem iff_false_left (ha : ¬a) : (a ↔ b) ↔ ¬b :=
⟨λ h => mt h.2 ha, iff_of_false ha⟩

theorem iff_false_right (ha : ¬a) : (b ↔ a) ↔ ¬b :=
Iff.comm.trans (iff_false_left ha)

lemma iff_mpr_iff_true_intro {P : Prop} (h : P) : Iff.mpr (iff_true_intro h) True.intro = h := rfl

-- See Note [decidable namespace]
protected theorem Decidable.not_or_of_imp [Decidable a] (h : a → b) : ¬ a ∨ b :=
if ha : a then Or.inr (h ha) else Or.inl ha

theorem not_or_of_imp : (a → b) → ¬ a ∨ b := Decidable.not_or_of_imp

-- See Note [decidable namespace]
protected theorem Decidable.imp_iff_not_or [Decidable a] : (a → b) ↔ (¬ a ∨ b) :=
⟨Decidable.not_or_of_imp, Or.neg_resolve_left⟩

theorem imp_iff_not_or : (a → b) ↔ (¬ a ∨ b) := Decidable.imp_iff_not_or

-- See Note [decidable namespace]
protected theorem Decidable.imp_or_distrib [Decidable a] : (a → b ∨ c) ↔ (a → b) ∨ (a → c) :=
by by_cases a <;> simp_all

theorem imp_or_distrib : (a → b ∨ c) ↔ (a → b) ∨ (a → c) := Decidable.imp_or_distrib

-- See Note [decidable namespace]
protected theorem Decidable.imp_or_distrib' [Decidable b] : (a → b ∨ c) ↔ (a → b) ∨ (a → c) :=
by by_cases b
   · simp [h]
   · rw [eq_false h, false_or]
     exact Iff.symm (or_iff_right_of_imp (λhx x => False.elim (hx x)))

theorem imp_or_distrib' : (a → b ∨ c) ↔ (a → b) ∨ (a → c) := Decidable.imp_or_distrib'

theorem not_imp_of_and_not : a ∧ ¬ b → ¬ (a → b)
| ⟨ha, hb⟩, h => hb $ h ha

-- See Note [decidable namespace]
protected theorem Decidable.not_imp [Decidable a] : ¬(a → b) ↔ a ∧ ¬b :=
⟨λ h => ⟨Decidable.of_not_imp h, not_of_not_imp h⟩, not_imp_of_and_not⟩

theorem not_imp : ¬(a → b) ↔ a ∧ ¬b := Decidable.not_imp

-- for monotonicity
lemma imp_imp_imp (h₀ : c → a) (h₁ : b → d) : (a → b) → (c → d) :=
λ (h₂ : a → b) => h₁ ∘ h₂ ∘ h₀

-- See Note [decidable namespace]
protected theorem Decidable.peirce (a b : Prop) [Decidable a] : ((a → b) → a) → a :=
if ha : a then λ _ => ha else λ h => h ha.elim

theorem peirce (a b : Prop) : ((a → b) → a) → a := Decidable.peirce _ _

theorem peirce' {a : Prop} (H : ∀ b : Prop, (a → b) → a) : a := H _ id

-- See Note [decidable namespace]
protected theorem Decidable.not_iff_not [Decidable a] [Decidable b] : (¬ a ↔ ¬ b) ↔ (a ↔ b) :=
by rw [@iff_def (¬ a), @iff_def' a]; exact and_congr Decidable.not_imp_not Decidable.not_imp_not

theorem not_iff_not : (¬ a ↔ ¬ b) ↔ (a ↔ b) := Decidable.not_iff_not

-- See Note [decidable namespace]
protected theorem Decidable.not_iff_comm [Decidable a] [Decidable b] : (¬ a ↔ b) ↔ (¬ b ↔ a) :=
by rw [@iff_def (¬ a), @iff_def (¬ b)]; exact and_congr Decidable.not_imp_comm imp_not_comm

theorem not_iff_comm : (¬ a ↔ b) ↔ (¬ b ↔ a) := Decidable.not_iff_comm

-- See Note [decidable namespace]
protected theorem Decidable.not_iff : ∀ [Decidable b], ¬ (a ↔ b) ↔ (¬ a ↔ b) :=
by intro h
   match h with
   | isTrue h => simp[h, iff_true]
   | isFalse h => simp[h, iff_false]

theorem not_iff : ¬ (a ↔ b) ↔ (¬ a ↔ b) := Decidable.not_iff

-- See Note [decidable namespace]
protected theorem Decidable.iff_not_comm [Decidable a] [Decidable b] : (a ↔ ¬ b) ↔ (b ↔ ¬ a) :=
by rw [@iff_def a, @iff_def b]; exact and_congr imp_not_comm Decidable.not_imp_comm

theorem iff_not_comm : (a ↔ ¬ b) ↔ (b ↔ ¬ a) := Decidable.iff_not_comm

-- See Note [decidable namespace]
protected theorem Decidable.iff_iff_and_or_not_and_not [Decidable b] :
  (a ↔ b) ↔ (a ∧ b) ∨ (¬ a ∧ ¬ b) :=
by constructor
   · intro h; rw [h]
     by_cases b
     · exact Or.inl <| And.intro h h
     · exact Or.inr <| And.intro h h
   · intro h
     match h with
     | Or.inl h => exact Iff.intro (λ _ => h.2) (λ _ => h.1)
     | Or.inr h => exact Iff.intro (λ a => False.elim $ h.1 a) (λ b => False.elim $ h.2 b)

theorem iff_iff_and_or_not_and_not : (a ↔ b) ↔ (a ∧ b) ∨ (¬ a ∧ ¬ b) :=
Decidable.iff_iff_and_or_not_and_not

lemma Decidable.iff_iff_not_or_and_or_not [Decidable a] [Decidable b] :
  (a ↔ b) ↔ ((¬a ∨ b) ∧ (a ∨ ¬b)) :=
by rw [iff_iff_implies_and_implies a b]
   simp only [Decidable.imp_iff_not_or, Or.comm]
   exact Iff.rfl

lemma iff_iff_not_or_and_or_not : (a ↔ b) ↔ ((¬a ∨ b) ∧ (a ∨ ¬b)) :=
Decidable.iff_iff_not_or_and_or_not

-- See Note [decidable namespace]
protected theorem Decidable.not_and_not_right [Decidable b] : ¬(a ∧ ¬b) ↔ (a → b) :=
⟨λ h ha => h.decidable_imp_symm $ And.intro ha, λ h ⟨ha, hb⟩ => hb $ h ha⟩

theorem not_and_not_right : ¬(a ∧ ¬b) ↔ (a → b) := Decidable.not_and_not_right

/-- Transfer decidability of `a` to decidability of `b`, if the propositions are equivalent.
**Important**: this function should be used instead of `rw` on `decidable b`, because the
kernel will get stuck reducing the usage of `propext` otherwise,
and `dec_trivial` will not work. -/
@[inline] def decidable_of_iff (a : Prop) (h : a ↔ b) [Decidable a] : Decidable b :=
decidable_of_decidable_of_iff h

/-- Transfer decidability of `b` to decidability of `a`, if the propositions are equivalent.
This is the same as `decidable_of_iff` but the iff is flipped. -/
@[inline] def decidable_of_iff' (b : Prop) (h : a ↔ b) [Decidable b] : Decidable a :=
decidable_of_decidable_of_iff h.symm

/-- Prove that `a` is decidable by constructing a boolean `b` and a proof that `b ↔ a`.
(This is sometimes taken as an alternate definition of decidability.) -/
def decidable_of_bool : ∀ (b : Bool), (b ↔ a) → Decidable a
| true, h => isTrue (h.1 rfl)
| false, h => isFalse (mt h.2 Bool.ff_ne_tt)

/-! ### De Morgan's laws -/

theorem not_and_of_not_or_not (h : ¬ a ∨ ¬ b) : ¬ (a ∧ b)
| ⟨ha, hb⟩ => Or.elim h (absurd ha) (absurd hb)

-- See Note [decidable namespace]
protected theorem Decidable.not_and_distrib [Decidable a] : ¬ (a ∧ b) ↔ ¬a ∨ ¬b :=
⟨λ h => if ha : a then Or.inr (λ hb => h ⟨ha, hb⟩) else Or.inl ha, not_and_of_not_or_not⟩

-- See Note [decidable namespace]
protected theorem Decidable.not_and_distrib' [Decidable b] : ¬ (a ∧ b) ↔ ¬a ∨ ¬b :=
⟨λ h => if hb : b then Or.inl (λ ha => h ⟨ha, hb⟩) else Or.inr hb, not_and_of_not_or_not⟩

/-- One of de Morgan's laws: the negation of a conjunction is logically equivalent to the
disjunction of the negations. -/
theorem not_and_distrib : ¬ (a ∧ b) ↔ ¬a ∨ ¬b := Decidable.not_and_distrib

@[simp] theorem not_and : ¬ (a ∧ b) ↔ (a → ¬ b) := and_imp

theorem not_and' : ¬ (a ∧ b) ↔ b → ¬a :=
not_and.trans imp_not_comm

/-- One of de Morgan's laws: the negation of a disjunction is logically equivalent to the
conjunction of the negations. -/
theorem not_or_distrib : ¬ (a ∨ b) ↔ ¬ a ∧ ¬ b :=
⟨λ h => ⟨λ ha => h (Or.inl ha), λ hb => h (Or.inr hb)⟩,
 λ ⟨h₁, h₂⟩ h => Or.elim h h₁ h₂⟩

-- See Note [decidable namespace]
protected theorem Decidable.or_iff_not_and_not [Decidable a] [Decidable b] : a ∨ b ↔ ¬ (¬a ∧ ¬b) :=
by rw [← not_or_distrib, Decidable.not_not]

theorem or_iff_not_and_not : a ∨ b ↔ ¬ (¬a ∧ ¬b) := Decidable.or_iff_not_and_not

-- See Note [decidable namespace]
protected theorem Decidable.and_iff_not_or_not [Decidable a] [Decidable b] :
  a ∧ b ↔ ¬ (¬ a ∨ ¬ b) :=
by rw [← Decidable.not_and_distrib, Decidable.not_not]

theorem and_iff_not_or_not : a ∧ b ↔ ¬ (¬ a ∨ ¬ b) := Decidable.and_iff_not_or_not

end propositional

/-! ### Declarations about equality -/

section equality

variable {α : Sort _} {a b : α}

theorem heq_iff_eq : HEq a b ↔ a = b :=
⟨eq_of_heq, heq_of_eq⟩

theorem proof_irrel_heq {p q : Prop} (hp : p) (hq : q) : HEq hp hq :=
have : p = q := propext ⟨λ _ => hq, λ _ => hp⟩
by subst q
   exact HEq.rfl

@[simp] lemma eq_rec_constant {α : Sort _} {a a' : α} {β : Sort _} (y : β) (h : a = a') :
  (@Eq.rec α a (λ α _ => β) y a' h) = y :=
by cases h
   exact rfl

lemma congr_arg2 {α β γ : Type _} (f : α → β → γ) {x x' : α} {y y' : β}
  (hx : x = x') (hy : y = y') : f x y = f x' y' :=
by subst hx
   subst hy
   exact rfl

end equality

/-! ### Declarations about quantifiers -/

section quantifiers
variable {α : Sort _} {β : Sort _} {p q : α → Prop} {b : Prop}

lemma forall_imp (h : ∀ a, p a → q a) : (∀ a, p a) → ∀ a, q a :=
λ h' a => h a (h' a)

lemma forall₂_congr {p q : α → β → Prop} (h : ∀ a b, p a b ↔ q a b) :
  (∀ a b, p a b) ↔ (∀ a b, q a b) :=
forall_congr' (λ a => forall_congr' (h a))

lemma forall₃_congr {γ : Sort _} {p q : α → β → γ → Prop}
  (h : ∀ a b c, p a b c ↔ q a b c) :
  (∀ a b c, p a b c) ↔ (∀ a b c, q a b c) :=
forall_congr' (λ a => forall₂_congr (h a))

lemma forall₄_congr {γ δ : Sort _} {p q : α → β → γ → δ → Prop}
  (h : ∀ a b c d, p a b c d ↔ q a b c d) :
  (∀ a b c d, p a b c d) ↔ (∀ a b c d, q a b c d) :=
forall_congr' (λ a => forall₃_congr (h a))

lemma exists_imp_exists' {p : α → Prop} {q : β → Prop} (f : α → β) (hpq : ∀ a, p a → q (f a))
  (hp : ∃ a, p a) : ∃ b, q b :=
Exists.elim hp (λ _ hp' => ⟨_, hpq _ hp'⟩)

lemma exists₂_congr {p q : α → β → Prop} (h : ∀ a b, p a b ↔ q a b) :
  (∃ a b, p a b) ↔ (∃ a b, q a b) :=
exists_congr (λ a => exists_congr (h a))

lemma exists₃_congr {γ : Sort _} {p q : α → β → γ → Prop}
  (h : ∀ a b c, p a b c ↔ q a b c) :
  (∃ a b c, p a b c) ↔ (∃ a b c, q a b c) :=
exists_congr (λ a => exists₂_congr (h a))

lemma exists₄_congr {γ δ : Sort _} {p q : α → β → γ → δ → Prop}
  (h : ∀ a b c d, p a b c d ↔ q a b c d) :
  (∃ a b c d, p a b c d) ↔ (∃ a b c d, q a b c d) :=
exists_congr (λ a => exists₃_congr (h a))

@[simp] theorem exists_imp_distrib : ((∃ x, p x) → b) ↔ ∀ x, p x → b :=
⟨λ h x hpx => h ⟨x, hpx⟩, λ h ⟨x, hpx⟩ => h x hpx⟩

/--
Extract an element from a existential statement, using `Classical.choose`.
-/
-- This enables projection notation.
@[reducible] noncomputable def Exists.choose {p : α → Prop} (P : ∃ a, p a) : α := Classical.choose P

/--
Show that an element extracted from `P : ∃ a, p a` using `P.some` satisfies `p`.
-/
lemma Exists.choose_spec {p : α → Prop} (P : ∃ a, p a) : p (P.choose) := Classical.choose_spec P

theorem not_exists_of_forall_not (h : ∀ x, ¬ p x) : ¬ ∃ x, p x :=
exists_imp_distrib.2 h

@[simp] theorem not_exists : (¬ ∃ x, p x) ↔ ∀ x, ¬ p x :=
exists_imp_distrib

theorem not.decidable_imp_symm [Decidable a] : (¬a → b) → ¬b → a := Decidable.not_imp_symm

theorem not_forall_of_exists_not {p : α → Prop} : (∃ x, ¬ p x) → ¬ ∀ x, p x
| ⟨x, hn⟩, h => hn (h x)

protected theorem Decidable.not_forall {p : α → Prop}
  [Decidable (∃ x, ¬ p x)] [∀ x, Decidable (p x)] : (¬ ∀ x, p x) ↔ ∃ x, ¬ p x :=
⟨not.decidable_imp_symm $ λ nx x => not.decidable_imp_symm (λ h => ⟨x, h⟩) nx,
 not_forall_of_exists_not⟩

@[simp] theorem not_forall {p : α → Prop} : (¬ ∀ x, p x) ↔ ∃ x, ¬ p x := Decidable.not_forall

@[simp] theorem forall_const (α : Sort _) [i : Nonempty α] : (α → b) ↔ b :=
⟨i.elim, λ hb _ => hb⟩

theorem forall_and_distrib {p q : α → Prop} : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
⟨λ h => ⟨λ x => (h x).left, λ x => (h x).right⟩, λ ⟨h₁, h₂⟩ x => ⟨h₁ x, h₂ x⟩⟩

@[simp] theorem forall_eq {p : α → Prop} {a' : α} : (∀ a, a = a' → p a) ↔ p a' :=
⟨λ h => h a' rfl, λ h _ e => e.symm ▸ h⟩

@[simp] theorem forall_eq' {a' : α} : (∀ a, a' = a → p a) ↔ p a' :=
by simp [@eq_comm _ a']

@[simp] theorem exists_false : ¬ (∃ _a : α, False) := fun ⟨_, h⟩ => h

@[simp] theorem exists_and_distrib_left {q : Prop} {p : α → Prop} :
  (∃ x, q ∧ p x) ↔ q ∧ (∃ x, p x) :=
⟨λ ⟨x, hq, hp⟩ => ⟨hq, x, hp⟩, λ ⟨hq, x, hp⟩ => ⟨x, hq, hp⟩⟩

@[simp] theorem exists_and_distrib_right {q : Prop} {p : α → Prop} :
  (∃x, p x ∧ q) ↔ (∃x, p x) ∧ q :=
by simp [And.comm]

@[simp] theorem exists_eq {a' : α} : ∃ a, a = a' := ⟨_, rfl⟩

@[simp] theorem exists_eq' {a' : α} : ∃ a, a' = a := ⟨_, rfl⟩

@[simp] theorem exists_eq_left {p : α → Prop} {a' : α} : (∃ a, a = a' ∧ p a) ↔ p a' :=
⟨λ ⟨_, e, h⟩ => e ▸ h, λ h => ⟨_, rfl, h⟩⟩

@[simp] theorem exists_eq_right {p : α → Prop} {a' : α} : (∃ a, p a ∧ a = a') ↔ p a' :=
(exists_congr $ by exact λ a => And.comm).trans exists_eq_left

@[simp] theorem exists_eq_left' {p : α → Prop} {a' : α} : (∃ a, a' = a ∧ p a) ↔ p a' :=
by simp [@eq_comm _ a']

@[simp] theorem exists_eq_right_right {α : Sort _} {p : α → Prop} {b : Prop} {a' : α} :
(∃ (a : α), p a ∧ b ∧ a = a') ↔ p a' ∧ b :=
  Iff.intro
  (fun ⟨_, ⟨p_a, hb, a_eq_a'⟩⟩ => And.intro (a_eq_a' ▸ p_a) hb)
  (fun ⟨p_a', hb⟩ => Exists.intro a' ⟨p_a', hb, (rfl : a' = a')⟩)

@[simp] theorem exists_eq_right_right' {α : Sort _} {p : α → Prop} {b : Prop} {a' : α} :
(∃ (a : α), p a ∧ b ∧ a' = a) ↔ p a' ∧ b :=
  Iff.intro
  (fun ⟨_, ⟨p_a, hb, a_eq_a'⟩⟩ => And.intro (a_eq_a' ▸ p_a) hb)
  (fun ⟨p_a', hb⟩ => Exists.intro a' ⟨p_a', hb, (rfl : a' = a')⟩)


@[simp]
theorem exists_prop {p q : Prop} : (∃ _h : p, q) ↔ p ∧ q :=
Iff.intro (fun ⟨hp, hq⟩ => And.intro hp hq) (fun ⟨hp, hq⟩ => Exists.intro hp hq)

@[simp] theorem exists_apply_eq_apply {α β : Type _} (f : α → β) (a' : α) : ∃ a, f a = f a' :=
⟨a', rfl⟩

theorem forall_prop_of_true {p : Prop} {q : p → Prop} (h : p) : (∀ h' : p, q h') ↔ q h :=
@forall_const (q h) p ⟨h⟩

end quantifiers

section ite

/-- A function applied to a `dite` is a `dite` of that function applied to each of the branches. -/
lemma apply_dite {α β : Sort _} (f : α → β) (P : Prop) [Decidable P] (x : P → α) (y : ¬ P → α) :
  f (dite P x y) = dite P (λ h => f (x h)) (λ h => f (y h)) :=
by by_cases h : P <;> simp[h]

/-- A function applied to a `int` is a `ite` of that function applied to each of the branches. -/
lemma apply_ite {α β : Sort _} (f : α → β) (P : Prop) [Decidable P] (x y : α) :
  f (ite P x y) = ite P (f x) (f y) :=
apply_dite f P (λ _ => x) (λ _ => y)

/-- Negation of the condition `P : Prop` in a `dite` is the same as swapping the branches. -/
@[simp] lemma dite_not {α : Sort _} (P : Prop) [Decidable P]  (x : ¬ P → α) (y : ¬¬ P → α) :
  dite (¬ P) x y = dite P (λ h => y (not_not_intro h)) x :=
by by_cases h : P <;> simp[h]

/-- Negation of the condition `P : Prop` in a `ite` is the same as swapping the branches. -/
@[simp] lemma ite_not {α : Sort _} (P : Prop) [Decidable P] (x y : α) :
 ite (¬ P) x y = ite P y x :=
dite_not P (λ _ => x) (λ _ => y)

end ite
