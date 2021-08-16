/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Mathlib.Init.Logic
import Mathlib.Tactic.Basic

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

namespace WellFounded

variable {α : Sort u} {C : α → Sort v} {r : α → α → Prop}

unsafe def fix'.impl (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) : C x :=
  F x fun y _ => impl hwf F y

set_option codegen false in
@[implementedBy fix'.impl]
def fix' (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) : C x := hwf.fix F x

end WellFounded

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

/-- Ex falso for negation. From `¬ a` and `a` anything follows. This is the same as `absurd` with
the arguments flipped, but it is in the `not` namespace so that projection notation can be used. -/
def Not.elim {α : Sort _} (H1 : ¬a) (H2 : a) : α := absurd H2 H1

@[reducible] theorem Not.imp {a b : Prop} (H2 : ¬b) (H1 : a → b) : ¬a := mt H1 H2

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

protected theorem Decidable.not_imp_symm [Decidable a] (h : ¬a → b) (hb : ¬b) : a :=
Decidable.by_contradiction $ hb ∘ h

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

theorem or.elim3 (h : a ∨ b ∨ c) (ha : a → d) (hb : b → d) (hc : c → d) : d :=
Or.elim_on h ha (λ h₂ => Or.elim_on h₂ hb hc)

theorem or_imp_distrib : (a ∨ b → c) ↔ (a → c) ∧ (b → c) :=
⟨fun h => ⟨fun ha => h (Or.inl ha), fun hb => h (Or.inr hb)⟩,
  fun ⟨ha, hb⟩ => Or.rec ha hb⟩

def decidable_of_iff (a : Prop) (h : a ↔ b) [D : Decidable a] : Decidable b :=
decidableOfDecidableOfIff D h

@[simp] theorem not_and : ¬ (a ∧ b) ↔ (a → ¬ b) := and_imp

end propositional

/-! ### Declarations about equality -/

section equality

variable {α : Sort _} {a b : α}

@[simp] theorem heq_iff_eq : HEq a b ↔ a = b :=
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

lemma Exists.imp (h : ∀ a, (p a → q a)) (p : ∃ a, p a) : ∃ a, q a := exists_imp_exists h p

lemma exists_imp_exists' {p : α → Prop} {q : β → Prop} (f : α → β) (hpq : ∀ a, p a → q (f a))
  (hp : ∃ a, p a) : ∃ b, q b :=
Exists.elim hp (λ a hp' => ⟨_, hpq _ hp'⟩)

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
⟨i.elim, λ hb x => hb⟩

theorem forall_and_distrib {p q : α → Prop} : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
⟨λ h => ⟨λ x => (h x).left, λ x => (h x).right⟩, λ ⟨h₁, h₂⟩ x => ⟨h₁ x, h₂ x⟩⟩

@[simp] theorem forall_eq {p : α → Prop} {a' : α} : (∀a, a = a' → p a) ↔ p a' :=
⟨λ h => h a' rfl, λ h a e => e.symm ▸ h⟩

@[simp] theorem exists_false : ¬ (∃a:α, False) := fun ⟨a, h⟩ => h

@[simp] theorem exists_and_distrib_left {q : Prop} {p : α → Prop} :
  (∃x, q ∧ p x) ↔ q ∧ (∃x, p x) :=
⟨λ ⟨x, hq, hp⟩ => ⟨hq, x, hp⟩, λ ⟨hq, x, hp⟩ => ⟨x, hq, hp⟩⟩

@[simp] theorem exists_and_distrib_right {q : Prop} {p : α → Prop} :
  (∃x, p x ∧ q) ↔ (∃x, p x) ∧ q :=
by simp [And.comm]

@[simp] theorem exists_eq {a' : α} : ∃ a, a = a' := ⟨_, rfl⟩

@[simp] theorem exists_eq' {a' : α} : ∃ a, a' = a := ⟨_, rfl⟩

@[simp] theorem exists_eq_left {p : α → Prop} {a' : α} : (∃ a, a = a' ∧ p a) ↔ p a' :=
⟨λ ⟨a, e, h⟩ => e ▸ h, λ h => ⟨_, rfl, h⟩⟩

@[simp] theorem exists_eq_right {p : α → Prop} {a' : α} : (∃ a, p a ∧ a = a') ↔ p a' :=
(exists_congr $ by exact λ a => And.comm).trans exists_eq_left

@[simp] theorem exists_eq_left' {p : α → Prop} {a' : α} : (∃ a, a' = a ∧ p a) ↔ p a' :=
by simp [@eq_comm _ a']

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
