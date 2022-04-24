/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/

import Mathlib.Tactic.Basic
import Mathlib.Tactic.Ext

-- Workaround for not being able to add ext lemmas from other modules.
@[ext] private def funext' := @funext
@[ext] private def propext' := @propext

@[ext] protected lemma Unit.ext (x y : Unit) : x = y := rfl
@[ext] protected lemma PUnit.ext (x y : Unit) : x = y := rfl

instance {f : α → β} [DecidablePred p] : DecidablePred (p ∘ f) :=
  inferInstanceAs <| DecidablePred fun x => p (f x)

theorem opt_param_eq (α : Sort u) (default : α) : optParam α default = α := optParam_eq α default

theorem Not.intro {a : Prop} (h : a → False) : ¬ a := h

/- not -/

def non_contradictory (a : Prop) : Prop := ¬¬a

theorem non_contradictory_intro {a : Prop} (ha : a) : ¬¬a :=
λ hna : ¬a => absurd ha hna

/-- Ex falso for negation. From `¬ a` and `a` anything follows. This is the same as `absurd` with
the arguments flipped, but it is in the `not` namespace so that projection notation can be used. -/
def Not.elim {α : Sort _} (H1 : ¬a) (H2 : a) : α := absurd H2 H1

@[reducible] theorem Not.imp {a b : Prop} (H2 : ¬b) (H1 : a → b) : ¬a := mt H1 H2

/- eq -/

-- proof irrelevance is built in
def proof_irrel := @proofIrrel

def congr_fun := @congrFun
def congr_arg := @congrArg

lemma trans_rel_left {α : Sort u} {a b c : α} (r : α → α → Prop) (h₁ : r a b) (h₂ : b = c) : r a c :=
h₂ ▸ h₁

lemma trans_rel_right {α : Sort u} {a b c : α} (r : α → α → Prop) (h₁ : a = b) (h₂ : r b c) : r a c :=
h₁.symm ▸ h₂

lemma not_of_eq_false {p : Prop} (h : p = False) : ¬p := fun hp => h ▸ hp

lemma cast_proof_irrel (h₁ h₂ : α = β) (a : α) : cast h₁ a = cast h₂ a := rfl

/- ne -/

lemma Ne.def {α : Sort u} (a b : α) : (a ≠ b) = ¬ (a = b) := rfl

def eq_rec_heq := @eqRec_heq

lemma heq_of_eq_rec_left {φ : α → Sort v} {a a' : α} {p₁ : φ a} {p₂ : φ a'} :
  (e : a = a') → (h₂ : Eq.rec (motive := fun a _ => φ a) p₁ e = p₂) → HEq p₁ p₂
| rfl, rfl => HEq.rfl

lemma heq_of_eq_rec_right {φ : α → Sort v} {a a' : α} {p₁ : φ a} {p₂ : φ a'} :
  (e : a' = a) → (h₂ : p₁ = Eq.rec (motive := fun a _ => φ a) p₂ e) → HEq p₁ p₂
| rfl, rfl => HEq.rfl

lemma of_heq_true (h : HEq a True) : a := of_eq_true (eq_of_heq h)

-- TODO eq_rec_compose

/- and -/

variable {a b c d : Prop}

def And.elim (f : a → b → α) (h : a ∧ b) : α := f h.1 h.2

lemma and.swap : a ∧ b → b ∧ a :=
λ ⟨ha, hb⟩ => ⟨hb, ha⟩

lemma And.symm : a ∧ b → b ∧ a | ⟨ha, hb⟩ => ⟨hb, ha⟩

/- or -/

lemma non_contradictory_em (a : Prop) : ¬¬(a ∨ ¬a) :=
λ not_em : ¬(a ∨ ¬a) =>
  have neg_a : ¬a := λ pos_a : a => absurd (Or.inl pos_a) not_em
  absurd (Or.inr neg_a) not_em

lemma Or.swap : a ∨ b → b ∨ a := Or.rec Or.inr Or.inl

lemma Or.symm : a ∨ b → b ∨ a
| Or.inl h => Or.inr h
| Or.inr h => Or.inl h

/- xor -/

def xor (a b : Prop) := (a ∧ ¬ b) ∨ (b ∧ ¬ a)

/- iff -/

def Iff.elim (f : (a → b) → (b → a) → c) (h : a ↔ b) : c := f h.1 h.2

def Iff.elim_left : (a ↔ b) → a → b := Iff.mp

def Iff.elim_right : (a ↔ b) → b → a := Iff.mpr

lemma Eq.to_iff : a = b → (a ↔ b) | rfl => Iff.rfl

lemma neq_of_not_iff : ¬(a ↔ b) → a ≠ b := mt Eq.to_iff

lemma not_iff_not_of_iff (h₁ : a ↔ b) : ¬ a ↔ ¬ b :=
Iff.intro
  (λ (hna : ¬ a) (hb : b) => hna (Iff.elim_right h₁ hb))
  (λ (hnb : ¬ b) (ha : a) => hnb (Iff.elim_left h₁ ha))

lemma of_iff_true (h : a ↔ True) : a := h.2 ⟨⟩

lemma not_of_iff_false : (a ↔ False) → ¬a := Iff.mp

lemma iff_true_intro (h : a) : a ↔ True := ⟨fun _ => ⟨⟩, fun _ => h⟩

lemma iff_false_intro (h : ¬a) : a ↔ False := ⟨h, fun h => h.elim⟩

lemma not_iff_false_intro (h : a) : ¬a ↔ False := iff_false_intro (not_not_intro h)

lemma not_non_contradictory_iff_absurd (a : Prop) : ¬¬¬a ↔ ¬a := ⟨mt not_not_intro, not_not_intro⟩

lemma imp_congr_left (h : a ↔ b) : (a → c) ↔ (b → c) :=
⟨fun hac ha => hac (h.2 ha), fun hbc ha => hbc (h.1 ha)⟩

lemma imp_congr_right (h : a → (b ↔ c)) : (a → b) ↔ (a → c) :=
⟨fun hab ha => (h ha).1 (hab ha), fun hcd ha => (h ha).2 (hcd ha)⟩

lemma imp_congr_ctx (h₁ : a ↔ c) (h₂ : c → (b ↔ d)) : (a → b) ↔ (c → d) :=
(imp_congr_left h₁).trans (imp_congr_right h₂)

lemma imp_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a → b) ↔ (c → d) := imp_congr_ctx h₁ fun _ => h₂

lemma not_of_not_not_not (h : ¬¬¬a) : ¬a :=
λ ha => absurd (not_not_intro ha) h

-- @[simp] -- Lean 4 has this built-in because it simplifies using decidable instances
lemma not_true : (¬ True) ↔ False :=
iff_false_intro (not_not_intro trivial)

-- @[simp] -- Lean 4 has this built-in because it simplifies using decidable instances
lemma not_false_iff : (¬ False) ↔ True :=
iff_true_intro not_false

lemma not_congr (h : a ↔ b) : ¬a ↔ ¬b := ⟨mt h.2, mt h.1⟩

lemma ne_self_iff_false (a : α) : a ≠ a ↔ False := not_iff_false_intro rfl

lemma eq_self_iff_true (a : α) : a = a ↔ True := iff_true_intro rfl

lemma heq_self_iff_true (a : α) : HEq a a ↔ True := iff_true_intro HEq.rfl

lemma iff_not_self : ¬(a ↔ ¬a) | H => let f h := H.1 h h; f (H.2 f)

@[simp] lemma not_iff_self : ¬(¬a ↔ a) | H => iff_not_self H.symm

lemma true_iff_false : (True ↔ False) ↔ False :=
iff_false_intro (λ h => Iff.mp h trivial)

lemma false_iff_true : (False ↔ True) ↔ False :=
iff_false_intro (λ h => Iff.mpr h trivial)

lemma false_of_true_iff_false : (True ↔ False) → False :=
λ h => Iff.mp h trivial

lemma false_of_true_eq_false : (True = False) → False :=
λ h => h ▸ trivial

lemma true_eq_false_of_false : False → (True = False) :=
False.elim

lemma eq_comm {a b : α} : a = b ↔ b = a := ⟨Eq.symm, Eq.symm⟩

/- and simp rules -/
lemma And.imp (f : a → c) (g : b → d) (h : a ∧ b) : c ∧ d := ⟨f h.1, g h.2⟩

lemma and_implies (hac : a → c) (hbd : b → d) : a ∧ b → c ∧ d := And.imp hac hbd

lemma and_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : a ∧ b ↔ c ∧ d := ⟨And.imp h₁.1 h₂.1, And.imp h₁.2 h₂.2⟩

lemma and_congr_right (h : a → (b ↔ c)) : (a ∧ b) ↔ (a ∧ c) :=
⟨fun ⟨ha, hb⟩ => ⟨ha, (h ha).1 hb⟩, fun ⟨ha, hb⟩ => ⟨ha, (h ha).2 hb⟩⟩

lemma And.comm : a ∧ b ↔ b ∧ a := ⟨And.symm, And.symm⟩

lemma and_comm (a b : Prop) : a ∧ b ↔ b ∧ a := And.comm

lemma And.assoc : (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) :=
⟨fun ⟨⟨ha, hb⟩, hc⟩ => ⟨ha, hb, hc⟩, fun ⟨ha, hb, hc⟩ => ⟨⟨ha, hb⟩, hc⟩⟩

lemma and_assoc (a b : Prop) : (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) := And.assoc

lemma And.left_comm : a ∧ (b ∧ c) ↔ b ∧ (a ∧ c) :=
by rw [← and_assoc, ← and_assoc, @And.comm a b]

lemma and_iff_left (hb : b) : a ∧ b ↔ a := ⟨And.left, fun ha => ⟨ha, hb⟩⟩

lemma and_iff_right (ha : a) : a ∧ b ↔ b := ⟨And.right, fun hb => ⟨ha, hb⟩⟩

@[simp] lemma and_not_self : ¬(a ∧ ¬a) | ⟨ha, hn⟩ => hn ha

@[simp] lemma not_and_self : ¬(¬a ∧ a) | ⟨hn, ha⟩ => hn ha

/- or simp rules -/

lemma Or.imp (f : a → c) (g : b → d) (h : a ∨ b) : c ∨ d := h.elim (inl ∘ f) (inr ∘ g)

lemma Or.imp_left (f : a → b) : a ∨ c → b ∨ c := Or.imp f id

lemma Or.imp_right (f : b → c) : a ∨ b → a ∨ c := Or.imp id f

lemma or_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a ∨ b) ↔ (c ∨ d) :=
⟨Or.imp h₁.1 h₂.1, Or.imp h₁.2 h₂.2⟩

lemma Or.comm : a ∨ b ↔ b ∨ a := ⟨Or.symm, Or.symm⟩

lemma or_comm (a b : Prop) : a ∨ b ↔ b ∨ a := Or.comm

lemma Or.assoc : (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) :=
Iff.intro
  (Or.rec (Or.imp_right Or.inl) (λ h => Or.inr (Or.inr h)))
  (Or.rec (λ h => Or.inl (Or.inl h)) (Or.imp_left Or.inr))

lemma or_assoc (a b : Prop) : (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) :=
Or.assoc

lemma Or.left_comm : a ∨ (b ∨ c) ↔ b ∨ (a ∨ c) :=
Iff.trans (Iff.symm Or.assoc) (Iff.trans (or_congr Or.comm (Iff.refl c)) Or.assoc)

theorem or_iff_right_of_imp (ha : a → b) : (a ∨ b) ↔ b :=
Iff.intro (Or.rec ha id) Or.inr

theorem or_iff_left_of_imp (hb : b → a) : (a ∨ b) ↔ a :=
Iff.intro (Or.rec id hb) Or.inl

-- Port note: in mathlib3, this is not_or
lemma not_or_intro {a b : Prop} : ¬ a → ¬ b → ¬ (a ∨ b)
| hna, hnb, (Or.inl ha) => absurd ha hna
| hna, hnb, (Or.inr hb) => absurd hb hnb

lemma not_or (p q) : ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q :=
⟨fun H => ⟨mt Or.inl H, mt Or.inr H⟩, fun ⟨hp, hq⟩ pq => pq.elim hp hq⟩

/- or resolution rules -/

lemma Or.resolve_left {a b : Prop} (h: a ∨ b) (na : ¬ a) : b :=
Or.elim h (λ ha => absurd ha na) id

lemma Or.neg_resolve_left (h : ¬a ∨ b) (ha : a) : b := h.elim (absurd ha) id

lemma Or.resolve_right {a b : Prop} (h: a ∨ b) (nb : ¬ b) : a :=
Or.elim h id (λ hb => absurd hb nb)

lemma Or.neg_resolve_right (h : a ∨ ¬b) (nb : b) : a := h.elim id (absurd nb)

lemma iff_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a ↔ b) ↔ (c ↔ d) :=
⟨fun h => h₁.symm.trans $ h.trans h₂, fun h => h₁.trans $ h.trans h₂.symm⟩

/- implies simp rule -/
-- This is not marked `@[simp]` because we have `implies_true : (α → True) = True` in core.
lemma implies_true_iff (α : Sort u) : (α → True) ↔ True :=
Iff.intro (λ h => trivial) (λ ha h => trivial)

lemma false_implies_iff (a : Prop) : (False → a) ↔ True :=
Iff.intro (λ h => trivial) (λ ha h => False.elim h)

theorem true_implies_iff (α : Prop) : (True → α) ↔ α :=
Iff.intro (λ h => h trivial) (λ h h' => h)

/- exists unique -/

def ExistsUnique (p : α → Prop) := ∃ x, p x ∧ ∀ y, p y → y = x

open Lean in
macro "∃! " xs:explicitBinders ", " b:term : term => expandExplicitBinders ``ExistsUnique xs b

lemma ExistsUnique.intro {p : α → Prop} (w : α)
  (h₁ : p w) (h₂ : ∀ y, p y → y = w) : ∃! x, p x := ⟨w, h₁, h₂⟩

lemma ExistsUnique.elim {α : Sort u} {p : α → Prop} {b : Prop}
    (h₂ : ∃! x, p x) (h₁ : ∀ x, p x → (∀ y, p y → y = x) → b) : b :=
Exists.elim h₂ (λ w hw => h₁ w (And.left hw) (And.right hw))

lemma exists_unique_of_exists_of_unique {α : Sort u} {p : α → Prop}
    (hex : ∃ x, p x) (hunique : ∀ y₁ y₂, p y₁ → p y₂ → y₁ = y₂) : ∃! x, p x :=
Exists.elim hex (λ x px => ExistsUnique.intro x px (λ y (h : p y) => hunique y x h px))

lemma exists_of_exists_unique {α : Sort u} {p : α → Prop} (h : ∃! x, p x) : ∃ x, p x :=
Exists.elim h (λ x hx => ⟨x, And.left hx⟩)

lemma unique_of_exists_unique {α : Sort u} {p : α → Prop}
    (h : ∃! x, p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂ :=
let ⟨x, hx, hy⟩ := h; (hy _ py₁).trans (hy _ py₂).symm

/- exists, forall, exists unique congruences -/

-- Port note: this is `forall_congr` from Lean 3. In Lean 4, there is already something
-- with that name and a slightly different type.
lemma forall_congr' {p q : α → Prop} (h : ∀ a, p a ↔ q a) : (∀ a, p a) ↔ ∀ a, q a :=
⟨fun H a => (h a).1 (H a), fun H a => (h a).2 (H a)⟩

lemma exists_imp_exists {α : Sort u} {p q : α → Prop}
  (h : ∀ a, (p a → q a)) (p : ∃ a, p a) : ∃ a, q a :=
Exists.elim p (λ a hp => ⟨a, h a hp⟩)

lemma Exists.imp {α : Sort u} {p q : α → Prop}
  (h : ∀ a, (p a → q a)) (p : ∃ a, p a) : ∃ a, q a := exists_imp_exists h p

lemma exists_congr {p q : α → Prop} (h : ∀ a, p a ↔ q a) : (∃ a, p a) ↔ ∃ a, q a :=
⟨exists_imp_exists fun x => (h x).1, exists_imp_exists fun x => (h x).2⟩

lemma exists_unique_congr {p q : α → Prop} (h : ∀ a, p a ↔ q a) : (∃! a, p a) ↔ ∃! a, q a :=
exists_congr fun x => and_congr (h _) $ forall_congr' fun y => imp_congr_left (h _)

lemma forall_not_of_not_exists {p : α → Prop} (hne : ¬∃ x, p x) (x) : ¬p x | hp => hne ⟨x, hp⟩

/- decidable -/

namespace Decidable
  variable {p q : Prop}

  -- TODO: rec_on_true and rec_on_false

  def by_cases {q : Sort u} [φ : Decidable p] : (p → q) → (¬p → q) → q := byCases

  lemma by_contradiction [φ : Decidable p] (h : ¬ p → False) : p := @byContradiction p φ h

  lemma not_not_iff (p) [Decidable p] : (¬ ¬ p) ↔ p :=
  Iff.intro of_not_not not_not_intro

  lemma not_or_iff_and_not (p q) [d₁ : Decidable p] [d₂ : Decidable q] : ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q :=
  Iff.intro
    (λ h => match d₁ with
          | isTrue h₁  => False.elim $ h (Or.inl h₁)
          | isFalse h₁ =>
            match d₂ with
            | isTrue h₂  => False.elim $ h (Or.inr h₂)
            | isFalse h₂ => ⟨h₁, h₂⟩)
    (λ ⟨np, nq⟩ h => Or.elim h np nq)

end Decidable
section
  variable {p q : Prop}
  protected def Or.by_cases [Decidable p] [Decidable q] {α : Sort u}
                                   (h : p ∨ q) (h₁ : p → α) (h₂ : q → α) : α :=
  if hp : p then h₁ hp else
    if hq : q then h₂ hq else
      False.elim (Or.elim h hp hq)
end

section
  variable {p q : Prop}

  instance [Decidable p] [Decidable q] : Decidable (xor p q) :=
  if hp : p then
    if hq : q then isFalse (Or.rec (λ ⟨_, h⟩ => h hq : ¬(p ∧ ¬ q)) (λ ⟨_, h⟩ => h hp : ¬(q ∧ ¬ p)))
    else isTrue $ Or.inl ⟨hp, hq⟩
  else
    if hq : q then isTrue $ Or.inr ⟨hq, hp⟩
    else isFalse (Or.rec (λ ⟨h, _⟩ => hp h : ¬(p ∧ ¬ q)) (λ ⟨h, _⟩ => hq h : ¬(q ∧ ¬ p)))

  instance exists_prop_decidable {p} (P : p → Prop)
    [Dp : Decidable p] [DP : ∀ h, Decidable (P h)] : Decidable (∃ h, P h) :=
  if h : p then decidable_of_decidable_of_iff
    ⟨λ h2 => ⟨h, h2⟩, λ⟨h', h2⟩ => h2⟩ else isFalse (mt (λ⟨h, _⟩ => h) h)

  instance forall_prop_decidable {p} (P : p → Prop)
    [Dp : Decidable p] [DP : ∀ h, Decidable (P h)] : Decidable (∀ h, P h) :=
  if h : p
  then decidable_of_decidable_of_iff ⟨λ h2 _ => h2, λ al => al h⟩
  else isTrue (λ h2 => absurd h2 h)
end

lemma Bool.ff_ne_tt : false = true → False := Bool.noConfusion

def is_dec_eq {α : Sort u} (p : α → α → Bool) : Prop   := ∀ ⦃x y : α⦄, p x y = true → x = y
def is_dec_refl {α : Sort u} (p : α → α → Bool) : Prop := ∀ x, p x x = true

def decidable_eq_of_bool_pred {α : Sort u} {p : α → α → Bool} (h₁ : is_dec_eq p) (h₂ : is_dec_refl p) :
  DecidableEq α :=
λ (x y : α) =>
 if hp : p x y = true then isTrue (h₁ hp)
 else isFalse (λ hxy : x = y => absurd (h₂ y) (by rwa [hxy] at hp))

lemma decidable_eq_inl_refl {α : Sort u} [h : DecidableEq α] (a : α) : h a a = isTrue (Eq.refl a) :=
match (h a a) with
| (isTrue e)  => rfl
| (isFalse n) => absurd rfl n

lemma decidable_eq_inr_neg {α : Sort u} [h : DecidableEq α] {a b : α} : ∀ n : a ≠ b, h a b = isFalse n :=
λ n =>
match (h a b) with
| (isTrue e)   => absurd e n
| (isFalse n₁) => proof_irrel n n₁ ▸ Eq.refl (isFalse n)

/- subsingleton -/

-- TODO: rec_subsingleton

lemma implies_of_if_pos {c t e : Prop} [Decidable c] (h : ite c t e) : c → t :=
by intro hc
   have hp : ite c t e = t := if_pos hc
   rwa [hp] at h

lemma implies_of_if_neg {c t e : Prop} [Decidable c] (h : ite c t e) : ¬c → e :=
by intro hnc
   have hn : ite c t e = e := if_neg hnc
   rwa [hn] at h

lemma if_ctx_congr {α : Sort u} {b c : Prop} [dec_b : Decidable b] [dec_c : Decidable c]
                   {x y u v : α}
                   (h_c : b ↔ c) (h_t : c → x = u) (h_e : ¬c → y = v) :
        ite b x y = ite c u v :=
match dec_b, dec_c with
| (isFalse h₁), (isFalse h₂) => h_e h₂
| (isTrue h₁),  (isTrue h₂)  => h_t h₂
| (isFalse h₁), (isTrue h₂)  => absurd h₂ (Iff.mp (not_iff_not_of_iff h_c) h₁)
| (isTrue h₁),  (isFalse h₂) => absurd h₁ (Iff.mpr (not_iff_not_of_iff h_c) h₂)

lemma if_congr {α : Sort u} {b c : Prop} [dec_b : Decidable b] [dec_c : Decidable c]
               {x y u v : α}
               (h_c : b ↔ c) (h_t : x = u) (h_e : y = v) :
        ite b x y = ite c u v :=
@if_ctx_congr α b c dec_b dec_c x y u v h_c (λ h => h_t) (λ h => h_e)

@[simp] lemma if_true {h : Decidable True} (t e : α) : (@ite α True h t e) = t :=
if_pos trivial

@[simp] lemma if_false {h : Decidable False} (t e : α) : (@ite α False h t e) = e :=
if_neg not_false

lemma if_ctx_congr_prop {b c x y u v : Prop} [dec_b : Decidable b] [dec_c : Decidable c]
                      (h_c : b ↔ c) (h_t : c → (x ↔ u)) (h_e : ¬c → (y ↔ v)) :
        ite b x y ↔ ite c u v :=
match dec_b, dec_c with
| (isFalse h₁), (isFalse h₂) => h_e h₂
| (isTrue h₁),  (isTrue h₂)  => h_t h₂
| (isFalse h₁), (isTrue h₂)  => absurd h₂ (Iff.mp (not_iff_not_of_iff h_c) h₁)
| (isTrue h₁),  (isFalse h₂) => absurd h₁ (Iff.mpr (not_iff_not_of_iff h_c) h₂)

lemma if_congr_prop {b c x y u v : Prop} [dec_b : Decidable b] [dec_c : Decidable c]
                    (h_c : b ↔ c) (h_t : x ↔ u) (h_e : y ↔ v) :
        ite b x y ↔ ite c u v :=
if_ctx_congr_prop h_c (λ h => h_t) (λ h => h_e)

lemma if_ctx_simp_congr_prop {b c x y u v : Prop} [dec_b : Decidable b]
                               (h_c : b ↔ c) (h_t : c → (x ↔ u)) (h_e : ¬c → (y ↔ v)) :
        ite b x y ↔ (@ite Prop c (decidable_of_decidable_of_iff h_c) u v) :=
@if_ctx_congr_prop b c x y u v dec_b (decidable_of_decidable_of_iff h_c) h_c h_t h_e

lemma if_simp_congr_prop {b c x y u v : Prop} [dec_b : Decidable b]
                           (h_c : b ↔ c) (h_t : x ↔ u) (h_e : y ↔ v) :
        ite b x y ↔ (@ite Prop c (decidable_of_decidable_of_iff h_c) u v) :=
@if_ctx_simp_congr_prop b c x y u v dec_b h_c (λ h => h_t) (λ h => h_e)

lemma dif_ctx_congr {α : Sort u} {b c : Prop} [dec_b : Decidable b] [dec_c : Decidable c]
                    {x : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}
                    (h_c : b ↔ c)
                    (h_t : ∀ (h : c),    x (Iff.mpr h_c h)                      = u h)
                    (h_e : ∀ (h : ¬c),   y (Iff.mpr (not_iff_not_of_iff h_c) h) = v h) :
        (@dite α b dec_b x y) = (@dite α c dec_c u v) :=
match dec_b, dec_c with
| (isFalse h₁), (isFalse h₂) => h_e h₂
| (isTrue h₁),  (isTrue h₂)  => h_t h₂
| (isFalse h₁), (isTrue h₂)  => absurd h₂ (Iff.mp (not_iff_not_of_iff h_c) h₁)
| (isTrue h₁),  (isFalse h₂) => absurd h₁ (Iff.mpr (not_iff_not_of_iff h_c) h₂)

lemma dif_ctx_simp_congr {α : Sort u} {b c : Prop} [dec_b : Decidable b]
                         {x : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}
                         (h_c : b ↔ c)
                         (h_t : ∀ (h : c),    x (Iff.mpr h_c h)                      = u h)
                         (h_e : ∀ (h : ¬c),   y (Iff.mpr (not_iff_not_of_iff h_c) h) = v h) :
        (@dite α b dec_b x y) = (@dite α c (decidable_of_decidable_of_iff h_c) u v) :=
@dif_ctx_congr α b c dec_b (decidable_of_decidable_of_iff h_c) x u y v h_c h_t h_e

def as_true (c : Prop) [Decidable c] : Prop :=
if c then True else False

def as_false (c : Prop) [Decidable c] : Prop :=
if c then False else True

lemma of_as_true {c : Prop} [h₁ : Decidable c] (h₂ : as_true c) : c :=
match h₁, h₂ with
| (isTrue h_c),  h₂ => h_c
| (isFalse h_c), h₂ => False.elim h₂

/-- Universe lifting operation -/
structure ulift.{r, s} (α : Type s) : Type (max s r) :=
up :: (down : α)

namespace ulift

/- Bijection between α and ulift.{v} α -/
lemma up_down {α : Type u} : ∀ (b : ulift.{v} α), up (down b) = b
| up a => rfl

lemma down_up {α : Type u} (a : α) : down (up.{v} a) = a := rfl

end ulift

/-- Universe lifting operation from Sort to Type -/
structure plift (α : Sort u) : Type u :=
up :: (down : α)

namespace plift
/- Bijection between α and plift α -/
lemma up_down : ∀ (b : plift α), up (down b) = b
| (up a) => rfl

lemma down_up (a : α) : down (up a) = a := rfl
end plift

/- Equalities for rewriting let-expressions -/
lemma let_value_eq {α : Sort u} {β : Sort v} {a₁ a₂ : α} (b : α → β) :
                   a₁ = a₂ → (let x : α := a₁; b x) = (let x : α := a₂; b x) :=
λ h => Eq.recOn (motive := (λ a _ => (let x : α := a₁; b x) = (let x : α := a; b x))) h rfl

lemma let_value_heq {α : Sort v} {β : α → Sort u} {a₁ a₂ : α} (b : ∀ x : α, β x) :
                    a₁ = a₂ → HEq (let x : α := a₁; b x) (let x : α := a₂; b x) :=
by intro h; rw [h]

lemma let_body_eq {α : Sort v} {β : α → Sort u} (a : α) {b₁ b₂ : ∀ x : α, β x} :
                  (∀ x, b₁ x = b₂ x) → (let x : α := a; b₁ x) = (let x : α := a; b₂ x) :=
by intro h; rw [h]

lemma let_eq {α : Sort v} {β : Sort u} {a₁ a₂ : α} {b₁ b₂ : α → β} :
             a₁ = a₂ → (∀ x, b₁ x = b₂ x) → (let x : α := a₁; b₁ x) = (let x : α := a₂; b₂ x) :=
λ h₁ h₂ => Eq.recOn (motive := λ a _ => (let x := a₁; b₁ x) = (let x := a; b₂ x)) h₁ (h₂ a₁)

-- TODO: `section relation`

section binary
variable {α : Type u} {β : Type v}
variable (f : α → α → α)
variable (inv : α → α)
variable (one : α)
variable (g : α → α → α)

def commutative        := ∀ a b, f a b = f b a
def associative        := ∀ a b c, f (f a b) c = f a (f b c)
def left_identity      := ∀ a, f one a = a
def right_identity     := ∀ a, f a one = a
def RightInverse      := ∀ a, f a (inv a) = one
def left_cancelative   := ∀ a b c, f a b = f a c → b = c
def right_cancelative  := ∀ a b c, f a b = f c b → a = c
def left_distributive  := ∀ a b c, f a (g b c) = g (f a b) (f a c)
def right_distributive := ∀ a b c, f (g a b) c = g (f a c) (f b c)
def right_commutative (h : β → α → β) := ∀ b a₁ a₂, h (h b a₁) a₂ = h (h b a₂) a₁
def left_commutative  (h : α → β → β) := ∀ a₁ a₂ b, h a₁ (h a₂ b) = h a₂ (h a₁ b)

lemma left_comm : commutative f → associative f → left_commutative f :=
by intros hcomm hassoc a b c
   have h1 : f a (f b c) = f (f a b) c := Eq.symm (hassoc a b c)
   have h2 : f (f a b) c = f (f b a) c := hcomm a b ▸ rfl
   have h3 : f (f b a) c = f b (f a c) := hassoc b a c
   rw [←h3, ←h2, ←h1]

lemma right_comm : commutative f → associative f → right_commutative f :=
by intros hcomm hassoc a b c
   have h1 : f (f a b) c = f a (f b c) := hassoc a b c
   have h2 : f a (f b c) = f a (f c b) := hcomm b c ▸ rfl
   have h3 : f a (f c b) = f (f a c) b := Eq.symm (hassoc a c b)
   rw [←h3, ←h2, ←h1]

end binary

-- We define a fix' function here because the fix function in the Lean 4 prelude has
-- `set_option codegen false`.

namespace WellFounded

variable {α : Sort u} {C : α → Sort v} {r : α → α → Prop}

unsafe def fix'.impl (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) : C x :=
  F x fun y _ => impl hwf F y

set_option codegen false in
@[implementedBy fix'.impl]
def fix' (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) : C x := hwf.fix F x

end WellFounded
