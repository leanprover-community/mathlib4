/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/

import Std.Tactic.Ext
import Std.Tactic.Lint.Basic
import Std.Logic
import Mathlib.Tactic.Alias
import Mathlib.Tactic.Basic

theorem opt_param_eq (α : Sort u) (default : α) : optParam α default = α := optParam_eq α default

/- not -/

def non_contradictory (a : Prop) : Prop := ¬¬a

alias not_not_intro ← non_contradictory_intro

/- eq -/

alias proofIrrel ← proof_irrel
alias congrFun ← congr_fun
alias congrArg ← congr_arg

lemma trans_rel_left {α : Sort u} {a b c : α}
    (r : α → α → Prop) (h₁ : r a b) (h₂ : b = c) : r a c := h₂ ▸ h₁

lemma trans_rel_right {α : Sort u} {a b c : α}
    (r : α → α → Prop) (h₁ : a = b) (h₂ : r b c) : r a c := h₁.symm ▸ h₂

lemma not_of_eq_false {p : Prop} (h : p = False) : ¬p := fun hp => h ▸ hp

lemma cast_proof_irrel (h₁ h₂ : α = β) (a : α) : cast h₁ a = cast h₂ a := rfl

/- ne -/

lemma Ne.def {α : Sort u} (a b : α) : (a ≠ b) = ¬ (a = b) := rfl

alias eqRec_heq ← eq_rec_heq

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

alias And.symm ← And.swap

/- or -/

alias not_not_em ← non_contradictory_em
alias Or.symm ← Or.swap

/- xor -/

def xor (a b : Prop) := (a ∧ ¬ b) ∨ (b ∧ ¬ a)

/- iff -/

theorem Iff.elim_left : type_of% @Iff.mp := @Iff.mp
theorem Iff.elim_right : type_of% @Iff.mpr := @Iff.mpr
alias not_congr ← not_iff_not_of_iff
alias not_not_not ← not_non_contradictory_iff_absurd
alias not_not_not ↔ not_of_not_not_not _
alias and_assoc ← And.assoc
alias and_left_comm ← And.left_comm
alias or_assoc ← Or.assoc
alias or_left_comm ← Or.left_comm

-- This is need for `calc` to work with `iff`.
instance : Trans Iff Iff Iff where
  trans := fun p q => p.trans q

/- exists unique -/

def ExistsUnique (p : α → Prop) := ∃ x, p x ∧ ∀ y, p y → y = x

open Lean in
macro "∃! " xs:explicitBinders ", " b:term : term => expandExplicitBinders ``ExistsUnique xs b

/-- Pretty-printing for `ExistsUnique`, following the same pattern as pretty printing
    for `Exists`. -/
@[appUnexpander ExistsUnique] def unexpandExistsUnique : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => ∃! $xs:binderIdent*, $b) => `(∃! $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident => $b)                      => `(∃! $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b)               => `(∃! ($x:ident : $t), $b)
  | _                                               => throw ()

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
let ⟨_, _, hy⟩ := h; (hy _ py₁).trans (hy _ py₂).symm

/- exists, forall, exists unique congruences -/

alias Exists.imp ← exists_imp_exists

lemma exists_unique_congr {p q : α → Prop} (h : ∀ a, p a ↔ q a) : (∃! a, p a) ↔ ∃! a, q a :=
exists_congr fun _ => and_congr (h _) $ forall_congr' fun _ => imp_congr_left (h _)

/- decidable -/

namespace Decidable
  variable {p q : Prop}

  -- TODO: rec_on_true and rec_on_false

  alias byCases ← by_cases
  alias byContradiction ← by_contradiction
  alias not_not ← not_not_iff

end Decidable

section
  variable {p q : Prop}

  instance [Decidable p] [Decidable q] : Decidable (xor p q) :=
  if hp : p then
    if hq : q then isFalse (Or.rec (λ ⟨_, h⟩ => h hq : ¬(p ∧ ¬ q)) (λ ⟨_, h⟩ => h hp : ¬(q ∧ ¬ p)))
    else isTrue $ Or.inl ⟨hp, hq⟩
  else
    if hq : q then isTrue $ Or.inr ⟨hq, hp⟩
    else isFalse (Or.rec (λ ⟨h, _⟩ => hp h : ¬(p ∧ ¬ q)) (λ ⟨h, _⟩ => hq h : ¬(q ∧ ¬ p)))
end

def is_dec_eq {α : Sort u} (p : α → α → Bool) : Prop   := ∀ ⦃x y : α⦄, p x y = true → x = y
def is_dec_refl {α : Sort u} (p : α → α → Bool) : Prop := ∀ x, p x x = true

def decidable_eq_of_bool_pred {α : Sort u} {p : α → α → Bool} (h₁ : is_dec_eq p)
    (h₂ : is_dec_refl p) : DecidableEq α :=
λ (x y : α) =>
 if hp : p x y = true then isTrue (h₁ hp)
 else isFalse (λ hxy : x = y => absurd (h₂ y) (by rwa [hxy] at hp))

lemma decidable_eq_inl_refl {α : Sort u} [h : DecidableEq α] (a : α) : h a a = isTrue (Eq.refl a) :=
match (h a a) with
| isTrue _  => rfl
| isFalse n => absurd rfl n

lemma decidable_eq_inr_neg {α : Sort u} [h : DecidableEq α] {a b : α} :
    ∀ n : a ≠ b, h a b = isFalse n :=
λ n =>
match (h a b) with
| isTrue e   => absurd e n
| isFalse n₁ => proof_irrel n n₁ ▸ Eq.refl (isFalse n)

/- subsingleton -/

-- TODO: rec_subsingleton

lemma imp_of_if_pos {c t e : Prop} [Decidable c] (h : ite c t e) : c → t :=
by intro hc
   have hp : ite c t e = t := if_pos hc
   rwa [hp] at h

lemma imp_of_if_neg {c t e : Prop} [Decidable c] (h : ite c t e) : ¬c → e :=
by intro hnc
   have hn : ite c t e = e := if_neg hnc
   rwa [hn] at h

lemma if_ctx_congr {α : Sort u} {b c : Prop} [dec_b : Decidable b] [dec_c : Decidable c]
                   {x y u v : α}
                   (h_c : b ↔ c) (h_t : c → x = u) (h_e : ¬c → y = v) :
        ite b x y = ite c u v :=
match dec_b, dec_c with
| isFalse _,  isFalse h₂ => h_e h₂
| isTrue _,   isTrue h₂  => h_t h₂
| isFalse h₁, isTrue h₂  => absurd h₂ (Iff.mp (not_iff_not_of_iff h_c) h₁)
| isTrue h₁,  isFalse h₂ => absurd h₁ (Iff.mpr (not_iff_not_of_iff h_c) h₂)

lemma if_congr {α : Sort u} {b c : Prop} [dec_b : Decidable b] [dec_c : Decidable c]
               {x y u v : α}
               (h_c : b ↔ c) (h_t : x = u) (h_e : y = v) :
        ite b x y = ite c u v :=
@if_ctx_congr α b c dec_b dec_c x y u v h_c (λ _ => h_t) (λ _ => h_e)

lemma if_ctx_congr_prop {b c x y u v : Prop} [dec_b : Decidable b] [dec_c : Decidable c]
                      (h_c : b ↔ c) (h_t : c → (x ↔ u)) (h_e : ¬c → (y ↔ v)) :
        ite b x y ↔ ite c u v :=
match dec_b, dec_c with
| isFalse _,  isFalse h₂ => h_e h₂
| isTrue _,   isTrue h₂  => h_t h₂
| isFalse h₁, isTrue h₂  => absurd h₂ (Iff.mp (not_iff_not_of_iff h_c) h₁)
| isTrue h₁,  isFalse h₂ => absurd h₁ (Iff.mpr (not_iff_not_of_iff h_c) h₂)

lemma if_congr_prop {b c x y u v : Prop} [Decidable b] [Decidable c]
                    (h_c : b ↔ c) (h_t : x ↔ u) (h_e : y ↔ v) :
        ite b x y ↔ ite c u v :=
if_ctx_congr_prop h_c (λ _ => h_t) (λ _ => h_e)

lemma if_ctx_simp_congr_prop {b c x y u v : Prop} [dec_b : Decidable b]
                               (h_c : b ↔ c) (h_t : c → (x ↔ u)) (h_e : ¬c → (y ↔ v)) :
        ite b x y ↔ (@ite Prop c (decidable_of_decidable_of_iff h_c) u v) :=
@if_ctx_congr_prop b c x y u v dec_b (decidable_of_decidable_of_iff h_c) h_c h_t h_e

lemma if_simp_congr_prop {b c x y u v : Prop} [dec_b : Decidable b]
                           (h_c : b ↔ c) (h_t : x ↔ u) (h_e : y ↔ v) :
        ite b x y ↔ (@ite Prop c (decidable_of_decidable_of_iff h_c) u v) :=
@if_ctx_simp_congr_prop b c x y u v dec_b h_c (λ _ => h_t) (λ _ => h_e)

lemma dif_ctx_congr {α : Sort u} {b c : Prop} [dec_b : Decidable b] [dec_c : Decidable c]
                    {x : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}
                    (h_c : b ↔ c)
                    (h_t : ∀ (h : c),    x (Iff.mpr h_c h)                      = u h)
                    (h_e : ∀ (h : ¬c),   y (Iff.mpr (not_iff_not_of_iff h_c) h) = v h) :
        (@dite α b dec_b x y) = (@dite α c dec_c u v) :=
match dec_b, dec_c with
| isFalse _,  isFalse h₂ => h_e h₂
| isTrue _,   isTrue h₂  => h_t h₂
| isFalse h₁, isTrue h₂  => absurd h₂ (Iff.mp (not_iff_not_of_iff h_c) h₁)
| isTrue h₁,  isFalse h₂ => absurd h₁ (Iff.mpr (not_iff_not_of_iff h_c) h₂)

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
| isTrue h_c, _ => h_c
| isFalse _, h₂ => False.elim h₂

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

section relation

variable {α : Sort u} {β : Sort v} (r : β → β → Prop)

/-- Local notation for an arbitrary binary relation `r`. -/
local infix:50 " ≺ " => r

/-- A reflexive relation relates every element to itself. -/
def reflexive := ∀ x, x ≺ x

/-- A relation is symmetric if `x ≺ y` implies `y ≺ x`. -/
def symmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x

/-- A relation is transitive if `x ≺ y` and `y ≺ z` together imply `x ≺ z`. -/
def transitive := ∀ ⦃x y z⦄, x ≺ y → y ≺ z → x ≺ z

/-- An equivalance is a reflexive, symmetric, and transitive relation. -/
def equivalence := reflexive r ∧ symmetric r ∧ transitive r

/-- A relation is total if for all `x` and `y`, either `x ≺ y` or `y ≺ x`. -/
def total := ∀ x y, x ≺ y ∨ y ≺ x

lemma mk_equivalence (rfl : reflexive r) (symm : symmetric r) (trans : transitive r) :
  equivalence r :=
⟨rfl, symm, trans⟩

/-- Irreflexive means "not reflexive". -/
def irreflexive := ∀ x, ¬ x ≺ x

/-- A relation is antisymmetric if `x ≺ y` and `y ≺ x` together imply that `x = y`. -/
def anti_symmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x → x = y

/-- An empty relation does not relate any elements. -/
@[nolint unusedArguments]
def empty_relation := λ _ _ : α => False

/-- `q` is a subrelation of `r` if for all `x` and `y`, `q x y` implies `r x y` -/
def subrelation (q r : β → β → Prop) := ∀ ⦃x y⦄, q x y → r x y

/-- Given `f : α → β`, a relation on `β` induces a relation on `α`.-/
def inv_image (f : α → β) : α → α → Prop :=
λ a₁ a₂ => f a₁ ≺ f a₂

lemma inv_image.trans (f : α → β) (h : transitive r) : transitive (inv_image r f) :=
λ (a₁ a₂ a₃ : α) (h₁ : inv_image r f a₁ a₂) (h₂ : inv_image r f a₂ a₃) => h h₁ h₂

lemma inv_image.irreflexive (f : α → β) (h : irreflexive r) : irreflexive (inv_image r f) :=
λ (a : α) (h₁ : inv_image r f a a) => h (f a) h₁

end relation

section binary

variable {α : Type u} {β : Type v}
variable (f : α → α → α)
variable (inv : α → α)
variable (one : α)

/-- Local notation for `f`, high priority to avoid ambiguity with `HMul.hMul`. -/
local infix:70 (priority := high) " * " => f

/-- Local notation for `inv`, high priority to avoid ambiguity with `Inv.inv`. -/
local postfix:100 (priority := high) "⁻¹"  => inv

variable (g : α → α → α)

/-- Local notation for `g`, high priority to avoid ambiguity with `HAdd.hAdd`. -/
local infix:65 (priority := high) " + " => g

def commutative        := ∀ a b, a * b = b * a
def associative        := ∀ a b c, (a * b) * c = a * (b * c)
def left_identity      := ∀ a, one * a = a
def right_identity     := ∀ a, a * one = a
def RightInverse       := ∀ a, a * a⁻¹ = one
def left_cancelative   := ∀ a b c, a * b = a * c → b = c
def right_cancelative  := ∀ a b c, a * b = c * b → a = c
def left_distributive  := ∀ a b c, a * (b + c) = a * b + a * c
def right_distributive := ∀ a b c, (a + b) * c = a * c + b * c
def right_commutative (h : β → α → β) := ∀ b a₁ a₂, h (h b a₁) a₂ = h (h b a₂) a₁
def left_commutative  (h : α → β → β) := ∀ a₁ a₂ b, h a₁ (h a₂ b) = h a₂ (h a₁ b)

lemma left_comm : commutative f → associative f → left_commutative f :=
λ hcomm hassoc a b c => calc
  a*(b*c) = (a*b)*c  := Eq.symm (hassoc a b c)
        _ = (b*a)*c  := hcomm a b ▸ rfl
        _ = b*(a*c)  := hassoc b a c

lemma right_comm : commutative f → associative f → right_commutative f :=
λ hcomm hassoc a b c => calc
  (a*b)*c = a*(b*c) := hassoc a b c
        _ = a*(c*b) := hcomm b c ▸ rfl
        _ = (a*c)*b := Eq.symm (hassoc a c b)

end binary

namespace WellFounded

variable {α : Sort u} {C : α → Sort v} {r : α → α → Prop}

unsafe def fix'.impl (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) : C x :=
  F x fun y _ => impl hwf F y

@[implementedBy fix'.impl]
def fix' (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) : C x := hwf.fix F x

end WellFounded
