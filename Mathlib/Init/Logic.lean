/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/
import Mathlib.Tactic.Lemma
import Mathlib.Mathport.Attributes
import Mathlib.Mathport.Rename
import Mathlib.Tactic.Relation.Trans
import Mathlib.Tactic.ProjectionNotation
import Batteries.Tactic.Alias
import Batteries.Tactic.Lint.Misc
import Batteries.Logic -- Only needed for #align

set_option autoImplicit true

#align opt_param_eq optParam_eq

#align non_contradictory_intro not_not_intro

/- Eq -/

theorem not_of_eq_false {p : Prop} (h : p = False) : ¬p := fun hp ↦ h ▸ hp

theorem cast_proof_irrel (h₁ h₂ : α = β) (a : α) : cast h₁ a = cast h₂ a := rfl

attribute [symm] Eq.symm

/- Ne -/

attribute [symm] Ne.symm

/- HEq -/

alias eq_rec_heq := eqRec_heq

-- FIXME This is still rejected after #857
-- attribute [refl] HEq.refl
attribute [symm] HEq.symm
attribute [trans] HEq.trans
attribute [trans] heq_of_eq_of_heq

theorem heq_of_eq_rec_left {φ : α → Sort v} {a a' : α} {p₁ : φ a} {p₂ : φ a'} :
    (e : a = a') → (h₂ : Eq.rec (motive := fun a _ ↦ φ a) p₁ e = p₂) → HEq p₁ p₂
  | rfl, rfl => HEq.rfl

theorem heq_of_eq_rec_right {φ : α → Sort v} {a a' : α} {p₁ : φ a} {p₂ : φ a'} :
    (e : a' = a) → (h₂ : p₁ = Eq.rec (motive := fun a _ ↦ φ a) p₂ e) → HEq p₁ p₂
  | rfl, rfl => HEq.rfl

theorem of_heq_true {a : Prop} (h : HEq a True) : a := of_eq_true (eq_of_heq h)

theorem eq_rec_compose {α β φ : Sort u} :
    ∀ (p₁ : β = φ) (p₂ : α = β) (a : α),
      (Eq.recOn p₁ (Eq.recOn p₂ a : β) : φ) = Eq.recOn (Eq.trans p₂ p₁) a
  | rfl, rfl, _ => rfl

theorem heq_prop {P Q : Prop} (p : P) (q : Q) : HEq p q :=
  Subsingleton.helim (propext <| iff_of_true p q) _ _

/- and -/

variable {a b c d : Prop}

#align and.symm And.symm
#align and.swap And.symm

/- or -/

#align non_contradictory_em not_not_em
#align or.symm Or.symm
#align or.swap Or.symm

/- xor -/

def Xor' (a b : Prop) := (a ∧ ¬ b) ∨ (b ∧ ¬ a)
#align xor Xor'

/- iff -/

#align iff.mp Iff.mp
#align iff.elim_left Iff.mp
#align iff.mpr Iff.mpr
#align iff.elim_right Iff.mpr

attribute [refl] Iff.refl
attribute [trans] Iff.trans
attribute [symm] Iff.symm

-- This is needed for `calc` to work with `iff`.
instance : Trans Iff Iff Iff where
  trans := fun p q ↦ p.trans q

#align not_congr not_congr
#align not_iff_not_of_iff not_congr
#align not_non_contradictory_iff_absurd not_not_not

alias ⟨not_of_not_not_not, _⟩ := not_not_not

-- FIXME
-- attribute [congr] not_congr

#align and.comm and_comm
#align and_comm and_comm

#align and_assoc and_assoc
#align and.assoc and_assoc

#align and.left_comm and_left_comm

#align and_iff_left and_iff_leftₓ -- reorder implicits

variable (p)

-- FIXME: remove _iff and add _eq for the lean 4 core versions
theorem and_true_iff : p ∧ True ↔ p := iff_of_eq (and_true _)
#align and_true and_true_iff
theorem true_and_iff : True ∧ p ↔ p := iff_of_eq (true_and _)
#align true_and true_and_iff
theorem and_false_iff : p ∧ False ↔ False := iff_of_eq (and_false _)
#align and_false and_false_iff
theorem false_and_iff : False ∧ p ↔ False := iff_of_eq (false_and _)
#align false_and false_and_iff
#align not_and_self not_and_self_iff
#align and_not_self and_not_self_iff
#align and_self and_self_iff

#align or.imp Or.impₓ -- reorder implicits

#align and.elim And.elimₓ
#align iff.elim Iff.elimₓ
#align imp_congr imp_congrₓ
#align imp_congr_ctx imp_congr_ctxₓ
#align imp_congr_right imp_congr_rightₓ

#align eq_true_intro eq_true
#align eq_false_intro eq_false

#align or.comm or_comm
#align or_comm or_comm

#align or.assoc or_assoc
#align or_assoc or_assoc

#align or_left_comm or_left_comm
#align or.left_comm or_left_comm

#align or_iff_left_of_imp or_iff_left_of_impₓ -- reorder implicits

theorem true_or_iff : True ∨ p ↔ True := iff_of_eq (true_or _)
#align true_or true_or_iff
theorem or_true_iff : p ∨ True ↔ True := iff_of_eq (or_true _)
#align or_true or_true_iff
theorem false_or_iff : False ∨ p ↔ p := iff_of_eq (false_or _)
#align false_or false_or_iff
theorem or_false_iff : p ∨ False ↔ p := iff_of_eq (or_false _)
#align or_false or_false_iff
#align or_self or_self_iff

theorem not_or_of_not : ¬a → ¬b → ¬(a ∨ b) := fun h1 h2 ↦ not_or.2 ⟨h1, h2⟩
#align not_or not_or_of_not

theorem iff_true_iff : (a ↔ True) ↔ a := iff_of_eq (iff_true _)
#align iff_true iff_true_iff
theorem true_iff_iff : (True ↔ a) ↔ a := iff_of_eq (true_iff _)
#align true_iff true_iff_iff

theorem iff_false_iff : (a ↔ False) ↔ ¬a := iff_of_eq (iff_false _)
#align iff_false iff_false_iff

theorem false_iff_iff : (False ↔ a) ↔ ¬a := iff_of_eq (false_iff _)
#align false_iff false_iff_iff

theorem iff_self_iff (a : Prop) : (a ↔ a) ↔ True := iff_of_eq (iff_self _)
#align iff_self iff_self_iff

#align iff_congr iff_congrₓ -- reorder implicits

#align implies_true_iff imp_true_iff
#align false_implies_iff false_imp_iff
#align true_implies_iff true_imp_iff

#align Exists Exists -- otherwise it would get the name ExistsCat

-- TODO
-- attribute [intro] Exists.intro

/- exists unique -/

def ExistsUnique (p : α → Prop) := ∃ x, p x ∧ ∀ y, p y → y = x

namespace Mathlib.Notation
open Lean

/--
Checks to see that `xs` has only one binder.
-/
def isExplicitBinderSingular (xs : TSyntax ``explicitBinders) : Bool :=
  match xs with
  | `(explicitBinders| $_:binderIdent $[: $_]?) => true
  | `(explicitBinders| ($_:binderIdent : $_)) => true
  | _ => false

open TSyntax.Compat in
/--
`∃! x : α, p x` means that there exists a unique `x` in `α` such that `p x`.
This is notation for `ExistsUnique (fun (x : α) ↦ p x)`.

This notation does not allow multiple binders like `∃! (x : α) (y : β), p x y`
as a shorthand for `∃! (x : α), ∃! (y : β), p x y` since it is liable to be misunderstood.
Often, the intended meaning is instead `∃! q : α × β, p q.1 q.2`.
-/
macro "∃!" xs:explicitBinders ", " b:term : term => do
  if !isExplicitBinderSingular xs then
    Macro.throwErrorAt xs "\
      The `ExistsUnique` notation should not be used with more than one binder.\n\
      \n\
      The reason for this is that `∃! (x : α), ∃! (y : β), p x y` has a completely different \
      meaning from `∃! q : α × β, p q.1 q.2`. \
      To prevent confusion, this notation requires that you be explicit \
      and use one with the correct interpretation."
  expandExplicitBinders ``ExistsUnique xs b

/--
Pretty-printing for `ExistsUnique`, following the same pattern as pretty printing for `Exists`.
However, it does *not* merge binders.
-/
@[app_unexpander ExistsUnique] def unexpandExistsUnique : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident ↦ $b)                      => `(∃! $x:ident, $b)
  | `($(_) fun ($x:ident : $t) ↦ $b)               => `(∃! $x:ident : $t, $b)
  | _                                               => throw ()

/--
`∃! x ∈ s, p x` means `∃! x, x ∈ s ∧ p x`, which is to say that there exists a unique `x ∈ s`
such that `p x`.
Similarly, notations such as `∃! x ≤ n, p n` are supported,
using any relation defined using the `binder_predicate` command.
-/
syntax "∃! " binderIdent binderPred ", " term : term

macro_rules
  | `(∃! $x:ident $p:binderPred, $b) => `(∃! $x:ident, satisfies_binder_pred% $x $p ∧ $b)
  | `(∃! _ $p:binderPred, $b) => `(∃! x, satisfies_binder_pred% x $p ∧ $b)

end Mathlib.Notation

-- @[intro] -- TODO
theorem ExistsUnique.intro {p : α → Prop} (w : α)
    (h₁ : p w) (h₂ : ∀ y, p y → y = w) : ∃! x, p x := ⟨w, h₁, h₂⟩

theorem ExistsUnique.elim {α : Sort u} {p : α → Prop} {b : Prop}
    (h₂ : ∃! x, p x) (h₁ : ∀ x, p x → (∀ y, p y → y = x) → b) : b :=
  Exists.elim h₂ (fun w hw ↦ h₁ w (And.left hw) (And.right hw))

theorem exists_unique_of_exists_of_unique {α : Sort u} {p : α → Prop}
    (hex : ∃ x, p x) (hunique : ∀ y₁ y₂, p y₁ → p y₂ → y₁ = y₂) : ∃! x, p x :=
  Exists.elim hex (fun x px ↦ ExistsUnique.intro x px (fun y (h : p y) ↦ hunique y x h px))

theorem ExistsUnique.exists {p : α → Prop} : (∃! x, p x) → ∃ x, p x | ⟨x, h, _⟩ => ⟨x, h⟩
#align exists_of_exists_unique ExistsUnique.exists
#align exists_unique.exists ExistsUnique.exists

theorem ExistsUnique.unique {α : Sort u} {p : α → Prop}
    (h : ∃! x, p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂ :=
  let ⟨_, _, hy⟩ := h; (hy _ py₁).trans (hy _ py₂).symm
#align unique_of_exists_unique ExistsUnique.unique
#align exists_unique.unique ExistsUnique.unique

/- exists, forall, exists unique congruences -/

-- TODO
-- attribute [congr] forall_congr'
-- attribute [congr] exists_congr'
#align forall_congr forall_congr'

#align Exists.imp Exists.imp
#align exists_imp_exists Exists.imp

-- @[congr]
theorem exists_unique_congr {p q : α → Prop} (h : ∀ a, p a ↔ q a) : (∃! a, p a) ↔ ∃! a, q a :=
  exists_congr fun _ ↦ and_congr (h _) <| forall_congr' fun _ ↦ imp_congr_left (h _)

/- decidable -/

#align decidable.to_bool Decidable.decide

theorem decide_True' (h : Decidable True) : decide True = true := by simp
#align to_bool_true_eq_tt decide_True'

theorem decide_False' (h : Decidable False) : decide False = false := by simp
#align to_bool_false_eq_ff decide_False'

namespace Decidable

def recOn_true [h : Decidable p] {h₁ : p → Sort u} {h₂ : ¬p → Sort u}
    (h₃ : p) (h₄ : h₁ h₃) : Decidable.recOn h h₂ h₁ :=
  cast (by match h with | .isTrue _ => rfl) h₄
#align decidable.rec_on_true Decidable.recOn_true

def recOn_false [h : Decidable p] {h₁ : p → Sort u} {h₂ : ¬p → Sort u} (h₃ : ¬p) (h₄ : h₂ h₃) :
    Decidable.recOn h h₂ h₁ :=
  cast (by match h with | .isFalse _ => rfl) h₄
#align decidable.rec_on_false Decidable.recOn_false

alias by_cases := byCases
alias by_contradiction := byContradiction
alias not_not_iff := not_not

end Decidable

#align decidable_of_decidable_of_iff decidable_of_decidable_of_iff
#align decidable_of_decidable_of_eq decidable_of_decidable_of_eq
#align or.by_cases Or.by_cases

alias Or.decidable := instDecidableOr
alias And.decidable := instDecidableAnd
alias Not.decidable := instDecidableNot
alias Iff.decidable := instDecidableIff
alias decidableTrue := instDecidableTrue
alias decidableFalse := instDecidableFalse

#align decidable.true decidableTrue
#align decidable.false decidableFalse
#align or.decidable Or.decidable
#align and.decidable And.decidable
#align not.decidable Not.decidable
#align iff.decidable Iff.decidable

instance [Decidable p] [Decidable q] : Decidable (Xor' p q) := inferInstanceAs (Decidable (Or ..))

def IsDecEq {α : Sort u} (p : α → α → Bool) : Prop := ∀ ⦃x y : α⦄, p x y = true → x = y
def IsDecRefl {α : Sort u} (p : α → α → Bool) : Prop := ∀ x, p x x = true

def decidableEq_of_bool_pred {α : Sort u} {p : α → α → Bool} (h₁ : IsDecEq p)
    (h₂ : IsDecRefl p) : DecidableEq α
  | x, y =>
    if hp : p x y = true then isTrue (h₁ hp)
    else isFalse (fun hxy : x = y ↦ absurd (h₂ y) (by rwa [hxy] at hp))
#align decidable_eq_of_bool_pred decidableEq_of_bool_pred

theorem decidableEq_inl_refl {α : Sort u} [h : DecidableEq α] (a : α) :
    h a a = isTrue (Eq.refl a) :=
  match h a a with
  | isTrue _ => rfl

theorem decidableEq_inr_neg {α : Sort u} [h : DecidableEq α] {a b : α}
    (n : a ≠ b) : h a b = isFalse n :=
  match h a b with
  | isFalse _ => rfl

#align inhabited.default Inhabited.default
#align arbitrary Inhabited.default
#align nonempty_of_inhabited instNonemptyOfInhabited

/- subsingleton -/

theorem rec_subsingleton {p : Prop} [h : Decidable p] {h₁ : p → Sort u} {h₂ : ¬p → Sort u}
    [h₃ : ∀ h : p, Subsingleton (h₁ h)] [h₄ : ∀ h : ¬p, Subsingleton (h₂ h)] :
    Subsingleton (Decidable.recOn h h₂ h₁) :=
  match h with
  | isTrue h => h₃ h
  | isFalse h => h₄ h

theorem imp_of_if_pos {c t e : Prop} [Decidable c] (h : ite c t e) (hc : c) : t :=
  (if_pos hc ▸ h :)
#align implies_of_if_pos imp_of_if_pos

theorem imp_of_if_neg {c t e : Prop} [Decidable c] (h : ite c t e) (hnc : ¬c) : e :=
  (if_neg hnc ▸ h :)
#align implies_of_if_neg imp_of_if_neg

theorem if_ctx_congr {α : Sort u} {b c : Prop} [dec_b : Decidable b] [dec_c : Decidable c]
    {x y u v : α} (h_c : b ↔ c) (h_t : c → x = u) (h_e : ¬c → y = v) : ite b x y = ite c u v :=
  match dec_b, dec_c with
  | isFalse _,  isFalse h₂ => h_e h₂
  | isTrue _,   isTrue h₂  => h_t h₂
  | isFalse h₁, isTrue h₂  => absurd h₂ (Iff.mp (not_congr h_c) h₁)
  | isTrue h₁,  isFalse h₂ => absurd h₁ (Iff.mpr (not_congr h_c) h₂)

theorem if_congr {α : Sort u} {b c : Prop} [Decidable b] [Decidable c]
    {x y u v : α} (h_c : b ↔ c) (h_t : x = u) (h_e : y = v) : ite b x y = ite c u v :=
  if_ctx_congr h_c (fun _ ↦ h_t) (fun _ ↦ h_e)

theorem if_ctx_congr_prop {b c x y u v : Prop} [dec_b : Decidable b] [dec_c : Decidable c]
    (h_c : b ↔ c) (h_t : c → (x ↔ u)) (h_e : ¬c → (y ↔ v)) : ite b x y ↔ ite c u v :=
  match dec_b, dec_c with
  | isFalse _,  isFalse h₂ => h_e h₂
  | isTrue _,   isTrue h₂  => h_t h₂
  | isFalse h₁, isTrue h₂  => absurd h₂ (Iff.mp (not_congr h_c) h₁)
  | isTrue h₁,  isFalse h₂ => absurd h₁ (Iff.mpr (not_congr h_c) h₂)

-- @[congr]
theorem if_congr_prop {b c x y u v : Prop} [Decidable b] [Decidable c] (h_c : b ↔ c) (h_t : x ↔ u)
    (h_e : y ↔ v) : ite b x y ↔ ite c u v :=
  if_ctx_congr_prop h_c (fun _ ↦ h_t) (fun _ ↦ h_e)

theorem if_ctx_simp_congr_prop {b c x y u v : Prop} [Decidable b] (h_c : b ↔ c) (h_t : c → (x ↔ u))
    -- FIXME: after https://github.com/leanprover/lean4/issues/1867 is fixed,
    -- this should be changed back to:
    -- (h_e : ¬c → (y ↔ v)) : ite b x y ↔ ite c (h := decidable_of_decidable_of_iff h_c) u v :=
    (h_e : ¬c → (y ↔ v)) : ite b x y ↔ @ite _ c (decidable_of_decidable_of_iff h_c) u v :=
  if_ctx_congr_prop (dec_c := decidable_of_decidable_of_iff h_c) h_c h_t h_e

theorem if_simp_congr_prop {b c x y u v : Prop} [Decidable b] (h_c : b ↔ c) (h_t : x ↔ u)
    -- FIXME: after https://github.com/leanprover/lean4/issues/1867 is fixed,
    -- this should be changed back to:
    -- (h_e : y ↔ v) : ite b x y ↔ (ite c (h := decidable_of_decidable_of_iff h_c) u v) :=
    (h_e : y ↔ v) : ite b x y ↔ (@ite _ c (decidable_of_decidable_of_iff h_c) u v) :=
  if_ctx_simp_congr_prop h_c (fun _ ↦ h_t) (fun _ ↦ h_e)

-- @[congr]
theorem dif_ctx_congr {α : Sort u} {b c : Prop} [dec_b : Decidable b] [dec_c : Decidable c]
    {x : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}
    (h_c : b ↔ c) (h_t : ∀ h : c, x (Iff.mpr h_c h) = u h)
    (h_e : ∀ h : ¬c, y (Iff.mpr (not_congr h_c) h) = v h) :
    @dite α b dec_b x y = @dite α c dec_c u v :=
  match dec_b, dec_c with
  | isFalse _, isFalse h₂ => h_e h₂
  | isTrue _, isTrue h₂ => h_t h₂
  | isFalse h₁, isTrue h₂ => absurd h₂ (Iff.mp (not_congr h_c) h₁)
  | isTrue h₁, isFalse h₂ => absurd h₁ (Iff.mpr (not_congr h_c) h₂)

theorem dif_ctx_simp_congr {α : Sort u} {b c : Prop} [Decidable b]
    {x : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}
    (h_c : b ↔ c) (h_t : ∀ h : c, x (Iff.mpr h_c h) = u h)
    (h_e : ∀ h : ¬c, y (Iff.mpr (not_congr h_c) h) = v h) :
    -- FIXME: after https://github.com/leanprover/lean4/issues/1867 is fixed,
    -- this should be changed back to:
    -- dite b x y = dite c (h := decidable_of_decidable_of_iff h_c) u v :=
    dite b x y = @dite _ c (decidable_of_decidable_of_iff h_c) u v :=
  dif_ctx_congr (dec_c := decidable_of_decidable_of_iff h_c) h_c h_t h_e

def AsTrue (c : Prop) [Decidable c] : Prop := if c then True else False

def AsFalse (c : Prop) [Decidable c] : Prop := if c then False else True

theorem AsTrue.get {c : Prop} [h₁ : Decidable c] (_ : AsTrue c) : c :=
  match h₁ with
  | isTrue h_c => h_c
#align of_as_true AsTrue.get

#align ulift ULift
#align ulift.up ULift.up
#align ulift.down ULift.down
#align plift PLift
#align plift.up PLift.up
#align plift.down PLift.down

/- Equalities for rewriting let-expressions -/
theorem let_value_eq {α : Sort u} {β : Sort v} {a₁ a₂ : α} (b : α → β)
    (h : a₁ = a₂) : (let x : α := a₁; b x) = (let x : α := a₂; b x) := congrArg b h

theorem let_value_heq {α : Sort v} {β : α → Sort u} {a₁ a₂ : α} (b : ∀ x : α, β x)
    (h : a₁ = a₂) : HEq (let x : α := a₁; b x) (let x : α := a₂; b x) := by cases h; rfl
#align let_value_heq let_value_heq -- FIXME: mathport thinks this is a dubious translation

theorem let_body_eq {α : Sort v} {β : α → Sort u} (a : α) {b₁ b₂ : ∀ x : α, β x}
    (h : ∀ x, b₁ x = b₂ x) : (let x : α := a; b₁ x) = (let x : α := a; b₂ x) := by exact h _ ▸ rfl
#align let_value_eq let_value_eq -- FIXME: mathport thinks this is a dubious translation

theorem let_eq {α : Sort v} {β : Sort u} {a₁ a₂ : α} {b₁ b₂ : α → β}
    (h₁ : a₁ = a₂) (h₂ : ∀ x, b₁ x = b₂ x) :
    (let x : α := a₁; b₁ x) = (let x : α := a₂; b₂ x) := by simp [h₁, h₂]
#align let_eq let_eq -- FIXME: mathport thinks this is a dubious translation

section Relation

variable {α : Sort u} {β : Sort v} (r : β → β → Prop)

/-- Local notation for an arbitrary binary relation `r`. -/
local infix:50 " ≺ " => r

/-- A reflexive relation relates every element to itself. -/
def Reflexive := ∀ x, x ≺ x

/-- A relation is symmetric if `x ≺ y` implies `y ≺ x`. -/
def Symmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x

/-- A relation is transitive if `x ≺ y` and `y ≺ z` together imply `x ≺ z`. -/
def Transitive := ∀ ⦃x y z⦄, x ≺ y → y ≺ z → x ≺ z

lemma Equivalence.reflexive {r : β → β → Prop} (h : Equivalence r) : Reflexive r := h.refl

lemma Equivalence.symmetric {r : β → β → Prop} (h : Equivalence r) : Symmetric r := fun _ _ ↦ h.symm

lemma Equivalence.transitive {r : β → β → Prop} (h : Equivalence r) : Transitive r :=
  fun _ _ _ ↦ h.trans

/-- A relation is total if for all `x` and `y`, either `x ≺ y` or `y ≺ x`. -/
def Total := ∀ x y, x ≺ y ∨ y ≺ x

#align mk_equivalence Equivalence.mk

/-- Irreflexive means "not reflexive". -/
def Irreflexive := ∀ x, ¬ x ≺ x

/-- A relation is antisymmetric if `x ≺ y` and `y ≺ x` together imply that `x = y`. -/
def AntiSymmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x → x = y

/-- An empty relation does not relate any elements. -/
@[nolint unusedArguments]
def EmptyRelation := fun _ _ : α ↦ False

theorem InvImage.trans (f : α → β) (h : Transitive r) : Transitive (InvImage r f) :=
  fun (a₁ a₂ a₃ : α) (h₁ : InvImage r f a₁ a₂) (h₂ : InvImage r f a₂ a₃) ↦ h h₁ h₂

theorem InvImage.irreflexive (f : α → β) (h : Irreflexive r) : Irreflexive (InvImage r f) :=
  fun (a : α) (h₁ : InvImage r f a a) ↦ h (f a) h₁

end Relation

section Binary

variable {α : Type u} {β : Type v} (f : α → α → α) (inv : α → α) (one : α)

/-- Local notation for `f`, high priority to avoid ambiguity with `HMul.hMul`. -/
local infix:70 (priority := high) " * " => f

/-- Local notation for `inv`, high priority to avoid ambiguity with `Inv.inv`. -/
local postfix:100 (priority := high) "⁻¹" => inv

variable (g : α → α → α)

/-- Local notation for `g`, high priority to avoid ambiguity with `HAdd.hAdd`. -/
local infix:65 (priority := high) " + " => g

def Commutative       := ∀ a b, a * b = b * a
def Associative       := ∀ a b c, (a * b) * c = a * (b * c)
def LeftIdentity      := ∀ a, one * a = a
def RightIdentity     := ∀ a, a * one = a
def RightInverse      := ∀ a, a * a⁻¹ = one
def LeftCancelative   := ∀ a b c, a * b = a * c → b = c
def RightCancelative  := ∀ a b c, a * b = c * b → a = c
def LeftDistributive  := ∀ a b c, a * (b + c) = a * b + a * c
def RightDistributive := ∀ a b c, (a + b) * c = a * c + b * c
def RightCommutative (h : β → α → β) := ∀ b a₁ a₂, h (h b a₁) a₂ = h (h b a₂) a₁
def LeftCommutative  (h : α → β → β) := ∀ a₁ a₂ b, h a₁ (h a₂ b) = h a₂ (h a₁ b)

theorem left_comm : Commutative f → Associative f → LeftCommutative f :=
  fun hcomm hassoc a b c ↦
    calc  a*(b*c)
      _ = (a*b)*c := Eq.symm (hassoc a b c)
      _ = (b*a)*c := hcomm a b ▸ rfl
      _ = b*(a*c) := hassoc b a c

theorem right_comm : Commutative f → Associative f → RightCommutative f :=
  fun hcomm hassoc a b c ↦
    calc  (a*b)*c
      _ = a*(b*c) := hassoc a b c
      _ = a*(c*b) := hcomm b c ▸ rfl
      _ = (a*c)*b := Eq.symm (hassoc a c b)

end Binary

#align not.elim Not.elim
#align not.imp Not.imp
#align not_not_of_not_imp not_not_of_not_imp
#align not_of_not_imp not_of_not_imp
#align imp_not_self imp_not_self
#align iff_def iff_def
#align iff_def' iff_def'
#align iff_of_eq iff_of_eq
#align iff_iff_eq iff_iff_eq
#align eq_iff_iff eq_iff_iff
#align iff_of_true iff_of_true
#align iff_of_false iff_of_false
#align iff_true_left iff_true_left
#align iff_true_right iff_true_right
#align iff_false_left iff_false_left
#align iff_false_right iff_false_right
#align imp_intro imp_intro
#align imp_imp_imp imp_imp_imp
#align imp_true_iff imp_true_iff
#align imp_self imp_self
#align imp_false imp_false
#align imp_not_comm imp_not_comm
#align and.imp_left And.imp_left
#align and.imp_right And.imp_right
#align and_congr_left' and_congr_left'
#align and_rotate and_rotate
#align and_and_and_comm and_and_and_comm
#align and_iff_left_of_imp and_iff_left_of_imp
#align and_iff_right_of_imp and_iff_right_of_imp
#align and_iff_left_iff_imp and_iff_left_iff_imp
#align and_iff_right_iff_imp and_iff_right_iff_imp
#align iff_self_and iff_self_and
#align iff_and_self iff_and_self
#align and_self_left and_self_left
#align and_self_right and_self_right
#align not_and_of_not_left not_and_of_not_left
#align not_and_of_not_right not_and_of_not_right
#align and_not_self_iff and_not_self_iff
#align not_and_self_iff not_and_self_iff
#align or_or_or_comm or_or_or_comm
#align or_or_distrib_left or_or_distrib_left
#align or_or_distrib_right or_or_distrib_right
#align or_rotate or_rotate
#align or_iff_left_iff_imp or_iff_left_iff_imp
#align or_iff_right_iff_imp or_iff_right_iff_imp
#align or_iff_right or_iff_right
#align not_imp_of_and_not not_imp_of_and_not
#align and_imp and_imp
#align not_and not_and
#align not_and' not_and'
#align not_and_of_not_or_not not_and_of_not_or_not
#align or_self_left or_self_left
#align or_self_right or_self_right
#align forall_imp forall_imp
#align forall₂_congr forall₂_congr
#align exists₂_congr exists₂_congr
#align forall₃_congr forall₃_congr
#align exists₃_congr exists₃_congr
#align forall₄_congr forall₄_congr
#align exists₄_congr exists₄_congr
#align forall₅_congr forall₅_congr
#align exists₅_congr exists₅_congr
#align not_exists not_exists
#align exists_false exists_false
#align forall_const forall_const
#align not_forall_of_exists_not not_forall_of_exists_not
#align forall_eq forall_eq
#align forall_eq' forall_eq'
#align exists_eq exists_eq
#align exists_eq' exists_eq'
#align exists_eq_left exists_eq_left
#align exists_eq_right exists_eq_right
#align exists_eq_left' exists_eq_left'
#align forall_eq_or_imp forall_eq_or_imp
#align exists_eq_right_right exists_eq_right_right
#align exists_eq_right_right' exists_eq_right_right'
#align exists_prop exists_prop
#align exists_apply_eq_apply exists_apply_eq_apply
#align forall_prop_of_true forall_prop_of_true
#align decidable.not_not Decidable.not_not
#align decidable.of_not_imp Decidable.of_not_imp
#align decidable.not_imp_symm Decidable.not_imp_symm
#align decidable.not_imp_comm Decidable.not_imp_comm
#align decidable.not_imp_self Decidable.not_imp_self
#align decidable.or_iff_not_imp_left Decidable.or_iff_not_imp_left
#align decidable.not_imp_not Decidable.not_imp_not
#align decidable.not_or_of_imp Decidable.not_or_of_imp
#align decidable.imp_iff_not_or Decidable.imp_iff_not_or
#align decidable.not_imp Decidable.not_imp_iff_and_not
#align decidable.peirce Decidable.peirce
#align peirce' peirce'
#align decidable.not_iff_not Decidable.not_iff_not
#align decidable.not_iff_comm Decidable.not_iff_comm
#align decidable.not_iff Decidable.not_iff
#align decidable.iff_not_comm Decidable.iff_not_comm
#align decidable.iff_iff_and_or_not_and_not Decidable.iff_iff_and_or_not_and_not
#align decidable.iff_iff_not_or_and_or_not Decidable.iff_iff_not_or_and_or_not
#align decidable.not_and_not_right Decidable.not_and_not_right
#align decidable.or_iff_not_and_not Decidable.or_iff_not_and_not
#align decidable.and_iff_not_or_not Decidable.and_iff_not_or_not
#align decidable.imp_iff_right_iff Decidable.imp_iff_right_iff
#align decidable.and_or_imp Decidable.and_or_imp
#align heq_iff_eq heq_iff_eq
#align proof_irrel_heq proof_irrel_heq
#align eq_rec_constant eq_rec_constant
#align ne_of_mem_of_not_mem ne_of_mem_of_not_mem
#align ne_of_mem_of_not_mem' ne_of_mem_of_not_mem'
#align apply_dite apply_dite
#align apply_ite apply_ite
#align dite_not dite_not
#align ite_not ite_not
#align empty.elim Empty.elim
#align pempty.elim PEmpty.elim
#align not_nonempty_pempty not_nonempty_pempty
#align eq_iff_true_of_subsingleton eq_iff_true_of_subsingleton
#align subsingleton_of_forall_eq subsingleton_of_forall_eq
#align subsingleton_iff_forall_eq subsingleton_iff_forall_eq
#align false_ne_true false_ne_true
#align ne_comm ne_comm
