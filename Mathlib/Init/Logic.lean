/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/
import Std.Tactic.Ext
import Std.Tactic.Lint.Basic
import Std.Tactic.Relation.Rfl
import Std.Logic
import Std.WF
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Relation.Symm
import Mathlib.Mathport.Attributes
import Mathlib.Mathport.Rename
import Mathlib.Tactic.Relation.Trans
import Mathlib.Util.Imports
import Mathlib.Tactic.ProjectionNotation

set_option autoImplicit true


/- Implication -/

@[deprecated] def Implies (a b : Prop) := a → b

/-- Implication `→` is transitive. If `P → Q` and `Q → R` then `P → R`. -/
-- FIXME This should have `@[trans]`, but the `trans` attribute PR'd in #253 rejects it.
-- Note that it is still rejected after #857.
@[deprecated] theorem Implies.trans {p q r : Prop} (h₁ : p → q) (h₂ : q → r) :
    p → r := fun hp ↦ h₂ (h₁ hp)

/- Not -/

@[deprecated] def NonContradictory (a : Prop) : Prop := ¬¬a


/- Eq -/

alias proof_irrel := proofIrrel
alias congr_fun := congrFun
alias congr_arg := congrArg

@[deprecated] theorem trans_rel_left {α : Sort u} {a b c : α}
    (r : α → α → Prop) (h₁ : r a b) (h₂ : b = c) : r a c := h₂ ▸ h₁

@[deprecated] theorem trans_rel_right {α : Sort u} {a b c : α}
    (r : α → α → Prop) (h₁ : a = b) (h₂ : r b c) : r a c := h₁ ▸ h₂

theorem not_of_eq_false {p : Prop} (h : p = False) : ¬p := fun hp ↦ h ▸ hp

theorem cast_proof_irrel (h₁ h₂ : α = β) (a : α) : cast h₁ a = cast h₂ a := rfl

attribute [symm] Eq.symm

/- Ne -/

theorem Ne.def {α : Sort u} (a b : α) : (a ≠ b) = ¬ (a = b) := rfl

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

/- and -/

variable {a b c d : Prop}


/- or -/


/- xor -/

def Xor' (a b : Prop) := (a ∧ ¬ b) ∨ (b ∧ ¬ a)

/- iff -/


attribute [refl] Iff.refl
attribute [trans] Iff.trans
attribute [symm] Iff.symm

-- This is needed for `calc` to work with `iff`.
instance : Trans Iff Iff Iff where
  trans := fun p q ↦ p.trans q


alias ⟨not_of_not_not_not, _⟩ := not_not_not

-- FIXME
-- attribute [congr] not_congr

@[deprecated and_comm] theorem and_comm' (a b) : a ∧ b ↔ b ∧ a := and_comm

@[deprecated and_assoc] theorem and_assoc' (a b) : (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) := and_assoc



variable (p)

-- FIXME: remove _iff and add _eq for the lean 4 core versions
theorem and_true_iff : p ∧ True ↔ p := iff_of_eq (and_true _)
theorem true_and_iff : True ∧ p ↔ p := iff_of_eq (true_and _)
theorem and_false_iff : p ∧ False ↔ False := iff_of_eq (and_false _)
theorem false_and_iff : False ∧ p ↔ False := iff_of_eq (false_and _)




@[deprecated or_comm] theorem or_comm' (a b) : a ∨ b ↔ b ∨ a := or_comm

@[deprecated or_assoc] theorem or_assoc' (a b) : (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) := or_assoc



theorem true_or_iff : True ∨ p ↔ True := iff_of_eq (true_or _)
theorem or_true_iff : p ∨ True ↔ True := iff_of_eq (or_true _)
theorem false_or_iff : False ∨ p ↔ p := iff_of_eq (false_or _)
theorem or_false_iff : p ∨ False ↔ p := iff_of_eq (or_false _)

theorem not_or_of_not : ¬a → ¬b → ¬(a ∨ b) := fun h1 h2 ↦ not_or.2 ⟨h1, h2⟩

theorem iff_true_iff : (a ↔ True) ↔ a := iff_of_eq (iff_true _)
theorem true_iff_iff : (True ↔ a) ↔ a := iff_of_eq (true_iff _)

theorem iff_false_iff : (a ↔ False) ↔ ¬a := iff_of_eq (iff_false _)

theorem false_iff_iff : (False ↔ a) ↔ ¬a := iff_of_eq (false_iff _)

theorem iff_self_iff (a : Prop) : (a ↔ a) ↔ True := iff_of_eq (iff_self _)




-- TODO
-- attribute [intro] Exists.intro

/- exists unique -/

def ExistsUnique (p : α → Prop) := ∃ x, p x ∧ ∀ y, p y → y = x

open Lean TSyntax.Compat in
macro "∃!" xs:explicitBinders ", " b:term : term => expandExplicitBinders ``ExistsUnique xs b

/-- Pretty-printing for `ExistsUnique`, following the same pattern as pretty printing
    for `Exists`. -/
@[app_unexpander ExistsUnique] def unexpandExistsUnique : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident ↦ ∃! $xs:binderIdent*, $b) => `(∃! $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident ↦ $b)                      => `(∃! $x:ident, $b)
  | `($(_) fun ($x:ident : $t) ↦ $b)               => `(∃! ($x:ident : $t), $b)
  | _                                               => throw ()

-- @[intro] -- TODO
theorem ExistsUnique.intro {p : α → Prop} (w : α)
    (h₁ : p w) (h₂ : ∀ y, p y → y = w) : ∃! x, p x := ⟨w, h₁, h₂⟩

theorem ExistsUnique.elim {α : Sort u} {p : α → Prop} {b : Prop}
    (h₂ : ∃! x, p x) (h₁ : ∀ x, p x → (∀ y, p y → y = x) → b) : b :=
  Exists.elim h₂ (λ w hw => h₁ w (And.left hw) (And.right hw))

theorem exists_unique_of_exists_of_unique {α : Sort u} {p : α → Prop}
    (hex : ∃ x, p x) (hunique : ∀ y₁ y₂, p y₁ → p y₂ → y₁ = y₂) : ∃! x, p x :=
  Exists.elim hex (λ x px => ExistsUnique.intro x px (λ y (h : p y) => hunique y x h px))

theorem ExistsUnique.exists {p : α → Prop} : (∃! x, p x) → ∃ x, p x | ⟨x, h, _⟩ => ⟨x, h⟩

theorem ExistsUnique.unique {α : Sort u} {p : α → Prop}
    (h : ∃! x, p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂ :=
  let ⟨_, _, hy⟩ := h; (hy _ py₁).trans (hy _ py₂).symm

/- exists, forall, exists unique congruences -/

-- TODO
-- attribute [congr] forall_congr'
-- attribute [congr] exists_congr'


-- @[congr]
theorem exists_unique_congr {p q : α → Prop} (h : ∀ a, p a ↔ q a) : (∃! a, p a) ↔ ∃! a, q a :=
  exists_congr fun _ ↦ and_congr (h _) $ forall_congr' fun _ ↦ imp_congr_left (h _)

/- decidable -/


theorem decide_True' (h : Decidable True) : decide True = true := by simp

theorem decide_False' (h : Decidable False) : decide False = false := by simp

namespace Decidable

def recOn_true [h : Decidable p] {h₁ : p → Sort u} {h₂ : ¬p → Sort u}
    (h₃ : p) (h₄ : h₁ h₃) : Decidable.recOn h h₂ h₁ :=
  cast (by match h with | .isTrue _ => rfl) h₄

def recOn_false [h : Decidable p] {h₁ : p → Sort u} {h₂ : ¬p → Sort u} (h₃ : ¬p) (h₄ : h₂ h₃) :
    Decidable.recOn h h₂ h₁ :=
  cast (by match h with | .isFalse _ => rfl) h₄

alias by_cases := byCases
alias by_contradiction := byContradiction
alias not_not_iff := not_not

@[deprecated not_or] theorem not_or_iff_and_not (p q) [Decidable p] [Decidable q] :
    ¬(p ∨ q) ↔ ¬p ∧ ¬q := not_or

end Decidable


alias Or.decidable := instDecidableOr
alias And.decidable := instDecidableAnd
alias Not.decidable := instDecidableNot
alias Iff.decidable := instDecidableIff
alias decidableTrue := instDecidableTrue
alias decidableFalse := instDecidableFalse


instance [Decidable p] [Decidable q] : Decidable (Xor' p q) := inferInstanceAs (Decidable (Or ..))

def IsDecEq {α : Sort u} (p : α → α → Bool) : Prop := ∀ ⦃x y : α⦄, p x y = true → x = y
def IsDecRefl {α : Sort u} (p : α → α → Bool) : Prop := ∀ x, p x x = true

def decidableEq_of_bool_pred {α : Sort u} {p : α → α → Bool} (h₁ : IsDecEq p)
    (h₂ : IsDecRefl p) : DecidableEq α
  | x, y =>
    if hp : p x y = true then isTrue (h₁ hp)
    else isFalse (λ hxy : x = y => absurd (h₂ y) (by rwa [hxy] at hp))

theorem decidableEq_inl_refl {α : Sort u} [h : DecidableEq α] (a : α) :
    h a a = isTrue (Eq.refl a) :=
  match h a a with
  | isTrue _ => rfl

theorem decidableEq_inr_neg {α : Sort u} [h : DecidableEq α] {a b : α}
    (n : a ≠ b) : h a b = isFalse n :=
  match h a b with
  | isFalse _ => rfl


/- subsingleton -/

theorem rec_subsingleton {p : Prop} [h : Decidable p] {h₁ : p → Sort u} {h₂ : ¬p → Sort u}
    [h₃ : ∀ h : p, Subsingleton (h₁ h)] [h₄ : ∀ h : ¬p, Subsingleton (h₂ h)] :
    Subsingleton (Decidable.recOn h h₂ h₁) :=
  match h with
  | isTrue h => h₃ h
  | isFalse h => h₄ h

@[deprecated ite_self]
theorem if_t_t (c : Prop) [Decidable c] {α : Sort u} (t : α) : ite c t t = t := ite_self _

theorem imp_of_if_pos {c t e : Prop} [Decidable c] (h : ite c t e) (hc : c) : t :=
  by have := if_pos hc ▸ h; exact this

theorem imp_of_if_neg {c t e : Prop} [Decidable c] (h : ite c t e) (hnc : ¬c) : e :=
  by have := if_neg hnc ▸ h; exact this

theorem if_ctx_congr {α : Sort u} {b c : Prop} [dec_b : Decidable b] [dec_c : Decidable c]
    {x y u v : α} (h_c : b ↔ c) (h_t : c → x = u) (h_e : ¬c → y = v) : ite b x y = ite c u v :=
  match dec_b, dec_c with
  | isFalse _,  isFalse h₂ => h_e h₂
  | isTrue _,   isTrue h₂  => h_t h₂
  | isFalse h₁, isTrue h₂  => absurd h₂ (Iff.mp (not_congr h_c) h₁)
  | isTrue h₁,  isFalse h₂ => absurd h₁ (Iff.mpr (not_congr h_c) h₂)

theorem if_congr {α : Sort u} {b c : Prop} [Decidable b] [Decidable c]
    {x y u v : α} (h_c : b ↔ c) (h_t : x = u) (h_e : y = v) : ite b x y = ite c u v :=
  if_ctx_congr h_c (λ _ => h_t) (λ _ => h_e)

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
  if_ctx_congr_prop h_c (λ _ => h_t) (λ _ => h_e)

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
  if_ctx_simp_congr_prop h_c (λ _ => h_t) (λ _ => h_e)

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


/- Equalities for rewriting let-expressions -/
theorem let_value_eq {α : Sort u} {β : Sort v} {a₁ a₂ : α} (b : α → β)
    (h : a₁ = a₂) : (let x : α := a₁; b x) = (let x : α := a₂; b x) := congrArg b h

theorem let_value_heq {α : Sort v} {β : α → Sort u} {a₁ a₂ : α} (b : ∀ x : α, β x)
    (h : a₁ = a₂) : HEq (let x : α := a₁; b x) (let x : α := a₂; b x) := by cases h; rfl

theorem let_body_eq {α : Sort v} {β : α → Sort u} (a : α) {b₁ b₂ : ∀ x : α, β x}
    (h : ∀ x, b₁ x = b₂ x) : (let x : α := a; b₁ x) = (let x : α := a; b₂ x) := by exact h _ ▸ rfl

theorem let_eq {α : Sort v} {β : Sort u} {a₁ a₂ : α} {b₁ b₂ : α → β}
    (h₁ : a₁ = a₂) (h₂ : ∀ x, b₁ x = b₂ x) :
    (let x : α := a₁; b₁ x) = (let x : α := a₂; b₂ x) := by simp [h₁, h₂]

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

lemma Equivalence.symmetric {r : β → β → Prop} (h : Equivalence r) : Symmetric r := λ _ _ => h.symm

lemma Equivalence.transitive {r : β → β → Prop}(h : Equivalence r) : Transitive r :=
  λ _ _ _ => h.trans

/-- A relation is total if for all `x` and `y`, either `x ≺ y` or `y ≺ x`. -/
def Total := ∀ x y, x ≺ y ∨ y ≺ x


/-- Irreflexive means "not reflexive". -/
def Irreflexive := ∀ x, ¬ x ≺ x

/-- A relation is antisymmetric if `x ≺ y` and `y ≺ x` together imply that `x = y`. -/
def AntiSymmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x → x = y

/-- An empty relation does not relate any elements. -/
@[nolint unusedArguments]
def EmptyRelation := λ _ _ : α => False

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


attribute [pp_dot] Iff.mp Iff.mpr False.elim Eq.symm Eq.trans
