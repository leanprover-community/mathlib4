/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/
import Mathlib.Tactic.TypeStar
import Batteries.Tactic.Alias

/-!
# `ExistsUnique`

This file defines the `ExistsUnique` predicate, notated as `∃!`, and proves some of its
basic properties.
-/

variable {α : Sort*}

/-- For `p : α → Prop`, `ExistsUnique p` means that there exists a unique `x : α` with `p x`. -/
def ExistsUnique (p : α → Prop) := ∃ x, p x ∧ ∀ y, p y → y = x

namespace Mathlib.Notation
open Lean

/-- Checks to see that `xs` has only one binder. -/
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

theorem ExistsUnique.elim {p : α → Prop} {b : Prop}
    (h₂ : ∃! x, p x) (h₁ : ∀ x, p x → (∀ y, p y → y = x) → b) : b :=
  Exists.elim h₂ (fun w hw ↦ h₁ w (And.left hw) (And.right hw))

theorem existsUnique_of_exists_of_unique {p : α → Prop}
    (hex : ∃ x, p x) (hunique : ∀ y₁ y₂, p y₁ → p y₂ → y₁ = y₂) : ∃! x, p x :=
  Exists.elim hex (fun x px ↦ ExistsUnique.intro x px (fun y (h : p y) ↦ hunique y x h px))

theorem ExistsUnique.exists {p : α → Prop} : (∃! x, p x) → ∃ x, p x | ⟨x, h, _⟩ => ⟨x, h⟩

theorem ExistsUnique.unique {p : α → Prop}
    (h : ∃! x, p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂ :=
  let ⟨_, _, hy⟩ := h; (hy _ py₁).trans (hy _ py₂).symm

-- TODO
-- attribute [congr] forall_congr'
-- attribute [congr] exists_congr'

-- @[congr]
theorem existsUnique_congr {p q : α → Prop} (h : ∀ a, p a ↔ q a) : (∃! a, p a) ↔ ∃! a, q a :=
  exists_congr fun _ ↦ and_congr (h _) <| forall_congr' fun _ ↦ imp_congr_left (h _)

@[simp] theorem existsUnique_iff_exists [Subsingleton α] {p : α → Prop} :
    (∃! x, p x) ↔ ∃ x, p x :=
  ⟨fun h ↦ h.exists, Exists.imp fun x hx ↦ ⟨hx, fun y _ ↦ Subsingleton.elim y x⟩⟩

theorem existsUnique_const {b : Prop} (α : Sort*) [i : Nonempty α] [Subsingleton α] :
    (∃! _ : α, b) ↔ b := by simp

@[simp] theorem existsUnique_eq {a' : α} : ∃! a, a = a' := by
  simp only [eq_comm, ExistsUnique, and_self, forall_eq', exists_eq']

/-- The difference with `existsUnique_eq` is that the equality is reversed. -/
@[simp] theorem existsUnique_eq' {a' : α} : ∃! a, a' = a := by
  simp only [ExistsUnique, and_self, forall_eq', exists_eq']

theorem existsUnique_prop {p q : Prop} : (∃! _ : p, q) ↔ p ∧ q := by simp

@[simp] theorem existsUnique_false : ¬∃! _ : α, False := fun ⟨_, h, _⟩ ↦ h

theorem existsUnique_prop_of_true {p : Prop} {q : p → Prop} (h : p) : (∃! h' : p, q h') ↔ q h :=
  @existsUnique_const (q h) p ⟨h⟩ _

theorem ExistsUnique.elim₂ {p : α → Sort*} [∀ x, Subsingleton (p x)]
    {q : ∀ (x) (_ : p x), Prop} {b : Prop} (h₂ : ∃! x, ∃! h : p x, q x h)
    (h₁ : ∀ (x) (h : p x), q x h → (∀ (y) (hy : p y), q y hy → y = x) → b) : b := by
  simp only [existsUnique_iff_exists] at h₂
  apply h₂.elim
  exact fun x ⟨hxp, hxq⟩ H ↦ h₁ x hxp hxq fun y hyp hyq ↦ H y ⟨hyp, hyq⟩

theorem ExistsUnique.intro₂ {p : α → Sort*} [∀ x, Subsingleton (p x)]
    {q : ∀ (x : α) (_ : p x), Prop} (w : α) (hp : p w) (hq : q w hp)
    (H : ∀ (y) (hy : p y), q y hy → y = w) : ∃! x, ∃! hx : p x, q x hx := by
  simp only [existsUnique_iff_exists]
  exact ExistsUnique.intro w ⟨hp, hq⟩ fun y ⟨hyp, hyq⟩ ↦ H y hyp hyq

theorem ExistsUnique.exists₂ {p : α → Sort*} {q : ∀ (x : α) (_ : p x), Prop}
    (h : ∃! x, ∃! hx : p x, q x hx) : ∃ (x : _) (hx : p x), q x hx :=
  h.exists.imp fun _ hx ↦ hx.exists

theorem ExistsUnique.unique₂ {p : α → Sort*} [∀ x, Subsingleton (p x)]
    {q : ∀ (x : α) (_ : p x), Prop} (h : ∃! x, ∃! hx : p x, q x hx) {y₁ y₂ : α}
    (hpy₁ : p y₁) (hqy₁ : q y₁ hpy₁) (hpy₂ : p y₂) (hqy₂ : q y₂ hpy₂) : y₁ = y₂ := by
  simp only [existsUnique_iff_exists] at h
  exact h.unique ⟨hpy₁, hqy₁⟩ ⟨hpy₂, hqy₂⟩

/-- This invokes the two `Decidable` arguments $O(n)$ times. -/
instance List.decidableBExistsUnique {α : Type*} [DecidableEq α] (p : α → Prop) [DecidablePred p] :
    (l : List α) → Decidable (∃! x, x ∈ l ∧ p x)
  | [] => .isFalse <| by simp
  | x :: xs =>
    if hx : p x then
      decidable_of_iff (∀ y ∈ xs, p y → x = y) (⟨fun h ↦ ⟨x, by grind⟩,
        fun ⟨z, h⟩ y hy hp ↦ (h.2 x ⟨mem_cons_self, hx⟩).trans (by grind)⟩)
    else
      have := List.decidableBExistsUnique p xs
      decidable_of_iff (∃! x, x ∈ xs ∧ p x) (by grind)
