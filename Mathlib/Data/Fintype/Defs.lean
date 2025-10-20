/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finite.Defs

/-!
# Finite types

This file defines a typeclass to state that a type is finite.

## Main declarations

* `Fintype α`:  Typeclass saying that a type is finite. It takes as fields a `Finset` and a proof
  that all terms of type `α` are in it.
* `Finset.univ`: The finset of all elements of a fintype.

See `Data.Fintype.Basic` for elementary results,
`Data.Fintype.Card` for the cardinality of a fintype,
the equivalence with `Fin (Fintype.card α)`, and pigeonhole principles.

## Instances

Instances for `Fintype` for
* `{x // p x}` are in this file as `Fintype.subtype`
* `Option α` are in `Data.Fintype.Option`
* `α × β` are in `Data.Fintype.Prod`
* `α ⊕ β` are in `Data.Fintype.Sum`
* `Σ (a : α), β a` are in `Data.Fintype.Sigma`

These files also contain appropriate `Infinite` instances for these types.

`Infinite` instances for `ℕ`, `ℤ`, `Multiset α`, and `List α` are in `Data.Fintype.Lattice`.
-/

assert_not_exists Monoid

open Function

open Nat

universe u v

variable {α β γ : Type*}

/-- `Fintype α` means that `α` is finite, i.e. there are only
  finitely many distinct elements of type `α`. The evidence of this
  is a finset `elems` (a list up to permutation without duplicates),
  together with a proof that everything of type `α` is in the list. -/
class Fintype (α : Type*) where
  /-- The `Finset` containing all elements of a `Fintype` -/
  elems : Finset α
  /-- A proof that `elems` contains every element of the type -/
  complete : ∀ x : α, x ∈ elems

/-! ### Preparatory lemmas -/

namespace Finset

theorem nodup_map_iff_injOn {f : α → β} {s : Finset α} :
    (Multiset.map f s.val).Nodup ↔ Set.InjOn f s := by
  simp [Multiset.nodup_map_iff_inj_on s.nodup, Set.InjOn]

end Finset

namespace List

variable [DecidableEq α] {a : α} {f : α → β} {s : Finset α} {t : Set β} {t' : Finset β}

instance [DecidableEq β] : Decidable (Set.InjOn f s) :=
  -- Use custom implementation for better performance.
  decidable_of_iff ((Multiset.map f s.val).Nodup) Finset.nodup_map_iff_injOn

instance [DecidableEq β] : Decidable (Set.BijOn f s t') :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end List

namespace Finset

variable [Fintype α] {s t : Finset α}

/-- `univ` is the universal finite set of type `Finset α` implied from
  the assumption `Fintype α`. -/
def univ : Finset α :=
  @Fintype.elems α _

@[simp, grind ←, push]
theorem mem_univ (x : α) : x ∈ (univ : Finset α) :=
  Fintype.complete x

theorem mem_univ_val : ∀ x, x ∈ (univ : Finset α).1 := by simp

theorem eq_univ_iff_forall : s = univ ↔ ∀ x, x ∈ s := by simp [Finset.ext_iff]

theorem eq_univ_of_forall : (∀ x, x ∈ s) → s = univ :=
  eq_univ_iff_forall.2

@[simp, norm_cast]
theorem coe_univ : ↑(univ : Finset α) = (Set.univ : Set α) := by ext; simp

@[simp, norm_cast]
theorem coe_eq_univ : (s : Set α) = Set.univ ↔ s = univ := by rw [← coe_univ, coe_inj]

@[simp]
theorem subset_univ (s : Finset α) : s ⊆ univ := fun a _ => mem_univ a

theorem mem_filter_univ {p : α → Prop} [DecidablePred p] : ∀ x, x ∈ univ.filter p ↔ p x := by simp

end Finset

namespace Mathlib.Meta
open Lean Elab Term Meta Batteries.ExtendedBinder Parser.Term PrettyPrinter.Delaborator SubExpr

/-- Elaborate set builder notation for `Finset`.

* `{x | p x}` is elaborated as `Finset.filter (fun x ↦ p x) Finset.univ` if the expected type is
  `Finset ?α`.
* `{x : α | p x}` is elaborated as `Finset.filter (fun x : α ↦ p x) Finset.univ` if the expected
  type is `Finset ?α`.
* `{x ∉ s | p x}` is elaborated as `Finset.filter (fun x ↦ p x) sᶜ` if either the expected type is
  `Finset ?α` or the expected type is not `Set ?α` and `s` has expected type `Finset ?α`.
* `{x ≠ a | p x}` is elaborated as `Finset.filter (fun x ↦ p x) {a}ᶜ` if the expected type is
  `Finset ?α`.

See also
* `Data.Set.Defs` for the `Set` builder notation elaborator that this elaborator partly overrides.
* `Data.Finset.Basic` for the `Finset` builder notation elaborator partly overriding this one for
  syntax of the form `{x ∈ s | p x}`.
* `Data.Fintype.Basic` for the `Finset` builder notation elaborator handling syntax of the form
  `{x | p x}`, `{x : α | p x}`, `{x ∉ s | p x}`, `{x ≠ a | p x}`.
* `Order.LocallyFinite.Basic` for the `Finset` builder notation elaborator handling syntax of the
  form `{x ≤ a | p x}`, `{x ≥ a | p x}`, `{x < a | p x}`, `{x > a | p x}`.
-/
@[term_elab setBuilder]
def elabFinsetBuilderSetOf : TermElab
  | `({ $x:ident | $p }), expectedType? => do
    -- If the expected type is not known to be `Finset ?α`, give up.
    unless ← knownToBeFinsetNotSet expectedType? do throwUnsupportedSyntax
    elabTerm (← `(Finset.filter (fun $x:ident ↦ $p) Finset.univ)) expectedType?
  | `({ $x:ident : $t | $p }), expectedType? => do
    -- If the expected type is not known to be `Finset ?α`, give up.
    unless ← knownToBeFinsetNotSet expectedType? do throwUnsupportedSyntax
    elabTerm (← `(Finset.filter (fun $x:ident : $t ↦ $p) Finset.univ)) expectedType?
  | `({ $x:ident ∉ $s:term | $p }), expectedType? => do
    -- If the expected type is known to be `Set ?α`, give up. If it is not known to be `Set ?α` or
    -- `Finset ?α`, check the expected type of `s`.
    unless ← knownToBeFinsetNotSet expectedType? do
      let ty ← try whnfR (← inferType (← elabTerm s none)) catch _ => throwUnsupportedSyntax
      -- If the expected type of `s` is not known to be `Finset ?α`, give up.
      match_expr ty with
      | Finset _ => pure ()
      | _ => throwUnsupportedSyntax
    -- Finally, we can elaborate the syntax as a finset.
    -- TODO: Seems a bit wasteful to have computed the expected type but still use `expectedType?`.
    elabTerm (← `(Finset.filter (fun $x:ident ↦ $p) $sᶜ)) expectedType?
  | `({ $x:ident ≠ $a | $p }), expectedType? => do
    -- If the expected type is not known to be `Finset ?α`, give up.
    unless ← knownToBeFinsetNotSet expectedType? do throwUnsupportedSyntax
    elabTerm (← `(Finset.filter (fun $x:ident ↦ $p) (singleton $a)ᶜ)) expectedType?
  | _, _ => throwUnsupportedSyntax

/-- Delaborator for `Finset.filter`. The `pp.funBinderTypes` option controls whether
to show the domain type when the filter is over `Finset.univ`. -/
@[app_delab Finset.filter] def delabFinsetFilter : Delab :=
  whenPPOption getPPNotation do
  let #[_, p, _, t] := (← getExpr).getAppArgs | failure
  guard p.isLambda
  let i ← withNaryArg 1 <| withBindingBodyUnusedName (pure ⟨·⟩)
  let p ← withNaryArg 1 <| withBindingBody i.getId delab
  if t.isAppOfArity ``Finset.univ 2 then
    if ← getPPOption getPPFunBinderTypes then
      let ty ← withNaryArg 0 delab
      `({$i:ident : $ty | $p})
    else
      `({$i:ident | $p})
  -- check if `t` is of the form `s₀ᶜ`, in which case we display `x ∉ s₀` instead
  else if t.isAppOfArity ``HasCompl.compl 3 then
    let #[_, _, s₀] := t.getAppArgs | failure
    -- if `s₀` is a singleton, we can even use the notation `x ≠ a`
    if s₀.isAppOfArity ``Singleton.singleton 4 then
      let t ← withNaryArg 3 <| withNaryArg 2 <| withNaryArg 3 delab
      `({$i:ident ≠ $t | $p})
    else
      let t ← withNaryArg 3 <| withNaryArg 2 delab
      `({$i:ident ∉ $t | $p})
  else
    let t ← withNaryArg 3 delab
    `({$i:ident ∈ $t | $p})

end Mathlib.Meta

open Finset

namespace Fintype

instance decidablePiFintype {α} {β : α → Type*} [∀ a, DecidableEq (β a)] [Fintype α] :
    DecidableEq (∀ a, β a) := fun f g =>
  decidable_of_iff (∀ a ∈ @univ α _, f a = g a)
    (by simp [funext_iff])

instance decidableForallFintype {p : α → Prop} [DecidablePred p] [Fintype α] :
    Decidable (∀ a, p a) :=
  decidable_of_iff (∀ a ∈ @univ α _, p a) (by simp)

instance decidableExistsFintype {p : α → Prop} [DecidablePred p] [Fintype α] :
    Decidable (∃ a, p a) :=
  decidable_of_iff (∃ a ∈ @univ α _, p a) (by simp)

instance decidableMemRangeFintype [Fintype α] [DecidableEq β] (f : α → β) :
    DecidablePred (· ∈ Set.range f) := fun _ => Fintype.decidableExistsFintype

instance decidableSubsingleton [Fintype α] [DecidableEq α] {s : Set α} [DecidablePred (· ∈ s)] :
    Decidable s.Subsingleton := decidable_of_iff (∀ a ∈ s, ∀ b ∈ s, a = b) Iff.rfl

section BundledHoms

instance decidableEqEquivFintype [DecidableEq β] [Fintype α] : DecidableEq (α ≃ β) := fun a b =>
  decidable_of_iff (a.1 = b.1) Equiv.coe_fn_injective.eq_iff

instance decidableEqEmbeddingFintype [DecidableEq β] [Fintype α] : DecidableEq (α ↪ β) := fun a b =>
  decidable_of_iff ((a : α → β) = b) Function.Embedding.coe_injective.eq_iff

end BundledHoms

theorem nodup_map_univ_iff_injective [Fintype α] {f : α → β} :
    (Multiset.map f univ.val).Nodup ↔ Function.Injective f := by
  rw [nodup_map_iff_injOn, coe_univ, Set.injective_iff_injOn_univ]

instance decidableInjectiveFintype [DecidableEq β] [Fintype α] :
    DecidablePred (Injective : (α → β) → Prop) :=
  -- Use custom implementation for better performance.
  fun f => decidable_of_iff ((Multiset.map f univ.val).Nodup) nodup_map_univ_iff_injective

instance decidableSurjectiveFintype [DecidableEq β] [Fintype α] [Fintype β] :
    DecidablePred (Surjective : (α → β) → Prop) := fun x => by unfold Surjective; infer_instance

instance decidableBijectiveFintype [DecidableEq β] [Fintype α] [Fintype β] :
    DecidablePred (Bijective : (α → β) → Prop) := fun x => by unfold Bijective; infer_instance

instance decidableRightInverseFintype [DecidableEq α] [Fintype α] (f : α → β) (g : β → α) :
    Decidable (Function.RightInverse f g) :=
  show Decidable (∀ x, g (f x) = x) by infer_instance

instance decidableLeftInverseFintype [DecidableEq β] [Fintype β] (f : α → β) (g : β → α) :
    Decidable (Function.LeftInverse f g) :=
  show Decidable (∀ x, f (g x) = x) by infer_instance

instance subsingleton (α : Type*) : Subsingleton (Fintype α) :=
  ⟨fun ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ => by congr; simp [Finset.ext_iff, h₁, h₂]⟩

instance (α : Type*) : Lean.Meta.FastSubsingleton (Fintype α) := {}

/-- Given a predicate that can be represented by a finset, the subtype
associated to the predicate is a fintype. -/
protected def subtype {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x) :
    Fintype { x // p x } :=
  ⟨⟨s.1.pmap Subtype.mk fun x => (H x).1, s.nodup.pmap fun _ _ _ _ => congr_arg Subtype.val⟩,
    fun ⟨x, px⟩ => Multiset.mem_pmap.2 ⟨x, (H x).2 px, rfl⟩⟩

/-- Construct a fintype from a finset with the same elements. -/
def ofFinset {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) : Fintype p :=
  Fintype.subtype s H

end Fintype

instance Bool.fintype : Fintype Bool :=
  ⟨⟨{true, false}, by simp⟩, fun x => by cases x <;> simp⟩

instance Ordering.fintype : Fintype Ordering :=
  ⟨⟨{.lt, .eq, .gt}, by simp⟩, fun x => by cases x <;> simp⟩

instance OrderDual.fintype (α : Type*) [Fintype α] : Fintype αᵒᵈ :=
  ‹Fintype α›

instance OrderDual.finite (α : Type*) [Finite α] : Finite αᵒᵈ :=
  ‹Finite α›

instance Lex.fintype (α : Type*) [Fintype α] : Fintype (Lex α) :=
  ‹Fintype α›
