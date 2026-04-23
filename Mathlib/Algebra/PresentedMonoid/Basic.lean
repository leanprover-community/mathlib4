/-
Copyright (c) 2024 Hannah Fechtner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Fechtner
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.GroupTheory.Congruence.Hom
public import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Translate.ToAdditive
import Mathlib.Util.CompileInductive

/-!
# Defining a monoid given by generators and relations

Given relations `rels` on the free monoid on a type `α`, this file constructs the monoid
given by generators `x : α` and relations `rels`.

## Main definitions

* `PresentedMonoid rels`: the quotient of the free monoid on a type `α` by the closure of one-step
  reductions (arising from a binary relation on free monoid elements `rels`).
* `PresentedMonoid.of`: The canonical map from `α` to a presented monoid with generators `α`.
* `PresentedMonoid.lift f`: the canonical monoid homomorphism `PresentedMonoid rels → M`, given
  a function `f : α → G` from a type `α` to a monoid `M` which satisfies the relations `rels`.

## Tags

generators, relations, monoid presentations
-/

@[expose] public section

variable {α : Type*}

/-- Given a set of relations, `rels`, over a type `α`, `PresentedMonoid` constructs the monoid with
generators `x : α` and relations `rels` as a quotient of a congruence structure over rels. -/
@[to_additive /-- Given a set of relations, `rels`, over a type `α`, `PresentedAddMonoid` constructs
the monoid with generators `x : α` and relations `rels` as a quotient of an AddCon structure over
rels -/]
def PresentedMonoid (rels : FreeMonoid α → FreeMonoid α → Prop) := (conGen rels).Quotient

namespace PresentedMonoid

open Set Submonoid

@[to_additive]
instance {rels : FreeMonoid α → FreeMonoid α → Prop} : Monoid (PresentedMonoid rels) :=
  inferInstanceAs <| Monoid (conGen rels).Quotient

/-- The quotient map from the free monoid on `α` to the presented monoid with the same generators
and the given relations `rels`. -/
@[to_additive /-- The quotient map from the free additive monoid on `α` to the presented additive
monoid with the same generators and the given relations `rels` -/]
def mk (rels : FreeMonoid α → FreeMonoid α → Prop) : FreeMonoid α →* PresentedMonoid rels where
  toFun := Quotient.mk (conGen rels).toSetoid
  map_one' := rfl
  map_mul' := fun _ _ => rfl

/-- `of` is the canonical map from `α` to a presented monoid with generators `x : α`. The term `x`
is mapped to the equivalence class of the image of `x` in `FreeMonoid α`. -/
@[to_additive
/-- `of` is the canonical map from `α` to a presented additive monoid with generators `x : α`. The
term `x` is mapped to the equivalence class of the image of `x` in `FreeAddMonoid α`. -/]
def of (rels : FreeMonoid α → FreeMonoid α → Prop) (x : α) : PresentedMonoid rels :=
  mk rels (.of x)

section inductionOn

variable {α₁ α₂ α₃ : Type*} {rels₁ : FreeMonoid α₁ → FreeMonoid α₁ → Prop}
  {rels₂ : FreeMonoid α₂ → FreeMonoid α₂ → Prop} {rels₃ : FreeMonoid α₃ → FreeMonoid α₃ → Prop}

local notation "P₁" => PresentedMonoid rels₁
local notation "P₂" => PresentedMonoid rels₂
local notation "P₃" => PresentedMonoid rels₃

@[to_additive (attr := elab_as_elim), induction_eliminator]
protected theorem inductionOn {δ : P₁ → Prop} (q : P₁) (h : ∀ a, δ (mk rels₁ a)) : δ q :=
  Quotient.ind h q

@[to_additive (attr := elab_as_elim)]
protected theorem inductionOn₂ {δ : P₁ → P₂ → Prop} (q₁ : P₁) (q₂ : P₂)
    (h : ∀ a b, δ (mk rels₁ a) (mk rels₂ b)) : δ q₁ q₂ :=
  Quotient.inductionOn₂ q₁ q₂ h

@[to_additive (attr := elab_as_elim)]
protected theorem inductionOn₃ {δ : P₁ → P₂ → P₃ → Prop} (q₁ : P₁)
    (q₂ : P₂) (q₃ : P₃) (h : ∀ a b c, δ (mk rels₁ a) (mk rels₂ b) (mk rels₃ c)) :
    δ q₁ q₂ q₃ :=
  Quotient.inductionOn₃ q₁ q₂ q₃ h

end inductionOn

variable {α : Type*} {rels : FreeMonoid α → FreeMonoid α → Prop} {x y : FreeMonoid α}

lemma mk_eq_mk_iff : mk rels x = mk rels y ↔ conGen rels x y := Quotient.eq

lemma mk_eq_mk_of_rel (h : rels x y) : mk rels x = mk rels y := mk_eq_mk_iff.2 (.of _ _ h)

/-- The generators of a presented monoid generate the presented monoid. That is, the submonoid
closure of the set of generators equals `⊤`. -/
@[to_additive (attr := simp) /-- The generators of a presented additive monoid generate the
presented additive monoid. That is, the additive submonoid closure of the set of generators equals
`⊤`. -/]
theorem closure_range_of (rels : FreeMonoid α → FreeMonoid α → Prop) :
    Submonoid.closure (Set.range (of rels)) = ⊤ := by
  rw [Submonoid.eq_top_iff']
  intro x
  induction x with | _ a
  induction a with
  | one => exact Submonoid.one_mem _
  | of x => exact subset_closure <| by simp [range, of]
  | mul x y hx hy => exact Submonoid.mul_mem _ hx hy

@[to_additive]
theorem surjective_mk {rels : FreeMonoid α → FreeMonoid α → Prop} :
    Function.Surjective (mk rels) := fun x ↦ PresentedMonoid.inductionOn x fun a ↦ .intro a rfl

section ToMonoid
variable {α M : Type*} [Monoid M] (f : α → M)
variable {rels : FreeMonoid α → FreeMonoid α → Prop}
variable (h : ∀ a b : FreeMonoid α, rels a b → FreeMonoid.lift f a = FreeMonoid.lift f b)

/-- The extension of a map `f : α → M` that satisfies the given relations to a monoid homomorphism
from `PresentedMonoid rels → M`. -/
@[to_additive /-- The extension of a map `f : α → M` that satisfies the given relations to an
additive-monoid homomorphism from `PresentedAddMonoid rels → M` -/]
def lift : PresentedMonoid rels →* M :=
  Con.lift _ (FreeMonoid.lift f) (Con.conGen_le h)

@[to_additive]
theorem toMonoid.unique (g : MonoidHom (conGen rels).Quotient M)
    (hg : ∀ a : α, g (of rels a) = f a) : g = lift f h :=
  Con.lift_unique (Con.conGen_le h) g (FreeMonoid.hom_eq hg)

@[to_additive (attr := simp)]
theorem lift_of {x : α} : lift f h (of rels x) = f x := rfl

end ToMonoid

@[to_additive (attr := ext)]
theorem ext {M : Type*} [Monoid M] (rels : FreeMonoid α → FreeMonoid α → Prop)
    {φ ψ : PresentedMonoid rels →* M} (hx : ∀ (x : α), φ (.of rels x) = ψ (.of rels x)) :
    φ = ψ := by
  apply MonoidHom.eq_of_eqOn_denseM (closure_range_of _)
  grind [Set.eqOn_range]

end PresentedMonoid
