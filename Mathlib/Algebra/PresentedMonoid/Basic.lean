/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Fechtner
-/

import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.GroupTheory.Congruence

/-!
# Defining a monoid given by generators and relations

Given a subset `rels` of relations of the free monoid on a type `α`, this file constructs the monoid
given by generators `x : α` and relations `r ∈ rels`.

## Main definitions

* `PresentedMonoid rels`: the quot group of the free group on a type `α` by the steps-to closure
  of a subset `rels` of relations of the free monoid on `α`.
* `of`: The canonical map from `α` to a presented monoid with generators `α`.
* `toMonoid f`: the canonical monoid homomorphism `PresentedMonoid rels → M`, given a function
  `f : α → G` from a type `α` to a monoid `M` which satisfies the relations `rels`.

## Tags

generators, relations, monoid presentations
-/

variable {α : Type*}

/-- Given a set of relations, `rels`, over a type `α`, `PresentedMonoid` constructs the monoid with
generators `x : α` and relations `rels` as a quotient of a congruence structure over rels. -/
@[to_additive "Given a set of relations, `rels`, over a type `α`, `PresentedAddMonoid` constructs
the monoid with generators `x : α` and relations `rels` as a quotient of an AddCon structure over
rels"]
def PresentedMonoid (rel : FreeMonoid α → FreeMonoid α → Prop) := (conGen rel).Quotient

namespace PresentedMonoid

open Set Submonoid


/-- The quotient map from the free monoid on `α` to the presented monoid with the same generators
and the given relations `rels`. -/
@[to_additive "The quotient map from the free additive monoid on `α` to the presented additive
monoid with the same generators and the given relations `rels`"]
def mk (rels : FreeMonoid α → FreeMonoid α → Prop) (a : FreeMonoid α) : PresentedMonoid rels :=
  Quotient.mk (conGen rels).toSetoid a

/-- `of` is the canonical map from `α` to a presented monoid with generators `x : α`. The term `x`
is mapped to the equivalence class of the image of `x` in `FreeMonoid α`. -/
@[to_additive "`of` is the canonical map from `α` to a presented additive monoid with generators
`x : α`. The term `x` is mapped to the equivalence class of the image of `x` in `FreeAddMonoid α`"]
def of (rels : FreeMonoid α → FreeMonoid α → Prop) (x : α) : PresentedMonoid rels :=
  Quotient.mk (conGen rels).toSetoid (FreeMonoid.of x)

section inductionOn

variable {α₁ α₂ α₃ : Type* } {rels₁ : FreeMonoid α₁ → FreeMonoid α₁ → Prop}
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

variable {α : Type*} {rels : FreeMonoid α → FreeMonoid α → Prop}

@[to_additive]
instance : Monoid (PresentedMonoid rels) := Con.monoid (conGen rels)

@[to_additive]
theorem mul_mk (a b : FreeMonoid α) : mk rels a * (mk rels b) = mk rels (a*b) := rfl

@[to_additive]
theorem one_def : (1 : PresentedMonoid rels) = mk rels 1 := rfl

/-- The generators of a presented monoid generate the presented monoid. That is, the submonoid
closure of the set of generators equals `⊤`. -/
@[to_additive (attr := simp) "The generators of a presented additive monoid generate the presented
additive monoid. That is, the submonoid closure of the set of generators equals `⊤`"]
theorem closure_range_of (rels : FreeMonoid α → FreeMonoid α → Prop) :
  Submonoid.closure (Set.range (PresentedMonoid.of rels)) = ⊤ := by
  rw [Submonoid.eq_top_iff']
  intro x
  induction' x with a
  induction a
  · exact Submonoid.one_mem _
  · rename_i x
    exact subset_closure (Exists.intro x rfl)
  rename_i x y hx hy
  exact Submonoid.mul_mem _ hx hy

section ToMonoid
variable {α M : Type*} [Monoid M] (f : α → M)
variable {rels : FreeMonoid α → FreeMonoid α → Prop}
variable (h : ∀ a b : FreeMonoid α, rels a b →  FreeMonoid.lift f a = FreeMonoid.lift f b)

/-- The extension of a map `f : α → M` that satisfies the given relations to a monoid homomorphism
from `PresentedMonoid rels → M`. -/
@[to_additive "The extension of a map `f : α → M` that satisfies the given relations to an
additive-monoid homomorphism from `PresentedAddMonoid rels → M`"]
def toMonoid : MonoidHom (PresentedMonoid rels) M :=
  Con.lift _ (FreeMonoid.lift f) (Con.conGen_le h)

@[to_additive]
theorem toMonoid.unique (g : MonoidHom (conGen rels).Quotient M)
    (hg : ∀ a : α, g (of rels a) = f a) : g = toMonoid f h :=
  Con.lift_unique (proof_1 f h) g (FreeMonoid.hom_eq fun x ↦ let_fun this := hg x; this)

@[to_additive (attr := simp)]
theorem toMonoid.of {x : α} : (PresentedMonoid.toMonoid f h) (PresentedMonoid.of rels x) =
    f x := rfl

end ToMonoid

@[to_additive (attr := ext)]
theorem ext {M : Type*} [Monoid M] (rels : FreeMonoid α → FreeMonoid α → Prop)
    {φ ψ : PresentedMonoid rels →* M} (hx : ∀ (x : α), φ (.of rels x) = ψ (.of rels x)) :
    φ = ψ := by
  ext a
  induction' a with b
  induction b
  · rw [← one_def, map_one, map_one]
  · rename_i x
    exact hx x
  rename_i x y hx hy
  rw [← mul_mk, map_mul, map_mul, hx, hy]

section Isomorphism
variable {β : Type*} (e : α ≃ β) (rels : FreeMonoid α → FreeMonoid α → Prop)

@[to_additive]
noncomputable def equivPresentedMonoid (rel : FreeMonoid β → FreeMonoid β → Prop) :
    PresentedMonoid rel ≃* PresentedMonoid (FreeMonoid.comap_rel e rel) :=
  (Con.comapQuotientEquivOfSurj _ _ (EquivLike.surjective (FreeMonoid.congr_iso e))).symm.trans <|
  Con.congr (Con.comap_conGen_of_Bijective (FreeMonoid.congr_iso e) (MulEquiv.bijective _) _ rel)

end Isomorphism
