/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Order.Category.PartOrd
public import Mathlib.Data.Finset.Image
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# Nonempty finite chains in a partially ordered type

Given a partially ordered type `X`, we introduce the type
`NonemptyFiniteChains` of nonempty finite chains in `X`, i.e.
nonempty finite subsets `A` of `X` such that all the elements
in `A` are comparable.

-/

@[expose] public section

universe v u

open CategoryTheory

namespace PartialOrder

/-- Given a partially ordered type `X`, this is the type of nonempty finite
subsets `A` of `X` such that all the elements of `A` are comparable. -/
@[ext]
structure NonemptyFiniteChains (X : Type u) [PartialOrder X] where
  /-- a finite subset -/
  finset : Finset X
  nonempty : finset.Nonempty := by simp
  comparable (a b : finset) : a ≤ b ∨ b ≤ a

namespace NonemptyFiniteChains

attribute [simp] nonempty

instance (X : Type u) [PartialOrder X] : PartialOrder (NonemptyFiniteChains X) :=
  PartialOrder.lift finset (fun _ _ _ ↦ by aesop)

variable {X Y : Type*} [PartialOrder X] [PartialOrder Y]

@[simp]
lemma le_iff (A B : NonemptyFiniteChains X) : A ≤ B ↔ A.finset ≤ B.finset := Iff.rfl

@[simp]
lemma lt_iff (A B : NonemptyFiniteChains X) : A < B ↔ A.finset < B.finset := Iff.rfl

open Classical in
/-- The image of a nonempty finite chain by a monotone map. -/
noncomputable def map (s : NonemptyFiniteChains X) (f : X →o Y) :
    NonemptyFiniteChains Y where
  finset := Finset.image f s.finset
  comparable := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    simp only [Finset.mem_image] at ha hb
    obtain ⟨a, ha', rfl⟩ := ha
    obtain ⟨b, hb', rfl⟩ := hb
    obtain h | h := s.comparable ⟨_, ha'⟩ ⟨_, hb'⟩
    · exact Or.inl (f.monotone h)
    · exact Or.inr (f.monotone h)

@[simp]
lemma mem_map_iff (s : NonemptyFiniteChains X) (f : X →o Y) (y : Y) :
    y ∈ (s.map f).finset ↔ ∃ x, x ∈ s.finset ∧ f x = y := by
  simp [map]

/-- The monotone map `NonemptyFiniteChains X →o NonemptyFiniteChains Y`
that is induced by `f : X →o Y`. -/
@[simps]
noncomputable def orderHomMap (f : X →o Y) :
    NonemptyFiniteChains X →o NonemptyFiniteChains Y where
  toFun s := map s f
  monotone' a b h x hx := by
    simp only [mem_map_iff] at hx ⊢
    obtain ⟨x, hx, rfl⟩ := hx
    exact ⟨x, h hx, rfl⟩

end NonemptyFiniteChains

end PartialOrder

open PartialOrder in
/-- The functor `PartOrd ⥤ PartOrd` which sends a partially ordered type `X`
to `NonemptyFiniteChains X`. -/
@[simps]
noncomputable def PartOrd.nonemptyFiniteChainsFunctor : PartOrd.{u} ⥤ PartOrd.{u} where
  obj X := .of (NonemptyFiniteChains X)
  map f := PartOrd.ofHom (NonemptyFiniteChains.orderHomMap f.hom)
