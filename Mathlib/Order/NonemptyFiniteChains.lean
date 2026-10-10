/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Image
public import Mathlib.Order.Category.PartOrd

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

-- to be moved
namespace Finset

variable {X : Type*}

lemma compl_singleton_ssubset_univ [Fintype X] [DecidableEq X] (x : X) :
    {x}ᶜ ⊂ Finset.univ := by
  rw [lt_iff_le_and_ne]
  aesop

lemma compl_singleton_ssubset_iff [Fintype X] [DecidableEq X] (s : Finset X) (x : X) :
    {x}ᶜ ⊂ s ↔ s = .univ := by
  simp [ssubset_iff]

lemma compl_singleton_subset_iff [Fintype X] [DecidableEq X] (s : Finset X) (x : X) :
    {x}ᶜ ⊆ s ↔ s = {x}ᶜ ∨ s = .univ := by
  rw [← s.compl_singleton_ssubset_iff x, le_iff_eq_or_lt']

lemma eq_compl_singleton_iff [Fintype X] [DecidableEq X] (s : Finset X) (x : X) :
    s = {x}ᶜ ↔ s < ⊤ ∧ s ∪ {x} = .univ := by
  refine ⟨by rintro rfl; simp [compl_singleton_ssubset_iff], fun ⟨h₁, h₂⟩ ↦ ?_⟩
  replace h₂ (z : X) : z = x ∨ z ∈ s := by
    simpa [← h₂] using Finset.mem_univ z
  grind [mem_compl]

end Finset

namespace PartialOrder

/-- Given a partially ordered type `X`, this is the type of nonempty finite
subsets `A` of `X` such that all the elements of `A` are comparable. -/
@[ext]
structure NonemptyFiniteChains (X : Type u) [PartialOrder X] where
  /-- a finite subset -/
  finset : Finset X
  nonempty : finset.Nonempty := by simp
  comparable (a b : finset) : a ≤ b ∨ b ≤ a := by apply le_total

namespace NonemptyFiniteChains

attribute [simp] nonempty

instance (X : Type u) [PartialOrder X] : PartialOrder (NonemptyFiniteChains X) :=
  PartialOrder.lift finset (fun _ _ _ ↦ by aesop)

variable {X Y : Type*} [PartialOrder X] [PartialOrder Y]

@[simp]
lemma le_iff (A B : NonemptyFiniteChains X) : A ≤ B ↔ A.finset ≤ B.finset := Iff.rfl

@[simp]
lemma lt_iff (A B : NonemptyFiniteChains X) : A < B ↔ A.finset < B.finset := Iff.rfl

open scoped Classical in
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

section

variable {Z : Type*} [LinearOrder Z] [Fintype Z]

instance [Nonempty Z] : OrderTop (NonemptyFiniteChains Z) where
  top :=
    { finset := .univ
      comparable := le_total }
  le_top _ := by simp

@[simp] lemma coe_top [Nonempty Z] : (⊤ : NonemptyFiniteChains Z).1 = Finset.univ := rfl

variable (x₀ : Z) [Nontrivial Z]

@[simps]
def complSingleton : NonemptyFiniteChains Z where
  finset := {x₀}ᶜ
  nonempty := ⟨(exists_ne x₀).choose, by simpa using (exists_ne x₀).choose_spec⟩
  comparable := le_total

--lemma complSingleton_le_iff {s : NonemptyFiniteChains Z} :
--    complSingleton x₀ ≤ s ↔ s = complSingleton x₀ ∨ s = ⊤ := by
--  simp [NonemptyFiniteChains.ext_iff]

--lemma complSingleton_lt_top :
--    complSingleton x₀ < ⊤ := by
--  simp

--lemma complSingleton_lt_iff {s : NonemptyFiniteChains Z} :
--    complSingleton x₀ < s ↔ s = ⊤ := by
--  simp [NonemptyFiniteChains.ext_iff]

--lemma eq_complSingleton_iff (s : NonemptyFiniteChains Z) :
--    s = complSingleton x₀ ↔ s < ⊤ ∧ s.finset ∪ {x₀} = ⊤ := by
--  simp [NonemptyFiniteChains.ext_iff, Finset.eq_compl_singleton_iff]


end

end NonemptyFiniteChains

end PartialOrder

open PartialOrder in
/-- The functor `PartOrd ⥤ PartOrd` which sends a partially ordered type `X`
to `NonemptyFiniteChains X`. -/
@[simps, implicit_reducible]
noncomputable def PartOrd.nonemptyFiniteChainsFunctor : PartOrd.{u} ⥤ PartOrd.{u} where
  obj X := ↧(NonemptyFiniteChains X)
  map f := PartOrd.ofHom (NonemptyFiniteChains.orderHomMap f.hom)
