/-
Copyright (c) 2026 Matteo Cipollina,Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/

module

public import Mathlib.CategoryTheory.Filtration.Basic

/-!

## Opposed filtrations (Deligne, *Théorie de Hodge II*, §1.2.1–§1.2.3).

This file defines the iterated graded pieces for a pair of filtrations and the predicate
that two filtrations are `n`-opposed.

Deligne's definition (1.2.3) says that two finite filtrations `F, G` on an object `A`
are `n`-opposed if

`Gr_F^p Gr_G^q(A) = 0` whenever `p + q ≠ n`.

We define `Gr_F^p Gr_G^q(A)` directly by the symmetric Zassenhaus quotient formula

`(F^p ∩ G^q) / ( (F^{p+1} ∩ G^q) + (F^p ∩ G^{q+1}) )`.

In a later PR we will prove the Zassenhaus isomorphisms and the splitting lemma
(Deligne 1.2.5).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

namespace DecFiltration

variable {A : C}

/-- The *bigraded* piece associated to two decreasing filtrations `F` and `G`.

This aims to model the Zassenhaus quotient (symmetric in `F` and `G`):

`(F p ⊓ G q) / ((F (p+1) ⊓ G q) ⊔ (F p ⊓ G (q+1)))`.

It is canonically isomorphic to both `Gr_F^p (Gr_G^q A)` and `Gr_G^q (Gr_F^p A)`;
those isomorphisms are formalized in PR 3.
-/
noncomputable def gr₂ [Abelian C] (F G : DecFiltration A) (p q : ℤ) : C :=
  let X : Subobject A := F p ⊓ G q
  let Y : Subobject A := (F (p + 1) ⊓ G q) ⊔ (F p ⊓ G (q + 1))
  have hY : Y ≤ X := by
    -- Each summand is contained in `F p ⊓ G q`.
    refine sup_le ?_ ?_
    · -- `F (p+1) ⊓ G q ≤ F p ⊓ G q`.
      have hp : p ≤ p + 1 := by omega
      have hF : F (p + 1) ≤ F p := F.antitone hp
      exact inf_le_inf hF le_rfl
    · -- `F p ⊓ G (q+1) ≤ F p ⊓ G q`.
      have hq : q ≤ q + 1 := by omega
      have hG : G (q + 1) ≤ G q := G.antitone hq
      exact inf_le_inf le_rfl hG
  cokernel (Y.ofLE X hY)

/-- Two filtrations are `n`-opposed (Deligne 1.2.3) if `Gr_F^p Gr_G^q(A) = 0`
whenever `p+q ≠ n`.

We express vanishing using `IsZero`.
-/
def IsNOpposed [Abelian C] (F G : DecFiltration A) (n : ℤ) : Prop :=
  ∀ p q : ℤ, p + q ≠ n → IsZero (gr₂ F G p q)

/-- Convenience lemma: if `F` and `G` are `n`-opposed then the bigraded piece off the
`p+q=n` diagonal is zero. -/
lemma isZero_gr₂_of_IsNOpposed [Abelian C] {F G : DecFiltration A} {n p q : ℤ}
    (h : IsNOpposed F G n) (hpq : p + q ≠ n) :
    IsZero (gr₂ F G p q) :=
  h p q hpq

end DecFiltration

/-- A *bifiltered object*: an object equipped with two decreasing ℤ-filtrations.

This is Deligne's ambient setting for §1.2.
-/
structure BifilteredObject (C : Type u) [Category.{v} C] where
  obj : C
  F : DecFiltration obj
  G : DecFiltration obj

namespace BifilteredObject

instance : Coe (BifilteredObject C) C where
  coe X := X.obj

/-- Morphisms of bifiltered objects: morphisms preserving both filtrations.

We use the pullback formulation: `f` preserves `F` if `A.F n ≤ (pullback f).obj (B.F n)`,
which is equivalent to saying the image of `A.F n` under `f` is contained in `B.F n`.
-/
structure Hom [HasPullbacks C] (A B : BifilteredObject C) where
  hom : (A : C) ⟶ (B : C)
  compatF : ∀ n : ℤ, A.F n ≤ (Subobject.pullback hom).obj (B.F n)
  compatG : ∀ n : ℤ, A.G n ≤ (Subobject.pullback hom).obj (B.G n)

variable [HasPullbacks C]

@[ext] lemma Hom.ext {A B : BifilteredObject C} (f g : Hom A B) (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Identity morphism of a bifiltered object. -/
def id (A : BifilteredObject C) : Hom A A where
  hom := 𝟙 A.obj
  compatF := by
    intro n
    simp only [Subobject.pullback_id]
    exact le_rfl
  compatG := by
    intro n
    simp only [Subobject.pullback_id]
    exact le_rfl

/-- Composition of morphisms of bifiltered objects. -/
def comp {A B D : BifilteredObject C} (f : Hom A B) (g : Hom B D) : Hom A D where
  hom := f.hom ≫ g.hom
  compatF := by
    intro n
    calc A.F n
        ≤ (Subobject.pullback f.hom).obj (B.F n) := f.compatF n
      _ ≤ (Subobject.pullback f.hom).obj ((Subobject.pullback g.hom).obj (D.F n)) :=
          (Subobject.pullback f.hom).monotone (g.compatF n)
      _ = (Subobject.pullback (f.hom ≫ g.hom)).obj (D.F n) := by
          rw [Subobject.pullback_comp]
  compatG := by
    intro n
    calc A.G n
        ≤ (Subobject.pullback f.hom).obj (B.G n) := f.compatG n
      _ ≤ (Subobject.pullback f.hom).obj ((Subobject.pullback g.hom).obj (D.G n)) :=
          (Subobject.pullback f.hom).monotone (g.compatG n)
      _ = (Subobject.pullback (f.hom ≫ g.hom)).obj (D.G n) := by
          rw [Subobject.pullback_comp]

instance : Category (BifilteredObject C) where
  Hom A B := Hom A B
  id A := id A
  comp f g := comp f g
  id_comp := by intro A B f; ext; simp [BifilteredObject.id, BifilteredObject.comp]
  comp_id := by intro A B f; ext; simp [BifilteredObject.id, BifilteredObject.comp]
  assoc := by intro A B D E f g h; ext; simp [BifilteredObject.comp, Category.assoc]

/-- The forgetful functor `BifilteredObject C ⥤ C`. -/
@[simps] def forget : BifilteredObject C ⥤ C where
  obj A := A.obj
  map f := f.hom
  map_id := by intro A; rfl
  map_comp := by intro A B D f g; rfl

section Abelian

variable [Abelian C]

/-- The `gr₂` construction for a bifiltered object. -/
noncomputable def gr₂ (A : BifilteredObject C) (p q : ℤ) : C :=
  DecFiltration.gr₂ A.F A.G p q

/-- A bifiltered object is `n`-opposed if its two filtrations are `n`-opposed (Deligne 1.2.3). -/
def IsNOpposed (A : BifilteredObject C) (n : ℤ) : Prop :=
  DecFiltration.IsNOpposed A.F A.G n

end Abelian

end BifilteredObject

end CategoryTheory
