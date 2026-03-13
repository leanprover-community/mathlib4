/-
Copyright (c) 2026 Jakob Scharmberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scharmberg
-/
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Defs.Induced
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.CommSq
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# Topological Pairs

In this file we introduce `TopPair`, the category of topological pairs.

We provide the inclusion and diagonal functors `TopCat` ⥤ `TopPair` and show that they are left and
right adjoint to the first projection functor, respectively.

We also define for two morphisms of topological pairs f, g : X ⟶ Y the structure `Homotopy f g` of
homotopies between them.
-/

open TopologicalSpace CategoryTheory unitInterval

universe u

/-- A pair of topological spaces consists of two topological spaces X and A and a map f : A → X
such that the topology of A is induced by f. -/
structure TopPair where
  /-- The first space of the pair -/
  first : TopCat

  /-- The second space of the pair -/
  second : TopCat

  /-- The map that induces the topology on A -/
  map : second ⟶ first
  map_inducing : Topology.IsInducing map.hom

namespace TopPair

/-- Constructor for a topological (X, A) pair where A ⊆ X. -/
def ofSubset {X : TopCat} (A : Set X) : TopPair where
  first := X
  second := TopCat.of A
  map := ⟨{ toFun := (↑) }⟩
  map_inducing := ⟨Eq.symm (TopologicalSpace.ext rfl)⟩

variable {X Y : TopPair}

/-- A morphism of a pair consists of a morphism between the first spaces and a morphism between the
second spaces that fit in a commutative square with the maps of the pairs. -/
@[ext]
structure Hom (X Y : TopPair) where
  /-- The map between the first spaces -/
  first : X.first ⟶ Y.first

  /-- The map between the second spaces -/
  second : X.second ⟶ Y.second

  /-- The proof that the two maps fit in the commutative square -/
  comm : CategoryTheory.CommSq second X.map Y.map first := by cat_disch

@[simps]
instance : Category TopPair where
  Hom := Hom
  id X := { first := 𝟙 X.first, second := 𝟙 X.second }
  comp f g := ⟨_, _, CommSq.horiz_comp f.comm g.comm⟩

/-- The functor from topological pairs to topological spaces that forgets the second space, ie. the
projection to the first space. -/
@[simps]
def proj₁ : TopPair ⥤ TopCat where
  obj := fun X ↦ X.first
  map := fun f ↦ f.first

/-- The functor from topological pairs to topological spaces that forgets the first space, ie. the
projection to the second space. -/
@[simps]
def proj₂ : TopPair ⥤ TopCat where
  obj := fun X ↦ X.second
  map := fun f ↦ f.second

/-- The inclusion functor from topological spaces to topological pairs that sends a space X to
(X, ∅). -/
@[simps]
def incl : TopCat ⥤ TopPair where
  obj := fun X ↦ ⟨_, _, TopCat.isInitialPEmpty.to _, TopCat.IsInducing.empty X⟩
  map := fun f ↦ ⟨f, 𝟙 (TopCat.of PEmpty), ⟨by ext x; induction x⟩⟩

/-- The functor from topological spaces to topological pairs that sends a space X to (X, X) with the
identity morphism on X. -/
@[simps]
def diag : TopCat ⥤ TopPair where
  obj := fun X ↦ ⟨_, _, 𝟙 X, by rw [hom_id]; exact Topology.IsInducing.id⟩
  map := fun f ↦ { first := f, second := f }

@[simps]
instance : Inhabited TopPair := ⟨incl.obj TopCat.inhabited.default⟩

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion functor is left adjoint to the projection to the first component. -/
def inclAdjProj₁ : incl ⊣ proj₁ where
  unit := { app X := 𝟙 X }
  counit := {
    app X := { first := 𝟙 X.first, second := TopCat.isInitialPEmpty.to _ }
    naturality := by
      intro X Y f
      apply Hom.ext
      · simp
      · simp only [Functor.comp_obj, proj₁_obj, Functor.id_obj, Functor.comp_map, proj₁_map,
        comp_second, incl_map_second, Functor.id_map, Limits.IsInitial.to_comp]
        cat_disch
  }
  left_triangle_components X := by
    simp only [Functor.id_obj, Functor.comp_obj, proj₁_obj, incl_obj_first,
      CategoryTheory.Functor.map_id, Category.id_comp]
    apply Hom.ext
    · simp only [incl_obj_first, id_first]
    · cat_disch

/-- The projection functor to the first component is left adjoint to the diagonal functor. -/
def proj₁AdjDiag : proj₁ ⊣ diag where
  unit := {
    app X := { first := 𝟙 X.first, second := X.map },
    naturality := by
      intro X Y f
      apply Hom.ext
      · simp
      · exact f.comm.w
  }
  counit := { app X := 𝟙 X }

/-- The unique morphism (A, ∅) ⟶ (A, B) that is the identity on A. -/
@[simps]
def j (X : TopPair) : TopPair.incl.obj X.first ⟶ X where
  first := 𝟙 X.first
  second := TopCat.isInitialPEmpty.to _
  comm := ⟨by ext x; induction x⟩

/-- A homotopy of maps between topological pairs is a homotopy on the first space and a homotopy on
the second space that fit in a commutative square with the maps of the pairs. -/
structure Homotopy (f g : X ⟶ Y) where
  /-- The homotopy on the first space. -/
  first : ContinuousMap.Homotopy f.first.hom g.first.hom

  /-- The homotopy on the second space. -/
  second : ContinuousMap.Homotopy f.second.hom g.second.hom

  /-- The proof that the homotopies fit into a commutative square with the maps of the pairs. -/
  comm : CommSq (W := I × X.second) (X := Y.second) (Y := I × X.first) (Z := Y.first) second
    (fun (t, x) ↦ (t, X.map x)) Y.map first

/-- Two maps between topological pairs are homotopic if there is a homotopy between them. -/
def Homotopic (f g : X ⟶ Y) := Nonempty (Homotopy f g)

end TopPair
