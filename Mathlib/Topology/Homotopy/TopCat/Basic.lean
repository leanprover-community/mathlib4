/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Topology.Category.TopCat.Monoidal
public import Mathlib.Topology.Homotopy.Basic

/-!
# Homotopies between morphisms in `TopCat`

In this file, we define the type `TopCat.Homotopy` of homotopies
between two morphisms in the category `TopCat`.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace TopCat

variable {X Y : TopCat.{u}}

/-- An homotopy between morphisms in `TopCat` is a homotopy between
the corresponding continuous maps. -/
abbrev Homotopy (f g : X ⟶ Y) := ContinuousMap.Homotopy f.hom g.hom

namespace Homotopy

variable {f g : X ⟶ Y} (H : Homotopy f g)

/-- The morphism `X ⊗ I ⟶ Y` that is part of a homotopy between two morphisms in `TopCat`. -/
def h (H : Homotopy f g) : X ⊗ I ⟶ Y :=
  (β_ _ _).hom ≫ ofHom (H.toContinuousMap.comp (ContinuousMap.prodMap I.homeomorph (.id _)))

@[reassoc (attr := simp)]
lemma ι₀_h : ι₀ ≫ H.h = f := by
  ext x
  exact H.map_zero_left x

@[reassoc (attr := simp)]
lemma ι₁_h : ι₁ ≫ H.h = g := by
  ext x
  exact H.map_one_left x

end Homotopy

end TopCat
