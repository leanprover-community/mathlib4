/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.ModelCategory.Bifibrant
import Mathlib.AlgebraicTopology.ModelCategory.Homotopy

/-!
# The fundamental lemma of homotopical algebra

-/

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable (C : Type*) [Category C] [ModelCategory C]

namespace CofibrantObject

def homRel : HomRel (CofibrantObject C) :=
  fun X Y ↦ RightHomotopyRel (X := X.1) (Y := Y.1)

lemma compClosure_homRel :
    Quotient.CompClosure (homRel C) = homRel C := by
  ext X Y f g
  refine ⟨?_, Quotient.CompClosure.of _ _ _⟩
  rintro ⟨i, f', g', p, h⟩
  exact (h.postcomp p).precomp i

end CofibrantObject

namespace FibrantObject

def homRel : HomRel (FibrantObject C) :=
  fun X Y ↦ LeftHomotopyRel (X := X.1) (Y := Y.1)

lemma compClosure_homRel :
    Quotient.CompClosure (homRel C) = homRel C := by
  ext X Y f g
  refine ⟨?_, Quotient.CompClosure.of _ _ _⟩
  rintro ⟨i, f', g', p, h⟩
  exact (h.postcomp p).precomp i

end FibrantObject

namespace BifibrantObject

def homRel : HomRel (BifibrantObject C) :=
  fun X Y ↦ RightHomotopyRel (X := X.1) (Y := Y.1)

instance : Congruence (homRel C) where
  equivalence := RightHomotopyRel.equivalence _ _
  compLeft p _ _ h := h.precomp p
  compRight p h := h.postcomp p

variable {C} {X Y : BifibrantObject C} (f g : X ⟶ Y)

lemma homRel_iff_rightHomotopyRel :
    homRel C f g ↔ RightHomotopyRel (ι.map f) (ι.map g) := Iff.rfl

lemma homRel_iff_leftHomotopyRel :
    homRel C f g ↔ LeftHomotopyRel (ι.map f) (ι.map g) := by
  rw [homRel_iff_rightHomotopyRel, leftHomotopyRel_iff_rightHomotopyRel]

end BifibrantObject

end HomotopicalAlgebra
