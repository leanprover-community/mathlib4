/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jonas van der Schaaf
-/
import Mathlib.CategoryTheory.Closed.Monoidal

/-!

# Internal projectivity

This file defines internal projectivity of objects `P` in a category `C` as a class
`InternallyProjective P`. This means that the functor taking internal homs out of `P`
preserves epimorphisms. It also proves that a retract of an internally projective object
is internally projective (see `InternallyProjective.ofRetract`).
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed Limits Functor

namespace CategoryTheory

variable {C : Type*} [Category C] [MonoidalCategory C] [MonoidalClosed C]

/--
An object `P : C` is *internally projective* if the functor `P ⟶[C] -` taking internal homs
out of `P` preserves epimorphisms.
-/
class InternallyProjective (P : C) : Prop where
  /-- The functor `P ⟶[C] -` preserves epimorphisms. -/
  preserves_epi : (ihom P).PreservesEpimorphisms

attribute [instance] InternallyProjective.preserves_epi

namespace InternallyProjective

lemma ofRetract {X Y : C} (r : Retract Y X) [InternallyProjective X] : InternallyProjective Y where
  preserves_epi :=
    have : Retract (ihom Y) (ihom X) := r.op.map internalHom
    preservesEpimorphisms.ofRetract this

end CategoryTheory.InternallyProjective
