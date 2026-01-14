/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jonas van der Schaaf
-/
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.ObjectProperty.Retract

/-!

# Internal projectivity

This file defines internal projectivity of objects `P` in a category `C` as a class
`InternallyProjective P`. This means that the functor taking internal homs out of `P`
preserves epimorphisms. It also proves that a retract of an internally projective object
is internally projective (see `InternallyProjective.ofRetract`).

This property is important in the setting of light condensed abelian groups, when establishing
the solid theory (see the lecture series on analytic stacks:
https://www.youtube.com/playlist?list=PLx5f8IelFRgGmu6gmL-Kf_Rl_6Mm7juZO).
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
def isInternallyProjective : ObjectProperty C := fun P ↦ (ihom P).PreservesEpimorphisms

/--
An object `P : C` is *internally projective* if the functor `P ⟶[C] -` taking internal homs
out of `P` preserves epimorphisms.
-/
abbrev InternallyProjective (P : C) := isInternallyProjective.Is P

instance InternallyProjective.preserves_epi (P : C) [InternallyProjective P] :
    (ihom P).PreservesEpimorphisms :=
  isInternallyProjective.prop_of_is P

instance : (isInternallyProjective (C := C)).IsStableUnderRetracts where
  of_retract {Y X} r h :=
    have : InternallyProjective X := ⟨h⟩
    have : Retract (ihom Y) (ihom X) := r.op.map internalHom
    preservesEpimorphisms.ofRetract this

namespace InternallyProjective

lemma ofRetract {X Y : C} (r : Retract Y X) [InternallyProjective X] : InternallyProjective Y :=
  ⟨isInternallyProjective.prop_of_retract r (isInternallyProjective.prop_of_is _)⟩

end CategoryTheory.InternallyProjective
