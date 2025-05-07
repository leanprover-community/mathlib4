/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.CochainComplexMinus

/-!
# Properties of homological complexes

-/

namespace CategoryTheory

open Limits

namespace ObjectProperty

variable {C : Type*} [Category C] [HasZeroMorphisms C]
  (P : ObjectProperty C)

def homologicalComplex {ι : Type*} (c : ComplexShape ι) :
    ObjectProperty (HomologicalComplex C c) :=
  fun K ↦ ∀ i, P (K.X i)

lemma homologicalComplex_iff {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex C c) :
    P.homologicalComplex c K ↔ ∀ i, P (K.X i) := Iff.rfl

instance {ι : Type*} (c : ComplexShape ι) [P.IsClosedUnderIsomorphisms] :
    (P.homologicalComplex c).IsClosedUnderIsomorphisms where
  of_iso e h n := P.prop_of_iso ((HomologicalComplex.eval C c n).mapIso e) (h n)

abbrev cochainComplex : ObjectProperty (CochainComplex C ℤ) :=
    P.homologicalComplex (.up ℤ)

def cochainComplexMinus : ObjectProperty (CochainComplex C ℤ) :=
    P.cochainComplex ⊓ CochainComplex.minus C

instance [P.IsClosedUnderIsomorphisms] :
    P.cochainComplexMinus.IsClosedUnderIsomorphisms := by
  dsimp [cochainComplexMinus]
  infer_instance

end ObjectProperty

end CategoryTheory
