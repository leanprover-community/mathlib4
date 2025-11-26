/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# The category of (commutative) (additive) groups has a zero object.

`AddCommGroup` also has zero morphisms. For definitional reasons, we infer this from preadditivity
rather than from the existence of a zero object.
-/

@[expose] public section


open CategoryTheory

open CategoryTheory.Limits

universe u

namespace GrpCat

@[to_additive]
theorem isZero_of_subsingleton (G : GrpCat) [Subsingleton G] : IsZero G := by
  refine ⟨fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩⟩
  · ext x
    have : x = 1 := Subsingleton.elim _ _
    rw [this, map_one, map_one]
  · ext
    subsingleton

@[to_additive AddGrpCat.hasZeroObject]
instance : HasZeroObject GrpCat :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩

@[to_additive]
lemma subsingleton_of_isZero {G : GrpCat} (h : Limits.IsZero G) :
    Subsingleton G :=
  (h.iso (isZero_of_subsingleton <| .of PUnit)).groupIsoToMulEquiv.subsingleton

@[to_additive]
lemma isZero_iff_subsingleton {G : GrpCat} : Limits.IsZero G ↔ Subsingleton G :=
  ⟨fun h ↦ subsingleton_of_isZero h, fun _ ↦ isZero_of_subsingleton G⟩

end GrpCat

namespace CommGrpCat

@[to_additive]
theorem isZero_of_subsingleton (G : CommGrpCat) [Subsingleton G] : IsZero G := by
  refine ⟨fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩⟩
  · ext x
    have : x = 1 := Subsingleton.elim _ _
    rw [this, map_one, map_one]
  · ext
    subsingleton

@[to_additive AddCommGrpCat.hasZeroObject]
instance : HasZeroObject CommGrpCat :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩

@[to_additive]
lemma subsingleton_of_isZero {G : CommGrpCat} (h : Limits.IsZero G) :
    Subsingleton G :=
  (h.iso (isZero_of_subsingleton <| .of PUnit)).commGroupIsoToMulEquiv.subsingleton

@[to_additive]
lemma isZero_iff_subsingleton {G : CommGrpCat} : Limits.IsZero G ↔ Subsingleton G :=
  ⟨fun h ↦ subsingleton_of_isZero h, fun _ ↦ isZero_of_subsingleton G⟩

end CommGrpCat
