/-
Copyright (c) 2024 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.Limits.Creates

import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Conj

/-!
# Colimits of connected index categories

This file proves theorems about connected categories related to limits.

## Main definitions

See `unitValuedFunctor` for the definition of the constant functor used in the statement.

## Main theorems

* `connected_iff_colimit_const_pUnit_iso_pUnit` proves that a category $\mathsf{C}$ is connected if
  and only if `colim F` is a singleton, where `F.obj _ = PUnit` (in a `Type _` category).
* `isConnected_iff_of_final` proves that the domain of a final functor is connected if and only if
  the codomain is connected.

## Tags

unit-valued, singleton, colimit
-/

universe w v u

namespace CategoryTheory.Limits.Types

open CategoryTheory.Limits
open CategoryTheory.Limits.Types

variable (C : Type u) [Category.{v} C]

/-- The functor mapping every object to `PUnit`. -/
def unitValuedFunctor : C ⥤ Type w := (Functor.const C).obj PUnit.{w + 1}

instance instSubsingletonColimitPUnit
    [IsPreconnected C] [HasColimit (unitValuedFunctor.{w} C)] :
    Subsingleton (colimit (unitValuedFunctor.{w} C)) where
  allEq a b := by
    obtain ⟨c, ⟨⟩, rfl⟩ :=
      jointly_surjective_of_isColimit (colimit.isColimit (unitValuedFunctor C)) a
    obtain ⟨d, ⟨⟩, rfl⟩ :=
      jointly_surjective_of_isColimit (colimit.isColimit (unitValuedFunctor C)) b
    apply constant_of_preserves_morphisms (colimit.ι (unitValuedFunctor C) · PUnit.unit)
    exact fun c d f => colimit_sound'' f rfl

/-- Given a connected index category, the colimit of the constant unit-valued functor is `PUnit`. -/
noncomputable def colimitConstPUnitIsoPUnit
    [IsConnected C] [HasColimit (unitValuedFunctor.{w} C)] :
    colimit (unitValuedFunctor.{w} C) ≅ PUnit.{w + 1} where
  hom := fun _ => PUnit.unit
  inv := fun _ => colimit.ι (unitValuedFunctor.{w} C) Classical.ofNonempty PUnit.unit

/-- Let `F` be a `Type`-valued functor. If two elements `a : F c` and `b : F d` represent the same
element of `colimit F`, then `c` and `d` are related by a `Zigzag`. -/
theorem zigzag_of_eqvGen_quot_rel (F : C ⥤ Type w) (c d : Σ j, F.obj j)
    (h : EqvGen (Quot.Rel F) c d) : Zigzag c.1 d.1 := by
  induction h with
  | rel _ _ h => exact zigzag_of_hom <| Exists.choose h
  | refl _ => rfl
  | symm _ _ _ ih => exact zigzag_symmetric ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- An index category is connected iff the colimit of the constant singleton-valued functor is a
singleton. -/
theorem connected_iff_colimit_const_pUnit_iso_pUnit
    [HasColimit (unitValuedFunctor.{w} C)] :
    IsConnected C ↔ Nonempty (colimit (unitValuedFunctor.{w} C) ≅ PUnit) := by
  refine ⟨fun _ => ⟨colimitConstPUnitIsoPUnit.{w} C⟩, fun ⟨h⟩ => ?_⟩
  have : Nonempty C := nonempty_of_nonempty_colimit <| Nonempty.map h.inv inferInstance
  refine zigzag_isConnected <| fun c d => ?_
  refine zigzag_of_eqvGen_quot_rel _ (unitValuedFunctor C) ⟨c, PUnit.unit⟩ ⟨d, PUnit.unit⟩ ?_
  exact colimit_eq <| h.toEquiv.injective rfl

universe v₂ u₂
variable {C : Type u} {D: Type u₂} [Category.{v} C] [Category.{v₂} D]

/-- The source of a final functor is connected if and only if the target is connected. -/
theorem isConnected_iff_of_final (F : C ⥤ D) [CategoryTheory.Functor.Final F] :
    IsConnected C ↔ IsConnected D := by
  refine Iff.trans (connected_iff_colimit_const_pUnit_iso_pUnit.{max v u v₂ u₂} C) ?_
  refine Iff.trans ?_ (connected_iff_colimit_const_pUnit_iso_pUnit.{max v u v₂ u₂} D).symm
  exact Equiv.nonempty_congr <| Iso.isoCongrLeft <|
    CategoryTheory.Functor.Final.colimitIso F <| unitValuedFunctor.{max u v u₂ v₂} D

end CategoryTheory.Limits.Types
