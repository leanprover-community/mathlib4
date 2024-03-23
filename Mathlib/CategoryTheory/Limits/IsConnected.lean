/-
Copyright (c) 2024 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.IsConnected

/-!
# Colimits of connected index categories

This file proves that a category $\mathsf{C}$ is connected if and only if `colim F` is a singleton,
where `F.obj _ = PUnit` (in a `Type _` category).

See `connected_iff_colimit_const_pUnit_iso_pUnit` for the proof of this characterization and
`unitValuedFunctor` for the definition of the constant functor used in the statement.

## Tags

unit-valued, singleton, colimit
-/

universe v u w

namespace CategoryTheory.Limits.Types

open CategoryTheory.Limits
open CategoryTheory.Limits.Types

variable (C : Type u) [Category.{v} C]

/-- The functor mapping every object to `PUnit`. -/
def unitValuedFunctor : C ⥤ Type w := (Functor.const C).obj PUnit.{w + 1}

instance instSubsingletonColimitPUnit
    [IsPreconnected C] [HasColimit (unitValuedFunctor.{v, u, w} C)] :
    Subsingleton (colimit (unitValuedFunctor.{v, u, w} C)) where
  allEq a b := by
    obtain ⟨c, ⟨⟩, rfl⟩ :=
      jointly_surjective_of_isColimit (colimit.isColimit (unitValuedFunctor C)) a
    obtain ⟨d, ⟨⟩, rfl⟩ :=
      jointly_surjective_of_isColimit (colimit.isColimit (unitValuedFunctor C)) b
    apply constant_of_preserves_morphisms (colimit.ι (unitValuedFunctor C) · PUnit.unit)
    exact fun c d f => colimit_sound'' f rfl

/-- Given a connected index category, the colimit of the constant unit-valued functor is `PUnit`. -/
noncomputable def colimitConstPUnitIsoPUnit
    [IsConnected C] [HasColimit (unitValuedFunctor.{v, u, w} C)] :
    colimit (unitValuedFunctor.{v, u, w} C) ≅ PUnit.{w + 1} where
  hom := fun _ => PUnit.unit
  inv := fun _ => colimit.ι (unitValuedFunctor.{v, u, w} C) Classical.ofNonempty PUnit.unit

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
theorem connected_iff_colimit_const_pUnit_iso_pUnit :
    IsConnected C ↔ Nonempty (colimit (unitValuedFunctor.{v, u, max v u w} C) ≅ PUnit) := by
  refine ⟨fun _ => ⟨colimitConstPUnitIsoPUnit.{v, u, max v u w} C⟩, fun ⟨h⟩ => ?_⟩
  have : Nonempty C := nonempty_of_nonempty_colimit <| Nonempty.map h.inv inferInstance
  refine zigzag_isConnected <| fun c d => ?_
  refine zigzag_of_eqvGen_quot_rel _ (unitValuedFunctor C) ⟨c, PUnit.unit⟩ ⟨d, PUnit.unit⟩ ?_
  exact colimit_eq <| h.toEquiv.injective rfl

end CategoryTheory.Limits.Types
