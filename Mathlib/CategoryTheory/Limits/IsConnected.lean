/-
Copyright (c) 2024 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.HomCongr

/-!
# Colimits of connected index categories

This file proves two characterizations of connected categories by means of colimits.

## Characterization of connected categories by means of the unit-valued functor

First, it is proved that a category `C` is connected if and only if `colim F` is a singleton,
where `F : C ⥤ Type w` and `F.obj _ = PUnit` (for arbitrary `w`).

See `isConnected_iff_colimit_constPUnitFunctor_iso_pUnit` for the proof of this characterization and
`constPUnitFunctor` for the definition of the constant functor used in the statement. A formulation
based on `IsColimit` instead of `colimit` is given in `isConnected_iff_isColimit_pUnitCocone`.

The `if` direction is also available directly in several formulations:
For connected index categories `C`, `PUnit.{w}` is a colimit of the `constPUnitFunctor`, where `w`
is arbitrary. See `instHasColimitConstPUnitFunctor`, `isColimitPUnitCocone` and
`colimitConstPUnitIsoPUnit`.

## Final functors preserve connectedness of categories (in both directions)

`isConnected_iff_of_final` proves that the domain of a final functor is connected if and only if
its codomain is connected.

## Tags

unit-valued, singleton, colimit
-/

universe w v u

namespace CategoryTheory

namespace Limits.Types

variable (C : Type u) [Category.{v} C]

/-- The functor mapping every object to `PUnit`. -/
def constPUnitFunctor : C ⥤ Type w := (Functor.const C).obj PUnit.{w + 1}

/-- The cocone on `constPUnitFunctor` with cone point `PUnit`. -/
@[simps]
def pUnitCocone : Cocone (constPUnitFunctor.{w} C) where
  pt := PUnit
  ι := { app := fun _ => id }

/-- If `C` is connected, the cocone on `constPUnitFunctor` with cone point `PUnit` is a colimit
cocone. -/
noncomputable def isColimitPUnitCocone [IsConnected C] : IsColimit (pUnitCocone.{w} C) where
  desc s := s.ι.app Classical.ofNonempty
  fac s j := by
    ext ⟨⟩
    apply constant_of_preserves_morphisms (s.ι.app · PUnit.unit)
    intro X Y f
    exact congrFun (s.ι.naturality f).symm PUnit.unit
  uniq s m h := by
    ext ⟨⟩
    simp [← h Classical.ofNonempty]

instance instHasColimitConstPUnitFunctor [IsConnected C] : HasColimit (constPUnitFunctor.{w} C) :=
  ⟨_, isColimitPUnitCocone _⟩

instance instSubsingletonColimitPUnit
    [IsPreconnected C] [HasColimit (constPUnitFunctor.{w} C)] :
    Subsingleton (colimit (constPUnitFunctor.{w} C)) where
  allEq a b := by
    obtain ⟨c, ⟨⟩, rfl⟩ := jointly_surjective' a
    obtain ⟨d, ⟨⟩, rfl⟩ := jointly_surjective' b
    apply constant_of_preserves_morphisms (colimit.ι (constPUnitFunctor C) · PUnit.unit)
    exact fun c d f => colimit_sound f rfl

/-- Given a connected index category, the colimit of the constant unit-valued functor is `PUnit`. -/
noncomputable def colimitConstPUnitIsoPUnit [IsConnected C] :
    colimit (constPUnitFunctor.{w} C) ≅ PUnit.{w + 1} :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (isColimitPUnitCocone.{w} C)

/-- Let `F` be a `Type`-valued functor. If two elements `a : F c` and `b : F d` represent the same
element of `colimit F`, then `c` and `d` are related by a `Zigzag`. -/
theorem zigzag_of_eqvGen_colimitTypeRel (F : C ⥤ Type w) (c d : Σ j, F.obj j)
    (h : Relation.EqvGen F.ColimitTypeRel c d) : Zigzag c.1 d.1 := by
  induction h with
  | rel _ _ h => exact Zigzag.of_hom <| Exists.choose h
  | refl _ => exact Zigzag.refl _
  | symm _ _ _ ih => exact zigzag_symmetric ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

@[deprecated (since := "2025-06-22")] alias zigzag_of_eqvGen_quot_rel :=
  zigzag_of_eqvGen_colimitTypeRel

/-- An index category is connected iff the colimit of the constant singleton-valued functor is a
singleton. -/
theorem isConnected_iff_colimit_constPUnitFunctor_iso_pUnit
    [HasColimit (constPUnitFunctor.{w} C)] :
    IsConnected C ↔ Nonempty (colimit (constPUnitFunctor.{w} C) ≅ PUnit) := by
  refine ⟨fun _ => ⟨colimitConstPUnitIsoPUnit.{w} C⟩, fun ⟨h⟩ => ?_⟩
  have : Nonempty C := nonempty_of_nonempty_colimit <| Nonempty.map h.inv inferInstance
  refine zigzag_isConnected <| fun c d => ?_
  refine zigzag_of_eqvGen_colimitTypeRel _ (constPUnitFunctor C) ⟨c, PUnit.unit⟩ ⟨d, PUnit.unit⟩ ?_
  exact colimit_eq <| h.toEquiv.injective rfl

theorem isConnected_iff_isColimit_pUnitCocone :
    IsConnected C ↔ Nonempty (IsColimit (pUnitCocone.{w} C)) := by
  refine ⟨fun inst => ⟨isColimitPUnitCocone C⟩, fun ⟨h⟩ => ?_⟩
  let colimitCocone : ColimitCocone (constPUnitFunctor C) := ⟨pUnitCocone.{w} C, h⟩
  have : HasColimit (constPUnitFunctor.{w} C) := ⟨⟨colimitCocone⟩⟩
  simp only [isConnected_iff_colimit_constPUnitFunctor_iso_pUnit.{w} C]
  exact ⟨colimit.isoColimitCocone colimitCocone⟩

end Limits.Types

namespace Functor

open Limits.Types

universe v₂ u₂

variable {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D]

/-- The domain of a final functor is connected if and only if its codomain is connected. -/
theorem isConnected_iff_of_final (F : C ⥤ D) [F.Final] : IsConnected C ↔ IsConnected D := by
  rw [isConnected_iff_colimit_constPUnitFunctor_iso_pUnit.{max v u v₂ u₂} C,
    isConnected_iff_colimit_constPUnitFunctor_iso_pUnit.{max v u v₂ u₂} D]
  exact Equiv.nonempty_congr <| Iso.isoCongrLeft <|
    CategoryTheory.Functor.Final.colimitIso F <| constPUnitFunctor.{max u v u₂ v₂} D

/-- The domain of an initial functor is connected if and only if its codomain is connected. -/
theorem isConnected_iff_of_initial (F : C ⥤ D) [F.Initial] : IsConnected C ↔ IsConnected D := by
  rw [← isConnected_op_iff_isConnected C, ← isConnected_op_iff_isConnected D]
  exact isConnected_iff_of_final F.op

end Functor

section

variable (C : Type*) [Category C]

/-- Prove that a category is connected by supplying an explicit initial object. -/
lemma isConnected_of_isInitial {x : C} (h : Limits.IsInitial x) : IsConnected C := by
  letI : Nonempty C := ⟨x⟩
  apply isConnected_of_zigzag
  intro j₁ j₂
  use [x, j₂]
  simp only [List.isChain_cons_cons, List.isChain_singleton, and_true, ne_eq,
    reduceCtorEq, not_false_eq_true, List.getLast_cons, List.cons_ne_self, List.getLast_singleton]
  exact ⟨Zag.symm <| Zag.of_hom <| h.to _, Zag.of_hom <| h.to _⟩

/-- Prove that a category is connected by supplying an explicit terminal object. -/
lemma isConnected_of_isTerminal {x : C} (h : Limits.IsTerminal x) : IsConnected C := by
  letI : Nonempty C := ⟨x⟩
  apply isConnected_of_zigzag
  intro j₁ j₂
  use [x, j₂]
  simp only [List.isChain_cons_cons, List.isChain_singleton, and_true, ne_eq,
    reduceCtorEq, not_false_eq_true, List.getLast_cons, List.cons_ne_self, List.getLast_singleton]
  exact ⟨Zag.of_hom <| h.from _, Zag.symm <| Zag.of_hom <| h.from _⟩

-- note : it seems making the following two as instances breaks things, so these are lemmas.
lemma isConnected_of_hasInitial [Limits.HasInitial C] : IsConnected C :=
  isConnected_of_isInitial C Limits.initialIsInitial

lemma isConnected_of_hasTerminal [Limits.HasTerminal C] : IsConnected C :=
  isConnected_of_isTerminal C Limits.terminalIsTerminal

end

end CategoryTheory
