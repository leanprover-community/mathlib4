/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.Final

/-!
# Canonical colimits, or functors that are dense at an object

Given a functor `F : C ⥤ D` and `Y : D`, we say that `F` is dense at `Y` (`F.DenseAt Y`),
if `Y` identifies to the colimit of all `F.obj X` for `X : C`
and `f : F.obj X ⟶ Y`, i.e. `Y` identifies to the colimit of
the obvious functor `CostructuredArrow F Y ⥤ D`. In some references,
it is also said that `Y` is a canonical colimit relatively to `F`.
While `F.DenseAt Y` contains data, we also introduce the
corresponding property `isDenseAt F` of objects of `D`.

## TODO

* formalize dense subcategories
* show the presheaves of types are canonical colimits relatively
  to the Yoneda embedding

## References
* https://ncatlab.org/nlab/show/dense+functor

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  (F : C ⥤ D)

namespace Functor

/-- A functor `F : C ⥤ D` is dense at `Y : D` if the obvious natural transformation
`F ⟶ F ⋙ 𝟭 D` makes `𝟭 D` a pointwise left Kan extension of `F` along itself at `Y`,
i.e. `Y` identifies to the colimit of the obvious functor `CostructuredArrow F Y ⥤ D`. -/
abbrev DenseAt (Y : D) : Type max u₁ u₂ v₂ :=
  (Functor.LeftExtension.mk (𝟭 D) F.rightUnitor.inv).IsPointwiseLeftKanExtensionAt Y

/-- `F` is dense at `Y` if `Y` identifies to the colimit of the obvious functor
`CostructuredArrow F Y ⥤ D`. -/
def denseAtEquiv (Y : D) :
    F.DenseAt Y ≃ IsColimit ((LeftExtension.mk (𝟭 D) F.rightUnitor.inv).coconeAt Y) :=
  .refl _

variable {F} {Y : D} (hY : F.DenseAt Y)

/-- If `F : C ⥤ D` is dense at `Y : D`, then it is also at `Y'`
if `Y` and `Y'` are isomorphic. -/
def DenseAt.ofIso {Y' : D} (e : Y ≅ Y') : F.DenseAt Y' :=
  LeftExtension.isPointwiseLeftKanExtensionAtOfIso' _ hY e

set_option backward.defeqAttrib.useBackward true in
/-- If `F : C ⥤ D` is dense at `Y : D`, and `G` is a functor that is isomorphic to `F`,
then `G` is also dense at `Y`. -/
def DenseAt.ofNatIso {G : C ⥤ D} (e : F ≅ G) : G.DenseAt Y :=
  (IsColimit.equivOfNatIsoOfIso
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerLeft _ e) _ _
      (by exact Cocone.ext (Iso.refl _)))
    (hY.whiskerEquivalence (CostructuredArrow.mapNatIso e.symm))

/-- If the canonical functor `CostructuredArrow (G ≫ F) Y ⥤ CostructuredArrow F Y` is final, then
`G ⋙ F` is dense at `Y` if and only if `F` is dense at `Y`. -/
noncomputable def DenseAt.precompEquivOfFinal
    {C' : Type*} [Category* C'] (G : C' ⥤ C) [(CostructuredArrow.pre G F Y).Final] :
    (G ⋙ F).DenseAt Y ≃ F.DenseAt Y :=
  Functor.Final.isColimitWhiskerEquiv (CostructuredArrow.pre G F Y)
    ((LeftExtension.mk (𝟭 D) F.rightUnitor.inv).coconeAt Y)

/-- If `F : C ⥤ D` is dense at `Y : D`, then so is `G ⋙ F` if
the canonical functor `CostructuredArrow (G ≫ F) Y ⥤ CostructuredArrow F Y` is final.
This holds in particular if `G` is an equivalence. -/
noncomputable def DenseAt.precompOfFinal
    {C' : Type*} [Category* C'] (G : C' ⥤ C) [(CostructuredArrow.pre G F Y).Final] :
    (G ⋙ F).DenseAt Y :=
  (DenseAt.precompEquivOfFinal G).symm hY

@[deprecated (since := "2025-12-17")]
alias DenseAt.precompEquivalence := DenseAt.precompOfFinal

set_option backward.defeqAttrib.useBackward true in
/-- If `F : C ⥤ D` is dense at `Y : D` and `G : D ⥤ D'` is an equivalence,
then `F ⋙ G` is dense at `G.obj Y`. -/
noncomputable def DenseAt.postcompEquivalence
    {D' : Type*} [Category* D'] (G : D ⥤ D') [G.IsEquivalence] :
    (F ⋙ G).DenseAt (G.obj Y) :=
  IsColimit.ofWhiskerEquivalence (CostructuredArrow.post F G Y).asEquivalence
    (IsColimit.ofIsoColimit ((isColimitOfPreserves G hY)) (Cocone.ext (Iso.refl _)))

variable (F) in
/-- Given a functor `F : C ⥤ D`, this is the property of objects `Y : D` such
that `F` is dense at `Y`. -/
def isDenseAt : ObjectProperty D :=
  fun Y ↦ Nonempty (F.DenseAt Y)

lemma isDenseAt_eq_isPointwiseLeftKanExtensionAt :
    F.isDenseAt =
      (Functor.LeftExtension.mk (𝟭 D) F.rightUnitor.inv).isPointwiseLeftKanExtensionAt :=
  rfl

lemma isDenseAt_iff {X : D} :
    F.isDenseAt X ↔ Nonempty (IsColimit <| (LeftExtension.mk (𝟭 D) F.rightUnitor.inv).coconeAt X) :=
  .rfl

instance : F.isDenseAt.IsClosedUnderIsomorphisms := by
  rw [isDenseAt_eq_isPointwiseLeftKanExtensionAt]
  infer_instance

lemma congr_isDenseAt {G : C ⥤ D} (e : F ≅ G) :
    F.isDenseAt = G.isDenseAt := by
  ext X
  exact ⟨fun ⟨h⟩ ↦ ⟨h.ofNatIso e⟩, fun ⟨h⟩ ↦ ⟨h.ofNatIso e.symm⟩⟩

lemma IsDenseAt.iff_of_final {C' : Type*} [Category* C'] (G : C' ⥤ C)
    [(CostructuredArrow.pre G F Y).Final] :
    (G ⋙ F).isDenseAt Y ↔ F.isDenseAt Y :=
  (DenseAt.precompEquivOfFinal G).nonempty_congr

lemma IsDenseAt.of_final {C' : Type*} [Category* C'] (G : C' ⥤ C)
    [(CostructuredArrow.pre G F Y).Final] (hY : F.isDenseAt Y) :
    (G ⋙ F).isDenseAt Y :=
  (iff_of_final G).mpr hY

end Functor

end CategoryTheory
