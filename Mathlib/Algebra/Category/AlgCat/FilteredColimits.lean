/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.AlgCat.Basic
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!

# Filtered colimits in the category of `R`-algebras

In this file we show that the forgetful functor from `R`-algebras to rings
creates filtered colimits.
-/

public section

universe w v u

open CategoryTheory Limits

variable {R : Type u} [CommRing R] {J : Type*} [Category* J] {F : J ⥤ AlgCat.{v} R}
  [PreservesColimitsOfShape J (forget RingCat.{v})]

section

variable {c : Cocone (F ⋙ forget₂ _ RingCat)} [IsFilteredOrEmpty J]

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation): The algebra instance on the cocone point of the underlying diagram of rings
is induced from the `j`-th inclusion map. Any choice of `j` gives a propositionally equal algebra
instance. -/
private abbrev AlgCat.algebraOfIsFiltered (hc : IsColimit c) (j : J) : Algebra R c.pt :=
  (c.ι.app j).hom.comp (algebraMap R (F.obj j)) |>.toAlgebra' <| by
    intro r x
    obtain ⟨k, hjk, y, rfl⟩ := Concrete.exists_hom_ι_eq_of_isColimit _ hc x j
    simp [← dsimp% c.w hjk, ← dsimp% (c.ι.app k).hom.map_mul, Algebra.commutes']

set_option backward.isDefEq.respectTransparency false in
/-- The cocone of the underlying diagram of rings lifted to `AlgCat R`. The algebra instance
on the cocone point is induced from the `j`-th inclusion map. -/
private def AlgCat.coconeOfIsFiltered (hc : IsColimit c) (j : J) : Cocone F where
  pt :=
    letI : Algebra R c.pt := algebraOfIsFiltered hc j
    AlgCat.of R c.pt
  ι.app k := by
    letI : Algebra R c.pt := algebraOfIsFiltered hc j
    refine AlgCat.ofHom { __ := (c.ι.app k).hom, commutes' r := ?_ }
    simp [RingHom.algebraMap_toAlgebra', ← c.w (IsFiltered.leftToMax j k),
      ← c.w (IsFiltered.rightToMax j k)]
  ι.naturality k k' f := by
    ext
    exact congr($(c.ι.naturality f).hom _)

set_option backward.isDefEq.respectTransparency false in
/-- The lifted cocone is colimiting. -/
private def AlgCat.isColimitCoconeOfIsFiltered (hc : IsColimit c) (j : J) :
    IsColimit (AlgCat.coconeOfIsFiltered hc j) where
  desc s := by
    letI : Algebra R c.pt := algebraOfIsFiltered hc j
    refine AlgCat.ofHom { __ := (hc.desc <| Functor.mapCocone _ s).hom, commutes' r := ?_ }
    simp [RingHom.algebraMap_toAlgebra', ← ConcreteCategory.comp_apply]
  fac s k := by
    ext
    apply congr($(hc.fac _ _) _)
  uniq s m hm := by
    ext
    refine congr($(hc.uniq (Functor.mapCocone _ s) ((forget₂ _ _).map m) fun j ↦ ?_) _)
    ext
    exact congr($(hm _) _)

end

@[no_expose] noncomputable instance [IsFiltered J] :
    CreatesColimitsOfShape J (forget₂ (AlgCat.{v} R) RingCat.{v}) where
  CreatesColimit := createsColimitOfReflectsIso fun _ hc ↦
    ⟨⟨AlgCat.coconeOfIsFiltered hc IsFiltered.nonempty.some, Iso.refl _⟩,
      AlgCat.isColimitCoconeOfIsFiltered _ _⟩

noncomputable instance [IsFiltered J] [HasColimitsOfShape J RingCat.{v}] :
    HasColimitsOfShape J (AlgCat.{v} R) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (forget₂ _ RingCat.{v})

instance : PreservesFilteredColimits (forget₂ (AlgCat.{v} R) RingCat.{v}) where
  preserves_filtered_colimits _ := inferInstance

instance : PreservesFilteredColimits (forget (AlgCat.{v} R)) :=
  Limits.comp_preservesFilteredColimits (forget₂ _ _) (forget RingCat.{v})
