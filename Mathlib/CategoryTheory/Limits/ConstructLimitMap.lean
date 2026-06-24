/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Comma.Final
public import Mathlib.CategoryTheory.Limits.ConeCategory
public import Mathlib.CategoryTheory.Presentable.Basic

/-!
# Constructing morphisms between (co)filtered (co)limits levelwise

Let `D : I ⥤ C` and `D' : I' ⥤ C` be cofiltered diagrams with limit cones `c` and `c'` and let
`f : c.pt ⟶ c'.pt` be an arbitrary morphism between the limits. We show that if every `D'.obj i'`
is cocompact relative to `D`, i.e. `yoneda.obj (D'.obj i')` preserves the colimit of `D.op`,
then `f` is induced by a natural transformation of diagrams: there exists a cofiltered category
`J` with initial functors `G : J ⥤ I` and `G' : J ⥤ I'` and a natural transformation
`g : G ⋙ D ⟶ G' ⋙ D'` inducing `f` on limits. See
`CategoryTheory.Limits.exists_eq_isLimitMap_of_preservesColimit_yoneda`.

Dually, a morphism between filtered colimits, where every object of the source diagram is
compact relative to the target diagram, is induced by a natural transformation after
restricting along final functors. See
`CategoryTheory.Limits.exists_eq_isColimitMap_of_preservesColimit_coyoneda`.

## Implementation

In the limit case, the category `J` is the comma category `Comma L R` of the functors
`L : I ⥤ Under c.pt` and `R : I' ⥤ Under c.pt` induced by the cones: its objects are triples
`(i, i', φ)` of a morphism `φ : D.obj i ⟶ D'.obj i'` satisfying
`c.π.app i ≫ φ = f ≫ c'.π.app i'`. The relative finality results for comma categories from
`Mathlib/CategoryTheory/Comma/Final.lean` do the main work.
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits

@[expose] public section

variable {C : Type u₁} [Category.{v₁} C]
  {I : Type u₂} {I' : Type u₃} [Category.{v₂} I] [Category.{v₃} I']
  {D : I ⥤ C} {D' : I' ⥤ C}

namespace ConstructLimitMap

variable {c : Cone D} {c' : Cone D'} (hc : IsLimit c) (hc' : IsLimit c') (f : c.pt ⟶ c'.pt)

/-- The diagram `D` lifted to the under category of the cone point of `c`. This is the left leg
of the comma category indexing the levelwise construction of `f`. -/
abbrev left (c : Cone D) : I ⥤ Under c.pt :=
  c.toStructuredArrow ⋙ StructuredArrow.toUnder c.pt D

/-- The diagram `D'` lifted along `f` to the under category of the cone point of `c`. This is
the right leg of the comma category indexing the levelwise construction of `f`. -/
abbrev right (c' : Cone D') (f : c.pt ⟶ c'.pt) : I' ⥤ Under c.pt :=
  (c'.toStructuredArrow ⋙ StructuredArrow.toUnder c'.pt D') ⋙ Under.map f

set_option backward.isDefEq.respectTransparency false in
/-- The tautological natural transformation on the comma category of `f`-compatible squares,
inducing `f` on limits (see `ConstructLimitMap.eq_isLimitMap`). -/
@[simps]
def map : Comma.fst (left c) (right c' f) ⋙ D ⟶ Comma.snd (left c) (right c' f) ⋙ D' where
  app A := A.hom.right
  naturality _ _ u := by simpa using congrArg CommaMorphism.right u.w

set_option backward.isDefEq.respectTransparency false in
/-- A morphism `f` between cone points is induced by the tautological natural transformation
`ConstructLimitMap.map` on the comma category of `f`-compatible squares. -/
lemma eq_isLimitMap [(Comma.snd (left c) (right c' f)).Initial] :
    f = IsLimit.map (c.whisker (Comma.fst (left c) (right c' f)))
      ((Functor.Initial.isLimitWhiskerEquiv (Comma.snd (left c) (right c' f)) c').symm hc')
      (map f) := by
  apply ((Functor.Initial.isLimitWhiskerEquiv _ _).symm hc').hom_ext
  intro A
  rw [IsLimit.map_π]
  exact (Under.w A.hom).symm

variable [IsCofiltered I]
  [∀ i : I', PreservesColimit D.op (yoneda.obj (D'.obj i))]

set_option backward.isDefEq.respectTransparency false in
include hc in
lemma isCofiltered_costructuredArrow (i' : I') :
    IsCofiltered (CostructuredArrow (left c) ((right c' f).obj i')) := by
  refine isCofiltered_costructuredArrow_of_isCofiltered_of_exists _ _ ?_ ?_
  · obtain ⟨j, p, hp⟩ := exists_hom_of_preservesColimit_yoneda hc (f ≫ c'.π.app i')
    exact ⟨j, ⟨Under.homMk p hp⟩⟩
  · intro a s s'
    obtain ⟨j, t, ht⟩ := exists_eq_of_preservesColimit_yoneda_self hc
      (show D.obj a ⟶ D'.obj i' from s.right) (show D.obj a ⟶ D'.obj i' from s'.right)
      ((Under.w s).trans (Under.w s').symm)
    exact ⟨j, t, by ext; simpa using ht⟩

include hc in
lemma initial_snd : (Comma.snd (left c) (right c' f)).Initial := by
  have (i' : I') : IsConnected (CostructuredArrow (left c) ((right c' f).obj i')) :=
    have := isCofiltered_costructuredArrow hc f i'
    IsCofiltered.isConnected _
  exact Comma.initial_snd_of_isConnected_costructuredArrow _ _

variable [IsCofiltered I']

include hc in
lemma isCofiltered : IsCofiltered (Comma (left c) (right c' f)) := by
  have := isCofiltered_costructuredArrow hc f
  exact Comma.isCofiltered_of_isCofiltered_costructuredArrow _ _

include hc in
lemma initial_fst : (Comma.fst (left c) (right c' f)).Initial := by
  have := isCofiltered_costructuredArrow hc f
  exact Comma.initial_fst_of_isCofiltered_costructuredArrow _ _

end ConstructLimitMap

open ConstructLimitMap in
set_option backward.isDefEq.respectTransparency false in
/-- A morphism `f` between cofiltered limits, where every object of the target diagram is
cocompact relative to the source diagram, is induced by a natural transformation of diagrams
after restricting both index categories along initial functors from a common cofiltered
category. -/
lemma Limits.exists_eq_isLimitMap_of_preservesColimit_yoneda
    {c : Cone D} {c' : Cone D'} (hc : IsLimit c) (hc' : IsLimit c') (f : c.pt ⟶ c'.pt)
    [IsCofiltered I] [IsCofiltered I']
    [∀ i : I', PreservesColimit D.op (yoneda.obj (D'.obj i))] :
    ∃ (J : Type (max u₂ u₃ v₁))
      (_ : Category.{max v₂ v₃} J) (_ : IsCofiltered J) (G : J ⥤ I) (G' : J ⥤ I')
      (_ : G.Initial) (_ : G'.Initial) (g : G ⋙ D ⟶ G' ⋙ D'),
      f = IsLimit.map (c.whisker _) ((Functor.Initial.isLimitWhiskerEquiv _ _).symm hc') g := by
  have := ConstructLimitMap.initial_fst hc f
  have := ConstructLimitMap.initial_snd hc f
  exact ⟨_, inferInstance, ConstructLimitMap.isCofiltered hc f, _, _, inferInstance, inferInstance,
    ConstructLimitMap.map f, ConstructLimitMap.eq_isLimitMap hc' f⟩

namespace ConstructColimitMap

variable {c : Cocone D} {c' : Cocone D'} (hc : IsColimit c) (hc' : IsColimit c')
  (f : c.pt ⟶ c'.pt)

/-- The diagram `D` lifted along `f` to the over category of the cocone point of `c'`. This is
the left leg of the comma category indexing the levelwise construction of `f`. -/
abbrev left (c : Cocone D) (f : c.pt ⟶ c'.pt) : I ⥤ Over c'.pt :=
  (c.toCostructuredArrow ⋙ CostructuredArrow.toOver D c.pt) ⋙ Over.map f

/-- The diagram `D'` lifted to the over category of the cocone point of `c'`. This is the right
leg of the comma category indexing the levelwise construction of `f`. -/
abbrev right (c' : Cocone D') : I' ⥤ Over c'.pt :=
  c'.toCostructuredArrow ⋙ CostructuredArrow.toOver D' c'.pt

set_option backward.isDefEq.respectTransparency false in
/-- The tautological natural transformation on the comma category of `f`-compatible squares,
inducing `f` on colimits (see `ConstructColimitMap.eq_isColimitMap`). -/
@[simps]
def map : Comma.fst (left c f) (right c') ⋙ D ⟶ Comma.snd (left c f) (right c') ⋙ D' where
  app A := A.hom.left
  naturality _ _ u := by simpa using congrArg CommaMorphism.left u.w

set_option backward.isDefEq.respectTransparency false in
/-- A morphism `f` between cocone points is induced by the tautological natural transformation
`ConstructColimitMap.map` on the comma category of `f`-compatible squares. -/
lemma eq_isColimitMap [(Comma.fst (left c f) (right c')).Final] :
    f = IsColimit.map
      ((Functor.Final.isColimitWhiskerEquiv (Comma.fst (left c f) (right c')) c).symm hc)
      (c'.whisker (Comma.snd (left c f) (right c'))) (map f) := by
  apply ((Functor.Final.isColimitWhiskerEquiv _ _).symm hc).hom_ext
  intro A
  rw [IsColimit.ι_map]
  exact (Over.w A.hom).symm

variable [IsFiltered I']
  [∀ i : I, PreservesColimit D' (coyoneda.obj (.op (D.obj i)))]

set_option backward.isDefEq.respectTransparency false in
include hc' in
lemma isFiltered_structuredArrow (i : I) :
    IsFiltered (StructuredArrow ((left c f).obj i) (right c')) := by
  refine isFiltered_structuredArrow_of_isFiltered_of_exists _ _ ?_ ?_
  · obtain ⟨j, p, hp⟩ := exists_hom_of_preservesColimit_coyoneda hc' (c.ι.app i ≫ f)
    exact ⟨j, ⟨Over.homMk p hp⟩⟩
  · intro a s s'
    obtain ⟨j, t, ht⟩ := exists_eq_of_preservesColimit_coyoneda_self hc'
      (show D.obj i ⟶ D'.obj a from s.left) (show D.obj i ⟶ D'.obj a from s'.left)
      ((Over.w s).trans (Over.w s').symm)
    exact ⟨j, t, by ext; simpa using ht⟩

include hc' in
lemma final_fst : (Comma.fst (left c f) (right c')).Final := by
  have (i : I) : IsConnected (StructuredArrow ((left c f).obj i) (right c')) :=
    have := isFiltered_structuredArrow hc' f i
    IsFiltered.isConnected _
  exact Comma.final_fst_of_isConnected_structuredArrow _ _

variable [IsFiltered I]

include hc' in
lemma isFiltered : IsFiltered (Comma (left c f) (right c')) := by
  have := isFiltered_structuredArrow hc' f
  exact Comma.isFiltered_of_isFiltered_structuredArrow _ _

include hc' in
lemma final_snd : (Comma.snd (left c f) (right c')).Final := by
  have := isFiltered_structuredArrow hc' f
  exact Comma.final_snd_of_isFiltered_structuredArrow _ _

end ConstructColimitMap

open ConstructColimitMap in
set_option backward.isDefEq.respectTransparency false in
/-- A morphism `f` between filtered colimits, where every object of the source diagram is
compact relative to the target diagram, is induced by a natural transformation of diagrams
after restricting both index categories along final functors from a common filtered
category. -/
lemma Limits.exists_eq_isColimitMap_of_preservesColimit_coyoneda
    {c : Cocone D} {c' : Cocone D'} (hc : IsColimit c) (hc' : IsColimit c') (f : c.pt ⟶ c'.pt)
    [IsFiltered I] [IsFiltered I']
    [∀ i : I, PreservesColimit D' (coyoneda.obj (.op (D.obj i)))] :
    ∃ (J : Type (max u₂ u₃ v₁))
      (_ : Category.{max v₂ v₃} J) (_ : IsFiltered J) (G : J ⥤ I) (G' : J ⥤ I')
      (_ : G.Final) (_ : G'.Final) (g : G ⋙ D ⟶ G' ⋙ D'),
      f = IsColimit.map ((Functor.Final.isColimitWhiskerEquiv _ _).symm hc) (c'.whisker _) g := by
  have := ConstructColimitMap.final_fst hc' f
  have := ConstructColimitMap.final_snd hc' f
  exact ⟨_, inferInstance, ConstructColimitMap.isFiltered hc' f, _, _, inferInstance, inferInstance,
    ConstructColimitMap.map f, ConstructColimitMap.eq_isColimitMap hc f⟩

end

end CategoryTheory
