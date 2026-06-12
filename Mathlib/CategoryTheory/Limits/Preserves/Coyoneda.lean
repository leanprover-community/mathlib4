/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Yoneda

/-!
# Morphisms into colimits preserved by coyoneda

Let `D : J ⥤ C` be a diagram with colimit cocone `c` and let `X : C` be an object such that
`coyoneda.obj (.op X)` preserves the colimit of `D`. This holds for example if `X` is finitely
presentable and `J` is a small filtered category. We show:

* `exists_hom_of_preservesColimit_coyoneda`: every morphism `X ⟶ c.pt` factors through a
  component `c.ι.app j`.
* `exists_eq_of_preservesColimit_coyoneda`: if `J` is filtered, two morphisms `X ⟶ D.obj i` and
  `X ⟶ D.obj j` that agree after composing into `c.pt` are identified at a later stage of the
  diagram.
* `exists_eq_of_preservesColimit_coyoneda_self`: the variant of the previous result for two
  morphisms into the same object `D.obj i`.

We also prove the dual results (`exists_hom_of_preservesColimit_yoneda` etc.) for morphisms out
of limits of diagrams `D : J ⥤ C` such that `yoneda.obj X` preserves the colimit of `D.op`.
-/

namespace CategoryTheory.Limits

public section

/-- A morphism from `X` into the colimit of `D` factors through a component of the colimit
cocone if `coyoneda.obj (.op X)` preserves the colimit of `D`.

The assumption on `X` is in particular satisfied if `X` is finitely presentable
and `J` is a small filtered category. -/
lemma exists_hom_of_preservesColimit_coyoneda {C : Type*} [Category* C] {J : Type*}
    [Category* J] {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c) {X : C}
    [PreservesColimit D (coyoneda.obj (.op X))] (f : X ⟶ c.pt) :
    ∃ (j : J) (p : X ⟶ D.obj j), p ≫ c.ι.app j = f :=
  Types.jointly_surjective_of_isColimit (isColimitOfPreserves (coyoneda.obj (.op X)) hc) f

/-- Two morphisms from `X` into objects of a filtered diagram `D` that agree in the colimit of
`D` are identified at a later stage of the diagram if `coyoneda.obj (.op X)` preserves the
colimit of `D`. -/
lemma exists_eq_of_preservesColimit_coyoneda {C : Type*} [Category* C] {J : Type*}
    [Category* J] [IsFiltered J]
    {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c) {X : C}
    [PreservesColimit D (coyoneda.obj (.op X))]
    {i j : J} (f : X ⟶ D.obj i) (g : X ⟶ D.obj j) (h : f ≫ c.ι.app i = g ≫ c.ι.app j) :
    ∃ (k : J) (u : i ⟶ k) (v : j ⟶ k), f ≫ D.map u = g ≫ D.map v :=
  (Types.FilteredColimit.isColimit_eq_iff _ (isColimitOfPreserves (coyoneda.obj (.op X)) hc)).mp h

/-- The variant of `exists_eq_of_preservesColimit_coyoneda` for two morphisms into the same
object of the diagram, equalized by a single morphism of the diagram. -/
lemma exists_eq_of_preservesColimit_coyoneda_self {C : Type*} [Category* C] {J : Type*}
    [Category* J] [IsFiltered J] {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c) {X : C}
    [PreservesColimit D (coyoneda.obj (.op X))]
    {i : J} (f g : X ⟶ D.obj i) (h : f ≫ c.ι.app i = g ≫ c.ι.app i) :
    ∃ (j : J) (a : i ⟶ j), f ≫ D.map a = g ≫ D.map a :=
  (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves (coyoneda.obj (.op X)) hc) f g).mp h

/-- A morphism from the limit of `D` to `X` factors through a component of the limit cone if
`yoneda.obj X` preserves the colimit of `D.op`. -/
lemma exists_hom_of_preservesColimit_yoneda {C : Type*} [Category* C] {J : Type*}
    [Category* J] {D : J ⥤ C} {c : Cone D} (hc : IsLimit c) {X : C}
    [PreservesColimit D.op (yoneda.obj X)] (f : c.pt ⟶ X) :
    ∃ (j : J) (p : D.obj j ⟶ X), c.π.app j ≫ p = f := by
  obtain ⟨j, p, hp⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (yoneda.obj X) hc.op) f
  exact ⟨j.unop, p, hp⟩

/-- Two morphisms into `X` from objects of a cofiltered diagram `D` that agree on the limit of
`D` are identified at an earlier stage of the diagram if `yoneda.obj X` preserves the colimit
of `D.op`. -/
lemma exists_eq_of_preservesColimit_yoneda {C : Type*} [Category* C] {J : Type*}
    [Category* J] [IsCofiltered J]
    {D : J ⥤ C} {c : Cone D} (hc : IsLimit c) {X : C}
    [PreservesColimit D.op (yoneda.obj X)]
    {i j : J} (f : D.obj i ⟶ X) (g : D.obj j ⟶ X) (h : c.π.app i ≫ f = c.π.app j ≫ g) :
    ∃ (k : J) (u : k ⟶ i) (v : k ⟶ j), D.map u ≫ f = D.map v ≫ g := by
  obtain ⟨k, u, v, huv⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff _ (isColimitOfPreserves (yoneda.obj X) hc.op)).mp h
  exact ⟨k.unop, u.unop, v.unop, huv⟩

/-- The variant of `exists_eq_of_preservesColimit_yoneda` for two morphisms from the same
object of the diagram, equalized by a single morphism of the diagram. -/
lemma exists_eq_of_preservesColimit_yoneda_self {C : Type*} [Category* C] {J : Type*}
    [Category* J] [IsCofiltered J] {D : J ⥤ C} {c : Cone D} (hc : IsLimit c) {X : C}
    [PreservesColimit D.op (yoneda.obj X)]
    {i : J} (f g : D.obj i ⟶ X) (h : c.π.app i ≫ f = c.π.app i ≫ g) :
    ∃ (j : J) (a : j ⟶ i), D.map a ≫ f = D.map a ≫ g := by
  obtain ⟨j, a, ha⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves (yoneda.obj X) hc.op) f g).mp h
  exact ⟨j.unop, a.unop, ha⟩

end

end CategoryTheory.Limits
