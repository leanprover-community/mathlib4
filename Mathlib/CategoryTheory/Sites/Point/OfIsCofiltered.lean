/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ShrinkYoneda
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Alternative constructor for points

Let `J` be a Grothendieck topology on a category `C`. We provide a constructor
`Point.ofIsCofiltered` for points for `J` which takes as inputs:
- a functor `p : N ⥤ C` where `N` is cofiltered and initially small
- the assumption that for any covering sieve `R` of `X`,
  any morphism `f : p.obj U ⟶ X`, there exists a morphism `g : Y ⟶ X` in `R`,
  a morphism `q : V ⟶ U` in `N` and a morphism `a : p.obj V ⟶ Y` such
  that `a ≫ g = p.map q ≫ f`.
We show that the fiber of a presheaf for the constructed point identifies
to a colimit indexed by the category `N`.

-/

@[expose] public section

universe w v'' v' v u'' u' u

namespace CategoryTheory

open Limits Opposite

namespace GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C]

variable [LocallySmall.{w} C] {N : Type u'} [Category.{v'} N]
  (p : N ⥤ C) [InitiallySmall.{w} N]
  {J : GrothendieckTopology C}

namespace ofIsCofiltered

local instance : HasColimitsOfShape Nᵒᵖ (Type w) :=
  hasColimitsOfShape_of_finallySmall _ _

/-- Given a functor `p : N ⥤ C`, this is the functor `C ⥤ Type w` which sends
`X : C` to the colimit of types of morphisms `p.obj U ⟶ X` for `U : N`. -/
noncomputable def fiber : C ⥤ Type w :=
  shrinkYoneda.{w} ⋙ (Functor.whiskeringLeft _ _ (Type w)).obj p.op ⋙ colim

variable {p} in
/-- Constructor for elements in `fiber`. -/
noncomputable def fiberMk {U : N} {X : C} (f : p.obj U ⟶ X) : (fiber.{w} p).obj X :=
  colimit.ι (p.op ⋙ shrinkYoneda.{w}.obj X) (op U)
    (shrinkYonedaObjObjEquiv.symm f)

variable {p} in
lemma fiberMk_jointly_surjective {X : C} (x : (fiber.{w} p).obj X) :
    ∃ (U : N) (f : p.obj U ⟶ X), fiberMk f = x := by
  obtain ⟨U, f, rfl⟩ := Types.jointly_surjective_of_isColimit
    (colimit.isColimit (p.op ⋙ shrinkYoneda.{w}.obj X)) x
  obtain ⟨f, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective f
  exact ⟨U.unop, f, rfl⟩

set_option backward.isDefEq.respectTransparency false in
variable {p} in
lemma exists_of_fiberMk_eq_fiberMk [IsCofiltered N]
    {U : N} {X : C} {f₁ f₂ : p.obj U ⟶ X} (hf : fiberMk f₁ = fiberMk f₂) :
    ∃ (V : N) (g : V ⟶ U), p.map g ≫ f₁ = p.map g ≫ f₂ := by
  obtain ⟨V, g, hg⟩  :=
    (Types.FilteredColimit.isColimit_eq_iff'
      (colimit.isColimit (p.op ⋙ shrinkYoneda.{w}.obj X)) _ _).1 hf
  refine ⟨V.unop, g.unop, ?_⟩
  simpa [shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm.{w}] using hg

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma fiberMk_map_comp {U V : N} (g : V ⟶ U) {X : C} (f : p.obj U ⟶ X) :
    fiberMk.{w} (p.map g ≫ f) = fiberMk.{w} (f) := by
  simp [fiberMk, ← dsimp% congr_fun (colimit.w (p.op ⋙ shrinkYoneda.{w}.obj X) g.op)
        (shrinkYonedaObjObjEquiv.symm f),
    fiber, shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm.{w}]

@[simp]
lemma fiberMk_map {U V : N} (g : V ⟶ U) :
    fiberMk.{w} (p.map g) = fiberMk.{w} (𝟙 (p.obj U)) := by
  simpa using fiberMk_map_comp (p := p) g (𝟙 (p.obj U))

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma fiber_map_fiberMk {U : N} {X : C} (f : p.obj U ⟶ X) {Y : C} (g : X ⟶ Y) :
    (fiber p).map g (fiberMk.{w} f) = fiberMk.{w} (f ≫ g) :=
  (congr_fun (ι_colimMap (p.op.whiskerLeft (shrinkYoneda.{w}.map g)) (op U))
    (shrinkYonedaObjObjEquiv.symm f)).trans (by
      simp [fiberMk, shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm.{w}])

/-- A functor `N ⥤ (fiber p).Elements` which is initial when `N`
is cofiltered and initially small. -/
@[simps]
noncomputable def functor : N ⥤ (fiber.{w} p).Elements where
  obj U := (Functor.elementsMk _ (p.obj U) (fiberMk (𝟙 _)))
  map {U V} f := CategoryOfElements.homMk _ _ (p.map f) (by simp)

instance [IsCofiltered N] : (functor.{w} p).Initial := by
  refine Functor.initial_of_exists_of_isCofiltered _ ?_ ?_
  · rintro ⟨X, x⟩
    obtain ⟨U, f, rfl⟩ := fiberMk_jointly_surjective x
    exact ⟨U, f, by simp⟩
  · rintro ⟨X, x⟩ V ⟨φ₁, hφ₁⟩ ⟨φ₂, hφ₂⟩
    obtain ⟨U, f, rfl⟩ := fiberMk_jointly_surjective x
    obtain ⟨W, g, hg⟩ := exists_of_fiberMk_eq_fiberMk
      (show fiberMk.{w} φ₁ = fiberMk.{w} φ₂ by simpa using hφ₁.trans hφ₂.symm)
    exact ⟨_, g, by cat_disch⟩

instance [IsCofiltered N] [InitiallySmall.{w} N] :
    InitiallySmall.{w} (fiber.{w} p).Elements :=
  initiallySmall_of_initial_of_initiallySmall (functor.{w} p)

instance [IsCofiltered N] :
    IsCofiltered (ofIsCofiltered.fiber p).Elements :=
  IsCofiltered.of_initial (functor.{w} p)

end ofIsCofiltered

variable [IsCofiltered N]
  (hp : ∀ ⦃X : C⦄ (R : Sieve X) (_ : R ∈ J X) ⦃U : N⦄ (f : p.obj U ⟶ X),
    ∃ (Y : C) (g : Y ⟶ X) (_ : R g) (V : N) (q : V ⟶ U) (a : p.obj V ⟶ Y),
      a ≫ g = p.map q ≫ f)

open ofIsCofiltered

/-- Constructor for points of Grothendieck topologies `J : GrothendieckTopology C`
that are given by a functor `p : N ⥤ C` from a cofiltered and initially small
category `N`. -/
@[simps]
noncomputable def ofIsCofiltered :
    Point.{w} J where
  fiber := ofIsCofiltered.fiber p
  jointly_surjective {X} R hR x := by
    obtain ⟨U, f, rfl⟩ := fiberMk_jointly_surjective x
    obtain ⟨Y, g, hg, V, q, a, ha⟩ := hp R hR f
    exact ⟨Y, g, hg, fiberMk a, by simp [ha]⟩

variable {A : Type u''} [Category.{v''} A] [HasColimitsOfSize.{w, w} A]

/-- The canonical maps `P.obj (op (p.obj U)) ⟶ (ofIsCofiltered p hp).presheafFiber.obj P`
that are part of the colimit cocone `presheafFiberOfIsCofilteredCocone`. -/
noncomputable def toPresheafFiberOfIsCofiltered (U : N) (P : Cᵒᵖ ⥤ A) :
    P.obj (op (p.obj U)) ⟶ (ofIsCofiltered p hp).presheafFiber.obj P :=
  (ofIsCofiltered p hp).toPresheafFiber _ (fiberMk (𝟙 _)) P

@[reassoc (attr := simp)]
lemma toPresheafFiberOfIsCofiltered_w {V U : N} (f : V ⟶ U) (P : Cᵒᵖ ⥤ A) :
    P.map (p.map f).op ≫ toPresheafFiberOfIsCofiltered p hp V P =
      toPresheafFiberOfIsCofiltered p hp U P := by
  simp [toPresheafFiberOfIsCofiltered]

@[reassoc (attr := simp)]
lemma toPresheafFiberOfIsCofiltered_naturality {P Q : Cᵒᵖ ⥤ A} (g : P ⟶ Q) (U : N) :
    toPresheafFiberOfIsCofiltered p hp U P ≫
      (ofIsCofiltered p hp).presheafFiber.map g =
    g.app (op (p.obj U)) ≫ toPresheafFiberOfIsCofiltered p hp U Q := by
  simp [toPresheafFiberOfIsCofiltered]

/-- The (colimit) cocone which, for a point constructed using `Point.ofIsCofiltered`
and a functor `p : N ⥤ C` expresses the fiber of a presheaf as a colimit
indexed indexed by `N`. -/
noncomputable def presheafFiberOfIsCofilteredCocone (P : Cᵒᵖ ⥤ A) :
    Cocone (p.op ⋙ P) where
  pt := (ofIsCofiltered p hp).presheafFiber.obj P
  ι.app U := toPresheafFiberOfIsCofiltered _ _ _ _

/-- For a point constructed using `Point.ofIsCofiltered` and a functor `p : N ⥤ C`,
the fiber of a presheaf can be computed as a colimit indexed by `N`. -/
noncomputable def isColimitPresheafFiberOfIsCofilteredCocone (P : Cᵒᵖ ⥤ A) :
    IsColimit (presheafFiberOfIsCofilteredCocone p hp P) :=
  (Functor.Final.isColimitWhiskerEquiv (functor.{w} p).op _).2
    ((ofIsCofiltered p hp).isColimitPresheafFiberCocone P)

end GrothendieckTopology.Point

end CategoryTheory
