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
# ...


-/

@[expose] public section

universe w v' v u' u

namespace CategoryTheory

open Limits Opposite

namespace GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C]

section

variable [LocallySmall.{w} C] {N : Type u'} [Category.{v'} N]
  (p : N ⥤ C) [InitiallySmall.{w} N]
  {J : GrothendieckTopology C}

namespace ofIsCofiltered

local instance : HasColimitsOfShape Nᵒᵖ (Type w) :=
  hasColimitsOfShape_of_finallySmall _ _

noncomputable def fiber : C ⥤ Type w :=
  shrinkYoneda.{w} ⋙ (Functor.whiskeringLeft _ _ (Type w)).obj p.op ⋙ colim

variable {p} in
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

variable {p} in
lemma exists_of_fiberMk_eq_fiberMk [IsCofiltered N]
    {U : N} {X : C} {f₁ f₂ : p.obj U ⟶ X} (hf : fiberMk f₁ = fiberMk f₂) :
    ∃ (V : N) (g : V ⟶ U), p.map g ≫ f₁ = p.map g ≫ f₂ := by
  obtain ⟨V, g, hg⟩  :=
    (Types.FilteredColimit.isColimit_eq_iff'
      (colimit.isColimit (p.op ⋙ shrinkYoneda.{w}.obj X)) _ _).1 hf
  refine ⟨V.unop, g.unop, ?_⟩
  simp at hg
  sorry

@[simp]
lemma fiberMk_map_comp {U V : N} (g : V ⟶ U) {X : C} (f : p.obj U ⟶ X) :
    fiberMk.{w} (p.map g ≫ f) = fiberMk.{w} (f) := by
  refine Eq.trans ?_ (congr_fun (colimit.w (p.op ⋙ shrinkYoneda.{w}.obj X) g.op)
    (shrinkYonedaObjObjEquiv.symm f))
  dsimp [fiber, fiberMk]
  apply congr_arg
  sorry

@[simp]
lemma fiberMk_map {U V : N} (g : V ⟶ U) :
    fiberMk.{w} (p.map g) = fiberMk.{w} (𝟙 (p.obj U)) := by
  simpa using fiberMk_map_comp (p := p) g (𝟙 (p.obj U))

@[simp]
lemma fiber_map_fiberMk {U : N} {X : C} (f : p.obj U ⟶ X) {Y : C} (g : X ⟶ Y) :
    (fiber p).map g (fiberMk.{w} f) = fiberMk.{w} (f ≫ g) :=
  (congr_fun (ι_colimMap (p.op.whiskerLeft (shrinkYoneda.{w}.map g)) (op U))
    (shrinkYonedaObjObjEquiv.symm f)).trans (by
      dsimp [fiberMk]
      apply congr_arg
      sorry)

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

@[simps]
noncomputable def ofIsCofiltered :
    Point.{w} J where
  fiber := ofIsCofiltered.fiber p
  jointly_surjective {X} R hR x := by
    obtain ⟨U, f, rfl⟩ := fiberMk_jointly_surjective x
    obtain ⟨Y, g, hg, V, q, a, ha⟩ := hp R hR f
    exact ⟨Y, g, hg, fiberMk a, by simp [ha]⟩

variable {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{w, w} A]
  (P : Cᵒᵖ ⥤ A)

noncomputable def toPresheafFiberOfCofiltered (U : N) :
    P.obj (op (p.obj U)) ⟶ (ofIsCofiltered p hp).presheafFiber.obj P :=
  (ofIsCofiltered p hp).toPresheafFiber _ (fiberMk (𝟙 _)) P

@[reassoc (attr := simp)]
lemma toPresheafFiberOfCofiltered_w {V U : N} (f : V ⟶ U) :
    P.map (p.map f).op ≫ toPresheafFiberOfCofiltered p hp P V =
      toPresheafFiberOfCofiltered p hp P U := by
  simp [toPresheafFiberOfCofiltered]

noncomputable def presheafFiberOfCofilteredCocone : Cocone (p.op ⋙ P) where
  pt := (ofIsCofiltered p hp).presheafFiber.obj P
  ι.app U := toPresheafFiberOfCofiltered _ _ _ _

noncomputable def isColimitPresheafFiberOfCofilteredCocone :
    IsColimit (presheafFiberOfCofilteredCocone p hp P) :=
  (Functor.Final.isColimitWhiskerEquiv (functor.{w} p).op _).2
    ((ofIsCofiltered p hp).isColimitPresheafFiberCocone P)

end

section

variable {D : Type u'} [Category.{v'} D] [LocallySmall.{w} D]
  {J : GrothendieckTopology C} (Φ : Point.{w} J) (F : C ⥤ D)
  (K : GrothendieckTopology D)

noncomputable def map [F.IsCocontinuous J K] : Point.{w} K :=
  Point.ofIsCofiltered.{w} (CategoryOfElements.π Φ.fiber ⋙ F) (by
    intro Y R hR ⟨U, u⟩ f
    dsimp at f ⊢
    obtain ⟨V, g, hg, v, rfl⟩ :=
      Φ.jointly_surjective _ (F.cover_lift J K (K.pullback_stable f hR)) u
    exact ⟨_, F.map g ≫ f, hg, Φ.fiber.elementsMk _ v, ⟨g, rfl⟩, 𝟙 _, by simp⟩)

end

end GrothendieckTopology.Point

end CategoryTheory
