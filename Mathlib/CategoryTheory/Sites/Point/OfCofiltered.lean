/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.ShrinkYoneda

/-!
# ...


-/

@[expose] public section

universe w v' v u' u

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  {N : Type u'} [Category.{v'} N] (p : N ⥤ C) [EssentiallySmall.{w} N]
  {J : GrothendieckTopology C}

namespace GrothendieckTopology.Point

namespace ofCofiltered

local instance : HasColimitsOfShape Nᵒᵖ (Type w) :=
  hasColimitsOfShape_of_equivalence (equivSmallModel.{w} Nᵒᵖ).symm

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

instance [IsCofiltered N] [EssentiallySmall.{w} N] :
    InitiallySmallCofiltered.{w} (fiber.{w} p).Elements :=
  initiallySmallCofiltered_of_initial (functor.{w} p)

instance [IsCofiltered N] [EssentiallySmall.{w} N] :
    InitiallySmall.{w} (fiber.{w} p).Elements :=
  initiallySmall_of_initial_of_essentiallySmall.{w} (functor.{w} p)

attribute [local instance] IsCofiltered.nonempty in
lemma isCofiltered_elements_fiber [IsCofiltered N]
    (h₁ : ∀ ⦃X₁ X₂ : C⦄ ⦃U : N⦄ (f₁ : p.obj U ⟶ X₁) (f₂ : p.obj U ⟶ X₂),
      ∃ (Y : C) (V : N) (f : p.obj V ⟶ Y) (g₁ : Y ⟶ X₁) (g₂ : Y ⟶ X₂) (q : V ⟶ U),
        f ≫ g₁ = p.map q ≫ f₁ ∧ f ≫ g₂ = p.map q ≫ f₂)
    (h₂ : ∀ ⦃X₁ X₂ : C⦄ (φ₁ φ₂ : X₁ ⟶ X₂) ⦃U : N⦄ (f : p.obj U ⟶ X₁),
      f ≫ φ₁ = f ≫ φ₂ → ∃ (Z : C) (g : Z ⟶ X₁) (V : N) (q : p.obj V ⟶ Z) (r : V ⟶ U),
        g ≫ φ₁ = g ≫ φ₂ ∧ q ≫ g = p.map r ≫ f) :
    IsCofiltered (fiber.{w} p).Elements where
  nonempty := ⟨Functor.elementsMk _ (p.obj (Classical.arbitrary N)) (fiberMk (𝟙 _))⟩
  cone_objs := by
    rintro ⟨X₁, x₁⟩ ⟨X₂, x₂⟩
    obtain ⟨U₁, f₁, rfl⟩ := fiberMk_jointly_surjective x₁
    obtain ⟨U₂, f₂, rfl⟩ := fiberMk_jointly_surjective x₂
    obtain ⟨Y, V, f, g₁, g₂, q, h₁, h₂⟩ :=
      h₁ (p.map (IsCofiltered.minToLeft U₁ U₂) ≫ f₁)
        (p.map (IsCofiltered.minToRight U₁ U₂) ≫ f₂)
    exact ⟨Functor.elementsMk _ Y (fiberMk f), ⟨g₁, by simp [h₁]⟩, ⟨g₂, by simp [h₂]⟩, ⟨⟩⟩
  cone_maps := by
    rintro ⟨X₁, x₁⟩ ⟨X₂, x₂⟩ ⟨φ₁, hφ₁⟩ ⟨φ₂, hφ₂⟩
    obtain ⟨U₁, f₁, rfl⟩ := fiberMk_jointly_surjective x₁
    obtain ⟨U₂, f₂, rfl⟩ := fiberMk_jointly_surjective x₂
    dsimp at φ₁ φ₂
    simp only [fiber_map_fiberMk] at hφ₁ hφ₂
    obtain ⟨V, b, hb⟩ := exists_of_fiberMk_eq_fiberMk (hφ₁.trans hφ₂.symm)
    obtain ⟨Z, g, W, q, r, hg, hr⟩ := h₂ φ₁ φ₂ (p.map b ≫ f₁) (by simpa)
    exact ⟨Functor.elementsMk _ Z (fiberMk q), ⟨g, by simp [hr]⟩, by ext; simpa⟩

instance isCofiltered_elements_fiber_of_hasFiniteLimits [IsCofiltered N] [HasFiniteLimits C] :
    IsCofiltered (fiber.{w} p).Elements :=
  isCofiltered_elements_fiber p
    (fun X₁ X₂ U f₁ f₂ ↦ ⟨X₁ ⨯ X₂, U, prod.lift f₁ f₂, prod.fst, prod.snd, 𝟙 _, by simp⟩)
    (fun X₁ X₂ φ₁ φ₂ U f hf ↦ ⟨_, equalizer.ι φ₁ φ₂, U, equalizer.lift _ hf, 𝟙 _, by
        simpa using equalizer.condition φ₁ φ₂, by simp⟩)

end ofCofiltered

variable [IsCofiltered N]
  (hp : ∀ ⦃X : C⦄ (R : Sieve X) (_ : R ∈ J X) ⦃U : N⦄ (f : p.obj U ⟶ X),
    ∃ (Y : C) (g : Y ⟶ X) (_ : R g) (V : N) (q : V ⟶ U) (a : p.obj V ⟶ Y),
      a ≫ g = p.map q ≫ f)

open ofCofiltered

@[simps]
noncomputable def ofCofiltered :
    Point.{w} J where
  fiber := ofCofiltered.fiber p
  jointly_surjective {X} R hR x := by
    obtain ⟨U, f, rfl⟩ := fiberMk_jointly_surjective x
    obtain ⟨Y, g, hg, V, q, a, ha⟩ := hp R hR f
    exact ⟨Y, g, hg, fiberMk a, by simp [ha]⟩

variable {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{w, w} A]
  (P : Cᵒᵖ ⥤ A)

noncomputable def toPresheafFiberOfCofiltered (U : N) :
    P.obj (op (p.obj U)) ⟶ (ofCofiltered p hp).presheafFiber.obj P :=
  (ofCofiltered p hp).toPresheafFiber _ (fiberMk (𝟙 _)) P

@[reassoc (attr := simp)]
lemma toPresheafFiberOfCofiltered_w {V U : N} (f : V ⟶ U) :
    P.map (p.map f).op ≫ toPresheafFiberOfCofiltered p hp P V =
      toPresheafFiberOfCofiltered p hp P U := by
  simp [toPresheafFiberOfCofiltered]

noncomputable def presheafFiberOfCofilteredCocone : Cocone (p.op ⋙ P) where
  pt := (ofCofiltered p hp).presheafFiber.obj P
  ι.app U := toPresheafFiberOfCofiltered _ _ _ _

noncomputable def isColimitPresheafFiberOfCofilteredCocone :
    IsColimit (presheafFiberOfCofilteredCocone p hp P) :=
  (Functor.Final.isColimitWhiskerEquiv (functor.{w} p).op _).2
    ((ofCofiltered p hp).isColimitPresheafFiberCocone P)

end GrothendieckTopology.Point

end CategoryTheory
