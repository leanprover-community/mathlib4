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

universe w v'' v' v u'' u' u

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

variable {A : Type u''} [Category.{v''} A] [HasColimitsOfSize.{w, w} A]

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

noncomputable def presheafFiberOfIsCofilteredCocone (P : Cᵒᵖ ⥤ A) :
    Cocone (p.op ⋙ P) where
  pt := (ofIsCofiltered p hp).presheafFiber.obj P
  ι.app U := toPresheafFiberOfIsCofiltered _ _ _ _

noncomputable def isColimitPresheafFiberOfIsCofilteredCocone (P : Cᵒᵖ ⥤ A) :
    IsColimit (presheafFiberOfIsCofilteredCocone p hp P) :=
  (Functor.Final.isColimitWhiskerEquiv (functor.{w} p).op _).2
    ((ofIsCofiltered p hp).isColimitPresheafFiberCocone P)

end

section

variable {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} (Φ : Point.{w} J) (F : C ⥤ D)
  (K : GrothendieckTopology D) [F.IsCocontinuous J K]

lemma map_aux ⦃X : D⦄ (R : Sieve X) (hR : R ∈ K X)
    ⦃u : Φ.fiber.Elements⦄ (f : (CategoryOfElements.π Φ.fiber ⋙ F).obj u ⟶ X) :
    ∃ (Y : D) (g : Y ⟶ X) (_ : R.arrows g) (v : Φ.fiber.Elements)
      (q : v ⟶ u) (a : F.obj v.fst ⟶ Y), a ≫ g = F.map q.1 ≫ f := by
  obtain ⟨U, u⟩ := u
  dsimp at f ⊢
  obtain ⟨V, g, hg, v, rfl⟩ :=
    Φ.jointly_surjective _ (F.cover_lift J K (K.pullback_stable f hR)) u
  exact ⟨_, F.map g ≫ f, hg, Φ.fiber.elementsMk _ v, ⟨g, rfl⟩, 𝟙 _, by simp⟩

variable [LocallySmall.{w} D]

noncomputable def map : Point.{w} K :=
  Point.ofIsCofiltered.{w} (CategoryOfElements.π Φ.fiber ⋙ F) (Φ.map_aux F K)

variable {A : Type u''} [Category.{v''} A] [HasColimitsOfSize.{w, w} A]

noncomputable def toPresheafFiberMap (P : Dᵒᵖ ⥤ A) (X : C) (x : Φ.fiber.obj X) :
    P.obj (op (F.obj X)) ⟶ (Φ.map F K).presheafFiber.obj P :=
  toPresheafFiberOfIsCofiltered _ (Φ.map_aux F K) (Φ.fiber.elementsMk X x) P

@[reassoc (attr := simp)]
lemma toPresheafFiberMap_w {X Y : C} (f : X ⟶ Y)
    (x : Φ.fiber.obj X) (P : Dᵒᵖ ⥤ A) :
    P.map (F.map f).op ≫ Φ.toPresheafFiberMap F K P X x =
      Φ.toPresheafFiberMap F K P Y (Φ.fiber.map f x) :=
  toPresheafFiberOfIsCofiltered_w _ (Φ.map_aux F K)
    (V := ⟨X, x⟩) (U := ⟨Y, Φ.fiber.map f x⟩) ⟨f, rfl⟩ P

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma toPresheafFiberMap_naturality {P Q : Dᵒᵖ ⥤ A} (g : P ⟶ Q) (X : C) (x : Φ.fiber.obj X) :
    Φ.toPresheafFiberMap F K P X x ≫ (Φ.map F K).presheafFiber.map g =
      g.app _ ≫ Φ.toPresheafFiberMap F K Q X x :=
  toPresheafFiberOfIsCofiltered_naturality _ _ _ _

noncomputable def presheafFiberMapCocone (P : Dᵒᵖ ⥤ A) :
    Cocone ((CategoryOfElements.π Φ.fiber).op ⋙ F.op ⋙ P) where
  pt := (Φ.map F K).presheafFiber.obj P
  ι.app x := Φ.toPresheafFiberMap F K P x.unop.1 x.unop.2

noncomputable def isColimitPresheafFiberMapCocone (P : Dᵒᵖ ⥤ A) :
    IsColimit (Φ.presheafFiberMapCocone F K P) :=
  (isColimitPresheafFiberOfIsCofilteredCocone.{w} _ (Φ.map_aux F K) P)

@[ext]
lemma presheafFiberMap_hom_ext {P : Dᵒᵖ ⥤ A} {T : A}
    {f g : (Φ.map F K).presheafFiber.obj P ⟶ T}
    (h : ∀ (X : C) (x : Φ.fiber.obj X),
      Φ.toPresheafFiberMap F K P X x ≫ f = Φ.toPresheafFiberMap F K P X x ≫ g) :
    f = g :=
  (Φ.isColimitPresheafFiberMapCocone F K P).hom_ext (fun _ ↦ h _ _)

noncomputable def presheafFiberMapObjIso (P : Dᵒᵖ ⥤ A) :
    (Φ.map F K).presheafFiber.obj P ≅ Φ.presheafFiber.obj (F.op ⋙ P) :=
  IsColimit.coconePointUniqueUpToIso (Φ.isColimitPresheafFiberMapCocone F K P)
    (Φ.isColimitPresheafFiberCocone (F.op ⋙ P))

@[reassoc (attr := simp)]
lemma toPresheafFiberMap_presheafFiberMapObjIso_hom (P : Dᵒᵖ ⥤ A) (X : C) (x : Φ.fiber.obj X) :
    Φ.toPresheafFiberMap F K P X x ≫ (Φ.presheafFiberMapObjIso F K P).hom =
      Φ.toPresheafFiber X x (F.op ⋙ P) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (Φ.isColimitPresheafFiberMapCocone F K P) _ ⟨X, x⟩

noncomputable def presheafFiberMapIso : (Φ.map F K).presheafFiber (A := A) ≅
    (Functor.whiskeringLeft _ _ _).obj F.op ⋙ (Φ.presheafFiber (A := A)) :=
  NatIso.ofComponents (Φ.presheafFiberMapObjIso F K)

end

end GrothendieckTopology.Point

end CategoryTheory
