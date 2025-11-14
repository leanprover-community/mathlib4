/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Functor.TypeFlat
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Points of a site

-/

universe w' w v v' u u'

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

namespace GrothendieckTopology

structure Point where
  fiber : C ⥤ Type w
  isCofiltered : IsCofiltered fiber.Elements := by infer_instance
  initiallySmall : InitiallySmall.{w} fiber.Elements := by infer_instance
  jointly_surjective {X : C} (R : Sieve X) (h : R ∈ J X) (x : fiber.obj X) :
    ∃ (Y : C) (f : Y ⟶ X) (_ : R f) (y : fiber.obj Y), fiber.map f y = x

namespace Point

attribute [instance] initiallySmall isCofiltered

variable {J} (Φ : Point.{w} J) {A : Type u'} [Category.{v'} A]
  [HasColimitsOfSize.{w, w} A]

instance : HasColimitsOfShape Φ.fiber.Elementsᵒᵖ A :=
    hasColimitsOfShape_of_finallySmall _ _

noncomputable def presheafFiber : (Cᵒᵖ ⥤ A) ⥤ A :=
  colimit ((CategoryOfElements.π Φ.fiber).op ⋙ evaluation _ A)

noncomputable def toPresheafFiber (X : C) (x : Φ.fiber.obj X) :
    (evaluation Cᵒᵖ A).obj (op X) ⟶ Φ.presheafFiber :=
  colimit.ι ((CategoryOfElements.π Φ.fiber).op ⋙ evaluation _ A) ⟨_, x⟩

@[elementwise (attr := simp)]
lemma toPresheafFiber_w {X Y : C} (f : X ⟶ Y) (x : Φ.fiber.obj X) (P : Cᵒᵖ ⥤ A) :
    P.map f.op ≫ (Φ.toPresheafFiber X x).app P =
      (Φ.toPresheafFiber Y (Φ.fiber.map f x)).app P :=
  NatTrans.congr_app (colimit.w ((CategoryOfElements.π Φ.fiber).op ⋙ evaluation _ A)
    (CategoryOfElements.homMk ⟨_, x⟩ ⟨_, Φ.fiber.map f x⟩ f rfl).op) P

@[reassoc]
lemma toPresheafFiber_naturality {P Q : Cᵒᵖ ⥤ A} (g : P ⟶ Q) (X : C) (x : Φ.fiber.obj X) :
    (Φ.toPresheafFiber X x).app P ≫ Φ.presheafFiber.map g =
      g.app (op X) ≫ (Φ.toPresheafFiber X x).app Q :=
  ((Φ.toPresheafFiber X x).naturality g).symm

section

variable {FC : A → A → Type*} {CC : A → Type w'}
  [∀ (X Y : A), FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory.{w'} A FC]
  {P Q : Cᵒᵖ ⥤ A}

@[simp]
lemma toPresheafFiber_naturality_apply {P Q : Cᵒᵖ ⥤ A} (g : P ⟶ Q) (X : C) (x : Φ.fiber.obj X)
    (p : ToType (P.obj (op X))) : by
    letI α : P.obj (op X) ⟶ _ := (Φ.toPresheafFiber X x).app P
    exact Φ.presheafFiber.map g (α p)  =
      (Φ.toPresheafFiber X x).app Q (g.app (op X) p) := by
  dsimp
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
  exact congr_fun ((forget A).congr_map (Φ.toPresheafFiber_naturality g X x)) p

variable [PreservesFilteredColimitsOfSize.{w, w} (forget A)]

instance : PreservesColimitsOfShape Φ.fiber.Elementsᵒᵖ (forget A) := by
  have : PreservesFilteredColimitsOfSize.{w, w} (forget A) := inferInstance
  sorry

lemma toPresheafFiber_app_jointly_surjective (p : ToType (Φ.presheafFiber.obj P)) :
    ∃ (X : C) (x : Φ.fiber.obj X) (z : ToType (P.obj (op X))),
      (Φ.toPresheafFiber X x).app P z = p := by
  obtain ⟨⟨X, x⟩, z, rfl⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ((evaluation _ A).obj P ⋙ forget A)
    (colimit.isColimit ((CategoryOfElements.π Φ.fiber).op ⋙ evaluation _ A))) p
  exact ⟨X, x, z, rfl⟩

variable (f : P ⟶ Q)

lemma toPresheafFiber_surjective [Presheaf.IsLocallySurjective J f] :
    Function.Surjective (Φ.presheafFiber.map f) := by
  intro p
  obtain ⟨X, x, z, rfl⟩ := Φ.toPresheafFiber_app_jointly_surjective p
  obtain ⟨Y, g, ⟨t, ht⟩, y, rfl⟩ := Φ.jointly_surjective _ (Presheaf.imageSieve_mem J f z) x
  exact ⟨(Φ.toPresheafFiber Y y).app P t, by simp [← toPresheafFiber_w, ← ht]⟩

lemma toPresheafFiber_injective [Presheaf.IsLocallyInjective J f] :
    Function.Injective (Φ.presheafFiber.map f) := by
  sorry

lemma toPresheafFiber_bijective
    [Presheaf.IsLocallyInjective J f] [Presheaf.IsLocallySurjective J f] :
    Function.Bijective (Φ.presheafFiber.map f) :=
  ⟨Φ.toPresheafFiber_injective f, Φ.toPresheafFiber_surjective f⟩

lemma W_isInvertedBy_presheafFiber
    [J.WEqualsLocallyBijective A] [(forget A).ReflectsIsomorphisms] :
    J.W.IsInvertedBy (Φ.presheafFiber (A := A)) := by
  intro P Q f hf
  obtain ⟨_, _⟩ := (J.W_iff_isLocallyBijective f).1 hf
  rw [← isIso_iff_of_reflects_iso _ (forget A), isIso_iff_bijective]
  exact Φ.toPresheafFiber_bijective f

end

instance : PreservesFiniteLimits (Φ.presheafFiber (A := A)) := sorry

noncomputable def sheafFiber : Sheaf J A ⥤ A :=
  sheafToPresheaf J A ⋙ Φ.presheafFiber

variable (K : Type) [SmallCategory K] [FinCategory K] [HasFiniteLimits A]

instance : PreservesFiniteLimits (Φ.sheafFiber (A := A)) := comp_preservesFiniteLimits _ _

end Point

end GrothendieckTopology

end CategoryTheory
