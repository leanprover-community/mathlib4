/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Functor.TypeFlat
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.PreservesLimits
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Filtered.FinallySmall

/-!
# Points of a site

-/

universe w' w v v' u u'

namespace CategoryTheory

open Limits Opposite

-- to be moved
instance {C D : Type*} [Category C] [Category D] [HasFiniteLimits D] (X : C) :
    PreservesFiniteLimits ((evaluation C D).obj X) where
  preservesFiniteLimits J _ _ := by
    infer_instance

-- to be moved
lemma HasExactColimitOfShape.of_final
    {J₁ J₂ : Type*} [Category J₁] [Category J₂] (F : J₁ ⥤ J₂) [F.Final]
    (C : Type*) [Category C] [HasFiniteLimits C]
    [HasColimitsOfShape J₁ C] [HasExactColimitsOfShape J₁ C] :
    letI : HasColimitsOfShape J₂ C := Functor.Final.hasColimitsOfShape_of_final F
    HasExactColimitsOfShape J₂ C := by
  letI : HasColimitsOfShape J₂ C := Functor.Final.hasColimitsOfShape_of_final F
  constructor
  let φ : (Functor.whiskeringLeft J₁ J₂ C).obj F ⋙ colim ⟶ colim :=
    { app G := colimit.pre G F }
  have : IsIso φ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro
    dsimp [φ]
    infer_instance
  have : PreservesFiniteLimits ((Functor.whiskeringLeft J₁ J₂ C).obj F) :=
    ⟨fun J _ _ ↦ ⟨fun {K} ↦ ⟨fun {c} hc ↦ ⟨evaluationJointlyReflectsLimits _
    (fun j ↦ isLimitOfPreserves ((evaluation _ _).obj (F.obj j)) hc) ⟩⟩⟩⟩
  exact preservesFiniteLimits_of_natIso (asIso φ)

variable {C : Type u} [Category.{v} C]

namespace Functor

instance [LocallySmall.{w} C] (F : C ⥤ Type w) : LocallySmall.{w} F.Elements where
  hom_small := by
    rintro ⟨X, _⟩ ⟨Y, y⟩
    exact small_of_injective (f := fun g ↦ g.val) (by cat_disch)

lemma isCofiltered_elements (F : C ⥤ Type w) [HasFiniteLimits C] [PreservesFiniteLimits F] :
    IsCofiltered F.Elements where
  nonempty := ⟨⊤_ C, (terminalIsTerminal.isTerminalObj F).from PUnit .unit⟩
  cone_objs := by
    rintro ⟨X, x⟩ ⟨Y, y⟩
    let h := mapIsLimitOfPreservesOfIsLimit F _ _ (prodIsProd X Y)
    let h' := Types.binaryProductLimit (F.obj X) (F.obj Y)
    exact ⟨⟨X ⨯ Y, (h'.conePointUniqueUpToIso h).hom ⟨x, y⟩⟩,
      ⟨prod.fst, congr_fun (h'.conePointUniqueUpToIso_hom_comp h (.mk .left)) _⟩,
      ⟨prod.snd, congr_fun (h'.conePointUniqueUpToIso_hom_comp h (.mk .right)) _⟩, by tauto⟩
  cone_maps := by
    rintro ⟨X, x⟩ ⟨Y, y⟩ ⟨f, hf⟩ ⟨g, hg⟩
    dsimp at f g hf hg
    subst hg
    let h := isLimitForkMapOfIsLimit F _ (equalizerIsEqualizer f g)
    let h' := (Types.equalizerLimit (g := F.map f) (h := F.map g)).isLimit
    exact ⟨⟨equalizer f g, (h'.conePointUniqueUpToIso h).hom ⟨x, hf⟩⟩,
      ⟨equalizer.ι f g, congr_fun (h'.conePointUniqueUpToIso_hom_comp h .zero) ⟨x, hf⟩⟩,
      by ext; exact equalizer.condition f g⟩

end Functor

namespace GrothendieckTopology

variable (J : GrothendieckTopology C)

structure Point [LocallySmall.{w} C] where
  fiber : C ⥤ Type w
  isCofiltered : IsCofiltered fiber.Elements := by infer_instance
  initiallySmall : InitiallySmall.{w} fiber.Elements := by infer_instance
  jointly_surjective {X : C} (R : Sieve X) (h : R ∈ J X) (x : fiber.obj X) :
    ∃ (Y : C) (f : Y ⟶ X) (_ : R f) (y : fiber.obj Y), fiber.map f y = x

variable [LocallySmall.{w} C]

namespace Point

attribute [instance] initiallySmall isCofiltered

variable {J} (Φ : Point.{w} J) {A : Type u'} [Category.{v'} A]
  [HasColimitsOfSize.{w, w} A]

instance : HasColimitsOfShape Φ.fiber.Elementsᵒᵖ A :=
    hasColimitsOfShape_of_finallySmall _ _

instance [AB5OfSize.{w, w} A] [HasFiniteLimits A] :
    HasExactColimitsOfShape Φ.fiber.Elementsᵒᵖ A := by
  obtain ⟨D, _, _, F, _⟩ := FinallySmall.exists_of_isFiltered.{w} Φ.fiber.Elementsᵒᵖ
  exact HasExactColimitOfShape.of_final F A

noncomputable def presheafFiber : (Cᵒᵖ ⥤ A) ⥤ A :=
  colimit ((CategoryOfElements.π Φ.fiber).op ⋙ evaluation _ A)

noncomputable def toPresheafFiberNatTrans (X : C) (x : Φ.fiber.obj X) :
    (evaluation Cᵒᵖ A).obj (op X) ⟶ Φ.presheafFiber :=
  colimit.ι ((CategoryOfElements.π Φ.fiber).op ⋙ evaluation _ A) ⟨_, x⟩

noncomputable abbrev toPresheafFiber (X : C) (x : Φ.fiber.obj X) (P : Cᵒᵖ ⥤ A) :
    P.obj (op X) ⟶ Φ.presheafFiber.obj P :=
  (Φ.toPresheafFiberNatTrans X x).app P

@[elementwise (attr := simp)]
lemma toPresheafFiber_w {X Y : C} (f : X ⟶ Y) (x : Φ.fiber.obj X) (P : Cᵒᵖ ⥤ A) :
    P.map f.op ≫ Φ.toPresheafFiber X x P =
      Φ.toPresheafFiber Y (Φ.fiber.map f x) P :=
  NatTrans.congr_app (colimit.w ((CategoryOfElements.π Φ.fiber).op ⋙ evaluation _ A)
    (CategoryOfElements.homMk ⟨_, x⟩ ⟨_, Φ.fiber.map f x⟩ f rfl).op) P

@[reassoc]
lemma toPresheafFiber_naturality {P Q : Cᵒᵖ ⥤ A} (g : P ⟶ Q) (X : C) (x : Φ.fiber.obj X) :
    Φ.toPresheafFiber X x P ≫ Φ.presheafFiber.map g =
      g.app (op X) ≫ Φ.toPresheafFiber X x Q :=
  ((Φ.toPresheafFiberNatTrans X x).naturality g).symm

section

variable {FC : A → A → Type*} {CC : A → Type w'}
  [∀ (X Y : A), FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory.{w'} A FC]
  {P Q : Cᵒᵖ ⥤ A}

@[simp]
lemma toPresheafFiber_naturality_apply {P Q : Cᵒᵖ ⥤ A} (g : P ⟶ Q) (X : C) (x : Φ.fiber.obj X)
    (p : ToType (P.obj (op X))) :
    Φ.presheafFiber.map g (Φ.toPresheafFiber X x P p)  =
      Φ.toPresheafFiber X x Q (g.app (op X) p) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
  exact congr_fun ((forget A).congr_map (Φ.toPresheafFiber_naturality g X x)) p

variable [PreservesFilteredColimitsOfSize.{w, w} (forget A)]

instance : PreservesColimitsOfShape Φ.fiber.Elementsᵒᵖ (forget A) :=
  Functor.Final.preservesColimitsOfShape_of_final (FinallySmall.fromFilteredFinalModel.{w} _) _

lemma toPresheafFiber_jointly_surjective (p : ToType (Φ.presheafFiber.obj P)) :
    ∃ (X : C) (x : Φ.fiber.obj X) (z : ToType (P.obj (op X))),
      Φ.toPresheafFiber X x P z = p := by
  obtain ⟨⟨X, x⟩, z, rfl⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ((evaluation _ A).obj P ⋙ forget A)
    (colimit.isColimit ((CategoryOfElements.π Φ.fiber).op ⋙ evaluation _ A))) p
  exact ⟨X, x, z, rfl⟩

lemma toPresheafFiber_jointly_surjective₂ (p₁ p₂ : ToType (Φ.presheafFiber.obj P)) :
    ∃ (X : C) (x : Φ.fiber.obj X) (z₁ z₂ : ToType (P.obj (op X))),
      Φ.toPresheafFiber X x P z₁ = p₁ ∧ Φ.toPresheafFiber X x P z₂ = p₂ := by
  obtain ⟨⟨X, x⟩, z₁, z₂, rfl, rfl⟩ := Types.FilteredColimit.jointly_surjective_of_isColimit₂
    (isColimitOfPreserves ((evaluation _ A).obj P ⋙ forget A)
    (colimit.isColimit ((CategoryOfElements.π Φ.fiber).op ⋙ evaluation _ A))) p₁ p₂
  exact ⟨X, x, z₁, z₂, rfl, rfl⟩

lemma toPresheafFiber_eq_iff' (X : C) (x : Φ.fiber.obj X) (z₁ z₂ : ToType (P.obj (op X))) :
    Φ.toPresheafFiber X x P z₁ = Φ.toPresheafFiber X x P z₂ ↔
      ∃ (Y : C) (f : Y ⟶ X) (y : Φ.fiber.obj Y), Φ.fiber.map f y = x ∧
        P.map f.op z₁ = P.map f.op z₂ := by
  refine (Types.FilteredColimit.isColimit_eq_iff'
    (ht := (isColimitOfPreserves ((evaluation _ A).obj P ⋙ forget A)
    (colimit.isColimit ((CategoryOfElements.π Φ.fiber).op ⋙ evaluation _ A)))) ..).trans ?_
  constructor
  · rintro ⟨⟨Y, y⟩, ⟨f, hf⟩, hf'⟩
    exact ⟨Y, f, y, hf, hf'⟩
  · rintro ⟨Y, f, y, hf, hf'⟩
    exact ⟨⟨Y, y⟩, ⟨f, hf⟩, hf'⟩

variable (f : P ⟶ Q)

lemma toPresheafFiber_map_surjective [Presheaf.IsLocallySurjective J f] :
    Function.Surjective (Φ.presheafFiber.map f) := by
  intro p
  obtain ⟨X, x, z, rfl⟩ := Φ.toPresheafFiber_jointly_surjective p
  obtain ⟨Y, g, ⟨t, ht⟩, y, rfl⟩ := Φ.jointly_surjective _ (Presheaf.imageSieve_mem J f z) x
  exact ⟨Φ.toPresheafFiber Y y P t, by simp [← toPresheafFiber_w, ← ht]⟩

lemma toPresheafFiber_map_injective [Presheaf.IsLocallyInjective J f] :
    Function.Injective (Φ.presheafFiber.map f) := by
  suffices ∀ (X : C) (x : Φ.fiber.obj X) (p₁ p₂ : ToType (P.obj (op X)))
      (hp : f.app _ p₁ = f.app _ p₂), Φ.toPresheafFiber X x P p₁ = Φ.toPresheafFiber X x P p₂ by
    rintro q₁ q₂ h
    obtain ⟨X, x, p₁, p₂, rfl, rfl⟩ := Φ.toPresheafFiber_jointly_surjective₂ q₁ q₂
    simp only [toPresheafFiber_naturality_apply, toPresheafFiber_eq_iff'] at h
    obtain ⟨Y, g, y, rfl, h⟩ := h
    simp only [← NatTrans.naturality_apply] at h
    simpa using this _ y _ _ h
  intro X x p₁ p₂ h
  obtain ⟨Y, g, hg, y, rfl⟩ := Φ.jointly_surjective _ (Presheaf.equalizerSieve_mem J f _ _ h) x
  simp only [Presheaf.equalizerSieve_apply] at hg
  simp only [← toPresheafFiber_w_apply, hg]

lemma toPresheafFiber_map_bijective
    [Presheaf.IsLocallyInjective J f] [Presheaf.IsLocallySurjective J f] :
    Function.Bijective (Φ.presheafFiber.map f) :=
  ⟨Φ.toPresheafFiber_map_injective f, Φ.toPresheafFiber_map_surjective f⟩

lemma W_isInvertedBy_presheafFiber
    [J.WEqualsLocallyBijective A] [(forget A).ReflectsIsomorphisms] :
    J.W.IsInvertedBy (Φ.presheafFiber (A := A)) := by
  intro P Q f hf
  obtain ⟨_, _⟩ := (J.W_iff_isLocallyBijective f).1 hf
  rw [← isIso_iff_of_reflects_iso _ (forget A), isIso_iff_bijective]
  exact Φ.toPresheafFiber_map_bijective f

end

instance [HasFiniteLimits A] [AB5OfSize.{w, w} A] :
    PreservesFiniteLimits (Φ.presheafFiber (A := A)) :=
  ObjectProperty.preservesFiniteLimits.prop_of_isColimit
    (colimit.isColimit ((CategoryOfElements.π Φ.fiber).op ⋙ evaluation _ A))
      (by dsimp; infer_instance)

noncomputable def sheafFiber : Sheaf J A ⥤ A :=
  sheafToPresheaf J A ⋙ Φ.presheafFiber

instance [HasFiniteLimits A] [AB5OfSize.{w, w} A] :
    PreservesFiniteLimits (Φ.sheafFiber (A := A)) := comp_preservesFiniteLimits _ _

end Point

end GrothendieckTopology

end CategoryTheory
