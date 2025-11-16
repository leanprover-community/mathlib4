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

Let `C` be a category equipped with a Grothendieck topology `J`. In this file,
we define the notion of point of the site `(C, J)`, as a
structure `GrothendieckTopology.Point`. Such a `Φ : J.Point` consists
in a functor `Φ.fiber : C ⥤ Type w` such that the category `Φ.fiber.Elements`
is cofiltered (and initially small) and such that if `x : Φ.fiber.obj X`
and `R` is a covering sieve of `X`, then `x` belongs to the image
of some `y : Φ.fiber.obj Y` by a morphism `f : Y ⟶ X` which belongs to `R`.
The fact that `Φ.fiber.Elementsᵒᵖ` is filtered allows to define
`Φ.presheafFiber : (Cᵒᵖ ⥤ A) ⥤ A` by taking the filtering colimit
of the evaluation functors at `op X` when `(X : C, x : F.obj X)` varies in
`Φ.fiber.Elementsᵒᵖ`. We define `Φ.sheafFiber : Sheaf J A ⥤ A` as the
restriction of `Φ.presheafFiber` to the full subcategory of sheaves.

Under certain assumptions, we show that if `A` is concrete and
`P ⟶ Q` is a locally bijective morphism between presheaves,
then the induced morphism on fibers is a bijection. It follows
that `Φ.sheafFiber : Sheaf J A ⥤ A` is not only the restriction of
`Φ.presheafFiber` but it may also be thought as a localization
of this functor with respect to the class of morphisms `J.W`.
In particular, the fiber of a presheaf identifies to the fiber of
its associated sheaf.

We show that both `Φ.presheafFiber` and `Φ.sheafFiber`
commute to finite limits and to arbitrary colimits.

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

instance [LocallySmall.{w} C] [AB5OfSize.{w, w} A] [HasFiniteLimits A] :
    HasExactColimitsOfShape Φ.fiber.Elementsᵒᵖ A := by
  obtain ⟨D, _, _, F, _⟩ := FinallySmall.exists_of_isFiltered.{w} Φ.fiber.Elementsᵒᵖ
  exact HasExactColimitOfShape.of_final F A

noncomputable def presheafFiber : (Cᵒᵖ ⥤ A) ⥤ A :=
  (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π Φ.fiber).op ⋙ colim

noncomputable def toPresheafFiberNatTrans (X : C) (x : Φ.fiber.obj X) :
    (evaluation Cᵒᵖ A).obj (op X) ⟶ Φ.presheafFiber where
  app P := colimit.ι ((CategoryOfElements.π Φ.fiber).op ⋙ P) (op ⟨X, x⟩)
  naturality _ _ f := by simp [presheafFiber]

noncomputable abbrev toPresheafFiber (X : C) (x : Φ.fiber.obj X) (P : Cᵒᵖ ⥤ A) :
    P.obj (op X) ⟶ Φ.presheafFiber.obj P :=
  (Φ.toPresheafFiberNatTrans X x).app P

@[elementwise (attr := simp)]
lemma toPresheafFiber_w {X Y : C} (f : X ⟶ Y) (x : Φ.fiber.obj X) (P : Cᵒᵖ ⥤ A) :
    P.map f.op ≫ Φ.toPresheafFiber X x P =
      Φ.toPresheafFiber Y (Φ.fiber.map f x) P :=
  colimit.w ((CategoryOfElements.π Φ.fiber).op ⋙ P)
      (CategoryOfElements.homMk ⟨X, x⟩ ⟨Y, Φ.fiber.map f x⟩ f rfl).op

@[reassoc]
lemma toPresheafFiber_naturality {P Q : Cᵒᵖ ⥤ A} (g : P ⟶ Q) (X : C) (x : Φ.fiber.obj X) :
    Φ.toPresheafFiber X x P ≫ Φ.presheafFiber.map g =
      g.app (op X) ≫ Φ.toPresheafFiber X x Q :=
  ((Φ.toPresheafFiberNatTrans X x).naturality g).symm

variable {FC : A → A → Type*} {CC : A → Type w'}
  [∀ (X Y : A), FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory.{w'} A FC]

section

variable {P Q : Cᵒᵖ ⥤ A}

@[simp]
lemma toPresheafFiber_naturality_apply {P Q : Cᵒᵖ ⥤ A} (g : P ⟶ Q) (X : C) (x : Φ.fiber.obj X)
    (p : ToType (P.obj (op X))) :
    Φ.presheafFiber.map g (Φ.toPresheafFiber X x P p)  =
      Φ.toPresheafFiber X x Q (g.app (op X) p) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
  exact congr_fun ((forget A).congr_map (Φ.toPresheafFiber_naturality g X x)) p

variable [PreservesFilteredColimitsOfSize.{w, w} (forget A)] [LocallySmall.{w} C]

instance : PreservesColimitsOfShape Φ.fiber.Elementsᵒᵖ (forget A) :=
  Functor.Final.preservesColimitsOfShape_of_final (FinallySmall.fromFilteredFinalModel.{w} _) _

lemma toPresheafFiber_jointly_surjective (p : ToType (Φ.presheafFiber.obj P)) :
    ∃ (X : C) (x : Φ.fiber.obj X) (z : ToType (P.obj (op X))),
      Φ.toPresheafFiber X x P z = p := by
  obtain ⟨⟨X, x⟩, z, rfl⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget A)
      (colimit.isColimit ((CategoryOfElements.π Φ.fiber).op ⋙ P))) p
  exact ⟨X, x, z, rfl⟩

lemma toPresheafFiber_jointly_surjective₂ (p₁ p₂ : ToType (Φ.presheafFiber.obj P)) :
    ∃ (X : C) (x : Φ.fiber.obj X) (z₁ z₂ : ToType (P.obj (op X))),
      Φ.toPresheafFiber X x P z₁ = p₁ ∧ Φ.toPresheafFiber X x P z₂ = p₂ := by
  obtain ⟨⟨X, x⟩, z₁, z₂, rfl, rfl⟩ := Types.FilteredColimit.jointly_surjective_of_isColimit₂
    (isColimitOfPreserves (forget A)
      (colimit.isColimit ((CategoryOfElements.π Φ.fiber).op ⋙ P))) p₁ p₂
  exact ⟨X, x, z₁, z₂, rfl, rfl⟩

lemma toPresheafFiber_eq_iff' (X : C) (x : Φ.fiber.obj X) (z₁ z₂ : ToType (P.obj (op X))) :
    Φ.toPresheafFiber X x P z₁ = Φ.toPresheafFiber X x P z₂ ↔
      ∃ (Y : C) (f : Y ⟶ X) (y : Φ.fiber.obj Y), Φ.fiber.map f y = x ∧
        P.map f.op z₁ = P.map f.op z₂ := by
  refine (Types.FilteredColimit.isColimit_eq_iff'
    (ht := isColimitOfPreserves (forget A)
      (colimit.isColimit ((CategoryOfElements.π Φ.fiber).op ⋙ P))) ..).trans ?_
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

noncomputable def sheafFiber : Sheaf J A ⥤ A :=
  sheafToPresheaf J A ⋙ Φ.presheafFiber

variable (A) in
noncomputable def sheafToPresheafCompPresheafFiber :
    sheafToPresheaf J A ⋙ Φ.presheafFiber ≅ Φ.sheafFiber := Iso.refl _

instance (P : Cᵒᵖ ⥤ A) [HasWeakSheafify J A]
    [PreservesFilteredColimitsOfSize.{w, w} (forget A)] [LocallySmall.{w} C]
    [J.WEqualsLocallyBijective A] [(forget A).ReflectsIsomorphisms] :
    IsIso (Φ.presheafFiber.map (CategoryTheory.toSheafify J P)) :=
  W_isInvertedBy_presheafFiber _ _ (W_toSheafify J P)

variable (A) in
noncomputable def presheafToSheafCompSheafFiber [HasWeakSheafify J A]
    [PreservesFilteredColimitsOfSize.{w, w} (forget A)] [LocallySmall.{w} C]
    [J.WEqualsLocallyBijective A] [(forget A).ReflectsIsomorphisms] :
    presheafToSheaf J A ⋙ Φ.sheafFiber ≅ Φ.presheafFiber :=
  Functor.isoWhiskerLeft (presheafToSheaf J A) (Φ.sheafToPresheafCompPresheafFiber A).symm ≪≫
    (NatIso.ofComponents
      (fun P ↦ asIso ((Φ.presheafFiber (A := A)).map (CategoryTheory.toSheafify J P) :))
        (by simp [← Functor.map_comp])).symm

instance [LocallySmall.{w} C] [HasFiniteLimits A] [AB5OfSize.{w, w} A] :
    PreservesFiniteLimits (Φ.presheafFiber (A := A)) := by
  dsimp [presheafFiber]
  have : PreservesFiniteLimits ((Functor.whiskeringLeft Φ.fiber.Elementsᵒᵖ Cᵒᵖ A).obj
      (CategoryOfElements.π Φ.fiber).op) := by
    constructor
    intro _ _ _
    infer_instance
  apply comp_preservesFiniteLimits

instance [LocallySmall.{w} C] [HasFiniteLimits A] [AB5OfSize.{w, w} A] :
    PreservesFiniteLimits (Φ.sheafFiber (A := A)) := comp_preservesFiniteLimits _ _

instance : PreservesColimitsOfSize.{w, w} (Φ.presheafFiber (A := A)) where
  preservesColimitsOfShape := by
    dsimp [presheafFiber]
    infer_instance

instance [HasSheafify J A] [J.WEqualsLocallyBijective A] [(forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{w, w} (forget A)] [LocallySmall.{w} C] :
    PreservesColimitsOfSize.{w, w} (Φ.sheafFiber (A := A)) where
  preservesColimitsOfShape {K _} := ⟨fun {F} ↦
    preservesColimit_of_preserves_colimit_cocone
      (Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _))
        (IsColimit.ofIsoColimit (isColimitOfPreserves Φ.presheafFiber
          (colimit.isColimit (F ⋙ sheafToPresheaf J A))) (by
            let G := colimit (F ⋙ sheafToPresheaf J A)
            let φ := (sheafificationAdjunction J A).unit.app G
            have : IsIso (Φ.presheafFiber.map φ) :=
              W_isInvertedBy_presheafFiber _ _ (W_toSheafify J _)
            refine Cocones.ext (asIso (Φ.presheafFiber.map φ)) (fun k ↦ ?_)
            -- needs cleanup
            dsimp [sheafFiber, Sheaf.sheafifyCocone, φ]
            simp [← Functor.map_comp]
            congr 1
            have (G : Sheaf J A) :
                ((sheafificationAdjunction J A).counit.app G).val ≫
                  (sheafificationAdjunction J A).unit.app G.val = 𝟙 _ := by
              simp [← cancel_mono ((sheafToPresheaf _ _).map
                ((sheafificationAdjunction J A).counit.app G))]
            rw [← cancel_epi ((sheafToPresheaf _ _).map
              ((sheafificationAdjunction J A).counit.app (F.obj k))),
              sheafToPresheaf_map, ← Sheaf.comp_val_assoc,
              IsIso.hom_inv_id, Sheaf.id_val, Category.id_comp,
              ← (sheafificationAdjunction J A).unit_naturality, reassoc_of% this]
            dsimp))⟩

end Point

end GrothendieckTopology

end CategoryTheory
