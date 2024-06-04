/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.Localization

/-!
# Locally bijective morphisms of presheaves

Let `C` a be category equipped with a Grothendieck topology `J`.
Let `A` be a concrete category.
In this file, we introduce a type-class `J.WEqualsLocallyBijective A` which says
that the class `J.W` (of morphisms of presheaves which become isomorphisms
after sheafification) is the class of morphisms that are both locally injective
and locally surjective (i.e. locally bijective). We prove that this holds iff
for any presheaf `P : Cᵒᵖ ⥤ A`, the sheafification map `toSheafify J P` is locally bijective.
We show that this holds under certain universe assumptions.

-/

universe w' w v' v u' u
namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type u'} [Category.{v'} A] [ConcreteCategory.{w} A]

namespace Sheaf

section

variable {F G : Sheaf J (Type w)} (f : F ⟶ G)

/-- A morphism of sheaves of types is locally bijective iff it is an isomorphism.
(This is generalized below as `isLocallyBijective_iff_isIso`.) -/
private lemma isLocallyBijective_iff_isIso' :
    IsLocallyInjective f ∧ IsLocallySurjective f ↔ IsIso f := by
  constructor
  · rintro ⟨h₁, _⟩
    rw [isLocallyInjective_iff_injective] at h₁
    suffices ∀ (X : Cᵒᵖ), Function.Surjective (f.val.app X) by
      rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _), NatTrans.isIso_iff_isIso_app]
      intro X
      rw [isIso_iff_bijective]
      exact ⟨h₁ X, this X⟩
    intro X s
    have H := (isSheaf_iff_isSheaf_of_type J F.val).1 F.cond _ (Presheaf.imageSieve_mem J f.val s)
    let t : Presieve.FamilyOfElements F.val (Presheaf.imageSieve f.val s).arrows :=
      fun Y g hg => Presheaf.localPreimage f.val s g hg
    have ht : t.Compatible := by
      intro Y₁ Y₂ W g₁ g₂ f₁ f₂ hf₁ hf₂ w
      apply h₁
      have eq₁ := FunctorToTypes.naturality _ _ f.val g₁.op (t f₁ hf₁)
      have eq₂ := FunctorToTypes.naturality _ _ f.val g₂.op (t f₂ hf₂)
      have eq₃ := congr_arg (G.val.map g₁.op) (Presheaf.app_localPreimage f.val s _ hf₁)
      have eq₄ := congr_arg (G.val.map g₂.op) (Presheaf.app_localPreimage f.val s _ hf₂)
      refine eq₁.trans (eq₃.trans (Eq.trans ?_ (eq₄.symm.trans eq₂.symm)))
      erw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply]
      simp only [← op_comp, w]
    refine ⟨H.amalgamate t ht, ?_⟩
    · apply (Presieve.isSeparated_of_isSheaf _ _
        ((isSheaf_iff_isSheaf_of_type J G.val).1 G.cond) _
        (Presheaf.imageSieve_mem J f.val s)).ext
      intro Y g hg
      rw [← FunctorToTypes.naturality, H.valid_glue ht]
      exact Presheaf.app_localPreimage f.val s g hg
  · intro
    constructor <;> infer_instance

end

section

variable {F G : Sheaf J A} (f : F ⟶ G) [(forget A).ReflectsIsomorphisms]
  [J.HasSheafCompose (forget A)]

lemma isLocallyBijective_iff_isIso :
    IsLocallyInjective f ∧ IsLocallySurjective f ↔ IsIso f := by
  constructor
  · rintro ⟨_, _⟩
    rw [← isIso_iff_of_reflects_iso f (sheafCompose J (forget A)),
      ← isLocallyBijective_iff_isIso']
    constructor <;> infer_instance
  · intro
    constructor <;> infer_instance

end

end Sheaf

variable (J A)

namespace GrothendieckTopology

/-- Given a category `C` equipped with a Grothendieck topology `J` and a concrete category `A`,
this property holds if a morphism in `Cᵒᵖ ⥤ A` satisfies `J.W` (i.e. becomes an iso after
sheafification) iff it is both locally injective and locally surjective. -/
class WEqualsLocallyBijective : Prop where
  iff {X Y : Cᵒᵖ ⥤ A} (f : X ⟶ Y) :
    J.W f ↔ Presheaf.IsLocallyInjective J f ∧ Presheaf.IsLocallySurjective J f

section

variable {A}
variable [J.WEqualsLocallyBijective A] {X Y : Cᵒᵖ ⥤ A} (f : X ⟶ Y)

lemma W_iff_isLocallyBijective :
    J.W f ↔ Presheaf.IsLocallyInjective J f ∧ Presheaf.IsLocallySurjective J f := by
  apply WEqualsLocallyBijective.iff

variable {J f}

lemma W.isLocallyInjective (hf : J.W f) : Presheaf.IsLocallyInjective J f :=
  ((J.W_iff_isLocallyBijective f).1 hf).1

lemma W.isLocallySurjective (hf : J.W f) : Presheaf.IsLocallySurjective J f :=
  ((J.W_iff_isLocallyBijective f).1 hf).2

variable [HasWeakSheafify J A] (P : Cᵒᵖ ⥤ A)

instance : Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P) :=
  (J.W_toSheafify P).isLocallyInjective

instance : Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P) :=
  (J.W_toSheafify P).isLocallySurjective

end

lemma WEqualsLocallyBijective.mk' [HasWeakSheafify J A] [(forget A).ReflectsIsomorphisms]
    [J.HasSheafCompose (forget A)]
    [∀ (P : Cᵒᵖ ⥤ A), Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P)]
    [∀ (P : Cᵒᵖ ⥤ A), Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P)] :
    J.WEqualsLocallyBijective A where
  iff {P Q} f := by
    rw [W_iff, ← Sheaf.isLocallyBijective_iff_isIso,
      ← Presheaf.isLocallyInjective_comp_iff J f (CategoryTheory.toSheafify J Q),
      ← Presheaf.isLocallySurjective_comp_iff J f (CategoryTheory.toSheafify J Q),
      CategoryTheory.toSheafify_naturality, Presheaf.comp_isLocallyInjective_iff,
      Presheaf.comp_isLocallySurjective_iff]

instance {D : Type w} [Category.{w'} D] [ConcreteCategory.{max u v} D]
    [HasWeakSheafify J D] [J.HasSheafCompose (forget D)]
    [J.PreservesSheafification (forget D)] [(forget D).ReflectsIsomorphisms] :
    J.WEqualsLocallyBijective D := by
  apply WEqualsLocallyBijective.mk'

instance : J.WEqualsLocallyBijective (Type (max u v)) := inferInstance

end GrothendieckTopology

namespace Presheaf

variable {A}
variable [HasWeakSheafify J A] [J.WEqualsLocallyBijective A] {P Q : Cᵒᵖ ⥤ A} (φ : P ⟶ Q)

lemma isLocallyInjective_presheafToSheaf_map_iff :
    Sheaf.IsLocallyInjective ((presheafToSheaf J A).map φ) ↔ IsLocallyInjective J φ := by
  rw [← Sheaf.isLocallyInjective_sheafToPresheaf_map_iff,
    ← isLocallyInjective_comp_iff J _ (toSheafify J Q),
    ← comp_isLocallyInjective_iff J (toSheafify J P),
    toSheafify_naturality, sheafToPresheaf_map]

lemma isLocallySurjective_presheafToSheaf_map_iff :
    Sheaf.IsLocallySurjective ((presheafToSheaf J A).map φ) ↔ IsLocallySurjective J φ := by
  rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff,
    ← isLocallySurjective_comp_iff J _ (toSheafify J Q),
    ← comp_isLocallySurjective_iff J (toSheafify J P),
    toSheafify_naturality, sheafToPresheaf_map]

end Presheaf

end CategoryTheory
