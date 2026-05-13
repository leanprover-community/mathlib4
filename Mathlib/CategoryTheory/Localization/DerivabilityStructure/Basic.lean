/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.Resolution
public import Mathlib.CategoryTheory.Localization.Opposite
public import Mathlib.CategoryTheory.GuitartExact.Opposite

/-!
# Derivability structures

Let `Φ : LocalizerMorphism W₁ W₂` be a localizer morphism, i.e. `W₁ : MorphismProperty C₁`,
`W₂ : MorphismProperty C₂`, and `Φ.functor : C₁ ⥤ C₂` is a functor which maps `W₁` to `W₂`.
Following the definition introduced by Bruno Kahn and Georges Maltsiniotis in
[Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008],
we say that `Φ` is a right derivability structure if `Φ` has right resolutions and
the following 2-square is Guitart exact, where `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂` are
localization functors for `W₁` and `W₂`, and `F : D₁ ⥤ D₂` is the induced functor
on the localized categories:

```
    Φ.functor
  C₁   ⥤   C₂
  |         |
L₁|         | L₂
  v         v
  D₁   ⥤   D₂
       F
```

## Implementation details

In the field `guitartExact'` of the structure `LocalizerMorphism.IsRightDerivabilityStructure`,
The condition that the square is Guitart exact is stated for the localization functors
of the constructed categories (`W₁.Q` and `W₂.Q`).
The lemma `LocalizerMorphism.isRightDerivabilityStructure_iff` shows that it does
not depend on the choice of the localization functors.

## TODO

* Construct the injective derivability structure in order to derive functor from
  the bounded below homotopy category in an abelian category with enough injectives
* Construct the projective derivability structure in order to derive functor from
  the bounded above homotopy category in an abelian category with enough projectives
* Construct the flat derivability structure on the bounded above homotopy category
  of categories of modules (and categories of sheaves of modules)
* Define the product derivability structure and formalize derived functors of
  functors in several variables

## References
* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]

-/

public section
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Localization Functor

variable {C₁ : Type u₁} {C₂ : Type u₂} [Category.{v₁} C₁] [Category.{v₂} C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W₁ W₂)

/-- A localizer morphism `Φ : LocalizerMorphism W₁ W₂` is a right derivability
structure if it has right resolutions and the 2-square where the left and right functors
are localization functors for `W₁` and `W₂` are Guitart exact. -/
class IsRightDerivabilityStructure : Prop where
  hasRightResolutions : Φ.HasRightResolutions := by infer_instance
  /-- Do not use this field directly: use the more general
  `guitartExact_of_isRightDerivabilityStructure` instead,
  see also the lemma `isRightDerivabilityStructure_iff`. -/
  guitartExact' : TwoSquare.GuitartExact ((Φ.catCommSq W₁.Q W₂.Q).iso).hom

attribute [instance] IsRightDerivabilityStructure.hasRightResolutions
  IsRightDerivabilityStructure.guitartExact'

variable {D₁ D₂ : Type*} [Category* D₁] [Category* D₂] (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂] (F : D₁ ⥤ D₂)

set_option backward.defeqAttrib.useBackward true in
lemma isRightDerivabilityStructure_iff [Φ.HasRightResolutions] (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F) :
    Φ.IsRightDerivabilityStructure ↔ TwoSquare.GuitartExact e.hom := by
  have : Φ.IsRightDerivabilityStructure ↔
      TwoSquare.GuitartExact ((Φ.catCommSq W₁.Q W₂.Q).iso).hom :=
    ⟨fun h => h.guitartExact', fun h => ⟨inferInstance, h⟩⟩
  rw [this]
  let e' := (Φ.catCommSq W₁.Q W₂.Q).iso
  let E₁ := Localization.uniq W₁.Q L₁ W₁
  let E₂ := Localization.uniq W₂.Q L₂ W₂
  let e₁ : W₁.Q ⋙ E₁.functor ≅ L₁ := compUniqFunctor W₁.Q L₁ W₁
  let e₂ : W₂.Q ⋙ E₂.functor ≅ L₂ := compUniqFunctor W₂.Q L₂ W₂
  let e'' : (Φ.functor ⋙ W₂.Q) ⋙ E₂.functor ≅ (W₁.Q ⋙ E₁.functor) ⋙ F :=
    associator _ _ _ ≪≫ isoWhiskerLeft _ e₂ ≪≫ e ≪≫ isoWhiskerRight e₁.symm F
  let e''' : Φ.localizedFunctor W₁.Q W₂.Q ⋙ E₂.functor ≅ E₁.functor ⋙ F :=
    liftNatIso W₁.Q W₁ _ _ _ _ e''
  have : TwoSquare.vComp' e'.hom e'''.hom e₁ e₂ = e.hom := by
    ext X₁
    rw [TwoSquare.vComp'_app, liftNatIso_hom, liftNatTrans_app]
    simp only [Functor.comp_obj, Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom,
      Iso.symm_hom, NatTrans.comp_app, Functor.associator_hom_app, whiskerLeft_app,
      whiskerRight_app, id_comp, assoc, e'']
    dsimp [Lifting.iso]
    rw [F.map_id, id_comp, ← F.map_comp, Iso.inv_hom_id_app, F.map_id, comp_id,
      ← Functor.map_comp_assoc]
    erw [show (CatCommSq.iso Φ.functor W₁.Q W₂.Q (localizedFunctor Φ W₁.Q W₂.Q)).hom =
      (Lifting.iso W₁.Q W₁ _ _).inv by rfl, Iso.inv_hom_id_app]
    simp
  rw [← TwoSquare.GuitartExact.vComp'_iff_of_equivalences e'.hom E₁ E₂ e''' e₁ e₂, this]

instance guitartExact_of_isRightDerivabilityStructure' [h : Φ.IsRightDerivabilityStructure]
    (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F) : TwoSquare.GuitartExact e.hom := by
  simpa only [Φ.isRightDerivabilityStructure_iff L₁ L₂ F e] using h

instance guitartExact_of_isRightDerivabilityStructure [Φ.IsRightDerivabilityStructure] :
    TwoSquare.GuitartExact ((Φ.catCommSq L₁ L₂).iso).hom :=
  guitartExact_of_isRightDerivabilityStructure' _ _ _ _ _

instance [W₁.ContainsIdentities] : (LocalizerMorphism.id W₁).HasRightResolutions :=
  fun X₂ => ⟨RightResolution.mk (𝟙 X₂) (W₁.id_mem X₂)⟩

set_option backward.defeqAttrib.useBackward true in
instance [W₁.ContainsIdentities] : (LocalizerMorphism.id W₁).IsRightDerivabilityStructure := by
  rw [(LocalizerMorphism.id W₁).isRightDerivabilityStructure_iff W₁.Q W₁.Q (𝟭 W₁.Localization)
    (Iso.refl _)]
  dsimp
  exact TwoSquare.guitartExact_id W₁.Q

/-- A localizer morphism `Φ : LocalizerMorphism W₁ W₂` is a left derivability
structure if it has left resolutions and the 2-square where the top and bottom functors
are localization functors for `W₁` and `W₂` is Guitart exact. -/
class IsLeftDerivabilityStructure : Prop where
  hasLeftResolutions : Φ.HasLeftResolutions := by infer_instance
  /-- Do not use this field directly: use the more general
  `guitartExact_of_isLeftDerivabilityStructure` instead,
  see also the lemma `isLeftDerivabilityStructure_iff`. -/
  guitartExact' : TwoSquare.GuitartExact ((Φ.catCommSq W₁.Q W₂.Q).iso).inv

attribute [instance] IsLeftDerivabilityStructure.hasLeftResolutions
  IsLeftDerivabilityStructure.guitartExact'

set_option backward.isDefEq.respectTransparency false in
lemma isLeftDerivabilityStructure_iff_op :
    Φ.IsLeftDerivabilityStructure ↔
      Φ.op.IsRightDerivabilityStructure := by
  let F := Φ.localizedFunctor W₁.Q W₂.Q
  let e : Φ.functor ⋙ W₂.Q ≅ W₁.Q ⋙ F := (Φ.catCommSq W₁.Q W₂.Q).iso
  let e' : Φ.functor.op ⋙ W₂.Q.op ≅ W₁.Q.op ⋙ F.op := NatIso.op e.symm
  have eq : TwoSquare.GuitartExact e'.hom ↔ TwoSquare.GuitartExact e.inv :=
    TwoSquare.guitartExact_op_iff _
  constructor
  · rintro ⟨_, _⟩
    rwa [Φ.op.isRightDerivabilityStructure_iff _ _ _ e', eq]
  · intro
    have : Φ.HasLeftResolutions := by
      rw [hasLeftResolutions_iff_op]
      infer_instance
    refine ⟨inferInstance, ?_⟩
    rw [← eq]
    exact Φ.op.guitartExact_of_isRightDerivabilityStructure' _ _ _ e'

lemma isLeftDerivabilityStructure_iff [Φ.HasLeftResolutions] (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F) :
    Φ.IsLeftDerivabilityStructure ↔ TwoSquare.GuitartExact e.inv := by
  rw [isLeftDerivabilityStructure_iff_op,
    Φ.op.isRightDerivabilityStructure_iff L₁.op L₂.op F.op (NatIso.op e.symm),
    ← TwoSquare.guitartExact_op_iff e.inv]
  rfl

instance guitartExact_of_isLeftDerivabilityStructure' [h : Φ.IsLeftDerivabilityStructure]
    (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F) : TwoSquare.GuitartExact e.inv := by
  simpa only [Φ.isLeftDerivabilityStructure_iff L₁ L₂ F e] using h

instance guitartExact_of_isLeftDerivabilityStructure [Φ.IsLeftDerivabilityStructure] :
    TwoSquare.GuitartExact ((Φ.catCommSq L₁ L₂).iso).inv :=
  guitartExact_of_isLeftDerivabilityStructure' _ _ _ _ _

instance [W₁.ContainsIdentities] : (LocalizerMorphism.id W₁).HasLeftResolutions :=
  fun X₂ => ⟨LeftResolution.mk (𝟙 X₂) (W₁.id_mem X₂)⟩

set_option backward.defeqAttrib.useBackward true in
instance [W₁.ContainsIdentities] : (LocalizerMorphism.id W₁).IsLeftDerivabilityStructure := by
  rw [(LocalizerMorphism.id W₁).isLeftDerivabilityStructure_iff W₁.Q W₁.Q (𝟭 W₁.Localization)
    (Iso.refl _)]
  dsimp
  exact TwoSquare.guitartExact_id' W₁.Q

end LocalizerMorphism

end CategoryTheory
