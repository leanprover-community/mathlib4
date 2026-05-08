/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.CategoryTheory.Monoidal.Types.Coyoneda

/-!
# Enriched ordinary categories

If `V` is a monoidal category, a `V`-enriched category `C` does not need
to be a category. However, when we have both `Category C` and `EnrichedCategory V C`,
we may require that the type of morphisms `X ⟶ Y` in `C` identify to
`𝟙_ V ⟶ EnrichedCategory.Hom X Y`. This data shall be packaged in the
typeclass `EnrichedOrdinaryCategory V C`.

In particular, if `C` is a `V`-enriched category, it is shown that
the "underlying" category `ForgetEnrichment V C` is equipped with a
`EnrichedOrdinaryCategory V C` instance.

Simplicial categories are implemented in `AlgebraicTopology.SimplicialCategory.Basic`
using an abbreviation for `EnrichedOrdinaryCategory SSet C`.

-/

@[expose] public section

universe v' v v'' u u' u''

open CategoryTheory Category MonoidalCategory Opposite

namespace CategoryTheory

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
  (C : Type u) [Category.{v} C]

/-- An enriched ordinary category is a category `C` that is also enriched
over a category `V` in such a way that morphisms `X ⟶ Y` in `C` identify
to morphisms `𝟙_ V ⟶ (X ⟶[V] Y)` in `V`. -/
class EnrichedOrdinaryCategory extends EnrichedCategory V C where
  /-- morphisms `X ⟶ Y` in the category identify morphisms `𝟙_ V ⟶ (X ⟶[V] Y)` in `V` -/
  homEquiv {X Y : C} : (X ⟶ Y) ≃ (𝟙_ V ⟶ (X ⟶[V] Y))
  homEquiv_id (X : C) : homEquiv (𝟙 X) = eId V X := by cat_disch
  homEquiv_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    homEquiv (f ≫ g) = (λ_ _).inv ≫ (homEquiv f ⊗ₘ homEquiv g) ≫
      eComp V X Y Z := by cat_disch

variable [EnrichedOrdinaryCategory V C] {C}

/-- The bijection `(X ⟶ Y) ≃ (𝟙_ V ⟶ (X ⟶[V] Y))` given by a
`EnrichedOrdinaryCategory` instance. -/
def eHomEquiv {X Y : C} : (X ⟶ Y) ≃ (𝟙_ V ⟶ (X ⟶[V] Y)) :=
  EnrichedOrdinaryCategory.homEquiv

@[simp]
lemma eHomEquiv_id (X : C) : eHomEquiv V (𝟙 X) = eId V X :=
  EnrichedOrdinaryCategory.homEquiv_id _

@[reassoc]
lemma eHomEquiv_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv V (f ≫ g) = (λ_ _).inv ≫ (eHomEquiv V f ⊗ₘ eHomEquiv V g) ≫ eComp V X Y Z :=
  EnrichedOrdinaryCategory.homEquiv_comp _ _

/-- The morphism `(X' ⟶[V] Y) ⟶ (X ⟶[V] Y)` induced by a morphism `X ⟶ X'`. -/
def eHomWhiskerRight {X X' : C} (f : X ⟶ X') (Y : C) :
    (X' ⟶[V] Y) ⟶ (X ⟶[V] Y) :=
  (λ_ _).inv ≫ eHomEquiv V f ▷ _ ≫ eComp V X X' Y

@[simp]
lemma eHomWhiskerRight_id (X Y : C) : eHomWhiskerRight V (𝟙 X) Y = 𝟙 _ := by
  simp [eHomWhiskerRight]

@[simp, reassoc]
lemma eHomWhiskerRight_comp {X X' X'' : C} (f : X ⟶ X') (f' : X' ⟶ X'') (Y : C) :
    eHomWhiskerRight V (f ≫ f') Y = eHomWhiskerRight V f' Y ≫ eHomWhiskerRight V f Y := by
  dsimp [eHomWhiskerRight]
  rw [assoc, assoc, eHomEquiv_comp, comp_whiskerRight_assoc, comp_whiskerRight_assoc, ← e_assoc',
    tensorHom_def', comp_whiskerRight_assoc, id_whiskerLeft, comp_whiskerRight_assoc,
    ← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight_assoc,
    comp_whiskerRight_assoc, leftUnitor_inv_whiskerRight_assoc,
    ← associator_inv_naturality_left_assoc, Iso.inv_hom_id_assoc,
    ← whisker_exchange_assoc, id_whiskerLeft_assoc, Iso.inv_hom_id_assoc]

/-- Whiskering commutes with the enriched composition. -/
@[reassoc]
lemma eComp_eHomWhiskerRight {X X' : C} (f : X ⟶ X') (Y Z : C) :
    eComp V X' Y Z ≫ eHomWhiskerRight V f Z =
      eHomWhiskerRight V f Y ▷ _ ≫ eComp V X Y Z := by
  dsimp [eHomWhiskerRight]
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc]
  simp [e_assoc']

/-- The morphism `(X ⟶[V] Y) ⟶ (X ⟶[V] Y')` induced by a morphism `Y ⟶ Y'`. -/
def eHomWhiskerLeft (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    (X ⟶[V] Y) ⟶ (X ⟶[V] Y') :=
  (ρ_ _).inv ≫ _ ◁ eHomEquiv V g ≫ eComp V X Y Y'

@[simp]
lemma eHomWhiskerLeft_id (X Y : C) : eHomWhiskerLeft V X (𝟙 Y) = 𝟙 _ := by
  simp [eHomWhiskerLeft]

@[simp, reassoc]
lemma eHomWhiskerLeft_comp (X : C) {Y Y' Y'' : C} (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    eHomWhiskerLeft V X (g ≫ g') = eHomWhiskerLeft V X g ≫ eHomWhiskerLeft V X g' := by
  dsimp [eHomWhiskerLeft]
  rw [assoc, assoc, eHomEquiv_comp, MonoidalCategory.whiskerLeft_comp_assoc,
    MonoidalCategory.whiskerLeft_comp_assoc, ← e_assoc, tensorHom_def,
    MonoidalCategory.whiskerRight_id_assoc, MonoidalCategory.whiskerLeft_comp_assoc,
    MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.whiskerLeft_comp_assoc,
    whiskerLeft_rightUnitor_assoc, whiskerLeft_rightUnitor_inv_assoc,
    triangle_assoc_comp_left_inv_assoc, MonoidalCategory.whiskerRight_id_assoc,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    associator_inv_naturality_right_assoc, Iso.hom_inv_id_assoc,
    whisker_exchange_assoc, MonoidalCategory.whiskerRight_id_assoc, Iso.inv_hom_id_assoc]

/-- Whiskering commutes with the enriched composition. -/
@[reassoc]
lemma eComp_eHomWhiskerLeft (X Y : C) {Z Z' : C} (g : Z ⟶ Z') :
    eComp V X Y Z ≫ eHomWhiskerLeft V X g =
      _ ◁ eHomWhiskerLeft V Y g ≫ eComp V X Y Z' := by
  dsimp [eHomWhiskerLeft]
  rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc]
  simp

/-- Given an isomorphism `α : Y ≅ Y₁` in C, the enriched composition map
`eComp V X Y Z : (X ⟶[V] Y) ⊗ (Y ⟶[V] Z) ⟶ (X ⟶[V] Z)` factors through the `V`
object `(X ⟶[V] Y₁) ⊗ (Y₁ ⟶[V] Z)` via the map defined by whiskering in the
middle with `α.hom` and `α.inv`. -/
@[reassoc]
lemma eHom_whisker_cancel {X Y Y₁ Z : C} (α : Y ≅ Y₁) :
    eHomWhiskerLeft V X α.hom ▷ _ ≫ _ ◁ eHomWhiskerRight V α.inv Z ≫
      eComp V X Y₁ Z = eComp V X Y Z := by
  dsimp [eHomWhiskerLeft, eHomWhiskerRight]
  simp only [MonoidalCategory.whiskerLeft_comp_assoc, whisker_assoc_symm,
    triangle_assoc_comp_left_inv_assoc, e_assoc', assoc]
  simp only [← comp_whiskerRight_assoc]
  change (eHomWhiskerLeft V X α.hom ≫ eHomWhiskerLeft V X α.inv) ▷ _ ≫ _ = _
  simp [← eHomWhiskerLeft_comp]

@[reassoc]
lemma eHom_whisker_cancel_inv {X Y Y₁ Z : C} (α : Y ≅ Y₁) :
    eHomWhiskerLeft V X α.inv ▷ _ ≫ _ ◁ eHomWhiskerRight V α.hom Z ≫
      eComp V X Y Z = eComp V X Y₁ Z := eHom_whisker_cancel V α.symm

@[reassoc]
lemma eHom_whisker_exchange {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    eHomWhiskerLeft V X' g ≫ eHomWhiskerRight V f Y' =
      eHomWhiskerRight V f Y ≫ eHomWhiskerLeft V X g := by
  dsimp [eHomWhiskerLeft, eHomWhiskerRight]
  rw [assoc, assoc, assoc, assoc, leftUnitor_inv_naturality_assoc,
    whisker_exchange_assoc, ← e_assoc, leftUnitor_tensor_inv_assoc,
    associator_inv_naturality_left_assoc, Iso.hom_inv_id_assoc,
    ← comp_whiskerRight_assoc, whisker_exchange_assoc,
    MonoidalCategory.whiskerRight_id_assoc, assoc, Iso.inv_hom_id_assoc,
    whisker_exchange_assoc, MonoidalCategory.whiskerRight_id_assoc, Iso.inv_hom_id_assoc]

attribute [local simp] eHom_whisker_exchange

variable (C) in
/-- The bifunctor `Cᵒᵖ ⥤ C ⥤ V` which sends `X : Cᵒᵖ` and `Y : C` to `X ⟶[V] Y`. -/
@[simps]
def eHomFunctor : Cᵒᵖ ⥤ C ⥤ V where
  obj X :=
    { obj := fun Y => X.unop ⟶[V] Y
      map := fun φ => eHomWhiskerLeft V X.unop φ }
  map φ :=
    { app := fun Y => eHomWhiskerRight V φ.unop Y }

instance ForgetEnrichment.enrichedOrdinaryCategory {D : Type*} [EnrichedCategory V D] :
    EnrichedOrdinaryCategory V (ForgetEnrichment V D) where
  toEnrichedCategory := inferInstanceAs (EnrichedCategory V D)
  homEquiv := Equiv.refl _
  homEquiv_id _ := Category.id_comp _
  homEquiv_comp _ _ := Category.assoc _ _ _

/-- If `D` is already an enriched ordinary category, there is a canonical functor from `D` to
`ForgetEnrichment V D`. -/
@[simps]
def ForgetEnrichment.equivInverse (D : Type u'') [Category.{v''} D] [EnrichedOrdinaryCategory V D] :
    D ⥤ ForgetEnrichment V D where
  obj X := .of V X
  map f := ForgetEnrichment.homOf V (eHomEquiv V f)
  map_comp f g := by simp [eHomEquiv_comp]

/-- If `D` is already an enriched ordinary category, there is a canonical functor from
`ForgetEnrichment V D` to `D`. -/
@[simps]
def ForgetEnrichment.equivFunctor (D : Type u'') [Category.{v''} D] [EnrichedOrdinaryCategory V D] :
    ForgetEnrichment V D ⥤ D where
  obj X := ForgetEnrichment.to V X
  map f := (eHomEquiv V).symm (ForgetEnrichment.homTo V f)
  map_id X := by rw [ForgetEnrichment.homTo_id, ← eHomEquiv_id, Equiv.symm_apply_apply]
  map_comp {X} {Y} {Z} f g := Equiv.injective
    (eHomEquiv V (X := ForgetEnrichment.to V X) (Y := ForgetEnrichment.to V Z))
    (by simp [eHomEquiv_comp])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `D` is already an enriched ordinary category, it is equivalent to `ForgetEnrichment V D`. -/
@[simps]
def ForgetEnrichment.equiv {D : Type u''} [Category.{v''} D] [EnrichedOrdinaryCategory V D] :
    ForgetEnrichment V D ≌ D where
  functor := equivFunctor V D
  inverse := equivInverse V D
  unitIso := NatIso.ofComponents (fun X => Iso.refl _)
  counitIso := NatIso.ofComponents (fun X => Iso.refl _)
  functor_unitIso_comp X := Equiv.injective
    (eHomEquiv V (X := ForgetEnrichment.to V X) (Y := ForgetEnrichment.to V X)) (by simp)

/-- enriched coyoneda functor `(X ⟶[V] _) : C ⥤ V`. -/
abbrev eCoyoneda (X : C) := (eHomFunctor V C).obj (op X)

section TransportEnrichment

variable {V} {W : Type u''} [Category.{v''} W] [MonoidalCategory W]
  (F : V ⥤ W) [F.LaxMonoidal]
  (C)

instance : Category (TransportEnrichment F C) := inferInstanceAs (Category C)

/-- If `C` is an ordinary enriched category, the category structure on `TransportEnrichment F C`
is trivially equivalent to the one on `C` itself. -/
def TransportEnrichment.ofOrdinaryEnrichedCategoryEquiv : TransportEnrichment F C ≌ C :=
  Equivalence.refl

open EnrichedCategory

set_option backward.isDefEq.respectTransparency false in
/-- If for a lax monoidal functor `F : V ⥤ W` the canonical function
`(𝟙_ V ⟶ v) → (𝟙_ W ⟶ F.obj v)` is bijective, and `C` is an enriched ordinary category on `V`,
then `F` induces the structure of a `W`-enriched ordinary category on `TransportEnrichment F C`,
i.e. on the same underlying category `C`. -/
@[implicit_reducible]
def TransportEnrichment.enrichedOrdinaryCategory
    (e : ∀ v : V, (𝟙_ V ⟶ v) ≃ (𝟙_ W ⟶ F.obj v))
    (h : ∀ v : V, ∀ f : 𝟙_ V ⟶ v, e v f = Functor.LaxMonoidal.ε F ≫ F.map f) :
    EnrichedOrdinaryCategory W (TransportEnrichment F C) where
  homEquiv {X Y} := (eHomEquiv V (C := C)).trans (e (Hom (C := C) X Y))
  homEquiv_id {X} := by simpa using h _ (eId V _)
  homEquiv_comp f g := by
    dsimp +instances [instEnrichedCategoryTransportEnrichment]
    rw [h, h, h, ← tensorHom_comp_tensorHom_assoc, eComp_eq, tensorHom_def_assoc,
      whiskerRight_id_assoc, unitors_inv_equal, Iso.inv_hom_id_assoc,
      Functor.LaxMonoidal.μ_natural_assoc, Functor.LaxMonoidal.right_unitality_inv_assoc,
      eHomEquiv_comp, ← F.map_comp, ← F.map_comp, unitors_inv_equal]

section Equiv

variable {W : Type u''} [Category.{v''} W] [MonoidalCategory W]
  (F : V ⥤ W) [F.LaxMonoidal]
  (D : Type u) [EnrichedCategory V D]
  (e : ∀ v : V, (𝟙_ V ⟶ v) ≃ (𝟙_ W ⟶ F.obj v))
  (h : ∀ (v : V) (f : 𝟙_ V ⟶ v), (e v) f = Functor.LaxMonoidal.ε F ≫ F.map f)

set_option backward.isDefEq.respectTransparency false in
/-- The functor that makes up `TransportEnrichment.forgetEnrichmentEquiv`. -/
@[simps]
def TransportEnrichment.forgetEnrichmentEquivFunctor :
    TransportEnrichment F (ForgetEnrichment V D) ⥤
      ForgetEnrichment W (TransportEnrichment F D) where
  obj X := ForgetEnrichment.of W X
  map {X} {Y} f := ForgetEnrichment.homOf W <| (e (Hom (C := ForgetEnrichment V D) X Y)) <|
    ForgetEnrichment.homTo V f
  map_id X := by
    rw [h, ForgetEnrichment.homTo_id, ← TransportEnrichment.eId_eq]
    simp [ForgetEnrichment.to]
  map_comp f g := by
    rw [h, h, h, ForgetEnrichment.homTo_comp, F.map_comp, F.map_comp, ← Category.assoc,
      ← Functor.LaxMonoidal.left_unitality_inv, Category.assoc, Category.assoc, Category.assoc,
      Category.assoc, ← Functor.LaxMonoidal.μ_natural_assoc, ← TransportEnrichment.eComp_eq,
      ← ForgetEnrichment.homOf_comp, leftUnitor_inv_naturality_assoc, ← tensorHom_def'_assoc,
      tensorHom_comp_tensorHom_assoc]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse functor that makes up `TransportEnrichment.forgetEnrichmentEquiv`. -/
@[simps]
def TransportEnrichment.forgetEnrichmentEquivInverse :
    ForgetEnrichment W (TransportEnrichment F D) ⥤ TransportEnrichment F (ForgetEnrichment V D)
      where
  obj X := ForgetEnrichment.of V (ForgetEnrichment.to (C := TransportEnrichment F D) W X)
  map f := ForgetEnrichment.homOf V ((e _).symm (ForgetEnrichment.homTo W f))
  map_id X := by
    rw [← ForgetEnrichment.homOf_eId]
    congr 1
    apply Equiv.injective (e _)
    rw [ForgetEnrichment.homTo_id, Equiv.apply_symm_apply, h, TransportEnrichment.eId_eq]
  map_comp f g := by
    rw [← ForgetEnrichment.homOf_comp]
    congr
    apply Equiv.injective (e _)
    rw [Equiv.apply_symm_apply, h]
    simp only [ForgetEnrichment.homTo_comp, eComp_eq, Category.assoc, Functor.map_comp]
    slice_rhs 1 3 =>
      rw [← Functor.LaxMonoidal.left_unitality_inv, Category.assoc, Category.assoc,
        ← Functor.LaxMonoidal.μ_natural, ← leftUnitor_inv_comp_tensorHom_assoc,
        tensorHom_comp_tensorHom_assoc]
    simp [← h]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `D` is a `V`-enriched category, then forgetting the enrichment and transporting the resulting
enriched ordinary category along a functor `F : V ⥤ W`, for which
`f ↦ Functor.LaxMonoidal.ε F ≫ F.map f` has an inverse, results in a category equivalent to
transporting along `F` and then forgetting about the resulting `W`-enrichment. -/
@[simps]
def TransportEnrichment.forgetEnrichmentEquiv : TransportEnrichment F (ForgetEnrichment V D) ≌
    ForgetEnrichment W (TransportEnrichment F D) where
  functor := forgetEnrichmentEquivFunctor _ _ e h
  inverse := forgetEnrichmentEquivInverse _ _ e h
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) fun f => by
    simp [ForgetEnrichment.to, ForgetEnrichment.of]
  functor_unitIso_comp X := by
    simp only [Functor.id_obj, forgetEnrichmentEquivFunctor_obj, Functor.comp_obj,
      forgetEnrichmentEquivInverse_obj, ForgetEnrichment.to_of, NatIso.ofComponents_hom_app,
      Iso.refl_hom, forgetEnrichmentEquivFunctor_map, h, Category.comp_id]
    rw [← ForgetEnrichment.homOf_eId, TransportEnrichment.eId_eq, ForgetEnrichment.homTo_id]
    rfl

end Equiv

end TransportEnrichment

section full_subcategory

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
  {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]

/-- A full subcategory of an enriched ordinary category is an enriched ordinary category. -/
instance (P : ObjectProperty C) :
    EnrichedOrdinaryCategory V (ObjectProperty.FullSubcategory P) where
  Hom X Y := X.obj ⟶[V] Y.obj
  id X := eId V X.obj
  comp X Y Z := eComp V X.obj Y.obj Z.obj
  homEquiv {X} {Y} := P.fullyFaithfulι.homEquiv.trans (eHomEquiv V)
  homEquiv_id {X} := by
    change _ = eId V X.obj
    rw [← eHomEquiv_id]
    rfl
  homEquiv_comp f g := by
    simp only [ObjectProperty.ι_obj, Equiv.trans_apply]
    change (eHomEquiv V) (P.ι.map (f ≫ g)) = _
    rw [Functor.map_comp, eHomEquiv_comp]
    rfl

end full_subcategory

end CategoryTheory
