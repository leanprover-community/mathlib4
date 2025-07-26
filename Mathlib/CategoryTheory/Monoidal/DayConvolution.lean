/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Monoidal.ExternalProduct.KanExtension
import Mathlib.CategoryTheory.Products.Associator

/-!
# Day convolution monoidal structure

Given functors `F G : C ⥤ V` between two monoidal categories,
this file defines a typeclass `DayConvolution` on functors `F` `G` that contains
a functor `F ⊛ G`, as well as the required data to exhibit `F ⊛ G` as a pointwise
left Kan extension of `F ⊠ G` (see `Mathlib/CategoryTheory/Monoidal/ExternalProduct/Basic.lean`
for the definition) along the tensor product of `C`.
Such a functor is called a Day convolution of `F` and `G`, and
although we do not show it yet, this operation defines a monoidal structure on `C ⥤ V`.

We also define a typeclass `DayConvolutionUnit` on a functor `U : C ⥤ V` that bundle the data
required to make it a unit for the Day convolution monoidal structure: said data is that of
a map `𝟙_ V ⟶ U.obj (𝟙_ C)` that exhibits `U` as a pointwise left Kan extension of
`fromPUnit (𝟙_ V)` along `fromPUnit (𝟙_ C)`.

## References
- [nLab page: Day convolution](https://ncatlab.org/nlab/show/Day+convolution)

## TODOs (@robin-carlier)
- Braided/symmetric case.
- Define a typeclass `DayConvolutionMonoidalCategory` extending `MonoidalCategory`
- Characterization of lax monoidal functors out of a day convolution monoidal category.
- Case `V = Type u` and its universal property.

-/

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory.MonoidalCategory
open scoped ExternalProduct

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V]
  [MonoidalCategory C] [MonoidalCategory V]

/-- A `DayConvolution` structure on functors `F G : C ⥤ V` is the data of
a functor `F ⊛ G : C ⥤ V`, along with a unit `F ⊠ G ⟶ tensor C ⋙ F ⊛ G`
that exhibits this functor as a pointwise left Kan extension of `F ⊠ G` along
`tensor C`. This is a `class` used to prove various property of such extensions,
but registering global instances of this class is probably a bad idea. -/
class DayConvolution (F G : C ⥤ V) where
  /-- The chosen convolution between the functors. Denoted `F ⊛ G`. -/
  convolution : C ⥤ V
  /-- The chosen convolution between the functors. -/
  unit (F) (G) : F ⊠ G ⟶ tensor C ⋙ convolution
  /-- The transformation `unit` exhibits `F ⊛ G` as a pointwise left Kan extension
  of `F ⊠ G` along `tensor C`. -/
  isPointwiseLeftKanExtensionUnit (F G) :
    (Functor.LeftExtension.mk (convolution) unit).IsPointwiseLeftKanExtension

namespace DayConvolution

open scoped Prod

section

/-- A notation for the Day convolution of two functors. -/
scoped infixr:80 " ⊛ " => convolution

variable (F G : C ⥤ V)

instance leftKanExtension [DayConvolution F G] :
    (F ⊛ G).IsLeftKanExtension (unit F G) :=
  isPointwiseLeftKanExtensionUnit F G|>.isLeftKanExtension

variable {F G}

/-- Two day convolution structures on the same functors gives an isomorphic functor. -/
def uniqueUpToIso (h : DayConvolution F G) (h' : DayConvolution F G) :
    h.convolution ≅ h'.convolution :=
  Functor.leftKanExtensionUnique h.convolution h.unit h'.convolution h'.unit

@[reassoc (attr := simp)]
lemma unit_uniqueUpToIso_hom (h : DayConvolution F G) (h' : DayConvolution F G) :
    h.unit ≫ Functor.whiskerLeft (tensor C) (h.uniqueUpToIso h').hom = h'.unit := by
  simp [uniqueUpToIso]

@[reassoc (attr := simp)]
lemma unit_uniqueUpToIso_inv (h : DayConvolution F G) (h' : DayConvolution F G) :
    h'.unit ≫ Functor.whiskerLeft (tensor C) (h.uniqueUpToIso h').inv = h.unit := by
  simp [uniqueUpToIso]

variable (F G) [DayConvolution F G]

section unit

variable {x x' y y' : C}

@[reassoc (attr := simp)]
lemma unit_naturality (f : x ⟶ x') (g : y ⟶ y') :
    (F.map f ⊗ₘ G.map g) ≫ (unit F G).app (x', y') =
    (unit F G).app (x, y) ≫ (F ⊛ G).map (f ⊗ₘ g) := by
  simpa [tensorHom_def] using (unit F G).naturality (f ×ₘ g)

variable (y) in
@[reassoc (attr := simp)]
lemma whiskerRight_comp_unit_app (f : x ⟶ x') :
    F.map f ▷ G.obj y ≫ (unit F G).app (x', y) =
    (unit F G).app (x, y) ≫ (F ⊛ G).map (f ▷ y) := by
  simpa [tensorHom_def] using (unit F G).naturality (f ×ₘ 𝟙 _)

variable (x) in
@[reassoc (attr := simp)]
lemma whiskerLeft_comp_unit_app (g : y ⟶ y') :
    F.obj x ◁ G.map g ≫ (unit F G).app (x, y') =
    (unit F G).app (x, y) ≫ (F ⊛ G).map (x ◁ g) := by
  simpa [tensorHom_def] using (unit F G).naturality (𝟙 _ ×ₘ g)

end unit

variable {F G}

section map

variable {F' G' : C ⥤ V} [DayConvolution F' G']

/-- The morphism between day convolutions (provided they exist) induced by a pair of morphisms. -/
def map (f : F ⟶ F') (g : G ⟶ G') : F ⊛ G ⟶ F' ⊛ G' :=
  Functor.descOfIsLeftKanExtension (F ⊛ G) (unit F G) (F' ⊛ G') <|
    (externalProductBifunctor C C V).map (f ×ₘ g) ≫ unit F' G'

variable (f : F ⟶ F') (g : G ⟶ G') (x y : C)

@[reassoc (attr := simp)]
lemma unit_app_map_app :
    (unit F G).app (x, y) ≫ (map f g).app (x ⊗ y : C) =
    (f.app x ⊗ₘ g.app y) ≫ (unit F' G').app (x, y) := by
  simpa [tensorHom_def] using
    (Functor.descOfIsLeftKanExtension_fac_app (F ⊛ G) (unit F G) (F' ⊛ G') <|
      (externalProductBifunctor C C V).map (f ×ₘ g) ≫ unit F' G') (x, y)

end map

variable (F G)

/-- The universal property of left Kan extensions characterizes the functor
corepresented by `F ⊛ G`. -/
@[simps!]
def corepresentableBy :
    (Functor.whiskeringLeft _ _ _).obj (tensor C) ⋙ coyoneda.obj (.op <| F ⊠ G)|>.CorepresentableBy
      (F ⊛ G) where
  homEquiv := Functor.homEquivOfIsLeftKanExtension _ (unit F G) _
  homEquiv_comp := by aesop

/-- Use the fact that `(F ⊛ G).obj c` is a colimit to characterize morphisms out of it at a
point. -/
theorem convolution_hom_ext_at (c : C) {v : V} {f g : (F ⊛ G).obj c ⟶ v}
    (h : ∀ {x y : C} (u : x ⊗ y ⟶ c),
      (unit F G).app (x, y) ≫ (F ⊛ G).map u ≫ f = (unit F G).app (x, y) ≫ (F ⊛ G).map u ≫ g) :
    f = g :=
  ((isPointwiseLeftKanExtensionUnit F G) c).hom_ext (fun j ↦ by simpa using h j.hom)

section associator

open Functor

variable {D : Type u₃} [Category.{v₃} D] (K : D ⥤ V)
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorRight v)]

open MonoidalCategory.ExternalProduct

instance : (K ⊠ F ⊛ G).IsLeftKanExtension <|
    extensionUnitRight (F ⊛ G) (unit F G) K :=
  (isPointwiseLeftKanExtensionExtensionUnitRight _ _ _ <|
    isPointwiseLeftKanExtensionUnit F G).isLeftKanExtension

instance : ((F ⊛ G) ⊠ K).IsLeftKanExtension <|
    extensionUnitLeft (F ⊛ G) (unit F G) K :=
  (isPointwiseLeftKanExtensionExtensionUnitLeft _ _ _ <|
    isPointwiseLeftKanExtensionUnit F G).isLeftKanExtension


variable (H : C ⥤ V) [DayConvolution G H] [DayConvolution F (G ⊛ H)] [DayConvolution (F ⊛ G) H]

/-- The `CorepresentableBy` structure asserting that the Type-valued functor
`Y ↦ (F ⊠ G ⊠ H ⟶ (𝟭 C).prod (tensor C) ⋙ tensor C ⋙ Y)` is corepresented by
`F ⊛ G ⊛ H`. -/
@[simps]
def corepresentableBy₂ :
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((𝟭 C).prod (tensor C)) ⋙
      coyoneda.obj (.op <| F ⊠ G ⊠ H)|>.CorepresentableBy (F ⊛ G ⊛ H) where
  homEquiv :=
    (corepresentableBy F (G ⊛ H)).homEquiv.trans <|
      Functor.homEquivOfIsLeftKanExtension _ (extensionUnitRight (G ⊛ H) (unit G H) F) _
  homEquiv_comp := by aesop

/-- The `CorepresentableBy` structure asserting that the Type-valued functor
`Y ↦ ((F ⊠ G) ⊠ H ⟶ (tensor C).prod (𝟭 C) ⋙ tensor C ⋙ Y)` is corepresented by
`(F ⊛ G) ⊛ H`. -/
@[simps]
def corepresentableBy₂' :
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((tensor C).prod (𝟭 C)) ⋙
      coyoneda.obj (.op <| (F ⊠ G) ⊠ H)|>.CorepresentableBy ((F ⊛ G) ⊛ H) where
  homEquiv :=
    (corepresentableBy (F ⊛ G) H).homEquiv.trans <|
      Functor.homEquivOfIsLeftKanExtension _ (extensionUnitLeft (F ⊛ G) (unit F G) H) _
  homEquiv_comp := by aesop

/-- The isomorphism of functors between
`((F ⊠ G) ⊠ H ⟶ (tensor C).prod (𝟭 C) ⋙ tensor C ⋙ -)` and
`(F ⊠ G ⊠ H ⟶ (𝟭 C).prod (tensor C) ⋙ tensor C ⋙ -)` that coresponsds to the associator
isomorphism for Day convolution through `corepresentableBy₂` and `corepresentableBy₂`. -/
@[simps!]
def associatorCorepresentingIso :
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((tensor C).prod (𝟭 C)) ⋙
      coyoneda.obj (.op <| (F ⊠ G) ⊠ H) ≅
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((𝟭 C).prod (tensor C)) ⋙
      coyoneda.obj (.op <| F ⊠ G ⊠ H) :=
  calc
    _ ≅ (whiskeringLeft _ _ _).obj (tensor C) ⋙
          (whiskeringLeft _ _ _).obj ((tensor C).prod (𝟭 C)) ⋙
          (whiskeringLeft _ _ _).obj (prod.associativity C C C).inverse ⋙
          coyoneda.obj (.op <| (prod.associativity C C C).inverse ⋙ (F ⊠ G) ⊠ H) :=
      isoWhiskerLeft _ (isoWhiskerLeft _
        (NatIso.ofComponents fun _ ↦ Equiv.toIso <|
          (prod.associativity C C C).congrLeft.fullyFaithfulFunctor.homEquiv))
    _ ≅ (whiskeringLeft _ _ _).obj
            ((prod.associativity C C C).inverse ⋙ (tensor C).prod (𝟭 C) ⋙ tensor C) ⋙
          coyoneda.obj (.op <| (prod.associativity C C C).inverse ⋙ (F ⊠ G) ⊠ H) :=
      .refl _
    _ ≅ (whiskeringLeft _ _ _).obj ((𝟭 C).prod (tensor C) ⋙ tensor C) ⋙
          coyoneda.obj (.op <| (prod.associativity C C C).inverse ⋙ (F ⊠ G) ⊠ H) :=
      isoWhiskerRight ((whiskeringLeft _ _ _).mapIso <| NatIso.ofComponents (fun _ ↦ α_ _ _ _)) _
    _ ≅ (whiskeringLeft _ _ _).obj ((𝟭 C).prod (tensor C) ⋙ tensor C) ⋙
          coyoneda.obj (.op <| F ⊠ G ⊠ H) :=
      isoWhiskerLeft _ <|
        coyoneda.mapIso <| Iso.op <| NatIso.ofComponents (fun _ ↦ α_ _ _ _|>.symm)

/-- The asociator isomorphism for Day convolution -/
def associator : (F ⊛ G) ⊛ H ≅ F ⊛ G ⊛ H :=
  corepresentableBy₂' F G H|>.ofIso (associatorCorepresentingIso F G H)|>.uniqueUpToIso <|
    corepresentableBy₂ F G H

/-- Characterizing the forward direction of the associator isomorphism
with respect to the unit transformations. -/
@[reassoc (attr := simp)]
lemma associator_hom_unit_unit (x y z : C) :
    (unit F G).app (x, y) ▷ (H.obj z) ≫
      (unit (F ⊛ G) H).app (x ⊗ y, z) ≫
      (associator F G H).hom.app ((x ⊗ y) ⊗ z) =
    (α_ _ _ _).hom ≫
      (F.obj x ◁ (unit G H).app (y, z)) ≫
      (unit F (G ⊛ H)).app (x, y ⊗ z) ≫
      (F ⊛ G ⊛ H).map (α_ _ _ _).inv := by
  have := congrArg (fun t ↦ t.app ((x, y), z)) <|
      (corepresentableBy₂' F G H).homEquiv.rightInverse_symm <|
        (corepresentableBy₂ F G H|>.ofIso
          (associatorCorepresentingIso F G H).symm|>.homEquiv (𝟙 _))
  dsimp [associator, Coyoneda.fullyFaithful, corepresentableBy₂,
    corepresentableBy₂', Functor.CorepresentableBy.ofIso, corepresentableBy₂,
    Functor.corepresentableByEquiv, associatorCorepresentingIso] at this ⊢
  simp only [whiskerLeft_id, Category.comp_id, Category.assoc] at this
  simp only [Category.assoc, this]
  simp [Functor.FullyFaithful.homEquiv, Equivalence.fullyFaithfulFunctor, prod.associativity]

/-- Characterizing the inverse direction of the associator
with respect to the unit transformations -/
@[reassoc (attr := simp)]
lemma associator_inv_unit_unit (x y z : C) :
    F.obj x ◁ (unit G H).app (y, z) ≫
      (unit F (G ⊛ H)).app (x, y ⊗ z) ≫
      (associator F G H).inv.app (x ⊗ y ⊗ z) =
    (α_ (F.obj x) (G.obj y) (H.obj z)).inv ≫ (unit F G).app (x, y) ▷ H.obj z ≫
      (unit (F ⊛ G) H).app (x ⊗ y, z) ≫
      ((F ⊛ G) ⊛ H).map (α_ x y z).hom := by
  have := congrArg (fun t ↦ t.app (x, y, z)) <|
      (corepresentableBy₂ F G H).homEquiv.rightInverse_symm <|
        (corepresentableBy₂' F G H|>.ofIso
          (associatorCorepresentingIso F G H)|>.homEquiv (𝟙 _))
  dsimp [associator, Coyoneda.fullyFaithful, corepresentableBy₂,
    corepresentableBy₂', Functor.CorepresentableBy.ofIso, corepresentableBy₂,
    Functor.corepresentableByEquiv, associatorCorepresentingIso] at this ⊢
  simp only [whiskerRight_tensor, id_whiskerRight, Category.id_comp, Iso.inv_hom_id] at this
  simp only [this]
  simp [Functor.FullyFaithful.homEquiv, Equivalence.fullyFaithfulFunctor, prod.associativity]

variable {F G H} in
theorem associator_naturality {F' G' H' : C ⥤ V}
    [DayConvolution F' G'] [DayConvolution G' H']
    [DayConvolution F' (G' ⊛ H')] [DayConvolution (F' ⊛ G') H']
    (f : F ⟶ F') (g : G ⟶ G') (h : H ⟶ H') :
      map (map f g) h ≫
        (associator F' G' H').hom =
      (associator F G H).hom ≫ map f (map g h) := by
  apply (corepresentableBy₂' F G H)|>.homEquiv.injective
  dsimp
  ext
  simp only [externalProductBifunctor_obj_obj, Functor.comp_obj, Functor.prod_obj, tensor_obj,
    Functor.id_obj, Functor.homEquivOfIsLeftKanExtension_apply_app,
    externalProductBifunctor_map_app, Functor.leftUnitor_inv_app, whiskerLeft_id, Category.comp_id,
    corepresentableBy_homEquiv_apply_app, NatTrans.comp_app, unit_app_map_app_assoc]
  rw [associator_hom_unit_unit_assoc]
  simp only [tensorHom_def, Category.assoc, externalProductBifunctor_obj_obj, tensor_obj,
    NatTrans.naturality, unit_app_map_app_assoc]
  rw [← comp_whiskerRight_assoc, unit_app_map_app]
  simp only [Functor.comp_obj, tensor_obj, comp_whiskerRight, Category.assoc]
  rw [← whisker_exchange_assoc, associator_hom_unit_unit, whisker_exchange_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, unit_app_map_app]
  simp [tensorHom_def]

section pentagon

variable [∀ (v : V) (d : C × C),
    Limits.PreservesColimitsOfShape (CostructuredArrow ((tensor C).prod (𝟭 C)) d) (tensorRight v)]

lemma pentagon (H K : C ⥤ V)
    [DayConvolution G H] [DayConvolution (F ⊛ G) H] [DayConvolution F (G ⊛ H)]
    [DayConvolution H K] [DayConvolution G (H ⊛ K)] [DayConvolution (G ⊛ H) K]
    [DayConvolution ((F ⊛ G) ⊛ H) K] [DayConvolution (F ⊛ G) (H ⊛ K)]
    [DayConvolution (F ⊛ G ⊛ H) K] [DayConvolution F (G ⊛ H ⊛ K)]
    [DayConvolution F ((G ⊛ H) ⊛ K)] :
    map (associator F G H).hom (𝟙 K) ≫
        (associator F (G ⊛ H) K).hom ≫ map (𝟙 F) (associator G H K).hom =
      (associator (F ⊛ G) H K).hom ≫ (associator F G (H ⊛ K)).hom := by
  -- We repeatedly apply the fact that the functors are left Kan extensions
  apply Functor.hom_ext_of_isLeftKanExtension (α := unit ((F ⊛ G) ⊛ H) K)
  apply Functor.hom_ext_of_isLeftKanExtension
    (α := extensionUnitLeft ((F ⊛ G) ⊛ H) (unit (F ⊛ G) H) K)
  have : (((F ⊛ G) ⊠ H) ⊠ K).IsLeftKanExtension
    (α := extensionUnitLeft ((F ⊛ G) ⊠ H)
      (extensionUnitLeft _ (unit F G) H) K) :=
    isPointwiseLeftKanExtensionExtensionUnitLeft _ _ _
      (isPointwiseLeftKanExtensionExtensionUnitLeft _ _ _
        (isPointwiseLeftKanExtensionUnit F G))|>.isLeftKanExtension
  apply Functor.hom_ext_of_isLeftKanExtension (α := extensionUnitLeft ((F ⊛ G) ⊠ H)
      (extensionUnitLeft _ (unit F G) H) K)
  -- And then we compute...
  ext ⟨⟨⟨i, j⟩, k⟩, l⟩
  have aux :
      ((unit F G).app (i, j) ⊗ₘ (unit H K).app (k, l)) ≫
        (unit (F ⊛ G) (H ⊛ K)).app ((i ⊗ j), (k ⊗ l)) =
      (α_ (F.obj i) (G.obj j) (H.obj k ⊗ K.obj l)).hom ≫
        F.obj i ◁ G.obj j ◁ (unit H K).app (k, l) ≫ F.obj i ◁ (unit G (H ⊛ K)).app (j, (k ⊗ l)) ≫
        (unit F (G ⊛ H ⊛ K)).app (i, (j ⊗ k ⊗ l)) ≫ (F ⊛ G ⊛ H ⊛ K).map (α_ i j (k ⊗ l)).inv ≫
        (associator F G (H ⊛ K)).inv.app ((i ⊗ j) ⊗ k ⊗ l) := by
    conv_rhs => simp only [Functor.comp_obj, tensor_obj, NatTrans.naturality,
      associator_inv_unit_unit_assoc, externalProductBifunctor_obj_obj, Iso.map_hom_inv_id,
      Category.comp_id]
    simp only [tensor_whiskerLeft_symm, Category.assoc, Iso.hom_inv_id_assoc,
    ← tensorHom_def'_assoc]
  dsimp
  simp only [MonoidalCategory.whiskerLeft_id, Category.comp_id, unit_app_map_app_assoc,
    externalProductBifunctor_obj_obj, NatTrans.id_app, tensorHom_id, associator_hom_unit_unit_assoc,
    tensor_obj, NatTrans.naturality]
  conv_rhs =>
    simp only [whiskerRight_tensor_symm_assoc, Iso.inv_hom_id_assoc, ← tensorHom_def_assoc]
    rw [reassoc_of% aux]
  simp only [Iso.inv_hom_id_app_assoc, ← comp_whiskerRight_assoc, associator_hom_unit_unit F G H]
  simp only [Functor.comp_obj, tensor_obj, comp_whiskerRight, whisker_assoc, Category.assoc,
    whiskerRight_comp_unit_app_assoc (F ⊛ G ⊛ H) K l (α_ i j k).inv,
    NatTrans.naturality_assoc, NatTrans.naturality, associator_hom_unit_unit_assoc,
    externalProductBifunctor_obj_obj, unit_app_map_app_assoc, NatTrans.id_app, id_tensorHom,
    Iso.inv_hom_id_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, associator_hom_unit_unit]
  simp [← Functor.map_comp, pentagon_inv, pentagon_assoc]

end pentagon

end associator

end

end DayConvolution

/-- A `DayConvolutionUnit` structure on a functor `C ⥤ V` is the data of a pointwise
left Kan extension of `fromPUnit (𝟙_ V)` along `fromPUnit (𝟙_ C)`. Again, this is
made a class to ease proofs when constructing `DayConvolutionMonoidalCategory` structures, but one
should avoid registering it globally. -/
class DayConvolutionUnit (F : C ⥤ V) where
  /-- A "canonical" structure map `𝟙_ V ⟶ F.obj (𝟙_ C)` that defines a natural transformation
  `fromPUnit (𝟙_ V) ⟶ fromPUnit (𝟙_ C) ⋙ F`. -/
  can : 𝟙_ V ⟶ F.obj (𝟙_ C)
  /-- The canonical map `𝟙_ V ⟶ F.obj (𝟙_ C)` exhibits `F` as a pointwise left kan extension
  of `fromPUnit.{0} 𝟙_ V` along `fromPUnit.{0} 𝟙_ C`. -/
  isPointwiseLeftKanExtensionCan : Functor.LeftExtension.mk F
    ({app _ := can} : Functor.fromPUnit.{0} (𝟙_ V) ⟶
      Functor.fromPUnit.{0} (𝟙_ C) ⋙ F)|>.IsPointwiseLeftKanExtension

namespace DayConvolutionUnit

variable (U : C ⥤ V) [DayConvolutionUnit U]
open scoped DayConvolution
open ExternalProduct Functor

/-- A shorthand for the natural transformation of functors out of PUnit defined by
the canonical morphism `𝟙_ V ⟶ U.obj (𝟙_ C)` when `U` is a unit for Day convolution. -/
abbrev φ : Functor.fromPUnit.{0} (𝟙_ V) ⟶ Functor.fromPUnit.{0} (𝟙_ C) ⋙ U where
  app _ := can

/-- Since a convolution unit is a pointwise left Kan extension, maps out of it at
any object are uniquely characterized. -/
lemma hom_ext {c : C} {v : V} {g h : U.obj c ⟶ v}
    (e : ∀ f : 𝟙_ C ⟶ c, can ≫ U.map f ≫ g = can ≫ U.map f ≫ h) :
    g = h := by
  apply (isPointwiseLeftKanExtensionCan c).hom_ext
  intro j
  simpa using e j.hom

variable {D : Type u₃} [Category.{v₃} D] (K : D ⥤ V)
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ C)) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ C)) d) (tensorRight v)]

instance : (K ⊠ U).IsLeftKanExtension <| extensionUnitRight U (φ U) K :=
  isPointwiseLeftKanExtensionExtensionUnitRight
    U (φ U) K isPointwiseLeftKanExtensionCan|>.isLeftKanExtension

instance : (U ⊠ K).IsLeftKanExtension <| extensionUnitLeft U (φ U) K :=
  isPointwiseLeftKanExtensionExtensionUnitLeft
    U (φ U) K isPointwiseLeftKanExtensionCan|>.isLeftKanExtension

variable (F : C ⥤ V)

/-- A `CorepresentableBy` structure that characterizes maps out of `U ⊛ F`
by leveraging the fact that `U ⊠ F` is a left Kan extension of `(fromPUnit 𝟙_ V) ⊠ F`. -/
@[simps]
def corepresentableByLeft [DayConvolution U F] :
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((Functor.fromPUnit.{0} (𝟙_ C)).prod (𝟭 C)) ⋙
      coyoneda.obj (.op <| Functor.fromPUnit.{0} (𝟙_ V) ⊠ F)|>.CorepresentableBy (U ⊛ F) where
  homEquiv :=
    Functor.homEquivOfIsLeftKanExtension _ (DayConvolution.unit U F) _|>.trans <|
      Functor.homEquivOfIsLeftKanExtension _ (extensionUnitLeft U (φ U) F) _
  homEquiv_comp := by aesop

/-- A `CorepresentableBy` structure that characterizes maps out of `F ⊛ U` by
leveraging the fact that `F ⊠ U` is a left Kan extension of `F ⊠ (fromPUnit 𝟙_ V)`. -/
@[simps]
def corepresentableByRight [DayConvolution F U] :
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((𝟭 C).prod (Functor.fromPUnit.{0} (𝟙_ C))) ⋙
      coyoneda.obj (.op <| F ⊠ Functor.fromPUnit.{0} (𝟙_ V))|>.CorepresentableBy (F ⊛ U) where
  homEquiv :=
    Functor.homEquivOfIsLeftKanExtension _ (DayConvolution.unit F U) _|>.trans <|
      Functor.homEquivOfIsLeftKanExtension _ (extensionUnitRight U (φ U) F) _
  homEquiv_comp := by aesop

/-- The isomorphism of corepresentable functors that defines the left unitor for
Day convolution. -/
@[simps!]
def leftUnitorCorepresentingIso :
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((Functor.fromPUnit.{0} (𝟙_ C)).prod (𝟭 C)) ⋙
      coyoneda.obj (.op <| Functor.fromPUnit.{0} (𝟙_ V) ⊠ F) ≅
    coyoneda.obj (.op <| F) := by
  calc
    _ ≅ (whiskeringLeft _ _ _).obj (tensor C) ⋙
          (whiskeringLeft _ _ _).obj ((Functor.fromPUnit.{0} (𝟙_ C)).prod (𝟭 C)) ⋙
          (whiskeringLeft _ _ _).obj (prod.leftUnitorEquivalence C).inverse ⋙
          coyoneda.obj (.op <|
           (prod.leftUnitorEquivalence C).inverse ⋙ Functor.fromPUnit.{0} (𝟙_ V) ⊠ F) :=
      isoWhiskerLeft _ (isoWhiskerLeft _
        (NatIso.ofComponents fun _ ↦ Equiv.toIso <|
          (prod.leftUnitorEquivalence C).congrLeft.fullyFaithfulFunctor.homEquiv))
    _ ≅ (whiskeringLeft _ _ _).obj
            ((prod.leftUnitorEquivalence C).inverse ⋙ (Functor.fromPUnit.{0} (𝟙_ C)).prod (𝟭 C) ⋙
              tensor C) ⋙
          coyoneda.obj (.op <|
            (prod.leftUnitorEquivalence C).inverse ⋙ Functor.fromPUnit.{0} (𝟙_ V) ⊠ F) :=
      .refl _
    _ ≅ (whiskeringLeft _ _ _).obj (𝟭 _) ⋙ coyoneda.obj (.op <|
          (prod.leftUnitorEquivalence C).inverse ⋙ Functor.fromPUnit.{0} (𝟙_ V) ⊠ F) :=
      isoWhiskerRight ((whiskeringLeft _ _ _).mapIso <| NatIso.ofComponents fun _ ↦ λ_ _) _
    _ ≅ _ := coyoneda.mapIso <| Iso.op <| NatIso.ofComponents fun _ ↦ (λ_ _).symm

/-- The isomorphism of corepresentable functors that defines the right unitor for
Day convolution. -/
@[simps!]
def rightUnitorCorepresentingIso :
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((𝟭 C).prod (Functor.fromPUnit.{0} (𝟙_ C))) ⋙
      coyoneda.obj (.op <| F ⊠ Functor.fromPUnit.{0} (𝟙_ V)) ≅
    coyoneda.obj (.op <| F) := by
  calc
    _ ≅ (whiskeringLeft _ _ _).obj (tensor C) ⋙
          (whiskeringLeft _ _ _).obj ((𝟭 C).prod (Functor.fromPUnit.{0} (𝟙_ C))) ⋙
          (whiskeringLeft _ _ _).obj (prod.rightUnitorEquivalence C).inverse ⋙
          coyoneda.obj (.op <|
           (prod.rightUnitorEquivalence C).inverse ⋙ F ⊠ Functor.fromPUnit.{0} (𝟙_ V)) :=
      isoWhiskerLeft _ (isoWhiskerLeft _
        (NatIso.ofComponents fun _ ↦ Equiv.toIso <|
          (prod.rightUnitorEquivalence C).congrLeft.fullyFaithfulFunctor.homEquiv))
    _ ≅ (whiskeringLeft _ _ _).obj
            ((prod.rightUnitorEquivalence C).inverse ⋙
              ((𝟭 C).prod (Functor.fromPUnit.{0} (𝟙_ C))) ⋙ tensor C) ⋙
          coyoneda.obj (.op <|
            (prod.rightUnitorEquivalence C).inverse ⋙ F ⊠ Functor.fromPUnit.{0} (𝟙_ V)) :=
      .refl _
    _ ≅ (whiskeringLeft _ _ _).obj (𝟭 _) ⋙ coyoneda.obj (.op <|
          (prod.rightUnitorEquivalence C).inverse ⋙ F ⊠ Functor.fromPUnit.{0} (𝟙_ V)) :=
      isoWhiskerRight ((whiskeringLeft _ _ _).mapIso <| NatIso.ofComponents fun _ ↦ ρ_ _) _
    _ ≅ _ := coyoneda.mapIso <| Iso.op <| NatIso.ofComponents fun _ ↦ (ρ_ _).symm

/-- The left unitor isomorphism for Day convolution. -/
def leftUnitor [DayConvolution U F] : U ⊛ F ≅ F :=
  corepresentableByLeft U F|>.ofIso (leftUnitorCorepresentingIso F)|>.uniqueUpToIso
    <| Functor.corepresentableByEquiv.symm (.refl _)

/-- The right unitor isomorphism for Day convolution. -/
def rightUnitor [DayConvolution F U] : F ⊛ U ≅ F :=
  corepresentableByRight U F|>.ofIso (rightUnitorCorepresentingIso F)|>.uniqueUpToIso
    <| Functor.corepresentableByEquiv.symm (.refl _)

section

omit [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
  (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ C)) d) (tensorLeft v)]
variable [DayConvolution U F]

/-- Characterizing the forward direction of `leftUnitor` via the universal maps. -/
@[reassoc (attr := simp)]
lemma leftUnitor_hom_unit_app (y : C) :
    can ▷ F.obj y ≫ (DayConvolution.unit U F).app (𝟙_ C, y) ≫
      (leftUnitor U F).hom.app (𝟙_ C ⊗ y) =
    (λ_ (F.obj y)).hom ≫ F.map (λ_ y).inv := by
  have := congrArg (fun t ↦ t.app (.mk PUnit.unit, y)) <|
      (corepresentableByLeft U F).homEquiv.rightInverse_symm <|
        ((leftUnitorCorepresentingIso F).symm.hom.app F) (𝟙 _)
  dsimp [leftUnitor, Coyoneda.fullyFaithful, corepresentableByLeft,
    leftUnitorCorepresentingIso, Functor.CorepresentableBy.ofIso,
    Functor.corepresentableByEquiv] at this ⊢
  simp only [whiskerLeft_id, Category.comp_id] at this
  simp only [Category.comp_id, this]
  simp [prod.leftUnitorEquivalence, Equivalence.congrLeft, Equivalence.fullyFaithfulFunctor,
    Functor.FullyFaithful.homEquiv]

@[simp, reassoc]
lemma leftUnitor_inv_app (x : C) :
    (leftUnitor U F).inv.app x =
    (λ_ (F.obj x)).inv ≫ can ▷ F.obj x ≫ (DayConvolution.unit U F).app (𝟙_ C, x) ≫
      (U ⊛ F).map (λ_ x).hom := by
  dsimp [leftUnitor, Coyoneda.fullyFaithful, corepresentableByLeft,
    leftUnitorCorepresentingIso, Functor.CorepresentableBy.ofIso,
    Functor.corepresentableByEquiv]
  simp [prod.leftUnitorEquivalence, Equivalence.congrLeft, Equivalence.fullyFaithfulFunctor,
    Functor.FullyFaithful.homEquiv]

variable {F} in
@[reassoc (attr := simp)]
lemma leftUnitor_naturality {G : C ⥤ V} [DayConvolution U G] (f : F ⟶ G) :
    DayConvolution.map (𝟙 _) f ≫ (leftUnitor U G).hom =
    (leftUnitor U F).hom ≫ f := by
  apply Functor.hom_ext_of_isLeftKanExtension _ (DayConvolution.unit _ _) _
  apply Functor.hom_ext_of_isLeftKanExtension _ (extensionUnitLeft U (φ U) F) _
  ext
  simp [← whisker_exchange_assoc]

end

section

omit [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
  (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ C)) d) (tensorRight v)]
variable [DayConvolution F U]

/-- Characterizing the forward direction of `rightUnitor` via the universal maps. -/
@[reassoc (attr := simp)]
lemma rightUnitor_hom_unit_app (x : C) :
    F.obj x ◁ can ≫ (DayConvolution.unit F U).app (x, 𝟙_ C) ≫
      (rightUnitor U F).hom.app (x ⊗ 𝟙_ C) =
    (ρ_ _).hom ≫ F.map (ρ_ x).inv := by
  have := congrArg (fun t ↦ t.app (x, .mk PUnit.unit)) <|
      (corepresentableByRight U F).homEquiv.rightInverse_symm <|
        ((rightUnitorCorepresentingIso F).symm.hom.app F) (𝟙 _)
  dsimp [rightUnitor, Coyoneda.fullyFaithful, corepresentableByRight,
    rightUnitorCorepresentingIso, Functor.CorepresentableBy.ofIso,
    Functor.corepresentableByEquiv] at this ⊢
  simp only [MonoidalCategory.whiskerRight_id, Category.id_comp, Iso.hom_inv_id,
    Category.comp_id] at this
  simp only [Category.comp_id, this]
  simp [prod.rightUnitorEquivalence, Equivalence.congrLeft, Equivalence.fullyFaithfulFunctor,
    Functor.FullyFaithful.homEquiv]

@[simp, reassoc]
lemma rightUnitor_inv_app (x : C) :
    (rightUnitor U F).inv.app x =
    (ρ_ (F.obj x)).inv ≫ F.obj x ◁ can ≫ (DayConvolution.unit F U).app (x, 𝟙_ C) ≫
      (F ⊛ U).map (ρ_ x).hom := by
  dsimp [rightUnitor, Coyoneda.fullyFaithful, corepresentableByRight,
    rightUnitorCorepresentingIso, Functor.CorepresentableBy.ofIso,
    Functor.corepresentableByEquiv]
  simp [prod.rightUnitorEquivalence, Equivalence.congrLeft, Equivalence.fullyFaithfulFunctor,
    Functor.FullyFaithful.homEquiv]

variable {F} in
@[reassoc (attr := simp)]
lemma rightUnitor_naturality {G : C ⥤ V} [DayConvolution G U] (f : F ⟶ G) :
    DayConvolution.map f (𝟙 _) ≫ (rightUnitor U G).hom =
    (rightUnitor U F).hom ≫ f := by
  apply Functor.hom_ext_of_isLeftKanExtension _ (DayConvolution.unit _ _) _
  apply Functor.hom_ext_of_isLeftKanExtension _ (extensionUnitRight U (φ U) F) _
  ext
  simp [whisker_exchange_assoc]

end

section

omit [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
  (CostructuredArrow (fromPUnit.{0} (𝟙_ C)) d) (tensorLeft v)]

/-- An extension of `F ⋙ tensorLeft (𝟙_ V)` along `tensorLeft (𝟙_ C)`,
which we will show is a left Kan extension. This is useful for working with
morphisms out of `U ⊛ F` without going through an external product.
Note that this extension is exactly the one that characterizes the left
unitors for Day convolutions in `leftUnitor_hom_unit_app`. -/
@[simps]
def unitLeft (F : C ⥤ V) [DayConvolution U F] :
    F ⋙ tensorLeft (𝟙_ V) ⟶ tensorLeft (𝟙_ C) ⋙ U ⊛ F where
  app x := can ▷ (F.obj x) ≫ (DayConvolution.unit U F).app (𝟙_ C, x)
  naturality {x y} f := by
    dsimp
    simp [← id_tensorHom, Category.assoc, ← tensorHom_id,
      ← tensor_comp_assoc, Category.comp_id, Category.id_comp,
      ← DayConvolution.unit_naturality, Functor.map_id]

/-- An extension of `K ⋙ tensorLeft (𝟙_ V)` along ` Prod.sectR (𝟙_ C) D`
(for any `K : _ ⥤ V`), which we will show is a left Kan extension.
This is useful for working with morphisms out of `U ⊠ K`. -/
@[simps]
def unitLeftExternal {D : Type u₃} [Category D] (K : D ⥤ V) :
    K ⋙ tensorLeft (𝟙_ V) ⟶ Prod.sectR (𝟙_ C) D ⋙ U ⊠ K where
  app y := can ▷ _
  naturality {x y} f := by simp [← whisker_exchange]

instance isLeftKanExtensionUnitLeftExternal
    {D : Type u₃} [Category D] (K : D ⥤ V) :
    (U ⊠ K).IsLeftKanExtension (unitLeftExternal U K) :=
  let α₀ :
    K ⋙ tensorLeft (𝟙_ V) ≅ (prod.leftUnitorEquivalence D).inverse ⋙
      fromPUnit.{0} (𝟙_ V) ⊠ K := NatIso.ofComponents fun _ ↦ .refl _
  let Φ :
      (prod.leftUnitorEquivalence D).inverse ⋙
        (fromPUnit.{0} <| 𝟙_ C).prod (𝟭 D) ≅
      (Prod.sectR (𝟙_ C) D) :=
    NatIso.ofComponents fun _ ↦ .refl _
  isLeftKanExtension_iff_postcompose α₀.hom (Prod.sectR (𝟙_ C) D) Φ
    (extensionUnitLeft U (φ U) K) (unitLeftExternal U K) (by aesop_cat)|>.mp
      inferInstance

variable [DayConvolution U F]

instance isLeftKanExtensionUnitLeft :
    (U ⊛ F).IsLeftKanExtension (unitLeft U F) :=
  let ψ : (Prod.sectR (𝟙_ C) C) ⋙ (tensor C) ≅ tensorLeft (𝟙_ C) :=
    NatIso.ofComponents fun _ ↦ .refl _
  isLeftKanExtension_iff_postcompose (unitLeftExternal U F)
    (tensorLeft <| 𝟙_ C) ψ (DayConvolution.unit U F) _ (by aesop_cat)|>.mp
      inferInstance

variable {F} in
lemma hom_ext_unit_left {G : C ⥤ V} {α β : U ⊛ F ⟶ G}
    (h : ∀ (c : C),
      can ▷ (F.obj c) ≫ (DayConvolution.unit U F).app (𝟙_ C, c) ≫ α.app (𝟙_ C ⊗ c) =
      can ▷ (F.obj c) ≫ (DayConvolution.unit U F).app (𝟙_ C, c) ≫ β.app (𝟙_ C ⊗ c)) :
    α = β := by
  apply (U ⊛ F).hom_ext_of_isLeftKanExtension (unitLeft U F)
  ext t
  simpa using h t

end

section

omit [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
  (CostructuredArrow (fromPUnit.{0} (𝟙_ C)) d) (tensorRight v)]

/-- An extension of `F ⋙ tensorRight (𝟙_ V)` along `tensorRight (𝟙_ C)`,
which we will show is a left Kan extension. This is useful for working with
morphisms out of `F ⊛ U` without going through an external product.
Note that this extension is exactly the one that characterizes the right
unitors for Day convolutions in `rightUnitor_hom_unit_app`. -/
@[simps]
def unitRight (F : C ⥤ V) [DayConvolution F U] :
    F ⋙ tensorRight (𝟙_ V) ⟶ tensorRight (𝟙_ C) ⋙ (F ⊛ U) where
  app x := F.obj x ◁ can ≫ (DayConvolution.unit F U).app (x, 𝟙_ C)
  naturality {x y} f := by
    simp [← id_tensorHom, Category.assoc, ← tensorHom_id,
      ← tensor_comp_assoc, Category.comp_id, Category.id_comp,
      ← DayConvolution.unit_naturality, Functor.map_id]

/-- An extension of `K ⋙ tensorLeft (𝟙_ V)` (for any `K : _ ⥤ V`) along
`Prod.sectL D (𝟙_ C)`, which we will show is a left Kan extension.
This is useful for working with morphisms out of `K ⊠ U`. -/
@[simps]
def unitRightExternal {D : Type u₃} [Category D] (K : D ⥤ V) :
    K ⋙ tensorRight (𝟙_ V) ⟶ Prod.sectL D (𝟙_ C) ⋙ K ⊠ U where
  app y := _ ◁ can
  naturality {x y} f := by simp [whisker_exchange]

instance isLeftKanExtensionUnitRightExternal
    {D : Type u₃} [Category D] (K : D ⥤ V) :
    (K ⊠ U).IsLeftKanExtension (unitRightExternal U K) :=
  let α₀ :
    K ⋙ tensorRight (𝟙_ V) ≅ (prod.rightUnitorEquivalence D).inverse ⋙
      K ⊠ fromPUnit.{0} (𝟙_ V) := NatIso.ofComponents fun _ ↦ .refl _
  let Φ :
      (prod.rightUnitorEquivalence D).inverse ⋙
        (𝟭 D).prod (fromPUnit.{0} <| 𝟙_ C)  ≅
      (Prod.sectL D (𝟙_ C)) :=
    NatIso.ofComponents fun _ ↦ .refl _
  isLeftKanExtension_iff_postcompose α₀.hom (Prod.sectL D (𝟙_ C)) Φ
    (extensionUnitRight U (φ U) K) (unitRightExternal U K) (by aesop_cat)|>.mp
      inferInstance

variable [DayConvolution F U]

instance isLeftKanExtensionUnitRight :
    (F ⊛ U).IsLeftKanExtension (unitRight U F) :=
  let ψ : (Prod.sectL C (𝟙_ C)) ⋙ (tensor C) ≅ tensorRight (𝟙_ C) :=
    NatIso.ofComponents fun _ ↦ .refl _
  isLeftKanExtension_iff_postcompose (unitRightExternal U F)
    (tensorRight (𝟙_ C)) ψ (DayConvolution.unit F U) _ (by aesop_cat)|>.mp
      inferInstance

variable {F} in
lemma hom_ext_unit_right {G : C ⥤ V} {α β : F ⊛ U ⟶ G}
    (h : ∀ (c : C),
      F.obj c ◁ can ≫ (DayConvolution.unit F U).app (c, 𝟙_ C) ≫ α.app (c ⊗ 𝟙_ C) =
      F.obj c ◁ can ≫ (DayConvolution.unit F U).app (c, 𝟙_ C) ≫ β.app (c ⊗ 𝟙_ C)) :
    α = β := by
  apply (F ⊛ U).hom_ext_of_isLeftKanExtension (unitRight U F)
  ext t
  simpa using (h t)

end

end DayConvolutionUnit

section triangle

open DayConvolution
open DayConvolutionUnit
open ExternalProduct

variable [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
    (CostructuredArrow (tensor C) d) (tensorLeft v)]
  [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
    (CostructuredArrow (tensor C) d) (tensorRight v)]
  [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
    (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]
  [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
    (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
  [∀ (v : V) (d : C × C), Limits.PreservesColimitsOfShape
    (CostructuredArrow ((𝟭 C).prod <| Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]

lemma DayConvolution.triangle (F G U : C ⥤ V) [DayConvolutionUnit U]
    [DayConvolution F U] [DayConvolution U G]
    [DayConvolution F (U ⊛ G)] [DayConvolution (F ⊛ U) G] [DayConvolution F G] :
    (DayConvolution.associator F U G).hom ≫
      DayConvolution.map (𝟙 F) (DayConvolutionUnit.leftUnitor U G).hom =
    DayConvolution.map (DayConvolutionUnit.rightUnitor U F).hom (𝟙 G) := by
  apply Functor.hom_ext_of_isLeftKanExtension _ (DayConvolution.unit _ _) _
  apply Functor.hom_ext_of_isLeftKanExtension
    (α := extensionUnitLeft (F ⊛ U) (DayConvolution.unit F U) G)
  have : (F ⊠ U) ⊠ G|>.IsLeftKanExtension
      (α := extensionUnitLeft (F ⊠ U) (extensionUnitRight U (DayConvolutionUnit.φ U) F) G) :=
    isPointwiseLeftKanExtensionExtensionUnitLeft (F ⊠ U) _ G
      (isPointwiseLeftKanExtensionExtensionUnitRight U (DayConvolutionUnit.φ U) F <|
        DayConvolutionUnit.isPointwiseLeftKanExtensionCan (F := U))|>.isLeftKanExtension
  apply Functor.hom_ext_of_isLeftKanExtension
    (α := extensionUnitLeft (F ⊠ U) (extensionUnitRight U (DayConvolutionUnit.φ U) F) G)
  ext
  dsimp
  simp only [MonoidalCategory.whiskerRight_id, Category.id_comp, Iso.hom_inv_id, whisker_assoc,
    MonoidalCategory.whiskerLeft_id, Category.comp_id,
    DayConvolution.associator_hom_unit_unit_assoc, externalProductBifunctor_obj_obj, tensor_obj,
    NatTrans.naturality, unit_app_map_app_assoc, NatTrans.id_app, id_tensorHom,
    Category.assoc, Iso.inv_hom_id_assoc, unit_app_map_app, Functor.comp_obj,
    tensorHom_id, Iso.cancel_iso_hom_left]
  simp only [← MonoidalCategory.whiskerLeft_comp_assoc, leftUnitor_hom_unit_app,
    associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, rightUnitor_hom_unit_app]
  simp [← Functor.map_comp]

end triangle

end

end CategoryTheory.MonoidalCategory
