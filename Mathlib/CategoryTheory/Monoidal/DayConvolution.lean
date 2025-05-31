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
left Kan extension of `F ⊠ G` (see `CategoryTheory/Monoidal/ExternalProduct` for the definition)
along the tensor product of `C`. Such a functor is called a Day convolution of `F` and `G`, and
although we do not show it yet, this operation defines a monoidal structure on `C ⥤ V`.

We also define a typeclass `DayConvolutionUnit` on a functor `U : C ⥤ V` that bundle the data
required to make it a unit for the Day convolution monoidal structure: said data is that of
a map `𝟙_ V ⟶ U.obj (𝟙_ C)` that exhibits `U` as a pointwise left Kan extension of
`fromPUnit (𝟙_ V)` along `fromPUnit (𝟙_ C)`.

## References
- [nLab page: Day convolution](https://ncatlab.org/nlab/show/Day+convolution)

## TODOs (@robin-carlier)
- Define associators and unitors, prove the pentagon and triangle identities.
- Braided/symmetric case.
- Case where `V` is closed.
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
a functor `F ⊛ G : C ⥤ V`, along with a unit `F ⊠ G to tensor C ⋙ F ⊛ G`
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
  unitPointwiseKan (F G) :
    (Functor.LeftExtension.mk (convolution) unit).IsPointwiseLeftKanExtension

namespace DayConvolution

section

/-- A notation for the Day convolution of two functors. -/
scoped infixr:80 " ⊛ " => convolution

variable (F G : C ⥤ V)

instance leftKanExtension [DayConvolution F G] :
    (F ⊛ G).IsLeftKanExtension (unit F G) :=
  unitPointwiseKan F G|>.isLeftKanExtension

variable {F G}

/-- Two day convolution structures on the same functors gives an isomorphic functor. -/
def uniqueUpToIso (h : DayConvolution F G) (h' : DayConvolution F G) :
    h.convolution ≅ h'.convolution :=
  Functor.leftKanExtensionUnique h.convolution h.unit h'.convolution h'.unit

@[simp]
lemma uniqueUpToIso_hom_unit (h : DayConvolution F G) (h' : DayConvolution F G) :
    h.unit ≫ CategoryTheory.whiskerLeft (tensor C) (h.uniqueUpToIso h').hom = h'.unit := by
  simp [uniqueUpToIso]

@[simp]
lemma uniqueUpToIso_inv_unit (h : DayConvolution F G) (h' : DayConvolution F G) :
    h'.unit ≫ CategoryTheory.whiskerLeft (tensor C) (h.uniqueUpToIso h').inv = h.unit := by
  simp [uniqueUpToIso]

variable (F G) [DayConvolution F G]

section unit

variable {x x' y y' : C}

@[reassoc (attr := simp)]
lemma unit_naturality (f : x ⟶ x') (g : y ⟶ y') :
    (F.map f ⊗ G.map g) ≫ (unit F G).app (x', y') =
    (unit F G).app (x, y) ≫ (F ⊛ G).map (f ⊗ g) := by
  simpa [tensorHom_def] using (unit F G).naturality ((f, g) : (x, y) ⟶ (x', y'))

variable (y) in
@[reassoc (attr := simp)]
lemma unit_naturality_id_right (f : x ⟶ x') :
    F.map f ▷ G.obj y ≫ (unit F G).app (x', y) =
    (unit F G).app (x, y) ≫ (F ⊛ G).map (f ▷ y) := by
  simpa [tensorHom_def] using (unit F G).naturality ((f, 𝟙 _) : (x, y) ⟶ (x', y))

variable (x) in
@[reassoc (attr := simp)]
lemma unit_naturality_id_left (g : y ⟶ y') :
    F.obj x ◁ G.map g ≫ (unit F G).app (x, y') =
    (unit F G).app (x, y) ≫ (F ⊛ G).map (x ◁ g) := by
  simpa [tensorHom_def] using (unit F G).naturality ((𝟙 _, g) : (x, y) ⟶ (x, y'))

end unit

variable {F G}

section map

variable {F' G' : C ⥤ V} [DayConvolution F' G']

/-- The morphism between day convolutions (provided they exist) induced by a pair of morphisms. -/
def map (f : F ⟶ F') (g : G ⟶ G') : F ⊛ G ⟶ F' ⊛ G' :=
  Functor.descOfIsLeftKanExtension (F ⊛ G) (unit F G) (F' ⊛ G') <|
    (externalProductBifunctor C C V).map ((f, g) : (F, G) ⟶ (F', G')) ≫ unit F' G'

variable (f : F ⟶ F') (g : G ⟶ G') (x y : C)

@[reassoc (attr := simp)]
lemma map_unit_app :
  (unit F G).app (x, y) ≫ (map f g).app (x ⊗ y : C) =
    (f.app x ⊗ g.app y) ≫ (unit F' G').app (x, y) := by
  simpa [tensorHom_def] using
    (Functor.descOfIsLeftKanExtension_fac_app (F ⊛ G) (unit F G) (F' ⊛ G') <|
      (externalProductBifunctor C C V).map ((f, g) : (F, G) ⟶ (F', G')) ≫ unit F' G') (x, y)

end map

variable (F G)
/-- The universal property of left Kan extensions characterizes the functor
corepresented by `F ⊛ G`. -/
@[simps!]
def corepresentableIso : coyoneda.obj (.op <| F ⊛ G) ≅
    (whiskeringLeft _ _ _).obj (tensor C) ⋙ coyoneda.obj (.op <| F ⊠ G) :=
  NatIso.ofComponents
    (fun H ↦ Equiv.toIso <| Functor.homEquivOfIsLeftKanExtension _ (unit F G) _)

/-- The universal property of left Kan extensions characterizes the functor
corepresented by `F ⊛ G`. -/
def corepresentable :
    (whiskeringLeft _ _ _).obj (tensor C) ⋙ coyoneda.obj (.op <| F ⊠ G)|>.CorepresentableBy
      (F ⊛ G) :=
  Functor.corepresentableByEquiv.symm <| corepresentableIso F G

/-- Use the fact that `(F ⊛ G).obj c` is a colimit to characterize morphisms out of it at a
point. -/
theorem convolution_hom_ext_at (c : C) {v : V} {f g : (F ⊛ G).obj c ⟶ v}
    (h : ∀ {x y : C} (u : x ⊗ y ⟶ c),
      (unit F G).app (x, y) ≫ (F ⊛ G).map u ≫ f = (unit F G).app (x, y) ≫ (F ⊛ G).map u ≫ g) :
    f = g :=
  (unitPointwiseKan F G c).hom_ext (by simpa using h ·.hom)


section associator

variable (H : C ⥤ V)
    [DayConvolution G H]
    [DayConvolution F (G ⊛ H)]
    [DayConvolution (F ⊛ G) H]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorRight v)]

open MonoidalCategory.ExternalProduct

instance : (F ⊠ G ⊛ H).IsLeftKanExtension <|
    extensionUnitRight (G ⊛ H) (unit G H) F :=
  (pointwiseLeftKanExtensionRight _ _ _ <| unitPointwiseKan G H).isLeftKanExtension

instance : ((F ⊛ G) ⊠ H).IsLeftKanExtension <|
    extensionUnitLeft (F ⊛ G) (unit F G) H :=
  (pointwiseLeftKanExtensionLeft _ _ _ <| unitPointwiseKan F G).isLeftKanExtension

/-- An auxiliary equivalence used to build the associators,
characterizing morphism out of `F ⊛ G ⊛ H` via the universal property of Kan extensions.
-/
@[simps!]
noncomputable def corepresentableIso₂ :
    coyoneda.obj (.op <| F ⊛ G ⊛ H) ≅
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((𝟭 C).prod (tensor C)) ⋙
      coyoneda.obj (.op <| F ⊠ G ⊠ H) :=
  calc
    _ ≅ (whiskeringLeft _ _ _).obj (tensor C) ⋙ coyoneda.obj (.op <| F ⊠ (G ⊛ H)) :=
      corepresentableIso F (G ⊛ H)
    _ ≅ _ := NatIso.ofComponents
      (fun _ ↦ Equiv.toIso <| Functor.homEquivOfIsLeftKanExtension _
        (extensionUnitRight (G ⊛ H) (unit G H) F) _)

/-- An auxiliary equivalence used to build the associators,
characterizing morphism out of `F ⊛ G ⊛ H` via the universal property of Kan extensions.
-/
@[simps!]
noncomputable def corepresentableIso₂' :
    coyoneda.obj (.op <| (F ⊛ G) ⊛ H) ≅
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((tensor C).prod (𝟭 C)) ⋙
      coyoneda.obj (.op <| (F ⊠ G) ⊠ H) :=
  calc
    _ ≅ (whiskeringLeft _ _ _).obj (tensor C) ⋙ coyoneda.obj (.op <| (F ⊛ G) ⊠ H) :=
      corepresentableIso (F ⊛ G) H
    _ ≅ _ := NatIso.ofComponents
      (fun _ ↦ Equiv.toIso <| Functor.homEquivOfIsLeftKanExtension _
        (extensionUnitLeft (F ⊛ G) (unit F G) H) _)

/-- The `CorepresentableBy` structure on `F ⊠ G ⊠ H ⟶ (𝟭 C).prod (tensor C) ⋙ tensor C ⋙ -`
derived from `tensorCorepresentableIso₂`. -/
def corepresentable₂ :
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((𝟭 C).prod (tensor C)) ⋙
      coyoneda.obj (.op <| F ⊠ G ⊠ H)|>.CorepresentableBy (F ⊛ G ⊛ H) :=
  Functor.corepresentableByEquiv.symm (corepresentableIso₂ F G H)

/-- The `CorepresentableBy` structure on `(F ⊠ G) ⊠ H ⟶ (tensor C).prod (𝟭 C) ⋙ tensor C ⋙ -`
derived from `tensorCorepresentableIso₂`. -/
def corepresentable₂' :
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((tensor C).prod (𝟭 C)) ⋙
      coyoneda.obj (.op <| (F ⊠ G) ⊠ H)|>.CorepresentableBy ((F ⊛ G) ⊛ H) :=
  Functor.corepresentableByEquiv.symm (corepresentableIso₂' F G H)

/-- The isomorphism of functors between
`((F ⊠ G) ⊠ H ⟶ (tensor C).prod (𝟭 C) ⋙ tensor C ⋙ -)` and
`(F ⊠ G ⊠ H ⟶ (𝟭 C).prod (tensor C) ⋙ tensor C ⋙ -)` that copresents the associator isomorphism
for Day convolution. -/
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

/-- The asociator morphism for Day convolution -/
def associator : (F ⊛ G) ⊛ H ≅ F ⊛ G ⊛ H :=
  corepresentable₂' F G H|>.ofIso (associatorCorepresentingIso F G H)|>.uniqueUpToIso <|
    corepresentable₂ F G H

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
  letI := congrArg (fun t ↦ t.app ((x, y), z)) <|
      (corepresentableIso₂' F G H).app (F ⊛ (G ⊛ H))|>.toEquiv.rightInverse_symm <|
        (corepresentable₂ F G H|>.ofIso
          (associatorCorepresentingIso F G H).symm|>.homEquiv (𝟙 _))
  dsimp [associator, Coyoneda.fullyFaithful, corepresentable₂,
    corepresentable₂', Functor.CorepresentableBy.ofIso, corepresentable₂,
    Functor.corepresentableByEquiv, associatorCorepresentingIso] at this ⊢
  simp only [Category.assoc, corepresentableIso₂'_hom_app_app] at this
  simp only [Category.assoc, this]
  simp [Functor.FullyFaithful.homEquiv, Equivalence.fullyFaithfulFunctor, prod.associativity]

/-- Characterizing associator_inv with respect to the unit transformations -/
@[reassoc (attr := simp)]
lemma associator_inv_unit_unit (x y z : C) :
    F.obj x ◁ (unit G H).app (y, z) ≫
      (unit F (G ⊛ H)).app (x, y ⊗ z) ≫
      (associator F G H).inv.app (x ⊗ y ⊗ z) =
    (α_ (F.obj x) (G.obj y) (H.obj z)).inv ≫ (unit F G).app (x, y) ▷ H.obj z ≫
      (unit (F ⊛ G) H).app (x ⊗ y, z) ≫
      ((F ⊛ G) ⊛ H).map (α_ x y z).hom := by
  letI := congrArg (fun t ↦ t.app (x, y, z)) <|
      (corepresentableIso₂ F G H).app ((F ⊛ G) ⊛ H)|>.toEquiv.rightInverse_symm <|
        (corepresentable₂' F G H|>.ofIso
          (associatorCorepresentingIso F G H)|>.homEquiv (𝟙 _))
  dsimp [associator, Coyoneda.fullyFaithful, corepresentable₂,
    corepresentable₂', Functor.CorepresentableBy.ofIso, corepresentable₂,
    Functor.corepresentableByEquiv, associatorCorepresentingIso] at this ⊢
  simp only [Category.assoc, corepresentableIso₂_hom_app_app] at this
  simp only [Category.assoc, this]
  simp [Functor.FullyFaithful.homEquiv, Equivalence.fullyFaithfulFunctor, prod.associativity]

variable {F G H} in
theorem associator_naturality {F' G' H' : C ⥤ V}
  [DayConvolution F' G'] [DayConvolution G' H']
  [DayConvolution F' (G' ⊛ H')] [DayConvolution (F' ⊛ G') H']
  (f : F ⟶ F') (g : G ⟶ G') (h : H ⟶ H') :
    map (map f g) h ≫
      (associator F' G' H').hom =
    (associator F G H).hom ≫ map f (map g h) := by
  apply (corepresentableIso₂' F G H).app (F' ⊛ G' ⊛ H')|>.toEquiv.injective
  dsimp
  ext
  simp only [externalProductBifunctor_obj_obj, whiskeringLeft_obj_obj, Functor.comp_obj,
    Functor.prod_obj, tensor_obj, Functor.id_obj, corepresentableIso₂'_hom_app_app,
    NatTrans.comp_app, map_unit_app_assoc]
  rw [associator_hom_unit_unit_assoc]
  simp only [tensorHom_def, Category.assoc, externalProductBifunctor_obj_obj, tensor_obj,
    NatTrans.naturality, map_unit_app_assoc]
  rw  [← comp_whiskerRight_assoc, map_unit_app]
  simp only [Functor.comp_obj, tensor_obj, comp_whiskerRight, Category.assoc]
  rw [← whisker_exchange_assoc, associator_hom_unit_unit, whisker_exchange_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, map_unit_app]
  simp [tensorHom_def]

section pentagon

variable [∀ (v : V) (d : C × C),
    Limits.PreservesColimitsOfShape (CostructuredArrow ((tensor C).prod (𝟭 C)) d) (tensorRight v)]

lemma pentagon (H K : C ⥤ V)
    [DayConvolution G H] [DayConvolution (F ⊛ G) H] [DayConvolution F (G ⊛ H)]
    [DayConvolution H K] [DayConvolution G (H ⊛ K)] [DayConvolution (G ⊛ H) K]
    [DayConvolution ((F ⊛ G) ⊛ H) K] [DayConvolution (F ⊛ G) (H ⊛ K)]
    [DayConvolution (F ⊛ G ⊛ H) K] [DayConvolution F  (G ⊛ H ⊛ K)]
    [DayConvolution F ((G ⊛ H) ⊛ K)] :
    map (associator F G H).hom (𝟙 K) ≫
        (associator F (G ⊛ H) K).hom ≫ map (𝟙 F) (associator G H K).hom =
      (associator (F ⊛ G) H K).hom ≫ (associator F G (H ⊛ K)).hom := by
  -- We repeatedly apply the fact that the functors are left Kan extended
  apply Functor.hom_ext_of_isLeftKanExtension (α := unit ((F ⊛ G) ⊛ H) K)
  apply Functor.hom_ext_of_isLeftKanExtension
    (α := extensionUnitLeft ((F ⊛ G) ⊛ H) (unit (F ⊛ G) H) K)
  letI : (((F ⊛ G) ⊠ H) ⊠ K).IsLeftKanExtension
    (α := extensionUnitLeft ((F ⊛ G) ⊠ H)
      (extensionUnitLeft _ (unit F G) H) K) :=
    pointwiseLeftKanExtensionLeft _ _ _
      (pointwiseLeftKanExtensionLeft _ _ _ (unitPointwiseKan F G))|>.isLeftKanExtension
  apply Functor.hom_ext_of_isLeftKanExtension (α := extensionUnitLeft ((F ⊛ G) ⊠ H)
      (extensionUnitLeft _ (unit F G) H) K)
  -- And then we compute...
  ext ⟨⟨⟨i, j⟩, k⟩, l⟩
  have aux :
      ((unit F G).app (i, j) ⊗ (unit H K).app (k, l)) ≫
        (unit (F ⊛ G) (H ⊛ K)).app ((i ⊗ j), (k ⊗ l)) =
      (α_ (F.obj i) (G.obj j) (H.obj k ⊗ K.obj l)).hom ≫
        F.obj i ◁ (G.obj j ◁ (unit H K).app (k, l)) ≫ F.obj i ◁ (unit G (H ⊛ K)).app (j, (k ⊗ l)) ≫
        (unit F (G ⊛ H ⊛ K)).app (i, (j ⊗ k ⊗ l)) ≫ (F ⊛ G ⊛ H ⊛ K).map (α_ i j (k ⊗ l)).inv ≫
        (associator F G (H ⊛ K)).inv.app ((i ⊗ j) ⊗ k ⊗ l) := by
    conv_rhs => simp only [Functor.comp_obj, tensor_obj, NatTrans.naturality,
      associator_inv_unit_unit_assoc, externalProductBifunctor_obj_obj, Iso.map_hom_inv_id,
      Category.comp_id]
    simp only [tensor_whiskerLeft_symm, Category.assoc, Iso.hom_inv_id_assoc,
    ← tensorHom_def'_assoc]
  dsimp
  simp only [MonoidalCategory.whiskerLeft_id, Category.comp_id, map_unit_app_assoc,
    externalProductBifunctor_obj_obj, NatTrans.id_app, tensorHom_id, associator_hom_unit_unit_assoc,
    tensor_obj, NatTrans.naturality]
  conv_rhs =>
    simp only [whiskerRight_tensor_symm_assoc, Iso.inv_hom_id_assoc, ← tensorHom_def_assoc]
    rw [reassoc_of% aux]
  simp only [Iso.inv_hom_id_app_assoc, ← comp_whiskerRight_assoc, associator_hom_unit_unit F G H]
  simp only [Functor.comp_obj, tensor_obj, comp_whiskerRight, whisker_assoc, Category.assoc,
    reassoc_of% unit_naturality_id_right (F ⊛ G ⊛ H) K l (α_ i j k).inv, NatTrans.naturality_assoc,
    NatTrans.naturality, associator_hom_unit_unit_assoc, externalProductBifunctor_obj_obj,
    tensor_obj, NatTrans.naturality_assoc, map_unit_app_assoc, NatTrans.id_app,
    id_tensorHom, Iso.inv_hom_id_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    associator_hom_unit_unit]
  simp [← Functor.map_comp, reassoc_of% unit_naturality_id_left F (G ⊛ H ⊛ K) i (α_ j k l).inv,
    pentagon_inv, pentagon_assoc]

end pentagon

end associator

end

end DayConvolution

/-- A dayConvolutionUnit structure on a functor `C ⥤ V` is the data of a pointwise
left Kan extension of `fromPUnit (𝟙_ V)` along `fromPUnit (𝟙_ C)`. Again, this is
made a class to ease proofs when constructing `DayConvolutionMonoidalCategory` structures, but one
should avoid registering it globally. -/
class DayConvolutionUnit (F : C ⥤ V) where
  /-- A "canonical" structure map `𝟙_ V ⟶ F.obj (𝟙_ C)` that defines a natural transformation
  `fromPUnit (𝟙_ V) ⟶ fromPUnit (𝟙_ C) ⋙ F`. -/
  can : 𝟙_ V ⟶ F.obj (𝟙_ C)
  /-- The canonical map `𝟙_ V ⟶ F.obj (𝟙_ C)` exhibits `F` as a pointwise left kan extension
  of `fromPUnit.{0} 𝟙_ V` along `fromPUnit.{0} 𝟙_ C`. -/
  canPointwiseLeftKanExtension : Functor.LeftExtension.mk F
    ({app _ := can} : Functor.fromPUnit.{0} (𝟙_ V) ⟶
      Functor.fromPUnit.{0} (𝟙_ C) ⋙ F)|>.IsPointwiseLeftKanExtension

namespace DayConvolutionUnit

variable (U : C ⥤ V) [DayConvolutionUnit U]
open scoped DayConvolution
open ExternalProduct

/-- A shorthand for the natural transformation of functors out of PUnit defined by
the canonical morphism `𝟙_ V ⟶ U.obj (𝟙_ C)` when `U` is a unit for Day convolution. -/
abbrev φ : Functor.fromPUnit.{0} (𝟙_ V) ⟶ Functor.fromPUnit.{0} (𝟙_ C) ⋙ U where
  app _ := can

/-- Since a convolution unit is a pointwise left Kan extension, maps out of it at
any object are uniquely characterized. -/
lemma hom_ext {c : C} {v : V} {g h : U.obj c ⟶ v}
    (e : ∀ f : 𝟙_ C ⟶ c, can ≫ U.map f ≫ g = can ≫ U.map f ≫ h) :
    g = h := by
  apply (canPointwiseLeftKanExtension c).hom_ext
  intro j
  simpa using e j.hom

variable (F : C ⥤ V)
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit (𝟙_ C)) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit (𝟙_ C)) d) (tensorRight v)]
    -- [∀ v : V, Limits.PreservesColimitsOfSize.{0, v₁} (tensorRight v)]

instance : (F ⊠ U).IsLeftKanExtension <| extensionUnitRight U (φ U) F :=
  pointwiseLeftKanExtensionRight U (φ U) F canPointwiseLeftKanExtension|>.isLeftKanExtension

instance : (U ⊠ F).IsLeftKanExtension <| extensionUnitLeft U (φ U) F :=
  pointwiseLeftKanExtensionLeft U (φ U) F canPointwiseLeftKanExtension|>.isLeftKanExtension

/-- An isomorphism that computes the functor corepresented by `U ⊛ F` using the
fact that `U ⊠ F` is left Kan extended from `(fromPUnit 𝟙_ V) ⊠ F`. -/
@[simps!]
def corepresentableIsoLeft [DayConvolution U F] :
    coyoneda.obj (.op <| U ⊛ F) ≅
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((Functor.fromPUnit.{0} (𝟙_ C)).prod (𝟭 C)) ⋙
      coyoneda.obj (.op <| Functor.fromPUnit.{0} (𝟙_ V) ⊠ F) :=
  NatIso.ofComponents
    (fun H ↦ Equiv.toIso <|
      calc
        _ ≃ (U ⊠ F ⟶ (tensor C) ⋙ H) :=
          Functor.homEquivOfIsLeftKanExtension _ (DayConvolution.unit U F) _
        _ ≃ _ :=
          Functor.homEquivOfIsLeftKanExtension _ (extensionUnitLeft U (φ U) F) (tensor C ⋙ H))

/-- The `CorepresentableBy` structure attached to the isomorphism
`convolutionUnitCorepresentableIsoLeft`. -/
def corepresentableLeft [DayConvolution U F] :
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((Functor.fromPUnit.{0} (𝟙_ C)).prod (𝟭 C)) ⋙
      coyoneda.obj (.op <| Functor.fromPUnit.{0} (𝟙_ V) ⊠ F)|>.CorepresentableBy (U ⊛ F) :=
  Functor.corepresentableByEquiv.symm <| corepresentableIsoLeft U F

/-- An isomorphism that computes the functor corepresented by `U ⊛ F` using the
fact that `F ⊠ U` is left Kan extended from `F ⊠ (fromPUnit 𝟙_ V)`. -/
@[simps!]
def corepresentableIsoRight [DayConvolution F U] :
    coyoneda.obj (.op <| F ⊛ U) ≅
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((𝟭 C).prod (Functor.fromPUnit.{0} (𝟙_ C))) ⋙
      coyoneda.obj (.op <| F ⊠ Functor.fromPUnit.{0} (𝟙_ V)) :=
  NatIso.ofComponents
    (fun H ↦ Equiv.toIso <|
      calc
        _ ≃ (F ⊠ U ⟶ (tensor C) ⋙ H) :=
          Functor.homEquivOfIsLeftKanExtension _ (DayConvolution.unit F U) _
        _ ≃ _ :=
          Functor.homEquivOfIsLeftKanExtension _ (extensionUnitRight U (φ U) F) (tensor C ⋙ H))

/-- The `CorepresentableBy` structure attached to the isomorphism
`convolutionUnitCorepresentableIsoRight`. -/
def corepresentableRight [DayConvolution F U] :
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((𝟭 C).prod (Functor.fromPUnit.{0} (𝟙_ C))) ⋙
      coyoneda.obj (.op <| F ⊠ Functor.fromPUnit.{0} (𝟙_ V))|>.CorepresentableBy (F ⊛ U) :=
  Functor.corepresentableByEquiv.symm <| corepresentableIsoRight U F

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
              ((𝟭 C).prod (Functor.fromPUnit.{u₁} (𝟙_ C))) ⋙ tensor C) ⋙
          coyoneda.obj (.op <|
            (prod.rightUnitorEquivalence C).inverse ⋙ F ⊠ Functor.fromPUnit.{0} (𝟙_ V)) :=
      .refl _
    _ ≅ (whiskeringLeft _ _ _).obj (𝟭 _) ⋙ coyoneda.obj (.op <|
          (prod.rightUnitorEquivalence C).inverse ⋙ F ⊠ Functor.fromPUnit.{0} (𝟙_ V)) :=
      isoWhiskerRight ((whiskeringLeft _ _ _).mapIso <| NatIso.ofComponents fun _ ↦ ρ_ _) _
    _ ≅ _ := coyoneda.mapIso <| Iso.op <| NatIso.ofComponents fun _ ↦ (ρ_ _).symm

/-- The left unitor isomorphism for Day convolution. -/
def leftUnitor [DayConvolution U F] : U ⊛ F ≅ F :=
  corepresentableLeft U F|>.ofIso (leftUnitorCorepresentingIso F)|>.uniqueUpToIso
    <| Functor.corepresentableByEquiv.symm (.refl _)

/-- The right unitor isomorphism for Day convolution. -/
def rightUnitor [DayConvolution F U] : F ⊛ U ≅ F :=
  corepresentableRight U F|>.ofIso (rightUnitorCorepresentingIso F)|>.uniqueUpToIso
    <| Functor.corepresentableByEquiv.symm (.refl _)

section

omit [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
  (CostructuredArrow (Functor.fromPUnit (𝟙_ C)) d) (tensorLeft v)]
variable [DayConvolution U F]

/-- Characterizing the forward direction of `leftUnitor` via the universal maps. -/
@[reassoc (attr := simp)]
lemma leftUnitor_hom_unit_app (y : C) :
    can ▷ F.obj y ≫ (DayConvolution.unit U F).app (𝟙_ C, y) ≫
      (leftUnitor U F).hom.app (𝟙_ C ⊗ y) =
    (λ_ (F.obj y)).hom ≫ F.map ((λ_ y).inv) := by
  letI := congrArg (fun t ↦ t.app (.mk PUnit.unit, y)) <|
      (corepresentableIsoLeft U F).app F|>.toEquiv.rightInverse_symm <|
        ((leftUnitorCorepresentingIso F).symm.hom.app (F)) (𝟙 _)
  dsimp [leftUnitor, Coyoneda.fullyFaithful, corepresentableLeft, corepresentableIsoLeft,
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
  dsimp [leftUnitor, Coyoneda.fullyFaithful, corepresentableLeft, corepresentableIsoLeft,
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
  ext ⟨x₁, x₂⟩
  simp [← whisker_exchange_assoc]

end

section

omit [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
  (CostructuredArrow (Functor.fromPUnit (𝟙_ C)) d) (tensorRight v)]
variable [DayConvolution F U]

/-- Characterizing the forward direction of `leftUnitor` via the universal maps. -/
@[reassoc (attr := simp)]
lemma rightUnitor_hom_unit_app (x : C) :
    F.obj x ◁ can ≫ (DayConvolution.unit F U).app (x, 𝟙_ C) ≫
      (rightUnitor U F).hom.app (x ⊗ 𝟙_ C) =
    (ρ_ _).hom ≫ F.map ((ρ_ x).inv) := by
  letI := congrArg (fun t ↦ t.app (x, .mk PUnit.unit)) <|
      (corepresentableIsoRight U F).app F|>.toEquiv.rightInverse_symm <|
        ((rightUnitorCorepresentingIso F).symm.hom.app (F)) (𝟙 _)
  dsimp [rightUnitor, Coyoneda.fullyFaithful, corepresentableRight, corepresentableIsoRight,
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
  dsimp [rightUnitor, Coyoneda.fullyFaithful, corepresentableRight, corepresentableIsoRight,
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
  ext ⟨x₁, x₂⟩
  simp [whisker_exchange_assoc]

end

end DayConvolutionUnit

section triangle

open scoped DayConvolution
open DayConvolutionUnit
open ExternalProduct

variable [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
    (CostructuredArrow (tensor C) d) (tensorLeft v)]
  [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
    (CostructuredArrow (tensor C) d) (tensorRight v)]
  [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
    (CostructuredArrow (Functor.fromPUnit <| 𝟙_ C) d) (tensorLeft v)]
  [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
    (CostructuredArrow (Functor.fromPUnit <| 𝟙_ C) d) (tensorRight v)]
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
  letI : (F ⊠ U) ⊠ G|>.IsLeftKanExtension
      (α := extensionUnitLeft (F ⊠ U) (extensionUnitRight U (DayConvolutionUnit.φ U) F) G) :=
    pointwiseLeftKanExtensionLeft (F ⊠ U) _ G
      (pointwiseLeftKanExtensionRight U (DayConvolutionUnit.φ U) F <|
        DayConvolutionUnit.canPointwiseLeftKanExtension (F := U))|>.isLeftKanExtension
  apply Functor.hom_ext_of_isLeftKanExtension
    (α := extensionUnitLeft (F ⊠ U) (extensionUnitRight U (DayConvolutionUnit.φ U) F) G)
  ext ⟨⟨x, _⟩, y⟩
  dsimp
  simp only [MonoidalCategory.whiskerRight_id, Category.id_comp, Iso.hom_inv_id, whisker_assoc,
    MonoidalCategory.whiskerLeft_id, Category.comp_id,
    DayConvolution.associator_hom_unit_unit_assoc, externalProductBifunctor_obj_obj, tensor_obj,
    NatTrans.naturality, DayConvolution.map_unit_app_assoc, NatTrans.id_app, id_tensorHom,
    Category.assoc, Iso.inv_hom_id_assoc, DayConvolution.map_unit_app, Functor.comp_obj,
    tensorHom_id, Iso.cancel_iso_hom_left]
  simp only [← MonoidalCategory.whiskerLeft_comp_assoc, leftUnitor_hom_unit_app,
    associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, rightUnitor_hom_unit_app]
  simp [← Functor.map_comp]

end triangle

end

end CategoryTheory.MonoidalCategory
