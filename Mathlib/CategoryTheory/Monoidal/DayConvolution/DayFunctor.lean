/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Monoidal.DayConvolution
import Mathlib.CategoryTheory.Monoidal.DayConvolution.Closed

/-!
# Day functors

In this file, given a monoidal category `C` and a monoidal category `V`,
we define a basic type synonym `DayFunctor C V` (denoted `C ⊛⥤ D`)
for the category `C ⥤ V` and endow it with the monoidal structure coming
from Day convolution. Such a setup is necessary as by default,
the `MonoidalCategory` instance on `C ⥤ V` is the "pointwise" one,
where the tensor product of `F` and `G` is the functor `x ↦ F.obj x ⊗ G.obj x`.

## TODOs
- Given a `LawfulDayConvolutionMonoidalCategoryStruct C V D`, show that
ι induce a monoidal functor `D ⥤ (C ⊛⥤ V)`.
- Specialize to the case `V := Type _`, and prove a universal property stating
that for every monoidal category `W` with suitable colimits,
colimit-preserving monoidal functors `(Cᵒᵖ ⊛⥤ Type u) ⥤ W` are equivalent to
to monoidal functors `C ⥤ W`. Show that the Yoneda embedding is monoidal.
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.MonoidalCategory
open scoped ExternalProduct

noncomputable section

/-- `DayFunctor C V` is a type synonym for `C ⥤ V`, implemented as a one-field
structure. -/
structure DayFunctor
    (C : Type u₁) [Category.{v₁} C] (V : Type u₂) [Category.{v₂} V]
    [MonoidalCategory C] [MonoidalCategory V] where
  /-- the underlying functor. -/
  functor : C ⥤ V

namespace DayFunctor

/-- Notation for `DayFunctor`. -/
scoped infixr:26 " ⊛⥤ " => DayFunctor

variable {C : Type u₁} [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V]
    [MonoidalCategory C] [MonoidalCategory V]

lemma mk_functor (F : C ⥤ V) : (mk F).functor = F := rfl

@[simp]
lemma functor_mk (F : C ⊛⥤ V) : mk (F.functor) = F := rfl

/-- Morphisms of Day functors are natural transformations of the underlying
functors. -/
structure Hom (F G : C ⊛⥤ V) where
  /-- the underlying natural transformation -/
  natTrans : F.functor ⟶ G.functor

@[simps id_natTrans comp_natTrans]
instance : Category (C ⊛⥤ V) where
  Hom := Hom
  id x := .mk <| 𝟙 x.functor
  comp α β := .mk <| α.natTrans ≫ β.natTrans

@[ext]
lemma hom_ext {F G : C ⊛⥤ V} {α β : F ⟶ G} (h : α.natTrans = β.natTrans) :
    α = β := by
  cases α
  cases β
  grind

variable (C V) in
/-- The tautological equivalence of categories between `C ⥤ V` and `C ⊛⥤ V`. -/
@[simps! functor_obj functor_map inverse_obj_functor inverse_map_natTrans
  unitIso_hom_app unitIso_inv_app counitIso_hom_app counitIso_inv_app]
def equiv : (C ⊛⥤ V) ≌ (C ⥤ V) where
  functor :=
    { obj F := F.functor
      map α := α.natTrans }
  inverse :=
    { obj F := .mk F
      map α := .mk α }
  unitIso := .refl _
  counitIso := .refl _

variable
    [hasDayConvolution : ∀ (F G : C ⥤ V),
      (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)]
    [hasDayConvolutionUnit :
      (Functor.fromPUnit.{0} <| 𝟙_ C).HasPointwiseLeftKanExtension
        (Functor.fromPUnit.{0} <| 𝟙_ V)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorRight v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C),
      Limits.PreservesColimitsOfShape
        (CostructuredArrow ((𝟭 C).prod <| Functor.fromPUnit.{0} <| 𝟙_ C) d)
        (tensorRight v)]
    [∀ (v : V) (d : C × C),
      Limits.PreservesColimitsOfShape
        (CostructuredArrow ((tensor C).prod (𝟭 C)) d) (tensorRight v)]

instance : MonoidalCategory (C ⊛⥤ V) :=
  monoidalOfHasDayConvolutions
    (equiv C V).functor
    (equiv C V).fullyFaithfulFunctor
    (fun _ _ => ⟨_, ⟨equiv C V|>.counitIso.app _⟩⟩)
    (⟨_, ⟨equiv C V|>.counitIso.app _⟩⟩)

@[simps! ι_obj ι_map]
instance : LawfulDayConvolutionMonoidalCategoryStruct C V (C ⊛⥤ V) :=
  lawfulDayConvolutionMonoidalCategoryStructOfHasDayConvolutions
    (equiv C V).functor
    (equiv C V).fullyFaithfulFunctor
    (fun _ _ => ⟨_, ⟨equiv C V|>.counitIso.app _⟩⟩)
    (⟨_, ⟨equiv C V|>.counitIso.app _⟩⟩)

open LawfulDayConvolutionMonoidalCategoryStruct in
instance : ι C V (C ⊛⥤ V)|>.Full := inferInstanceAs (equiv C V).functor.Full

/-- The functor underlying `𝟙_ C ⊛⥤ V` is a DayConvolutionUnit.
We’re not making this a global instance given that `DayConvolution` and
`DayConvolutionUnit` are data-carrying classes that we might prefer to
not register globally. This is nonetheless useful as a local instance in
some cases. -/
def unitFunctorDayConvoltionUnit : DayConvolutionUnit (𝟙_ (C ⊛⥤ V)).functor :=
  LawfulDayConvolutionMonoidalCategoryStruct.convolutionUnit _ _ (C ⊛⥤ V)

/-- There is always a day convolution of `F.functor` and `G.functor`.
We’re not making this a global instance given that `DayConvolution` and
`DayConvolutionUnit` are data-carrying classes that we might prefer to
not register globally. This is nonetheless useful as a local instance in
some cases. -/
def dayConvolutionFunctorFunctor (F G : C ⊛⥤ V) :
    DayConvolution F.functor G.functor :=
  LawfulDayConvolutionMonoidalCategoryStruct.convolution _ _ _ F G

/-- The unit transformation exhibiting `(F ⊗ G).functor` as a left Kan extension of
`F.functor ⊠ G.functor` along `tensor C`. -/
def η (F G : C ⊛⥤ V) :
    F.functor ⊠ G.functor ⟶ (tensor C) ⋙ (F ⊗ G).functor :=
  LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit
    C V F G

open LawfulDayConvolutionMonoidalCategoryStruct in
instance (F G : C ⊛⥤ V) : (F ⊗ G).functor.IsLeftKanExtension (η F G) :=
  (isPointwiseLeftKanExtensionConvolutionExtensionUnit F G).isLeftKanExtension

open LawfulDayConvolutionMonoidalCategoryStruct in
theorem tensor_hom_ext {F G H : C ⊛⥤ V} {α β : F ⊗ G ⟶ H}
    (h : ∀ (x y : C),
      (η F G).app (x, y) ≫ α.natTrans.app (x ⊗ y) =
      (η F G).app (x, y) ≫ β.natTrans.app (x ⊗ y)) :
    α = β := by
  ext : 1
  apply Functor.homEquivOfIsLeftKanExtension
    (F ⊗ G).functor (η F G) _|>.injective
  ext ⟨x, y⟩
  exact h x y

/-- A natural transformation `F.functor ⊠ G.functor ⟶ (tensor C) ⋙ H.functor`
defines a morphism `F ⨂ G ⟶ H`. -/
def tensorDesc {F G H : C ⊛⥤ V}
    (α : F.functor ⊠ G.functor ⟶ (tensor C) ⋙ H.functor) :
    F ⊗ G ⟶ H :=
  .mk <| (F ⊗ G).functor.descOfIsLeftKanExtension (η F G) H.functor α

lemma η_comp_tensorDec {F G H : C ⊛⥤ V}
    (α : F.functor ⊠ G.functor ⟶ (tensor C) ⋙ H.functor) :
   (η F G) ≫ Functor.whiskerLeft _ (tensorDesc α).natTrans = α :=
  Functor.descOfIsLeftKanExtension_fac _ _ _ _

@[reassoc (attr := simp)]
lemma η_comp_tensorDesc_app {F G H : C ⊛⥤ V}
    (α : F.functor ⊠ G.functor ⟶ (tensor C) ⋙ H.functor) (x y : C) :
   (η F G).app (x , y) ≫ (tensorDesc α).natTrans.app (x ⊗ y) = α.app (x, y) :=
  Functor.descOfIsLeftKanExtension_fac_app _ _ _ _ _

open LawfulDayConvolutionMonoidalCategoryStruct
/-- An abstract isomorphism between `(F ⊗ G).functor` and the generic pointwise
left Kan extension of `F.functor ⊠ G.functor` along the -/
def isoPointwiseLeftKanExtension (F G : C ⊛⥤ V) :
    (F ⊗ G).functor ≅
    (tensor C).pointwiseLeftKanExtension (F.functor ⊠ G.functor) :=
  Functor.leftKanExtensionUnique
    (F ⊗ G).functor (η F G) _
    ((tensor C).pointwiseLeftKanExtensionUnit (F.functor ⊠ G.functor))

@[simp]
lemma η_comp_isoPointwiseLeftKanExtension_hom (F G : C ⊛⥤ V) (x y : C) :
    (η F G).app (x, y) ≫ (isoPointwiseLeftKanExtension F G).hom.app (x ⊗ y) =
    Limits.colimit.ι
      ((CostructuredArrow.proj (tensor C) (x ⊗ y)) ⋙ F.functor ⊠ G.functor)
        (.mk (Y := (x, y)) <| 𝟙 (x ⊗ y)) := by
  simpa [η, isoPointwiseLeftKanExtension] using
    Functor.descOfIsLeftKanExtension_fac_app
      (F ⊗ G).functor (η F G) _
      ((tensor C).pointwiseLeftKanExtensionUnit (F.functor ⊠ G.functor)) (x, y)

@[simp]
lemma ι_comp_isoPointwiseLeftKanExtension_inv (F G : C ⊛⥤ V) (x y : C) :
    Limits.colimit.ι
      ((CostructuredArrow.proj (tensor C) (x ⊗ y)) ⋙ F.functor ⊠ G.functor)
        (.mk (Y := (x, y)) <| 𝟙 (x ⊗ y)) ≫
      (isoPointwiseLeftKanExtension F G).inv.app (x ⊗ y) =
    (η F G).app (x, y) := by
  simp [η, isoPointwiseLeftKanExtension]

variable (C V) in
/-- The canonical map `𝟙_ V ⟶ (𝟙_ (C ⊛⥤ V)).functor.obj (𝟙_ C)`
that exhibits `(𝟙_ (C ⊛⥤ V)).functor` as a Day convolution unit. -/
def ν : 𝟙_ V ⟶ (𝟙_ (C ⊛⥤ V)).functor.obj (𝟙_ C) :=
  LawfulDayConvolutionMonoidalCategoryStruct.unitUnit C V (C ⊛⥤ V)

variable (C V) in
/-- The reinterpretation of `ν` as a natural transformation. -/
@[simps]
def νNatTrans :
    Functor.fromPUnit.{0} (𝟙_ V) ⟶
      Functor.fromPUnit.{0} (𝟙_ C) ⋙ (𝟙_ (C ⊛⥤ V)).functor where
  app _ := ν C V

open LawfulDayConvolutionMonoidalCategoryStruct in
instance : (𝟙_ (C ⊛⥤ V)).functor.IsLeftKanExtension (νNatTrans C V) :=
  isPointwiseLeftKanExtensionUnitUnit C V (C ⊛⥤ V)|>.isLeftKanExtension

lemma unit_hom_ext {F : C ⊛⥤ V} {α β : 𝟙_ (C ⊛⥤ V) ⟶ F}
    (h : ν C V ≫ α.natTrans.app (𝟙_ C) = ν C V ≫ β.natTrans.app (𝟙_ C)) :
    α = β := by
  ext1
  apply Functor.hom_ext_of_isLeftKanExtension
    (𝟙_ (C ⊛⥤ V)).functor (νNatTrans C V)
  ext
  exact h

/-- Given `F : C ⊛⥤ V`, a morphism `𝟙_ V ⟶ F.functor.obj (𝟙_ C)` induces a
(unique) morphism `𝟙_ (C ⊛⥤ V) ⟶ F`. -/
def unitDesc {F : C ⊛⥤ V} (φ : 𝟙_ V ⟶ F.functor.obj (𝟙_ C)) :
    𝟙_ (C ⊛⥤ V) ⟶ F :=
  .mk <| Functor.descOfIsLeftKanExtension (𝟙_ (C ⊛⥤ V)).functor (νNatTrans C V)
    F.functor { app _ := φ }

@[reassoc (attr := simp)]
lemma ν_comp_unitDesc {F : C ⊛⥤ V} (φ : 𝟙_ V ⟶ F.functor.obj (𝟙_ C)) :
    ν C V ≫ (unitDesc φ).natTrans.app (𝟙_ C) = φ :=
  Functor.descOfIsLeftKanExtension_fac_app (𝟙_ (C ⊛⥤ V)).functor (νNatTrans C V)
    F.functor { app _ := φ } default

section structureLemmas

open LawfulDayConvolutionMonoidalCategoryStruct

open scoped Prod in
@[reassoc]
lemma η_naturality {F₁ F₂ : C ⊛⥤ V} {x₁ x₂ y₁ y₂ : C}
    (f₁ : x₁ ⟶ y₁) (f₂ : x₂ ⟶ y₂) :
    F₁.functor.map f₁ ▷ F₂.functor.obj x₂ ≫
      F₁.functor.obj y₁ ◁ F₂.functor.map f₂ ≫ (η F₁ F₂).app (y₁, y₂) =
    (η F₁ F₂).app (x₁, x₂) ≫ (F₁ ⊗ F₂).functor.map (f₁ ⊗ₘ f₂) := by
  simpa using η F₁ F₂|>.naturality (f₁ ×ₘ f₂)

open scoped Prod in
@[reassoc (attr := simp)]
lemma η_naturality_left {F₁ F₂ : C ⊛⥤ V} {x y : C}
    (f : x ⟶ y) (z : C) :
    F₁.functor.map f ▷ F₂.functor.obj z ≫ (η F₁ F₂).app (y, z) =
    (η F₁ F₂).app (x, z) ≫ (F₁ ⊗ F₂).functor.map (f ▷ z) := by
  simpa using η F₁ F₂|>.naturality (f ×ₘ (𝟙 z))

open scoped Prod in
@[reassoc (attr := simp)]
lemma η_naturality_right {F₁ F₂ : C ⊛⥤ V}
    (x : C) {y z : C} (f : y ⟶ z) :
    F₁.functor.obj x ◁ F₂.functor.map f ≫ (η F₁ F₂).app (x, z) =
    (η F₁ F₂).app (x, y) ≫ (F₁ ⊗ F₂).functor.map (x ◁ f) := by
  simpa using η F₁ F₂|>.naturality ((𝟙 x) ×ₘ f)

@[reassoc (attr := simp)]
lemma η_app_comp_tensorHom_natTrans_app_tensor
    {F₁ F₂ F₁' F₂' : C ⊛⥤ V} (f₁ : F₁ ⟶ F₁') (f₂ : F₂ ⟶ F₂') (x y : C) :
    (η F₁ F₂).app (x, y) ≫ (f₁ ⊗ₘ f₂).natTrans.app (x ⊗ y) =
    (f₁.natTrans.app x ⊗ₘ f₂.natTrans.app y) ≫ (η F₁' F₂').app (x, y) :=
  convolutionExtensionUnit_comp_ι_map_tensorHom_app C V f₁ f₂ _ _

@[reassoc (attr := simp)]
lemma η_app_comp_whiskerRight_natTrans_app_tensor
    {F₁ F₁' : C ⊛⥤ V} (f₁ : F₁ ⟶ F₁') (F₂ : C ⊛⥤ V) (x y : C) :
    (η F₁ F₂).app (x, y) ≫ (f₁ ▷ F₂).natTrans.app (x ⊗ y) =
    (f₁.natTrans.app x ▷ F₂.functor.obj y) ≫ (η F₁' F₂).app (x, y) := by
  simp [← tensorHom_id]

@[reassoc (attr := simp)]
lemma η_app_comp_whiskerLeft_natTrans_app_tensor
    (F₁ : C ⊛⥤ V) {F₂ F₂' : C ⊛⥤ V} (f₂ : F₂ ⟶ F₂') (x y : C) :
    (η F₁ F₂).app (x, y) ≫ (F₁ ◁ f₂).natTrans.app (x ⊗ y) =
    (F₁.functor.obj x ◁ f₂.natTrans.app y) ≫ (η F₁ F₂').app (x, y) := by
  simp [← id_tensorHom]

@[reassoc (attr := simp)]
lemma η_η_associator_hom (F F' F'' : C ⊛⥤ V) (x y z : C) :
    (η F F').app (x, y) ▷ F''.functor.obj z ≫
      (η (F ⊗ F') F'').app (x ⊗ y, z) ≫
      (α_ F F' F'').hom.natTrans.app ((x ⊗ y) ⊗ z) =
    (α_ _ _ _).hom ≫
      F.functor.obj x ◁ (η F' F'').app (y, z) ≫
      (η F (F' ⊗ F'')).app (x, y ⊗ z) ≫
      (F ⊗ F' ⊗ F'').functor.map (α_ _ _ _).inv :=
  associator_hom_unit_unit _ _ _ _ _ _ _

@[reassoc (attr := simp)]
lemma ν_η_leftUnitor (F : C ⊛⥤ V) (y : C) :
    ν C V ▷ F.functor.obj y ≫
      (η (𝟙_ (C ⊛⥤ V)) F).app (𝟙_ C, y) ≫
      (λ_ F).hom.natTrans.app (𝟙_ C ⊗ y) =
    (λ_ (F.functor.obj y)).hom ≫ F.functor.map (λ_ y).inv :=
  leftUnitor_hom_unit_app V F y

@[reassoc (attr := simp)]
lemma ν_η_rightUnitor (F : C ⊛⥤ V) (y : C) :
    (F.functor.obj y ◁ ν C V) ≫
      (η F (𝟙_ (C ⊛⥤ V))).app (y, 𝟙_ C) ≫
      (ρ_ F).hom.natTrans.app (y ⊗ 𝟙_ C) =
    (ρ_ _).hom ≫ F.functor.map (ρ_ y).inv :=
  rightUnitor_hom_unit_app V F y

end structureLemmas

section

attribute [local instance] dayConvolutionFunctorFunctor unitFunctorDayConvoltionUnit
variable {D : Type u₃} [Category.{v₃} D]

/-- We expose the "unit left" transformation that exhibits `U ⊛ F` as a
left Kan extension of `F ⋙ tensorLeft (𝟙_ V)` along `tensorLeft (𝟙_ C)`. -/
def unitLeft (F : C ⊛⥤ V) :
    F.functor ⋙ tensorLeft (𝟙_ V) ⟶ tensorLeft (𝟙_ C) ⋙ (𝟙_ (C ⊛⥤ V) ⊗ F).functor :=
  DayConvolutionUnit.unitLeft (𝟙_ (C ⊛⥤ V)).functor F.functor

@[simp]
lemma unitLeft_app (F : C ⊛⥤ V) (c : C) :
    (unitLeft F).app c =
    ν C V ▷ (F.functor.obj c) ≫ (η (𝟙_ _) F).app (𝟙_ _, c) :=
  rfl

/-- We expose the "unit right" transformation that exhibits `F ⊛ U` as a
left Kan extension of `F ⋙ tensorRight (𝟙_ V)` along `tensorRight (𝟙_ C)`. -/
def unitRight (F : C ⊛⥤ V) :
    F.functor ⋙ tensorRight (𝟙_ V) ⟶ tensorRight (𝟙_ C) ⋙ (F ⊗ 𝟙_ (C ⊛⥤ V)).functor :=
  DayConvolutionUnit.unitRight (𝟙_ (C ⊛⥤ V)).functor F.functor

@[simp]
lemma unitRight_app (F : C ⊛⥤ V) (c : C) :
    (unitRight F).app c =
    (F.functor.obj c) ◁ ν C V ≫ (η F (𝟙_ _)).app (c, 𝟙_ _) :=
  rfl

variable (C) in
/-- A variant of the previous which instead considers `(𝟙_ (C ⊛⥤ V)).functor ⊠ _` -/
def unitLeftExternal (K : D ⥤ V) :
    K ⋙ tensorLeft (𝟙_ V) ⟶ Prod.sectR (𝟙_ C) D ⋙ (𝟙_ (C ⊛⥤ V)).functor ⊠ K :=
  DayConvolutionUnit.unitLeftExternal _ K

@[simp]
lemma unitLeftExternal_app (K : D ⥤ V) (x : D) :
    (unitLeftExternal C K).app x = ν C V ▷ K.obj x :=
  rfl

variable (C) in
/-- A variant of the previous which instead considers `(𝟙_ (C ⊛⥤ V)).functor ⊠ _` -/
def unitRightExternal (K : D ⥤ V) :
    K ⋙ tensorRight (𝟙_ V) ⟶ Prod.sectL D (𝟙_ C) ⋙ K ⊠ (𝟙_ (C ⊛⥤ V)).functor :=
  DayConvolutionUnit.unitRightExternal _ K

@[simp]
lemma unitRightExternal_app (K : D ⥤ V) (x : D) :
    (unitRightExternal C K).app x = K.obj x ◁ ν C V :=
  rfl

open DayConvolution in
instance isLeftKanExtensionUnitLeft (F : C ⊛⥤ V) :
    (𝟙_ (C ⊛⥤ V) ⊗ F).functor.IsLeftKanExtension (unitLeft F) :=
  inferInstanceAs <| (_ ⊛ _).IsLeftKanExtension <|
    DayConvolutionUnit.unitLeft (𝟙_ (C ⊛⥤ V)).functor F.functor

open DayConvolution in
instance isLeftKanExtensionUnitRight (F : C ⊛⥤ V) :
    (F ⊗ 𝟙_ (C ⊛⥤ V)).functor.IsLeftKanExtension (unitRight F) :=
  inferInstanceAs <| (_ ⊛ _).IsLeftKanExtension <|
    DayConvolutionUnit.unitRight (𝟙_ (C ⊛⥤ V)).functor F.functor

instance isLeftKanExtensionUnitLeftExternal (K : D ⥤ V) :
    ((𝟙_ (C ⊛⥤ V)).functor ⊠ K).IsLeftKanExtension (unitLeftExternal C K) :=
  inferInstanceAs <| ((𝟙_ (C ⊛⥤ V)).functor ⊠ K).IsLeftKanExtension <|
    DayConvolutionUnit.unitLeftExternal _ K

open DayConvolution in
instance isLeftKanExtensionExtensionUnitLeft (F G : C ⊛⥤ V) (K : D ⥤ V) :
    ((F ⊗ G).functor ⊠ K).IsLeftKanExtension <|
      ExternalProduct.extensionUnitLeft _ (η F G) K :=
  inferInstanceAs <| ((F.functor ⊛ G.functor) ⊠ K).IsLeftKanExtension <|
    ExternalProduct.extensionUnitLeft _ (DayConvolution.unit F.functor G.functor) K

open DayConvolution in
instance isLeftKanExtensionExtensionUnitRight (F G : C ⊛⥤ V) (K : D ⥤ V) :
    (K ⊠ (F ⊗ G).functor).IsLeftKanExtension <|
      ExternalProduct.extensionUnitRight _ (η F G) K :=
  inferInstanceAs <| (K ⊠ (F.functor ⊛ G.functor)).IsLeftKanExtension <|
    ExternalProduct.extensionUnitRight _ (DayConvolution.unit F.functor G.functor) K

end


section Closed

variable [MonoidalClosed V]
    [∀ (F G : C ⥤ V) (c : C),
      Limits.HasEnd <|
        dayConvolutionInternalHomDiagramFunctor F |>.obj G |>.obj c]

instance : LawfulDayConvolutionClosedMonoidalCategoryStruct C V (C ⊛⥤ V) :=
  .ofHasEnds C V _ (fun _ _ ↦ ⟨_, ⟨equiv C V|>.counitIso.app _⟩⟩)

instance closed : MonoidalClosed (C ⊛⥤ V) :=
  LawfulDayConvolutionClosedMonoidalCategoryStruct.monoidalClosed C V _

open LawfulDayConvolutionClosedMonoidalCategoryStruct

variable (F G : C ⊛⥤ V)

/-- The canonical family of maps that exhibits
`(F ⟶[C ⊛⥤ V] G).functor.obj c` as an end of `F - ⟶[V] G.obj (- ⊗ c)`. -/
def ihom.π (c j : C) :
    (F ⟶[C ⊛⥤ V] G).functor.obj c ⟶
      (F.functor.obj j ⟶[V] G.functor.obj (j ⊗ c)) :=
  ihomDayConvolutionInternalHom C V F G|>.π c j

@[reassoc]
lemma ihom.hπ (c : C) ⦃j j' : C⦄ (φ : j ⟶ j') :
    ihom.π F G c j ≫ (ihom (F.functor.obj j)).map (G.functor.map <| φ ▷ c) =
    ihom.π F G c j' ≫
      (MonoidalClosed.pre <| F.functor.map φ).app (G.functor.obj <| j' ⊗ c) :=
  ihomDayConvolutionInternalHom C V F G|>.hπ c φ

/-- The wedge on `F - ⟶[V] G.obj (- ⊗ c)` defined by `ihom.π` and `ihom.hπ` is
a limit wedge. -/
def ihom.isLimitWedge (c : C) :
    Limits.IsLimit <|
      (Limits.Wedge.mk
        (F := dayConvolutionInternalHomDiagramFunctor
          F.functor |>.obj G.functor |>.obj c)
        ((F ⟶[C ⊛⥤ V] G).functor.obj c) (ihom.π F G c) (ihom.hπ F G c)) :=
  ihomDayConvolutionInternalHom C V F G|>.isLimitWedge c

@[reassoc (attr := simp)]
lemma ihom_functor_map_comp_π {c c' : C} (f : c ⟶ c') (j : C) :
    ((F ⟶[C ⊛⥤ V] G).functor.map f) ≫ ihom.π F G c' j =
    ihom.π F G c j ≫ (ihom <| F.functor.obj j).map (G.functor.map <| j ◁ f) :=
  ihomDayConvolutionInternalHom C V F G|>.map_comp_π f j

@[reassoc (attr := simp)]
lemma unit_app_ev_natTrans_app_app (x y : C) :
    (η F (F ⟶[_] G)).app (x, y) ≫ ((ihom.ev F).app G).natTrans.app (x ⊗ y) =
    MonoidalClosed.uncurry (ihom.π F G y x) := by
  change _ ≫ ((ι C V (C ⊛⥤ V)).map (ev_app C V F G)).app _ = _
  rw [ι_map_ev_app C V F G]
  letI := convolution C V (C ⊛⥤ V)
  exact ihomDayConvolutionInternalHom C V F G|>.unit_app_ev_app_app x y

@[reassoc (attr := simp)]
lemma coev_app_π (c j : C) :
    (ihom.coev F|>.app G).natTrans.app c ≫ ihom.π F (F ⊗ G) c j =
    MonoidalClosed.curry (η F G|>.app (j, c)) := by
  change ((ι C V (C ⊛⥤ V)).map (coev_app C V F G)).app _ ≫ _ = _
  rw [ι_map_coev_app C V F G]
  letI := convolution C V (C ⊛⥤ V)
  exact ihomDayConvolutionInternalHom C V F (F ⊗ G)|>.coev_app_π
    (F := ι C V (C ⊛⥤ V)|>.obj F) (G := ι C V (C ⊛⥤ V)|>.obj G) c j

variable {G} in
@[reassoc (attr := simp)]
lemma ihom_map_comp_π {G' : C ⊛⥤ V} (f : G ⟶ G') (c j : C) :
    ((ihom F).map f).natTrans.app c ≫ ihom.π F G' c j =
    ihom.π F G c j ≫
      (ihom <| F.functor.obj j).map (f.natTrans.app <| j ⊗ c) := by
  change (ι C V (C ⊛⥤ V)|>.map <|
    LawfulDayConvolutionClosedMonoidalCategoryStruct.ihom C V F|>.map _).app
      _ ≫ _ = _
  rw [ι_map_ihom_map]
  exact ihomDayConvolutionInternalHom C V F G|>.map_app_comp_π _ _ c j

end Closed

end DayFunctor

end

end CategoryTheory.MonoidalCategory
