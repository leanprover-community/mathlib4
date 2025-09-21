/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Monoidal.DayConvolution

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
lemma functor_mk (F : C ⊛⥤ V) : mk F.functor = F := rfl

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
    ⟨_, ⟨equiv C V|>.counitIso.app _⟩⟩

@[simps! ι_obj ι_map]
instance : LawfulDayConvolutionMonoidalCategoryStruct C V (C ⊛⥤ V) :=
  lawfulDayConvolutionMonoidalCategoryStructOfHasDayConvolutions
    (equiv C V).functor
    (equiv C V).fullyFaithfulFunctor
    (fun _ _ => ⟨_, ⟨equiv C V|>.counitIso.app _⟩⟩)
    ⟨_, ⟨equiv C V|>.counitIso.app _⟩⟩

/-- The unit transformation exhibiting `(F ⊗ G).functor` as a left Kan extension of
`F.functor ⊠ G.functor` along `tensor C`. -/
def η (F G : C ⊛⥤ V) :
    F.functor ⊠ G.functor ⟶ tensor C ⋙ (F ⊗ G).functor :=
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
  apply Functor.hom_ext_of_isLeftKanExtension
    (F ⊗ G).functor (η F G) _
  ext ⟨x, y⟩
  exact h x y

/-- A natural transformation `F.functor ⊠ G.functor ⟶ tensor C ⋙ H.functor`
defines a morphism `F ⨂ G ⟶ H`. -/
def tensorDesc {F G H : C ⊛⥤ V}
    (α : F.functor ⊠ G.functor ⟶ tensor C ⋙ H.functor) :
    F ⊗ G ⟶ H :=
  .mk <| (F ⊗ G).functor.descOfIsLeftKanExtension (η F G) H.functor α

lemma η_comp_tensorDec {F G H : C ⊛⥤ V}
    (α : F.functor ⊠ G.functor ⟶ tensor C ⋙ H.functor) :
   η F G ≫ Functor.whiskerLeft _ (tensorDesc α).natTrans = α :=
  Functor.descOfIsLeftKanExtension_fac _ _ _ _

@[reassoc (attr := simp)]
lemma η_comp_tensorDesc_app {F G H : C ⊛⥤ V}
    (α : F.functor ⊠ G.functor ⟶ tensor C ⋙ H.functor) (x y : C) :
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
      (CostructuredArrow.proj (tensor C) (x ⊗ y) ⋙ F.functor ⊠ G.functor)
      (.mk (Y := (x, y)) <| 𝟙 (x ⊗ y)) := by
  simpa [η, isoPointwiseLeftKanExtension] using
    Functor.descOfIsLeftKanExtension_fac_app
      (F ⊗ G).functor (η F G) _
      ((tensor C).pointwiseLeftKanExtensionUnit (F.functor ⊠ G.functor)) (x, y)

@[simp]
lemma ι_comp_isoPointwiseLeftKanExtension_inv (F G : C ⊛⥤ V) (x y : C) :
    Limits.colimit.ι
      (CostructuredArrow.proj (tensor C) (x ⊗ y) ⋙ F.functor ⊠ G.functor)
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

end DayFunctor

end

end CategoryTheory.MonoidalCategory
