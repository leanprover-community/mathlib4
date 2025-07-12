/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Monoidal.DayConvolution
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Limits.Shapes.End

/-! # Internal homs for day convolution

Given a category `V` that is monoidal closed, a category `C` that
is monoidal, a functor `C ⥤ V`, and given the data of suitable day convolutions
and suitable ends of profunctors `c c₁ c₂ ↦ ihom (F c₁) (·.obj (c₂ ⊗ c))`,
we prove that the data of the units of the left Kan extensions that define
day convolutions and the data of the canonical morphisms to the aforementioned
ends can be organised as data that exhibit `F` as monoidal closed in `C ⥤ V` for
the Day convolution monoidal structure.

## TODOs
* When `LawfulDayConvolutionMonoidalStruct` (#26820) lands, transport the
constructions here to produce actual `CategoryTheory.MonoidalClosed` instances.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.MonoidalCategory
open scoped ExternalProduct
open Opposite

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V]
  [MonoidalCategory C] [MonoidalCategory V] [MonoidalClosed V]

/-- Given `F : C ⥤ V`, this is the functor
`G ↦ c c₁ c₂ ↦ ihom (F c₁) (G.obj (c₂ ⊗ c))`.
The internal hom functor for Day convolution `[F, -]` is naturally isomorphic
to the functor `G ↦ c ↦ end_ (c₁ c₂ ↦ ihom (F c₁) (G.obj (c₂ ⊗ c)))`, hence
this definition. -/
@[simps!]
def internalHomDiagramFunctor (F : C ⥤ V) : (C ⥤ V) ⥤ C ⥤ Cᵒᵖ ⥤ C ⥤ V where
  obj G :=
    { obj c := Functor.whiskeringLeft₂ _|>.obj F.op|>.obj
        (tensorRight c ⋙ G)|>.obj MonoidalClosed.internalHom
      map {c c'} f := Functor.whiskeringLeft₂ _|>.obj F.op|>.map
        (Functor.whiskerRight (curriedTensor C|>.flip.map f) G)|>.app
          MonoidalClosed.internalHom }
  map {G G'} η :=
    { app c := Functor.whiskeringLeft₂ _|>.obj F.op|>.map
        (Functor.whiskerLeft _ η) |>.app MonoidalClosed.internalHom
      naturality {c c'} f := by
        ext j k
        dsimp
        simpa [-NatTrans.naturality] using congr_arg (ihom (F.obj (unop j))).map
          (η.naturality <| k ◁ f) }

/-- `DayConvolutionInternalHom F H` asserts that `H` is an
internal hom functor of `F` for the Day convolution monoidal structure.
This is phrased as the data of a limit `CategoryTheory.Limits.Wedge`
(i.e an end) on `internalHomDiagramFunctor F|>.obj G|>.obj c` for every `G` and
`c`, with tip `(H.obj G).obj c` and two compatibility conditions asserting that
the functoriality of `H` identifies to the functoriality of ends. -/
structure DayConvolutionInternalHom (F : C ⥤ V) (H : (C ⥤ V) ⥤ C ⥤ V) where
  /-- The canonical projections maps -/
  π (G : C ⥤ V) (c j : C) :
    (H.obj G).obj c ⟶ (ihom (F.obj j)).obj (G.obj (j ⊗ c))
  /-- The projections maps assemble into a wedge. -/
  hπ (G : C ⥤ V) (c : C) ⦃i j : C⦄ (f : i ⟶ j) :
    π G c i ≫ (ihom (F.obj i)).map (G.map (f ▷ c)) =
    π G c j ≫ (MonoidalClosed.pre (F.map f)).app (G.obj (j ⊗ c))
  /-- The wedge defined by `π` and `hπ` is a limit wedge, i.e `H.obj c` is
  an end of `internalHomDiagramFunctor F G|>.obj c`. -/
  isLimitWedge G c :
    Limits.IsLimit <|
      Limits.Wedge.mk (F := internalHomDiagramFunctor F|>.obj G|>.obj c)
        (H.obj G|>.obj c) (π G c) (hπ G c)
  /-- The functoriality of `H.obj G` identifies (through
  `Limits.Wedge.IsLimit.hom_ext`) with the functoriality on ends induced by
  functoriality of `internalHomDiagramFunctor F|>.obj G`. -/
  obj_map_comp_π (G : C ⥤ V) {c c' : C} (f : c ⟶ c') (j : C) :
    (H.obj G).map f ≫ π G c' j =
    π G c j ≫ (ihom (F.obj j)).map (G.map (j ◁ f))
  /-- The functoriality of `H` in its first variable identifies (through
  `Limits.Wedge.IsLimit.hom_ext`) with the functoriality on ends
  induced by functoriality of `internalHomDiagramFunctor F`. -/
  map_app_comp_π {G G' : C ⥤ V} (η : G ⟶ G') (c j : C) :
    (H.map η).app c ≫ π G' c j =
    π G c j ≫ (ihom (F.obj j)).map (η.app (j ⊗ c))


namespace DayConvolutionInternalHom
open scoped DayConvolution

attribute [reassoc (attr := simp)] obj_map_comp_π map_app_comp_π hπ

variable {F : C ⥤ V} {H : (C ⥤ V) ⥤ C ⥤ V}
  (ℌ : DayConvolutionInternalHom F H)

section ev

variable (G : C ⥤ V) [DayConvolution F (H.obj G)]

/-- Given `ℌ : DayConvolutionInternalHom F H`, if we think of `H.obj G`
as the internal hom `[F, G]`, then this is the transformation
corresponding to the component at `G` of the "evaluation" natural morphism
`F ⊛ [F, _] ⟶ 𝟭`. -/
def ev_app : F ⊛ (H.obj G) ⟶ G :=
  DayConvolution.corepresentableBy F (H.obj G)|>.homEquiv.symm <|
    { app := fun x => MonoidalClosed.uncurry <| ℌ.π G x.2 x.1
      naturality {x y} f := by
        haveI := congrArg (fun t ↦ F.obj x.1 ◁ t) <| ℌ.hπ G x.2 f.1
        dsimp at this ⊢
        simp only [whiskerLeft_comp] at this
        simp only [Category.assoc, MonoidalClosed.uncurry_eq, Functor.id_obj]
        rw [← whiskerLeft_comp_assoc, obj_map_comp_π]
        simp [← whisker_exchange_assoc, tensorHom_def,
          ← ihom.ev_naturality_assoc]
        rw [reassoc_of% this]
        simp }

@[reassoc (attr := simp)]
lemma curry_unit_app_comp_ev_app_app (x y : C) :
    ((DayConvolution.unit F (H.obj G)).app (x, y) ≫
      (ev_app ℌ G).app (x ⊗ y)) =
    MonoidalClosed.uncurry (ℌ.π G y x) := by
  simp [ev_app]
  haveI := Functor.descOfIsLeftKanExtension_fac_app
    (F ⊛ H.obj G) (DayConvolution.unit F (H.obj G)) G
  dsimp at this
  rw [this]

variable {G} in
lemma ev_naturality_app {G' : C ⥤ V} [DayConvolution F (H.obj G')] (η : G ⟶ G') :
    DayConvolution.map (𝟙 F) (H.map η) ≫ (ev_app ℌ G') =
    (ev_app ℌ G) ≫ η := by
  apply DayConvolution.corepresentableBy F (H.obj G)|>.homEquiv.injective
  dsimp
  ext ⟨x, y⟩
  dsimp
  simp only [DayConvolution.unit_app_map_app_assoc,
    externalProductBifunctor_obj_obj, NatTrans.id_app, id_tensorHom,
    curry_unit_app_comp_ev_app_app, MonoidalClosed.uncurry_eq,
    Functor.id_obj, curry_unit_app_comp_ev_app_app_assoc, Category.assoc]
  rw [← whiskerLeft_comp_assoc, map_app_comp_π]
  simp

end ev

section coev

variable (G : C ⥤ V) [DayConvolution F G]

/-- Given `ℌ : DayConvolutionInternalHom F H`, if we think of `H.obj G`
as the internal hom `[F, G]`, then this is the transformation
corresponding to the component at `G` of the "coevaluation" natural morphism
`𝟭 ⟶ [F, F ⊛ _]`. -/
def coev_app : G ⟶ H.obj (F ⊛ G) where
  app c :=
    Limits.Wedge.IsLimit.lift (ℌ.isLimitWedge (F ⊛ G) c)
      (fun c' => MonoidalClosed.curry <|
        (DayConvolution.unit F G).app (c', c))
        (fun {c' c''} f => by
          haveI := DayConvolution.unit_naturality F G f (𝟙 c)
          simp only [Functor.map_id, tensorHom_id] at this
          replace this := congrArg MonoidalClosed.curry this
          simp only [MonoidalClosed.curry_natural_right] at this
          dsimp
          rw [← this]
          simp [MonoidalClosed.curry_eq])
  naturality {c c'} f := by
    dsimp
    apply Limits.Wedge.IsLimit.hom_ext (ℌ.isLimitWedge (F ⊛ G) c')
    intro (j : C)
    simp [Limits.multicospanIndexEnd_left,
      Limits.Multifork.ofι_pt, Limits.Wedge.mk_ι, Category.assoc]
    rw [← Limits.Wedge.mk_ι (F := internalHomDiagramFunctor F|>.obj _|>.obj c)
        (H.obj (F ⊛ G)|>.obj c) (ℌ.π (F ⊛ G) c) (ℌ.hπ (F ⊛ G) c),
      ← Limits.Wedge.mk_ι (F := internalHomDiagramFunctor F|>.obj _|>.obj c')
        (H.obj (F ⊛ G)|>.obj c') (ℌ.π (F ⊛ G) c') (ℌ.hπ (F ⊛ G) c'),
      Limits.Wedge.IsLimit.lift_ι_assoc, Limits.Wedge.IsLimit.lift_ι]
    haveI := DayConvolution.unit_naturality F G (𝟙 j) f
    simp only [Functor.map_id, id_tensorHom] at this
    replace this := congrArg MonoidalClosed.curry this
    simp only [MonoidalClosed.curry_natural_right] at this
    rw [← this]
    simp [MonoidalClosed.curry_eq]

@[reassoc (attr := simp)]
lemma coev_app_comp_π (c j : C) :
    (ℌ.coev_app G).app c ≫ ℌ.π (F ⊛ G) c j =
    MonoidalClosed.curry ((DayConvolution.unit F G).app (j, c)) := by
  dsimp [coev_app]
  rw [← Limits.Wedge.mk_ι (F := internalHomDiagramFunctor F|>.obj _|>.obj c)
      (H.obj (F ⊛ G)|>.obj c) (ℌ.π (F ⊛ G) c) (ℌ.hπ (F ⊛ G) c),
    Limits.Wedge.IsLimit.lift_ι]

variable {G} in
@[simp]
lemma coev_naturality_app {G' : C ⥤ V} [DayConvolution F G'] (η : G ⟶ G') :
    η ≫ ℌ.coev_app G' = ℌ.coev_app G ≫ H.map (DayConvolution.map (𝟙 _) η) := by
  ext c
  dsimp
  apply Limits.Wedge.IsLimit.hom_ext (ℌ.isLimitWedge (F ⊛ G') c)
  intro j
  apply MonoidalClosed.uncurry_injective
  dsimp
  simp only [Category.assoc, coev_app_comp_π, Functor.comp_obj, tensor_obj,
    map_app_comp_π, coev_app_comp_π_assoc, MonoidalClosed.uncurry_natural_right,
    MonoidalClosed.uncurry_curry, DayConvolution.unit_app_map_app,
    NatTrans.id_app, id_tensorHom]
  simp [MonoidalClosed.uncurry_natural_left]

end coev

theorem left_triangle_component (G : C ⥤ V) [DayConvolution F G]
    [DayConvolution F (H.obj (F ⊛ G))] :
    DayConvolution.map (𝟙 F) (ℌ.coev_app G) ≫ ℌ.ev_app (F ⊛ G) = 𝟙 (F ⊛ G) := by
  apply DayConvolution.corepresentableBy F G|>.homEquiv.injective
  dsimp
  ext ⟨x, y⟩
  apply MonoidalClosed.curry_injective
  simp [MonoidalClosed.curry_natural_left]

theorem right_triangle_component (G : C ⥤ V) [DayConvolution F (H.obj G)] :
    ℌ.coev_app (H.obj G) ≫ H.map (ℌ.ev_app G) = 𝟙 (H.obj G) := by
  ext c
  apply Limits.Wedge.IsLimit.hom_ext (ℌ.isLimitWedge _ c)
  intro j
  apply MonoidalClosed.uncurry_injective
  simp [MonoidalClosed.uncurry_natural_right]

end DayConvolutionInternalHom

end

end CategoryTheory.MonoidalCategory
