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

universe v₁ v₂ v₃ u₁ u₂ u₃

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
        simpa [-NatTrans.naturality] using congr_arg (ihom <| F.obj <| unop j).map
          (η.naturality <| k ◁ f) }

/-- `DayConvolutionInternalHom F G H` asserts that `H` is the value at `G` of
an internal hom functor of `F` for the Day convolution monoidal structure.
This is phrased as the data of a limit `CategoryTheory.Limits.Wedge`
(i.e an end) on `internalHomDiagramFunctor F|>.obj G|>.obj c` and
`c`, with tip `(H.obj G).obj c` and a compatibility condition asserting that
the functoriality of `H` identifies to the functoriality of ends. -/
structure DayConvolutionInternalHom (F : C ⥤ V) (G : C ⥤ V) (H : C ⥤ V) where
  /-- The canonical projections maps -/
  π (c j : C) : H.obj c ⟶ (ihom <| F.obj j).obj (G.obj <| j ⊗ c)
  /-- The projections maps assemble into a wedge. -/
  hπ (c : C) ⦃i j : C⦄ (f : i ⟶ j) :
    π c i ≫ (ihom (F.obj i)).map (G.map <| f ▷ c) =
    π c j ≫ (MonoidalClosed.pre <| F.map f).app (G.obj <| j ⊗ c)
  /-- The wedge defined by `π` and `hπ` is a limit wedge, i.e `H.obj c` is
  an end of `internalHomDiagramFunctor F G|>.obj c`. -/
  isLimitWedge c :
    Limits.IsLimit <|
      Limits.Wedge.mk (F := internalHomDiagramFunctor F|>.obj G|>.obj c)
        (H.obj c) (π c) (hπ c)
  /-- The functoriality of `H.obj G` identifies (through
  `Limits.Wedge.IsLimit.hom_ext`) with the functoriality on ends induced by
  functoriality of `internalHomDiagramFunctor F|>.obj G`. -/
  obj_map_comp_π {c c' : C} (f : c ⟶ c') (j : C) :
    H.map f ≫ π c' j =
    π c j ≫ (ihom <| F.obj j).map (G.map <| j ◁ f)

namespace DayConvolutionInternalHom

open scoped DayConvolution

attribute [reassoc (attr := simp)] obj_map_comp_π hπ

variable {F : C ⥤ V} {G : C ⥤ V} {H : C ⥤ V}

/-- If we have a map `G ⟶ G'` and a `DayConvolutionInternalHom F G' H'`, then
there is a unique map `H ⟶ H'` induced by functoriality of ends and functoriality
of `internalHomDiagramFunctor F`. -/
def map (ℌ : DayConvolutionInternalHom F G H) {G' : C ⥤ V} {H' : C ⥤ V}
    (f : G ⟶ G') (ℌ' : DayConvolutionInternalHom F G' H') :
    H ⟶ H' where
  app c := Limits.Wedge.IsLimit.lift (ℌ'.isLimitWedge c)
    (fun j ↦ (ℌ.π c j) ≫
      (internalHomDiagramFunctor F|>.map f|>.app c|>.app (op j)|>.app j))
    (fun ⦃j j'⦄ φ ↦ by
      haveI := congrArg (fun t ↦ t.app j') <|
        internalHomDiagramFunctor F|>.map f|>.app c|>.naturality φ.op
      dsimp at this
      dsimp
      rw [Category.assoc, ← (ihom (F.obj j)).map_comp, ← f.naturality,
        Functor.map_comp, reassoc_of% ℌ.hπ]
      simp)
  naturality {c c'} f := by
    apply Limits.Wedge.IsLimit.hom_ext (ℌ'.isLimitWedge c')
    intro j
    dsimp
    simp only [Category.assoc, obj_map_comp_π]
    rw [← Limits.Wedge.mk_ι (F := internalHomDiagramFunctor F|>.obj _|>.obj c')
        (H'.obj c') (ℌ'.π c') (ℌ'.hπ c'),
      ← Limits.Wedge.mk_ι (F := internalHomDiagramFunctor F|>.obj _|>.obj c)
        (H'.obj c) (ℌ'.π c) (ℌ'.hπ c),
      Limits.Wedge.IsLimit.lift_ι (ℌ'.isLimitWedge c'),
      Limits.Wedge.IsLimit.lift_ι_assoc (ℌ'.isLimitWedge c) ]
    simp [← Functor.map_comp]

@[reassoc (attr := simp)]
lemma map_app_comp_π (ℌ : DayConvolutionInternalHom F G H)
    {G' : C ⥤ V} {H' : C ⥤ V} (f : G ⟶ G')
    (ℌ' : DayConvolutionInternalHom F G' H') (c : C) (j : C) :
    (ℌ.map f ℌ').app c ≫ ℌ'.π c j =
    ℌ.π c j ≫ (ihom <| F.obj j).map (f.app <| j ⊗ c) := by
  dsimp [map]
  rw [← Limits.Wedge.mk_ι (F := internalHomDiagramFunctor F|>.obj _|>.obj c)
      (H'.obj c) (ℌ'.π c) (ℌ'.hπ c),
    Limits.Wedge.IsLimit.lift_ι (ℌ'.isLimitWedge c)]

section ev

variable [DayConvolution F H] (ℌ : DayConvolutionInternalHom F G H)

/-- Given `ℌ : DayConvolutionInternalHom F H`, if we think of `H.obj G`
as the internal hom `[F, G]`, then this is the transformation
corresponding to the component at `G` of the "evaluation" natural morphism
`F ⊛ [F, _] ⟶ 𝟭`. -/
def ev_app : F ⊛ H ⟶ G :=
  DayConvolution.corepresentableBy F H|>.homEquiv.symm <|
    { app := fun x => MonoidalClosed.uncurry <| ℌ.π x.2 x.1
      naturality {x y} f := by
        haveI := congrArg (fun t ↦ F.obj x.1 ◁ t) <| ℌ.hπ x.2 f.1
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
    ((DayConvolution.unit F H).app (x, y) ≫ (ℌ.ev_app).app (x ⊗ y)) =
    MonoidalClosed.uncurry (ℌ.π y x) := by
  simp [ev_app]
  haveI := Functor.descOfIsLeftKanExtension_fac_app (F ⊛ H)
    (DayConvolution.unit F H) G
  dsimp at this
  rw [this]

lemma ev_naturality_app {G' H' : C ⥤ V} (ℌ' : DayConvolutionInternalHom F G' H')
    [DayConvolution F H'] (η : G ⟶ G') :
    DayConvolution.map (𝟙 F) (ℌ.map η ℌ') ≫ ℌ'.ev_app = ℌ.ev_app ≫ η := by
  apply DayConvolution.corepresentableBy F H|>.homEquiv.injective
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

variable {G : C ⥤ V} [DayConvolution F G]
    (ℌ : DayConvolutionInternalHom F (F ⊛ G) H)

/-- Given `ℌ : DayConvolutionInternalHom F H`, if we think of `H.obj G`
as the internal hom `[F, G]`, then this is the transformation
corresponding to the component at `G` of the "coevaluation" natural morphism
`𝟭 ⟶ [F, F ⊛ _]`. -/
def coev_app : G ⟶ H where
  app c :=
    Limits.Wedge.IsLimit.lift (ℌ.isLimitWedge c)
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
    apply Limits.Wedge.IsLimit.hom_ext <| ℌ.isLimitWedge c'
    intro (j : C)
    simp [Limits.multicospanIndexEnd_left,
      Limits.Multifork.ofι_pt, Limits.Wedge.mk_ι, Category.assoc]
    rw [← Limits.Wedge.mk_ι (F := internalHomDiagramFunctor F|>.obj _|>.obj c)
        (H.obj c) (ℌ.π c) (ℌ.hπ c),
      ← Limits.Wedge.mk_ι (F := internalHomDiagramFunctor F|>.obj _|>.obj c')
        (H.obj c') (ℌ.π c') (ℌ.hπ c'),
      Limits.Wedge.IsLimit.lift_ι_assoc, Limits.Wedge.IsLimit.lift_ι]
    haveI := DayConvolution.unit_naturality F G (𝟙 j) f
    simp only [Functor.map_id, id_tensorHom] at this
    replace this := congrArg MonoidalClosed.curry this
    simp only [MonoidalClosed.curry_natural_right] at this
    rw [← this]
    simp [MonoidalClosed.curry_eq]

@[reassoc (attr := simp)]
lemma coev_app_comp_π (c j : C) :
    ℌ.coev_app.app c ≫ ℌ.π c j =
    MonoidalClosed.curry ((DayConvolution.unit F G).app (j, c)) := by
  dsimp [coev_app]
  rw [← Limits.Wedge.mk_ι (F := internalHomDiagramFunctor F|>.obj _|>.obj c)
      (H.obj c) (ℌ.π c) (ℌ.hπ c),
    Limits.Wedge.IsLimit.lift_ι]

@[simp]
lemma coev_naturality_app {G' : C ⥤ V} [DayConvolution F G'] (η : G ⟶ G')
    (ℌ'' : DayConvolutionInternalHom F (F ⊛ G') H) :
    η ≫ ℌ''.coev_app =
    ℌ.coev_app ≫ ℌ.map (DayConvolution.map (𝟙 _) η) ℌ'' := by
  ext c
  dsimp
  apply Limits.Wedge.IsLimit.hom_ext <| ℌ''.isLimitWedge c
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
    (ℌ : DayConvolutionInternalHom F (F ⊛ G) H) [DayConvolution F H] :
    DayConvolution.map (𝟙 F) ℌ.coev_app ≫ ℌ.ev_app = 𝟙 (F ⊛ G) := by
  apply DayConvolution.corepresentableBy F G|>.homEquiv.injective
  dsimp
  ext ⟨x, y⟩
  apply MonoidalClosed.curry_injective
  simp [MonoidalClosed.curry_natural_left]

theorem right_triangle_component (G : C ⥤ V) [DayConvolution F H]
    (ℌ : DayConvolutionInternalHom F G H) {H' : C ⥤ V}
    (ℌ' : DayConvolutionInternalHom F (F ⊛ H) H') :
    ℌ'.coev_app ≫ ℌ'.map ℌ.ev_app ℌ = 𝟙 H := by
  ext c
  apply Limits.Wedge.IsLimit.hom_ext <| ℌ.isLimitWedge c
  intro j
  apply MonoidalClosed.uncurry_injective
  simp [MonoidalClosed.uncurry_natural_right]

end DayConvolutionInternalHom

end

section

open LawfulDayConvolutionMonoidalCategoryStruct

class LawfulDayConvolutionClosedMonoidalCategoryStruct
    (C : Type u₁) [Category.{v₁} C] (V : Type u₂) [Category.{v₂} V]
    [MonoidalCategory C] [MonoidalCategory V] [MonoidalClosed V]
    (D : Type u₃) [Category.{v₃} D] [MonoidalCategoryStruct D]
    [LawfulDayConvolutionMonoidalCategoryStruct C V D] where
  ihom (d : D) : D ⥤ D
  ihomDayConvolutionInternalHom (d d' : D) :
    DayConvolutionInternalHom
      (ι C V D|>.obj d) (ι C V D|>.obj d') (ι C V D|>.obj <| (ihom d).obj d')
  ihomMap (d : D) {d' d'' : D} (f : d' ⟶ d'') (c j : C) :
    (ι C V D|>.map <| (ihom d).map f).app c ≫
      (ihomDayConvolutionInternalHom d d'').π c j =
    (ihomDayConvolutionInternalHom d d').π c j ≫
      (CategoryTheory.ihom <| (ι C V D|>.obj d).obj j).map
        (ι C V D|>.map f|>.app <| j ⊗ c)

namespace LawfulDayConvolutionClosedMonoidalCategoryStruct

variable (C : Type u₁) [Category.{v₁} C] (V : Type u₂) [Category.{v₂} V]
    [MonoidalCategory C] [MonoidalCategory V] [MonoidalClosed V]

noncomputable def ofHasEnd
    (D : Type u₃) [Category.{v₃} D] [MonoidalCategoryStruct D]
    [LawfulDayConvolutionMonoidalCategoryStruct C V D]
    [∀ (d d' : D) (c : C),
      Limits.HasEnd <|
        internalHomDiagramFunctor (ι C V D |>.obj d) |>.obj (ι C V D |>.obj d') |>.obj c] 
    LawfulDayConvolutionClosedMonoidalCategoryStruct C V D where
  ihom d := sorry
  ihomDayConvolutionInternalHom := sorry
  ihomMap := sorry


end

end

end CategoryTheory.MonoidalCategory
