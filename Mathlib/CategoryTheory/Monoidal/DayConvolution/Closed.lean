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
def dayConvolutionInternalHomDiagramFunctor (F : C ⥤ V) :
    (C ⥤ V) ⥤ C ⥤ Cᵒᵖ ⥤ C ⥤ V where
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
        simpa [-NatTrans.naturality] using
          congr_arg (ihom <| F.obj <| unop j).map (η.naturality <| k ◁ f) }

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
      Limits.Wedge.mk
        (F := dayConvolutionInternalHomDiagramFunctor F|>.obj G|>.obj c)
        (H.obj c) (π c) (hπ c)
  /-- The functoriality of `H.obj G` identifies (through
  `Limits.Wedge.IsLimit.hom_ext`) with the functoriality on ends induced by
  functoriality of `internalHomDiagramFunctor F|>.obj G`. -/
  map_comp_π {c c' : C} (f : c ⟶ c') (j : C) :
    H.map f ≫ π c' j =
    π c j ≫ (ihom <| F.obj j).map (G.map <| j ◁ f)

namespace DayConvolutionInternalHom

open scoped DayConvolution

attribute [reassoc (attr := simp)] map_comp_π
attribute [reassoc] hπ

variable {F : C ⥤ V} {G : C ⥤ V} {H : C ⥤ V}

/-- If we have a map `G ⟶ G'` and a `DayConvolutionInternalHom F G' H'`, then
there is a unique map `H ⟶ H'` induced by functoriality of ends and functoriality
of `internalHomDiagramFunctor F`. -/
def map (ℌ : DayConvolutionInternalHom F G H) {G' : C ⥤ V} {H' : C ⥤ V}
    (f : G ⟶ G') (ℌ' : DayConvolutionInternalHom F G' H') :
    H ⟶ H' where
  app c := Limits.Wedge.IsLimit.lift (ℌ'.isLimitWedge c)
    (fun j ↦ (ℌ.π c j) ≫
      (dayConvolutionInternalHomDiagramFunctor
        F|>.map f|>.app c|>.app (op j)|>.app j))
    (fun ⦃j j'⦄ φ ↦ by
      haveI := congrArg (fun t ↦ t.app j') <|
        dayConvolutionInternalHomDiagramFunctor
          F|>.map f|>.app c|>.naturality φ.op
      dsimp at this
      dsimp
      rw [Category.assoc, ← (ihom (F.obj j)).map_comp, ← f.naturality,
        Functor.map_comp, reassoc_of% ℌ.hπ]
      simp)
  naturality {c c'} f := by
    apply Limits.Wedge.IsLimit.hom_ext (ℌ'.isLimitWedge c')
    intro j
    dsimp
    simp only [Category.assoc, map_comp_π]
    rw [← Limits.Wedge.mk_ι
        (F := dayConvolutionInternalHomDiagramFunctor F|>.obj _|>.obj c')
        (H'.obj c') (ℌ'.π c') (ℌ'.hπ c'),
      ← Limits.Wedge.mk_ι
        (F := dayConvolutionInternalHomDiagramFunctor F|>.obj _|>.obj c)
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
  rw [← Limits.Wedge.mk_ι
      (F := dayConvolutionInternalHomDiagramFunctor F|>.obj _|>.obj c)
      (H'.obj c) (ℌ'.π c) (ℌ'.hπ c),
    Limits.Wedge.IsLimit.lift_ι (ℌ'.isLimitWedge c)]

@[simp]
lemma map_id (ℌ : DayConvolutionInternalHom F G H) : ℌ.map (𝟙 _) ℌ = 𝟙 _ := by
  ext
  apply Limits.Wedge.IsLimit.hom_ext (ℌ.isLimitWedge _)
  aesop_cat

lemma map_comp (ℌ : DayConvolutionInternalHom F G H)
    {G' : C ⥤ V} {H' : C ⥤ V}
    (f : G ⟶ G') (ℌ' : DayConvolutionInternalHom F G' H')
    {G'' : C ⥤ V} {H'' : C ⥤ V}
    (g : G' ⟶ G'') (ℌ'' : DayConvolutionInternalHom F G'' H'') :
    ℌ.map (f ≫ g) ℌ'' = ℌ.map f ℌ' ≫ ℌ'.map g ℌ'' := by
  ext
  apply Limits.Wedge.IsLimit.hom_ext (ℌ''.isLimitWedge _)
  aesop_cat

/-- transport a `DayConvolutionInternalHom F G H` along a natural isomorphism. -/
def transport (ℌ : DayConvolutionInternalHom F G H) {H' : C ⥤ V} (e : H' ≅ H) :
    DayConvolutionInternalHom F G H' where
  π c j := e.hom.app c ≫ ℌ.π c j
  hπ c i j f := by simp [hπ]
  isLimitWedge c := by
    apply Limits.IsLimit.equivOfNatIsoOfIso (.refl _) _ _ _ (ℌ.isLimitWedge _)
    exact Limits.Wedge.ext (e.symm.app c) (fun j ↦ by
      simp [Limits.Cones.postcompose, Limits.Multifork.ι])
  map_comp_π f j := by simp

section

variable (F G)

/-- If the relevant ends exist, (noncomputably) construct a
functor `C ⥤ V` that is an internal hom of `F` and `G`. -/
@[simps]
noncomputable def ihomOfHasEnds
    [∀ c : C, Limits.HasEnd <|
      dayConvolutionInternalHomDiagramFunctor F |>.obj G |>.obj c] :
    C ⥤ V where
  obj c := Limits.end_ <|
    dayConvolutionInternalHomDiagramFunctor F |>.obj G |>.obj c
  map f := Limits.end_.map <|
    dayConvolutionInternalHomDiagramFunctor F |>.obj G |>.map f

/-- If the relevant ends exist, the functor `ihomOfHasEnds F G` is indeed
an internal hom for Day convolution. -/
@[simps]
noncomputable def dayConvolutionInternalHomOfHasEnds
    [∀ c : C, Limits.HasEnd <|
      dayConvolutionInternalHomDiagramFunctor F |>.obj G |>.obj c] :
    DayConvolutionInternalHom F G (ihomOfHasEnds F G) where
  π c j := Limits.end_.π _ _
  hπ c _ _ φ := Limits.end_.condition _ φ
  isLimitWedge c :=
    Limits.IsLimit.ofIsoLimit (Limits.limit.isLimit _) <|
      Limits.Wedge.ext
        (Iso.refl _)
        (fun j ↦ by dsimp; rw [Category.id_comp]; rfl)
  map_comp_π {c c'} f j := by simp

end

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
        rw [← whiskerLeft_comp_assoc, map_comp_π]
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
    rw [← Limits.Wedge.mk_ι
        (F := dayConvolutionInternalHomDiagramFunctor F|>.obj _|>.obj c)
        (H.obj c) (ℌ.π c) (ℌ.hπ c),
      ← Limits.Wedge.mk_ι
        (F := dayConvolutionInternalHomDiagramFunctor F|>.obj _|>.obj c')
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
  rw [← Limits.Wedge.mk_ι
      (F := dayConvolutionInternalHomDiagramFunctor F|>.obj _|>.obj c)
      (H.obj c) (ℌ.π c) (ℌ.hπ c),
    Limits.Wedge.IsLimit.lift_ι]

lemma coev_naturality_app {G' H' : C ⥤ V} [DayConvolution F G'] (η : G ⟶ G')
    (ℌ' : DayConvolutionInternalHom F (F ⊛ G') H') :
    η ≫ ℌ'.coev_app =
    ℌ.coev_app ≫ ℌ.map (DayConvolution.map (𝟙 _) η) ℌ' := by
  ext c
  dsimp
  apply Limits.Wedge.IsLimit.hom_ext <| ℌ'.isLimitWedge c
  intro j
  apply MonoidalClosed.uncurry_injective
  dsimp
  simp only [Category.assoc, coev_app_comp_π, Functor.comp_obj, tensor_obj,
    map_app_comp_π, coev_app_comp_π_assoc, MonoidalClosed.uncurry_natural_right,
    MonoidalClosed.uncurry_curry, DayConvolution.unit_app_map_app,
    NatTrans.id_app, id_tensorHom]
  simp [MonoidalClosed.uncurry_natural_left]

end coev

theorem left_triangle_components (G : C ⥤ V) [DayConvolution F G]
    (ℌ : DayConvolutionInternalHom F (F ⊛ G) H) [DayConvolution F H] :
    DayConvolution.map (𝟙 F) ℌ.coev_app ≫ ℌ.ev_app = 𝟙 (F ⊛ G) := by
  apply DayConvolution.corepresentableBy F G|>.homEquiv.injective
  dsimp
  ext ⟨x, y⟩
  apply MonoidalClosed.curry_injective
  simp [MonoidalClosed.curry_natural_left]

theorem right_triangle_components (G : C ⥤ V) [DayConvolution F H]
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

/-- When there is a `LawfulDayConvolutionMonoidalCategoryStruct C V D`
instance aroun, a `LawfulDayConvolutionClosedMonoidalCategoryStruct C V D`
bundles the data to define a well-behaved internal hom functor on
the Day convolution monoidal structure on `D`. It bundles the
data part with equations stating that after applying `ι C V D`, one
gets the corresponding objects (internal homs, `DayConvolutionInternalHom`,
co/evaluation morphisms) at the level of functors. -/
class LawfulDayConvolutionClosedMonoidalCategoryStruct
    (C : Type u₁) [Category.{v₁} C] (V : Type u₂) [Category.{v₂} V]
    [MonoidalCategory C] [MonoidalCategory V] [MonoidalClosed V]
    (D : Type u₃) [Category.{v₃} D] [MonoidalCategoryStruct D]
    [LawfulDayConvolutionMonoidalCategoryStruct C V D] where
  /-- The chosen ihom functor at `d : D`. -/
  ihom (C) (V) (d : D) : D ⥤ D
  /-- For every `d d' : D`, `ι C V D|>.obj <| (ihom d).obj d'` is
  indeed a `DayConvolutionInternalHom`. -/
  ihomDayConvolutionInternalHom (C) (V) (d d' : D) :
    DayConvolutionInternalHom
      (ι C V D|>.obj d) (ι C V D|>.obj d') (ι C V D|>.obj <| (ihom d).obj d')
  ι_map_ihom_map (C) (V) (d : D) {d' d'' : D} (f : d' ⟶ d'') :
    (ι C V D|>.map <| (ihom d).map f) =
    (ihomDayConvolutionInternalHom d d').map ((ι C V D).map f)
      (ihomDayConvolutionInternalHom d d'')
  /-- A chosen preimage by `ι` of (a component of) the coevaluation natural
  transformation. -/
  coev_app (C) (V) (d d' : D) : d' ⟶ (ihom d).obj (d ⊗ d')
  /-- A chosen preimage by `ι` of (a component of) the evaluation natural
  transformation. -/
  ev_app (C) (V) (d d' : D) : d ⊗ (ihom d).obj d' ⟶ d'
  ι_map_ev_app (C) (V) d d' :
    letI := convolution C V D d d'
    letI := convolution C V D d ((ihom d).obj d')
    (ι C V D).map (ev_app d d') =
    (ihomDayConvolutionInternalHom d d').ev_app
  ι_map_coev_app (C) (V) d d' :
    letI := convolution C V D d d'
    (ι C V D).map (coev_app d d') =
    (ihomDayConvolutionInternalHom d _).coev_app

namespace LawfulDayConvolutionClosedMonoidalCategoryStruct

variable (C : Type u₁) [Category.{v₁} C] (V : Type u₂) [Category.{v₂} V]
    [MonoidalCategory C] [MonoidalCategory V] [MonoidalClosed V]

section ofHasEnds

variable (D : Type u₃) [Category.{v₃} D] [MonoidalCategoryStruct D]
  [LawfulDayConvolutionMonoidalCategoryStruct C V D]
  [∀ (d d' : D) (c : C),
    Limits.HasEnd <|
      dayConvolutionInternalHomDiagramFunctor (ι C V D |>.obj d) |>.obj
        (ι C V D |>.obj d') |>.obj c]

/-- Given `d d' : D`, this is the functor in `C ⥤ V` that corresponds to the
internal hom of `ι C V D|>.obj d` and `ι C V D|>.obj d'`, if the relevant ends
exist. This is an auxiliary construction to construct internal homs in
`D`. -/
@[simps]
noncomputable def ihom' (d d' : D) : (C ⥤ V) where
  obj c := Limits.end_ <|
    dayConvolutionInternalHomDiagramFunctor (ι C V D|>.obj d) |>.obj
      (ι C V D|>.obj d') |>.obj c
  map {c c'} f := Limits.end_.map <|
    dayConvolutionInternalHomDiagramFunctor (ι C V D|>.obj d) |>.obj
      (ι C V D|>.obj d') |>.map f

/-- Given `d d' : D`, this is the object in `D`_ that corresponds to the
internal hom of `ι C V D|>.obj d` and `ι C V D|>.obj d'` whenever
`ihom' d d'` is in the essential image of ι. -/
noncomputable def ihomObj (d d' : D)
    (h : (ι C V D).essImage (ihom' C V D d d')) : D :=
  h.witness

open DayConvolutionInternalHom

/-- A `DayConvolutionInternalHom` structure on `iHomObj d d'`, obtained
by transporting the "canonical" one for `ihom'` along the isomorphism
`(ι C V D).map (iHomObj d d') ≅ ihom' d d'`. -/
noncomputable def ihomObjDayConvolutionInternalHom (d d' : D)
    (h : (ι C V D).essImage (ihom' C V D d d')) :
    DayConvolutionInternalHom (ι C V D|>.obj d) (ι C V D|>.obj d')
      (ι C V D|>.obj <| ihomObj C V D d d' h) :=
  dayConvolutionInternalHomOfHasEnds _ _|>.transport h.getIso

attribute [local instance] convolution in
/--
Assuming existence of relevant ends, the fact that the essential
image of `ι` contains the relevant objects, and fullness of ι,
noncomputably define a `LawfulDayConvolutionClosedMonoidalCategoryStruct C V D`.
-/
noncomputable def ofHasEnds
    (h : ∀ d d', (ι C V D).essImage (ihom' C V D d d'))
    [(ι C V D).Full] :
    LawfulDayConvolutionClosedMonoidalCategoryStruct C V D where
  ihom d :=
    { obj d' := ihomObj C V D d d' (h d d')
      map {d' d''} f := (ι C V D).preimage <|
        (ihomObjDayConvolutionInternalHom C V D d d' (h d d')).map
          ((ι C V D).map f)
          (ihomObjDayConvolutionInternalHom C V D d d'' (h d d''))
      map_comp f g := by
        apply (ι C V D).map_injective
        simp only [Functor.map_comp, Functor.map_preimage]
        exact map_comp _ _ _ _ _ }
  ihomDayConvolutionInternalHom d d' :=
    ihomObjDayConvolutionInternalHom C V D d d' (h d d')
  coev_app d d' :=
    (ι C V D).preimage <|
      (ihomObjDayConvolutionInternalHom C V D d (d ⊗ d') (h _ _)).coev_app
        (G := (ι C V D).obj d')
  ev_app d d' :=
    (ι C V D).preimage <|
      (ihomObjDayConvolutionInternalHom C V D d d' (h _ _)).ev_app
        (G := (ι C V D).obj d')
  ι_map_ev_app := by simp
  ι_map_coev_app := by simp
  ι_map_ihom_map := by simp

end ofHasEnds

section MonoidalClosed
variable
    (D : Type u₃) [Category.{v₃} D]
    [MonoidalCategoryStruct D]
    [LawfulDayConvolutionMonoidalCategoryStruct C V D]
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

attribute [local instance] convolution in
/-- If we have a `LawfulDayConvolutionMonoidalCategoryStruct C V D` and
the Day convolution monoidal structure on `D` exist, then the data
of a `LawfulDayConvolutionClosedMonoidalCategoryStruct` defines a
`MonoidalClosed` structure on `D`. -/
@[simps! -isSimp]
def monoidalClosed
    [LawfulDayConvolutionClosedMonoidalCategoryStruct C V D] :
    letI := monoidalOfLawfulDayConvolutionMonoidalCategoryStruct C V D
    MonoidalClosed D :=
  letI := monoidalOfLawfulDayConvolutionMonoidalCategoryStruct C V D
  { closed d :=
    { rightAdj := LawfulDayConvolutionClosedMonoidalCategoryStruct.ihom C V d
      adj :=
        { unit :=
            { app d' := coev_app C V d d'
              naturality {d' d''} f := by
                apply (ι C V D).map_injective
                haveI := ihomDayConvolutionInternalHom
                      C V d (d ⊗ d')|>.coev_naturality_app
                    (ι C V D|>.map f)
                    (ihomDayConvolutionInternalHom C V d (d ⊗ d''))
                simp only [Functor.id_obj, Functor.comp_obj,
                  curriedTensor_obj_obj, Functor.id_map, Functor.map_comp,
                  Functor.comp_map, curriedTensor_obj_map]
                rw [ι_map_coev_app, ι_map_coev_app, this, ι_map_ihom_map,
                  ← id_tensorHom, ι_map_tensorHom_hom_eq_tensorHom,
                  Functor.map_id] }
          counit :=
            { app d' := ev_app C V d d'
              naturality {d' d''} f := by
                apply (ι C V D).map_injective
                haveI := ihomDayConvolutionInternalHom
                    C V d d'|>.ev_naturality_app
                  (ihomDayConvolutionInternalHom C V d d'')
                  (ι C V D|>.map f)
                simp only [Functor.id_obj, Functor.comp_obj,
                  curriedTensor_obj_obj, Functor.id_map, Functor.map_comp,
                  Functor.comp_map, curriedTensor_obj_map]
                rw [ι_map_ev_app, ι_map_ev_app, ← this,
                  ← id_tensorHom, ι_map_tensorHom_hom_eq_tensorHom,
                  Functor.map_id, ι_map_ihom_map] }
          left_triangle_components d' := by
            dsimp
            apply (ι C V D).map_injective
            rw [Functor.map_comp, ← id_tensorHom,
              ι_map_tensorHom_hom_eq_tensorHom, Functor.map_id, Functor.map_id,
              ι_map_coev_app, ι_map_ev_app]
            exact ihomDayConvolutionInternalHom
                C V d (d ⊗ d')|>.left_triangle_components (ι C V D|>.obj d')
          right_triangle_components d' := by
            dsimp
            apply (ι C V D).map_injective
            rw [Functor.map_comp, ι_map_coev_app, Functor.map_id,
              ι_map_ihom_map, ι_map_ev_app]
            exact ihomDayConvolutionInternalHom
                C V d d'|>.right_triangle_components
              (ι C V D|>.obj d')
              (ihomDayConvolutionInternalHom C V d (d ⊗ _)) } } }

end MonoidalClosed

end LawfulDayConvolutionClosedMonoidalCategoryStruct

end

end CategoryTheory.MonoidalCategory
