/-
Copyright (c) 2026 Yannis Monbru-Carcelero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yannis Monbru Carcelero
-/
module

public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompleteLattice.MulticoequalizerDiagram
public import Mathlib.Topology.Sets.BaseChangeNhds
public import Mathlib.Topology.Sheaves.Presheaf


/-!
# KPresheaves on a topological space

We define `TopCat.KPresheaf A X` simply as `(Compacts X)ᵒᵖ ⥤ A`,
and inherit the category structure with natural transformations as morphisms.

We define construction that will allow to state the condition of being a K-sheaf.

We also define the pushforward of a presheaf by a proper map

-/
@[expose] public section

universe w v u

open Topology CategoryTheory TopologicalSpace Opposite Limits Compacts

variable {A : Type u} [Category.{v} A] {X : TopCat.{w}}

namespace TopCat

variable (A X) in
/-- The category of `A`-valued K-presheaves on a (bundled) topological space `X` -/
abbrev KPresheaf : Type max u v w := (Compacts X)ᵒᵖ ⥤ A

namespace KPresheaf

/-- If `P` is a K-presheaf, and `K` a compact subset then `P.obj (op K)` is equipped with a
structure of cocone over the diagram defined by the `P.obj (op L)` for `L` a compact
neighbourhood of `K` -/
@[simps, implicit_reducible]
def coconeOfCompacts (P : KPresheaf A X) (K : Compacts X) :
    Cocone ((Set.mono_coe K.compactNhds).functor.op ⋙ P) where
  pt := P.obj (op K)
  ι.app K' := P.map <| opHomOfLE (Compacts.subset_of_mem_compactNhds K'.unop.prop)
  ι.naturality _ _ _ := by
    dsimp
    rw [← P.map_comp, Category.comp_id]
    rfl

/-- For `P` a K-presheaf, and `K` a compact subset then `P.obj (op K)` is equipped with a
structure of cocone over the diagram defined by the `P.obj (op (closure (U : Set X))`
for `U` an open neighbourhood of `K` -/
@[simps!, implicit_reducible]
def coconeOfClosureOfOpens (P : KPresheaf A X) (K : Compacts X) :=
  Cocone.whisker K.openRcNhdsToCompactNhds_mono.functor.op <| P.coconeOfCompacts K

variable [T2Space X]

/-- For `K` a compact and `P` a K-presheaf verifying the third axiom of K-sheaves, this is
a recipe to build maps from `P.obj (op K)` by only using the open relatively
compact neighbourhoods and not all the compacts neighbourhoods. -/
@[no_expose]
noncomputable def descOfOpenClosure (P : KPresheaf A X) (K : Compacts X)
    (h : (IsColimit (P.coconeOfCompacts K))) {Z : A}
    (ι : K.openRcNhdsToCompactNhds_mono.functor.op ⋙ (Set.mono_coe _).functor.op ⋙ P ⟶
      (Functor.const _).obj Z) :
    P.obj (op K) ⟶ Z :=
  ((Functor.Final.isColimitWhiskerEquiv
    K.openRcNhdsToCompactNhds_mono.functor.op _).symm h).desc (Cocone.mk _ ι)

@[reassoc (attr := simp)]
lemma map_comp_descOfOpenClosure (P : KPresheaf A X) {K : Compacts X} (V : K.openRcNhds)
    (h : (IsColimit (P.coconeOfCompacts K))) {Z : A}
    (ι : K.openRcNhdsToCompactNhds_mono.functor.op ⋙ (Set.mono_coe _).functor.op ⋙ P ⟶
      (Functor.const _).obj Z) :
    dsimp% P.map (op (homOfLE (V.property.2.trans subset_closure))) ≫ P.descOfOpenClosure K h ι =
      ι.app (op V) :=
  ((Functor.Final.isColimitWhiskerEquiv
    K.openRcNhdsToCompactNhds_mono.functor.op _).symm h).fac (Cocone.mk _ ι) (op V)

@[ext]
lemma hom_ext_of_isColimit_coconeOfCompacts (P : KPresheaf A X) {K : Compacts X}
    (h : IsColimit (P.coconeOfCompacts K))
    {W : A} {f f' : P.obj (op K) ⟶ W}
    (w : ∀ V, dsimp% (P.coconeOfClosureOfOpens K).ι.app V ≫ f =
      (P.coconeOfClosureOfOpens K).ι.app V ≫ f') :
    f = f' :=
  ((Functor.Final.isColimitWhiskerEquiv K.openRcNhdsToCompactNhds_mono.functor.op
    _).symm h).hom_ext w

/-- The pushforward by a proper map as a functor over K-presheaves -/
@[simps!, implicit_reducible]
def pushforward {Y : TopCat.{w}} (f : X ⟶ Y) (pf : IsProperMap f) :
    KPresheaf A X ⥤ KPresheaf A Y :=
  (Functor.whiskeringLeft _ _ _).obj (Compacts.properPreimage_mono pf).functor.op

end KPresheaf

noncomputable section

namespace Presheaf

/- TODO: replace HasCoimitsOfSize by HasFilteredColimitsOfSize, but it breaks things below-/

variable [HasColimitsOfSize.{w, w} A] (F : Presheaf A X) {K : Compacts X}

variable (K) in
/-- The `.obj` component of `TopCat.Presheaf.toKPresheafFunctorObj` -/
def toKPresheafFunctorObjObj : A := colimit ((Set.mono_coe K.openNhds).functor.op ⋙ F)

/-- The canonical map from a value of the presheaf over an open subset to a value of it's
  coresponding Kpresheaf -/
def ιToKPresheafFunctorObjObj (U : (K.openNhds)) :
    F.obj (op U.val) ⟶ F.toKPresheafFunctorObjObj K :=
  colimit.ι ((Set.mono_coe K.openNhds).functor.op ⋙ F) _

@[reassoc (attr := simp)]
lemma toKPresheafFunctorObjObj_w {U V : (K.openNhds)} (i : op U ⟶ op V) :
    F.map i ≫ F.ιToKPresheafFunctorObjObj V = F.ιToKPresheafFunctorObjObj U :=
  colimit.w ((Set.mono_coe K.openNhds).functor.op ⋙ F) i

variable (K) in
/-- The cocone structure of `F.toKPresheafFunctorObjObj K` over all values of opens subset
that contains `K` -/
@[simps, implicit_reducible]
def toKPresheafFunctorObjObjCocone : Cocone ((Set.mono_coe K.openNhds).functor.op ⋙ F) where
 pt := F.toKPresheafFunctorObjObj K
 ι.app U := ιToKPresheafFunctorObjObj F U.unop

variable (K) in
/-- The evidence that `F.toKPresheafFunctorObjObjCocone` is a colimit cocone -/
def isColimitToKPresheafFunctorObjObjCocone : IsColimit (toKPresheafFunctorObjObjCocone F K) :=
  colimit.isColimit _

variable {F} in
@[ext]
lemma toKPresheafFunctorObjObj_hom_ext {Y : A} (f g : F.toKPresheafFunctorObjObj K ⟶ Y)
    (h : ∀ U : K.openNhds, F.ιToKPresheafFunctorObjObj U ≫ f = F.ιToKPresheafFunctorObjObj U ≫ g) :
    f = g :=
  (F.isColimitToKPresheafFunctorObjObjCocone K).hom_ext (fun _ ↦ h _)

@[reassoc (attr := simp)]
lemma toKPresheafFunctorObjObj_ι_desc {K : Compacts X}
    (c : Cocone <| (Set.mono_coe K.openNhds).functor.op ⋙ F) (U : K.openNhds) :
    F.ιToKPresheafFunctorObjObj U ≫ (isColimitToKPresheafFunctorObjObjCocone F K).desc c =
    c.ι.app (op U) :=
  colimit.ι_desc c (op U)

/-- The canonical map from a value of the presheaf over an open subset relatively compact to a
value of it's coresponding Kpresheaf -/
def ιToKPresheafFunctorObjObjRc (U : (K.openRcNhds)) :
    F.obj (op U.val) ⟶ F.toKPresheafFunctorObjObj K :=
  F.ιToKPresheafFunctorObjObj (K.openRcNhdsToOpenNhds_mono.functor.obj U)

@[reassoc (attr := simp)]
lemma toKPresheafFunctorObjObjRc_w {U V : (K.openRcNhds)} (i : op U ⟶ op V) :
    F.map i ≫ F.ιToKPresheafFunctorObjObjRc V = F.ιToKPresheafFunctorObjObjRc U :=
  F.toKPresheafFunctorObjObj_w <| op (K.openRcNhdsToOpenNhds_mono.functor.map i.unop)

variable (K) in
/-- The cocone structure of `F.toKPresheafFunctorObjObj K` over all values of opens subset
 relatively compact that contains `K` -/
@[simps, implicit_reducible]
def toKPresheafFunctorObjObjRcCocone : Cocone ((Set.mono_coe K.openRcNhds).functor.op ⋙ F) where
  pt := toKPresheafFunctorObjObj F K
  ι.app U := ιToKPresheafFunctorObjObjRc F U.unop

variable (K) in
/-- The evidence that `F.toKPresheafFunctorObjObjRcCocone` is a colimit cocone -/
def isColimitToKPresheafFunctorObjObjRcCocone [T2Space X] [LocallyCompactSpace X] :
    IsColimit (toKPresheafFunctorObjObjRcCocone F K) :=
  (Functor.Final.isColimitWhiskerEquiv (K.openRcNhdsToOpenNhds_mono.functor.op) _).invFun
  (isColimitToKPresheafFunctorObjObjCocone _ _)

variable {F} in
@[ext]
lemma toKPresheafFunctorObjObjRC_hom_ext [T2Space X] [LocallyCompactSpace X] {Y : A}
    (f g : F.toKPresheafFunctorObjObj K ⟶ Y)
    (h : ∀ U : K.openRcNhds, F.ιToKPresheafFunctorObjObjRc U ≫ f =
    F.ιToKPresheafFunctorObjObjRc U ≫ g) : f = g :=
  (isColimitToKPresheafFunctorObjObjRcCocone F K).hom_ext (fun _ ↦ h _)

@[reassoc (attr := simp)]
lemma toKPresheafFunctorObjObjRc_ι_desc [T2Space X] [LocallyCompactSpace X] {K : Compacts X}
    (c : Cocone <| (Set.mono_coe K.openRcNhds).functor.op ⋙ F) (U : K.openRcNhds) :
    F.ιToKPresheafFunctorObjObjRc U ≫ (isColimitToKPresheafFunctorObjObjRcCocone F K).desc c =
    c.ι.app (op U) :=
  (isColimitToKPresheafFunctorObjObjRcCocone F K).fac _ _

/-- The `.map` component of `TopCat.Presheaf.toKPresheafFunctorObj` -/
def toKPresheafFunctorObjMap {K L : Compacts X} (i : K ⟶ L) :
    F.toKPresheafFunctorObjObj L ⟶ F.toKPresheafFunctorObjObj K :=
  colimit.pre ((Set.mono_coe K.openNhds).functor.op ⋙ F) (baseChangeOpenNhds_mono i).functor.op

@[reassoc (attr := simp)]
lemma ι_toKPresheafFunctorObjMap {K L : Compacts X} (i : K ⟶ L) (U : L.openNhds) :
    F.ιToKPresheafFunctorObjObj U ≫ F.toKPresheafFunctorObjMap i =
    F.ιToKPresheafFunctorObjObj ((baseChangeOpenNhds_mono i).functor.obj U) :=
  colimit.ι_pre ((Set.mono_coe K.openNhds).functor.op ⋙ F)
  (baseChangeOpenNhds_mono i).functor.op _

/-- The KPresheaf associated to a Presheaf -/
@[simps, implicit_reducible]
def toKPresheafFunctorObj (F : Presheaf A X) : KPresheaf A X where
  obj K := F.toKPresheafFunctorObjObj (K.unop)
  map i := F.toKPresheafFunctorObjMap i.unop
  map_comp {K L M} f g := by
    ext U
    simp
    suffices F.ιToKPresheafFunctorObjObj (baseChangeOpenNhds (g.unop ≫ f.unop) U) =  F.ιToKPresheafFunctorObjObj (baseChangeOpenNhds g.unop (baseChangeOpenNhds f.unop U)) by
      rw [this]

      sorry

    rfl
    sorry

variable {F} in
@[ext]
lemma toKPresheafFunctorObjObj_hom_ext' {Y : A} {K : (Compacts X)ᵒᵖ}
    (f g : F.toKPresheafFunctorObj.obj K ⟶ Y)
    (h : ∀ U : K.unop.openNhds, F.ιToKPresheafFunctorObjObj U ≫ f =
      F.ιToKPresheafFunctorObjObj U ≫ g) :
    f = g :=
  toKPresheafFunctorObjObj_hom_ext _ _ h

@[simp]
lemma toKPresheafFunctorObjMap_comp {K L M : Compacts X} (i : K ⟶ L) (j : L ⟶ M) :
    F.toKPresheafFunctorObjMap (i ≫ j) = F.toKPresheafFunctorObjMap j ≫
    F.toKPresheafFunctorObjMap i :=
  F.toKPresheafFunctorObj.map_comp _ _

/-- The `.app` component of `TopCat.Presheaf.toKPresheafFunctorMap` -/
def toKPresheafFunctorMapApp {F1 F2 : Presheaf A X} (τ : F1 ⟶ F2) (K : Compacts X) :
    F1.toKPresheafFunctorObjObj K ⟶ F2.toKPresheafFunctorObjObj K :=
  colimMap <| Functor.whiskerLeft _ τ

@[reassoc (attr := simp)]
lemma ι_toKPresheafFunctorMapApp {F1 F2 : Presheaf A X} (τ : F1 ⟶ F2) {K : Compacts X}
    (U : K.openNhds) : F1.ιToKPresheafFunctorObjObj U ≫ toKPresheafFunctorMapApp τ K =
    τ.app (op U.val) ≫ F2.ιToKPresheafFunctorObjObj U :=
  Limits.ι_colimMap _ _

attribute [local simp] baseChangeOpenNhds in
/-- The natural transformation between KPresheaves induced by a
natural transformation between their coresponding presheaves -/
@[simps]
def toKPresheafFunctorMap {F1 F2 : Presheaf A X} (τ : F1 ⟶ F2) :
    F1.toKPresheafFunctorObj ⟶ F2.toKPresheafFunctorObj where
  app K := toKPresheafFunctorMapApp τ K.unop

/-- The functor sending Presheaves into Kpresheaves -/
@[simps, implicit_reducible]
def toKPresheafFunctor : Presheaf A X ⥤ KPresheaf A X where
  obj := toKPresheafFunctorObj
  map := toKPresheafFunctorMap
  map_id := sorry
  map_comp := sorry

variable {F} in
@[ext]
lemma toKPresheafFunctorObjObj_hom_ext'' {Y : A} {K : (Compacts X)ᵒᵖ}
    (f g : (toKPresheafFunctor.obj F).obj K ⟶ Y)
    (h : ∀ U : K.unop.openNhds, F.ιToKPresheafFunctorObjObj U ≫ f =
      F.ιToKPresheafFunctorObjObj U ≫ g) :
    f = g :=
  toKPresheafFunctorObjObj_hom_ext _ _ h

end Presheaf

namespace KPresheaf

open Opens

/- TODO: replace HasLimitsOfSize by HasCofilteredLimitsOfSize, but it breaks thing below-/

variable [HasLimitsOfSize.{w, w} A] (G : KPresheaf A X) {U : Opens X}

variable (U) in
/-- The `.obj` component of `TopCat.KPresheaf.toPresheafFunctorObj` -/
def toPresheafFunctorObjObj (U : Opens X) : A :=
  limit ((Set.mono_coe U.compactsInside).functor.op ⋙ G)

/-- The canonical map to a value of the Kpresheaf over a compact subset to a value of it's
coresponding Presheaf -/
def πToPresheafFunctorObjObj (K : U.compactsInside) :
    G.toPresheafFunctorObjObj U ⟶ G.obj (op K.val) :=
  limit.π ((Set.mono_coe U.compactsInside).functor.op ⋙ G) _

@[reassoc (attr := simp)]
lemma toPresheafFunctorObjObj_w {K L : U.compactsInside} (i : op K ⟶ op L) :
    G.πToPresheafFunctorObjObj K ≫ G.map i = G.πToPresheafFunctorObjObj L := limit.w _ i

variable (U) in
/-- The cone structure of `G.toPresheafFunctorObjObj U` over all values of compacts subset
inside `U` -/
@[simp, implicit_reducible]
def toPresheafFunctorObjObjCone : Cone ((Set.mono_coe U.compactsInside).functor.op ⋙ G) where
  pt := G.toPresheafFunctorObjObj U
  π.app U := πToPresheafFunctorObjObj G U.unop

variable (U) in
/-- The evidence that `G.toPresheafFunctorObjObjCone` is a limit cone. -/
def isLimitToPresheafFunctorObjObjCone : IsLimit (toPresheafFunctorObjObjCone G U) :=
  limit.isLimit _

variable {G} in
@[ext]
lemma toPresheafFunctorObjObj_hom_ext {Y : A} (f g : Y ⟶ G.toPresheafFunctorObjObj U)
    (h : ∀ K : U.compactsInside, (f ≫ G.πToPresheafFunctorObjObj K =
    g ≫ G.πToPresheafFunctorObjObj K)) : f = g :=
  (G.isLimitToPresheafFunctorObjObjCone _ ).hom_ext (fun _ ↦ h _)

@[reassoc (attr := simp)]
lemma toPresheafFunctorObjObj_lift_π {U : Opens X}
    (c : Cone <| (Set.mono_coe U.compactsInside).functor.op ⋙ G) (K : U.compactsInside) :
    (G.isLimitToPresheafFunctorObjObjCone _ ).lift c ≫ G.πToPresheafFunctorObjObj K =
  c.π.app (op K) := limit.lift_π c (op K)

/-- The `.map` component of `TopCat.KPresheaf.toPresheafFunctorObj` -/
def toPresheafFunctorObjMap {U V : Opens X} (i : U ⟶ V) :
    G.toPresheafFunctorObjObj V ⟶ G.toPresheafFunctorObjObj U :=
  limit.pre ((Set.mono_coe V.compactsInside).functor.op ⋙ G)
  (baseChangeCompactsInside_mono i).functor.op

@[reassoc (attr := simp)]
lemma toPresheafFunctorObjMap_π {U V : Opens X} (i : U ⟶ V) (K : U.compactsInside) :
    G.toPresheafFunctorObjMap i ≫ G.πToPresheafFunctorObjObj K =
    G.πToPresheafFunctorObjObj ((baseChangeCompactsInside_mono i).functor.obj K) :=
  limit.pre_π _ (baseChangeCompactsInside_mono i).functor.op (op K)

/-- The presheaf associated to a Kpresheaf -/
@[simps, implicit_reducible]
def toPresheafFunctorObj (G : KPresheaf A X) : Presheaf A X where
  obj U := G.toPresheafFunctorObjObj U.unop
  map i := G.toPresheafFunctorObjMap i.unop
  map_comp := sorry


variable {G} in
@[ext]
lemma toPresheafFunctorObjObj_hom_ext' {Y : A} {U : (Opens X)ᵒᵖ}
    (f g : Y ⟶ G.toPresheafFunctorObj.obj U)
    (h : ∀ K : U.unop.compactsInside, (f ≫ G.πToPresheafFunctorObjObj K =
    g ≫ G.πToPresheafFunctorObjObj K)) : f = g :=
  toPresheafFunctorObjObj_hom_ext _ _ h

/-- The `.app` component of `TopCat.KPresheaf.toPresheafFunctorMap` -/
def toPresheafFunctorMapApp {G1 G2 : KPresheaf A X} (σ : G1 ⟶ G2) (U : Opens X) :
    G1.toPresheafFunctorObjObj U ⟶ G2.toPresheafFunctorObjObj U :=
  limMap <| Functor.whiskerLeft _ σ

@[reassoc (attr := simp)]
lemma toPresheafFunctorMapApp_π {G1 G2 : KPresheaf A X} (σ : G1 ⟶ G2) {U : Opens X}
    (K : U.compactsInside) : toPresheafFunctorMapApp σ U ≫ G2.πToPresheafFunctorObjObj K =
    G1.πToPresheafFunctorObjObj K ≫ σ.app (op K.val) := limMap_π _ (op K)

/-- The natural transformation between presheaves induced by a natural transformation between
their coresponding Kpresheaves -/
@[simps]
def toPresheafFunctorMap {G1 G2 : KPresheaf A X} (σ : G1 ⟶ G2) :
    G1.toPresheafFunctorObj ⟶ G2.toPresheafFunctorObj where
  app U := toPresheafFunctorMapApp σ U.unop
  naturality := sorry

@[simp]
lemma toPresheafFunctorMapId {G : KPresheaf A X} : toPresheafFunctorMap (𝟙 G) = 𝟙 _:= by
  aesop

/-- The functor sending Kpresheaves into presheaves -/
@[simps, implicit_reducible]
def toPresheafFunctor : KPresheaf A X ⥤ Presheaf A X where
  obj := toPresheafFunctorObj
  map := toPresheafFunctorMap

variable {G} in
@[ext]
lemma toPresheafFunctorObjObj_hom_ext'' {Y : A} {U : (Opens X)ᵒᵖ}
    (f g : Y ⟶ (toPresheafFunctor.obj G).obj U)
    (h : ∀ K : U.unop.compactsInside, (f ≫ G.πToPresheafFunctorObjObj K =
    g ≫ G.πToPresheafFunctorObjObj K)) : f = g :=
  toPresheafFunctorObjObj_hom_ext _ _ h

end KPresheaf

namespace KPresheaf

variable [HasColimitsOfSize.{w, w} A] [HasLimitsOfSize.{w, w} A]

open TopCat Presheaf Compacts Opens

namespace adjunction

variable {F : Presheaf A X} {G : KPresheaf A X} (τ : (toKPresheafFunctor).obj F ⟶ G)
  (σ : F ⟶ (KPresheaf.toPresheafFunctor).obj G) (K : Compacts X) (U : Opens X)

/-- The Cone to buid `KPresheaf.adjunction.homEquivToFunhomEquivToFun` -/
@[simps, implicit_reducible]
def homEquivToFunCone : Cone <| (Set.mono_coe U.compactsInside).functor.op ⋙ G where
  pt := F.obj (op U)
  π.app K := F.ιToKPresheafFunctorObjObj (openNhdsOfCompactsInside K.unop) ≫ τ.app (op K.unop.val)
  π.naturality {_ _} _:= by
    simp [← τ.naturality]
    rfl

/-- The function from `F.toKPresheafFunctorObj ⟶ G` to `F ⟶ G.toPresheafFunctorObj` -/
@[simps]
def homEquivToFun : F ⟶ toPresheafFunctor.obj G where
 app U := (G.isLimitToPresheafFunctorObjObjCone U.unop).lift (homEquivToFunCone τ U.unop)
 naturality {U V} i := by
  ext K
  simpa [baseChangeCompactsInside] using toKPresheafFunctorObjObj_w_assoc _ (show
    op (openNhdsOfCompactsInside (baseChangeCompactsInside i.unop K)) ⟶
    op (openNhdsOfCompactsInside K) from i) _

/-- The Cocone to build `KPresheaf.adjunction.homEquivInvFunhomEquivToFun` -/
@[simps, implicit_reducible]
def homEquivInvFunCocone : Cocone <| (Set.mono_coe K.openNhds).functor.op ⋙ F where
  pt := G.obj (op K)
  ι.app U := σ.app _ ≫ G.πToPresheafFunctorObjObj (compactsInsideOfOpenNhds U.unop)

/-- The function from `F ⟶ G.toPresheafFunctorObj` to `F.toKPresheafFunctorObj ⟶ G` -/
@[simps]
def homEquivInvFun : toKPresheafFunctor.obj F ⟶ G where
 app K := (F.isColimitToKPresheafFunctorObjObjCocone K.unop).desc (homEquivInvFunCocone σ _)
 naturality {K L} i := by--ça on doit pouvoir arriver à faire en sorte qu'il le fasse tout seul
  ext U
  simpa [baseChangeOpenNhds] using whisker_eq _ (toPresheafFunctorObjObj_w G (show
  op (compactsInsideOfOpenNhds U) ⟶
  op (compactsInsideOfOpenNhds (baseChangeOpenNhds i.unop U)) from i)).symm

variable (F) in
/-- The bijection between `F.toKPresheafFunctorObj ⟶ G` to `F ⟶ G.toPresheafFunctorObj` -/
def homEquiv : (toKPresheafFunctor.obj F ⟶ G) ≃ (F ⟶ toPresheafFunctor.obj G) where
 toFun := homEquivToFun
 invFun := homEquivInvFun
 left_inv _ := by aesop
 right_inv _ := by aesop

attribute [local simp] homEquiv in
/-- The data necessary to build the adjunction between `toKPresheafFunctor` and
`toPresheafFunctor` -/
def coreHomEquiv :
    Adjunction.CoreHomEquiv (toKPresheafFunctor (A := A) (X := X)) toPresheafFunctor where
  homEquiv := homEquiv

end adjunction

/-- The adjunction between `toKpresheafFunctor` and `toPresheafFunctor` -/
def adjunction : (toKPresheafFunctor (A := A) (X := X)) ⊣ (toPresheafFunctor ) :=
  Adjunction.mkOfHomEquiv adjunction.coreHomEquiv

attribute [local simp] adjunction adjunction.coreHomEquiv adjunction.homEquiv in
@[simp]
lemma adjunctionUnitEq (F : Presheaf A X) (U : (Opens X)ᵒᵖ) (K : U.unop.compactsInside) :
    (adjunction.unit.app F).app U ≫ (toKPresheafFunctor.obj F).πToPresheafFunctorObjObj K =
    F.ιToKPresheafFunctorObjObj (openNhdsOfCompactsInside K):= by
  aesop

attribute [local simp] adjunction adjunction.coreHomEquiv adjunction.homEquiv in
@[simp]
lemma adjunctionCounitEq (G : KPresheaf A X) (K : (Compacts X)ᵒᵖ) (U : K.unop.openNhds) :
    (toPresheafFunctor.obj G).ιToKPresheafFunctorObjObj U ≫ (adjunction.counit.app G).app K =
    G.πToPresheafFunctorObjObj (compactsInsideOfOpenNhds U):= by
  aesop

/-@[simps, implicit_reducible]
def adjunctionUnitCone (F : Presheaf A X) (U : (Opens X)ᵒᵖ) :
    Cone ((Set.mono_coe U.unop.compactsInside).functor.op ⋙ (toKPresheafFunctorObj F)) where
  pt := F.obj U
  π.app K := F.ιToKPresheafFunctorObjObj (openNhdsOfCompactsInside K.unop)


@[simps]
def adjunctionUnit' : 𝟭 (Presheaf A X) ⟶ toKPresheafFunctor ⋙ toPresheafFunctor where
  app F := ⟨ fun U =>
    (isLimitToPresheafFunctorObjObjCone (toKPresheafFunctorObj F) (unop U)).lift
      (adjunctionUnitCone F U)
    , by
    intro U V i
    dsimp
    ext
    simpa [openNhdsOfCompactsInside] using
      toKPresheafFunctorObjObj_w F (show (op ⟨unop U, _⟩ ⟶ op ⟨unop V, _⟩ ) from i)
    ⟩



attribute [local simp] adjunction adjunction.coreHomEquiv adjunction.homEquiv in
@[simp]
lemma adjunctionUnitEq' : (adjunction (A:= A) (X := X)).unit = adjunctionUnit' := by
  aesop

@[simps]
def adjunctionCounit' :  toPresheafFunctor ⋙ toKPresheafFunctor ⟶  𝟭 (KPresheaf A X) where
  app F := ⟨ fun K =>
    (isColimitToKPresheafFunctorObjObjCocone (toPresheafFunctorObj F) (unop K)).desc ⟨F.obj K,⟨fun U
      => F.πToPresheafFunctorObjObj (compactsInsideOfOpenNhds U.unop),by aesop⟩⟩
    , by
    intro K L i
    dsimp
    ext
    simpa [compactsInsideOfOpenNhds] using
      (toPresheafFunctorObjObj_w F (show (op ⟨unop K, _⟩ ⟶ op ⟨unop L, _⟩ ) from i)).symm
    ⟩

attribute [local simp] adjunction adjunction.coreHomEquiv adjunction.homEquiv in
@[simp]
lemma adjunctionUCouitEq : (adjunction (A:= A) (X := X)).counit = adjunctionCounit' := by
  aesop-/

end KPresheaf

end

end TopCat

end TopCat
