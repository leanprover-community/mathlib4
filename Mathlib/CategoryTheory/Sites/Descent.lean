/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Sites.ObjectsCoverTop
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.InducedTopology

/-! Descent of sheaves

By definition, if `F` is a sheaf of types, we know that sections of `F` can be glued.
The construction of `SheafHom` (see the file `CategoryTheory.Sites.SheafHom`) show
that morphisms of sheaves can be glued. In this file, we shall show that sheaves
may also be glued (TODO).

More precisely, given a site `(C, J)` and a family of objects `Y : I → C`
such that `hY : J.ObjectsCoverTop Y`, we construct a category `hY.SheafDescentData A`
(for any category `A`) which consists of families of sheaves `sheaf i : Sheaf (J.over (Y i)) A`
on `Y i` for all `i` that are equipped with a descent data: this data makes it
reasonable to expect that there exists a sheaf `F` on `(C, J)` (well defined up
to a unique isomorphism) such that each `sheaf i` is canonically isomorphic to
the pullback of `F`: if it is so, then for any `X` in `C` with two maps `f₁ : X ⟶ Y i₁`
and `f₂ : X ⟶ Y i₂`, the pullback on `X` of `sheaf i₁` and `sheaf i₂` must be isomorphic.
This data is encoded in the `iso` field of `SheafDescentData`, and compatibilites
are stated as `pullback_iso` and `iso_trans`. In case `C` has suitable binary products,
it is clear from the `pullback_iso` condition that it suffices to define the `iso`
field on the binary products `Y i₁ ⨯ Y i₂`, and then, the transitivity condition `iso_trans`
can be formulated using ternary products (TODO: define such a constructor).

Currently, the main result is that the obvious functor
`hY.sheafToDescentData A : Sheaf J A ⥤ hY.SheafDescentData A` is fully faithful:
this can be understood as the descent of morphisms of sheaves. When we are
able to show that this functor is essentially surjective, we may say that the descent
is effective: this should require that suitable limits exists in `A`, and this
should be a consequence of the results in `Sites.DenseSubsite` (TODO).

More concretely, in the case of topological space `X` and an open covering `i ↦ Y i`,
the effectiveness of the descent of sheaves means that if we have sheaves
`F i` on each `Y i`, and isomorphisms between the restrictions
of `F i` and `F j` on the intersections of `Y i` and `Y j` which satisfy certain
compatibilites, then the sheaves `F i` can be glued in order to obtain a sheaf on `X`
whose restriction of `Y i` identifies to `F i`, in a way that is compatible
with the given isomorphisms.

* Giraud, Jean, Mémoires de la Société Mathématique de France, no. 2 (1964) , 156 p.

-/

universe v' v u' u

namespace CategoryTheory

open Category

namespace GrothendieckTopology

namespace ObjectsCoverTop

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {I : Type*} {Y : I → C}

/-- Given a site `(C, J)` and family of objects `Y : I → C` which cover the final object,
this is the type of families of sheaves over the `Y i` that are equipped
with a descent data. When the descent is effective, this category
is equivalent to `Sheaf J A` (TODO) -/
structure SheafDescentData (hY : J.ObjectsCoverTop Y)
    (A : Type u') [Category.{v'} A] where
  /-- a sheaf on `J.over (Y i)` -/
  sheaf (i : I) : Sheaf (J.over (Y i)) A
  /-- the descent data -/
  iso ⦃X : C⦄ ⦃i₁ i₂ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) :
    (J.overMapPullback A f₁).obj (sheaf i₁) ≅
      (J.overMapPullback A f₂).obj (sheaf i₂)
  /-- the given isomorphism satisfy a compatibility with precomposition -/
  pullback_iso ⦃X X' : C⦄ (g : X' ⟶ X) ⦃i₁ i₂ : I⦄
      (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) :
      iso (g ≫ f₁) (g ≫ f₂) = (J.overMapPullbackComp A g f₁).symm.app _ ≪≫
        (J.overMapPullback A g).mapIso (iso f₁ f₂) ≪≫
        (J.overMapPullbackComp A g f₂).app _ := by aesop_cat
  /-- the "cocycle" relation of the descent data -/
  iso_trans ⦃X : C⦄ ⦃i₁ i₂ i₃ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) (f₃ : X ⟶ Y i₃) :
    iso f₁ f₂ ≪≫ iso f₂ f₃ = iso f₁ f₃ := by aesop_cat

namespace SheafDescentData

variable {hY : J.ObjectsCoverTop Y} {A : Type u'} [Category.{v'} A]
    (D D₁ D₂ D₃ : hY.SheafDescentData A)

attribute [simp] iso_trans

@[reassoc (attr := simp)]
lemma iso_trans_hom ⦃X : C⦄ ⦃i₁ i₂ i₃ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) (f₃ : X ⟶ Y i₃) :
    (D.iso f₁ f₂).hom ≫ (D.iso f₂ f₃).hom = (D.iso f₁ f₃).hom := by
  rw [← Iso.trans_hom, D.iso_trans]

@[reassoc (attr := simp)]
lemma iso_trans_inv ⦃X : C⦄ ⦃i₁ i₂ i₃ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) (f₃ : X ⟶ Y i₃) :
    (D.iso f₂ f₃).inv ≫ (D.iso f₁ f₂).inv = (D.iso f₁ f₃).inv := by
  rw [← Iso.trans_inv, D.iso_trans]

lemma iso_refl_hom ⦃X : C⦄ ⦃i : I⦄ (f : X ⟶ Y i) :
    (D.iso f f).hom = 𝟙 _ := by
  rw [← cancel_mono (D.iso f f).hom, iso_trans_hom, id_comp]

@[simp 1000]
lemma iso_refl ⦃X : C⦄ ⦃i : I⦄ (f : X ⟶ Y i) :
    D.iso f f = Iso.refl _ := by
  ext1
  rw [iso_refl_hom, Iso.refl_hom]

lemma iso_refl_inv ⦃X : C⦄ ⦃i : I⦄ (f : X ⟶ Y i) :
    (D.iso f f).inv = 𝟙 _ := by simp

lemma iso_inv ⦃X : C⦄ ⦃i₁ i₂ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) :
    (D.iso f₁ f₂).inv = (D.iso f₂ f₁).hom := by
  rw [← cancel_mono (D.iso f₁ f₂).hom, Iso.inv_hom_id, iso_trans_hom, iso_refl, Iso.refl_hom]

lemma iso_symm ⦃X : C⦄ ⦃i₁ i₂ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) :
    (D.iso f₁ f₂).symm = D.iso f₂ f₁ := by
  ext1
  rw [Iso.symm_hom, iso_inv]

def isoSections ⦃X : C⦄ ⦃i₁ i₂ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) :
    (D.sheaf i₁).1.obj (Opposite.op (Over.mk f₁)) ≅
      (D.sheaf i₂).1.obj (Opposite.op (Over.mk f₂)) :=
  (overMapPullbackSectionsIso J A f₁ (Over.mk (𝟙 _)) (Over.mk f₁)
    (Over.isoMk (Iso.refl _))).symm.app (D.sheaf i₁) ≪≫
    ((sheafSections (J.over X) A).obj (Opposite.op (Over.mk (𝟙 X)))).mapIso (D.iso f₁ f₂) ≪≫
    (overMapPullbackSectionsIso J A f₂ (Over.mk (𝟙 _)) (Over.mk f₂)
      (Over.isoMk (Iso.refl _))).app (D.sheaf i₂)

/-- The type of morphisms between families of sheaves equipped with a descent data. -/
@[ext]
structure Hom where
  /-- a family of morphisms of sheaves  -/
  hom (i : I) : D₁.sheaf i ⟶ D₂.sheaf i
  comm ⦃X : C⦄ ⦃i₁ i₂ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) :
    (J.overMapPullback A f₁).map (hom i₁) ≫ (D₂.iso f₁ f₂).hom =
    (D₁.iso f₁ f₂).hom ≫ (J.overMapPullback A f₂).map (hom i₂) := by aesop_cat

namespace Hom

attribute [reassoc (attr := simp, nolint simpNF)] comm

/-- The identity morphism in `hY.SheafDescentData A`. -/
@[simps]
def id : Hom D D where
  hom _ := 𝟙 _

variable {D₁ D₂ D₃}

/-- The composition of morphisms in `hY.SheafDescentData A`. -/
@[simps]
def comp (α : Hom D₁ D₂) (β : Hom D₂ D₃): Hom D₁ D₃ where
  hom i := α.hom i ≫ β.hom i

instance : Category (hY.SheafDescentData A) where
  Hom := Hom
  id := id
  comp := comp

end Hom

variable {D₁ D₂}

lemma congr_hom {f g : D₁ ⟶ D₂} (h : f = g) (i : I) : f.hom i = g.hom i := by
  subst h
  rfl

@[ext]
lemma hom_ext {f g : D₁ ⟶ D₂}
    (h : ∀ i, f.hom i = g.hom i) : f = g :=
  Hom.ext _ _ (funext h)

end SheafDescentData

variable {hY : J.ObjectsCoverTop Y} (A : Type u') [Category.{v'} A]

set_option maxHeartbeats 600000 in
/-- Given a family of objects `Y : I → C` which cover the final object for a Grothendieck
topology `J`, this is the functor `Sheaf J A ⥤ hY.SheafDescentData A`
which sends a sheaf `F` to the family of the pullbacks of `F` to all these `Y i`,
with the obbvious descent data. -/
@[simps! obj_sheaf obj_iso_hom obj_iso_inv map_hom]
def sheafToDescentData : Sheaf J A ⥤ hY.SheafDescentData A where
  obj F :=
    { sheaf := fun i => (J.overPullback A (Y i)).obj F
      iso := fun _ _ _ _ _ => Iso.refl _
      pullback_iso := fun X X' g i₁ i₂ f₁ f₂ => by
        ext W
        simp [overMapPullbackComp, Over.mapComp] }
  map {F G} φ :=
    { hom := fun i => (J.overPullback A (Y i)).map φ }

instance : Faithful (hY.sheafToDescentData A) where
  map_injective h :=
    (sheafHomSectionsEquiv _ _).symm.injective
      (hY.sections_ext _ (SheafDescentData.congr_hom h))

namespace SheafToDescentData

namespace Hom

variable {A}

/-- Given two sheaves `F` and `G`, a family of objects `Y : I → C` which cover the final
object, a morphism `φ : (hY.sheafToDescentData A).obj F ⟶ (hY.sheafToDescentData A).obj G`,
this is `φ.hom`, considered as a (compatible) family of sections of `(sheafHom F G).1` over
this family of objects `Y`. -/
abbrev toFamilyOfElementsOnObjects {F G : Sheaf J A}
    (φ : (hY.sheafToDescentData A).obj F ⟶ (hY.sheafToDescentData A).obj G) :
  Presheaf.FamilyOfElementsOnObjects (sheafHom F G).1 Y := φ.hom

lemma isCompatible_toFamilyOfElementsOnObjects {F G : Sheaf J A}
    (φ : (hY.sheafToDescentData A).obj F ⟶ (hY.sheafToDescentData A).obj G) :
    (toFamilyOfElementsOnObjects φ).IsCompatible := by
  intro Z i j f g
  simpa using φ.comm f g

end Hom

end SheafToDescentData

noncomputable instance : Full (hY.sheafToDescentData A) where
  preimage {F G} φ := (sheafHomSectionsEquiv _ _)
    ((SheafToDescentData.Hom.isCompatible_toFamilyOfElementsOnObjects φ).section_
      hY (Sheaf.cond _))
  witness φ := by
    ext1 i
    simp

/-- Given `Y : I → C` (which cover the final object for a certain Grothendieck topology `J`),
this is the full subcategory of `C` consisting of objects `X` such that there is a
morphism `f : X ⟶ Y i` for some `i : I`. The fact that `i` and `f` are data will ease the
gluing process. -/
structure OverSome (hY : J.ObjectsCoverTop Y) where
  /-- an object of the original category -/
  X : C
  /-- an index -/
  i : I
  /-- a morphism to one of the objects of the given family -/
  f : X ⟶ Y i

instance : Category hY.OverSome := InducedCategory.category OverSome.X

variable (hY)

/-- The obvious fully faithful functor `hY.OverSome ⥤ C`. -/
@[simps! obj]
def overSomeForget : hY.OverSome ⥤ C := inducedFunctor _

instance : Full hY.overSomeForget := InducedCategory.full _
instance : Faithful hY.overSomeForget := InducedCategory.faithful _

instance : Functor.IsCoverDense hY.overSomeForget J where
  is_cover X := by
    refine' J.superset_covering _ (hY X)
    rintro W f ⟨i, ⟨g⟩⟩
    exact
     ⟨{ obj := ⟨W, i, g⟩
        lift := 𝟙 _
        map := f }⟩

/-- The induced Grothendieck topology on `hY.overSome`. -/
abbrev overSomeTopology : GrothendieckTopology hY.OverSome :=
  Functor.inducedTopologyOfIsCoverDense hY.overSomeForget J

/- TODO: a presheaf on `hY.OverSome` is a sheaf iff the restriction to `Over (Y i)`
is for all `i`. -/

namespace SheafDescentData

variable {hY A} (F : hY.SheafDescentData A)

namespace ToPresheafOverSome

def obj (W : hY.OverSome) : A :=
  (F.sheaf W.i).1.obj (Opposite.op (Over.mk W.f))

def map {W₁ W₂ : hY.OverSome} (φ : W₁ ⟶ W₂) : obj F W₂ ⟶ obj F W₁ :=
  (F.sheaf W₂.i).1.map (Quiver.Hom.op (by exact Over.homMk φ)) ≫
    (F.isoSections (φ ≫ W₂.f) W₁.f).hom

/-lemma map_eq {W₁ W₂ : hY.OverSome} (φ : W₁ ⟶ W₂) {i : I} (f₁ : W₁.X ⟶ Y i) (f₂ : W₂.X ⟶ Y i)
    (fac : f₁ = hY.overSomeForget.map φ ≫ f₂) :
    map F φ = (F.isoSections W₂.f f₂).hom ≫
      (F.sheaf i).1.map (Quiver.Hom.op (by exact Over.homMk (hY.overSomeForget.map φ))) ≫
        (F.isoSections W₁.f f₁).inv := by
  sorry-/

end ToPresheafOverSome

/-open ToPresheafOverSome in
def toPresheafOverSome (F : hY.SheafDescentData A) : hY.OverSomeᵒᵖ ⥤ A where
  obj W := obj F W.unop
  map φ := map F φ.unop
  map_id := by
    rintro ⟨W⟩
    dsimp
    rw [map_eq F (𝟙 W) W.f W.f (by simp)]
    erw [Functor.map_id, id_comp, Iso.hom_inv_id]
    rfl
  map_comp := by
    rintro ⟨W₁⟩ ⟨W₂⟩ ⟨W₃⟩ ⟨f : W₂ ⟶ W₁⟩ ⟨g : W₃ ⟶ W₂⟩
    change map F (g ≫ f) = map F f ≫ map F g
    rw [map_eq F f _ W₁.f rfl, map_eq F (g ≫ f) _ W₁.f rfl,
      map_eq F g (hY.overSomeForget.map (g ≫ f) ≫ W₁.f)
        (hY.overSomeForget.map f ≫ W₁.f) (by simp)]
    simp only [overSomeForget_obj, Functor.map_comp, assoc, Iso.inv_hom_id_assoc,
      Iso.cancel_iso_hom_left]
    rw [← Functor.map_comp_assoc ]
    rfl-/

end SheafDescentData


end ObjectsCoverTop

end GrothendieckTopology

end CategoryTheory
