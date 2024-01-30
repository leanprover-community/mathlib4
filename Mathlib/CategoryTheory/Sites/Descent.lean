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

* Giraud, Jean, Mémoires de la Société Mathématique de France, no. 2 (1964), 156 p.

-/

universe v' v u' u

namespace CategoryTheory

open Category Limits

-- is this a duplicate lemma???
lemma NatTrans.naturality' {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (e : X ≅ Y) :
    α.app X = F.map e.hom ≫ α.app Y ≫ G.map e.inv := by
  simp only [naturality_assoc, ← G.map_comp, e.hom_inv_id, G.map_id, comp_id]

@[simp]
lemma sheafToPresheaf_preimage_val {C : Type*} [Category C] {J : GrothendieckTopology C}
    {A : Type*} [Category A] {F G : Sheaf J A} (φ : F.1 ⟶ G.1) :
    ((sheafToPresheaf J A).preimage φ).val = φ := rfl

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

@[reassoc]
lemma iso_trans_hom ⦃X : C⦄ ⦃i₁ i₂ i₃ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) (f₃ : X ⟶ Y i₃) :
    (D.iso f₁ f₂).hom ≫ (D.iso f₂ f₃).hom = (D.iso f₁ f₃).hom := by
  rw [← Iso.trans_hom, D.iso_trans]

@[reassoc]
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

/-- Given `D : hY.SheafDescentData A`, this is the isomorphism on
sections of `D.sheaf i₁` and `D.sheaf i₂` on objects which map
to two objects `Y i₁` and `Y i₂` of the family. -/
def isoSections ⦃X : C⦄ ⦃i₁ i₂ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) :
    (D.sheaf i₁).1.obj (Opposite.op (Over.mk f₁)) ≅
      (D.sheaf i₂).1.obj (Opposite.op (Over.mk f₂)) :=
  (overMapPullbackSectionsIso J A f₁ (Over.mk (𝟙 _)) (Over.mk f₁)
    (Over.isoMk (Iso.refl _))).symm.app (D.sheaf i₁) ≪≫
    ((sheafSections (J.over X) A).obj (Opposite.op (Over.mk (𝟙 X)))).mapIso (D.iso f₁ f₂) ≪≫
    (overMapPullbackSectionsIso J A f₂ (Over.mk (𝟙 _)) (Over.mk f₂)
      (Over.isoMk (Iso.refl _))).app (D.sheaf i₂)

lemma isoSections_trans ⦃X : C⦄ ⦃i₁ i₂ i₃ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) (f₃ : X ⟶ Y i₃) :
    D.isoSections f₁ f₂ ≪≫ D.isoSections f₂ f₃ = D.isoSections f₁ f₃ := by
  ext1
  simp [isoSections, ← D.iso_trans_hom f₁ f₂ f₃]

@[reassoc]
lemma isoSections_trans_hom ⦃X : C⦄ ⦃i₁ i₂ i₃ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) (f₃ : X ⟶ Y i₃) :
    (D.isoSections f₁ f₂).hom ≫ (D.isoSections f₂ f₃).hom = (D.isoSections f₁ f₃).hom := by
  rw [← Iso.trans_hom, isoSections_trans ]

@[reassoc]
lemma isoSections_trans_inv ⦃X : C⦄ ⦃i₁ i₂ i₃ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) (f₃ : X ⟶ Y i₃) :
    (D.isoSections f₂ f₃).inv ≫ (D.isoSections f₁ f₂).inv = (D.isoSections f₁ f₃).inv := by
  rw [← Iso.trans_inv, isoSections_trans]

lemma isoSections_refl ⦃X : C⦄ ⦃i : I⦄ (f : X ⟶ Y i) :
    D.isoSections f f = Iso.refl _ := by
  ext1
  dsimp
  rw [← cancel_mono (D.isoSections f f).hom, isoSections_trans_hom, id_comp]

lemma isoSections_inv ⦃X : C⦄ ⦃i₁ i₂ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) :
    (D.isoSections f₁ f₂).inv = (D.isoSections f₂ f₁).hom := by
  rw [← cancel_mono (D.isoSections f₁ f₂).hom, Iso.inv_hom_id, isoSections_trans_hom,
    isoSections_refl, Iso.refl_hom]

lemma isoSections_symm ⦃X : C⦄ ⦃i₁ i₂ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) :
    (D.isoSections f₁ f₂).symm = (D.isoSections f₂ f₁) := by
  ext1
  dsimp
  rw [isoSections_inv]

lemma pullback_iso' ⦃X Z : C⦄ (h : X ⟶ Z) ⦃i₁ : I⦄
    (f₁ : X ⟶ Y i₁) (g₁ : Z ⟶ Y i₁) (fac₁ : h ≫ g₁ = f₁)
      ⦃i₂ : I⦄ (f₂ : X ⟶ Y i₂) (g₂ : Z ⟶ Y i₂) (fac₂ : h ≫ g₂ = f₂) :
      D.iso f₁ f₂ = (J.overMapPullbackComp' A h g₁ f₁ fac₁).symm.app _ ≪≫
          (J.overMapPullback A h).mapIso (D.iso g₁ g₂) ≪≫
          (J.overMapPullbackComp' A h g₂ f₂ fac₂).app _ := by
  subst fac₁ fac₂
  apply pullback_iso

lemma pullback_iso'' ⦃X Z : C⦄ (h : X ⟶ Z) ⦃i₁ : I⦄
    (f₁ : X ⟶ Y i₁) (g₁ : Z ⟶ Y i₁) (fac₁ : h ≫ g₁ = f₁)
      ⦃i₂ : I⦄ (f₂ : X ⟶ Y i₂) (g₂ : Z ⟶ Y i₂) (fac₂ : h ≫ g₂ = f₂)
      (W : Over X) (W' : Over Z) (e : W' ≅ (Over.map h).obj W):
    (D.iso f₁ f₂).hom.val.app (Opposite.op W) =
      (D.sheaf i₁).val.map (Quiver.Hom.op (Over.homMk e.hom.left
          (by simp [← Over.w e.hom, fac₁]))) ≫
        (D.iso g₁ g₂).hom.val.app (Opposite.op W') ≫
          (D.sheaf i₂).val.map (Quiver.Hom.op (Over.homMk e.inv.left
            (by simp [← Over.w e.inv, fac₂]))) := by
  rw [D.pullback_iso' h f₁ g₁ fac₁ f₂ g₂ fac₂]
  dsimp
  rw [NatTrans.naturality' (D.iso g₁ g₂).hom.val e.op]
  dsimp [overMapPullbackComp', Functor.sheafPushforwardContinuousComp',
    Functor.sheafPushforwardContinuousComp, Functor.sheafPushforwardContinuousIso]
  rw [id_comp, assoc, assoc, assoc]
  erw [id_comp]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp, ← op_comp, ← op_comp]
  congr 3
  · ext
    simp [Over.mapComp'] -- there should exists a simp lemma Over.mapComp'_left
  · congr 1
    ext
    simp [Over.mapComp']

@[reassoc]
lemma isoSections_naturality ⦃X Z : C⦄ (h : X ⟶ Z) ⦃i₁ : I⦄ (f₁ : X ⟶ Y i₁)
    (g₁ : Z ⟶ Y i₁) (fac₁ : h ≫ g₁ = f₁) ⦃i₂ : I⦄ (f₂ : X ⟶ Y i₂) (g₂ : Z ⟶ Y i₂)
    (fac₂ : h ≫ g₂ = f₂) :
      (D.sheaf i₁).val.map (Quiver.Hom.op (by exact Over.homMk h)) ≫
        (D.isoSections f₁ f₂).hom = (D.isoSections g₁ g₂).hom ≫
        (D.sheaf i₂).val.map (Quiver.Hom.op (by exact Over.homMk h)) := by
  dsimp [isoSections]
  rw [D.pullback_iso' h f₁ g₁ fac₁ f₂ g₂ fac₂]
  dsimp [overMapPullbackSectionsIso]
  simp only [assoc, ← (D.sheaf i₂).val.map_comp, ← op_comp]
  let α : (Over.map h).obj (Over.mk (𝟙 X)) ⟶ Over.mk (𝟙 Z) := Over.homMk h
  have H := (iso D g₁ g₂).hom.val.naturality α.op
  dsimp at H
  let β : Over.mk f₂ ⟶ Over.mk g₂ := Over.homMk h
  let γ : Over.mk g₂ ≅ (Over.map g₂).obj (Over.mk (𝟙 Z)) := Over.isoMk (Iso.refl _)
  have fac : β ≫ γ.hom = (by exact Over.homMk (𝟙 _)) ≫ (Over.map g₂).map α := by
    ext; simp
  conv_rhs =>
    erw [fac]
  rw [op_comp, (D.sheaf i₂).val.map_comp, ← reassoc_of% H]
  conv_lhs => rw [← assoc, ← assoc]
  conv_rhs => rw [← assoc]
  congr 1
  · dsimp [overMapPullbackComp', Functor.sheafPushforwardContinuousComp',
      Functor.sheafPushforwardContinuousComp, Functor.sheafPushforwardContinuousIso]
    simp only [assoc]
    erw [comp_id]
    simp only [← Functor.map_comp, ← op_comp]
    congr 2
    ext
    dsimp [Over.mapComp']
    simp
  · congr 1
    dsimp [overMapPullbackComp', Functor.sheafPushforwardContinuousComp',
      Functor.sheafPushforwardContinuousComp, Functor.sheafPushforwardContinuousIso]
    simp only [id_comp, ← Functor.map_comp, ← op_comp]
    congr 2
    ext
    dsimp [Over.mapComp']
    simp

lemma isoSections_naturality' ⦃X Z : C⦄ (h : X ⟶ Z) ⦃i₁ : I⦄ (f₁ : X ⟶ Y i₁)
    (g₁ : Z ⟶ Y i₁) (fac₁ : h ≫ g₁ = f₁) ⦃i₂ : I⦄ (f₂ : X ⟶ Y i₂) (g₂ : Z ⟶ Y i₂)
    (fac₂ : h ≫ g₂ = f₂) :
      (D.sheaf i₁).val.map (Quiver.Hom.op (by exact Over.homMk h)) = (D.isoSections g₁ g₂).hom ≫
        (D.sheaf i₂).val.map (Quiver.Hom.op (by exact Over.homMk h)) ≫
          (D.isoSections f₁ f₂).inv := by
  rw [← D.isoSections_naturality_assoc h f₁ g₁ fac₁ f₂ g₂ fac₂, Iso.hom_inv_id, comp_id]

lemma iso_hom_val_app ⦃X : C⦄ (Z : (Over X)ᵒᵖ) ⦃i₁ i₂ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) :
    (D.iso f₁ f₂).hom.val.app Z =
      (D.sheaf i₁).val.map (Over.homMk (𝟙 _)).op ≫
        (D.isoSections (Z.unop.hom ≫ f₁) (Z.unop.hom ≫ f₂)).hom := by
  have eq := D.pullback_iso'' Z.unop.hom _ f₁ rfl _ f₂ rfl (Over.mk (𝟙 _)) Z.unop
    (Over.isoMk (Iso.refl _))
  dsimp [isoSections] at eq ⊢
  rw [eq, assoc,
    ← cancel_epi ((D.sheaf i₁).val.map (𝟙 (Opposite.op ((Over.map f₁).obj Z.unop)))),
    ← cancel_mono ((D.sheaf i₂).val.map (𝟙 (Opposite.op ((Over.map f₂).obj Z.unop))))]
  dsimp [overMapPullbackSectionsIso]
  simp only [assoc, ← Functor.map_comp_assoc, ← Functor.map_comp, ← op_comp]
  congr 2
  · apply Quiver.Hom.unop_inj
    ext
    simp
  · congr 1
    apply Quiver.Hom.unop_inj
    ext
    simp

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
def comp (α : Hom D₁ D₂) (β : Hom D₂ D₃) : Hom D₁ D₃ where
  hom i := α.hom i ≫ β.hom i

instance : Category (hY.SheafDescentData A) where
  Hom := Hom
  id := id
  comp := comp

end Hom

@[simp, reassoc]
lemma id_hom (i : I) :
    Hom.hom (𝟙 D₁) i = 𝟙 _ := rfl

variable {D₁ D₂ D₃}

@[simp, reassoc]
lemma comp_hom {α : D₁ ⟶ D₂} {β : D₂ ⟶ D₃} (i : I) :
    (α ≫ β).hom i = α.hom i ≫ β.hom i := rfl

lemma congr_hom {f g : D₁ ⟶ D₂} (h : f = g) (i : I) : f.hom i = g.hom i := by
  subst h
  rfl

@[ext]
lemma hom_ext {f g : D₁ ⟶ D₂}
    (h : ∀ i, f.hom i = g.hom i) : f = g :=
  Hom.ext _ _ (funext h)

@[reassoc]
lemma isoSections_hom_naturality₂ {D₁ D₂ : hY.SheafDescentData A}
    (φ : D₁ ⟶ D₂) ⦃X : C⦄ ⦃i₁ i₂ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) :
    (φ.hom i₁).val.app _ ≫ (D₂.isoSections f₁ f₂).hom =
      (D₁.isoSections f₁ f₂).hom ≫ (φ.hom i₂).val.app _ := by
  dsimp [isoSections]
  have h₁ := (overMapPullbackSectionsIso J A f₁ (Over.mk (𝟙 X)) (Over.mk f₁)
    (Over.isoMk (Iso.refl X))).inv.naturality (φ.hom i₁)
  have h₂ := (overMapPullbackSectionsIso J A f₂ (Over.mk (𝟙 X)) (Over.mk f₂)
    (Over.isoMk (Iso.refl X))).hom.naturality (φ.hom i₂)
  have h₃ := NatTrans.congr_app ((sheafToPresheaf _ _).congr_map (φ.comm f₁ f₂))
    (Opposite.op (Over.mk (𝟙 X)))
  dsimp at h₁ h₂ h₃
  simp only [assoc, ← h₂, reassoc_of% h₁, reassoc_of% h₃]

@[reassoc]
lemma isoSections_inv_naturality₂ {D₁ D₂ : hY.SheafDescentData A}
    (φ : D₁ ⟶ D₂) ⦃X : C⦄ ⦃i₁ i₂ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) :
    (φ.hom i₂).val.app _ ≫ (D₂.isoSections f₁ f₂).inv =
      (D₁.isoSections f₁ f₂).inv ≫ (φ.hom i₁).val.app _ := by
  rw [← cancel_mono (D₂.isoSections f₁ f₂).hom, assoc, assoc,
    Iso.inv_hom_id, comp_id, isoSections_hom_naturality₂ φ f₁ f₂,
    Iso.inv_hom_id_assoc]

/-- Constructor for isomorphisms in `hY.SheafDescentData A`. -/
@[simps]
def isoMk {D₁ D₂ : hY.SheafDescentData A} (e : ∀ i, D₁.sheaf i ≅ D₂.sheaf i)
    (comm : ∀ ⦃X : C⦄ ⦃i₁ i₂ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂),
    (J.overMapPullback A f₁).map (e i₁).hom ≫ (D₂.iso f₁ f₂).hom =
      (D₁.iso f₁ f₂).hom ≫ (J.overMapPullback A f₂).map (e i₂).hom) : D₁ ≅ D₂ where
  hom :=
    { hom := fun i => (e i).hom
      comm := comm }
  inv :=
    { hom := fun i => (e i).inv
      comm := by
        intro X i₁ i₂ f₁ f₂
        dsimp
        rw [← cancel_mono ((J.overMapPullback A f₂).map (e i₂).hom), assoc, assoc,
          ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id, comp_id, ← comm,
          ← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, id_comp] }
  hom_inv_id := by
    ext1 i
    exact (e i).hom_inv_id
  inv_hom_id := by
    ext1 i
    exact (e i).inv_hom_id

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
        dsimp
        erw [overMapPullBackComp'_hom_app_overPullback_obj,
          overMapPullBackComp'_inv_app_overPullback_obj]
        simp }
  map {F G} φ :=
    { hom := fun i => (J.overPullback A (Y i)).map φ }

instance : Faithful (hY.sheafToDescentData A) where
  map_injective h :=
    (sheafHomSectionsEquiv _ _).symm.injective
      (hY.sections_ext _ (SheafDescentData.congr_hom h))

@[simp]
lemma sheafToDescentData_isoSections
    (F : Sheaf J A) ⦃X : C⦄ ⦃i₁ i₂ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) :
    ((hY.sheafToDescentData A).obj F).isoSections f₁ f₂ = Iso.refl _ := by
  ext
  simp [SheafDescentData.isoSections, overMapPullbackSectionsIso]

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

/-- The inclusion functor of `Over (Y i)` in `hY.OverSome`. -/
@[simps]
def toOverSome (i : I) : Over (Y i) ⥤ hY.OverSome where
  obj X :=
    { X := X.left
      i := i
      f := X.hom }
  map f := f.left

/-- The canonical isomorphism
`hY.toOverSome i ⋙ hY.overSomeForget ≅ Over.forget (Y i)`. -/
@[simps!]
def toOverSomeForget (i : I) :
    hY.toOverSome i ⋙ hY.overSomeForget ≅ Over.forget (Y i) :=
  Iso.refl _

lemma toOverSome_coverPreserving (i : I) :
    CoverPreserving (J.over (Y i)) hY.overSomeTopology (hY.toOverSome i) where
  cover_preserve {U S} hS := by
    change _ ∈ J U.left
    rw [mem_over_iff] at hS
    convert hS
    exact (Sieve.functorPushforward_comp (hY.toOverSome i) (hY.overSomeForget) S).symm

lemma toOverSome_compatiblePreserving (i : I) :
    CompatiblePreserving hY.overSomeTopology (hY.toOverSome i) where
  compatible ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ h := by
    replace h := hY.overSomeForget.congr_map h
    simp at h
    let X' : Over (Y i) := Over.mk (hY.overSomeForget.map f₁ ≫ Y₁.hom)
    let φ₁ : X' ⟶ Y₁ := Over.homMk f₁
    let φ₂ : X' ⟶ Y₂ := Over.homMk f₂ (by
      dsimp
      erw [← Over.w g₂, ← reassoc_of% h, Over.w g₁])
    have H := hx φ₁ φ₂ hg₁ hg₂ (by ext; exact h)
    let e : X ≅ (hY.toOverSome i).obj X' := hY.overSomeForget.preimageIso (Iso.refl _)
    refine' Eq.trans _ ((congr_arg (ℱ.val.map e.hom.op) H).trans _)
    all_goals
      dsimp
      rw [← FunctorToTypes.map_comp_apply, ← op_comp]
      apply congr_fun
      congr 2
      apply hY.overSomeForget.map_injective
      simp
      rfl

instance (i : I) : (hY.toOverSome i).IsContinuous (J.over (Y i)) hY.overSomeTopology :=
  Functor.isContinuous_of_coverPreserving (hY.toOverSome_compatiblePreserving i)
    (hY.toOverSome_coverPreserving i)

/-- The restriction functor from sheaves on `hY.OverSome` to
the sheaves on `Over (Y i)`. -/
abbrev overSomeRestriction (i : I) :
    Sheaf hY.overSomeTopology A ⥤ Sheaf (J.over (Y i)) A :=
  (hY.toOverSome i).sheafPushforwardContinuous _ _ _

/-- The pullback functor from sheaves on `J` to `hY.overSomeTopology` that is induced
by the composition with `hY.overSomeForget : hY.OverSome ⥤ C`. -/
abbrev pullbackOverSome : Sheaf J A ⥤ Sheaf hY.overSomeTopology A :=
  (hY.overSomeForget).sheafPushforwardContinuous _ _ _

/-- The isomorphism `Over.map f₁ ⋙ hY.toOverSome i₁ ≅ Over.map f₂ ⋙ hY.toOverSome i₂`
when we have two maps `f₁ : X ⟶ Y i₁` and `f₂ : X ⟶ Y i₂`. -/
def overMapCompToOverSomeIso ⦃X : C⦄ ⦃i₁ i₂ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) :
    Over.map f₁ ⋙ hY.toOverSome i₁ ≅
      Over.map f₂ ⋙ hY.toOverSome i₂ :=
  NatIso.ofComponents (fun Z => hY.overSomeForget.preimageIso (Iso.refl _))
    (fun φ => hY.overSomeForget.map_injective (by aesop_cat))

@[simp]
lemma overSomeForget_map_overMapCompToOverSomeIso_hom_app
    ⦃X : C⦄ ⦃i₁ i₂ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) (Z : Over X) :
    (hY.overMapCompToOverSomeIso f₁ f₂).hom.app Z = 𝟙 _ := rfl

@[simp]
lemma overSomeForget_map_overMapCompToOverSomeIso_inv_app
    ⦃X : C⦄ ⦃i₁ i₂ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) (Z : Over X) :
    (hY.overMapCompToOverSomeIso f₁ f₂).inv.app Z = 𝟙 _ := rfl

variable {A hY}

/-- Equivalence between sieves of objects in `hY.OverSome` and the
induced objects in  -/
def overSomeSieveEquiv (X : hY.OverSome) :
    Sieve X ≃ Sieve X.X where
  toFun S := Sieve.functorPushforward hY.overSomeForget S
  invFun S' := Sieve.functorPullback hY.overSomeForget S'
  left_inv S := by
    ext W g
    dsimp [Sieve.functorPushforward, Sieve.functorPullback]
    constructor
    · rintro ⟨T, a, b, ha, fac⟩
      obtain rfl : g = b ≫ a := fac
      exact S.downward_closed ha _
    · intro hg
      exact ⟨W, g, 𝟙 _, hg, by simp⟩
  right_inv S' := by
    ext W g
    dsimp [Sieve.functorPushforward, Sieve.functorPullback]
    constructor
    · rintro ⟨T, a, b, ha, rfl⟩
      exact S'.downward_closed ha _
    · intro hg
      exact ⟨⟨W, X.i, g ≫ X.f⟩, g, 𝟙 _, hg, (id_comp _).symm⟩

lemma overSomeSieveEquiv_apply_mem_iff {X : hY.OverSome} (S : Sieve X) :
    overSomeSieveEquiv X S ∈ J X.X ↔ S ∈ hY.overSomeTopology X := by
  rfl

lemma overSomeSieveEquiv_symm_apply_mem_iff (X : hY.OverSome) (S : Sieve X.X) :
    (overSomeSieveEquiv X).symm S ∈ hY.overSomeTopology X ↔ S ∈ J X.X := by
  obtain ⟨S, rfl⟩ := (overSomeSieveEquiv X).surjective S
  rw [overSomeSieveEquiv_apply_mem_iff, Equiv.symm_apply_apply]

/-- The diagram category of a presieve. -/
abbrev _root_.CategoryTheory.Presieve.diagramCategory {C : Type*} [Category C] {X : C}
    (S : Presieve X) := FullSubcategory fun f : Over X => S f.hom

section

variable (X : hY.OverSome) (S : Sieve X.X)

/-- Given `X : hY.OverSome` and a sieve of `X.X`,
this is the functor (which is an equivalence) between the diagram categories of
related sieves of `Over.mk X.f : Over (Y X.i)` and `X`. -/
@[simps]
def OverSome.diagramFunctor :
    ((Sieve.overEquiv (Over.mk X.f)).symm S).arrows.diagramCategory ⥤
      ((overSomeSieveEquiv X).symm S).arrows.diagramCategory where
  obj := fun ⟨Z, hZ⟩ =>
    ⟨Over.mk (show OverSome.mk Z.left.left X.i (Z.hom.left ≫ X.f) ⟶ X from Z.hom.left), hZ⟩
  map {Z₁ Z₂} φ := Over.homMk φ.left.left (by
    dsimp
    rw [← Over.w φ]
    rfl)

instance : Faithful (OverSome.diagramFunctor X S) where
  map_injective := by
    rintro ⟨Z₁, hZ₁⟩ ⟨Z₂, hZ₂⟩ (f f' : Z₁ ⟶ Z₂) h
    apply CostructuredArrow.hom_ext
    apply CostructuredArrow.hom_ext
    have := (Over.forget _).congr_map h
    exact this

noncomputable instance : Full (OverSome.diagramFunctor X S) :=
  Functor.fullOfSurjective _ (by
    rintro ⟨Z₁, hZ₁⟩ ⟨Z₂, hZ₂⟩ φ
    refine' ⟨Over.homMk (Over.homMk φ.left _) _, rfl⟩
    · dsimp
      have h₁ := Over.w Z₁.hom
      have h₂ := Over.w Z₂.hom
      have h₃ := Over.w φ
      dsimp at h₁ h₂ h₃
      simp only [← h₁, ← h₂, ← h₃]
      erw [assoc]
    · ext
      exact Over.w φ)

instance : EssSurj (OverSome.diagramFunctor X S) where
  mem_essImage := by
    rintro ⟨Z, hZ⟩
    let W := Over.mk (hY.overSomeForget.map Z.hom ≫ X.f)
    let α : W ⟶ Over.mk X.f := Over.homMk Z.hom
    exact ⟨⟨Over.mk α, hZ⟩, ⟨(fullSubcategoryInclusion _).preimageIso
      (Over.isoMk (hY.overSomeForget.preimageIso (Iso.refl _)) (id_comp _))⟩⟩

noncomputable instance : IsEquivalence (OverSome.diagramFunctor X S) :=
  Equivalence.ofFullyFaithfullyEssSurj _

/-- Given `X : hY.OverSome` and a sieve of `X.X`,
this is the equivalence between the diagram categories of
related sieves of `Over.mk X.f : Over (Y X.i)` and `X`. -/
@[simps! functor]
noncomputable def OverSome.diagramFunctorEquivalence :=
  (OverSome.diagramFunctor X S).asEquivalence

end

/-- Auxiliary definition for `OverSome.isSheaf_iff`. -/
def OverSome.diagramIso (P : hY.OverSomeᵒᵖ ⥤ A) (X : hY.OverSome) (S : Sieve X.X) :
    ((((Sieve.overEquiv (Over.mk X.f)).symm S).arrows.diagram).op ⋙
        (hY.toOverSome X.i).op ⋙ P) ≅
      ((diagramFunctor X S).op ⋙ (((overSomeSieveEquiv X).symm S).arrows.diagram).op ⋙ P) :=
  NatIso.ofComponents (fun ⟨Z, hZ⟩ => P.mapIso
    ((hY.overSomeForget.preimageIso (by exact Iso.refl _)).op)) (by
      rintro ⟨⟨Z₁, hZ₁⟩⟩ ⟨⟨Z₂, hZ₂⟩⟩ ⟨f : Z₂ ⟶ Z₁⟩
      dsimp
      simp only [← P.map_comp, ← op_comp]
      congr 2
      apply hY.overSomeForget.map_injective
      simp
      rfl)

/-- Auxiliary definition for `OverSome.isSheaf_iff`. -/
noncomputable def OverSome.coneIso (P : hY.OverSomeᵒᵖ ⥤ A) (X : hY.OverSome) (S : Sieve X.X) :
  ((toOverSome hY X.i).op ⋙ P).mapCone (((Sieve.overEquiv (Over.mk X.f)).symm S).arrows.cocone.op) ≅
  (Cones.postcompose (diagramIso P X S).inv).obj
    (Cone.whisker (Equivalence.op (diagramFunctorEquivalence X S)).functor
      (P.mapCone ((((overSomeSieveEquiv X).symm S).arrows.cocone.op)))) :=
  Cones.ext (Iso.refl _) (by
    rintro ⟨Z, hZ⟩
    dsimp [diagramIso, diagramFunctor]
    rw [id_comp, ← P.map_comp, ← op_comp]
    erw [id_comp])

/-- Auxiliary definition for `OverSome.isSheaf_iff`. -/
noncomputable def OverSome.isLimitCone (P : hY.OverSomeᵒᵖ ⥤ A) (X : hY.OverSome) (S : Sieve X.X)
    (h : IsLimit (((hY.toOverSome X.i).op ⋙ P).mapCone
      ((Presieve.cocone ((Sieve.overEquiv (Over.mk X.f)).symm S).arrows).op))) :
    IsLimit (P.mapCone (Presieve.cocone ((overSomeSieveEquiv X).symm S).arrows).op) :=
  IsLimit.ofWhiskerEquivalence (diagramFunctorEquivalence X S).op
    ((IsLimit.postcomposeInvEquiv (diagramIso P X S) _).1
      (IsLimit.ofIsoLimit h (coneIso P X S)))

lemma OverSome.isSheaf_iff (P : hY.OverSomeᵒᵖ ⥤ A) :
    Presheaf.IsSheaf hY.overSomeTopology P ↔
      ∀ (i : I), Presheaf.IsSheaf (J.over (Y i)) ((hY.toOverSome i).op ⋙ P) := by
  constructor
  · intro h i
    exact Functor.op_comp_isSheaf (hY.toOverSome i) _ _ ⟨_, h⟩
  · intro h
    rw [Presheaf.isSheaf_iff_isLimit]
    rintro X S hS
    simp only [Presheaf.isSheaf_iff_isLimit] at h
    obtain ⟨S, rfl⟩ := (overSomeSieveEquiv X).symm.surjective S
    refine' ⟨isLimitCone P X S (h X.i ((Sieve.overEquiv (Over.mk X.f)).symm S) (by
      rw [overSomeSieveEquiv_symm_apply_mem_iff] at hS
      exact overEquiv_symm_mem_over _ _ _ hS)).some⟩

namespace SheafDescentData

variable (F : hY.SheafDescentData A)

namespace ToPresheafOverSome

/-- Auxiliary definition for `toPresheafOverSome`. -/
def obj (W : hY.OverSome) : A :=
  (F.sheaf W.i).1.obj (Opposite.op (Over.mk W.f))

/-- Auxiliary definition for `toPresheafOverSome`. -/
def map {W₁ W₂ : hY.OverSome} (φ : W₁ ⟶ W₂) : obj F W₂ ⟶ obj F W₁ :=
  (F.sheaf W₂.i).1.map (Quiver.Hom.op (by exact Over.homMk (hY.overSomeForget.map φ))) ≫
    (F.isoSections ((hY.overSomeForget.map φ) ≫ W₂.f) W₁.f).hom

lemma map_eq {W₁ W₂ : hY.OverSome} (φ : W₁ ⟶ W₂) {i : I} (f₁ : W₁.X ⟶ Y i) (f₂ : W₂.X ⟶ Y i)
    (fac : f₁ = hY.overSomeForget.map φ ≫ f₂) :
    map F φ = (F.isoSections W₂.f f₂).hom ≫
      (F.sheaf i).1.map (Quiver.Hom.op (by exact Over.homMk (hY.overSomeForget.map φ))) ≫
        (F.isoSections W₁.f f₁).inv := by
  dsimp [map]
  rw [F.isoSections_naturality' (hY.overSomeForget.map φ)
    ((hY.overSomeForget.map φ) ≫ W₂.f) W₂.f rfl f₁ f₂ fac.symm]
  simp only [overSomeForget_obj, assoc, Iso.cancel_iso_hom_left,
    isoSections_inv, isoSections_trans_hom]

end ToPresheafOverSome

open ToPresheafOverSome in
/-- The presheaf on `hY.OverSome` induced by `F : hY.SheafDescentData A`. -/
@[simps]
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
    rfl

/-- Given `F : hY.SheafDescentData A`, this is the canonical isomorphism
from the restriction of `F.toPresheafOverSome` to `Y i` and `(F.sheaf i).1`. -/
def toOverSomeOpToPresheafSheafOverSome (F : hY.SheafDescentData A) (i : I) :
    (hY.toOverSome i).op ⋙ F.toPresheafOverSome ≅ (F.sheaf i).1 :=
  NatIso.ofComponents (fun W => Iso.refl _) (by
    rintro ⟨W₁⟩ ⟨W₂⟩ ⟨f : W₂ ⟶ W₁⟩
    dsimp [toPresheafOverSome]
    rw [comp_id, id_comp]
    let φ : (toOverSome hY i).obj W₂ ⟶ (toOverSome hY i).obj W₁ := f.left
    refine' (ToPresheafOverSome.map_eq F φ W₂.hom W₁.hom (Over.w f).symm).trans _
    dsimp
    simp only [isoSections_refl, Iso.refl_hom, Iso.refl_inv, comp_id, id_comp]
    rfl)

/-- The sheaf on `hY.OverSome` induced by `F : hY.SheafDescentData A`. -/
@[simps]
def toSheafOverSome (F : hY.SheafDescentData A) : Sheaf hY.overSomeTopology A where
  val := F.toPresheafOverSome
  cond := by
    rw [OverSome.isSheaf_iff]
    intro i
    rw [Presheaf.isSheaf_of_iso_iff (toOverSomeOpToPresheafSheafOverSome F i)]
    apply Sheaf.cond

/-- Given `F : hY.SheafDescentData A`, this is the canonical isomorphism
from the restriction of `F.toSheafOverSome` to `Y i` and `F.sheaf i`. -/
def overSomeRestrictionToSheafOverSome (F : hY.SheafDescentData A) (i : I) :
    (hY.overSomeRestriction A i).obj F.toSheafOverSome ≅ F.sheaf i :=
  (sheafToPresheaf _ _).preimageIso (toOverSomeOpToPresheafSheafOverSome F i)

@[simp]
lemma overSomeRestrictionToSheafOverSome_hom_val_app (F : hY.SheafDescentData A) (i : I)
    (Z : (Over (Y i))ᵒᵖ) :
    (F.overSomeRestrictionToSheafOverSome i).hom.val.app Z = 𝟙 _ := rfl

@[simp]
lemma overSomeRestrictionToSheafOverSome_inv_val_app (F : hY.SheafDescentData A) (i : I)
    (Z : (Over (Y i))ᵒᵖ) :
    (F.overSomeRestrictionToSheafOverSome i).inv.val.app Z = 𝟙 _ := rfl

end SheafDescentData

variable (hY A)

/-- The obvious functor `hY.SheafDescentData A ⥤ Sheaf hY.overSomeTopology A`. -/
@[simps]
def toSheafOverSomeFunctor : hY.SheafDescentData A ⥤ Sheaf hY.overSomeTopology A where
  obj F := F.toSheafOverSome
  map {F G} φ := ⟨
    { app := fun X => (φ.hom X.unop.i).val.app _
      naturality := fun {X Y} α => by
        dsimp
        simp only [SheafDescentData.ToPresheafOverSome.map_eq _ α.unop
          ((overSomeForget _).map α.unop ≫ X.unop.f) X.unop.f (by simp), assoc,
          SheafDescentData.isoSections_refl, Iso.refl_hom, overSomeForget_obj, id_comp,
          ← SheafDescentData.isoSections_inv_naturality₂, NatTrans.naturality_assoc] }⟩

variable {A}

/-- The canonical isomorphism
`((hY.sheafToDescentData A).obj F).toSheafOverSome ≅ (hY.pullbackOverSome A).obj F` for
a sheaf `F : Sheaf J A`. -/
def sheafToDescentDataToSheafOverSomeIso (F : Sheaf J A) :
    ((hY.sheafToDescentData A).obj F).toSheafOverSome ≅ (hY.pullbackOverSome A).obj F :=
  (sheafToPresheaf _ _).preimageIso (NatIso.ofComponents (fun X => Iso.refl _) (by
    rintro X Y f
    dsimp [SheafDescentData.ToPresheafOverSome.map]
    simp only [comp_id, id_comp, sheafToDescentData_isoSections, Iso.refl_hom]
    dsimp
    simp only [comp_id]))

@[simp]
lemma sheafToDescentDataToSheafOverSomeIso_hom_val_app (F : Sheaf J A) (X : hY.OverSomeᵒᵖ) :
    (hY.sheafToDescentDataToSheafOverSomeIso F).hom.val.app X = 𝟙 _ := rfl

@[simp]
lemma sheafToDescentDataToSheafOverSomeIso_inv_val_app (F : Sheaf J A) (X : hY.OverSomeᵒᵖ) :
    (hY.sheafToDescentDataToSheafOverSomeIso F).inv.val.app X = 𝟙 _ := rfl

variable (A)

/-- The natural isomorphism
`hY.sheafToDescentData A ⋙ hY.toSheafOverSomeFunctor A ≅ hY.pullbackOverSome A`. -/
@[simps!]
def sheafToDescentDataCompToSheafOverSomeFunctorIso :
    hY.sheafToDescentData A ⋙ hY.toSheafOverSomeFunctor A ≅ hY.pullbackOverSome A :=
  NatIso.ofComponents hY.sheafToDescentDataToSheafOverSomeIso (by aesop_cat)

/- TODO: show that `toSheafOverSomeFunctor` is an equivalence of categories, then,
as the composition `Sheaf J A ⥤ hY.SheafDescentData A ⥤ Sheaf hY.overSomeTopology A`
identifies to the obvious restriction (done below),
which under suitable assumptions is an equivalence of categories
(see `Functor.IsCoverDense.sheafEquivOfCoverPreservingCoverLifting`, we can deduce
that `Sheaf J A ⥤ hY.SheafDescentData A` is an equivalence.)
-/

namespace SheafDescentData

variable {hY A}
variable (F : Sheaf hY.overSomeTopology A)

namespace OfSheafOverSome

/-- The descent data for `ObjectsCoverTop.SheafDescentData.ofSheafOverSome`. -/
def iso ⦃X : C⦄ ⦃i₁ i₂ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) :
    (J.overMapPullback A f₁).obj ((hY.overSomeRestriction A i₁).obj F) ≅
      (J.overMapPullback A f₂).obj ((hY.overSomeRestriction A i₂).obj F) :=
  (sheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun Z => F.val.mapIso
      ((hY.overMapCompToOverSomeIso f₁ f₂).app Z.unop).symm.op) (by
      intros Z₁ Z₂ α
      dsimp
      simp only [← Functor.map_comp, ← op_comp]
      congr 2
      erw [id_comp, comp_id]))

@[simp]
lemma iso_hom_val_app ⦃X : C⦄ ⦃i₁ i₂ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) (Z : (Over X)ᵒᵖ) :
    (iso F f₁ f₂).hom.val.app Z = F.1.map (Quiver.Hom.op (𝟙 Z.unop.left)) := rfl

@[simp]
lemma iso_inv_val_app ⦃X : C⦄ ⦃i₁ i₂ : I⦄ (f₁ : X ⟶ Y i₁) (f₂ : X ⟶ Y i₂) (Z : (Over X)ᵒᵖ) :
    (iso F f₁ f₂).inv.val.app Z = F.1.map (Quiver.Hom.op (𝟙 Z.unop.left)) := rfl

end OfSheafOverSome

/-- The sheaves with descent data attached to a sheaf for `hY.overSomeTopology`. -/
@[simps]
def ofSheafOverSome : hY.SheafDescentData A where
  sheaf i := (hY.overSomeRestriction A i).obj F
  iso {X i₁ i₂} f₁ f₂ := OfSheafOverSome.iso F f₁ f₂
  pullback_iso X X' g i₁ i₂ f₁ f₂ := by
    ext Z
    dsimp [overMapPullbackComp, overMapPullbackComp',
      Functor.sheafPushforwardContinuousComp',
      Functor.sheafPushforwardContinuousIso, Over.mapComp',
      Functor.sheafPushforwardContinuousComp]
    simp only [id_comp, assoc]
    erw [id_comp]
    simp only [← Functor.map_comp, ← op_comp]
    congr 2
    erw [id_comp, id_comp]
  iso_trans X i₁ i₂ i₃ f₁ f₂ f₃ := by
    ext Z
    dsimp
    rw [← Functor.map_comp, ← op_comp]
    congr 2
    erw [id_comp]

@[simp]
lemma ofSheafOverSome_toPresheafOverSome_map {Z₁ Z₂ : hY.OverSome} (φ : Z₁ ⟶ Z₂) :
    ToPresheafOverSome.map (ofSheafOverSome F) φ = F.1.map φ.op := by
  dsimp [ToPresheafOverSome.map, overSomeForget, isoSections,
    overMapPullbackSectionsIso]
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  erw [id_comp, id_comp, id_comp]

end SheafDescentData

/-- The obvious functor `Sheaf hY.overSomeTopology A ⥤ hY.SheafDescentData A`. -/
@[simps]
def fromSheafOverSomeFunctor : Sheaf hY.overSomeTopology A ⥤ hY.SheafDescentData A where
  obj := SheafDescentData.ofSheafOverSome
  map {F₁ F₂} φ :=
    { hom := fun i => (hY.overSomeRestriction A i).map φ }

namespace SheafOverFunctorEquivalence

variable {hY A}

/-- Auxiliary definition for `ObjectsCoverTop.sheafOverSomeEquivalence`. -/
@[simps!]
def unitIsoApp (F : hY.SheafDescentData A) :
    F ≅ (hY.fromSheafOverSomeFunctor A).obj ((hY.toSheafOverSomeFunctor A).obj F) :=
  SheafDescentData.isoMk
    (fun i => (F.overSomeRestrictionToSheafOverSome i).symm) (by
      intros X i₁ i₂ f₁ f₂
      dsimp
      ext Z
      dsimp
      rw [id_comp, comp_id]
      let α : ((hY.toOverSome i₂).obj ((Over.map f₂).obj Z.unop)) ⟶
        ((hY.toOverSome i₁).obj ((Over.map f₁).obj Z.unop)) := 𝟙 Z.unop.left
      rw [SheafDescentData.ToPresheafOverSome.map_eq F α (Z.unop.hom ≫ f₁)
        (Z.unop.hom ≫ f₁) (by erw [id_comp])]
      dsimp
      rw [SheafDescentData.isoSections_refl, Iso.refl_hom, id_comp,
        SheafDescentData.isoSections_inv]
      exact (F.iso_hom_val_app Z f₁ f₂).symm)

/-- Auxiliary definition for `ObjectsCoverTop.sheafOverSomeEquivalence`. -/
def counitIsoApp (F : Sheaf hY.overSomeTopology A) :
    (hY.toSheafOverSomeFunctor A).obj ((hY.fromSheafOverSomeFunctor A).obj F) ≅ F :=
  (sheafToPresheaf _ _).preimageIso (NatIso.ofComponents (fun Z => Iso.refl _)
    (by aesop_cat))

@[simp]
lemma counitIsoApp_hom (F : Sheaf hY.overSomeTopology A) (Z : hY.OverSomeᵒᵖ) :
    (counitIsoApp F).hom.val.app Z = 𝟙 _ := rfl

@[simp]
lemma counitIsoApp_inv (F : Sheaf hY.overSomeTopology A) (Z : hY.OverSomeᵒᵖ) :
    (counitIsoApp F).inv.val.app Z = 𝟙 _ := rfl

variable (hY A)

/-- Auxiliary definition for `ObjectsCoverTop.sheafOverSomeEquivalence`. -/
@[simps!]
def unitIso : 𝟭 _ ≅ hY.toSheafOverSomeFunctor A ⋙ hY.fromSheafOverSomeFunctor A :=
  NatIso.ofComponents unitIsoApp (by
    intro F G φ
    ext i Z
    dsimp
    erw [comp_id, id_comp]
    rfl)

/-- Auxiliary definition for `ObjectsCoverTop.sheafOverSomeEquivalence`. -/
@[simps!]
def counitIso : hY.fromSheafOverSomeFunctor A ⋙ hY.toSheafOverSomeFunctor A ≅ 𝟭 _ :=
  NatIso.ofComponents counitIsoApp (by aesop_cat)

end SheafOverFunctorEquivalence

/-- The equivalence `hY.SheafDescentData A ≌ Sheaf hY.overSomeTopology A` between
sheaves equipped with descent data and the category of sheaves
over `hY.overSomeTopology`. -/
def sheafOverSomeEquivalence :
    hY.SheafDescentData A ≌ Sheaf hY.overSomeTopology A where
  functor := hY.toSheafOverSomeFunctor A
  inverse := hY.fromSheafOverSomeFunctor A
  unitIso := SheafOverFunctorEquivalence.unitIso hY A
  counitIso := SheafOverFunctorEquivalence.counitIso hY A

namespace SheafDescentData

instance : IsEquivalence (hY.toSheafOverSomeFunctor A) := by
  change IsEquivalence (hY.sheafOverSomeEquivalence A).functor
  infer_instance

instance : IsEquivalence (hY.fromSheafOverSomeFunctor A) := by
  change IsEquivalence (hY.sheafOverSomeEquivalence A).inverse
  infer_instance

instance [IsEquivalence (hY.pullbackOverSome A)] :
    IsEquivalence (hY.sheafToDescentData A) :=
  IsEquivalence.cancelCompRight (hY.sheafToDescentData A)
    (hY.toSheafOverSomeFunctor A) inferInstance
    (IsEquivalence.ofIso (hY.sheafToDescentDataCompToSheafOverSomeFunctorIso A).symm
      inferInstance)

section

variable {D : Type u} [Category.{u} D] {K : GrothendieckTopology D}
  {J : Type} {Z : J → D} (hZ : K.ObjectsCoverTop Z)
  (B : Type v) [Category.{u} B] [HasLimits B]

noncomputable instance : IsEquivalence (hZ.pullbackOverSome B) :=
  (inferInstance : IsEquivalence (Functor.IsCoverDense.sheafEquivOfCoverPreservingCoverLifting
    hZ.overSomeForget hZ.overSomeTopology K B).inverse)

noncomputable example : IsEquivalence (hZ.sheafToDescentData B) := inferInstance

end

end SheafDescentData

end ObjectsCoverTop

end GrothendieckTopology

end CategoryTheory
