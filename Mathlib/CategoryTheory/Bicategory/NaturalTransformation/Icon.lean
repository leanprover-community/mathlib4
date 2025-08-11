/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Lax
import Mathlib.CategoryTheory.Bicategory.EqToHom

/-! # Identity-component oplax natural transformations of lax functors

An identity-component oplax natural transformation ("icon") between
lax functors `F` and `G` is the data of an oplax natural transformation
`η` from `F` to `G`, along with equalities of objects `h_x : F.obj x = G.obj x`
for every `x`, and equalities of 1-morphisms `η.app x = eqToHom h_x` for
every `x`. In other words: an icon is an oplax natural transformation that does
nothing at the level of objects.

## References
* [Johnson-Yau, *2-Dimensional Categories*, section 4.6](https://arxiv.org/abs/2002.06055)

-/


namespace CategoryTheory.Lax

open Category Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B]
    {C : Type u₂} [Bicategory.{w₂, v₂} C]

/-- An identity-component oplax natural transformation ("icon") between
lax functors `F` `G` bundles an equality `F.obj x = G.obj x`for every
object `x`. And an oplax natural transformation `η` from `F` to `G` such that
`η.app x` is the transport `1`-cell along the equality `F.obj x = G.obj x`.
-/
structure Icon (F G : LaxFunctor B C) extends Lax.OplaxTrans F G where
  obj_eq : ∀ (x : B), F.obj x = G.obj x
  app_eq_eqToHom : ∀ (x : B), app x = eqToHom (obj_eq x)

namespace Icon

/-- The identity icon from `F` to itself has the identity oplax natural
transformation as underlying oplax natural transformation. -/
@[simps!]
def id (F : LaxFunctor B C) : Icon F F where
  __ := OplaxTrans.id F
  obj_eq _ := rfl
  app_eq_eqToHom _ := rfl

section vComp
variable {F G H : LaxFunctor B C} (η : Icon F G) (θ : Icon G H)

/-- The app component of the vertical composition of icons. By definition, it is an
`eqToHom` 1-cell along the equality on objects between the source and target functors
that can be deduced from the available icons. -/
abbrev vCompApp (x : B) :
    F.obj x ⟶ H.obj x :=
  eqToHom <| (η.obj_eq x).trans (θ.obj_eq x)

/-- The naturality component 2-cell of the vertical composition of icons. Up to the equality of
objects and morphisms at hand, this is in fact the naturality component of the underlying oplax
natural transformation of lax functors. -/
abbrev vCompNaturality {x y : B} (f : x ⟶ y) :
    F.map f ≫ vCompApp η θ y ⟶ vCompApp η θ x ≫ H.map f :=
  letI i₁ := eqToHomTransIso (η.obj_eq y) (θ.obj_eq y)
  letI i₂ := eqToHomTransIso (η.obj_eq x) (θ.obj_eq x)
  letI i₃ : η.app y ≫ θ.app y ≅ eqToHom (η.obj_eq y) ≫ eqToHom (θ.obj_eq y) :=
    whiskerLeftIso _ (eqToIso <| θ.app_eq_eqToHom y) ≪≫
      whiskerRightIso (eqToIso <| η.app_eq_eqToHom y) _
  letI i₄ : η.app x ≫ θ.app x ≅ eqToHom (η.obj_eq x) ≫ eqToHom (θ.obj_eq x) :=
    whiskerLeftIso _ (eqToIso <| θ.app_eq_eqToHom x) ≪≫
      whiskerRightIso (eqToIso <| η.app_eq_eqToHom x) _
  F.map f ◁ (i₁.hom ≫ i₃.inv) ≫
    (η.toOplaxTrans.vComp θ.toOplaxTrans|>.naturality f) ≫
    (i₄.hom ≫ i₂.inv) ▷ H.map f

lemma vCompNaturality_id (x : B) :
    F.mapId x ▷ vCompApp η θ x ≫ vCompNaturality η θ (𝟙 x) =
    (λ_ (vCompApp η θ x)).hom ≫ (ρ_ (vCompApp η θ x)).inv ≫
      vCompApp η θ x ◁ H.mapId x := by
  have u := (η.toOplaxTrans.vComp θ.toOplaxTrans|>.naturality_id x)
  dsimp [vCompApp, vCompNaturality, OplaxTrans.vComp,
    OplaxTrans.vCompApp] at u ⊢
  simp only [whiskerRight_comp, assoc, Iso.hom_inv_id_assoc,
    comp_whiskerLeft] at u
  simp only [eqToHom_whiskerRight, whiskerLeft_eqToHom, eqToHom_trans,
    whiskerLeft_comp, comp_whiskerRight, assoc, ← whisker_exchange_assoc,
    id_whiskerLeft, whiskerRight_comp,
    associator_inv_congr (f := 𝟙 (F.obj x)) rfl (η.app_eq_eqToHom x).symm
      (θ.app_eq_eqToHom x).symm,
    associator_hom_congr (f := F.map (𝟙 x)) rfl (η.app_eq_eqToHom x).symm
      (θ.app_eq_eqToHom x).symm,
    eqToHom_trans_assoc, eqToHom_refl, id_comp, Iso.hom_inv_id_assoc,
    Iso.cancel_iso_hom_left]
  rw [whiskerRight_congr (θ.app_eq_eqToHom x).symm,
    whiskerRight_congr (η.app_eq_eqToHom x).symm]
  let t := eqToHomTransIso (η.obj_eq x) (θ.obj_eq x)
  have := rightUnitor_inv_naturality
      (eqToHomTransIso (η.obj_eq x) (θ.obj_eq x)).hom =≫
        (eqToHomTransIso (η.obj_eq x) (θ.obj_eq x)).inv ▷ 𝟙 (H.obj x)
  simp only [assoc, hom_inv_whiskerRight, comp_id] at this
  simp only [comp_whiskerRight, eqToHom_whiskerRight, assoc, eqToHom_trans,
    eqToHom_trans_assoc, eqToHom_refl, id_comp, reassoc_of% u, ← this,
    rightUnitor_inv_congr (congr_arg₂ (· ≫ ·)
      (η.app_eq_eqToHom x).symm (θ.app_eq_eqToHom x).symm),
    leftUnitor_inv_congr (congr_arg₂ (· ≫ ·)
      (η.app_eq_eqToHom x).symm (θ.app_eq_eqToHom x).symm)]
  congr 2
  dsimp [t]
  rw [← whisker_exchange]
  simp [associator_inv_congr (h := H.map (𝟙 x)) (η.app_eq_eqToHom x).symm
      (θ.app_eq_eqToHom x).symm rfl,
    associator_hom_congr (h := 𝟙 (H.obj x)) (η.app_eq_eqToHom x).symm
      (θ.app_eq_eqToHom x).symm rfl,
    congr_whiskerLeft (θ.app_eq_eqToHom x).symm (H.mapId x),
    congr_whiskerLeft (η.app_eq_eqToHom x).symm (θ.app x ◁ H.mapId x) ]

lemma vCompNaturality_comp {x y z : B} (f : x ⟶ y) (g : y ⟶ z) :
    F.mapComp f g ▷ vCompApp η θ z ≫ vCompNaturality η θ (f ≫ g) =
    (α_ _ _ _).hom ≫ F.map f ◁ vCompNaturality η θ g ≫
      (α_ _ _ _).inv ≫ vCompNaturality η θ f ▷ H.map g ≫ (α_ _ _ _).hom ≫
      vCompApp η θ x ◁ H.mapComp f g := by
    dsimp [vCompApp, vCompNaturality]
    have u := (η.toOplaxTrans.vComp θ.toOplaxTrans|>.naturality_comp f g)
    simp only [OplaxTrans.vComp, whiskerRight_comp, assoc, Iso.hom_inv_id_assoc,
      whiskerLeft_comp, comp_whiskerRight, whisker_assoc, comp_whiskerLeft,
      pentagon_inv_hom_hom_hom_hom_assoc, Iso.inv_hom_id_assoc,
      pentagon_inv_assoc] at u
    simp only [eqToHom_whiskerRight,
      whiskerLeft_eqToHom, eqToHom_trans,
      whiskerLeft_comp, comp_whiskerRight, assoc, whisker_assoc,
      Iso.inv_hom_id_assoc, ← whiskerLeft_comp_assoc,
      inv_hom_whiskerRight, whiskerLeft_id, id_comp]
    simp only [OplaxTrans.vComp, assoc, whiskerLeft_comp, comp_whiskerRight,
      whisker_assoc]
    slice_lhs 1 4 =>
      equals _ ◁ (eqToHomTransIso (η.obj_eq z) (θ.obj_eq z)).hom ≫
          _ ◁ (eqToHom (congr_arg₂ (· ≫ ·)
            (η.app_eq_eqToHom z).symm (θ.app_eq_eqToHom z).symm)) ≫
          F.mapComp f g ▷ _ ≫ (α_ _ _ _).inv =>
        simp only [← whisker_exchange_assoc, comp_whiskerLeft,
          whiskerRight_comp, assoc, whiskerLeft_eqToHom, Iso.hom_inv_id,
          comp_id, Iso.cancel_iso_hom_left]
        rw [whiskerRight_congr (θ.app_eq_eqToHom z).symm,
          whiskerRight_congr (η.app_eq_eqToHom z).symm]
        simp [associator_hom_congr (f := (F.map (f ≫ g)))
            rfl (η.app_eq_eqToHom z).symm (θ.app_eq_eqToHom z).symm,
          associator_inv_congr (f := (F.map f ≫ F.map g))
            rfl (η.app_eq_eqToHom z).symm (θ.app_eq_eqToHom z).symm]
    simp only [Category.assoc, whiskerRight_comp, Iso.hom_inv_id_assoc,
      ← comp_whiskerRight_assoc]
    simp only [comp_whiskerRight, assoc, reassoc_of% u]
    simp only [comp_whiskerLeft, associator_inv_congr
        (f := F.map f) (g := F.map g) rfl rfl (congr_arg₂ (· ≫ ·)
          (η.app_eq_eqToHom z).symm (θ.app_eq_eqToHom z).symm),
      whiskerLeft_eqToHom, OplaxTrans.vCompApp, assoc, eqToHom_trans_assoc,
      eqToHom_refl, id_comp, Iso.inv_hom_id_assoc,
      associator_inv_congr (f := F.map f) (h := H.map g) rfl
        (congr_arg₂ (· ≫ ·) (η.app_eq_eqToHom y).symm (θ.app_eq_eqToHom y).symm)
        rfl,
      pentagon_inv_assoc, Iso.cancel_iso_hom_left]
    congr 12
    rw [associator_naturality_left_assoc, ← whisker_exchange]
    simp only [comp_whiskerLeft, assoc]
    rw [congr_whiskerLeft (θ.app_eq_eqToHom x).symm,
      congr_whiskerLeft (η.app_eq_eqToHom x).symm]
    simp [associator_inv_congr (h := H.map (f ≫ g))
        (η.app_eq_eqToHom x).symm (θ.app_eq_eqToHom x).symm rfl,
      associator_hom_congr (h := H.map f ≫ H.map g)
        (η.app_eq_eqToHom x).symm (θ.app_eq_eqToHom x).symm rfl,
      associator_hom_congr (g := H.map f) (h := H.map g)
        (congr_arg₂ (· ≫ ·)
          (η.app_eq_eqToHom x).symm (θ.app_eq_eqToHom x).symm) rfl rfl]

lemma vCompNaturality_naturality {x y : B} {u v : x ⟶ y} (f : u ⟶ v) :
    F.map₂ f ▷ vCompApp η θ y ≫ vCompNaturality η θ v =
    vCompNaturality η θ u ≫ vCompApp η θ x ◁ H.map₂ f := by
  dsimp [vCompApp, vCompNaturality]
  have n := (η.toOplaxTrans.vComp θ.toOplaxTrans|>.naturality_naturality f)
  simp only [OplaxTrans.vComp, OplaxTrans.vCompApp, whiskerRight_comp, assoc,
    Iso.hom_inv_id_assoc, comp_whiskerLeft, Iso.inv_hom_id_assoc,
    Iso.cancel_iso_inv_left, eqToHom_whiskerRight,
    whiskerLeft_eqToHom, eqToHom_trans, whiskerLeft_comp,
    comp_whiskerRight] at n ⊢
  simp only [← whisker_exchange_assoc, whiskerRight_comp,
    associator_inv_congr (f := F.map u)
      rfl (η.app_eq_eqToHom y).symm (θ.app_eq_eqToHom y).symm,
    whiskerRight_congr (η.app_eq_eqToHom y).symm (F.map₂ f), comp_whiskerRight,
    eqToHom_whiskerRight, assoc, eqToHom_trans, eqToHom_trans_assoc,
    whiskerRight_congr (θ.app_eq_eqToHom y).symm (F.map₂ f ▷ η.app y),
    associator_hom_congr (f := F.map v)
      rfl (η.app_eq_eqToHom y).symm (θ.app_eq_eqToHom y).symm,
    eqToHom_refl, id_comp, Iso.hom_inv_id_assoc, reassoc_of% n]
  congr 6
  simp [← whisker_exchange,
    associator_hom_congr (h := H.map u)
      (η.app_eq_eqToHom x).symm (θ.app_eq_eqToHom x).symm rfl,
    associator_inv_congr (h := H.map v)
      (η.app_eq_eqToHom x).symm (θ.app_eq_eqToHom x).symm rfl,
    congr_whiskerLeft (θ.app_eq_eqToHom x).symm (H.map₂ f),
    congr_whiskerLeft (η.app_eq_eqToHom x).symm (θ.app x ◁ H.map₂ f)]

end vComp

/-- Vertical composition of icons. This is in fact the vertical composition of the underlying
oplax natural transformations, with correction terms added so that the app component can be a
single `eqToHom` morphism (rather than a composition of such). -/
def vComp {F G H : LaxFunctor B C} (η : Icon F G) (θ : Icon G H) :
    Icon F H where
  app x := vCompApp η θ x
  naturality f := vCompNaturality η θ f
  obj_eq x := (η.obj_eq x).trans (θ.obj_eq x)
  app_eq_eqToHom _ := rfl
  naturality_id x := vCompNaturality_id η θ x
  naturality_comp f g := vCompNaturality_comp η θ f g
  naturality_naturality f := vCompNaturality_naturality η θ f

attribute [local ext] Icon in
theorem comp_assoc {F G H K : LaxFunctor B C}
    (η : Icon F G) (θ : Icon G H) (τ : Icon H K) :
    (η.vComp θ).vComp τ = η.vComp (θ.vComp τ) := by
  ext
  · rfl
  · rw [heq_iff_eq]
    ext x y f
    dsimp [vComp, vCompApp, vCompNaturality, OplaxTrans.vComp,
      OplaxTrans.vCompApp, OplaxTrans.vCompNaturality]
    simp only [Category.comp_id, Category.id_comp, Category.assoc,
      whiskerLeft_id, id_whiskerRight,
      whiskerLeft_comp, comp_whiskerRight, Category.assoc]
    -- The proof here is to pull the naturality 2-cells towards the
    -- center of the expressions as much as possible, the "outer morphisms"
    -- will then be a buch of eqToHoms that will eventually cancel out, and
    -- we’ll be left with a simpable bicategory goal.
    -- Abstracting away the proofs speeds up things a bit, it’s also somewhat
    -- more convenient to give them shorter names
    generalize_proofs t₁ t₂ t₃ oy₃ my₃ oy₁ oy₂ my₁ my₂
      ox₂ mx₂ ox₁ mx₁ t₄ ox₃ mx₃ t₅ t₆
    slice_lhs 12 17 =>
      equals (α_ (η.app x ≫ θ.app x) (H.map f) (τ.app y)).hom ≫
          _ ◁ τ.naturality f ≫ (eqToHom (congr_arg₂ (· ≫ ·) mx₁ mx₂) ≫
            (eqToHomTransIso ox₁ ox₂).inv) ▷ _ ≫ (α_ _ _ _).inv =>
        dsimp
        simp only [comp_whiskerLeft,
          whiskerRight_comp, comp_whiskerRight, assoc, Iso.hom_inv_id, comp_id]
        rw [associator_inv_naturality_right_assoc, Iso.hom_inv_id_assoc,
          ← associator_inv_naturality_left_assoc, whisker_exchange_assoc,
          ← associator_inv_naturality_left, whisker_exchange_assoc]
        simp
    slice_rhs 4 8 =>
      equals (F.map f ≫ η.app y) ◁ (eqToHomTransIso oy₂ oy₃).hom ≫
          (F.map f ≫ η.app y) ◁ eqToHom (congr_arg₂ (· ≫ ·) my₂ my₃) ≫
          η.naturality f ▷ _ ≫ (α_ _ _ _).hom =>
        simp only [comp_whiskerLeft, whiskerRight_comp, assoc,
          Iso.inv_hom_id_assoc]
        rw [associator_naturality_left_assoc, Iso.inv_hom_id_assoc,
          associator_inv_naturality_right_assoc, whisker_exchange_assoc,
          associator_inv_naturality_right_assoc, whisker_exchange_assoc,
          Iso.hom_inv_id_assoc]
        simp [associator_inv_congr (f := η.app x) (g := G.map f)
          rfl rfl (congr_arg₂ (· ≫ ·) my₂ my₃)]
    simp only [whisker_assoc, whiskerLeft_comp, assoc, comp_whiskerLeft,
      whiskerRight_comp, comp_whiskerRight, Iso.hom_inv_id, comp_id,
      pentagon_inv_hom_hom_hom_hom_assoc, Iso.inv_hom_id_assoc,
      pentagon_inv_assoc, pentagon_hom_hom_inv_hom_hom,
      whiskerLeft_inv_hom_assoc]
    -- Now we cancel out the outer morphisms that are jjust eqToHoms noise
    let V : F.map f ≫ eqToHom ?_ ⟶ F.map f ≫ η.app y ≫ θ.app y ≫ τ.app y := ?_
    slice_rhs 1 4 => change V
    simp only [assoc]
    rw [← cancel_epi (inv V), IsIso.inv_hom_id_assoc]
    let W : η.app x ≫ θ.app x ≫ τ.app x ≫ K.map f ⟶ eqToHom ?_ ≫ K.map f := ?_
    slice_rhs 9 16 => change W
    rw [← cancel_mono (inv W)]
    simp only [assoc, IsIso.hom_inv_id, comp_id]
    slice_lhs 1 7 => equals 𝟙 _ =>
      simp only [IsIso.inv_comp, inv_whiskerLeft, inv_eqToHom,
        IsIso.Iso.inv_hom, inv_whiskerRight, assoc, V, ← whiskerLeft_comp]
      conv_lhs => arg 2; equals 𝟙 _ =>
        have := eqToHom oy₁ ◁ (eqToHomTransIso oy₂ oy₃).hom ≫=
          associator_eqToHom_inv oy₁ oy₂ oy₃ =≫
          (eqToHomTransIso oy₁ oy₂).inv ▷ eqToHom oy₃
        simp only [assoc, hom_inv_whiskerRight, comp_id,
          whiskerLeft_hom_inv_assoc] at this
        simp [associator_hom_congr (f := η.app y) (h := τ.app y) rfl my₂ rfl,
          ← reassoc_of% this,
          associator_inv_congr my₁ my₂ my₃,
          congr_whiskerLeft my₁ (eqToHomTransIso oy₂ oy₃).hom,
          whiskerRight_congr my₃ (eqToHomTransIso oy₁ oy₂).inv]
      simp
    simp only [Category.assoc, id_comp]
    slice_lhs 9 17 => equals 𝟙 _ =>
      have n' := congr_arg (fun t ↦ t ▷ K.map f) <|
        associator_eqToHom_hom ox₁ ox₂ ox₃ =≫
          eqToHom ox₁ ◁ (eqToHomTransIso ox₂ ox₃).inv
      simp only [comp_whiskerRight, whisker_assoc, assoc,
        whiskerLeft_hom_inv, comp_id] at n'
      simp only [IsIso.inv_comp, inv_whiskerRight, IsIso.Iso.inv_inv,
        inv_eqToHom, assoc, inv_whiskerLeft, W]
      rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
        associator_inv_naturality_left_assoc, ← reassoc_of% n']
      simp only [eqToHom_whiskerRight, whiskerLeft_eqToHom, assoc,
        eqToHom_trans_assoc, eqToHom_refl, id_comp, Iso.inv_hom_id_assoc,
        pentagon_inv_hom_hom_hom_inv_assoc, whiskerLeft_comp, eqToHom_trans,
        pentagon_hom_hom_inv_hom_hom_assoc,
        associator_hom_congr (g := τ.app x) (h := K.map f)
          (congr_arg₂ (· ≫ ·) mx₁.symm mx₂.symm) rfl rfl,
        congr_whiskerLeft mx₁.symm ((eqToHomTransIso ox₂ ox₃).inv ▷ K.map f),
        associator_inv_congr (g := eqToHom t₆) (h := K.map f) mx₁.symm rfl rfl,
        associator_hom_congr mx₁.symm mx₂.symm
          (congr_arg₂ (· ≫ ·) mx₃.symm (rfl : K.map f = _)),
        associator_inv_congr (h := K.map f) mx₂.symm mx₃.symm rfl,
        congr_whiskerLeft mx₁.symm (α_ (θ.app x) (τ.app x) (K.map f)).inv]
      simp [← whiskerLeft_comp_assoc,
        associator_hom_congr (f := θ.app x) (h := K.map f)
          rfl mx₃.symm rfl]
    simp

attribute [local ext] Icon in
theorem comp_id {F G : LaxFunctor B C} (η : Icon F G) :
    (η.vComp (id G)) = η := by
  ext
  · simp [vComp, id, vCompApp, η.app_eq_eqToHom]
  · -- Deep in the DTT hell
    apply Function.hfunext rfl
    intro a a' h
    rw [heq_iff_eq] at h
    subst h
    apply Function.hfunext rfl
    intro b b' h
    rw [heq_iff_eq] at h
    subst h
    apply Function.hfunext rfl
    intro f f' h
    rw [heq_iff_eq] at h
    subst h
    rw [← conj_eqToHom_iff_heq]
    rotate_right 2
    · simp [vComp, id, vCompApp, η.app_eq_eqToHom]
    · simp [vComp, id, vCompApp, η.app_eq_eqToHom]
    · simp [vComp, vCompApp, vCompNaturality, OplaxTrans.vComp,
        OplaxTrans.vCompApp, OplaxTrans.vCompNaturality,
        eqToHomTransIso_refl_right (η.obj_eq b),
        eqToHomTransIso_refl_right (η.obj_eq a)];

attribute [local ext] Icon in
theorem id_comp {F G : LaxFunctor B C} (η : Icon F G) :
    ((id F).vComp η) = η := by
  ext
  · simp [vComp, id, vCompApp, η.app_eq_eqToHom]
  · apply Function.hfunext rfl
    intro a a' h
    rw [heq_iff_eq] at h
    subst h
    apply Function.hfunext rfl
    intro b b' h
    rw [heq_iff_eq] at h
    subst h
    apply Function.hfunext rfl
    intro f f' h
    rw [heq_iff_eq] at h
    subst h
    rw [← conj_eqToHom_iff_heq]
    rotate_right 2
    · simp [vComp, id, vCompApp, η.app_eq_eqToHom]
    · simp [vComp, id, vCompApp, η.app_eq_eqToHom]
    · simp [vComp, vCompApp, vCompNaturality, OplaxTrans.vComp,
      OplaxTrans.vCompApp, OplaxTrans.vCompNaturality,
      eqToHomTransIso_refl_left (η.obj_eq b),
      eqToHomTransIso_refl_left (η.obj_eq a),
      leftUnitor_inv_congr (η.app_eq_eqToHom b).symm,
      associator_hom_congr (f := 𝟙 (F.obj a)) (h := G.map f)
        rfl (η.app_eq_eqToHom a).symm rfl,
      leftUnitor_hom_congr
        (congr_arg₂ (· ≫ ·) (η.app_eq_eqToHom a).symm (rfl : G.map f = _))];

end Icon

end CategoryTheory.Lax
