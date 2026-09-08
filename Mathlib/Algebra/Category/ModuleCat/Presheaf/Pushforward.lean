/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings

/-!
# Pushforward of presheaves of modules

If `F : C ⥤ D`, the precomposition `F.op ⋙ _` induces a functor from presheaves
over `D` to presheaves over `C`. When `R : Dᵒᵖ ⥤ RingCat`, we define the
induced functor `pushforward₀ : PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} (F.op ⋙ R)`
on presheaves of modules.

In case we have a morphism of presheaves of rings `S ⟶ F.op ⋙ R`, we also construct
a functor `pushforward : PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} S`, and
we show that they interact with the composition of morphisms similarly as pseudofunctors.

-/

@[expose] public section

universe v v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

open CategoryTheory Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']

namespace PresheafOfModules

variable (F : C ⥤ D)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `pushforward₀`. -/
@[simps]
def pushforward₀Obj (R : Dᵒᵖ ⥤ RingCat.{u}) (M : PresheafOfModules R) :
    PresheafOfModules (F.op ⋙ R) :=
  { obj X := ↧(M.obj (F.op.obj X))
    map {X Y} f := M.map (F.op.map f)
    map_id X := by
      refine ModuleCat.hom_ext
        -- Work around an instance diamond for `restrictScalarsId'`
        (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun x => ?_))
      exact (M.congr_map_apply (F.op.map_id X) x).trans (by simp)
    map_comp := fun f g ↦ by
      refine ModuleCat.hom_ext
        -- Work around an instance diamond for `restrictScalarsId'`
        (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun x => ?_))
      exact (M.congr_map_apply (F.op.map_comp f g) x).trans (by simp) }

@[deprecated (since := "2026-04-27")] alias pushforward₀_obj := pushforward₀Obj

set_option backward.isDefEq.respectTransparency false in
/-- The pushforward functor on presheaves of modules for a functor `F : C ⥤ D` and
`R : Dᵒᵖ ⥤ RingCat`. On the underlying presheaves of abelian groups, it is induced
by the precomposition with `F.op`. -/
def pushforward₀ (R : Dᵒᵖ ⥤ RingCat.{u}) :
    PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} (F.op ⋙ R) where
  obj M := pushforward₀Obj F R M
  map {M₁ M₂} φ := { app X := φ.app _ }

/-- If `F : C ⥤ D` if a functor and `R : Dᵒᵖ ⥤ CommRingCat` is a presheaf
of commutative rings, this is the pushforward functor from the category
of presheaves of modules on `R` to the category of presheaves of
modules on `F.op ⋙ R`. -/
abbrev pushforward₀OfCommRingCat (R : Dᵒᵖ ⥤ CommRingCat.{u}) :
    PresheafOfModules.{v} (R ⋙ forget₂ _ _) ⥤
      PresheafOfModules.{v} ((F.op ⋙ R) ⋙ forget₂ _ _) :=
  pushforward₀ F (R ⋙ forget₂ _ _)

/-- The pushforward of presheaves of modules commutes with the forgetful functor
to presheaves of abelian groups. -/
noncomputable def pushforward₀CompToPresheaf (R : Dᵒᵖ ⥤ RingCat.{u}) :
    pushforward₀.{v} F R ⋙ toPresheaf _ ≅ toPresheaf _ ⋙ (whiskeringLeft _ _ _).obj F.op :=
  Iso.refl _

variable {F}
variable {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

attribute [local simp] pushforward₀ in
/-- The pushforward functor `PresheafOfModules R ⥤ PresheafOfModules S` induced by
a morphism of presheaves of rings `S ⟶ F.op ⋙ R`. -/
@[simps! obj_obj]
noncomputable def pushforward : PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} S :=
  pushforward₀ F R ⋙ restrictScalars φ

lemma forget₂_map_pushforward_obj_map {U V : Cᵒᵖ} (f : U ⟶ V) (M : PresheafOfModules R) :
    (forget₂ _ Ab).map (((PresheafOfModules.pushforward φ).obj M).map f) =
      M.presheaf.map (F.map f.unop).op :=
  rfl

lemma forget₂_map_pushforward_map_app {U : Cᵒᵖ} {M N : PresheafOfModules _} (g : M ⟶ N) :
    (forget₂ _ Ab).map (((pushforward φ).map g).app U) = (forget₂ _ Ab).map (g.app _) :=
  rfl

/-- The pushforward of presheaves of modules commutes with the forgetful functor
to presheaves of abelian groups. -/
noncomputable def pushforwardCompToPresheaf :
    pushforward.{v} φ ⋙ toPresheaf _ ≅ toPresheaf _ ⋙ (whiskeringLeft _ _ _).obj F.op :=
  Iso.refl _

lemma pushforward_obj_map_apply (M : PresheafOfModules.{v} R) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (m : (ModuleCat.restrictScalars (φ.app X).hom).obj (M.obj (Opposite.op (F.obj X.unop)))) :
      (((pushforward φ).obj M).map f).hom m = M.map (F.map f.unop).op m := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- `@[simp]`-normal form of `pushforward_obj_map_apply`. -/
@[simp]
lemma pushforward_obj_map_apply' (M : PresheafOfModules.{v} R) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (m : (ModuleCat.restrictScalars (φ.app X).hom).obj (M.obj (Opposite.op (F.obj X.unop)))) :
      DFunLike.coe
        (F := ↑((ModuleCat.restrictScalars _).obj _) →ₗ[_]
          ↑((ModuleCat.restrictScalars (S.map f).hom).obj ((ModuleCat.restrictScalars _).obj _)))
        (((pushforward φ).obj M).map f).hom m = M.map (F.map f.unop).op m := rfl

lemma pushforward_map_app_apply {M N : PresheafOfModules.{v} R} (α : M ⟶ N) (X : Cᵒᵖ)
    (m : (ModuleCat.restrictScalars (φ.app X).hom).obj (M.obj (Opposite.op (F.obj X.unop)))) :
    (((pushforward φ).map α).app X).hom m = α.app (Opposite.op (F.obj X.unop)) m := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- `@[simp]`-normal form of `pushforward_map_app_apply`. -/
@[simp]
lemma pushforward_map_app_apply' {M N : PresheafOfModules.{v} R} (α : M ⟶ N) (X : Cᵒᵖ)
    (m : (ModuleCat.restrictScalars (φ.app X).hom).obj (M.obj (Opposite.op (F.obj X.unop)))) :
    DFunLike.coe
      (F := ↑((ModuleCat.restrictScalars _).obj _) →ₗ[_] ↑((ModuleCat.restrictScalars _).obj _))
      (((pushforward φ).map α).app X).hom m = α.app (Opposite.op (F.obj X.unop)) m := rfl

section

variable (R) in
/-- The morphism of presheaves of rings `R ⟶ (𝟭 D).op ⋙ R` which is the identity on each
object: it is the left unitor of `R` composed with `Functor.opId`, see `pushforwardIdHom_eq`.
It is the datum along which the pushforward by the identity functor is taken. -/
@[simps]
def pushforwardIdHom : R ⟶ (𝟭 D).op ⋙ R where
  app X := 𝟙 _

variable (R) in
lemma pushforwardIdHom_eq :
    pushforwardIdHom R = R.leftUnitor.inv ≫ whiskerRight (Functor.opId D).inv R := by
  ext; simp

variable (R) in
/-- The pushforward functor by the identity morphism identifies to
the identity functor of the category of presheaves of modules. -/
noncomputable def pushforwardId : pushforward.{v} (pushforwardIdHom R) ≅ 𝟭 _ :=
  Iso.refl _

section

variable {T : Eᵒᵖ ⥤ RingCat.{u}} {G : D ⥤ E} (ψ : R ⟶ G.op ⋙ T)

/-- The morphism of presheaves of rings `S ⟶ (F ⋙ G).op ⋙ T` obtained by composing
`φ : S ⟶ F.op ⋙ R` and `ψ : R ⟶ G.op ⋙ T`, the associator and `Functor.opComp`
(see `pushforwardCompHom_eq`). It is the datum along which the pushforward by the
composition `F ⋙ G` is taken. -/
@[simps]
def pushforwardCompHom : S ⟶ (F ⋙ G).op ⋙ T where
  app X := φ.app X ≫ ψ.app (F.op.obj X)

lemma pushforwardCompHom_eq :
    pushforwardCompHom φ ψ = φ ≫ whiskerLeft F.op ψ ≫ (Functor.associator _ _ _).inv ≫
      whiskerRight (Functor.opComp F G).inv T := by
  ext; simp

/-- The composition of two pushforward functors on categories of presheaves of modules
identify to the pushforward for the composition. -/
noncomputable def pushforwardComp :
    pushforward.{v} ψ ⋙ pushforward.{v} φ ≅ pushforward.{v} (pushforwardCompHom φ ψ) :=
  Iso.refl _

end

section Transport

/-- Pushforwards along equal morphisms of presheaves of rings are isomorphic. -/
noncomputable def pushforwardCongr {φ ψ : S ⟶ F.op ⋙ R} (e : φ = ψ) :
    pushforward.{v} φ ≅ pushforward.{v} ψ :=
  NatIso.ofComponents
    (fun M ↦ isoMk (fun X ↦ (ModuleCat.restrictScalarsCongr (by rw [e])).app (M.obj (F.op.obj X)))
      (fun _ _ f ↦ by ext x; rfl))
    (fun f ↦ by ext X x; rfl)

@[simp]
lemma pushforwardCongr_symm {φ ψ : S ⟶ F.op ⋙ R} (e : φ = ψ) :
    (pushforwardCongr.{v} e).symm = pushforwardCongr e.symm := rfl

@[simp]
lemma pushforwardCongr_hom_app_app_apply {φ ψ : S ⟶ F.op ⋙ R} (e : φ = ψ)
    (M : PresheafOfModules.{v} R) (X : Cᵒᵖ) (x : ((pushforward φ).obj M).obj X) :
    ((pushforwardCongr e).hom.app M).app X x = x := by rfl

@[simp]
lemma pushforwardCongr_inv_app_app_apply {φ ψ : S ⟶ F.op ⋙ R} (e : φ = ψ)
    (M : PresheafOfModules.{v} R) (X : Cᵒᵖ) (x : ((pushforward ψ).obj M).obj X) :
    ((pushforwardCongr e).inv.app M).app X x = x := by rfl

variable {F' : C ⥤ D}

/-- A natural transformation `α : F' ⟶ F` induces a natural transformation between
the pushforward functors, from `pushforward φ` to the pushforward along
`φ ≫ whiskerRight (NatTrans.op α) R : S ⟶ F'.op ⋙ R`. -/
noncomputable def pushforwardNatTrans (α : F' ⟶ F) :
    pushforward.{v} φ ⟶ pushforward.{v} (φ ≫ whiskerRight (NatTrans.op α) R) where
  app M :=
    { app X := (ModuleCat.restrictScalars (φ.app X).hom).map (M.map (α.app X.unop).op) ≫
        (ModuleCat.restrictScalarsComp'App (φ.app X).hom (R.map (α.app X.unop).op).hom
          ((φ ≫ whiskerRight (NatTrans.op α) R).app X).hom (by simp)
          (M.obj (F'.op.obj X))).inv
      naturality := fun {X Y} i ↦ by
        ext x
        have h : F.op.map i ≫ (α.app Y.unop).op = (α.app X.unop).op ≫ F'.op.map i := by
          simp only [Functor.op_map, ← op_comp, α.naturality]
        exact (M.map_comp_apply (F.op.map i) (α.app Y.unop).op x).symm.trans
          ((M.congr_map_apply h x).trans (M.map_comp_apply (α.app X.unop).op (F'.op.map i) x)) }
  naturality _ _ f := by
    ext X x
    exact (naturality_apply f (α.app X.unop).op x).symm

@[simp]
lemma pushforwardNatTrans_app_app_apply (α : F' ⟶ F) (M : PresheafOfModules.{v} R) (X : Cᵒᵖ)
    (x : ((pushforward φ).obj M).obj X) :
    ((pushforwardNatTrans φ α).app M).app X x = M.map (α.app X.unop).op x := by rfl

/-- A natural isomorphism `α : F' ≅ F` induces an isomorphism between the pushforward
functors, from `pushforward φ` to the pushforward along
`φ ≫ whiskerRight (NatTrans.op α.hom) R : S ⟶ F'.op ⋙ R`. -/
@[simps hom]
noncomputable def pushforwardNatIso (α : F' ≅ F) :
    pushforward.{v} φ ≅ pushforward.{v} (φ ≫ whiskerRight (NatTrans.op α.hom) R) where
  hom := pushforwardNatTrans φ α.hom
  inv := pushforwardNatTrans _ α.inv ≫
    (pushforwardCongr (by ext : 2; simp [← Functor.map_comp, ← op_comp])).hom
  hom_inv_id := by
    ext M X x
    exact (M.map_comp_apply (α.hom.app X.unop).op (α.inv.app X.unop).op x).symm.trans
      ((M.congr_map_apply (show (α.hom.app X.unop).op ≫ (α.inv.app X.unop).op = 𝟙 _ by
        simp [← op_comp]) x).trans (M.map_id_apply _ x))
  inv_hom_id := by
    ext M X x
    exact (M.map_comp_apply (α.inv.app X.unop).op (α.hom.app X.unop).op x).symm.trans
      ((M.congr_map_apply (show (α.inv.app X.unop).op ≫ (α.hom.app X.unop).op = 𝟙 _ by
        simp [← op_comp]) x).trans (M.map_id_apply _ x))

/-- More flexible variant of `PresheafOfModules.pushforwardNatIso`: an isomorphism
`pushforward φ ≅ pushforward ψ` when `ψ : S ⟶ F'.op ⋙ R` is obtained from
`φ : S ⟶ F.op ⋙ R` by transport along an isomorphism `e : F' ≅ F`. Note that `e` goes from
the base functor of `ψ` to that of `φ`, which is why the coherence lemmas below transport
along `(associator ..).symm` and the inverses of the unitors. -/
noncomputable def pushforwardCongr₂ {ψ : S ⟶ F'.op ⋙ R} (e : F' ≅ F)
    (he : φ ≫ whiskerRight (NatTrans.op e.hom) R = ψ) :
    pushforward.{v} φ ≅ pushforward.{v} ψ :=
  pushforwardNatIso φ e ≪≫ pushforwardCongr he

@[simp]
lemma pushforwardCongr₂_hom_app_app_apply {ψ : S ⟶ F'.op ⋙ R} (e : F' ≅ F)
    (he : φ ≫ whiskerRight (NatTrans.op e.hom) R = ψ) (M : PresheafOfModules.{v} R) (X : Cᵒᵖ)
    (x : ((pushforward φ).obj M).obj X) :
    ((pushforwardCongr₂ φ e he).hom.app M).app X x = M.map (e.hom.app X.unop).op x := by rfl

end Transport

section Coherence

variable {T : Eᵒᵖ ⥤ RingCat.{u}} {G : D ⥤ E} (ψ : R ⟶ G.op ⋙ T)
  {T' : E'ᵒᵖ ⥤ RingCat.{u}} {G' : E ⥤ E'} (ψ' : T ⟶ G'.op ⋙ T')

lemma pushforwardCompHom_assoc :
    pushforwardCompHom (pushforwardCompHom φ ψ) ψ' ≫
      whiskerRight (NatTrans.op (associator F G G').inv) T' =
    pushforwardCompHom φ (pushforwardCompHom ψ ψ') := by
  ext; simp

lemma pushforward_assoc :
    isoWhiskerLeft (pushforward ψ') (pushforwardComp φ ψ) ≪≫
      pushforwardComp (pushforwardCompHom φ ψ) ψ' ≪≫
        pushforwardCongr₂ _ (associator F G G').symm (pushforwardCompHom_assoc φ ψ ψ') =
    (associator (pushforward ψ') (pushforward ψ) (pushforward φ)).symm ≪≫
      isoWhiskerRight (pushforwardComp ψ ψ') (pushforward φ) ≪≫
        pushforwardComp φ (pushforwardCompHom ψ ψ') := by
  ext M X x
  exact (M.congr_map_apply (show ((associator F G G').inv.app X.unop).op = 𝟙 _ by simp) x).trans
    (M.map_id_apply _ x)

lemma pushforwardCompHom_pushforwardIdHom_left :
    pushforwardCompHom (F := 𝟭 C) (pushforwardIdHom S) φ ≫
      whiskerRight (NatTrans.op (leftUnitor F).inv) R = φ := by
  ext; simp

lemma pushforwardCompHom_pushforwardIdHom_right :
    pushforwardCompHom (G := 𝟭 D) φ (pushforwardIdHom R) ≫
      whiskerRight (NatTrans.op (rightUnitor F).inv) R = φ := by
  ext; simp

lemma pushforward_comp_id :
    pushforwardComp.{v} (F := 𝟭 C) (pushforwardIdHom S) φ ≪≫
      pushforwardCongr₂ _ (leftUnitor F).symm (pushforwardCompHom_pushforwardIdHom_left φ) =
    isoWhiskerLeft (pushforward.{v} φ) (pushforwardId S) ≪≫ rightUnitor _ := by
  ext M X x
  exact (M.congr_map_apply (show ((leftUnitor F).inv.app X.unop).op = 𝟙 _ by simp) x).trans
    (M.map_id_apply _ x)

lemma pushforward_id_comp :
    pushforwardComp.{v} (G := 𝟭 D) φ (pushforwardIdHom R) ≪≫
      pushforwardCongr₂ _ (rightUnitor F).symm (pushforwardCompHom_pushforwardIdHom_right φ) =
    isoWhiskerRight (pushforwardId R) (pushforward.{v} φ) ≪≫ leftUnitor _ := by
  ext M X x
  exact (M.congr_map_apply (show ((rightUnitor F).inv.app X.unop).op = 𝟙 _ by simp) x).trans
    (M.map_id_apply _ x)

end Coherence

end

end PresheafOfModules
