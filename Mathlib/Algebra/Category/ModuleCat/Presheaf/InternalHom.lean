/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# The internal hom for presheaves of modules


-/

@[expose] public section

open CategoryTheory Category Opposite

universe w v u v₁ u₁

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

namespace PresheafOfModules

noncomputable section

/-- Given `X : C`, this is the presheaf of modules on `Over X` that
is obtained from a presheaf of modules on `C`. -/
abbrev over {S : Cᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{v} S) (X : C) :
    PresheafOfModules.{v} ((Over.forget X).op ⋙ S) :=
  (pushforward.{v} (F := Over.forget X) (𝟙 _)).obj M

/-- The induced map on the restrictions presheaves of modules to `Over X` -/
abbrev Hom.over {S : Cᵒᵖ ⥤ RingCat.{u}} {M N : PresheafOfModules.{v} S} (φ : M ⟶ N)
    (X : C) : M.over X ⟶ N.over X :=
  (pushforward.{v} (F := Over.forget X) (𝟙 _)).map φ

@[simps -isSimp]
instance smulOver (U : Cᵒᵖ)
    (F G : (PresheafOfModules ((Over.forget U.unop).op ⋙ R ⋙ forget₂ _ _))) :
    SMul (R.obj U) (F ⟶ G) where
  smul a φ :=
    { app V := ModuleCat.ofHom
        { toFun s :=
            (show ((Over.forget (unop U)).op ⋙ R ⋙
                forget₂ CommRingCat RingCat).obj V from R.map V.unop.hom.op a) • φ.app _ s
          map_smul' b s := by dsimp at b; simp [smul_smul, mul_comm b]
          map_add' := by simp }
      naturality f := by
        ext x
        have := ConcreteCategory.congr_hom (φ.naturality f) x
        rw [ConcreteCategory.comp_apply] at this
        dsimp at this ⊢
        simp only [this, map_smul, ModuleCat.restrictScalars.smul_def,
          ← ConcreteCategory.comp_apply, ← R.map_comp, ← op_comp, Over.w] }

lemma over_smul_app_apply
    {U : Cᵒᵖ} {F G : (PresheafOfModules.{w} ((Over.forget U.unop).op ⋙ R ⋙ forget₂ _ _))}
    (a : R.obj U) (φ : F ⟶ G) {V : (Over U.unop)ᵒᵖ} (s : F.obj V) :
    (a • φ).app V s =
      letI b : ((Over.forget (unop U)).op ⋙ R ⋙ forget₂ CommRingCat RingCat).obj V :=
        R.map V.unop.hom.op a
      b • φ.app _ s :=
  rfl

attribute [local simp] smulOver_smul_app

open ConcreteCategory

instance (U : Cᵒᵖ) :
    Linear (R.obj U) (PresheafOfModules ((Over.forget U.unop).op ⋙ R ⋙ forget₂ _ _)) where
  homModule F G :=
    { zero_smul _ := by ext; simp
      one_smul _ := by ext; simp
      mul_smul _ _ _ := by ext; simp [map_mul, mul_smul]
      add_smul _ _ _ := by ext; simp [map_add, add_smul]
      smul_zero _ := by ext; exact smul_zero _
      smul_add _ _ _ := by ext; exact smul_add _ _ _ }
  smul_comp _ _ _ _ _ _ := by
    ext
    dsimp
    rw [comp_app]
    dsimp
    rw [map_smul]
    rfl
  comp_smul _ _ _ _ _ _ := rfl

variable (F G : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

/-- The restriction map sending `φ : F.over U ⟶ G.over U` to `F.over V ⟶ G.over V` -/
@[simps]
def internalHomMap {U V : C} (f : V ⟶ U) (φ : F.over U ⟶ G.over U) :
    F.over V ⟶ G.over V where
  app W := φ.app ((Over.map f).op.obj W)
  naturality g := φ.naturality ((Over.map f).op.map g)

/-- The Hom presheaf for presheaves of modules. Given `F G : PresheafOfModules`, this is the
sheaf whose value on `U : Cᵒᵖ` is `F.over U.unop ⟶ G.over U.unop` and whose restriction maps
are `internalHomMap`. Note that `internalHom` lives in the universe `max u u₁ v₁` so it is
only truly "internal" when `C` is a small category of type `u`. -/
@[simps]
def internalHom : PresheafOfModules.{max u u₁ v₁} (R ⋙ forget₂ _ _) where
  obj U := ModuleCat.of (R.obj U) (F.over U.unop ⟶ G.over U.unop)
  map {U V} f := ConcreteCategory.ofHom (C := ModuleCat (R.obj U))
    { toFun := internalHomMap _ _ f.unop
      map_add' _ _ := rfl
      map_smul' _ _ := PresheafOfModules.hom_ext (fun _ ↦ by
        ext
        erw [over_smul_app_apply, over_smul_app_apply]
        dsimp
        rw [Functor.map_comp]
        rfl ) }
  map_id _ := by
    ext
    refine PresheafOfModules.hom_ext (fun _ ↦ ?_)
    dsimp
    congr
    simp [Over.mapId_eq]
  map_comp {X₁ X₂ X₃} f g := by
    ext
    refine PresheafOfModules.hom_ext (fun _ ↦ ?_)
    dsimp
    congr 2
    simp [Over.mapComp_eq]

/-- This is the functor that sends `G : PresheafOfModules` to `internalHom F G`.
TODO: Show this is right adjoint to `MonoidalCategory.tensorLeft F`, giving `PresheafOfModules`
the structure of a closed monoidal category. -/
@[simps]
def internalHomFunctor : PresheafOfModules.{u} (R ⋙ forget₂ _ _) ⥤
    PresheafOfModules.{max u u₁ v₁} (R ⋙ forget₂ _ _) where
  obj G := internalHom F G
  map φ :=
    { app V := ModuleCat.ofHom
        { toFun s := s ≫ φ.over (unop V)
          map_smul' b s := by simp
          map_add' := by simp }
    }

/-- Internal version of the co-Yoneda functor `CategoryTheory.coyoneda` -/
@[simps]
def internalHomCoyoneda :
    (PresheafOfModules.{u} (R ⋙ forget₂ _ _))ᵒᵖ ⥤
      PresheafOfModules.{u} (R ⋙ forget₂ _ _) ⥤
      PresheafOfModules.{max u u₁ v₁} (R ⋙ forget₂ _ _) where
  obj F := internalHomFunctor (unop F)
  map φ :=
    { app G :=
      { app V := ModuleCat.ofHom
          { toFun s := φ.unop.over (unop V) ≫ s
            map_add' := by simp
            map_smul' := by simp
          }
      }
    }

variable {J : GrothendieckTopology C} [J.HasSheafCompose (forget AddCommGrpCat.{u})]

/-- If a morphism between the underlying presheaves on `Over X` is locally equal to
module-linear morphisms, then it is module-linear. -/
lemma internalHom_isLinear_of_locally
    (hG : Presheaf.IsSheaf J G.presheaf) {X : C} {S : Sieve X} (hS : S ∈ J X)
    (x : Presieve.FamilyOfElements ((internalHom F G).presheaf ⋙ forget AddCommGrpCat)
      S.arrows) {y' : (presheafHom F.presheaf G.presheaf).obj (op X)}
    (hy' : ∀ (Y : C) (g : Y ⟶ X) (hg : S.arrows g),
      y'.app (op (Over.mk g)) = ((toPresheaf _).map (x g hg)).app (op (Over.mk (𝟙 Y)))) :
    ∃ φ : F.over X ⟶ G.over X, (toPresheaf _).map φ = y' := by
  refine ⟨homMk y' ?_, rfl⟩
  intro W r m
  apply hG.isSeparated W.unop.left (S.pullback W.unop.hom)
    (J.pullback_stable W.unop.hom hS)
  intro Z p hp
  letI : Module (((Over.forget X).op ⋙ R ⋙ forget₂ CommRingCat RingCat).obj W)
      (((Over.forget X).op ⋙ G.presheaf).obj W) :=
    inferInstanceAs (Module _ ((G.over X).obj W))
  letI : Module (((Over.forget X).op ⋙ R ⋙ forget₂ CommRingCat RingCat).obj W)
      (((Over.forget X).op ⋙ F.presheaf).obj W) :=
    inferInstanceAs (Module _ ((F.over X).obj W))
  letI : Module (R.obj (op Z)) (G.presheaf.obj (op Z)) :=
    inferInstanceAs (Module (R.obj (op Z)) (G.obj (op Z)))
  letI : Module (R.obj (op Z)) (F.presheaf.obj (op Z)) :=
    inferInstanceAs (Module (R.obj (op Z)) (F.obj (op Z)))
  let V : Over X := Over.mk (p ≫ W.unop.hom)
  let i : V ⟶ W.unop := Over.homMk p
  have hnat₁ := ConcreteCategory.congr_hom (y'.naturality i.op) (r • m)
  have hnat₂ := ConcreteCategory.congr_hom (y'.naturality i.op) m
  dsimp [V, i] at hnat₁ hnat₂
  change (G.presheaf.map p.op).hom (y'.app W (r • m)) =
    (G.presheaf.map p.op).hom (r • (y'.app W m : (G.over X).obj W))
  rw [show (G.presheaf.map p.op).hom (r • (y'.app W m : (G.over X).obj W)) =
    R.map p.op r • (G.presheaf.map p.op).hom (y'.app W m) from G.map_smul p.op r _]
  change (G.presheaf.map p.op).hom ((y'.app W).hom (r • m)) =
    R.map p.op r • (G.presheaf.map p.op).hom ((y'.app W).hom m)
  refine hnat₁.symm.trans ?_
  erw [F.map_smul p.op r m]
  refine Eq.trans ?_ (congrArg (fun t => R.map p.op r • t) hnat₂)
  rw [hy' Z (p ≫ W.unop.hom) hp]
  exact ((x (p ≫ W.unop.hom) hp).app (op (Over.mk (𝟙 Z)))).hom.map_smul _ _

theorem internalHom_presheaf_isSheaf (hG : Presheaf.IsSheaf J G.presheaf) :
    Presheaf.IsSheaf J (internalHom F G).presheaf := by
  rw [Presheaf.isSheaf_iff_isSheaf_comp J _ (forget _ ⋙
    uliftFunctor.{max v₁ u₁, max u u₁ v₁}), isSheaf_iff_isSheaf_of_type]
  refine Presieve.isSheaf_comp_uliftFunctor (P := (F.internalHom G).presheaf ⋙ forget Ab) J ?_
  intro X S hS x hx
  let x' : Presieve.FamilyOfElements (presheafHom F.presheaf G.presheaf)
      S.arrows := fun Y f hf => (toPresheaf _).map (x f hf)
  have hx' : x'.Compatible := by
    intro Y₁ Y₂ W g₁ g₂ f₁ f₂ hf₁ hf₂ w
    dsimp [x']
    exact congrArg ((toPresheaf _).map) (hx g₁ g₂ hf₁ hf₂ w)
  obtain ⟨y', hy', hyuniq'⟩ := presheafHom_isSheafFor F.presheaf G.presheaf S
    (fun _ f => ((Presheaf.isSheaf_iff_isLimit J G.presheaf).1 hG _
      (J.pullback_stable f hS)).some) x' hx'
  rw [PresheafHom.isAmalgamation_iff S x' hx'] at hy'
  obtain ⟨y, hy_toPresheaf⟩ := internalHom_isLinear_of_locally _ _ hG hS x hy'
  refine ⟨y, ?_, ?_⟩
  · intro Y f hf
    apply (toPresheaf _).map_injective
    change (presheafHom F.presheaf G.presheaf).map f.op
        ((toPresheaf _).map y) = x' f hf
    rw [hy_toPresheaf]
    exact ((PresheafHom.isAmalgamation_iff S x' hx' y').2 hy') f hf
  · intro y₂ hy₂
    apply (toPresheaf _).map_injective
    change (toPresheaf _).map y₂ = (toPresheaf _).map y
    rw [hy_toPresheaf]
    exact hyuniq' ((toPresheaf _).map y₂) (fun Y f hf =>
      congrArg ((toPresheaf _).map) (hy₂ f hf))

end

end PresheafOfModules
