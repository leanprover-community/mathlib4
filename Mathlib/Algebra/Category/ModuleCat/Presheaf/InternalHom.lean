/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-!
# Internal hom for presheaves of modules

This file constructs the internal hom for presheaves of modules over a presheaf of
commutative rings and proves that it is right adjoint to tensoring on the left.
-/

@[expose] public noncomputable section

universe v v₁ v₂ u₁ u₂ u

open CategoryTheory Functor Limits

namespace PresheafOfModulesOfCommRing

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- Restrict a presheaf of modules to the over category of an object. -/
abbrev over (M : PresheafOfModulesOfCommRing.{v} R) (X : C) :
    PresheafOfModulesOfCommRing.{v} ((Over.forget X).op ⋙ R) :=
  (pushforward.{v} (𝟙 _)).obj M

/-- Restrict a morphism of presheaves of modules to an over category. -/
abbrev overHom {M N : PresheafOfModulesOfCommRing.{v} R} (φ : M ⟶ N)
    (X : C) : M.over X ⟶ N.over X := (pushforward.{v} (𝟙 _)).map φ

variable (F : (PresheafOfModulesOfCommRing R))

open ConcreteCategory in
abbrev smulOver' (U : Cᵒᵖ) (F G : (PresheafOfModulesOfCommRing ((Over.forget U.unop).op ⋙ R))) :
    SMul (R.obj U) (F ⟶ G) where
  smul a φ := by
    fapply PresheafOfModulesOfCommRing.mkHom
    · intro V
      fapply ModuleCat.ofHom
      exact {
        toFun s := (R.map V.unop.hom.op a) • φ.app _ s
        map_add' := by simp
        map_smul' b s := by simp [smul_smul, mul_comm]
      }
    · intro U V f
      dsimp
      ext x
      dsimp +instances

      sorry


@[simps -isSimp]
instance smulOver (U : Cᵒᵖ) (F G : (PresheafOfModulesOfCommRing ((Over.forget U.unop).op ⋙ R))) :
    SMul (R.obj U) (F ⟶ G) where
  smul a φ := {
    app V := ModuleCat.ofHom {
      toFun s := (R.map V.unop.hom.op a) • φ.app _ s
      map_add' := by simp
      map_smul' b s := by
        simp [smul_smul, mul_comm]
    }
    naturality f := by
      ext x
      dsimp
      rw [PresheafOfModules.naturality_apply, G.map_smul]
      congr 1
      change R.map _ a = R.map f.unop.left.op (R.map _ a)
      rw [← comp_apply, ← R.map_comp, ← op_comp, f.unop.w]
  }

lemma over_smul_app_apply
    {U : Cᵒᵖ} {F G : (PresheafOfModulesOfCommRing.{v} ((Over.forget U.unop).op ⋙ R))}
    (a : R.obj U) (φ : F ⟶ G) {V : (Over U.unop)ᵒᵖ} (s : F.obj V) :
    (a • φ).app V s = R.map V.unop.hom.op a • φ.app _ s :=
  rfl

attribute [local simp] smulOver_smul_app

instance (U : Cᵒᵖ) :
    Linear (R.obj U) (PresheafOfModulesOfCommRing.{v} ((Over.forget U.unop).op ⋙ R)) where
  homModule F G :=
    { zero_smul _ := by ext; simp
      one_smul _ := by ext; simp
      mul_smul _ _ _ := by ext; simp [map_mul, mul_smul]
      add_smul _ _ _ := by ext; simp [add_smul]
      smul_zero _ := by ext; simp
      smul_add _ _ _ := by ext; simp}
  smul_comp _ _ _ _ _ _ := by ext; simp
  comp_smul _ _ _ _ _ _ := rfl

variable (F G : PresheafOfModulesOfCommRing.{u} R)

/-- Restrict a morphism on `Over U` along a morphism `V ⟶ U`. -/
@[simps]
def internalHomMap {U V : C} (f : V ⟶ U) (φ : F.over U ⟶ G.over U) :
    F.over V ⟶ G.over V where
  app W := φ.app ((Over.map f).op.obj W)
  naturality g := φ.naturality ((Over.map f).op.map g)

@[simp]
lemma internalHomMap_smul {U V : Cᵒᵖ} (f : U ⟶ V) (a : R.obj U)
    (φ : F.over U.unop ⟶ G.over U.unop) :
    F.internalHomMap G f.unop (a • φ) = R.map f a • F.internalHomMap G f.unop φ := by
  ext W x
  simp
  rfl

@[simp]
lemma internalHomMap_comp {U V W} (g : W ⟶ V) (f : V ⟶ U) (φ : F.over U ⟶ G.over U) :
    F.internalHomMap G (g ≫ f) φ = F.internalHomMap G g (F.internalHomMap G f φ) := by
  refine PresheafOfModules.hom_ext (fun _ ↦ ?_)
  simp only [internalHomMap_app]
  congr 1
  simp [Over.mapComp_eq]

@[simp]
lemma internalHomMap_id {U : C} (φ : F.over U ⟶ G.over U) :
    F.internalHomMap G (𝟙 U) φ = φ := by
  refine PresheafOfModules.hom_ext (fun _ ↦ ?_)
  simp only [internalHomMap_app]
  congr 1
  simp [Over.mapId_eq]

set_option backward.isDefEq.respectTransparency false in
/-- The internal hom of two presheaves of modules. Its sections over `U` are morphisms between
the restrictions of the two presheaves to `Over U.unop`. -/
@[simps]
def internalHom : PresheafOfModulesOfCommRing.{max u u₁ v₁} R where
  obj U := ModuleCat.of (R.obj U) (F.over U.unop ⟶ G.over U.unop)
  map {U V} f := ConcreteCategory.ofHom (C := ModuleCat (R.obj U))
    { toFun := internalHomMap _ _ f.unop
      map_add' _ _ := rfl
      map_smul' a φ := internalHomMap_smul _ _ _ _ _ }
  map_id _ := by ext x; simp [ModuleCat.restrictScalarsId'App_inv_apply (x := x)]
  map_comp _ _ := by ext; simp

open Opposite

/-- The functor that sends `G : PresheafOfModules` to `internalHom F G`. -/
@[simps]
def internalHomFunctor : PresheafOfModulesOfCommRing.{u} R ⥤
    PresheafOfModulesOfCommRing.{max u u₁ v₁} R where
  obj G := internalHom F G
  map φ :=
    { app V := ModuleCat.ofHom
        { toFun s := s ≫ overHom φ (unop V)
          map_smul' b s := by simp
          map_add' := by simp }
    }

/-- Internal version of the co-Yoneda functor `CategoryTheory.coyoneda` -/
@[simps]
def internalHomCoyoneda :
    (PresheafOfModulesOfCommRing.{u} R)ᵒᵖ ⥤
      PresheafOfModulesOfCommRing.{u} R ⥤
      PresheafOfModulesOfCommRing.{max u u₁ v₁} R where
  obj F := internalHomFunctor (unop F)
  map φ :=
    { app G :=
      { app V := ModuleCat.ofHom
          { toFun s := overHom φ.unop (unop V) ≫ s
            map_add' := by simp
            map_smul' := by simp
          }
      }
    }

end PresheafOfModulesOfCommRing

section Monoidal

open PresheafOfModulesOfCommRing PresheafOfModules MonoidalCategory Opposite

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (F : PresheafOfModulesOfCommRing.{u} R)

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {F G M : PresheafOfModulesOfCommRing.{u} R}

open ModuleCat.MonoidalCategory

@[simp]
lemma overMap_obj_mk_id {U V : C} (f : V ⟶ U) :
    (Over.map f).obj (Over.mk (𝟙 V)) = Over.mk f := by
  change Over.mk (𝟙 V ≫ f) = Over.mk f
  simp

lemma overMap_obj_mk_id_hom {U : C} (W : Over U) :
    (Over.map W.hom).obj (Over.mk (𝟙 W.left)) = W := by
  change Over.mk (𝟙 W.left ≫ W.hom) = W
  rw [Category.id_comp]
  cases W
  rfl

lemma over_map_homMk_id_apply (M : PresheafOfModulesOfCommRing.{u} R)
    {U V : Cᵒᵖ} (f : U ⟶ V) (m : M.obj U) :
    (M.over U.unop).map
        (Over.homMk f.unop :
          (Over.map f.unop).obj (Over.mk (𝟙 V.unop)) ⟶ Over.mk (𝟙 U.unop)).op m =
      M.map f m := rfl

lemma over_hom_op_eq_comp {U : C} {W W' : (Over U)ᵒᵖ} (g : W ⟶ W') :
    W'.unop.hom.op = W.unop.hom.op ≫ (Over.forget U).op.map g := by
  apply Quiver.Hom.unop_inj
  cat_disch

lemma internalHomMap_app_mk_id_apply {U V : C} (f : V ⟶ U)
    (φ : F.over U ⟶ G.over U) (x : F.obj (op V)) :
    (internalHomMap F G f φ).app (op (Over.mk (𝟙 V))) x =
      φ.app (op (Over.mk f)) x := by
  dsimp [internalHomMap]
  congr
  exact overMap_obj_mk_id f

lemma internalHomMap_app_mk_id_hom_apply {U : C} (W : (Over U)ᵒᵖ)
    (φ : F.over U ⟶ G.over U) (x : (F.over U).obj W) :
    (internalHomMap F G W.unop.hom φ).app (op (Over.mk (𝟙 W.unop.left))) x =
      φ.app W x := by
  dsimp [internalHomMap]
  congr
  exact overMap_obj_mk_id_hom W.unop

/-- The coevaluation map for the closed structure on presheaves of modules. -/
noncomputable def internalHomCoev' (F M : PresheafOfModulesOfCommRing.{u} R) :
    M ⟶ internalHom F (F ⊗ M) := by
  fapply PresheafOfModulesOfCommRing.mkHom
  · intro U
    apply ModuleCat.ofHom (R := R.obj U)
    fconstructor
    · fconstructor
      · intro m
        fapply PresheafOfModulesOfCommRing.mkHom
        · intro W
          have := (unop W).1
          change (F.over (unop U)).obj W ⟶ (F ⊗ M).obj (op (unop W).1)
          sorry
        sorry
      sorry

    sorry
  sorry

/-- The coevaluation map for the closed structure on presheaves of modules. -/
noncomputable def internalHomCoev (F M : PresheafOfModulesOfCommRing.{u} R) :
    M ⟶ internalHom F (F ⊗ M) where
  app U :=
    letI : Module ((R ⋙ forget₂ CommRingCat RingCat).obj U)
        (F.over U.unop ⟶ (F ⊗ M).over U.unop) :=
      inferInstanceAs (Module (R.obj U) (F.over U.unop ⟶ (F ⊗ M).over U.unop))
    ModuleCat.ofHom
    { toFun := fun m =>
        { app W :=
            letI : CommRing (((Over.forget U.unop).op ⋙ R ⋙
                forget₂ CommRingCat RingCat).obj W) :=
              inferInstanceAs (CommRing (R.obj (op W.unop.left)))
            ModuleCat.ofHom
              { toFun := fun x =>
                (show F.obj (op W.unop.left) from x) ⊗ₜ[
                  ((Over.forget U.unop).op ⋙ R ⋙ forget₂ CommRingCat RingCat).obj W]
                  (show M.obj (op W.unop.left) from M.map W.unop.hom.op m)
                map_add' := by simp [TensorProduct.add_tmul]
                map_smul' := by
                  intro r x
                  rfl }
          naturality := by
            intro W W' g
            ext x
            dsimp
            erw [PresheafOfModules.Monoidal.tensorObj_map_tmul]
            change (F.map ((Over.forget U.unop).op.map g) x) ⊗ₜ[
                R.obj ((Over.forget U.unop).op.obj W')]
                  (M.map W'.unop.hom.op m) =
              (F.map ((Over.forget U.unop).op.map g) x) ⊗ₜ[
                R.obj ((Over.forget U.unop).op.obj W')]
                  (M.map ((Over.forget U.unop).op.map g) (M.map W.unop.hom.op m))
            congr 1
            calc
              M.map W'.unop.hom.op m =
                  M.map (W.unop.hom.op ≫ (Over.forget U.unop).op.map g) m := by
                rw [over_hom_op_eq_comp g]
                rfl
              _ = M.map ((Over.forget U.unop).op.map g) (M.map W.unop.hom.op m) :=
                M.map_comp_apply _ _ _ }
      map_add' := by
        intro m₁ m₂
        apply PresheafOfModules.hom_ext
        intro W
        ext x
        change (show F.obj (op W.unop.left) from x) ⊗ₜ[R.obj (op W.unop.left)]
            (M.map W.unop.hom.op (m₁ + m₂)) =
          (show F.obj (op W.unop.left) from x) ⊗ₜ[R.obj (op W.unop.left)]
              (M.map W.unop.hom.op m₁) +
            (show F.obj (op W.unop.left) from x) ⊗ₜ[R.obj (op W.unop.left)]
              (M.map W.unop.hom.op m₂)
        rw [_root_.map_add, TensorProduct.tmul_add]
      map_smul' := by
        intro r m
        apply PresheafOfModules.hom_ext
        intro W
        ext x
        erw [over_smul_app_apply]
        change (show F.obj (op W.unop.left) from x) ⊗ₜ[
            (R ⋙ forget₂ CommRingCat RingCat).obj (op W.unop.left)]
            (M.map W.unop.hom.op (r • m)) =
          (((R ⋙ forget₂ CommRingCat RingCat).map W.unop.hom.op) r) •
            ((show F.obj (op W.unop.left) from x) ⊗ₜ[
              (R ⋙ forget₂ CommRingCat RingCat).obj (op W.unop.left)]
              (M.map W.unop.hom.op m))
        erw [M.map_smul]
        rw [TensorProduct.tmul_smul]
        rfl }
  naturality := by
    intro U V f
    ext m
    apply PresheafOfModules.hom_ext
    intro W
    ext x
    change (show F.obj (op W.unop.left) from x) ⊗ₜ[R.obj (op W.unop.left)]
        (M.map W.unop.hom.op (M.map f m)) =
      (show F.obj (op W.unop.left) from x) ⊗ₜ[R.obj (op W.unop.left)]
        (M.map (f ≫ W.unop.hom.op) m)
    congr 1
    exact (M.map_comp_apply f W.unop.hom.op m).symm

/-- The component of the evaluation map for the closed structure on presheaves of modules. -/
noncomputable def internalHomEvApp (F G : PresheafOfModulesOfCommRing.{u} R)
    (U : Cᵒᵖ) : (F ⊗ internalHom F G).obj U ⟶ G.obj U :=
  tensorLift
    (fun x φ => φ.app (op (Over.mk (𝟙 U.unop))) x)
    (by intros; dsimp +instances; simp)
    (by intros; simp)
    (by intros; simp)
    (by
      intro r x φ
      rw [over_smul_app_apply]
      simp)

@[simp]
lemma internalHomEvApp_tmul (F G : PresheafOfModulesOfCommRing.{u} R)
    (U : Cᵒᵖ) (x : F.obj U) (φ : (internalHom F G).obj U) :
    internalHomEvApp F G U (x ⊗ₜ[R.obj U] φ) =
      φ.app (op (Over.mk (𝟙 U.unop))) x := rfl

@[simp]
lemma internalHomEvApp_map_tmul {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : F.obj U) (φ : (internalHom F G).obj U) :
    internalHomEvApp F G V
        ((F.map f x) ⊗ₜ[R.obj V] (internalHomMap F G f.unop φ)) =
      G.map f (internalHomEvApp F G U (x ⊗ₜ[R.obj U] φ)) := by
  erw [internalHomEvApp_tmul]
  erw [internalHomEvApp_tmul]
  have hφ := ConcreteCategory.congr_hom
    (φ.naturality
      (Over.homMk f.unop :
        (Over.map f.unop).obj (Over.mk (𝟙 V.unop)) ⟶ Over.mk (𝟙 U.unop)).op) x
  dsimp [internalHomMap] at hφ ⊢
  change ((internalHomMap F G f.unop φ).app (op (Over.mk (𝟙 V.unop)))) (F.map f x) =
    G.map f (φ.app (op (Over.mk (𝟙 U.unop))) x)
  rw [← over_map_homMk_id_apply F f x,
    ← over_map_homMk_id_apply G f (φ.app (op (Over.mk (𝟙 U.unop))) x)]
  exact hφ

/-- The evaluation map for the closed structure on presheaves of modules. -/
noncomputable def internalHomEv (F G : PresheafOfModulesOfCommRing.{u} R) :
    F ⊗ internalHom F G ⟶ G where
  app U := internalHomEvApp F G U
  naturality := by
    intro U V f
    apply tensor_ext
    intro x φ
    have htensor := PresheafOfModules.Monoidal.tensorObj_map_tmul
      (M₁ := F) (M₂ := internalHom F G) f x φ
    change internalHomEvApp F G V (((F ⊗ internalHom F G).map f) (x ⊗ₜ φ)) =
      G.map f (internalHomEvApp F G U (x ⊗ₜ φ))
    erw [htensor]
    exact internalHomEvApp_map_tmul (F := F) (G := G) f x φ

@[simp, nolint simpNF]
lemma internalHomCoev_app_apply_app_apply
    (F M : PresheafOfModulesOfCommRing.{u} R) (U : Cᵒᵖ)
    (m : M.obj U) (W : (Over U.unop)ᵒᵖ) (x : (F.over U.unop).obj W) :
    ((internalHomCoev F M).app U m).app W x =
      (show F.obj (op W.unop.left) from x) ⊗ₜ
        (show M.obj (op W.unop.left) from M.map W.unop.hom.op m) := rfl

lemma internalHomEvApp_coev_tmul (F M : PresheafOfModulesOfCommRing.{u} R)
    (U : Cᵒᵖ) (x : F.obj U) (m : M.obj U) :
    internalHomEvApp F (F ⊗ M) U
        (x ⊗ₜ[R.obj U] ((internalHomCoev F M).app U m)) =
      x ⊗ₜ[R.obj U] m := by
  erw [internalHomEvApp_tmul]
  rw [internalHomCoev_app_apply_app_apply]
  congr
  exact ConcreteCategory.congr_hom (M.map_id U) m

@[simp, nolint simpNF]
lemma internalHomEv_app_tmul (F G : PresheafOfModulesOfCommRing.{u} R)
    (U : Cᵒᵖ) (x : F.obj U) (φ : (internalHom F G).obj U) :
    (internalHomEv F G).app U (x ⊗ₜ[R.obj U] φ) =
      φ.app (op (Over.mk (𝟙 U.unop))) x := internalHomEvApp_tmul F G U x φ

/-- The adjunction `F ⊗ - ⊣ internalHom F -` for presheaves of modules. -/
noncomputable def internalHomAdjunction (F : PresheafOfModulesOfCommRing.{u} R) :
    MonoidalCategory.tensorLeft F ⊣ internalHomFunctor F where
  unit :=
    { app := fun M => internalHomCoev F M
      naturality := by
        intro X Y f
        ext U m
        apply PresheafOfModules.hom_ext
        intro W
        ext x
        change (show F.obj (op W.unop.left) from x) ⊗ₜ[R.obj (op W.unop.left)]
            (Y.map W.unop.hom.op (f.app U m)) =
          (show F.obj (op W.unop.left) from x) ⊗ₜ[R.obj (op W.unop.left)]
            (f.app (op W.unop.left) (X.map W.unop.hom.op m))
        congr 1
        exact (naturality_apply f W.unop.hom.op (show X.obj U from m)).symm }
  counit :=
    { app := fun G => internalHomEv F G
      naturality := by
        intro X Y f
        ext U z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul x φ =>
            change internalHomEvApp F Y U
                (x ⊗ₜ (((internalHomFunctor F).map f).app U φ)) =
              f.app U (internalHomEvApp F X U (x ⊗ₜ φ))
            erw [internalHomEvApp_tmul]
        | add z₁ z₂ hz₁ hz₂ =>
            rw [_root_.map_add, _root_.map_add, hz₁, hz₂] }
  left_triangle_components M := by
    ext U z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x m =>
        change internalHomEvApp F (F ⊗ M) U
            (x ⊗ₜ ((internalHomCoev F M).app U m)) = x ⊗ₜ m
        exact internalHomEvApp_coev_tmul F M U x m
    | add z₁ z₂ hz₁ hz₂ =>
        rw [_root_.map_add, _root_.map_add, hz₁, hz₂]
  right_triangle_components G := by
    ext U φ
    apply PresheafOfModules.hom_ext
    intro W
    ext x
    change ((internalHomMap F G W.unop.hom φ).app (op (Over.mk (𝟙 W.unop.left)))) x =
      φ.app W x
    simpa using internalHomMap_app_mk_id_hom_apply (F := F) (G := G) W φ x

@[simp]
lemma internalHomAdjunction_unit_app (F M : PresheafOfModulesOfCommRing.{u} R) :
    (internalHomAdjunction F).unit.app M = internalHomCoev F M := rfl

@[simp]
lemma internalHomAdjunction_counit_app (F G : PresheafOfModulesOfCommRing.{u} R) :
    (internalHomAdjunction F).counit.app G = internalHomEv F G := rfl

end Monoidal
