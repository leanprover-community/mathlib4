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

The equivalence `PresheafOfModulesOfCommRing.internalHomEquiv` is given by currying and
uncurrying. The unit and counit of `internalHomAdjunction` are the coevaluation and
evaluation morphisms `PresheafOfModulesOfCommRing.internalHomCoev` and
`PresheafOfModulesOfCommRing.internalHomEv`.
-/

@[expose] public noncomputable section

universe v v₁ v₂ u₁ u₂ u

open CategoryTheory Functor Limits

namespace PresheafOfModulesOfCommRing

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- Restrict a presheaf of modules to the over category of an object. -/
abbrev over (M : PresheafOfModulesOfCommRing.{v} R) (X : C) :
    PresheafOfModulesOfCommRing.{v} ((Over.forget X).op ⋙ R) :=
  (pushforward₀.{v} (Over.forget X) R).obj M

/-- Restrict a morphism of presheaves of modules to an over category. -/
abbrev overHom {M N : PresheafOfModulesOfCommRing.{v} R} (φ : M ⟶ N)
    (X : C) : M.over X ⟶ N.over X := (pushforward₀.{v} (Over.forget X) R).map φ

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
    naturality {V W} f := by
      ext x
      dsimp
      rw [naturality_apply, G.map_smul]
      congr 1
      calc
        R.map W.unop.hom.op a = R.map (V.unop.hom.op ≫ f.unop.left.op) a := by
          rw [← op_comp, f.unop.w]
        _ = R.map f.unop.left.op (R.map V.unop.hom.op a) :=
          ConcreteCategory.congr_hom (R.map_comp _ _) a
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

set_option backward.isDefEq.respectTransparency false

variable {F G M : PresheafOfModulesOfCommRing.{u} R}

namespace PresheafOfModulesOfCommRing

/-- Restricting an internal hom and evaluating at the identity gives its component
at the restriction morphism. -/
lemma internalHomMap_app_mkId {U V : C} (f : V ⟶ U) (φ : F.over U ⟶ G.over U)
    (x : F.obj (op V)) :
    (F.internalHomMap G f φ).app (op (Over.mk (𝟙 V))) x =
      φ.app (op (Over.mk f)) x :=
  congrArg (β := G.obj (op V))
    (fun g : V ⟶ U ↦ φ.app (op (Over.mk g)) x) (Category.id_comp f)

/-- The evaluation morphism for the internal hom of presheaves of modules. -/
def internalHomEv (F G : PresheafOfModulesOfCommRing.{u} R) :
    F ⊗ internalHom F G ⟶ G :=
  tensorLift (fun U x φ ↦ φ.app (op (Over.mk (𝟙 U.unop))) x)
    (by intros; exact map_add _ _ _)
    (by intros; exact map_smul _ _ _)
    (by intros; rfl)
    (by
      intro U a x φ
      rw [over_smul_app_apply]
      simp)
    (by
      intro U V f x φ
      refine (internalHomMap_app_mkId f.unop φ (F.map f x)).trans ?_
      exact naturality_apply φ
        (Over.homMk (U := Over.mk f.unop) (V := Over.mk (𝟙 U.unop)) f.unop).op x)

@[simp]
lemma internalHomEv_app_tmul (F G : PresheafOfModulesOfCommRing.{u} R)
    (U : Cᵒᵖ) (x : F.obj U) (φ : (internalHom F G).obj U) :
    dsimp% (internalHomEv F G).app U (x ⊗ₜ[R.obj U] φ) =
      φ.app (op (Over.mk (𝟙 U.unop))) x := rfl

/-- A section of `M` over `U` induces a morphism on `Over U.unop` by restricting the
section and applying a morphism out of `F ⊗ M`. -/
def internalHomCurryHom (f : F ⊗ M ⟶ G) (U : Cᵒᵖ) (m : M.obj U) :
    F.over U.unop ⟶ G.over U.unop :=
  mkHom (fun W ↦ ModuleCat.ofHom
    { toFun x := f.app _ (x ⊗ₜ M.map W.unop.hom.op m)
      map_add' := by intro x y; simp +instances [TensorProduct.add_tmul]
      map_smul' := by intro r x; simp +instances [← TensorProduct.smul_tmul'] })
    (fun {W W'} g ↦ by
      ext x
      calc
        f.app (op W'.unop.left) (F.map g.unop.left.op x ⊗ₜ
            M.map W'.unop.hom.op m) =
            f.app (op W'.unop.left) (F.map g.unop.left.op x ⊗ₜ
              M.map g.unop.left.op (M.map W.unop.hom.op m)) := by
          congr 2
          exact (M.congr_map_apply (congrArg Quiver.Hom.op g.unop.w).symm m).trans
            (M.map_comp_apply W.unop.hom.op g.unop.left.op m)
        _ = _ := naturality_apply f g.unop.left.op (x ⊗ₜ M.map W.unop.hom.op m))

@[simp]
lemma internalHomCurryHom_app_apply (f : F ⊗ M ⟶ G) (U : Cᵒᵖ) (m : M.obj U)
    (W : (Over U.unop)ᵒᵖ) (x : (F.over U.unop).obj W) :
    dsimp% (internalHomCurryHom f U m).app W x =
      f.app _ (x ⊗ₜ[R.obj (op W.unop.left)] M.map W.unop.hom.op m) := rfl

/-- Currying a morphism out of a tensor product of presheaves of modules. -/
def internalHomCurry (f : F ⊗ M ⟶ G) : M ⟶ internalHom F G :=
  mkHom (fun U ↦ ModuleCat.ofHom (R := R.obj U)
    { toFun := internalHomCurryHom f U
      map_add' := by
        intro m n
        ext W x
        dsimp [internalHomCurryHom]
        simp +instances [TensorProduct.tmul_add]
        rfl
      map_smul' := by
        intro r m
        apply PresheafOfModules.hom_ext
        intro W
        apply ConcreteCategory.hom_ext
        intro x
        rw [over_smul_app_apply]
        simp })
    (fun g ↦ by
      ext m
      apply PresheafOfModules.hom_ext
      intro W
      ext x
      exact congrArg (fun n ↦ f.app (op W.unop.left) (x ⊗ₜ n))
        (M.map_comp_apply g W.unop.hom.op m).symm)

@[simp]
lemma internalHomCurry_app_apply_app_apply (f : F ⊗ M ⟶ G) (U : Cᵒᵖ) (m : M.obj U)
    (W : (Over U.unop)ᵒᵖ) (x : (F.over U.unop).obj W) :
    dsimp% ((internalHomCurry f).app U m).app W x =
      f.app _ (x ⊗ₜ[R.obj (op W.unop.left)] M.map W.unop.hom.op m) := rfl

/-- Uncurrying a morphism into the internal hom of presheaves of modules. -/
def internalHomUncurry (f : M ⟶ internalHom F G) : F ⊗ M ⟶ G :=
  F ◁ f ≫ internalHomEv F G

@[simp]
lemma internalHomUncurry_app_tmul (f : M ⟶ internalHom F G)
    (U : Cᵒᵖ) (x : F.obj U) (m : M.obj U) :
    dsimp% (internalHomUncurry f).app U (x ⊗ₜ[R.obj U] m) =
      (f.app U m).app (op (Over.mk (𝟙 U.unop))) x := rfl

@[simp]
lemma internalHomUncurry_curry (f : F ⊗ M ⟶ G) :
    internalHomUncurry (internalHomCurry f) = f := by
  apply tensor_ext
  intro U x m
  simpa +instances using
    internalHomCurry_app_apply_app_apply f U m (op (Over.mk (𝟙 U.unop))) x

@[simp]
lemma internalHomCurry_uncurry (f : M ⟶ internalHom F G) :
    internalHomCurry (internalHomUncurry f) = f := by
  ext U m
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  exact (congrArg
    (fun φ : F.over W.unop.left ⟶ G.over W.unop.left ↦
      φ.app (op (Over.mk (𝟙 W.unop.left))) x)
    (naturality_apply f W.unop.hom.op m)).trans
      (internalHomMap_app_mkId W.unop.hom (f.app U m) x)

/-- The tensor–internal hom equivalence for presheaves of modules. -/
@[simps apply symm_apply]
def internalHomEquiv (F M G : PresheafOfModulesOfCommRing.{u} R) :
    (F ⊗ M ⟶ G) ≃ (M ⟶ internalHom F G) where
  toFun := internalHomCurry
  invFun := internalHomUncurry
  left_inv := internalHomUncurry_curry
  right_inv := internalHomCurry_uncurry

/-- The coevaluation morphism for the internal hom of presheaves of modules. -/
def internalHomCoev (F M : PresheafOfModulesOfCommRing.{u} R) :
    M ⟶ internalHom F (F ⊗ M) :=
  internalHomCurry (𝟙 (F ⊗ M))

@[simp]
lemma internalHomCoev_app_apply_app_apply (F M : PresheafOfModulesOfCommRing.{u} R)
    (U : Cᵒᵖ) (m : M.obj U) (W : (Over U.unop)ᵒᵖ) (x : (F.over U.unop).obj W) :
    dsimp% ((internalHomCoev F M).app U m).app W x =
      x ⊗ₜ[R.obj (op W.unop.left)] M.map W.unop.hom.op m := rfl

end PresheafOfModulesOfCommRing

/-- The adjunction `F ⊗ - ⊣ internalHom F -` for presheaves of modules. -/
def internalHomAdjunction (F : PresheafOfModulesOfCommRing.{u} R) :
    MonoidalCategory.tensorLeft F ⊣ internalHomFunctor F :=
  Adjunction.mkOfHomEquiv
    { homEquiv := internalHomEquiv F
      homEquiv_naturality_left_symm := by
        intros
        apply PresheafOfModulesOfCommRing.tensor_ext
        intros
        rfl
      homEquiv_naturality_right := by
        intros
        ext U m
        apply PresheafOfModules.hom_ext
        intro W
        ext x
        rfl }

@[simp]
lemma internalHomAdjunction_homEquiv (F M G : PresheafOfModulesOfCommRing.{u} R) :
    (internalHomAdjunction F).homEquiv M G = internalHomEquiv F M G := by
  simp [internalHomAdjunction]

@[simp]
lemma internalHomAdjunction_unit_app (F M : PresheafOfModulesOfCommRing.{u} R) :
    (internalHomAdjunction F).unit.app M = internalHomCoev F M := rfl

@[simp]
lemma internalHomAdjunction_counit_app (F G : PresheafOfModulesOfCommRing.{u} R) :
    (internalHomAdjunction F).counit.app G = internalHomEv F G := by
  simp [internalHomAdjunction, internalHomEquiv, internalHomUncurry]

noncomputable instance : MonoidalClosed (PresheafOfModulesOfCommRing.{u} R) where
  closed F := {
    rightAdj := internalHomFunctor F
    adj := internalHomAdjunction F
  }

namespace PresheafOfModulesOfCommRing

@[simp]
lemma ihom_obj_obj_carrier (F G : PresheafOfModulesOfCommRing.{u} R) (U : Cᵒᵖ) :
    ((ihom F).obj G).obj U = (F.over U.unop ⟶ G.over U.unop) := rfl

@[simp]
lemma ihom_obj_map_apply (F G : PresheafOfModulesOfCommRing.{u} R)
    {U V : Cᵒᵖ} (f : U ⟶ V) (φ : ((ihom F).obj G).obj U) :
    dsimp% ((ihom F).obj G).map f φ = internalHomMap F G f.unop φ := rfl

@[simp]
lemma ihom_map_app_apply_app_apply (F : PresheafOfModulesOfCommRing.{u} R) (f : G ⟶ M)
    (U : Cᵒᵖ) (φ : ((ihom F).obj G).obj U) (W : (Over U.unop)ᵒᵖ)
    (x : (F.over U.unop).obj W) :
    dsimp% (((ihom F).map f).app U φ).app W x =
      f.app (op W.unop.left) (φ.app W x) := rfl

@[simp]
lemma ihom_ev_app_app_tmul (F G : PresheafOfModulesOfCommRing.{u} R)
    (U : Cᵒᵖ) (x : F.obj U) (φ : ((ihom F).obj G).obj U) :
    dsimp% ((ihom.ev F).app G).app U (x ⊗ₜ[R.obj U] φ) =
      φ.app (op (Over.mk (𝟙 U.unop))) x := by
  rw [ihom.ev, show ihom.adjunction F = internalHomAdjunction F from rfl,
    internalHomAdjunction_counit_app]
  exact internalHomEv_app_tmul F G U x φ

@[simp]
lemma ihom_coev_app_app_apply_app_apply (F M : PresheafOfModulesOfCommRing.{u} R)
    (U : Cᵒᵖ) (m : M.obj U) (W : (Over U.unop)ᵒᵖ) (x : (F.over U.unop).obj W) :
    dsimp% (((ihom.coev F).app M).app U m).app W x =
      x ⊗ₜ[R.obj (op W.unop.left)] M.map W.unop.hom.op m :=
  internalHomCoev_app_apply_app_apply F M U m W x

@[simp]
lemma monoidalClosed_curry_app_apply_app_apply (f : F ⊗ M ⟶ G)
    (U : Cᵒᵖ) (m : M.obj U) (W : (Over U.unop)ᵒᵖ) (x : (F.over U.unop).obj W) :
    dsimp% ((MonoidalClosed.curry f).app U m).app W x =
      f.app (op W.unop.left) (x ⊗ₜ[R.obj (op W.unop.left)] M.map W.unop.hom.op m) := by
  rw [MonoidalClosed.curry, show ihom.adjunction F = internalHomAdjunction F from rfl,
    internalHomAdjunction_homEquiv]
  exact internalHomCurry_app_apply_app_apply f U m W x

@[simp]
lemma monoidalClosed_uncurry_app_tmul (f : M ⟶ (ihom F).obj G)
    (U : Cᵒᵖ) (x : F.obj U) (m : M.obj U) :
    dsimp% (MonoidalClosed.uncurry f).app U (x ⊗ₜ[R.obj U] m) =
      (f.app U m).app (op (Over.mk (𝟙 U.unop))) x := by
  rw [MonoidalClosed.uncurry, show ihom.adjunction F = internalHomAdjunction F from rfl,
    internalHomAdjunction_homEquiv]
  exact internalHomUncurry_app_tmul f U x m

end PresheafOfModulesOfCommRing

end Monoidal
