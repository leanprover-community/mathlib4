/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jack McKoen, Joël Riou
-/
module

public import Mathlib.Algebra.Category.Grp.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# The monoidal category structure on presheaves of modules

Given a presheaf of commutative rings `R : Cᵒᵖ ⥤ CommRingCat`, we construct
the monoidal category structure on the category of presheaves of modules
`PresheafOfModules (R ⋙ forget₂ _ _)`. The tensor product `M₁ ⊗ M₂` is defined
as the presheaf of modules which sends `X : Cᵒᵖ` to `M₁.obj X ⊗ M₂.obj X`.

## Notes

This contribution was created as part of the AIM workshop
"Formalizing algebraic geometry" in June 2024.

-/

@[expose] public section

open CategoryTheory MonoidalCategory BraidedCategory Category Limits

universe v u v₁ u₁

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

instance (X : Cᵒᵖ) : CommRing ((R ⋙ forget₂ _ RingCat).obj X) :=
  inferInstanceAs (CommRing (R.obj X))

namespace PresheafOfModules

namespace Monoidal

variable (M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `tensorObj`. -/
noncomputable def tensorObjMap {X Y : Cᵒᵖ} (f : X ⟶ Y) : M₁.obj X ⊗ M₂.obj X ⟶
    (ModuleCat.restrictScalars (R.map f).hom).obj (M₁.obj Y ⊗ M₂.obj Y) :=
  ModuleCat.MonoidalCategory.tensorLift (fun m₁ m₂ ↦ M₁.map f m₁ ⊗ₜ M₂.map f m₂)
    (by
      intro m₁ m₁' m₂
      dsimp +instances
      rw [map_add, TensorProduct.add_tmul])
    (by intro a m₁ m₂; dsimp; erw [M₁.map_smul]; rfl)
    (by
      intro m₁ m₂ m₂'
      dsimp +instances
      rw [map_add, TensorProduct.tmul_add])
    (by intro a m₁ m₂; dsimp; erw [M₂.map_smul, TensorProduct.tmul_smul (r := R.map f a)]; rfl)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The tensor product of two presheaves of modules. -/
@[simps obj]
noncomputable def tensorObj : PresheafOfModules (R ⋙ forget₂ _ _) where
  obj X := M₁.obj X ⊗ M₂.obj X
  map f := tensorObjMap M₁ M₂ f
  map_id X := ModuleCat.MonoidalCategory.tensor_ext (by
    intro m₁ m₂
    dsimp [tensorObjMap]
    simp
    rfl) -- `ModuleCat.restrictScalarsId'App_inv_apply` doesn't get picked up due to type mismatch
  map_comp f g := ModuleCat.MonoidalCategory.tensor_ext (by
    intro m₁ m₂
    dsimp [tensorObjMap]
    simp +instances)

variable {M₁ M₂ M₃ M₄}

@[simp]
lemma tensorObj_map_tmul {X Y : Cᵒᵖ} (f : X ⟶ Y) (m₁ : M₁.obj X) (m₂ : M₂.obj X) :
    DFunLike.coe (α := (M₁.obj X ⊗ M₂.obj X :))
      (β := fun _ ↦ (ModuleCat.restrictScalars (R.map f).hom).obj (M₁.obj Y ⊗ M₂.obj Y))
      (ModuleCat.Hom.hom (R := ↑(R.obj X)) ((tensorObj M₁ M₂).map f)) (m₁ ⊗ₜ[R.obj X] m₂) =
    M₁.map f m₁ ⊗ₜ[R.obj Y] M₂.map f m₂ := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The tensor product of two morphisms of presheaves of modules. -/
@[simps]
noncomputable def tensorHom (f : M₁ ⟶ M₂) (g : M₃ ⟶ M₄) : tensorObj M₁ M₃ ⟶ tensorObj M₂ M₄ where
  app X := f.app X ⊗ₘ g.app X
  naturality {X Y} φ := ModuleCat.MonoidalCategory.tensor_ext (fun m₁ m₃ ↦ by
    dsimp
    rw [tensorObj_map_tmul]
    -- Need `erw` because of the type mismatch in `map` and the tensor product.
    erw [ModuleCat.MonoidalCategory.tensorHom_tmul, tensorObj_map_tmul]
    rw [naturality_apply, naturality_apply]
    simp)

end Monoidal

open Monoidal

open ModuleCat.MonoidalCategory in
noncomputable instance monoidalCategoryStruct :
    MonoidalCategoryStruct (PresheafOfModules.{u} (R ⋙ forget₂ _ _)) where
  tensorObj := tensorObj
  whiskerLeft _ _ _ g := tensorHom (𝟙 _) g
  whiskerRight f _ := tensorHom f (𝟙 _)
  tensorHom := tensorHom
  tensorUnit := unit _
  associator M₁ M₂ M₃ := isoMk (fun _ ↦ α_ _ _ _)
    (fun _ _ _ ↦ ModuleCat.MonoidalCategory.tensor_ext₃' (by intros; rfl))
  leftUnitor M := Iso.symm (isoMk (fun _ ↦ (λ_ _).symm) (fun X Y f ↦ by
    ext m
    dsimp [CommRingCat.forgetToRingCat_obj]
    erw [leftUnitor_inv_apply, leftUnitor_inv_apply, tensorObj_map_tmul, (R.map f).hom.map_one]
    rfl))
  rightUnitor M := Iso.symm (isoMk (fun _ ↦ (ρ_ _).symm) (fun X Y f ↦ by
    ext m
    dsimp [CommRingCat.forgetToRingCat_obj]
    erw [rightUnitor_inv_apply, rightUnitor_inv_apply, tensorObj_map_tmul, (R.map f).hom.map_one]
    rfl))

noncomputable instance monoidalCategory :
    MonoidalCategory (PresheafOfModules.{u} (R ⋙ forget₂ _ _)) where
  tensorHom_def _ _ := by ext1; apply tensorHom_def
  id_tensorHom_id _ _ := by ext1; apply id_tensorHom_id
  tensorHom_comp_tensorHom _ _ _ _ := by ext1; apply tensorHom_comp_tensorHom
  whiskerLeft_id M₁ M₂ := by
    ext1 X
    apply MonoidalCategory.whiskerLeft_id (C := ModuleCat (R.obj X))
  id_whiskerRight _ _ := by
    ext1 X
    apply MonoidalCategory.id_whiskerRight (C := ModuleCat (R.obj X))
  associator_naturality _ _ _ := by ext1; apply associator_naturality
  leftUnitor_naturality _ := by ext1; apply leftUnitor_naturality
  rightUnitor_naturality _ := by ext1; apply rightUnitor_naturality
  pentagon _ _ _ _ := by ext1; apply pentagon
  triangle _ _ := by ext1; apply triangle

open BraidedCategory

noncomputable instance symmetricCategory :
    SymmetricCategory (PresheafOfModules.{u} (R ⋙ forget₂ _ _)) where
  braiding M₁ M₂ :=
    isoMk (fun X ↦ braiding (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X))
      (fun _ _ f ↦ ModuleCat.MonoidalCategory.tensor_ext (fun _ _ ↦ rfl))
  braiding_naturality_right _ _ _ _ := by
    ext : 1
    exact ModuleCat.MonoidalCategory.tensor_ext (fun _ _ ↦ rfl)
  braiding_naturality_left _ _ := by
    ext : 1
    exact ModuleCat.MonoidalCategory.tensor_ext (fun _ _ ↦ rfl)
  hexagon_forward _ _ _ := by
    ext : 1
    apply hexagon_forward (C := ModuleCat (R.obj _))
  hexagon_reverse _ _ _ := by
    ext : 1
    apply hexagon_reverse (C := ModuleCat (R.obj _))
  symmetry _ _ := by
    ext : 1
    apply SymmetricCategory.symmetry (C := ModuleCat (R.obj _))

section

variable (M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

lemma tensorObj_obj (X : Cᵒᵖ) :
    (M₁ ⊗ M₂).obj X =
      MonoidalCategory.tensorObj (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X) := rfl

attribute [local simp] tensorObj_obj

variable {M₂ M₃} in
@[simp]
lemma whiskerLeft_app (f : M₂ ⟶ M₃) (X : Cᵒᵖ) :
    dsimp% (M₁ ◁ f).app X = whiskerLeft (C := ModuleCat (R.obj X)) (M₁.obj X) (f.app X) :=
  rfl

variable {M₁ M₂} in
@[simp]
lemma whiskerRight_app (f : M₁ ⟶ M₂) (M₃ : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (X : Cᵒᵖ) :
    dsimp% (f ▷ M₃).app X = whiskerRight (C := ModuleCat (R.obj X)) (f.app X) (M₃.obj X) := rfl

variable {M₁ M₂ M₃ M₄} in
@[simp]
lemma tensorHom_app (f : M₁ ⟶ M₂) (g : M₃ ⟶ M₄) (X : Cᵒᵖ) :
    dsimp% (f ⊗ₘ g).app X =
      MonoidalCategory.tensorHom (C := ModuleCat (R.obj X)) (f.app X) (g.app X) := rfl

@[simp]
lemma leftUnitor_hom_app (X : Cᵒᵖ) :
    dsimp% (λ_ M₁).hom.app X = (leftUnitor (C := ModuleCat (R.obj X)) (M₁.obj X)).hom :=
  rfl

@[simp]
lemma leftUnitor_inv_app (X : Cᵒᵖ) :
    dsimp% (λ_ M₁).inv.app X = (leftUnitor (C := ModuleCat (R.obj X)) (M₁.obj X)).inv := by
  rfl

@[simp]
lemma rightUnitor_hom_app (X : Cᵒᵖ) :
    dsimp% (ρ_ M₁).hom.app X = (rightUnitor (C := ModuleCat (R.obj X)) (M₁.obj X)).hom :=
  rfl

@[simp]
lemma rightUnitor_inv_app (X : Cᵒᵖ) :
    dsimp% (ρ_ M₁).inv.app X = (rightUnitor (C := ModuleCat (R.obj X)) (M₁.obj X)).inv :=
  rfl

@[simp]
lemma associator_hom_app (X : Cᵒᵖ) :
    (α_ M₁ M₂ M₃).hom.app X =
      (associator (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X) (M₃.obj X)).hom :=
  rfl

@[simp]
lemma associator_inv_app (X : Cᵒᵖ) :
    (α_ M₁ M₂ M₃).inv.app X =
      (associator (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X) (M₃.obj X)).inv :=
  rfl

@[simp]
lemma braiding_hom_app (X : Cᵒᵖ) :
    dsimp% (braiding M₁ M₂).hom.app X =
      (braiding (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X)).hom := by
  rfl

@[simp]
lemma braiding_inv_app (X : Cᵒᵖ) :
    dsimp% (braiding M₁ M₂).inv.app X =
      (braiding (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X)).inv := rfl

end

instance (F : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
    PreservesColimitsOfSize.{u, u} (tensorLeft F) where
  preservesColimitsOfShape := ⟨⟨fun hc ↦ ⟨evaluationJointlyReflectsColimits _ _
      (fun X ↦ isColimitOfPreserves (tensorLeft (show ModuleCat (R.obj X) from F.obj X))
        (isColimitOfPreserves (evaluation _ X) hc))⟩⟩⟩

instance (F : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
    PreservesColimitsOfSize.{u, u} (tensorRight F) :=
  preservesColimits_of_natIso (tensorLeftIsoTensorRight F)

/-!
## The tensor product of presheaves of modules as a coequalizer

Let `R : Cᵒᵖ ⥤ CommRingCat` be a presheaf of commutative rings.  Any presheaf of modules
over `R` has an underlying presheaf of abelian groups (`PresheafOfModules.toPresheaf`).
For presheaves of modules `M` and `N`, the canonical epimorphism

`distrib : M ⊗ N ⟶ M ⊗[R] N` (of presheaves of abelian groups)

(where the tensor product on the left is the pointwise tensor product over `ℤ`) exhibits
the underlying presheaf of abelian groups of `M ⊗[R] N` as the coequalizer of the two maps
`M ⊗ (R ⊗ N) ⇉ M ⊗ N` given by `m ⊗ (r ⊗ n) ↦ (r • m) ⊗ n` and `m ⊗ (r ⊗ n) ↦ m ⊗ (r • n)`.
These are bundled into `colimitCoconeAb`.
-/

open TensorProduct

instance (M : PresheafOfModules.{u} (R ⋙ forget₂ ..)) (U : Cᵒᵖ) :
    Module (R.obj U) (M.presheaf.obj U) :=
  inferInstanceAs (Module (R.obj U) (M.obj U))

variable (M N : PresheafOfModules.{u} (R ⋙ forget₂ ..))

/-- The canonical morphism from the pointwise tensor product over `ℤ` to the tensor
product over `R`. -/
noncomputable def distrib : M.presheaf ⊗ N.presheaf ⟶ (M ⊗ N).presheaf where
  app U := AddCommGrpCat.ofHom
    (mapOfCompatibleSMul (R.obj U) ℤ ℤ (M.obj U) (N.obj U)).toAddMonoidHom
  naturality _ _ _ := by ext1; exact TensorProduct.ext' fun _ _ ↦ rfl

instance epi_distrib : Epi (distrib M N) where
  left_cancellation _ _ h := by
    ext U x
    obtain ⟨y, rfl⟩ := mapOfCompatibleSMul_surjective _ ℤ ℤ _ _ x
    exact congr(($h).app U y)

/-- The presheaf of rings, viewed as a presheaf of abelian groups. -/
noncomputable abbrev ringAb (R : Cᵒᵖ ⥤ CommRingCat.{u}) : Cᵒᵖ ⥤ Ab.{u} :=
  (unit (R ⋙ forget₂ ..)).presheaf

/-- The action of the presheaf of rings on a presheaf of modules, written on the left. -/
noncomputable def act : ringAb R ⊗ M.presheaf ⟶ M.presheaf where
  app U := AddCommGrpCat.ofHom <| TensorProduct.liftAddHom (smulAddHom (R.obj U) _)
    fun n (r : R.obj U) m ↦ show (n • r) • m = r • (n • m) by rw [smul_comm, smul_assoc]
  naturality U V f := by ext1; exact TensorProduct.ext' fun r m ↦ (M.map_smul ..).symm

/-- The first of the two maps whose coequalizer is the tensor product: it sends
`m ⊗ (r ⊗ n)` to `(r • m) ⊗ n`. -/
noncomputable def act₁ : (M.presheaf ⊗ ringAb R) ⊗ N.presheaf ⟶ M.presheaf ⊗ N.presheaf :=
  ((β_ _ _).hom ≫ act M) ▷ N.presheaf

/-- The second of the two maps whose coequalizer is the tensor product: it sends
`m ⊗ (r ⊗ n)` to `m ⊗ (r • n)`. -/
noncomputable def act₂ : (M.presheaf ⊗ ringAb R) ⊗ N.presheaf ⟶ M.presheaf ⊗ N.presheaf :=
  (α_ _ _ _).hom ≫ (M.presheaf ◁ act N)

lemma act_distrib : act₁ M N ≫ distrib M N = act₂ M N ≫ distrib M N := by
  ext U : 3
  exact TensorProduct.extₗ fun m (r : R.obj U) n ↦ by exact smul_tmul (R := R.obj U) r m n
  /- erw to be diagnosed:
  exact TensorProduct.ext' fun mr n ↦ mr.induction_on (by erw [zero_tmul, map_zero])
    (fun m (r : R.obj U) ↦ smul_tmul (R := R.obj U) r m n) fun _ _ h₁ h₂ ↦ by
    erw [add_tmul, map_add, map_add, h₁, h₂] -/

/-- The colimit cocone realizing the tensor product as a coequalizer. -/
noncomputable def colimitCoconeAb : ColimitCocone (parallelPair (act₁ M N) (act₂ M N)) where
  cocone := Cofork.ofπ _ (act_distrib M N)
  isColimit := have : Epi (Cofork.ofπ _ (act_distrib M N)).π := inferInstanceAs (Epi <| distrib M N)
    Cofork.IsColimit.ofEpi _ (fun c ↦
    { app U := AddCommGrpCat.ofHom <| TensorProduct.liftAddHom ((LinearMap.toAddMonoidHom'.comp
        (TensorProduct.mk ℤ (M.obj U) (N.obj U)).toAddMonoidHom).compr₂ ((c.ι.app .one).app U).hom)
        fun r m n ↦ congr($(Cofork.condition c).app U ((m ⊗ₜ r) ⊗ₜ n))
      naturality U V f := by
        ext1
        exact TensorProduct.ext' fun m n ↦ congr_arg (· (m ⊗ₜ n)) ((c.ι.app .one).naturality f) })
    (fun c ↦ by ext _ : 3; exact TensorProduct.ext' fun _ _ ↦ rfl)

end PresheafOfModules
