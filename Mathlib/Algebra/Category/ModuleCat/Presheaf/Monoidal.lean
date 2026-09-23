/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jack McKoen, Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed

/-!
# The monoidal category structure on presheaves of modules

Given a presheaf of commutative rings `R : Cᵒᵖ ⥤ CommRingCat`, we construct
the monoidal category structure on the category of presheaves of modules
`PresheafOfModulesOfCommRing R`. The tensor product `M₁ ⊗ M₂` is defined
as the presheaf of modules which sends `X : Cᵒᵖ` to `M₁.obj X ⊗ M₂.obj X`.

## Notes

This contribution was created as part of the AIM workshop
"Formalizing algebraic geometry" in June 2024.

-/

@[expose] public section

open CategoryTheory MonoidalCategory BraidedCategory Category Limits

universe v u v₁ u₁

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

namespace PresheafOfModulesOfCommRing

namespace Monoidal

variable (M₁ M₂ M₃ M₄ : PresheafOfModulesOfCommRing.{u} R)

#adaptation_note
/--
After https://github.com/leanprover/lean4/pull/14624:

We had to use the `instanceSearchTypes` backward compatibility flag to make an instance search
succeed. Concretely, the following instance cannot be synthesized:
`TensorProduct.CompatibleSMul ↑(R.obj Y) ↑(R.obj Y) ↑(M₁.obj Y) ↑(M₂.obj Y)`

The failure happens while applying `@TensorProduct.CompatibleSMul.isScalarTower`: assigning one of
its instance-implicit-argument metavariables is rejected because the metavariable's type and the
type of the assigned value do not match at `.instances` transparency. The metavariable's expected
type is `DistribMulAction ↑(R.obj Y) ↑(M₂.obj Y)`, whereas the assigned value
`ModuleCat.instModuleCarrierObjRestrictScalars.toDistribMulAction` has type
```
DistribMulAction ↑((R ⋙ forget₂ CommRingCat RingCat).obj Y)
  ↑((ModuleCat.restrictScalars (RingCat.Hom.hom ((R ⋙ forget₂ CommRingCat RingCat).map f))).obj
      (M₂.obj Y))
```
Lean falls back to synthesize an instance of the correct type, but it returns
`(M₂.obj Y).isModule.toDistribMulAction`, which is again not defeq to the assigned value. Both
comparisons bottom out at `↑(R.obj Y) =?= ↑((R ⋙ forget₂ CommRingCat RingCat).obj Y)`, the same
ring bundled once as a `CommRingCat` and once as a `RingCat`; seeing that these agree requires
unfolding `⋙`, which is `@[implicit_reducible]`.

Potential fix: Concentrate on removing `respectTransparency false` first.
For example, do this by making `ModuleCat.RestrictScalars.obj'` and `ModuleCat.restrictScalars`
implicit-reducible *at their definition site*.
Without the backward-compatibility flag `respectTransparency false`, Lean bumps transparency for
instance-implicit arguments to `implicit`, thereby comparing the synthesized and unified instances
at implicit transparency instead of the stricter instance transparency.
After that, you can remove `instanceSearchTypes false`, too.
-/
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `tensorObj`. -/
noncomputable def tensorObjMap {X Y : Cᵒᵖ} (f : X ⟶ Y) : M₁.obj X ⊗ M₂.obj X ⟶
    (ModuleCat.restrictScalars (R.map f).hom).obj (M₁.obj Y ⊗ M₂.obj Y) :=
  ModuleCat.MonoidalCategory.tensorLift (fun m₁ m₂ ↦ M₁.map f m₁ ⊗ₜ M₂.map f m₂)
    (by
      intro m₁ m₁' m₂
      dsimp
      rw [map_add, TensorProduct.add_tmul])
    (by intro a m₁ m₂; dsimp; erw [M₁.map_smul]; rfl)
    (by
      intro m₁ m₂ m₂'
      dsimp
      rw [map_add, TensorProduct.tmul_add])
    (by intro a m₁ m₂; dsimp; erw [M₂.map_smul, TensorProduct.tmul_smul (r := R.map f a)]; rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The tensor product of two presheaves of modules. -/
@[simps obj]
noncomputable def tensorObj : PresheafOfModulesOfCommRing R :=
  mk (fun X ↦ M₁.obj X ⊗ M₂.obj X)
    (fun f ↦ tensorObjMap M₁ M₂ f)
    (fun X ↦ ModuleCat.MonoidalCategory.tensor_ext (by
      intro m₁ m₂
      dsimp [tensorObjMap]
      simp))
    (fun f g ↦ ModuleCat.MonoidalCategory.tensor_ext (by
      intro m₁ m₂
      dsimp [tensorObjMap]
      simp +instances))

variable {M₁ M₂ M₃ M₄}

@[simp]
lemma tensorObj_map_tmul {X Y : Cᵒᵖ} (f : X ⟶ Y) (m₁ : M₁.obj X) (m₂ : M₂.obj X) :
    DFunLike.coe (α := (M₁.obj X ⊗ M₂.obj X :))
      (β := fun _ ↦ (ModuleCat.restrictScalars (R.map f).hom).obj (M₁.obj Y ⊗ M₂.obj Y))
      (ModuleCat.Hom.hom ((tensorObj M₁ M₂).map f)) (m₁ ⊗ₜ[R.obj X] m₂) =
    M₁.map f m₁ ⊗ₜ[R.obj Y] M₂.map f m₂ := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The tensor product of two morphisms of presheaves of modules. -/
@[simps]
noncomputable def tensorHom (f : M₁ ⟶ M₂) (g : M₃ ⟶ M₄) :
    tensorObj M₁ M₃ ⟶ tensorObj M₂ M₄ :=
  homMk (fun X ↦ f.app' X ⊗ₘ g.app' X)
    (fun φ ↦ ModuleCat.MonoidalCategory.tensor_ext (fun m₁ m₃ ↦ by
      dsimp
      rw [tensorObj_map_tmul, ModuleCat.MonoidalCategory.tensorHom_tmul, tensorObj_map_tmul,
        naturality_apply, naturality_apply]))

end Monoidal

open Monoidal

noncomputable instance monoidalCategoryStruct :
    MonoidalCategoryStruct (PresheafOfModulesOfCommRing.{u} R) where
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
    erw [ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
      ModuleCat.MonoidalCategory.leftUnitor_inv_apply, tensorObj_map_tmul, (R.map f).hom.map_one]
    rfl))
  rightUnitor M := Iso.symm (isoMk (fun _ ↦ (ρ_ _).symm) (fun X Y f ↦ by
    ext m
    dsimp [CommRingCat.forgetToRingCat_obj]
    erw [ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
      ModuleCat.MonoidalCategory.rightUnitor_inv_apply, tensorObj_map_tmul, (R.map f).hom.map_one]
    rfl))

noncomputable instance monoidalCategory :
    MonoidalCategory (PresheafOfModulesOfCommRing.{u} R) where
  tensorHom_def _ _ := by ext1; apply tensorHom_def
  id_tensorHom_id _ _ := by ext1; apply id_tensorHom_id
  tensorHom_comp_tensorHom _ _ _ _ := by
    ext1 X
    apply tensorHom_comp_tensorHom (C := ModuleCat (R.obj X))
  whiskerLeft_id M₁ M₂ := by
    ext1 X
    apply MonoidalCategory.whiskerLeft_id (C := ModuleCat (R.obj X))
  id_whiskerRight _ _ := by
    ext1 X
    apply MonoidalCategory.id_whiskerRight (C := ModuleCat (R.obj X))
  associator_naturality _ _ _ := by
    ext1 X
    apply associator_naturality (C := ModuleCat (R.obj X))
  leftUnitor_naturality _ := by
    ext1 X
    apply leftUnitor_naturality (C := ModuleCat (R.obj X))
  rightUnitor_naturality _ := by
    ext1 X
    apply rightUnitor_naturality (C := ModuleCat (R.obj X))
  pentagon _ _ _ _ := by
    ext1 X
    apply pentagon (C := ModuleCat (R.obj X))
  triangle _ _ := by
    ext1 X
    apply triangle (C := ModuleCat (R.obj X))

open BraidedCategory

noncomputable instance symmetricCategory :
    SymmetricCategory (PresheafOfModulesOfCommRing.{u} R) where
  braiding M₁ M₂ :=
    isoMk (fun X ↦ braiding (M₁.obj X) (M₂.obj X))
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

variable (M₁ M₂ M₃ M₄ : PresheafOfModulesOfCommRing.{u} R)

lemma tensorObj_obj (X : Cᵒᵖ) :
    (M₁ ⊗ M₂).obj X = MonoidalCategory.tensorObj (M₁.obj X) (M₂.obj X) := rfl

attribute [local simp] tensorObj_obj

variable {M₂ M₃} in
@[simp]
lemma whiskerLeft_app (f : M₂ ⟶ M₃) (X : Cᵒᵖ) :
    dsimp% (M₁ ◁ f).app' X = whiskerLeft (M₁.obj X) (f.app' X) := rfl

variable {M₁ M₂} in
@[simp]
lemma whiskerRight_app (f : M₁ ⟶ M₂) (M₃ : PresheafOfModulesOfCommRing.{u} R)
    (X : Cᵒᵖ) :
    dsimp% (f ▷ M₃).app' X = whiskerRight (f.app' X) (M₃.obj X) := rfl

variable {M₁ M₂ M₃ M₄} in
@[simp]
lemma tensorHom_app (f : M₁ ⟶ M₂) (g : M₃ ⟶ M₄) (X : Cᵒᵖ) :
    dsimp% (f ⊗ₘ g).app' X =
      MonoidalCategory.tensorHom (f.app' X) (g.app' X) := rfl

@[simp]
lemma leftUnitor_hom_app (X : Cᵒᵖ) :
    dsimp% (λ_ M₁).hom.app' X = (leftUnitor (M₁.obj X)).hom :=
  rfl

@[simp]
lemma leftUnitor_inv_app (X : Cᵒᵖ) :
    dsimp% (λ_ M₁).inv.app' X = (leftUnitor (M₁.obj X)).inv := by
  rfl

@[simp]
lemma rightUnitor_hom_app (X : Cᵒᵖ) :
    dsimp% (ρ_ M₁).hom.app' X = (rightUnitor (M₁.obj X)).hom :=
  rfl

@[simp]
lemma rightUnitor_inv_app (X : Cᵒᵖ) :
    dsimp% (ρ_ M₁).inv.app' X = (rightUnitor (M₁.obj X)).inv :=
  rfl

@[simp]
lemma associator_hom_app (X : Cᵒᵖ) :
    (α_ M₁ M₂ M₃).hom.app' X =
      (associator (M₁.obj X) (M₂.obj X) (M₃.obj X)).hom :=
  rfl

@[simp]
lemma associator_inv_app (X : Cᵒᵖ) :
    (α_ M₁ M₂ M₃).inv.app' X =
      (associator (M₁.obj X) (M₂.obj X) (M₃.obj X)).inv :=
  rfl

@[simp]
lemma braiding_hom_app (X : Cᵒᵖ) :
    dsimp% (braiding M₁ M₂).hom.app' X =
      (braiding (M₁.obj X) (M₂.obj X)).hom := by
  rfl

@[simp]
lemma braiding_inv_app (X : Cᵒᵖ) :
    dsimp% (braiding M₁ M₂).inv.app' X =
      (braiding (M₁.obj X) (M₂.obj X)).inv := rfl

end

instance (F : PresheafOfModulesOfCommRing.{u} R) :
    PreservesColimitsOfSize.{u, u} (tensorLeft F) where
  preservesColimitsOfShape := ⟨⟨fun hc ↦ ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _
      (fun X ↦ isColimitOfPreserves (tensorLeft (show ModuleCat (R.obj X) from F.obj X))
        (isColimitOfPreserves (PresheafOfModules.evaluation _ X) hc))⟩⟩⟩

instance (F : PresheafOfModulesOfCommRing.{u} R) :
    PreservesColimitsOfSize.{u, u} (tensorRight F) :=
  preservesColimits_of_natIso (tensorLeftIsoTensorRight F)

end PresheafOfModulesOfCommRing
