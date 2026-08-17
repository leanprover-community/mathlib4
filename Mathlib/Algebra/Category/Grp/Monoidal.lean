/-
Copyright (c) 2026 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# The symmetric monoidal structure on abelian groups

The category `AddCommGrpCat.{u}` of abelian groups in the universe `u` is equipped with the
monoidal structure given by the tensor product over `ℤ`, with unit the (universe-lifted) copy
`ULift.{u} ℤ` of `ℤ`.

The construction follows the pattern used for `ModuleCat.monoidalCategory`: the data of the
monoidal structure (tensor product, unit, associator and unitors) is given explicitly, and the
axioms are transported, via `CategoryTheory.Monoidal.induced`, along the faithful functor
`AddCommGrpCat.toModuleCatULiftInt : AddCommGrpCat.{u} ⥤ ModuleCat.{u} (ULift.{u} ℤ)`, which is
in fact an equivalence of categories. The braiding and the symmetry, as well as the monoidal
closed structure, are then obtained by transport along this equivalence.
-/

universe u

open CategoryTheory MonoidalCategory TensorProduct

@[expose] public section

namespace AddCommGrpCat

/-- The data of the monoidal structure on abelian groups: the tensor product over `ℤ`, with
unit the universe-lifted copy `ULift ℤ` of `ℤ`. -/
noncomputable instance monoidalCategoryStruct : MonoidalCategoryStruct Ab.{u} where
  tensorObj M N := of (M ⊗[ℤ] N)
  whiskerLeft M _ _ f := ofHom (f.hom.toIntLinearMap.lTensor M)
  whiskerRight f N := ofHom (f.hom.toIntLinearMap.rTensor N)
  tensorHom f g := ofHom (TensorProduct.map f.hom.toIntLinearMap g.hom.toIntLinearMap)
  tensorUnit := of (ULift.{u} ℤ)
  associator M N K := (TensorProduct.assoc ℤ M N K).toAddEquiv.toAddCommGrpIso
  leftUnitor M := ((TensorProduct.congr ULift.moduleEquiv (LinearEquiv.refl ℤ M)).trans
    (TensorProduct.lid ℤ M)).toAddEquiv.toAddCommGrpIso
  rightUnitor M := ((TensorProduct.congr (LinearEquiv.refl ℤ M) ULift.moduleEquiv).trans
    (TensorProduct.rid ℤ M)).toAddEquiv.toAddCommGrpIso

/-- The functor sending an abelian group to the corresponding module over `ULift.{u} ℤ`,
which is an equivalence of categories. -/
@[implicit_reducible, simps! functor inverse]
noncomputable def toModuleCatULiftInt : Ab.{u} ≌ ModuleCat.{u} (ULift.{u} ℤ) :=
  ModuleCat.intEquivalence.symm.trans
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv ULift.ringEquiv)

/-- Extensionality for morphisms out of the image of a tensor product of abelian groups. -/
lemma toModuleCatULiftInt_tensor_ext {X Y : Ab.{u}} {W : ModuleCat.{u} (ULift.{u} ℤ)}
    {f g : toModuleCatULiftInt.functor.obj (X ⊗ Y) ⟶ W}
    (h : ∀ (x : X) (y : Y), f.hom (x ⊗ₜ y) = g.hom (x ⊗ₜ y)) : f = g := by
  ext t
  exact t.induction_on ((map_zero _).trans (map_zero _).symm) h
    fun _ _ h₁ h₂ ↦ (map_add ..).trans <| congr($h₁ + $h₂).trans (map_add ..).symm

/-- The data needed to induce the monoidal structure on `Ab` from the one on
`ModuleCat (ULift ℤ)`. -/
noncomputable def inducingFunctorData :
    Monoidal.InducingFunctorData toModuleCatULiftInt.functor where
  μIso X Y := (TensorProduct.equivOfCompatibleSMul ℤ (ULift ℤ) (ULift ℤ) X Y).toModuleIso
  εIso := .refl _
  whiskerLeft_eq _ _ _ _ := toModuleCatULiftInt_tensor_ext fun _ _ ↦ rfl
  whiskerRight_eq _ _ := toModuleCatULiftInt_tensor_ext fun _ _ ↦ rfl
  tensorHom_eq _ _ := toModuleCatULiftInt_tensor_ext fun _ _ ↦ rfl
  associator_eq X Y Z := toModuleCatULiftInt_tensor_ext fun t z ↦ t.induction_on rfl (fun _ _ ↦ rfl)
    fun _ _ h h' ↦ by
    rw [TensorProduct.add_tmul]; exact (map_add ..).trans <| congr($h + $h').trans (map_add ..).symm
  leftUnitor_eq _ := toModuleCatULiftInt_tensor_ext fun _ _ ↦ rfl
  rightUnitor_eq _ := toModuleCatULiftInt_tensor_ext fun _ _ ↦ rfl

/-- The monoidal structure on the category of abelian groups, given by the tensor product
over `ℤ`. -/
noncomputable instance : MonoidalCategory Ab.{u} :=
  Monoidal.induced toModuleCatULiftInt.functor inducingFunctorData

noncomputable instance : toModuleCatULiftInt.{u}.functor.Monoidal :=
  Monoidal.fromInducedMonoidal _ inducingFunctorData

noncomputable instance : BraidedCategory Ab.{u} :=
  .ofFaithful toModuleCatULiftInt.functor
    (fun M N ↦ (TensorProduct.comm ℤ M N).toAddEquiv.toAddCommGrpIso)
    fun _ _ ↦ by ext1; exact TensorProduct.ext' fun _ _ ↦ rfl

noncomputable instance : SymmetricCategory Ab.{u} where
  symmetry _ _ := by ext1; exact TensorProduct.ext' fun _ _ ↦ rfl

/-- The category of abelian groups is monoidal closed. -/
noncomputable instance monoidalClosed : MonoidalClosed Ab.{u} where
  closed M :=
  { rightAdj := coyoneda.obj (.op M)
    adj := .mkOfHomEquiv
      { homEquiv N P := ((β_ M N).homFromEquiv.trans <| ConcreteCategory.homEquiv.trans
          liftAddEquivInt.symm.toEquiv).trans ConcreteCategory.homEquiv.symm
        homEquiv_naturality_left_symm _ _ := by ext1; exact TensorProduct.ext' fun _ _ ↦ rfl
        homEquiv_naturality_right _ _ := rfl } }

lemma tensorObj_def (M N : Ab.{u}) : (M ⊗ N : Ab.{u}) = of (M ⊗[ℤ] N) :=
  rfl

lemma tensorUnit_def : (𝟙_ Ab.{u}) = of (ULift.{u} ℤ) := rfl

variable {M₁ M₂ M₃ M₄ : Ab.{u}}

@[simp] lemma whiskerLeft_apply (M : Ab.{u}) (f : M₁ ⟶ M₂) (m : M) (x : M₁) :
    (M ◁ f) (m ⊗ₜ x) = m ⊗ₜ f x := rfl

@[simp] lemma whiskerRight_apply (f : M₁ ⟶ M₂) (M : Ab.{u}) (x : M₁) (m : M) :
    (f ▷ M) (x ⊗ₜ m) = f x ⊗ₜ m := rfl

@[simp] lemma tensorHom_apply (f : M₁ ⟶ M₂) (g : M₃ ⟶ M₄) (x : M₁) (y : M₃) :
    (f ⊗ₘ g) (x ⊗ₜ y) = f x ⊗ₜ g y := rfl

@[simp] lemma associator_hom_apply (x : M₁) (y : M₂) (z : M₃) :
    (α_ M₁ M₂ M₃).hom ((x ⊗ₜ y) ⊗ₜ z) = x ⊗ₜ (y ⊗ₜ z) := rfl

@[simp] lemma leftUnitor_hom_apply (a : ULift.{u} ℤ) (x : M₁) :
    (λ_ M₁).hom (a ⊗ₜ x) = a.down • x := rfl

@[simp] lemma rightUnitor_hom_apply (x : M₁) (a : ULift.{u} ℤ) :
    (ρ_ M₁).hom (x ⊗ₜ a) = a.down • x := rfl

@[simp] lemma brading_hom_apply (x : M₁) (y : M₂) :
    (β_ M₁ M₂).hom (x ⊗ₜ y) = y ⊗ₜ x := rfl

@[simp] lemma braiding_inv_apply (x : M₁) (y : M₂) :
    (β_ M₁ M₂).inv (y ⊗ₜ x) = x ⊗ₜ y := rfl

@[simp] lemma ihom_obj (M N : Ab.{u}) : (ihom M).obj N = of (M →+ N) := by
  with_implicit rfl

end AddCommGrpCat
