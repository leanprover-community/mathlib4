/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Patrick Massot, Scott Morrison

! This file was ported from Lean 3 source module topology.category.UniformSpace
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.CategoryTheory.ConcreteCategory.UnbundledHom
import Mathlib.CategoryTheory.Monad.Limits
import Mathlib.Topology.Category.Top.Basic
import Mathlib.Topology.UniformSpace.Completion

/-!
# The category of uniform spaces

We construct the category of uniform spaces, show that the complete separated uniform spaces
form a reflective subcategory, and hence possess all limits that uniform spaces do.

TODO: show that uniform spaces actually have all limits!
-/


universe u

open CategoryTheory

/-- A (bundled) uniform space. -/
def UniformSpaceCat : Type (u + 1) :=
  Bundled UniformSpace
#align UniformSpace UniformSpaceCat

namespace UniformSpaceCat

/-- The information required to build morphisms for `UniformSpace`. -/
instance : UnbundledHom @UniformContinuous :=
  ⟨@uniformContinuous_id, @UniformContinuous.comp⟩

deriving instance LargeCategory, ConcreteCategory for UniformSpaceCat

instance : CoeSort UniformSpaceCat (Type _) :=
  Bundled.hasCoeToSort

instance (x : UniformSpaceCat) : UniformSpace x :=
  x.str

/-- Construct a bundled `UniformSpace` from the underlying type and the typeclass. -/
def of (α : Type u) [UniformSpace α] : UniformSpaceCat :=
  ⟨α⟩
#align UniformSpace.of UniformSpaceCat.of

instance : Inhabited UniformSpaceCat :=
  ⟨UniformSpaceCat.of Empty⟩

@[simp]
theorem coe_of (X : Type u) [UniformSpace X] : (of X : Type u) = X :=
  rfl
#align UniformSpace.coe_of UniformSpaceCat.coe_of

instance (X Y : UniformSpaceCat) : CoeFun (X ⟶ Y) fun _ => X → Y :=
  ⟨CategoryTheory.Functor.map (forget UniformSpaceCat)⟩

@[simp]
theorem coe_comp {X Y Z : UniformSpaceCat} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : X → Z) = g ∘ f :=
  rfl
#align UniformSpace.coe_comp UniformSpaceCat.coe_comp

@[simp]
theorem coe_id (X : UniformSpaceCat) : (𝟙 X : X → X) = id :=
  rfl
#align UniformSpace.coe_id UniformSpaceCat.coe_id

@[simp]
theorem coe_mk {X Y : UniformSpaceCat} (f : X → Y) (hf : UniformContinuous f) :
    ((⟨f, hf⟩ : X ⟶ Y) : X → Y) = f :=
  rfl
#align UniformSpace.coe_mk UniformSpaceCat.coe_mk

theorem hom_ext {X Y : UniformSpaceCat} {f g : X ⟶ Y} : (f : X → Y) = g → f = g :=
  Subtype.eq
#align UniformSpace.hom_ext UniformSpaceCat.hom_ext

/-- The forgetful functor from uniform spaces to topological spaces. -/
instance hasForgetToTop : HasForget₂ UniformSpaceCat.{u} TopCat.{u}
    where forget₂ :=
    { obj := fun X => TopCat.of X
      map := fun X Y f =>
        { toFun := f
          continuous_toFun := UniformContinuous.continuous f.property } }
#align UniformSpace.has_forget_to_Top UniformSpaceCat.hasForgetToTop

end UniformSpaceCat

/-- A (bundled) complete separated uniform space. -/
structure CpltSepUniformSpace where
  α : Type u
  [isUniformSpace : UniformSpace α]
  [is_completeSpace : CompleteSpace α]
  [is_separated : SeparatedSpace α]
#align CpltSepUniformSpace CpltSepUniformSpace

namespace CpltSepUniformSpace

instance : CoeSort CpltSepUniformSpace (Type u) :=
  ⟨CpltSepUniformSpace.α⟩

attribute [instance] is_uniform_space is_complete_space is_separated

/-- The function forgetting that a complete separated uniform spaces is complete and separated. -/
def toUniformSpace (X : CpltSepUniformSpace) : UniformSpaceCat :=
  UniformSpaceCat.of X
#align CpltSepUniformSpace.to_UniformSpace CpltSepUniformSpace.toUniformSpace

instance completeSpace (X : CpltSepUniformSpace) : CompleteSpace (toUniformSpace X).α :=
  CpltSepUniformSpace.is_completeSpace X
#align CpltSepUniformSpace.complete_space CpltSepUniformSpace.completeSpace

instance separatedSpace (X : CpltSepUniformSpace) : SeparatedSpace (toUniformSpace X).α :=
  CpltSepUniformSpace.is_separated X
#align CpltSepUniformSpace.separated_space CpltSepUniformSpace.separatedSpace

/-- Construct a bundled `UniformSpace` from the underlying type and the appropriate typeclasses. -/
def of (X : Type u) [UniformSpace X] [CompleteSpace X] [SeparatedSpace X] : CpltSepUniformSpace :=
  ⟨X⟩
#align CpltSepUniformSpace.of CpltSepUniformSpace.of

@[simp]
theorem coe_of (X : Type u) [UniformSpace X] [CompleteSpace X] [SeparatedSpace X] :
    (of X : Type u) = X :=
  rfl
#align CpltSepUniformSpace.coe_of CpltSepUniformSpace.coe_of

instance : Inhabited CpltSepUniformSpace :=
  haveI : SeparatedSpace Empty := separated_iff_t2.mpr (by infer_instance)
  ⟨CpltSepUniformSpace.of Empty⟩

/-- The category instance on `CpltSepUniformSpace`. -/
instance category : LargeCategory CpltSepUniformSpace :=
  InducedCategory.category toUniformSpace
#align CpltSepUniformSpace.category CpltSepUniformSpace.category

/-- The concrete category instance on `CpltSepUniformSpace`. -/
instance concreteCategory : ConcreteCategory CpltSepUniformSpace :=
  InducedCategory.concreteCategory toUniformSpace
#align CpltSepUniformSpace.concrete_category CpltSepUniformSpace.concreteCategory

instance hasForgetToUniformSpace : HasForget₂ CpltSepUniformSpace UniformSpaceCat :=
  InducedCategory.hasForget₂ toUniformSpace
#align CpltSepUniformSpace.has_forget_to_UniformSpace CpltSepUniformSpace.hasForgetToUniformSpace

end CpltSepUniformSpace

namespace UniformSpaceCat

open UniformSpace

open CpltSepUniformSpace

/-- The functor turning uniform spaces into complete separated uniform spaces. -/
noncomputable def completionFunctor : UniformSpaceCat ⥤ CpltSepUniformSpace where
  obj X := CpltSepUniformSpace.of (Completion X)
  map X Y f := ⟨Completion.map f.1, Completion.uniformContinuous_map⟩
  map_id' X := Subtype.eq Completion.map_id
  map_comp' X Y Z f g := Subtype.eq (Completion.map_comp g.property f.property).symm
#align UniformSpace.completion_functor UniformSpaceCat.completionFunctor

/-- The inclusion of a uniform space into its completion. -/
def completionHom (X : UniformSpaceCat) :
    X ⟶ (forget₂ CpltSepUniformSpace UniformSpaceCat).obj (completionFunctor.obj X) where
  val := (coe : X → Completion X)
  property := Completion.uniformContinuous_coe X
#align UniformSpace.completion_hom UniformSpaceCat.completionHom

@[simp]
theorem completionHom_val (X : UniformSpaceCat) (x) : (completionHom X) x = (x : Completion X) :=
  rfl
#align UniformSpace.completion_hom_val UniformSpaceCat.completionHom_val

/-- The mate of a morphism from a `UniformSpace` to a `CpltSepUniformSpace`. -/
noncomputable def extensionHom {X : UniformSpaceCat} {Y : CpltSepUniformSpace}
    (f : X ⟶ (forget₂ CpltSepUniformSpace UniformSpaceCat).obj Y) : completionFunctor.obj X ⟶ Y
    where
  val := Completion.extension f
  property := Completion.uniformContinuous_extension
#align UniformSpace.extension_hom UniformSpaceCat.extensionHom

@[simp]
theorem extensionHom_val {X : UniformSpaceCat} {Y : CpltSepUniformSpace}
    (f : X ⟶ (forget₂ _ _).obj Y) (x) : (extensionHom f) x = Completion.extension f x :=
  rfl
#align UniformSpace.extension_hom_val UniformSpaceCat.extensionHom_val

@[simp]
theorem extension_comp_coe {X : UniformSpaceCat} {Y : CpltSepUniformSpace}
    (f : toUniformSpace (CpltSepUniformSpace.of (Completion X)) ⟶ toUniformSpace Y) :
    extensionHom (completionHom X ≫ f) = f := by apply Subtype.eq; funext x;
  exact congr_fun (completion.extension_comp_coe f.property) x
#align UniformSpace.extension_comp_coe UniformSpaceCat.extension_comp_coe

/-- The completion functor is left adjoint to the forgetful functor. -/
noncomputable def adj : completionFunctor ⊣ forget₂ CpltSepUniformSpace UniformSpaceCat :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => completionHom X ≫ f
          invFun := fun f => extensionHom f
          left_inv := fun f => by dsimp; erw [extension_comp_coe]
          right_inv := fun f => by
            apply Subtype.eq; funext x; cases f
            exact
              @completion.extension_coe _ _ _ _ _ (CpltSepUniformSpace.separatedSpace _) f_property
                _ }
      homEquiv_naturality_left_symm := fun X X' Y f g => by
        apply hom_ext; funext x; dsimp
        erw [coe_comp, ← completion.extension_map]
        rfl; exact g.property; exact f.property }
#align UniformSpace.adj UniformSpaceCat.adj

noncomputable instance : IsRightAdjoint (forget₂ CpltSepUniformSpace UniformSpaceCat) :=
  ⟨completionFunctor, adj⟩

noncomputable instance : Reflective (forget₂ CpltSepUniformSpace UniformSpaceCat) where

open CategoryTheory.Limits

-- TODO Once someone defines `has_limits UniformSpace`, turn this into an instance.
example [HasLimits.{u} UniformSpaceCat.{u}] : HasLimits.{u} CpltSepUniformSpace.{u} :=
  has_limits_of_reflective <| forget₂ CpltSepUniformSpace UniformSpaceCat.{u}

end UniformSpaceCat

