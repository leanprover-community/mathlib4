/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Patrick Massot, Kim Morrison
-/
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.CategoryTheory.ConcreteCategory.UnbundledHom
import Mathlib.CategoryTheory.Monad.Limits
import Mathlib.Topology.Category.TopCat.Basic
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

namespace UniformSpaceCat

/-- The information required to build morphisms for `UniformSpace`. -/
instance : UnbundledHom @UniformContinuous :=
  ⟨@uniformContinuous_id, @UniformContinuous.comp⟩

deriving instance LargeCategory for UniformSpaceCat

instance : ConcreteCategory UniformSpaceCat :=
  inferInstanceAs <| ConcreteCategory <| Bundled UniformSpace

instance : CoeSort UniformSpaceCat Type* :=
  Bundled.coeSort

instance (x : UniformSpaceCat) : UniformSpace x :=
  x.str

/-- Construct a bundled `UniformSpace` from the underlying type and the typeclass. -/
def of (α : Type u) [UniformSpace α] : UniformSpaceCat :=
  ⟨α, ‹_›⟩

instance : Inhabited UniformSpaceCat :=
  ⟨UniformSpaceCat.of Empty⟩

@[simp]
theorem coe_of (X : Type u) [UniformSpace X] : (of X : Type u) = X :=
  rfl

instance (X Y : UniformSpaceCat) : CoeFun (X ⟶ Y) fun _ => X → Y :=
  ⟨(forget UniformSpaceCat).map⟩

@[simp]
theorem coe_comp {X Y Z : UniformSpaceCat} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : X → Z) = g ∘ f :=
  rfl

@[simp]
theorem coe_id (X : UniformSpaceCat) : (𝟙 X : X → X) = id :=
  rfl

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11119): removed `simp` attribute
-- due to `LEFT-HAND SIDE HAS VARIABLE AS HEAD SYMBOL.`
theorem coe_mk {X Y : UniformSpaceCat} (f : X → Y) (hf : UniformContinuous f) :
    ((⟨f, hf⟩ : X ⟶ Y) : X → Y) = f :=
  rfl

theorem hom_ext {X Y : UniformSpaceCat} {f g : X ⟶ Y} : (f : X → Y) = g → f = g :=
  Subtype.eq

/-- The forgetful functor from uniform spaces to topological spaces. -/
instance hasForgetToTop : HasForget₂ UniformSpaceCat.{u} TopCat.{u} where
  forget₂ :=
    { obj := fun X => TopCat.of X
      map := fun f =>
        { toFun := f
          continuous_toFun := f.property.continuous } }

end UniformSpaceCat

/-- A (bundled) complete separated uniform space. -/
structure CpltSepUniformSpace where
  /-- The underlying space -/
  α : Type u
  [isUniformSpace : UniformSpace α]
  [isCompleteSpace : CompleteSpace α]
  [isT0 : T0Space α]

namespace CpltSepUniformSpace

instance : CoeSort CpltSepUniformSpace (Type u) :=
  ⟨CpltSepUniformSpace.α⟩

attribute [instance] isUniformSpace isCompleteSpace isT0

/-- The function forgetting that a complete separated uniform spaces is complete and separated. -/
def toUniformSpace (X : CpltSepUniformSpace) : UniformSpaceCat :=
  UniformSpaceCat.of X

instance completeSpace (X : CpltSepUniformSpace) : CompleteSpace (toUniformSpace X).α :=
  CpltSepUniformSpace.isCompleteSpace X

instance t0Space (X : CpltSepUniformSpace) : T0Space (toUniformSpace X).α :=
  CpltSepUniformSpace.isT0 X

/-- Construct a bundled `UniformSpace` from the underlying type and the appropriate typeclasses. -/
def of (X : Type u) [UniformSpace X] [CompleteSpace X] [T0Space X] : CpltSepUniformSpace :=
  ⟨X⟩

@[simp]
theorem coe_of (X : Type u) [UniformSpace X] [CompleteSpace X] [T0Space X] :
    (of X : Type u) = X :=
  rfl

instance : Inhabited CpltSepUniformSpace :=
  ⟨CpltSepUniformSpace.of Empty⟩

/-- The category instance on `CpltSepUniformSpace`. -/
instance category : LargeCategory CpltSepUniformSpace :=
  InducedCategory.category toUniformSpace

/-- The concrete category instance on `CpltSepUniformSpace`. -/
instance concreteCategory : ConcreteCategory CpltSepUniformSpace :=
  InducedCategory.concreteCategory toUniformSpace

instance hasForgetToUniformSpace : HasForget₂ CpltSepUniformSpace UniformSpaceCat :=
  InducedCategory.hasForget₂ toUniformSpace

end CpltSepUniformSpace

namespace UniformSpaceCat

open UniformSpace

open CpltSepUniformSpace

/-- The functor turning uniform spaces into complete separated uniform spaces. -/
noncomputable def completionFunctor : UniformSpaceCat ⥤ CpltSepUniformSpace where
  obj X := CpltSepUniformSpace.of (Completion X)
  map f := ⟨Completion.map f.1, Completion.uniformContinuous_map⟩
  map_id _ := Subtype.eq Completion.map_id
  map_comp f g := Subtype.eq (Completion.map_comp g.property f.property).symm

/-- The inclusion of a uniform space into its completion. -/
def completionHom (X : UniformSpaceCat) :
    X ⟶ (forget₂ CpltSepUniformSpace UniformSpaceCat).obj (completionFunctor.obj X) where
  val := ((↑) : X → Completion X)
  property := Completion.uniformContinuous_coe X

@[simp]
theorem completionHom_val (X : UniformSpaceCat) (x) : (completionHom X) x = (x : Completion X) :=
  rfl

/-- The mate of a morphism from a `UniformSpace` to a `CpltSepUniformSpace`. -/
noncomputable def extensionHom {X : UniformSpaceCat} {Y : CpltSepUniformSpace}
    (f : X ⟶ (forget₂ CpltSepUniformSpace UniformSpaceCat).obj Y) :
    completionFunctor.obj X ⟶ Y where
  val := Completion.extension f
  property := Completion.uniformContinuous_extension

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/10754): added this instance to make things compile
instance (X : UniformSpaceCat) : UniformSpace ((forget _).obj X) :=
  show UniformSpace X from inferInstance

-- This was a global instance prior to https://github.com/leanprover-community/mathlib4/pull/13170. We may experiment with removing it.
attribute [local instance] CategoryTheory.ConcreteCategory.instFunLike in
@[simp]
theorem extensionHom_val {X : UniformSpaceCat} {Y : CpltSepUniformSpace}
    (f : X ⟶ (forget₂ _ _).obj Y) (x) : (extensionHom f) x = Completion.extension f x :=
  rfl

@[simp]
theorem extension_comp_coe {X : UniformSpaceCat} {Y : CpltSepUniformSpace}
    (f : toUniformSpace (CpltSepUniformSpace.of (Completion X)) ⟶ toUniformSpace Y) :
    extensionHom (completionHom X ≫ f) = f := by
  apply Subtype.eq
  funext x
  exact congr_fun (Completion.extension_comp_coe f.property) x

/-- The completion functor is left adjoint to the forgetful functor. -/
noncomputable def adj : completionFunctor ⊣ forget₂ CpltSepUniformSpace UniformSpaceCat :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => completionHom X ≫ f
          invFun := fun f => extensionHom f
          left_inv := fun f => by dsimp; rw [extension_comp_coe]
          right_inv := fun f => by
            apply Subtype.eq; funext x; cases f
            exact @Completion.extension_coe _ _ _ _ _ (CpltSepUniformSpace.t0Space _)
              ‹_› _ }
      homEquiv_naturality_left_symm := fun {X' X Y} f g => by
        apply hom_ext; funext x; dsimp
        erw [coe_comp]
        -- Porting note: used to be `erw [← Completion.extension_map]`
        have := (Completion.extension_map (γ := Y) (f := g) g.2 f.2)
        simp only [forget_map_eq_coe] at this ⊢
        erw [this]
        rfl }

noncomputable instance : Reflective (forget₂ CpltSepUniformSpace UniformSpaceCat) where
  adj := adj
  map_surjective f := ⟨f, rfl⟩

open CategoryTheory.Limits

-- TODO Once someone defines `HasLimits UniformSpace`, turn this into an instance.
example [HasLimits.{u} UniformSpaceCat.{u}] : HasLimits.{u} CpltSepUniformSpace.{u} :=
  hasLimits_of_reflective <| forget₂ CpltSepUniformSpace UniformSpaceCat.{u}

end UniformSpaceCat
