/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.CategoryTheory.Monoidal.Comon_
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# The category of commutative comonoids in a braided monoidal category.

We define the category of commutative comonoid objects in a braided monoidal category `C`.

## Main definitions

* `CommComon C` - The bundled structure of commutative comonoid objects

## Tags

comonoid, commutative, braided
-/

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace CategoryTheory

open MonoidalCategory ComonObj Functor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory.{v₁} C]

variable (C) in
/-- A commutative comonoid object internal to a monoidal category. -/
structure CommComon where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [comon : ComonObj X]
  [comm : IsCommComonObj X]

attribute [instance] CommComon.comon CommComon.comm

namespace CommComon

/-- A commutative comonoid object is a comonoid object. -/
@[simps X]
def toComon (A : CommComon C) : Comon C := ⟨A.X⟩

section

attribute [local instance] ComonObj.instTensorUnit in
/-- The trivial comonoid on the unit object is commutative. -/
instance instCommComonObjUnit : IsCommComonObj (𝟙_ C) where
  comul_comm := by simp [← unitors_equal]

end

attribute [local instance] ComonObj.instTensorUnit in
variable (C) in
/-- The trivial commutative comonoid object. We later show this is initial in `CommComon C`. -/
@[simps!]
def trivial : CommComon C := mk (𝟙_ C)

instance : Inhabited (CommComon C) :=
  ⟨trivial C⟩

variable {M : CommComon C}

instance : Category (CommComon C) :=
  InducedCategory.category CommComon.toComon

@[simp]
theorem id_hom (A : CommComon C) : Comon.Hom.hom (𝟙 A) = 𝟙 A.X :=
  rfl

@[simp]
theorem comp_hom {R S T : CommComon C} (f : R ⟶ S) (g : S ⟶ T) :
    Comon.Hom.hom (f ≫ g) = f.hom ≫ g.hom :=
  rfl

@[ext]
lemma hom_ext {A B : CommComon C} (f g : A ⟶ B) (h : f.hom = g.hom) : f = g :=
  Comon.Hom.ext h

section

variable (C)

/-- The forgetful functor from commutative comonoid objects to comonoid objects. -/
@[simps!]
def forget₂Comon : CommComon C ⥤ Comon C :=
  inducedFunctor _

end

end CommComon

end CategoryTheory
