/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Comon_Class
import Mathlib.Tactic.Widget.StringDiagram

/-!
# The category of bimonoids in a braided monoidal category.

We define bimonoids in a braided monoidal category `C`
as comonoid objects in the category of monoid objects in `C`.

We verify that this is equivalent to the monoid objects in the category of comonoid objects.

## TODO
* Define Hopf monoids, which in a cartesian monoidal category are exactly group objects,
  and use this to define group schemes.
* Construct the category of modules, and show that it is monoidal with a monoidal forgetful functor
  to `C`.
* Some form of Tannaka reconstruction:
  given a monoidal functor `F : C ⥤ D` into a braided category `D`,
  the internal endomorphisms of `F` form a bimonoid in presheaves on `D`,
  in good circumstances this is representable by a bimonoid in `D`, and then
  `C` is monoidally equivalent to the modules over that bimonoid.
-/

noncomputable section

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]
variable [BraidedCategory C]

open scoped Mon_Class Comon_Class

class Bimon_Class (M : C) extends Mon_Class M, Comon_Class M where
  mul_comul' : μ ≫ Δ = (Δ ⊗ Δ) ≫ tensor_μ C (M, M) (M, M) ≫ (μ ⊗ μ) := by aesop_cat
  one_comul' : (η ≫ Δ : 𝟙_ C ⟶ M ⊗ M) = η := by aesop_cat
  mul_counit' : (μ ≫ ε : M ⊗ M ⟶ 𝟙_ C) = ε := by aesop_cat
  one_counit' : (η : 𝟙_ C ⟶ M) ≫ ε = 𝟙 (𝟙_ C) := by aesop_cat

namespace Bimon_Class

show_panel_widgets [local Mathlib.Tactic.Widget.StringDiagram]

variable (M : C) [Bimon_Class M]

@[reassoc (attr := simp)]
theorem mul_comul : μ ≫ Δ = (Δ ⊗ Δ) ≫ tensor_μ C (M, M) (M, M) ≫ (μ ⊗ μ) := mul_comul'

@[reassoc (attr := simp)]
theorem one_comul : (η ≫ Δ : 𝟙_ C ⟶ M ⊗ M) = η := one_comul'

@[reassoc (attr := simp)]
theorem mul_counit : (μ ≫ ε : M ⊗ M ⟶ 𝟙_ C) = ε := mul_counit'

@[reassoc (attr := simp)]
theorem one_counit : (η : 𝟙_ C ⟶ M) ≫ ε = 𝟙 (𝟙_ C) := one_counit'

end Bimon_Class

variable (C)

/--
A bimonoid object in a braided category `C` is a comonoid object in the (monoidal)
category of monoid objects in `C`.
-/
def Bimon_Cat := Comon_Cat (Mon_Cat C)

namespace Bimon_Cat

variable {C}

instance : Category (Bimon_Cat C) := inferInstanceAs (Category (Comon_Cat (Mon_Cat C)))

@[simps!]
instance (M : C) [Bimon_Class M] : Comon_Class (Mon_Cat.mk M) where
  counit := { hom := (ε : M ⟶ 𝟙_ C) }
  comul := { hom := (Δ : M ⟶ M ⊗ M) }

@[simps!]
instance (M : C) [Bimon_Class M] : Mon_Class (Comon_Cat.mk M) where
  one := { hom := (η : 𝟙_ C ⟶ M) }
  mul := { hom := (μ : M ⊗ M ⟶ M) }

def mk (M : C) [Bimon_Class M] : Bimon_Cat C where
  X := Mon_Cat.mk M

@[ext] lemma ext {X Y : Bimon_Cat C} {f g : X ⟶ Y} (w : f.hom.hom = g.hom.hom) : f = g :=
  Comon_Class.Hom.ext _ _ (Mon_Class.Hom.ext _ _ w)

@[simp] theorem id_hom' (M : Bimon_Cat C) : Comon_Class.Hom.hom (𝟙 M) = 𝟙 M.X := rfl

@[simp]
theorem comp_hom' {M N K : Bimon_Cat C} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

variable (C)

/-- The forgetful functor from bimonoid objects to monoid objects. -/
abbrev toMon_Class : Bimon_Cat C ⥤ Mon_Cat C := Comon_Cat.forget (Mon_Cat C)

/-- The forgetful functor from bimonoid objects to the underlying category. -/
def forget : Bimon_Cat C ⥤ C := toMon_Class C ⋙ Mon_Cat.forget C

@[simp]
theorem toMon_Classforget : toMon_Class C ⋙ Mon_Cat.forget C = forget C := rfl

/-- The forgetful functor from bimonoid objects to comonoid objects. -/
@[simps!]
def toComon_Class : Bimon_Cat C ⥤ Comon_Cat C :=
  (Mon_Cat.forgetMonoidal C).toOplaxMonoidalFunctor.mapComonCat

-- instance (M : Bimon_Cat C) : Comon_Class (toComon_Class C ⋙ forget C) M := inferInstance

@[simp]
theorem toComon_Classforget : toComon_Class C ⋙ Comon_Cat.forget C = forget C := rfl

open scoped Mon_Class Comon_Class

@[simps!]
instance (M : Bimon_Cat C) : Comon_Class M.X.X := inferInstanceAs (Comon_Class (((toComon_Class C).obj M).X))

-- @[simps!?]
instance (M : Bimon_Cat C) : Bimon_Class M.X.X where

-- @[simp]
-- theorem toComon_Classcounit  (M : Bimon_Cat C)  :
--     (ε : M.X.X  ⟶ _) = (ε : M.X ⟶ _).hom := by
--   erw [OplaxMonoidalFunctor.instComon_ClassObj_counit]
--   simp

-- @[simp]
-- theorem toComon_Classcomul (M : Bimon_Cat C)  :
--     (Δ : M.X.X ⟶ _) = (Δ : M.X ⟶ _).hom := by
--   erw [OplaxMonoidalFunctor.instComon_ClassObj_comul]
--   simp

/-- The object level part of the forward direction of `Comon_Class (Mon_Class C) ≌ Mon_Class (Comon_Class C)` -/
def toMon_ClassComon_Classobj (M : C) [Bimon_Class M] : Mon_Cat (Comon_Cat C) where
  X := Comon_Cat.mk M

attribute [simps!] toMon_ClassComon_Classobj -- We add this after the fact to avoid a timeout.

/-- The forward direction of `Comon_Class (Mon_Class C) ≌ Mon_Class (Comon_Class C)` -/
@[simps]
def toMon_ClassComon_Class : Bimon_Cat C ⥤ Mon_Cat (Comon_Cat C) where
  obj M := toMon_ClassComon_Classobj C M.X.X
  map f :=
  { hom := (toComon_Class C).map f }

-- instance (M : C) [Bimon_Class M] : Mon_Class M := inferInstance
--   inferInstanceAs (Mon_Class ((Comon_Cat.forgetMonoidal C).obj (Comon_Cat.mk M)))

@[simps!]
instance (M : (Comon_Cat C)) [Mon_Class M] : Mon_Class M.X :=
  inferInstanceAs (Mon_Class ((Comon_Cat.forgetMonoidal C).obj M))




-- @[simp]
-- theorem MonCatComonCatOne (M : C) [Bimon_Class M] :
--     (η : 𝟙_ C ⟶ M) = (η : 𝟙_ (Comon_Cat C) ⟶ (Comon_Cat.mk M)).hom := rfl
  -- calc
  --   _ = 𝟙 (𝟙_ C) ≫ (η : 𝟙_ (Comon_Cat C) ⟶ (Comon_Cat.mk M)).hom := rfl
  --   _ = _ := by simp

-- @[simp]
-- theorem MonCatComonCatmul (M : C) [Bimon_Class M] :
--     (μ : M ⊗ M ⟶ M) = (μ :  (Comon_Cat.mk M) ⊗  (Comon_Cat.mk M) ⟶  (Comon_Cat.mk M)).hom :=
--   calc
--     _ = 𝟙 (M ⊗ M) ≫ (μ : (Comon_Cat.mk M) ⊗  (Comon_Cat.mk M) ⟶  (Comon_Cat.mk M)).hom := rfl
--     _ = _ := by simp

-- @[simp]
-- theorem MonCatComonCatOne (M : Mon_Cat (Comon_Cat C)) :
--     (η : 𝟙_ (Comon_Cat C) ⟶ M.X).hom  = (η : 𝟙_ C ⟶ M.X.X) :=
--   calc
--     _ = 𝟙 (𝟙_ C) ≫ (η : 𝟙_ (Comon_Cat C) ⟶ M.X).hom := by simp
--     _ = _ := rfl

-- instance (M : C) [Bimon_Class M] : Comon_Class (Mon_Cat.mk M.X) where
--   counit :=
--   { hom := (ε : M.X ⟶ _) }
--   comul :=
--   { hom := (Δ : M.X ⟶ _),
--     mul_hom := by dsimp; simp [tensor_μ] }


-- instance (M : (Comon_Cat C)) [Mon_Class M] : Comon_Class (Mon_Cat.mk M.X) where
--   counit := (ε : M.X ⟶ _)
--   comul := (Δ : M.X ⟶ _)
  -- { hom := (Δ : M.X ⟶ _),
  -- mul_hom' := by dsimp; simp [tensor_μ]

-- instance (M : Mon_Cat (Comon_Cat C)) : Comon_Class M where
--   counit :=
--   { hom := (ε : M.X.X ⟶ _) }
--   comul :=
--   { hom := (Δ : M.X.X ⟶ _),
--     mul_hom := by dsimp; simp [tensor_μ] }

-- @[simps!?]
instance (M : Mon_Cat (Comon_Cat C)) : Bimon_Class M.X.X where

-- @[simp]
-- theorem XXComon_Cat_one (M : Mon_Cat (Comon_Cat C)) : η = (η : 𝟙_ (Comon_Cat C) ⟶ M.X).hom := by
--   simp

-- @[simp]
-- theorem XXComon_Cat_mul (M : Mon_Cat (Comon_Cat C)) :
--     (μ : M.X.X ⊗ M.X.X ⟶ M.X.X) = (μ : M.X ⊗ M.X ⟶ M.X).hom := by
--   simp

/-- The object level part of the backward direction of `Comon_Class (Mon_Class C) ≌ Mon_Class (Comon_Class C)` -/
@[simps]
def ofMon_ClassComon_Classobj (M : C) [Bimon_Class M] : Bimon_Cat C where
  X := Mon_Cat.mk M

/-- The backward direction of `Comon_Class (Mon_Class C) ≌ Mon_Class (Comon_Class C)` -/
@[simps]
def ofMon_ClassComon_Class : Mon_Cat (Comon_Cat C) ⥤ Bimon_Cat C where
  obj M := ofMon_ClassComon_Classobj C M.X.X
  map f :=
  { hom := (Comon_Cat.forgetMonoidal C).toLaxMonoidalFunctor.mapMonCat.map f }

/-- The equivalence `Comon_Class (Mon_Class C) ≌ Mon_Class (Comon_Class C)` -/
def equivMon_ClassComon_Class : Bimon_Cat C ≌ Mon_Cat (Comon_Cat C) where
  functor := toMon_ClassComon_Class C
  inverse := ofMon_ClassComon_Class C
  unitIso := NatIso.ofComponents (fun M =>
    Comon_Cat.mkIso (Comon_Class.mkIso (Mon_Cat.mkIso (Mon_Class.mkIso (Iso.refl M.X.X)
      (by simp; change _ = _ ≫ _; simp) (by simp; change _ = _ ≫ _; simp)))
      (by ext; simp; change _ ≫ _ = _; simp) (by ext; simp; change _ ≫ _ = _; simp)))
  counitIso := NatIso.ofComponents (fun M =>
    Mon_Cat.mkIso (Mon_Class.mkIso (Comon_Cat.mkIso (Comon_Class.mkIso (Iso.refl M.X.X)
      (by simp; change _ = _ ≫ _; simp) (by simp; change _ = _ ≫ _; simp)))
      (by ext; simp; change _ ≫ _ = _; simp) (by ext; simp; change _ ≫ _ = _; simp)))

end Bimon_Cat
