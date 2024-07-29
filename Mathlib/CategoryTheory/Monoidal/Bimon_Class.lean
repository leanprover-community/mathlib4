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

open scoped Mon_ Comon_

class Bimon_ (M : C) extends Mon_ M, Comon_ M where
  mul_comul' : μ ≫ Δ = (Δ ⊗ Δ) ≫ tensor_μ C (M, M) (M, M) ≫ (μ ⊗ μ) := by aesop_cat
  one_comul' : (η ≫ Δ : 𝟙_ C ⟶ M ⊗ M) = η := by aesop_cat
  mul_counit' : (μ ≫ ε : M ⊗ M ⟶ 𝟙_ C) = ε := by aesop_cat
  one_counit' : (η : 𝟙_ C ⟶ M) ≫ ε = 𝟙 (𝟙_ C) := by aesop_cat

namespace Bimon_

show_panel_widgets [local Mathlib.Tactic.Widget.StringDiagram]

variable (M : C) [Bimon_ M]

@[reassoc (attr := simp)]
theorem mul_comul : μ ≫ Δ = (Δ ⊗ Δ) ≫ tensor_μ C (M, M) (M, M) ≫ (μ ⊗ μ) := mul_comul'

@[reassoc (attr := simp)]
theorem one_comul : (η ≫ Δ : 𝟙_ C ⟶ M ⊗ M) = η := one_comul'

@[reassoc (attr := simp)]
theorem mul_counit : (μ ≫ ε : M ⊗ M ⟶ 𝟙_ C) = ε := mul_counit'

@[reassoc (attr := simp)]
theorem one_counit : (η : 𝟙_ C ⟶ M) ≫ ε = 𝟙 (𝟙_ C) := one_counit'

end Bimon_

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
instance (M : C) [Bimon_ M] : Comon_ (Mon_Cat.mk M) where
  counit := { hom := (ε : M ⟶ 𝟙_ C) }
  comul := { hom := (Δ : M ⟶ M ⊗ M) }

@[simps!]
instance (M : C) [Bimon_ M] : Mon_ (Comon_Cat.mk M) where
  one := { hom := (η : 𝟙_ C ⟶ M) }
  mul := { hom := (μ : M ⊗ M ⟶ M) }

def mk (M : C) [Bimon_ M] : Bimon_Cat C where
  X := Mon_Cat.mk M

@[ext] lemma ext {X Y : Bimon_Cat C} {f g : X ⟶ Y} (w : f.hom.hom = g.hom.hom) : f = g :=
  Comon_.Hom.ext _ _ (Mon_.Hom.ext _ _ w)

@[simp] theorem id_hom' (M : Bimon_Cat C) : Comon_.Hom.hom (𝟙 M) = 𝟙 M.X := rfl

@[simp]
theorem comp_hom' {M N K : Bimon_Cat C} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

variable (C)

/-- The forgetful functor from bimonoid objects to monoid objects. -/
abbrev toMon_ : Bimon_Cat C ⥤ Mon_Cat C := Comon_Cat.forget (Mon_Cat C)

/-- The forgetful functor from bimonoid objects to the underlying category. -/
def forget : Bimon_Cat C ⥤ C := toMon_ C ⋙ Mon_Cat.forget C

@[simp]
theorem toMon_forget : toMon_ C ⋙ Mon_Cat.forget C = forget C := rfl

/-- The forgetful functor from bimonoid objects to comonoid objects. -/
@[simps!?]
def toComon_ : Bimon_Cat C ⥤ Comon_Cat C :=
  (Mon_Cat.forgetMonoidal C).toOplaxMonoidalFunctor.mapComon

-- instance (M : Bimon_Cat C) : Comon_ (toComon_ C ⋙ forget C) M := inferInstance

@[simp]
theorem toComon_forget : toComon_ C ⋙ Comon_Cat.forget C = forget C := rfl

open scoped Mon_ Comon_

@[simps!?]
instance (M : Bimon_Cat C) : Comon_ M.X.X := inferInstanceAs (Comon_ (((toComon_ C).obj M).X))

-- @[simps!?]
instance (M : Bimon_Cat C) : Bimon_ M.X.X where

-- @[simp]
-- theorem toComon_counit  (M : Bimon_Cat C)  :
--     (ε : M.X.X  ⟶ _) = (ε : M.X ⟶ _).hom := by
--   erw [OplaxMonoidalFunctor.instComon_Obj_counit]
--   simp

-- @[simp]
-- theorem toComon_comul (M : Bimon_Cat C)  :
--     (Δ : M.X.X ⟶ _) = (Δ : M.X ⟶ _).hom := by
--   erw [OplaxMonoidalFunctor.instComon_Obj_comul]
--   simp

/-- The object level part of the forward direction of `Comon_ (Mon_ C) ≌ Mon_ (Comon_ C)` -/
def toMon_Comon_obj (M : C) [Bimon_ M] : Mon_Cat (Comon_Cat C) where
  X := Comon_Cat.mk M

attribute [simps!?] toMon_Comon_obj -- We add this after the fact to avoid a timeout.

/-- The forward direction of `Comon_ (Mon_ C) ≌ Mon_ (Comon_ C)` -/
@[simps]
def toMon_Comon_ : Bimon_Cat C ⥤ Mon_Cat (Comon_Cat C) where
  obj M := toMon_Comon_obj C M.X.X
  map f :=
  { hom := (toComon_ C).map f }

-- instance (M : C) [Bimon_ M] : Mon_ M := inferInstance
--   inferInstanceAs (Mon_ ((Comon_Cat.forgetMonoidal C).obj (Comon_Cat.mk M)))

@[simps!]
instance (M : (Comon_Cat C)) [Mon_ M] : Mon_ M.X :=
  inferInstanceAs (Mon_ ((Comon_Cat.forgetMonoidal C).obj M))




-- @[simp]
-- theorem MonCatComonCatOne (M : C) [Bimon_ M] :
--     (η : 𝟙_ C ⟶ M) = (η : 𝟙_ (Comon_Cat C) ⟶ (Comon_Cat.mk M)).hom := rfl
  -- calc
  --   _ = 𝟙 (𝟙_ C) ≫ (η : 𝟙_ (Comon_Cat C) ⟶ (Comon_Cat.mk M)).hom := rfl
  --   _ = _ := by simp

-- @[simp]
-- theorem MonCatComonCatmul (M : C) [Bimon_ M] :
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

-- instance (M : C) [Bimon_ M] : Comon_ (Mon_Cat.mk M.X) where
--   counit :=
--   { hom := (ε : M.X ⟶ _) }
--   comul :=
--   { hom := (Δ : M.X ⟶ _),
--     mul_hom := by dsimp; simp [tensor_μ] }


-- instance (M : (Comon_Cat C)) [Mon_ M] : Comon_ (Mon_Cat.mk M.X) where
--   counit := (ε : M.X ⟶ _)
--   comul := (Δ : M.X ⟶ _)
  -- { hom := (Δ : M.X ⟶ _),
  -- mul_hom' := by dsimp; simp [tensor_μ]

-- instance (M : Mon_Cat (Comon_Cat C)) : Comon_ M where
--   counit :=
--   { hom := (ε : M.X.X ⟶ _) }
--   comul :=
--   { hom := (Δ : M.X.X ⟶ _),
--     mul_hom := by dsimp; simp [tensor_μ] }

-- @[simps!?]
instance (M : Mon_Cat (Comon_Cat C)) : Bimon_ M.X.X where

-- @[simp]
-- theorem XXComon_Cat_one (M : Mon_Cat (Comon_Cat C)) : η = (η : 𝟙_ (Comon_Cat C) ⟶ M.X).hom := by
--   simp

-- @[simp]
-- theorem XXComon_Cat_mul (M : Mon_Cat (Comon_Cat C)) :
--     (μ : M.X.X ⊗ M.X.X ⟶ M.X.X) = (μ : M.X ⊗ M.X ⟶ M.X).hom := by
--   simp

/-- The object level part of the backward direction of `Comon_ (Mon_ C) ≌ Mon_ (Comon_ C)` -/
@[simps]
def ofMon_Comon_obj (M : C) [Bimon_ M] : Bimon_Cat C where
  X := Mon_Cat.mk M

/-- The backward direction of `Comon_ (Mon_ C) ≌ Mon_ (Comon_ C)` -/
@[simps]
def ofMon_Comon_ : Mon_Cat (Comon_Cat C) ⥤ Bimon_Cat C where
  obj M := ofMon_Comon_obj C M.X.X
  map f :=
  { hom := (Comon_Cat.forgetMonoidal C).toLaxMonoidalFunctor.mapMon.map f }

/-- The equivalence `Comon_ (Mon_ C) ≌ Mon_ (Comon_ C)` -/
def equivMon_Comon_ : Bimon_Cat C ≌ Mon_Cat (Comon_Cat C) where
  functor := toMon_Comon_ C
  inverse := ofMon_Comon_ C
  unitIso := NatIso.ofComponents (fun M =>
    Comon_Cat.mkIso (Comon_.mkIso (Mon_Cat.mkIso (Mon_.mkIso (Iso.refl M.X.X)
      (by simp; change _ = _ ≫ _; simp) (by simp; change _ = _ ≫ _; simp)))
      (by ext; simp; change _ ≫ _ = _; simp) (by ext; simp; change _ ≫ _ = _; simp)))
  counitIso := NatIso.ofComponents (fun M =>
    Mon_Cat.mkIso (Mon_.mkIso (Comon_Cat.mkIso (Comon_.mkIso (Iso.refl M.X.X)
      (by simp; change _ = _ ≫ _; simp) (by simp; change _ = _ ≫ _; simp)))
      (by ext; simp; change _ ≫ _ = _; simp) (by ext; simp; change _ ≫ _ = _; simp)))

end Bimon_Cat
