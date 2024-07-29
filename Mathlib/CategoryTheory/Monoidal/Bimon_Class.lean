/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Comon_Class

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

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C]
variable [BraidedCategory C]

open scoped Mon_ Comon_

class Bimon_ (M : C) extends Mon_ M, Comon_ M where
  mul_comp_comul : (μ ≫ Δ : M ⊗ M ⟶ M ⊗ M) = (Δ ⊗ Δ) ≫ μ := by aesop_cat
  one_comp_comul : (η ≫ Δ : 𝟙_ C ⟶ M ⊗ M) = η := by aesop_cat
  mul_comp_counit : (μ ≫ ε : M ⊗ M ⟶ 𝟙_ C) = (ε ⊗ ε) ≫ μ := by aesop_cat
  one_comp_counit : (η : 𝟙_ C ⟶ M) ≫ ε = η := by aesop_cat

namespace Bimon_



end Bimon_

/--
A bimonoid object in a braided category `C` is a comonoid object in the (monoidal)
category of monoid objects in `C`.
-/
def Bimon_Cat := Comon_Cat (Mon_Cat C)

namespace Bimon_

variable {C}

instance : Category (Bimon_Cat C) := inferInstanceAs (Category (Comon_Cat (Mon_Cat C)))

def mk (M : Mon_Cat C) [Comon_ M] : Bimon_Cat C := Comon_Cat.mk M

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

instance (M : Bimon_Cat C) : Comon_ M.X.X := inferInstanceAs (Comon_ (((toComon_ C).obj M).X))


@[simp]
example (M : Mon_Cat C) [Comon_ M] :((toComon_ C).obj (Comon_Cat.mk M)) = sorry := by
  dsimp [toComon_]
  dsimp [OplaxMonoidalFunctor.mapComon]

instance (M : Mon_Cat C) [Comon_ M] : Comon_ M.X :=
  inferInstanceAs (Comon_ (Bimon_.mk M : Bimon_Cat C).X.X)

@[simp]
theorem toComon_counit (M : Mon_Cat C) [Comon_ M] :
    (ε : M.X  ⟶ _) = (ε : M ⟶ _).hom := by
  erw [OplaxMonoidalFunctor.instComon_Obj_counit]
  simp

@[simp]
theorem toComon_comul (M : Mon_Cat C) [Comon_ M] :
    (Δ : M.X ⟶ _) = (Δ : M ⟶ _).hom := by
  erw [OplaxMonoidalFunctor.instComon_Obj_comul]
  simp

instance toMon_Comon_objInst (M : Mon_Cat C) [Comon_ M] : Mon_ (Comon_Cat.mk M.X) where
  one := { hom := (η : _ ⟶ M.X) }
  mul := { hom := (μ : _ ⟶ M.X) }

/-- The object level part of the forward direction of `Comon_ (Mon_ C) ≌ Mon_ (Comon_ C)` -/
def toMon_Comon_obj (M : Mon_Cat C) [Comon_ M] : Mon_Cat (Comon_Cat C) where
  X := Comon_Cat.mk M.X

attribute [simps!?] toMon_Comon_objInst toMon_Comon_obj -- We add this after the fact to avoid a timeout.

/-- The forward direction of `Comon_ (Mon_ C) ≌ Mon_ (Comon_ C)` -/
@[simps]
def toMon_Comon_ : Bimon_Cat C ⥤ Mon_Cat (Comon_Cat C) where
  obj M := toMon_Comon_obj C M.X
  map f :=
  { hom := (toComon_ C).map f }

instance (M : Comon_Cat C) [Mon_ M] : Mon_ M.X :=
  inferInstanceAs (Mon_ ((Comon_Cat.forgetMonoidal C).obj M))

@[simp]
theorem MonCatComonCatOne (M : Comon_Cat C) [Mon_ M] :
    (η : 𝟙_ C ⟶ M.X) = (η : 𝟙_ (Comon_Cat C) ⟶ M).hom :=
  calc
    _ = 𝟙 (𝟙_ C) ≫ (η : 𝟙_ (Comon_Cat C) ⟶ M).hom := rfl
    _ = _ := by simp

@[simp]
theorem MonCatComonCatmul  (M : Comon_Cat C) [Mon_ M] :
    (μ : M.X ⊗ M.X ⟶ M.X) = (μ : M ⊗ M ⟶ M).hom :=
  calc
    _ = 𝟙 (M.X ⊗ M.X) ≫ (μ : M ⊗ M ⟶ M).hom := rfl
    _ = _ := by simp

-- @[simp]
-- theorem MonCatComonCatOne (M : Mon_Cat (Comon_Cat C)) :
--     (η : 𝟙_ (Comon_Cat C) ⟶ M.X).hom  = (η : 𝟙_ C ⟶ M.X.X) :=
--   calc
--     _ = 𝟙 (𝟙_ C) ≫ (η : 𝟙_ (Comon_Cat C) ⟶ M.X).hom := by simp
--     _ = _ := rfl

example (M : Mon_Cat (Comon_Cat C)) : ((Comon_Cat.forgetMonoidal C).toLaxMonoidalFunctor.mapMon.obj M) = sorry := by
  dsimp [LaxMonoidalFunctor.mapMon]

instance (M : Comon_Cat C) [Mon_ M] : Comon_ (Mon_Cat.mk M.X) where
  counit :=
  { hom := (ε : M.X ⟶ _) }
  comul :=
  { hom := (Δ : M.X ⟶ _),
    mul_hom := by dsimp; simp [tensor_μ] }


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

/-- The object level part of the backward direction of `Comon_ (Mon_ C) ≌ Mon_ (Comon_ C)` -/
@[simps]
def ofMon_Comon_obj (M : Comon_Cat C) [Mon_ M] : Bimon_Cat C where
  X := Mon_Cat.mk M.X

/-- The backward direction of `Comon_ (Mon_ C) ≌ Mon_ (Comon_ C)` -/
@[simps]
def ofMon_Comon_ : Mon_Cat (Comon_Cat C) ⥤ Bimon_Cat C where
  obj M := ofMon_Comon_obj C M.X
  map f :=
  { hom := (Comon_Cat.forgetMonoidal C).toLaxMonoidalFunctor.mapMon.map f }

/-- The equivalence `Comon_ (Mon_ C) ≌ Mon_ (Comon_ C)` -/
def equivMon_Comon_ : Bimon_Cat C ≌ Mon_Cat (Comon_Cat C) where
  functor := toMon_Comon_ C
  inverse := ofMon_Comon_ C
  unitIso := NatIso.ofComponents (fun _ => Comon_.mkIso (Mon_.mkIso (Iso.refl _)))
  counitIso := NatIso.ofComponents (fun _ => Mon_.mkIso (Comon_.mkIso (Iso.refl _)))

end Bimon_
