/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Comon_

/-!
# The category of bimonoids in a braided monoidal category.

We define bimonoids in a braided monoidal category `C`
as comonoid objects in the category of monoid objects in `C`.
-/

noncomputable section

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory C]

/--
A bimonoid object in a braided category `C` is a comonoid object in the (monoidal)
category of monoid objects in `C`.
-/
def Bimon_ := Comon_ (Mon_ C)

instance : Category (Bimon_ C) := inferInstanceAs (Category (Comon_ (Mon_ C)))

/-- The forgetful functor from bimonoid objects to monoid objects. -/
abbrev toMon_ : Bimon_ C ⥤ Mon_ C := Comon_.forget (Mon_ C)

/-- The forgetful functor from bimonoid objects to the underlying category. -/
def forget : Bimon_ C ⥤ C := toMon_ C ⋙ Mon_.forget C

@[simp]
theorem toMon_forget : toMon_ C ⋙ Mon_.forget C = forget C := rfl

/-- The forgetful functor from bimonoid objects to comonoid objects. -/
@[simps!]
def toComon_ : Bimon_ C ⥤ Comon_ C := (Mon_.forgetMonoidal C).toOplaxMonoidalFunctor.mapComon

@[simp]
theorem toComon_forget : toComon_ C ⋙ Comon_.forget C = forget C := rfl

@[simp] theorem foo {V} [Quiver V] {X Y x} :
    @Quiver.Hom.unop V _ X Y (Opposite.op (unop := x)) = x := rfl

@[simps]
def to_Mon_Comon_obj (M : Bimon_ C) : Mon_ (Comon_ C) where
  X := (toComon_ C).obj M
  one := { hom := M.X.one }
  mul := { hom := M.X.mul, hom_comul := sorry, }
  mul_one := by
    ext
    simp
    fail_if_success
      simp only [foo] -- Doesn't work as a simp lemma until we specify the universe levels explicitly!
    simp only [foo.{v₁ + 1}]
    -- This should just be by `Quiver.Hom.unop_mk`, but I can't get that to fire at all.
    simp
  one_mul := sorry
  mul_assoc := sorry

def to_Mon_Comon : Bimon_ C ⥤ Mon_ (Comon_ C) where
  obj := to_Mon_Comon_obj C
  map f :=
  { hom := (toComon_ C).map f,
    one_hom := by
      ext
      simp,
    mul_hom := by
      ext
      simp
      sorry }

def equiv_Mon_Comon : Bimon_ C ≌ Mon_ (Comon_ C) := sorry

end
