/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Monoidal.End
import Mathlib.CategoryTheory.Monoidal.Mon_

/-!

# The equivalence between `Monad C` and `Mon_ (C ⥤ C)`.

A monad "is just" a monoid in the category of endofunctors.

# Definitions/Theorems

1. `toMon` associates a monoid object in `C ⥤ C` to any monad on `C`.
2. `monadToMon` is the functorial version of `toMon`.
3. `ofMon` associates a monad on `C` to any monoid object in `C ⥤ C`.
4. `monadMonEquiv` is the equivalence between `Monad C` and `Mon_ (C ⥤ C)`.

-/


namespace CategoryTheory

open Category Mon_Class

universe v u -- morphism levels before object levels. See note [category_theory universes].

variable {C : Type u} [Category.{v} C]

namespace Monad

attribute [local instance] endofunctorMonoidalCategory

@[simps]
instance (M : Monad C) : Mon_Class (M : C ⥤ C) where
  one := M.η
  mul := M.μ
  mul_assoc := by ext; simp [M.assoc]

/-- To every `Monad C` we associated a monoid object in `C ⥤ C`. -/
@[simps]
def toMon (M : Monad C) : Mon_ (C ⥤ C) where
  X := (M : C ⥤ C)

variable (C) in
/-- Passing from `Monad C` to `Mon_ (C ⥤ C)` is functorial. -/
@[simps]
def monadToMon : Monad C ⥤ Mon_ (C ⥤ C) where
  obj := toMon
  map f := .mk' f.toNatTrans

/-- To every monoid object in `C ⥤ C` we associate a `Monad C`. -/
@[simps «η» «μ»]
def ofMon (M : Mon_ (C ⥤ C)) : Monad C where
  toFunctor := M.X
  «η» := η[M.X]
  «μ» := μ[M.X]
  left_unit := fun X ↦ by
    simpa [-Mon_Class.mul_one] using congrArg (fun t ↦ t.app X) (mul_one M.X)
  right_unit := fun X ↦ by
    simpa [-Mon_Class.one_mul] using congrArg (fun t ↦ t.app X) (one_mul M.X)
  assoc := fun X ↦ by
    simpa [-Mon_Class.mul_assoc] using congrArg (fun t ↦ t.app X) (mul_assoc M.X)

-- Porting note: `@[simps]` fails to generate `ofMon_obj`:
@[simp] lemma ofMon_obj (M : Mon_ (C ⥤ C)) (X : C) : (ofMon M).obj X = M.X.obj X := rfl

variable (C)

/-- Passing from `Mon_ (C ⥤ C)` to `Monad C` is functorial. -/
@[simps]
def monToMonad : Mon_ (C ⥤ C) ⥤ Monad C where
  obj := ofMon
  map {X Y} f :=
    { f.hom with
      app_η X := by
        simpa [-IsMon_Hom.one_hom] using congrArg (fun t ↦ t.app X) (IsMon_Hom.one_hom f.hom)
      app_μ Z := by
        simpa [-IsMon_Hom.mul_hom] using congrArg (fun t ↦ t.app Z) (IsMon_Hom.mul_hom f.hom) }

/-- Oh, monads are just monoids in the category of endofunctors (equivalence of categories). -/
@[simps]
def monadMonEquiv : Monad C ≌ Mon_ (C ⥤ C) where
  functor := monadToMon _
  inverse := monToMonad _
  unitIso :=
  { hom := { app := fun _ ↦ { app := fun _ ↦ 𝟙 _ } }
    inv := { app := fun _ ↦ { app := fun _ ↦ 𝟙 _ } } }
  counitIso :=
  { hom := { app := fun _ ↦ { hom := 𝟙 _ } }
    inv := { app := fun _ ↦ { hom := 𝟙 _ } } }

-- Sanity check
example (A : Monad C) {X : C} : ((monadMonEquiv C).unitIso.app A).hom.app X = 𝟙 _ :=
  rfl

end Monad

end CategoryTheory
