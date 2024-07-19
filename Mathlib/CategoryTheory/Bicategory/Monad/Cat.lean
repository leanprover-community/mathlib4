/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.CategoryTheory.Bicategory.Monad.Basic
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Category.Cat
/-!
# Monads in Cat

-/

universe v₁ u₁

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

namespace Bicategory

namespace Monad

/-- A monad on `C` gives a monad in the bicategory `Cat`. -/
def ofCatMonad (T : CategoryTheory.Monad C) :
    Bicategory.Monad (a := Cat.of C) (T : C ⥤ C) where
  mul := T.μ
  unit := T.η
  assoc := T.assoc''
  -- The left/right inversion is due to differences in conventions of composition order.
  left_unit := T.right_unit''
  right_unit := T.left_unit''

/-- A comonad on `C` gives a comonad in the bicategory `Cat`. -/
def toCatMonad (T : C ⥤ C) [Bicategory.Monad (a := Cat.of C) (T : C ⥤ C)] :
    CategoryTheory.Monad C :=
  Monad.ofNatTransEq
    (T := T)
    (Monad.unit (a := Cat.of C))
    (Monad.mul (a := Cat.of C))
    (Monad.assoc (a := Cat.of C))
    (Monad.right_unit (a := Cat.of C))
    (Monad.left_unit (a := Cat.of C))

end Monad

/-- A comonad on `C` gives a comonad in the bicategory `Cat`. -/
def Comonad.ofCatComonad (G : CategoryTheory.Comonad C) :
    Bicategory.Comonad (a := Cat.of C) (G : C ⥤ C) where
  comul := G.δ
  counit := G.ε
  coassoc := G.coassoc''
  -- The left/right inversion is due to differences in conventions of composition order.
  left_counit := G.right_counit''
  right_counit := G.left_counit''

end Bicategory

end CategoryTheory
