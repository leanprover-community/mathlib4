/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Monad.Algebra

/-!
# Algebras for the coproduct monad

The functor `Y ↦ X ⨿ Y` forms a monad, whose category of monads is equivalent to the under category
of `X`. Similarly, `Y ↦ X ⨯ Y` forms a comonad, whose category of coalgebras is equivalent to the
over category of `X`.

## TODO

Show that `Over.forget X : Over X ⥤ C` is a comonadic left adjoint and `Under.forget : Under X ⥤ C`
is a monadic right adjoint.
-/

@[expose] public section


noncomputable section

universe v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] (X : C)

section

open Comonad

variable [HasBinaryProducts C]

set_option backward.isDefEq.respectTransparency false in
/-- `X ⨯ -` has a comonad structure. This is sometimes called the writer comonad. -/
@[simps!]
def prodComonad : Comonad C where
  toFunctor := prod.functor.obj X
  ε := { app := fun _ => Limits.prod.snd }
  δ := { app := fun _ => prod.lift Limits.prod.fst (𝟙 _) }

set_option backward.isDefEq.respectTransparency false in
/-- The forward direction of the equivalence from coalgebras for the product comonad to the over
category.
-/
@[simps]
def coalgebraToOver : Coalgebra (prodComonad X) ⥤ Over X where
  obj A := Over.mk (A.a ≫ Limits.prod.fst)
  map f := Over.homMk f.f (by simp [← dsimp% f.h_assoc])

set_option backward.isDefEq.respectTransparency false in
/-- The backward direction of the equivalence from coalgebras for the product comonad to the over
category.
-/
@[simps]
def overToCoalgebra : Over X ⥤ Coalgebra (prodComonad X) where
  obj f :=
    { A := f.left
      a := prod.lift f.hom (𝟙 _) }
  map g := { f := g.left }

set_option backward.isDefEq.respectTransparency false in
/-- The equivalence from coalgebras for the product comonad to the over category. -/
@[simps]
def coalgebraEquivOver : Coalgebra (prodComonad X) ≌ Over X where
  functor := coalgebraToOver X
  inverse := overToCoalgebra X
  unitIso := NatIso.ofComponents fun A =>
    Coalgebra.isoMk (Iso.refl _) (Limits.prod.hom_ext (by simp) (by simpa using A.counit))
  counitIso := NatIso.ofComponents fun f => Over.isoMk (Iso.refl _)

end

section

open Monad

variable [HasBinaryCoproducts C]

set_option backward.isDefEq.respectTransparency false in
/-- `X ⨿ -` has a monad structure. This is sometimes called the either monad. -/
@[simps!]
def coprodMonad : Monad C where
  toFunctor := coprod.functor.obj X
  η := { app := fun _ => coprod.inr }
  μ := { app := fun _ => coprod.desc coprod.inl (𝟙 _) }

set_option backward.isDefEq.respectTransparency false in
/-- The forward direction of the equivalence from algebras for the coproduct monad to the under
category.
-/
@[simps]
def algebraToUnder : Monad.Algebra (coprodMonad X) ⥤ Under X where
  obj A := Under.mk (coprod.inl ≫ A.a)
  map f := Under.homMk f.f (by simp [← dsimp% f.h])

set_option backward.isDefEq.respectTransparency false in
/-- The backward direction of the equivalence from algebras for the coproduct monad to the under
category.
-/
@[simps]
def underToAlgebra : Under X ⥤ Monad.Algebra (coprodMonad X) where
  obj f :=
    { A := f.right
      a := coprod.desc f.hom (𝟙 _) }
  map g := { f := g.right }

set_option backward.isDefEq.respectTransparency false in
/-- The equivalence from algebras for the coproduct monad to the under category.
-/
@[simps]
def algebraEquivUnder : Monad.Algebra (coprodMonad X) ≌ Under X where
  functor := algebraToUnder X
  inverse := underToAlgebra X
  unitIso := NatIso.ofComponents fun A =>
    Monad.Algebra.isoMk (Iso.refl _) (coprod.hom_ext (by simp) (by simpa using A.unit.symm))
  counitIso :=
    NatIso.ofComponents fun f => Under.isoMk (Iso.refl _)

end

end CategoryTheory
