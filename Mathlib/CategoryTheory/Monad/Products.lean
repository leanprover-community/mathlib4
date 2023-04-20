/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.monad.products
! leanprover-community/mathlib commit d6814c584384ddf2825ff038e868451a7c956f31
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Over
import Mathbin.CategoryTheory.Monad.Algebra
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Algebras for the coproduct monad

The functor `Y ↦ X ⨿ Y` forms a monad, whose category of monads is equivalent to the under category
of `X`. Similarly, `Y ↦ X ⨯ Y` forms a comonad, whose category of comonads is equivalent to the
over category of `X`.

## TODO

Show that `over.forget X : over X ⥤ C` is a comonadic left adjoint and `under.forget : under X ⥤ C`
is a monadic right adjoint.
-/


noncomputable section

universe v u

-- morphism levels before object levels. See note [category_theory universes].
namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] (X : C)

section

open Comonad

variable [HasBinaryProducts C]

/-- `X ⨯ -` has a comonad structure. This is sometimes called the writer comonad. -/
@[simps]
def prodComonad : Comonad C where
  toFunctor := prod.functor.obj X
  ε' := { app := fun Y => Limits.prod.snd }
  δ' := { app := fun Y => prod.lift Limits.prod.fst (𝟙 _) }
#align category_theory.prod_comonad CategoryTheory.prodComonad

/-- The forward direction of the equivalence from coalgebras for the product comonad to the over
category.
-/
@[simps]
def coalgebraToOver : Coalgebra (prodComonad X) ⥤ Over X
    where
  obj A := Over.mk (A.a ≫ Limits.prod.fst)
  map A₁ A₂ f :=
    Over.homMk f.f
      (by
        rw [over.mk_hom, ← f.h_assoc]
        dsimp
        simp)
#align category_theory.coalgebra_to_over CategoryTheory.coalgebraToOver

/-- The backward direction of the equivalence from coalgebras for the product comonad to the over
category.
-/
@[simps]
def overToCoalgebra : Over X ⥤ Coalgebra (prodComonad X)
    where
  obj f :=
    { A := f.left
      a := prod.lift f.Hom (𝟙 _) }
  map f₁ f₂ g := { f := g.left }
#align category_theory.over_to_coalgebra CategoryTheory.overToCoalgebra

/-- The equivalence from coalgebras for the product comonad to the over category. -/
@[simps]
def coalgebraEquivOver : Coalgebra (prodComonad X) ≌ Over X
    where
  Functor := coalgebraToOver X
  inverse := overToCoalgebra X
  unitIso :=
    NatIso.ofComponents
      (fun A =>
        Coalgebra.isoMk (Iso.refl _)
          (prod.hom_ext
            (by
              dsimp
              simp)
            (by
              dsimp
              simpa using A.counit)))
      fun A₁ A₂ f => by
      ext
      simp
  counitIso := NatIso.ofComponents (fun f => Over.isoMk (Iso.refl _)) fun f g k => by tidy
#align category_theory.coalgebra_equiv_over CategoryTheory.coalgebraEquivOver

end

section

open _Root_.Monad

variable [HasBinaryCoproducts C]

/-- `X ⨿ -` has a monad structure. This is sometimes called the either monad. -/
@[simps]
def coprodMonad : Monad C where
  toFunctor := coprod.functor.obj X
  η' := { app := fun Y => coprod.inr }
  μ' := { app := fun Y => coprod.desc coprod.inl (𝟙 _) }
#align category_theory.coprod_monad CategoryTheory.coprodMonad

/-- The forward direction of the equivalence from algebras for the coproduct monad to the under
category.
-/
@[simps]
def algebraToUnder : Monad.Algebra (coprodMonad X) ⥤ Under X
    where
  obj A := Under.mk (coprod.inl ≫ A.a)
  map A₁ A₂ f :=
    Under.homMk f.f
      (by
        rw [under.mk_hom, assoc, ← f.h]
        dsimp
        simp)
#align category_theory.algebra_to_under CategoryTheory.algebraToUnder

/-- The backward direction of the equivalence from algebras for the coproduct monad to the under
category.
-/
@[simps]
def underToAlgebra : Under X ⥤ Monad.Algebra (coprodMonad X)
    where
  obj f :=
    { A := f.right
      a := coprod.desc f.Hom (𝟙 _) }
  map f₁ f₂ g := { f := g.right }
#align category_theory.under_to_algebra CategoryTheory.underToAlgebra

/-- The equivalence from algebras for the coproduct monad to the under category.
-/
@[simps]
def algebraEquivUnder : Monad.Algebra (coprodMonad X) ≌ Under X
    where
  Functor := algebraToUnder X
  inverse := underToAlgebra X
  unitIso :=
    NatIso.ofComponents
      (fun A =>
        Monad.Algebra.isoMk (Iso.refl _)
          (coprod.hom_ext (by tidy)
            (by
              dsimp
              simpa using A.unit.symm)))
      fun A₁ A₂ f => by
      ext
      simp
  counitIso :=
    NatIso.ofComponents (fun f => Under.isoMk (Iso.refl _) (by tidy)) fun f g k => by tidy
#align category_theory.algebra_equiv_under CategoryTheory.algebraEquivUnder

end

end CategoryTheory

