/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Creates

open Lean Elab Command

namespace CategoryTheory.Reflected

structure ReflectedCategory where mk' ::
  cat : Term
  opp : Term
  isOpp : Bool

def ReflectedCategory.mk (C : CommandElabM Term) : CommandElabM ReflectedCategory := do
  return ⟨← C, ← `($(← C)ᵒᵖ), false⟩

def ReflectedCategory.op : ReflectedCategory → ReflectedCategory
  | ⟨cat, opp, isOpp⟩ => ⟨opp, cat, !isOpp⟩

instance : Coe ReflectedCategory Term where
  coe := ReflectedCategory.cat

structure ReflectedFunctor where mk' ::
  dom : ReflectedCategory
  cod : ReflectedCategory
  self : Term
  opp : Term

def getFunctorOpposite (F : Term) (C : ReflectedCategory) (D : ReflectedCategory) :
    CommandElabM Term :=
  match C.isOpp, D.isOpp with
  | false, false => `($(F).op)
  | false, true  => `($(F).leftOp)
  | true,  false => `($(F).rightOp)
  | true,  true  => `($(F).unop)

def oppositeFunctorDeclarationName (C : ReflectedCategory) (D : ReflectedCategory) : String :=
  match C.isOpp, D.isOpp with
  | false, false => "Op"
  | false, true  => "LeftOp"
  | true,  false => "RightOp"
  | true,  true  => "Unop"

def ReflectedFunctor.mk (F : CommandElabM Term) (C : ReflectedCategory) (D : ReflectedCategory) :
    CommandElabM ReflectedFunctor := do
  return ⟨C, D, ← F, ← getFunctorOpposite (← F) C D⟩

def ReflectedFunctor.op : ReflectedFunctor → ReflectedFunctor
  | ⟨dom, cod, self, opp⟩ => ⟨dom.op, cod.op, opp, self⟩

instance : Coe ReflectedFunctor Term where
  coe := ReflectedFunctor.self

structure LimitContext where
  PreservesLimit : Term
  PreservesColimit : Term


def limitContext : CommandElabM LimitContext := do
  return {
      PreservesLimit := ← `(CategoryTheory.Limits.PreservesLimit)
      PreservesColimit := ← `(CategoryTheory.Limits.PreservesLimit) }
  -- return ⟨← `(CategoryTheory.Limits.PreservesLimit), ← `(CategoryTheory.Limits.PreservesColimit)⟩

end CategoryTheory.Reflected

section

open CategoryTheory.Reflected

open CategoryTheory Limits

universe w w' v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : Type w} [Category.{w'} J]

def mySyntax (n : Name) (C D J : ReflectedCategory) (K F : ReflectedFunctor) (c : LimitContext) (proof : Term) :
    CommandElabM Syntax :=
  `(def $(mkIdent n) (K : $(J) ⥤ $(C.op)) (F : $(C) ⥤ $(D)) [$(c.PreservesColimit) $(K.op) $(F)] :
        $(c.PreservesLimit) $(K) $(F.op) :=
      $proof)

elab "adds" : command => do
  let C' ← ReflectedCategory.mk `(C)
  let D' ← ReflectedCategory.mk `(D)
  let J ← ReflectedCategory.mk `(J)
  for C in [C', C'.op] do
    for D in [D', D'.op] do
      for backward in [false, true] do
        let K ← ReflectedFunctor.mk `(K) J C.op
        let F ← ReflectedFunctor.mk `(F) C D
        let colimit := false
        let innerName := "preserves" ++ (if colimit then "Colimit" else "Limit")
          ++ (if backward then "Of" else "") ++ oppositeFunctorDeclarationName C D
        let name : Name := .str (.str (.str .anonymous "CategoryTheory") "Limits") innerName
        let c ← limitContext
        elabCommand (← mySyntax name C D J K F c (← `(sorry)))
        let docstring := "This is another docstring"
        -- let docstring := s!"If {F'.asDocstring} preserves {if colimit then "" else "co"}limits "
        --   ++ s!"of {K.opposite.asDocstring}, then {F'.opposite.asDocstring} preserves "
        --   ++ s!"{if colimit then "co" else ""}limits of {K.asDocstring}."
        addDocString name docstring

adds

#check CategoryTheory.Limits.preservesLimitLeftOp

end
