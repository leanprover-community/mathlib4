/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Opposites

open CategoryTheory

open Lean Meta Qq Lean.Elab.Command

/-- Contains information about a category that a theorem quantifies over. -/
structure CategoryInformation where
  /-- Universe level of objects. -/
  u : Level
  /-- Universe level of morphisms. -/
  v : Level
  /-- The type of objects. -/
  T : Expr
  /-- The category instance. -/
  cat : Expr
  /-- The quiver instance for easy access to morphisms. Always equal to
      `cat.toCategoryStruct.toQuiver`. -/
  quiv : Expr

def withLocalCategory {α : Type} (n v u : Name) (k : CategoryInformation → MetaM α) : MetaM α := do
  let u : Level := .param u
  withLocalDecl n .default (.sort (.succ u)) fun C => do
    let v : Level := .param v
    let instName ← mkFreshUserName `inst
    withLocalDecl instName .instImplicit (mkApp (.const ``Category [v, u]) C) fun instCategoryC =>
      let categoryStructC := mkAppN (.const ``Category.toCategoryStruct [v, u]) #[C, instCategoryC]
      let quiverC := mkAppN (.const ``CategoryStruct.toQuiver [v, u]) #[C, categoryStructC]
      k ⟨u, v, C, instCategoryC, quiverC⟩

def functorType (C D : CategoryInformation) : Expr :=
 mkAppN (.const ``CategoryTheory.Functor [C.v, D.v, C.u, D.u]) #[C.T, C.cat, D.T, D.cat]

def withLocalFunctor {α : Type} (F : Name) (C D : CategoryInformation) (k : Expr → MetaM α) :
    MetaM α := do
  withLocalDecl F .default (functorType C D) k

def addOneEqualsOne : MetaM Unit := do
  withLocalCategory `C `v `u fun C => do
    withLocalDecl `X .implicit C.T fun X => do
      withLocalDecl `Y .implicit C.T fun Y => do
        let homType := mkApp4 (.const ``Quiver.Hom [.succ C.v, C.u]) C.T C.quiv X Y
        withLocalDecl `f .default homType fun f => do
          let fEqf ← mkAppM ``Eq #[f, f]
          -- let rfl ← mkAppM ``Eq.refl #[f]
          let statement ← mkForallFVars #[C.T, C.cat, X, Y, f] fEqf
          let proof ← mkSorry statement false
          addDecl <| .thmDecl {
            name := `one_equals_one
            levelParams := [`v, `u]
            type := statement
            value := proof }

elab "add_one_equals_one" : command =>
  liftCoreM <| MetaM.run' addOneEqualsOne

add_one_equals_one

#print one_equals_one

#check one_equals_one

example : 1 = 1 := one_equals_one
