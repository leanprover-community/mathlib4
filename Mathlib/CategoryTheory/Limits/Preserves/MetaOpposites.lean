/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Opposites

open CategoryTheory

open Lean Meta Qq Lean.Elab.Command

/-- Contains information about a category that a theorem quantifies over. -/
structure CategoryData where
  /-- Universe level of objects. -/
  u : Level
  /-- Universe level of morphisms. -/
  v : Level
  /-- The type of objects. -/
  type : Expr
  /-- The type of objects of the opposite. -/
  typeop : Expr
  /-- The category instance. -/
  cat : Expr
  /-- The category instance of the opposite-/
  catop : Expr

structure CategoryWithPolarity where
  category : CategoryData
  isOpposite : Bool

def CategoryWithPolarity.u : CategoryWithPolarity → Level
| ⟨category, _⟩ => category.u

def CategoryWithPolarity.v : CategoryWithPolarity → Level
  | ⟨category, _⟩ => category.v

def CategoryWithPolarity.type : CategoryWithPolarity → Expr
  | ⟨category, false⟩ => category.type
  | ⟨category, true⟩ => category.typeop

def CategoryWithPolarity.cat : CategoryWithPolarity → Expr
  | ⟨category, false⟩ => category.cat
  | ⟨category, true⟩ => category.catop

def CategoryWithPolarity.opposite : CategoryWithPolarity → CategoryWithPolarity
  | ⟨category, opposite⟩ => ⟨category, !opposite⟩

def withLocalCategory {α : Type} (n v u : Name) (k : CategoryData → MetaM α) : MetaM α := do
  let u : Level := .param u
  withLocalDecl n .implicit (.sort (.succ u)) fun C => do
    let v : Level := .param v
    let instName ← mkFreshUserName `inst
    withLocalDecl instName .instImplicit (mkApp (.const ``Category [v, u]) C) fun instCategoryC =>
      let Cop := mkApp (.const ``Opposite [.succ u]) C
      let instCategoryCop := mkAppN (.const ``Category.opposite [v, u]) #[C, instCategoryC]
      k ⟨u, v, C, Cop, instCategoryC, instCategoryCop⟩

def oppositeFunctor : CategoryWithPolarity → CategoryWithPolarity → Expr → Expr
  | ⟨C, false⟩, ⟨D, false⟩, F =>
      mkAppN (.const ``Functor.op [C.v, D.v, C.u, D.u]) #[C.type, C.cat, D.type, D.cat, F]
  | ⟨C, false⟩, ⟨D, true⟩, F =>
      mkAppN (.const ``Functor.leftOp [C.v, D.v, C.u, D.u]) #[C.type, C.cat, D.type, D.cat, F]
  | ⟨C, true⟩, ⟨D, false⟩, F =>
      mkAppN (.const ``Functor.rightOp [C.v, D.v, C.u, D.u]) #[C.type, C.cat, D.type, D.cat, F]
  | ⟨C, true⟩, ⟨D, true⟩, F =>
      mkAppN (.const ``Functor.unop [C.v, D.v, C.u, D.u]) #[C.type, C.cat, D.type, D.cat, F]

def oppositeFunctorName : CategoryWithPolarity → CategoryWithPolarity → String
  | ⟨_, false⟩, ⟨_, false⟩ => "Op"
  | ⟨_, false⟩, ⟨_, true⟩ => "LeftOp"
  | ⟨_, true⟩, ⟨_, false⟩ => "RightOp"
  | ⟨_, true⟩, ⟨_, true⟩ => "Unop"

structure FunctorData where
  source : CategoryWithPolarity
  target : CategoryWithPolarity
  functor : Expr
  functorOp : Expr

def FunctorData.opposite : FunctorData → FunctorData
  | ⟨source, target, functor, functorOp⟩ => ⟨source.opposite, target.opposite, functorOp, functor⟩

def functorType (C D : CategoryWithPolarity) : Expr :=
 mkAppN (.const ``CategoryTheory.Functor [C.v, D.v, C.u, D.u]) #[C.type, C.cat, D.type, D.cat]

def withLocalFunctor {α : Type} (n : Name) (C D : CategoryWithPolarity)
    (k : FunctorData → MetaM α) : MetaM α := do
  withLocalDecl n .default (functorType C D) fun F => k ⟨C, D, F, oppositeFunctor C D F⟩

def mkPreservesLimit (K F : FunctorData) (colimit : Bool) : Expr :=
  let name := if colimit then ``Limits.PreservesColimit else ``Limits.PreservesLimit
  let base : Expr := .const name [K.source.v, K.source.u, K.target.v, F.target.v, K.target.u, F.target.u]
  mkAppN base #[F.source.type, F.source.cat, F.target.type, F.target.cat,
    K.source.type, K.source.cat, K.functor, F.functor]

def addPreservesLimit (J : CategoryData) (C D : CategoryWithPolarity) (colimit backward : Bool) : MetaM Unit := do
  withLocalFunctor `K ⟨J, false⟩ C.opposite fun K => do
    let C' := if backward then C.opposite else C
    withLocalFunctor `F C' D fun F => do
      let F' := if backward then F.opposite else F
      let argumentType := mkPreservesLimit K.opposite F' !colimit
      let instName ← mkFreshUserName `inst
      withLocalDecl instName .instImplicit argumentType fun inst => do
        let targetType := mkPreservesLimit K F'.opposite colimit
        let statement ← mkForallFVars
          #[C.category.type, C.category.cat, D.category.type, D.category.cat,
            J.type, J.cat, K.functor, F.functor, inst] targetType
        let proof ← mkSorry statement false
        let innerName := "preserves" ++ (if colimit then "Colimit" else "Limit")
          ++ (if backward then "Of" else "") ++ oppositeFunctorName C' D
        let name : Name := .str (.str (.str .anonymous "CategoryTheory") "Limits") innerName
        addDecl <| .defnDecl {
          name := name
          levelParams := [`w', `w, `v₁, `v₂, `u₁, `u₂]
          type := statement
          value := proof
          hints := .opaque
          safety := .safe }

def addOppositePreservationStatements : MetaM Unit := do
  withLocalCategory `C `v₁ `u₁ fun C => do
    withLocalCategory `D `v₂ `u₂ fun D => do
      withLocalCategory `J `w' `w fun J => do
        for cop in [false, true] do
          for dop in [false, true] do
            for colimit in [false, true] do
              for backward in [false, true] do
                addPreservesLimit J ⟨C, cop⟩ ⟨D, dop⟩ colimit backward

elab "add_opposite_preservation_statements" : command =>
  liftCoreM <| MetaM.run' addOppositePreservationStatements

#check Functor.op
#check Functor.unop

add_opposite_preservation_statements

#check CategoryTheory.Limits.preservesLimitOp
#check CategoryTheory.Limits.preservesLimitOfOp
#check CategoryTheory.Limits.preservesColimitLeftOp
#check CategoryTheory.Limits.preservesLimitOfUnop
