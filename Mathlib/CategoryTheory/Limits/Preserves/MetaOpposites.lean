/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Creates

open CategoryTheory

open Lean Meta Qq Elab Command Term

/-
{C : Type u₁} →
  [inst : Category.{v₁, u₁} C] →
    {D : Type u₂} →
      [inst_1 : Category.{v₂, u₂} D] →
        {J : Type w} →
          [inst_2 : Category.{w', w} J] →
            (K : J ⥤ Cᵒᵖ) → (F : C ⥤ D) →
            [inst_3 : Limits.PreservesColimit K.leftOp F] → Limits.PreservesLimit K F.op
-/

open CategoryTheory.Limits

section

universe w w' v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : Type w} [Category.{w'} J]

def preservesLimitOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [PreservesColimit K.leftOp F] :
    PreservesLimit K F.op where
  preserves {c} hc := by
    let opCocone : Cocone K.leftOp := coconeLeftOpOfCone c
    let opCoconeIsColimit : IsColimit opCocone := isColimitCoconeLeftOpOfCone _ hc

    let mappedOpCocone : Cocone (K.leftOp ⋙ F) := F.mapCocone opCocone
    let mappedOpConeIsColimit : IsColimit mappedOpCocone := isColimitOfPreserves F opCoconeIsColimit

    let unopMappedOpCocone : Cone (K.leftOp ⋙ F).rightOp := coneRightOpOfCocone mappedOpCocone
    let isLimitUnopMappedOpCocone : IsLimit unopMappedOpCocone :=
      isLimitConeRightOpOfCocone _ mappedOpConeIsColimit

    let functorsMatchUp : (K.leftOp ⋙ F).rightOp ≅ K ⋙ F.op :=
      NatIso.ofComponents (fun X => Iso.refl _) (by aesop_cat)

    let matchedUnopMappedOpCocone : Cone (K ⋙ F.op) :=
      (Cones.postcompose functorsMatchUp.hom).obj unopMappedOpCocone
    let isLimitMatchedUnopMappedOpCocone : IsLimit matchedUnopMappedOpCocone :=
      (IsLimit.postcomposeHomEquiv functorsMatchUp _).symm isLimitUnopMappedOpCocone

    let coneMatches : matchedUnopMappedOpCocone ≅ F.op.mapCone c :=
      Cones.ext (Iso.refl _) (by aesop_cat)
    exact IsLimit.ofIsoLimit isLimitMatchedUnopMappedOpCocone coneMatches

def reflectsLimitOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [ReflectsColimit K.leftOp F] :
    ReflectsLimit K F.op where
  reflects {c} hc := by
    let opCocone : Cocone (K ⋙ F.op).leftOp := coconeLeftOpOfCone (F.op.mapCone c)
    let opCoconeIsColimit : IsColimit opCocone := isColimitCoconeLeftOpOfCone _ hc

    let functorsMatchUp : (K ⋙ F.op).leftOp ≅ K.leftOp ⋙ F :=
      NatIso.ofComponents (fun X => Iso.refl _) (by aesop_cat)

    let matchedOpCocone : Cocone (K.leftOp ⋙ F) :=
      (Cocones.precompose functorsMatchUp.hom).obj opCocone
    let isColimitMatchedOpCocone : IsColimit matchedOpCocone :=
      (IsColimit.precomposeHomEquiv functorsMatchUp _).symm opCoconeIsColimit

    let opCoconeUpstairs : Cocone K.leftOp := coconeLeftOpOfCone c

    let coconeMatches : matchedOpCocone ≅ F.mapCocone opCoconeUpstairs :=
      Cocones.ext (Iso.refl _) (by aesop_cat)

    let isColimitMapOpCoconeUpstairs : IsColimit (F.mapCocone opCoconeUpstairs) :=
      IsColimit.ofIsoColimit isColimitMatchedOpCocone coconeMatches

    let isColimitOpCoconeUpstairs : IsColimit opCoconeUpstairs :=
      isColimitOfReflects _ isColimitMapOpCoconeUpstairs

    let unopOpConeUpstairs : Cone K := coneOfCoconeLeftOp opCoconeUpstairs
    let isLimitUnopOpConeUpstairs : IsLimit unopOpConeUpstairs :=
      isLimitConeOfCoconeLeftOp _ isColimitOpCoconeUpstairs

    let coneMatches : unopOpConeUpstairs ≅ c :=
      Cones.ext (Iso.refl _)

    exact IsLimit.ofIsoLimit isLimitUnopOpConeUpstairs coneMatches

def createsLimitOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [CreatesColimit K.leftOp F] :
    CreatesLimit K F.op :=
  { reflectsLimitOp K F with
    lifts := fun c {hc} =>
      let opCocone : Cocone (K ⋙ F.op).leftOp := coconeLeftOpOfCone c;
      let opCoconeIsColimit : IsColimit opCocone := isColimitCoconeLeftOpOfCone _ hc;

      let functorsMatchUp : (K ⋙ F.op).leftOp ≅ K.leftOp ⋙ F :=
        NatIso.ofComponents (fun X => Iso.refl _) (by aesop_cat);

      let matchedOpCocone : Cocone (K.leftOp ⋙ F) :=
        (Cocones.precompose functorsMatchUp.hom).obj opCocone;
      let isColimitMatchedOpCocone : IsColimit matchedOpCocone :=
        (IsColimit.precomposeHomEquiv functorsMatchUp _).symm opCoconeIsColimit;

      let liftedCocone : Cocone K.leftOp := liftColimit isColimitMatchedOpCocone;
      { liftedCone := coneOfCoconeLeftOp liftedCocone
        validLift := by
          let i := liftedColimitMapsToOriginal isColimitMatchedOpCocone


          sorry
         } }


end


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

def getPreservesLimit : Bool → CommandElabM Term
  | false => `(PreservesLimit)
  | true => `(PreservesColimit)

section

universe w w' v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : Type w} [Category.{w'} J]


def mySyntax (n : Name) (C D J : ReflectedCategory) (K F : ReflectedFunctor) (proof : Term) :
    CommandElabM Syntax :=
  `(/-- This $proof is a docstring. -/
    def $(mkIdent n) (K : $(J) ⥤ $(C.op)) (F : $(C) ⥤ $(D)) [PreservesColimit $(K.op) $(F)] :
        PreservesLimit $(K) $(F.op) := $proof)

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
        elabCommand (← mySyntax name C D J K F (← `(sorry)))
        let docstring := "This is another docstring"
        -- let docstring := s!"If {F'.asDocstring} preserves {if colimit then "" else "co"}limits "
        --   ++ s!"of {K.opposite.asDocstring}, then {F'.opposite.asDocstring} preserves "
        --   ++ s!"{if colimit then "co" else ""}limits of {K.asDocstring}."
        addDocString name docstring

adds

#check CategoryTheory.Limits.preservesLimitLeftOp

end



open Lean in
run_cmd
  logInfo (← `(command|
    /-- doc-strings are ok -/
    def $(mkIdent `newOne) := 1
    -- but comments are not
  ))

#check newOne
  -- liftCoreM <| MetaM.run' addOppositePreservationStatements

/-- Contains information about a category that a theorem quantifies over. -/
structure CategoryData where
  /-- Universe level of objects. -/
  u : Level
  /-- Universe level of morphisms. -/
  v : Level
  name : String
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

def CategoryWithPolarity.name : CategoryWithPolarity → String
  | ⟨category, opposite⟩ => category.name ++ (if opposite then "ᵒᵖ" else "")

def withLocalCategory {α : Type} (n : String) (v u : Name) (k : CategoryData → MetaM α) : MetaM α := do
  let u : Level := .param u
  withLocalDecl n .implicit (.sort (.succ u)) fun C => do
    let v : Level := .param v
    let instName ← mkFreshUserName `inst
    withLocalDecl instName .instImplicit (mkApp (.const ``Category [v, u]) C) fun instCategoryC =>
      let Cop := mkApp (.const ``Opposite [.succ u]) C
      let instCategoryCop := mkAppN (.const ``Category.opposite [v, u]) #[C, instCategoryC]
      k ⟨u, v, n, C, Cop, instCategoryC, instCategoryCop⟩

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
  | ⟨_, false⟩, ⟨_, false⟩ => "op"
  | ⟨_, false⟩, ⟨_, true⟩ => "leftOp"
  | ⟨_, true⟩, ⟨_, false⟩ => "rightOp"
  | ⟨_, true⟩, ⟨_, true⟩ => "unop"

def oppositeFunctorDeclarationName' : CategoryWithPolarity → CategoryWithPolarity → String
  | ⟨_, false⟩, ⟨_, false⟩ => "Op"
  | ⟨_, false⟩, ⟨_, true⟩ => "LeftOp"
  | ⟨_, true⟩, ⟨_, false⟩ => "RightOp"
  | ⟨_, true⟩, ⟨_, true⟩ => "Unop"

structure FunctorData where
  name : String
  nameOp : String
  source : CategoryWithPolarity
  target : CategoryWithPolarity
  functor : Expr
  functorOp : Expr

def FunctorData.asDocstring (F : FunctorData) : String :=
  s!"`{F.name} : {F.source.name} ⥤ {F.target.name}`"

def FunctorData.opposite : FunctorData → FunctorData
  | ⟨name, nameOp, source, target, functor, functorOp⟩ =>
      ⟨nameOp, name, source.opposite, target.opposite, functorOp, functor⟩

def functorType (C D : CategoryWithPolarity) : Expr :=
 mkAppN (.const ``CategoryTheory.Functor [C.v, D.v, C.u, D.u]) #[C.type, C.cat, D.type, D.cat]

def withLocalFunctor {α : Type} (n : String) (C D : CategoryWithPolarity)
    (k : FunctorData → MetaM α) : MetaM α := do
  withLocalDecl n .default (functorType C D) fun F => k ⟨n, n ++ "." ++ oppositeFunctorName C D,
    C, D, F, oppositeFunctor C D F⟩

def mkPreservesLimit (K F : FunctorData) (colimit : Bool) : Expr :=
  let name := if colimit then ``Limits.PreservesColimit else ``Limits.PreservesLimit
  let base : Expr := .const name [K.source.v, K.source.u, K.target.v, F.target.v, K.target.u, F.target.u]
  mkAppN base #[F.source.type, F.source.cat, F.target.type, F.target.cat,
    K.source.type, K.source.cat, K.functor, F.functor]

def addPreservesLimit (J : CategoryData) (C D : CategoryWithPolarity) (colimit backward : Bool) : MetaM Unit := do
  withLocalFunctor "K" ⟨J, false⟩ C.opposite fun K => do
    let C' := if backward then C.opposite else C
    withLocalFunctor "F" C' D fun F => do
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
          ++ (if backward then "Of" else "") ++ oppositeFunctorDeclarationName' C' D
        let name : Name := .str (.str (.str .anonymous "CategoryTheory") "Limits") innerName
        addDecl <| .defnDecl {
          name := name
          levelParams := [`w', `w, `v₁, `v₂, `u₁, `u₂]
          type := statement
          value := proof
          hints := .opaque
          safety := .safe }
        let docstring := s!"If {F'.asDocstring} preserves {if colimit then "" else "co"}limits "
          ++ s!"of {K.opposite.asDocstring}, then {F'.opposite.asDocstring} preserves "
          ++ s!"{if colimit then "co" else ""}limits of {K.asDocstring}."
        addDocString name docstring

def addOppositePreservationStatements : MetaM Unit := do
  withLocalCategory "C" `v₁ `u₁ fun C => do
    withLocalCategory "D" `v₂ `u₂ fun D => do
      withLocalCategory "J" `w' `w fun J => do
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
