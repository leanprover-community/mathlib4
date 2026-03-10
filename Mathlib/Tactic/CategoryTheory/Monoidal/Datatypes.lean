/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public meta import Mathlib.Tactic.CategoryTheory.Coherence.Datatypes
public import Mathlib.Tactic.CategoryTheory.Coherence.Datatypes
public import Mathlib.Tactic.CategoryTheory.MonoidalComp

/-!
# Expressions for monoidal categories

This file converts lean expressions representing morphisms in monoidal categories into `Mor₂Iso`
or `Mor` terms. The converted expressions are used in the coherence tactics and the string diagram
widgets.

-/

public meta section

open Lean Meta Elab Qq
open CategoryTheory Mathlib.Tactic.BicategoryLike MonoidalCategory

namespace Mathlib.Tactic.Monoidal

/-- The domain of a morphism. -/
def srcExpr (η : Expr) : MetaM Expr := do
  match (← whnfR (← inferType η)).getAppFnArgs with
  | (``Quiver.Hom, #[_, _, f, _]) => return f
  | _ => throwError m!"{η} is not a morphism"

/-- The codomain of a morphism. -/
def tgtExpr (η : Expr) : MetaM Expr := do
  match (← whnfR (← inferType η)).getAppFnArgs with
  | (``Quiver.Hom, #[_, _, _, g]) => return g
  | _ => throwError m!"{η} is not a morphism"

/-- The domain of an isomorphism. -/
def srcExprOfIso (η : Expr) : MetaM Expr := do
  match (← whnfR (← inferType η)).getAppFnArgs with
  | (``Iso, #[_, _, f, _]) => return f
  | _ => throwError m!"{η} is not a morphism"

/-- The codomain of an isomorphism. -/
def tgtExprOfIso (η : Expr) : MetaM Expr := do
  match (← whnfR (← inferType η)).getAppFnArgs with
  | (``Iso, #[_, _, _, g]) => return g
  | _ => throwError m!"{η} is not a morphism"

initialize registerTraceClass `monoidal

/-- The context for evaluating expressions. -/
structure Context where
  /-- The level for morphisms. -/
  level₂ : Level
  /-- The level for objects. -/
  level₁ : Level
  /-- The expression for the underlying category. -/
  C : Q(Type level₁)
  /-- The category instance. -/
  instCat : Q(Category.{level₂, level₁} $C)
  /-- The monoidal category instance. -/
  instMonoidal? : Option Q(MonoidalCategory.{level₂, level₁} $C)

/-- Populate a `context` object for evaluating `e`. -/
def mkContext? (e : Expr) : MetaM (Option Context) := do
  let e ← instantiateMVars e
  let type ← instantiateMVars <| ← inferType e
  match (← whnfR type).getAppFnArgs with
  | (``Quiver.Hom, #[_, _, f, _]) =>
    let C ← instantiateMVars <| ← inferType f
    let .succ level₁ ← getLevel C | return none
    let .succ level₂ ← getLevel type | return none
    let some instCat ← synthInstance?
      (mkAppN (.const ``Category [level₂, level₁]) #[C]) | return none
    let instMonoidal? ← synthInstance?
      (mkAppN (.const ``MonoidalCategory [level₂, level₁]) #[C, instCat])
    return some ⟨level₂, level₁, C, instCat, instMonoidal?⟩
  | _ => return none

instance : BicategoryLike.Context Monoidal.Context where
  mkContext? := Monoidal.mkContext?

/-- The monad for the normalization of 2-morphisms. -/
abbrev MonoidalM := CoherenceM Context

/-- Throw an error if the monoidal category instance is not found. -/
def synthMonoidalError {α : Type} : MetaM α := do
  throwError "failed to find monoidal category instance"

instance : MonadMor₁ MonoidalM where
  id₁M a := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    return .id (q(𝟙_ _) : Q($ctx.C)) a
  comp₁M f g := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let f_e : Q($ctx.C) := f.e
    let g_e : Q($ctx.C) := g.e
    return .comp (q($f_e ⊗ $g_e)) f g

section

universe v u
variable {C : Type u} [Category.{v} C]

theorem structuralIsoOfExpr_comp {f g h : C}
    (η : f ⟶ g) (η' : f ≅ g) (ih_η : η'.hom = η)
    (θ : g ⟶ h) (θ' : g ≅ h) (ih_θ : θ'.hom = θ) :
    (η' ≪≫ θ').hom  = η ≫ θ := by
  simp [ih_η, ih_θ]

theorem StructuralOfExpr_monoidalComp {f g h i : C} [MonoidalCoherence g h]
    (η : f ⟶ g) (η' : f ≅ g) (ih_η : η'.hom = η) (θ : h ⟶ i) (θ' : h ≅ i) (ih_θ : θ'.hom = θ) :
    (η' ≪⊗≫ θ').hom = η ⊗≫ θ := by
  simp [ih_η, ih_θ, monoidalIsoComp, monoidalComp]

variable [MonoidalCategory C]

theorem structuralIsoOfExpr_whiskerLeft (f : C) {g h : C}
    (η : g ⟶ h) (η' : g ≅ h) (ih_η : η'.hom = η) :
    (whiskerLeftIso f η').hom = f ◁ η := by
  simp [ih_η]

theorem structuralIsoOfExpr_whiskerRight {f g : C} (h : C)
    (η : f ⟶ g) (η' : f ≅ g) (ih_η : η'.hom = η) :
    (whiskerRightIso η' h).hom = η ▷ h := by
  simp [ih_η]

theorem structuralIsoOfExpr_horizontalComp {f₁ g₁ f₂ g₂ : C}
    (η : f₁ ⟶ g₁) (η' : f₁ ≅ g₁) (ih_η : η'.hom = η)
    (θ : f₂ ⟶ g₂) (θ' : f₂ ≅ g₂) (ih_θ : θ'.hom = θ) :
    (η' ⊗ᵢ θ').hom = η ⊗ₘ θ := by
  simp [ih_η, ih_θ]

end

open MonadMor₁

instance : MonadMor₂Iso MonoidalM where
  associatorM f g h := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let f_e : Q($ctx.C) := f.e
    let g_e : Q($ctx.C) := g.e
    let h_e : Q($ctx.C) := h.e
    return .associator q(α_ $f_e $g_e $h_e) f g h
  leftUnitorM f := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let f_e : Q($ctx.C) := f.e
    return .leftUnitor q(λ_ $f_e) f
  rightUnitorM f := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let f_e : Q($ctx.C) := f.e
    return .rightUnitor q(ρ_ $f_e) f
  id₂M f := do
    let ctx ← read
    let _cat := ctx.instCat
    have f_e : Q($ctx.C) := f.e
    return .id q(Iso.refl $f_e) f
  coherenceHomM f g inst := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have f_e : Q($ctx.C) := f.e
    have g_e : Q($ctx.C) := g.e
    have inst : Q(MonoidalCoherence $f_e $g_e) := inst
    match (← whnfI inst).getAppFnArgs with
    | (``MonoidalCoherence.mk, #[_, _, _, _, α]) =>
      let e : Q($f_e ≅ $g_e) := q(MonoidalCoherence.iso)
      return ⟨e, f, g, inst, α⟩
    | _ => throwError m!"failed to unfold {inst}"
  comp₂M η θ := do
    let ctx ← read
    let _cat := ctx.instCat
    let f ← η.srcM
    let g ← η.tgtM
    let h ← θ.tgtM
    have f_e : Q($ctx.C) := f.e
    have g_e : Q($ctx.C) := g.e
    have h_e : Q($ctx.C) := h.e
    have η_e : Q($f_e ≅ $g_e) := η.e
    have θ_e : Q($g_e ≅ $h_e) := θ.e
    return .comp q($η_e ≪≫ $θ_e) f g h η θ
  whiskerLeftM f η := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let g ← η.srcM
    let h ← η.tgtM
    have f_e : Q($ctx.C) := f.e
    have g_e : Q($ctx.C) := g.e
    have h_e : Q($ctx.C) := h.e
    have η_e : Q($g_e ≅ $h_e) := η.e
    return .whiskerLeft q(whiskerLeftIso $f_e $η_e) f g h η
  whiskerRightM η h := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let f ← η.srcM
    let g ← η.tgtM
    have f_e : Q($ctx.C) := f.e
    have g_e : Q($ctx.C) := g.e
    have h_e : Q($ctx.C) := h.e
    have η_e : Q($f_e ≅ $g_e) := η.e
    return .whiskerRight q(whiskerRightIso $η_e $h_e) f g η h
  horizontalCompM η θ := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let f₁ ← η.srcM
    let g₁ ← η.tgtM
    let f₂ ← θ.srcM
    let g₂ ← θ.tgtM
    have f₁_e : Q($ctx.C) := f₁.e
    have g₁_e : Q($ctx.C) := g₁.e
    have f₂_e : Q($ctx.C) := f₂.e
    have g₂_e : Q($ctx.C) := g₂.e
    have η_e : Q($f₁_e ≅ $g₁_e) := η.e
    have θ_e : Q($f₂_e ≅ $g₂_e) := θ.e
    return .horizontalComp q(tensorIso $η_e $θ_e) f₁ g₁ f₂ g₂ η θ
  symmM η := do
    let ctx ← read
    let _cat := ctx.instCat
    let f ← η.srcM
    let g ← η.tgtM
    have f_e : Q($ctx.C) := f.e
    have g_e : Q($ctx.C) := g.e
    have η_e : Q($f_e ≅ $g_e) := η.e
    return .inv q(Iso.symm $η_e) f g η
  coherenceCompM α η θ := do
    let ctx ← read
    let _cat := ctx.instCat
    let f ← η.srcM
    let g ← η.tgtM
    let h ← θ.srcM
    let i ← θ.tgtM
    have f_e : Q($ctx.C) := f.e
    have g_e : Q($ctx.C) := g.e
    have h_e : Q($ctx.C) := h.e
    have i_e : Q($ctx.C) := i.e
    have _inst : Q(MonoidalCoherence $g_e $h_e) := α.inst
    have η_e : Q($f_e ≅ $g_e) := η.e
    have θ_e : Q($h_e ≅ $i_e) := θ.e
    return .coherenceComp q($η_e ≪⊗≫ $θ_e) f g h i α η θ

open MonadMor₂Iso

instance : MonadMor₂ MonoidalM where
  homM η := do
    let ctx ← read
    let _cat := ctx.instCat
    let f ← η.srcM
    let g ← η.tgtM
    have f_e : Q($ctx.C) := f.e
    have g_e : Q($ctx.C) := g.e
    have η_e : Q($f_e ≅ $g_e) := η.e
    let e : Q($f_e ⟶ $g_e) := q(Iso.hom $η_e)
    have eq : Q(Iso.hom $η_e = $e) := q(rfl)
    return .isoHom e ⟨η, eq⟩ η
  atomHomM η := do
    let ctx ← read
    let _cat := ctx.instCat
    let f := η.src
    let g := η.tgt
    have f_e : Q($ctx.C) := f.e
    have g_e : Q($ctx.C) := g.e
    have η_e : Q($f_e ≅ $g_e) := η.e
    return .mk q(Iso.hom $η_e) f g
  invM η := do
    let ctx ← read
    let _cat := ctx.instCat
    let f ← η.srcM
    let g ← η.tgtM
    have f_e : Q($ctx.C) := f.e
    have g_e : Q($ctx.C) := g.e
    have η_e : Q($f_e ≅ $g_e) := η.e
    let e : Q($g_e ⟶ $f_e) := q(Iso.inv $η_e)
    let η_inv ← symmM η
    let eq : Q(Iso.inv $η_e = $e) := q(Iso.symm_hom $η_e)
    return .isoInv e ⟨η_inv, eq⟩ η
  atomInvM η := do
    let ctx ← read
    let _cat := ctx.instCat
    let f := η.src
    let g := η.tgt
    have f_e : Q($ctx.C) := f.e
    have g_e : Q($ctx.C) := g.e
    have η_e : Q($f_e ≅ $g_e) := η.e
    return .mk q(Iso.inv $η_e) g f
  id₂M f := do
    let ctx ← read
    let _cat := ctx.instCat
    have f_e : Q($ctx.C) := f.e
    let e : Q($f_e ⟶ $f_e) := q(𝟙 $f_e)
    let eq : Q(𝟙 $f_e = $e) := q(Iso.refl_hom $f_e)
    return .id e ⟨.structuralAtom <| ← id₂M f, eq⟩ f
  comp₂M η θ := do
    let ctx ← read
    let _cat := ctx.instCat
    let f ← η.srcM
    let g ← η.tgtM
    let h ← θ.tgtM
    have f_e : Q($ctx.C) := f.e
    have g_e : Q($ctx.C) := g.e
    have h_e : Q($ctx.C) := h.e
    have η_e : Q($f_e ⟶ $g_e) := η.e
    have θ_e : Q($g_e ⟶ $h_e) := θ.e
    let iso_lift? ← (match (η.isoLift?, θ.isoLift?) with
      | (some η_iso, some θ_iso) =>
        have η_iso_e : Q($f_e ≅ $g_e) := η_iso.e.e
        have θ_iso_e : Q($g_e ≅ $h_e) := θ_iso.e.e
        have η_iso_eq : Q(Iso.hom $η_iso_e = $η_e) := η_iso.eq
        have θ_iso_eq : Q(Iso.hom $θ_iso_e = $θ_e) := θ_iso.eq
        let eq := q(structuralIsoOfExpr_comp _ _ $η_iso_eq _ _ $θ_iso_eq)
        return some ⟨← comp₂M η_iso.e θ_iso.e, eq⟩
      | _ => return none)
    let e : Q($f_e ⟶ $h_e) := q($η_e ≫ $θ_e)
    return .comp e iso_lift? f g h η θ
  whiskerLeftM f η := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let g ← η.srcM
    let h ← η.tgtM
    have f_e : Q($ctx.C) := f.e
    have g_e : Q($ctx.C) := g.e
    have h_e : Q($ctx.C) := h.e
    have η_e : Q($g_e ⟶ $h_e) := η.e
    let iso_lift? ← (match η.isoLift? with
      | some η_iso => do
        have η_iso_e : Q($g_e ≅ $h_e) := η_iso.e.e
        have η_iso_eq : Q(Iso.hom $η_iso_e = $η_e) := η_iso.eq
        let eq := q(structuralIsoOfExpr_whiskerLeft $f_e _ _ $η_iso_eq)
        return some ⟨← whiskerLeftM f η_iso.e, eq⟩
      | _ => return none)
    let e : Q($f_e ⊗ $g_e ⟶ $f_e ⊗ $h_e) := q($f_e ◁ $η_e)
    return .whiskerLeft e iso_lift? f g h η
  whiskerRightM η h := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let f ← η.srcM
    let g ← η.tgtM
    have f_e : Q($ctx.C) := f.e
    have g_e : Q($ctx.C) := g.e
    have h_e : Q($ctx.C) := h.e
    have η_e : Q($f_e ⟶ $g_e) := η.e
    let iso_lift? ← (match η.isoLift? with
      | some η_iso => do
        have η_iso_e : Q($f_e ≅ $g_e) := η_iso.e.e
        have η_iso_eq : Q(Iso.hom $η_iso_e = $η_e) := η_iso.eq
        let eq := q(structuralIsoOfExpr_whiskerRight $h_e _ _ $η_iso_eq)
        return some ⟨← whiskerRightM η_iso.e h, eq⟩
      | _ => return none)
    let e : Q($f_e ⊗ $h_e ⟶ $g_e ⊗ $h_e) := q($η_e ▷ $h_e)
    return .whiskerRight e iso_lift? f g η h
  horizontalCompM η θ := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let f₁ ← η.srcM
    let g₁ ← η.tgtM
    let f₂ ← θ.srcM
    let g₂ ← θ.tgtM
    have f₁_e : Q($ctx.C) := f₁.e
    have g₁_e : Q($ctx.C) := g₁.e
    have f₂_e : Q($ctx.C) := f₂.e
    have g₂_e : Q($ctx.C) := g₂.e
    have η_e : Q($f₁_e ⟶ $g₁_e) := η.e
    have θ_e : Q($f₂_e ⟶ $g₂_e) := θ.e
    let iso_lift? ← (match (η.isoLift?, θ.isoLift?) with
      | (some η_iso, some θ_iso) => do
        have η_iso_e : Q($f₁_e ≅ $g₁_e) := η_iso.e.e
        have θ_iso_e : Q($f₂_e ≅ $g₂_e) := θ_iso.e.e
        have η_iso_eq : Q(Iso.hom $η_iso_e = $η_e) := η_iso.eq
        have θ_iso_eq : Q(Iso.hom $θ_iso_e = $θ_e) := θ_iso.eq
        let eq := q(structuralIsoOfExpr_horizontalComp _ _ $η_iso_eq _ _ $θ_iso_eq)
        return some ⟨← horizontalCompM η_iso.e θ_iso.e, eq⟩
      | _ => return none)
    let e : Q($f₁_e ⊗ $f₂_e ⟶ $g₁_e ⊗ $g₂_e) := q($η_e ⊗ₘ $θ_e)
    return .horizontalComp e iso_lift? f₁ g₁ f₂ g₂ η θ
  coherenceCompM α η θ := do
    let ctx ← read
    let _cat := ctx.instCat
    let f ← η.srcM
    let g ← η.tgtM
    let h ← θ.srcM
    let i ← θ.tgtM
    have f_e : Q($ctx.C) := f.e
    have g_e : Q($ctx.C) := g.e
    have h_e : Q($ctx.C) := h.e
    have i_e : Q($ctx.C) := i.e
    have _inst : Q(MonoidalCoherence $g_e $h_e) := α.inst
    have η_e : Q($f_e ⟶ $g_e) := η.e
    have θ_e : Q($h_e ⟶ $i_e) := θ.e
    let iso_lift? ← (match (η.isoLift?, θ.isoLift?) with
      | (some η_iso, some θ_iso) => do
        have η_iso_e : Q($f_e ≅ $g_e) := η_iso.e.e
        have θ_iso_e : Q($h_e ≅ $i_e) := θ_iso.e.e
        have η_iso_eq : Q(Iso.hom $η_iso_e = $η_e) := η_iso.eq
        have θ_iso_eq : Q(Iso.hom $θ_iso_e = $θ_e) := θ_iso.eq
        let eq := q(StructuralOfExpr_monoidalComp _ _ $η_iso_eq _ _ $θ_iso_eq)
        return some ⟨← coherenceCompM α η_iso.e θ_iso.e, eq⟩
      | _ => return none)
    let e : Q($f_e ⟶ $i_e) := q($η_e ⊗≫ $θ_e)
    return .coherenceComp e iso_lift? f g h i α η θ

/-- Check that `e` is definitionally equal to `𝟙_ C`. -/
def id₁? (e : Expr) : MonoidalM (Option Obj) := do
  let ctx ← read
  match ctx.instMonoidal? with
  | some _monoidal => do
    if ← withDefault <| isDefEq e (q(𝟙_ _) : Q($ctx.C)) then
      return some ⟨none⟩
    else
      return none
  | _ => return none

/-- Return `(f, g)` if `e` is definitionally equal to `f ⊗ g`. -/
def comp? (e : Expr) : MonoidalM (Option (Mor₁ × Mor₁)) := do
  let ctx ← read
  let f ← mkFreshExprMVarQ ctx.C
  let g ← mkFreshExprMVarQ ctx.C
  match ctx.instMonoidal? with
    | some _monoidal => do
      if ← withDefault <| isDefEq e q($f ⊗ $g) then
        let f ← instantiateMVars f
        let g ← instantiateMVars g
        return some ((.of ⟨f, ⟨none⟩, ⟨none⟩⟩ : Mor₁), (.of ⟨g, ⟨none⟩, ⟨none⟩⟩ : Mor₁))
      else
        return none
    | _ => return none

/-- Construct a `Mor₁` expression from a Lean expression. -/
partial def mor₁OfExpr (e : Expr) : MonoidalM Mor₁ := do
  if let some f := (← get).cache.get? e then
    return f
  let f ←
    if let some a ← id₁? e then
      MonadMor₁.id₁M a
    else if let some (f, g) ← comp? e then
      MonadMor₁.comp₁M (← mor₁OfExpr f.e) (← mor₁OfExpr g.e)
    else
      return Mor₁.of ⟨e, ⟨none⟩, ⟨none⟩⟩
  modify fun s => { s with cache := s.cache.insert e f }
  return f

instance : MkMor₁ MonoidalM where
  ofExpr := mor₁OfExpr

/-- Construct a `Mor₂Iso` term from a Lean expression. -/
partial def Mor₂IsoOfExpr (e : Expr) : MonoidalM Mor₂Iso := do
  match (← whnfR e).getAppFnArgs with
  | (``MonoidalCategoryStruct.associator, #[_, _, _, f, g, h]) =>
    associatorM' (← MkMor₁.ofExpr f) (← MkMor₁.ofExpr g) (← MkMor₁.ofExpr h)
  | (``MonoidalCategoryStruct.leftUnitor, #[_, _, _, f]) =>
    leftUnitorM' (← MkMor₁.ofExpr f)
  | (``MonoidalCategoryStruct.rightUnitor, #[_, _, _, f]) =>
    rightUnitorM' (← MkMor₁.ofExpr f)
  | (``Iso.refl, #[_, _, f]) =>
    id₂M' (← MkMor₁.ofExpr f)
  | (``Iso.symm, #[_, _, _, _, η]) =>
    symmM (← Mor₂IsoOfExpr η)
  | (``Iso.trans, #[_, _, _, _, _, η, θ]) =>
    comp₂M (← Mor₂IsoOfExpr η) (← Mor₂IsoOfExpr θ)
  | (``MonoidalCategory.whiskerLeftIso, #[_, _, _, f, _, _, η]) =>
    whiskerLeftM (← MkMor₁.ofExpr f) (← Mor₂IsoOfExpr η)
  | (``MonoidalCategory.whiskerRightIso, #[_, _, _, _, _, η, h]) =>
    whiskerRightM (← Mor₂IsoOfExpr η) (← MkMor₁.ofExpr h)
  | (``tensorIso, #[_, _, _, _, _, _, _, η, θ]) =>
    horizontalCompM (← Mor₂IsoOfExpr η) (← Mor₂IsoOfExpr θ)
  | (``monoidalIsoComp, #[_, _, _, g, h, _, inst, η, θ]) =>
    let α ← coherenceHomM (← MkMor₁.ofExpr g) (← MkMor₁.ofExpr h) inst
    coherenceCompM α (← Mor₂IsoOfExpr η) (← Mor₂IsoOfExpr θ)
  | (``MonoidalCoherence.iso, #[_, _, f, g, inst]) =>
    coherenceHomM' (← MkMor₁.ofExpr f) (← MkMor₁.ofExpr g) inst
  | _ =>
    return .of ⟨e, ← MkMor₁.ofExpr (← srcExprOfIso e), ← MkMor₁.ofExpr (← tgtExprOfIso e)⟩

open MonadMor₂ in
/-- Construct a `Mor₂` term from a Lean expression. -/
partial def Mor₂OfExpr (e : Expr) : MonoidalM Mor₂ := do
  match ← whnfR e with
  -- whnfR version of `Iso.hom η`
  | .proj ``Iso 0 η => homM (← Mor₂IsoOfExpr η)
  -- whnfR version of `Iso.inv η`
  | .proj ``Iso 1 η => invM (← Mor₂IsoOfExpr η)
  | .app .. => match (← whnfR e).getAppFnArgs with
    | (``CategoryStruct.id, #[_, _, f]) => id₂M (← MkMor₁.ofExpr f)
    | (``CategoryStruct.comp, #[_, _, _, _, _, η, θ]) =>
      comp₂M (← Mor₂OfExpr η) (← Mor₂OfExpr θ)
    | (``MonoidalCategoryStruct.whiskerLeft, #[_, _, _, f, _, _, η]) =>
      whiskerLeftM (← MkMor₁.ofExpr f) (← Mor₂OfExpr η)
    | (``MonoidalCategoryStruct.whiskerRight, #[_, _, _, _, _, η, h]) =>
      whiskerRightM (← Mor₂OfExpr η) (← MkMor₁.ofExpr h)
    | (``MonoidalCategoryStruct.tensorHom, #[_, _, _, _, _, _, _, η, θ]) =>
      horizontalCompM (← Mor₂OfExpr η) (← Mor₂OfExpr θ)
    | (``monoidalComp, #[_, _, _, g, h, _, inst, η, θ]) =>
      let α ← coherenceHomM (← MkMor₁.ofExpr g) (← MkMor₁.ofExpr h) inst
      coherenceCompM α (← Mor₂OfExpr η) (← Mor₂OfExpr θ)
    | _ => return .of ⟨e, ← MkMor₁.ofExpr (← srcExpr e), ← MkMor₁.ofExpr (← tgtExpr e)⟩
  | _ =>
    return .of ⟨e, ← MkMor₁.ofExpr (← srcExpr e), ← MkMor₁.ofExpr (← tgtExpr e)⟩

instance : BicategoryLike.MkMor₂ MonoidalM where
  ofExpr := Mor₂OfExpr

instance : MonadCoherehnceHom MonoidalM where
  unfoldM α := Mor₂IsoOfExpr α.unfold

end Mathlib.Tactic.Monoidal
