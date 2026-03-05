/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

open Bundle Filter Module Topology Set

open scoped Bundle Manifold ContDiff

@[expose] public section

section delaborators

open Lean PrettyPrinter Delaborator SubExpr

open scoped Bundle Manifold ContDiff

@[app_delab TotalSpace.mk] meta def delabTotalSpace_mk : Delab := do
  whenPPOption getPPNotation do
  let #[_B, _F, _E, _b, _v] := (← getExpr).getAppArgs | failure
  let bd : Term ← withNaryArg 3 <| delab
  let vd : Term ← withNaryArg 4 <| delab
  `(⟨$bd, $vd⟩)

@[app_delab Bundle.TotalSpace.mk'] meta def delabTotalSpace_mk' : Delab := do
  whenPPOption getPPNotation do
  let #[_B, _F, _E, _b, _v] := (← getExpr).getAppArgs | failure
  let bd : Term ← withNaryArg 3 <| delab
  let vd : Term ← withNaryArg 4 <| delab
  `(⟨$bd, $vd⟩)

@[app_delab mfderiv] meta def delab_mfderiv : Delab := do
  whenPPOption getPPNotation do
  withOverApp 21 do
  try
    let f := (← getExpr).appArg!
    let .lam n _ b _ := f | failure
    guard <| b.isAppOf ``Bundle.TotalSpace.mk'
    let s := b.getAppArgs[4]!.getAppFn
    guard <| s.isFVar
    let ss ← withAppArg do
      let ss ← withBindingBody n <| withNaryArg 4 <| withNaryFn delab
      annotateGoToSyntaxDef (← `(T% $ss))
    let stx ← `(mfderiv% ($ss))
    annotateGoToSyntaxDef stx
  catch _ =>
    let f ← withAppArg delab
    annotateGoToSyntaxDef (← `(mfderiv% $f))

@[app_delab MDifferentiableAt] meta def delabMDifferentiableAt : Delab := do
  whenPPOption getPPNotation do
  withOverApp 21 do
  try
    let f := (← getExpr).appArg!
    let .lam n _ b _ := f | failure
    guard <| b.isAppOf ``Bundle.TotalSpace.mk'
    let s := b.getAppArgs[4]!.getAppFn
    guard <| s.isFVar
    let ss ← withAppArg do
      let ss ← withBindingBody n <| withNaryArg 4 <| withNaryFn delab
      annotateGoToSyntaxDef (← `(T% $ss))
    let stx ← `(MDiffAt $ss)
    annotateGoToSyntaxDef stx
  catch _ =>
    let f ← withAppArg delab
    annotateGoToSyntaxDef (← `(MDiffAt $f))

-- @[app_delab MDifferentiableWithinAt] meta def delabMDifferentiableWithinAt : Delab := do
--   whenPPOption getPPNotation do
--   withOverApp 22 do
--   try
--     let f := (← getExpr).getAppArgs[20]!
--     let .lam n _ b _ := f | failure
--     guard <| b.isAppOf ``Bundle.TotalSpace.mk'
--     let s := b.getAppArgs[4]!.getAppFn
--     guard <| s.isFVar
--     let fs ← withNaryArg 20 <| delab
--     let ss ← withAppArg do
--       let ss ← withBindingBody n <| withNaryArg 4 <| withNaryFn delab
--       annotateGoToSyntaxDef (← `(T% $ss))
--     let stx ← `(MDiffAt $ss)
--     annotateGoToSyntaxDef stx
--   catch _ =>
--     let ss ← withAppArg delab
--     let fs ← withNaryArg 20 <| delab
--     annotateGoToSyntaxDef (← `(MDiffAt[$ss] $fs))

section

open Bundle
open scoped Bundle Manifold ContDiff

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]
  (f : M → M) (x : M) (s : Set M)
  (v : (x : M) → TangentSpace I x)

-- #check MDiffAt f x
-- #check MDiffAt[s] f x
-- #check mfderiv% f x
-- #check mfderiv I I.tangent (fun x ↦ Bundle.TotalSpace.mk' E x (v x)) x
-- #check mfderiv% (T% v) x
-- #check TotalSpace.mk' E x (v x)

end
end delaborators
