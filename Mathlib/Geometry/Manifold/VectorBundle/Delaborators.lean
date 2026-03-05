/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

/-!
# Delaborators for the custom elaborators

-/

open Bundle Filter Module Topology Set

open scoped Bundle Manifold ContDiff

@[expose] public section

section delaborators

open Lean PrettyPrinter Delaborator SubExpr

open scoped Bundle Manifold ContDiff

@[app_delab TotalSpace.mk] meta def delabTotalSpace_mk : Delab := do
  whenPPOption getPPNotation do
  withOverApp 5 do
  let bd ← withNaryArg 3 <| delab
  let vd ← withNaryArg 4 <| delab
  `(⟨$bd, $vd⟩)

@[app_delab Bundle.TotalSpace.mk'] meta def delabTotalSpace_mk' : Delab := do
  whenPPOption getPPNotation do
  withOverApp 5 do
  let bd ← withNaryArg 3 <| delab
  let vd ← withNaryArg 4 <| delab
  `(⟨$bd, $vd⟩)

@[app_delab mfderiv] meta def delab_mfderiv : Delab := do
  whenPPOption getPPNotation do
  withOverApp 21 do
  try
    let fe := (← getExpr).appArg!
    let .lam n _ b _ := fe | failure
    guard <| b.isAppOf ``Bundle.TotalSpace.mk'
    let σe := b.getAppArgs[4]!.getAppFn
    guard <| σe.isFVar
    let Tσs ← withAppArg do
      let σs ← withBindingBody n <| withNaryArg 4 <| withNaryFn delab
      `(T% $σs) >>= annotateGoToSyntaxDef
    `(mfderiv% ($Tσs)) >>= annotateGoToSyntaxDef
  catch _ =>
    let fs ← withAppArg delab
    `(mfderiv% $fs) >>= annotateGoToSyntaxDef

@[app_delab MDifferentiableAt] meta def delabMDifferentiableAt : Delab := do
  whenPPOption getPPNotation do
  withOverApp 21 do
  try
    let fe := (← getExpr).appArg!
    let .lam n _ b _ := fe | failure
    guard <| b.isAppOf ``Bundle.TotalSpace.mk'
    let σe := b.getAppArgs[4]!.getAppFn
    guard <| σe.isFVar
    let Tσs ← withAppArg do
      let σs ← withBindingBody n <| withNaryArg 4 <| withNaryFn delab
      `((T% $σs)) >>= annotateGoToSyntaxDef
    `(MDiffAt $Tσs) >>= annotateGoToSyntaxDef
  catch _ =>
    let fs ← withAppArg delab
    `(MDiffAt $fs) >>= annotateGoToSyntaxDef

@[app_delab MDifferentiableWithinAt] meta def delabMDifferentiableWithinAt : Delab := do
  whenPPOption getPPNotation do
  withOverApp 22 do
  let ss ← withAppArg delab
  try
    let f := (← getExpr).getAppArgs[20]!
    let .lam n _ b _ := f | failure
    guard <| b.isAppOf ``Bundle.TotalSpace.mk'
    let s := b.getAppArgs[4]!.getAppFn
    guard <| s.isFVar
    let fs ← withNaryArg 20 do
      let fs ← withBindingBody n <| withNaryArg 4 <| withNaryFn delab
      `((T% $fs)) >>= annotateGoToSyntaxDef
    `(MDiffAt[$ss] $fs) >>= annotateGoToSyntaxDef
  catch _ =>
    let fs ← withNaryArg 20 <| delab
    `(MDiffAt[$ss] $fs) >>= annotateGoToSyntaxDef

section

open Bundle
open scoped Bundle Manifold ContDiff

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]
  (f : M → M) (x : M) (s : Set M)
  (v : (x : M) → TangentSpace I x)

/-- info: MDiffAt f x : Prop -/
#guard_msgs in
#check MDiffAt f x

/-- info: MDiffAt[s] f x : Prop -/
#guard_msgs in
#check MDiffAt[s] f x

/-- info: MDiffAt (T% v) x : Prop -/
#guard_msgs in
#check MDiffAt (T% v) x

/-- info: MDiffAt[s] (T% v) x : Prop -/
#guard_msgs in
#check MDiffAt[s] (T% v) x

/-- info: mfderiv% f x : TangentSpace I x →L[ℝ] TangentSpace I (f x) -/
#guard_msgs in
#check mfderiv% f x

/-- info: mfderiv% (T% v) x : TangentSpace I x →L[ℝ] TangentSpace (I.prod 𝓘(ℝ, E)) ⟨x, v x⟩ -/
#guard_msgs in
#check mfderiv% (T% v) x

/-- info: ⟨x, v x⟩ : TotalSpace E (TangentSpace I) -/
#guard_msgs in
#check TotalSpace.mk' E x (v x)

/-- info: ⟨x, v x⟩ : TotalSpace E (TangentSpace I) -/
#guard_msgs in
#check TotalSpace.mk (F := E) x (v x)
end
end delaborators
