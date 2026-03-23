/-
Copyright (c) 2024 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib

/-!

# Pushforward of QC is QC

-/

@[expose] public noncomputable section

universe u

open TopCat AlgebraicGeometry TopologicalSpace CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (U : X.Opens) (M : X.Modules) (f : Γ(X, ⊤))

set_option backward.isDefEq.respectTransparency false in
abbrev modulePresheaf : X.Opensᵒᵖ ⥤ ModuleCat Γ(X, ⊤) := (PresheafOfModules.forgetToPresheafModuleCat (op ⊤)
  (Limits.initialOpOfTerminal Limits.isTerminalTop)).obj M.val

def IsLocalizing : Prop :=
  IsLocalizedModule.Away f (M.modulePresheaf.map (X.basicOpen f).leTop.op).hom



end AlgebraicGeometry.Scheme.Modules
