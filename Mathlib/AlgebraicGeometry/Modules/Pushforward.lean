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

variable {X : Scheme.{u}} (U : X.Opens) (M : X.Modules)

instance test : Algebra Γ(X, ⊤) Γ(X, U) := (X.presheaf.map U.leTop.op).hom.toAlgebra

example : Module Γ(X, U) Γ(M, U) := inferInstance

set_option backward.isDefEq.respectTransparency false in
abbrev modulePresheaf := (PresheafOfModules.forgetToPresheafModuleCat (op ⊤)
  (Limits.initialOpOfTerminal Limits.isTerminalTop)).obj M.val

variable (f : Γ(X, ⊤))

#check (M.modulePresheaf.map U.leTop.op).hom
#check (M.modulePresheaf.obj (op ⊤)).isModule
#check @IsLocalizedModule.Away Γ(X, ⊤) _ _ _ f _ (M.modulePresheaf.obj (op ⊤)).isModule _ (M.modulePresheaf.obj (op U)).isModule (M.modulePresheaf.map U.leTop.op).hom

end AlgebraicGeometry.Scheme.Modules
