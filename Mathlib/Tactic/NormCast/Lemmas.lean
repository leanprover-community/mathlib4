/-
Copyright (c) 2022 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/

import Mathlib.Tactic.NormCast.CoeExt
import Mathlib.Tactic.NormCast.Ext

/-- `addElim foo` registers `foo` as an elim-lemma in `norm_cast`. -/
local elab "addElim" id:ident : command =>
  open Tactic.NormCast Lean Meta in
  Elab.Command.liftCoreM do MetaM.run' do
    addElim (← resolveGlobalConstNoOverload id)

addElim ne_eq

attribute [coe] Fin.val Array.ofSubarray
