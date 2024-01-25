/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Data.Finite.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.FunLike.Basic

#align_import data.fun_like.fintype from "leanprover-community/mathlib"@"f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c"

/-!
# Finiteness of `DFunLike` types

We show a type `F` with a `DFunLike F α β` is finite if both `α` and `β` are finite.
This corresponds to the following two pairs of declarations:

 * `DFunLike.fintype` is a definition stating all `DFunLike`s are finite if their domain and
   codomain are.
 * `DFunLike.finite` is a lemma stating all `DFunLike`s are finite if their domain and
   codomain are.
 * `DFunLike.fintype'` is a non-dependent version of `DFunLike.fintype` and
 * `DFunLike.finite` is a non-dependent version of `DFunLike.finite`, because dependent instances
   are harder to infer.

You can use these to produce instances for specific `DFunLike` types.
(Although there might be options for `Fintype` instances with better definitional behaviour.)
They can't be instances themselves since they can cause loops.
-/

-- porting notes: `Type` is a reserved word, switched to `Type'`
section Type'

variable (F G : Type*) {α γ : Type*} {β : α → Type*} [DFunLike F α β] [FunLike G α γ]

/-- All `DFunLike`s are finite if their domain and codomain are.

This is not an instance because specific `DFunLike` types might have a better-suited definition.

See also `DFunLike.finite`.
-/
noncomputable def DFunLike.fintype [DecidableEq α] [Fintype α] [∀ i, Fintype (β i)] : Fintype F :=
  Fintype.ofInjective _ DFunLike.coe_injective
#align fun_like.fintype DFunLike.fintype

/-- All `FunLike`s are finite if their domain and codomain are.

Non-dependent version of `DFunLike.fintype` that might be easier to infer.
This is not an instance because specific `FunLike` types might have a better-suited definition.
-/
noncomputable def FunLike.fintype [DecidableEq α] [Fintype α] [Fintype γ] : Fintype G :=
  DFunLike.fintype G
#align fun_like.fintype' FunLike.fintype

end Type'

-- porting notes: `Sort` is a reserved word, switched to `Sort'`
section Sort'

variable (F G : Sort*) {α γ : Sort*} {β : α → Sort*} [DFunLike F α β] [FunLike G α γ]

/-- All `DFunLike`s are finite if their domain and codomain are.  -/
instance DFunLike.finite [Finite α] [∀ i, Finite (β i)] : Finite F :=
  Finite.of_injective _ DFunLike.coe_injective
#align fun_like.finite DFunLike.finite

/-- All `FunLike`s are finite if their domain and codomain are.

Non-dependent version of `DFunLike.finite` that might be easier to infer.
-/
instance FunLike.finite [Finite α] [Finite γ] : Finite G :=
  DFunLike.finite G
#align fun_like.finite' FunLike.finite

end Sort'
