/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Data.Prod.Lex
import Mathlib.Order.Hom.Basic

/-!
# Order homomorphism for `Prod.Lex`
-/

/-- `toLex` as an `OrderHom`. -/
@[simps]
def Prod.Lex.toLexOrderHom {α β : Type*} [PartialOrder α] [Preorder β] :
    α × β →o α ×ₗ β where
  toFun := toLex
  monotone' := Prod.Lex.toLex_mono
