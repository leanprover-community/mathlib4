import Mathlib.Order.CompleteBooleanAlgebra

variable {X : Type*} [Order.Frame X]

structure Nucleus (X : Type*) [Order.Frame X] where
  toFun : X → X
  idempotent (x : X) : toFun (toFun x) = toFun x
  increasing (x : X) : x ≤ toFun x
  preserves_inf (x y : X) : toFun (x ⊓ y) = toFun x ⊓ toFun y

lemma nucleus_preserves_top (n : Nucleus X) : n.toFun ⊤ = ⊤ :=
   top_le_iff.mp (n.increasing ⊤)
