import Mathlib.Order.CompleteBooleanAlgebra

variable {X : Type*} [Order.Frame X]

structure Nucleus (X : Type*) [Order.Frame X] where
  toFun : X → X
  idempotent (x : X) : toFun (toFun x) = toFun x
  increasing (x : X) : x ≤ toFun x
  preserves_inf (x y : X) : toFun (x ⊓ y) = toFun x ⊓ toFun y

lemma nucleus_preserves_top (n : Nucleus X) : n.toFun ⊤ = ⊤ :=
   top_le_iff.mp (n.increasing ⊤)

lemma nucleus_monotone (n : Nucleus X) : Monotone n.toFun := by
  rw [Monotone]
  intro a b h
  have h1 : a ⊓ b = a := inf_eq_left.mpr h
  have h2 := n.preserves_inf a b
  rw [h1] at h2
  exact left_eq_inf.mp h2
