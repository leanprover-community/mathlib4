import Mathlib.Algebra.Algebra.Int
import Mathlib.RingTheory.TensorProduct.Basic

variable {A B : Type*}

open TensorProduct

/-- Verify that typeclass search finds the ring structure on `A ⊗[ℤ] B`
when `A` and `B` are merely rings, by treating both as `ℤ`-algebras.
-/
noncomputable example [Ring A] [Ring B] : Ring (A ⊗[ℤ] B) := by infer_instance

/-- Verify that typeclass search finds the comm_ring structure on `A ⊗[ℤ] B`
when `A` and `B` are merely comm_rings, by treating both as `ℤ`-algebras.
-/
noncomputable example [CommRing A] [CommRing B] : CommRing (A ⊗[ℤ] B) := by infer_instance


