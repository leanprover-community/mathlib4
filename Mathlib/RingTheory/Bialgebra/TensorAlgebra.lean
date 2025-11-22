/-
Copyright (c) 2025 Nikolas Tapia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolas Tapia
-/
module

public import Mathlib.LinearAlgebra.TensorAlgebra.Basic
public import Mathlib.RingTheory.Bialgebra.Basic

/-!
# Bialgebra structure on `TensorAlgebra R M`

In this file we implement the natural bialgebra structure on `TensorAlgebra R M`.
The comultiplication is the unique algebra map satisfying `comul (ι R x) = ι R x ⊗ 1 + 1 ⊗ ι R
x` for all `x : M`, and `algebraMapInv` acts as the counit.
-/

@[expose] public section

namespace TensorAlgebra

open scoped TensorProduct RingTheory.LinearMap
open TensorProduct

variable (R : Type*) [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]

local notation "T[" M "]" => TensorAlgebra R M

/-- Comultiplication in `TensorAlgebra R M` as an algebra map.
It is induced by the linear map sending `(m : M)` to `ι R m ⊗ₜ[R] 1 + 1 ⊗ₜ[R] ι R m`.
See `comul_apply`.
-/
def comul : T[M] →ₐ[R] T[M] ⊗[R] T[M] := lift R (
  (ι R ⊗ₘ Algebra.linearMap R T[M]) ∘ₗ (TensorProduct.rid R M).symm +
  (Algebra.linearMap R T[M] ⊗ₘ ι R) ∘ₗ (TensorProduct.lid R M).symm
  )

@[simp]
lemma comul_apply (m : M) : comul R (ι R m) = ι R m ⊗ₜ[R] 1 + 1 ⊗ₜ[R] ι R m := by
  simp [comul]

@[simp]
lemma algebraMapInv_ι_apply (m : M) : algebraMapInv (ι R m) = 0 := by
  simp [algebraMapInv]

@[simp]
lemma algebraMapInv_ι_eq_zero : algebraMapInv.toLinearMap ∘ₗ (ι R) = (0 : M →ₗ[R] R) :=
  LinearMap.ext <| algebraMapInv_ι_apply _

instance instBialgebra : Bialgebra R T[M] := Bialgebra.ofAlgHom (comul R) algebraMapInv
    (by ext; simpa [comul, Algebra.TensorProduct.one_def, add_tmul, tmul_add] using by abel)
    (by ext; simp [comul, algebraMapInv])
    (by ext; simp [comul, algebraMapInv])

end TensorAlgebra
