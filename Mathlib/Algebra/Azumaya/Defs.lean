/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang
-/
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Finiteness.Defs

/-!
# Azumaya Algebras

An Azumaya algebra over a commutative ring `R` is a finitely generated, projective
and faithful R-algebra where the tensor product `A ⊗[R] Aᵐᵒᵖ` is isomorphic to the
endomorphism ring of A `End R A` via the map `f : a ⊗ b ↦ (x ↦ a * x * b.unop)`.
TODO : Add the rest three definitions and prove they are equivalent:
· There exist an `R`-algebra `B` such that `B ⊗[R] A` is Morita equivalent to `R`,
· `Aᵐᵒᵖ ⊗[R] A` is Morita equivalent to `R`,
· The center of `A` is `R` and `A` is a separable algebra.

## Reference

* <https://en.wikipedia.org/wiki/Azumaya_algebra>
* [Benson Farb , R. Keith Dennis, *Noncommutative Algebra*]

## Tags

Azumaya algebra, central simple algebra, noncommutative algebra
-/

variable (R A : Type*) [CommRing R] [Ring A] [Algebra R A]

open TensorProduct MulOpposite

/-- The canonical map from `A ⊗[R] Aᵐᵒᵖ` to `Module.End R A` where
  `a ⊗ b` maps to `f : x ↦ a * x * b`-/
noncomputable abbrev TensorProduct.Algebra.moduleAux' : (A ⊗[R] Aᵐᵒᵖ) →ₐ[R] Module.End R A :=
  {
    __ := TensorProduct.Algebra.moduleAux
    map_one' := by simp [Algebra.TensorProduct.one_def, Algebra.moduleAux]
    map_mul' := fun x y ↦ by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul x1 x2 =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul y1 y2 =>
          ext; simp [mul_assoc, Algebra.moduleAux_apply]
        | add y1 y2 hy1 hy2 => simp_all [mul_add]
      | add x1 x2 hx1 hx2 => simp_all [add_mul]
    map_zero' := rfl
    commutes' := fun r ↦ by
      ext a
      simp [Algebra.moduleAux_apply, Algebra.algebraMap_eq_smul_one,
        Algebra.TensorProduct.one_def]
  }

/-- An azumaya algebra is a finitely generated, projective and faithful R-algebra where
  `TensorProduct.Algebra.moduleAux` is an isomorphism. -/
class IsAzumaya extends Module.Projective R A, FaithfulSMul R A : Prop where
    fg : Module.Finite R A
    bij : Function.Bijective <| TensorProduct.Algebra.moduleAux' R A
