/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang
-/
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Finiteness.Defs

/-!
# Definition of Azumaya Algebras
An Azumaya algebra over a commutative ring `R` is a finitely generated, projective 
and faithful R-algebra
where the tensorproduct `A ⊗[R] Aᵐᵒᵖ` is isomorphic to the endomorphism ring of A `End R A`
via the map `f : a ⊗ b ↦ (x ↦ a * x * b.unop)`.
TODO : Add the rest three definitions and prove they are equivalent.

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
noncomputable abbrev endo : (A ⊗[R] Aᵐᵒᵖ) →ₐ[R] Module.End R A :=
Algebra.TensorProduct.lift
  (Algebra.lsmul R R A) (Algebra.lsmul R R A)
  (fun _ _ ↦ by ext; simp [commute_iff_eq, mul_assoc])

@[simp] lemma endo_apply (a : A) (b : Aᵐᵒᵖ) (x : A) : endo R A (a ⊗ₜ b) x = a * x * b.unop := by
  simp [mul_assoc]

class IsAzumaya extends Module.Projective R A, FaithfulSMul R A : Prop where
    fg : Module.Finite R A
    bij : Function.Bijective <| endo R A
