/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang
-/
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Azumaya Algebras

An Azumaya algebra over a commutative ring `R` is a finitely generated, projective
and faithful R-algebra where the tensor product `A ⊗[R] Aᵐᵒᵖ` is isomorphic to the
`R`-endomorphisms of A via the map `f : a ⊗ b ↦ (x ↦ a * x * b.unop)`.
TODO : Add the three more definitions and prove they are equivalent:
· There exists an `R`-algebra `B` such that `B ⊗[R] A` is Morita equivalent to `R`;
· `Aᵐᵒᵖ ⊗[R] A` is Morita equivalent to `R`;
· The center of `A` is `R` and `A` is a separable algebra.

## Reference

* [Benson Farb , R. Keith Dennis, *Noncommutative Algebra*][bensonfarb1993]

## Tags

Azumaya algebra, central simple algebra, noncommutative algebra
-/

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

open TensorProduct MulOpposite

noncomputable instance : Module (A ⊗[R] Aᵐᵒᵖ) A := TensorProduct.Algebra.module

instance : IsScalarTower R (A ⊗[R] Aᵐᵒᵖ) A where
  smul_assoc r aa' x := by
    induction aa' using TensorProduct.induction_on with
    | zero => simp
    | tmul a a' => exact LinearMap.map_smul₂ _ _ _ _
    | add aa' bb' h1 h2 => simp_all [add_smul]

/-- The canonical map from `A ⊗[R] Aᵐᵒᵖ` to `Module.End R A` where
  `a ⊗ b` maps to `f : x ↦ a * x * b`-/
noncomputable abbrev AlgHom.tensorMopToEnd : (A ⊗[R] Aᵐᵒᵖ) →ₐ[R] Module.End R A :=
  Algebra.Module.toModuleEndAlgHom R A

lemma AlgHom.tensorMopToEnd_apply (a : A) (b : Aᵐᵒᵖ) (x : A) :
    AlgHom.tensorMopToEnd R A (a ⊗ₜ b) x = a * x * b.unop := by
  simp only [tensorMopToEnd, Algebra.Module.toModuleEndAlgHom, coe_mk, Module.toModuleEnd_apply,
    DistribMulAction.toLinearMap_apply]
  change TensorProduct.Algebra.moduleAux _ _ = _
  simp [TensorProduct.Algebra.moduleAux_apply, ← mul_assoc]

/-- An azumaya algebra is a finitely generated, projective and faithful R-algebra where
  `AlgHom.tensorMopToEnd` is an isomorphism. -/
class IsAzumaya extends Module.Projective R A, FaithfulSMul R A, Module.Finite R A: Prop where
    bij : Function.Bijective <| AlgHom.tensorMopToEnd R A
