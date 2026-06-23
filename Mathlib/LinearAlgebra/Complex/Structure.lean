/-
Copyright (c) 2026 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang
-/
module

public import Mathlib.LinearAlgebra.Complex.Module

/-!
# Complex structures on real vector spaces

A *complex structure* on a real vector space `V` is an `ℝ`-linear endomorphism `J` of `V`
satisfying `J ∘ J = -1`. Such a `J` lets one multiply vectors by `Complex.I` (namely by `J`),
turning `V` into a complex vector space whose underlying real vector space is the original `V`.

## Main definitions

* `ComplexStructure V`: a complex structure on the real vector space `V`, bundled as an
  endomorphism `J` of `V` with `J ∘ J = -1`.
* `ComplexStructure.toAlgHom`: the `ℝ`-algebra homomorphism `ℂ →ₐ[ℝ] Module.End ℝ V` sending
  `Complex.I` to `J`.
* `ComplexStructure.module`: the `Module ℂ V` induced by a complex structure. This is a `def`
  rather than an instance to avoid diamonds with any ambient complex structure on `V`.
* `ComplexStructure.equivAlgHom`: complex structures on `V` are the same data as `ℝ`-algebra
  homomorphisms `ℂ →ₐ[ℝ] Module.End ℝ V`.

-/

@[expose] public section

open scoped Complex

variable (V : Type*) [AddCommGroup V] [Module ℝ V]

/-- A *complex structure* on a real vector space `V` is an `ℝ`-linear endomorphism `J` of `V`
with `J * J = -1`. -/
@[ext]
structure ComplexStructure where
  /-- The endomorphism underlying the complex structure. -/
  toEnd : Module.End ℝ V
  /-- The defining relation `J * J = -1`. -/
  toEnd_mul_self : toEnd * toEnd = -1

namespace ComplexStructure

variable {V}

instance : CoeFun (ComplexStructure V) (fun _ => V → V) where
  coe J := J.toEnd

theorem apply_apply (J : ComplexStructure V) (v : V) : J (J v) = -v := by
  have : (J.toEnd * J.toEnd) v = (-1 : Module.End ℝ V) v := by rw [J.toEnd_mul_self]
  simpa using this

/-- The `ℝ`-algebra homomorphism `ℂ →ₐ[ℝ] Module.End ℝ V` determined by a complex structure,
sending `Complex.I` to `J`. -/
def toAlgHom (J : ComplexStructure V) : ℂ →ₐ[ℝ] Module.End ℝ V :=
  Complex.lift ⟨J.toEnd, J.toEnd_mul_self⟩

@[simp] lemma toAlgHom_I (J : ComplexStructure V) : J.toAlgHom Complex.I = J.toEnd := by
  simp [toAlgHom]

/-- Complex structures on `V` are the same as `ℝ`-algebra homomorphisms
`ℂ →ₐ[ℝ] Module.End ℝ V`. -/
@[simps]
def equivAlgHom : ComplexStructure V ≃ (ℂ →ₐ[ℝ] Module.End ℝ V) where
  toFun J := J.toAlgHom
  invFun f := ⟨f Complex.I, by rw [← map_mul, Complex.I_mul_I, map_neg, map_one]⟩
  left_inv J := by ext1; simp
  right_inv f := by
    apply (Complex.lift.symm).injective
    ext1
    simp [toAlgHom, Complex.lift]

/-- The complex module structure on `V` induced by a complex structure `J`: multiplication by
`Complex.I` acts as `J`. This is a `def` rather than an instance to avoid conflict with any
preexisting complex module on `V`. -/
@[reducible] def module (J : ComplexStructure V) : Module ℂ V :=
  Module.compHom V J.toAlgHom.toRingHom

theorem I_smul (J : ComplexStructure V) (v : V) :
    haveI := J.module; (Complex.I : ℂ) • v = J v := by
  change J.toAlgHom Complex.I v = J v
  simp

theorem ofReal_smul (J : ComplexStructure V) (r : ℝ) (v : V) :
    haveI := J.module; ((r : ℂ)) • v = r • v := by
  change J.toAlgHom r v = r • v
  simp [toAlgHom]

end ComplexStructure
