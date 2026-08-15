/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Instances.Matrix

/-!
# Measurable space structure on Matrices

If `α` is a measurable space, we set the measurable space structure on `Matrix m n α` to be the
same as the one on `m → n → α`.
-/

@[expose] public section

variable (m n α : Type*) [MeasurableSpace α]

namespace Matrix

instance : MeasurableSpace (Matrix m n α) := inferInstanceAs <| MeasurableSpace (m → n → α)

@[fun_prop]
lemma measurable_matrix_of : Measurable <| Matrix.of (m := m) (n := n) (α := α) :=
  measurable_id

variable [Countable m] [Countable n] [TopologicalSpace α] [SecondCountableTopology α]
  [BorelSpace α]

instance : BorelSpace (Matrix m n α) := inferInstanceAs <| BorelSpace (m → n → α)

end Matrix

namespace MeasurableEquiv

/-- The map from `m → n → α` to `Matrix m n α` as a measurable equivalence. -/
protected def toMatrix : (m → n → α) ≃ᵐ (Matrix m n α) where
  toEquiv := Matrix.of.symm
  measurable_toFun := measurable_id
  measurable_invFun := Matrix.measurable_matrix_of m n α

lemma coe_toMatrix : ⇑(MeasurableEquiv.toMatrix m n α) = Matrix.of.symm := rfl

lemma coe_toMatrix_symm : ⇑(MeasurableEquiv.toMatrix m n α).symm = Matrix.of := rfl

@[simp]
lemma toMatrix_apply (f : m → n → α) : MeasurableEquiv.toMatrix m n α f = Matrix.of.symm f := rfl

@[simp]
lemma toMatrix_symm_apply (M : Matrix m n α) :
    (MeasurableEquiv.toMatrix m n α).symm M = Matrix.of M := rfl

end MeasurableEquiv
