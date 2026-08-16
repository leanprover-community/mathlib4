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

lemma measurable_iff [MeasurableSpace m] {M : Matrix m n α} :
    Measurable M ↔ ∀ j, Measurable fun i ↦ M i j := measurable_pi_iff

lemma measurable_eval [MeasurableSpace m] {j : n} {M : Matrix m n α} (hM : Measurable M) :
    Measurable fun i ↦ M i j := hM.eval

lemma measurable_lambda [MeasurableSpace m] (M : Matrix m n α)
    (hM : ∀ j, Measurable fun i ↦ M i j) : Measurable M := measurable_pi_lambda M hM

@[fun_prop]
lemma measurable_of : Measurable <| Matrix.of (m := m) (n := n) (α := α) :=
  measurable_id

instance [Countable m] [Countable n] [TopologicalSpace α] [SecondCountableTopology α]
  [BorelSpace α] : BorelSpace (Matrix m n α) := inferInstanceAs <| BorelSpace (m → n → α)

protected def ofMeasurableEquiv : (m → n → α) ≃ᵐ (Matrix m n α) where
  toEquiv := Matrix.of
  measurable_toFun := measurable_id
  measurable_invFun := measurable_of m n α

lemma coe_toMatrix : ⇑(Matrix.ofMeasurableEquiv m n α) = Matrix.of := rfl

lemma coe_toMatrix_symm : ⇑(Matrix.ofMeasurableEquiv m n α).symm = Matrix.of.symm := rfl

@[simp]
lemma toMatrix_apply (f : m → n → α) : Matrix.ofMeasurableEquiv m n α f = Matrix.of f := rfl

@[simp]
lemma toMatrix_symm_apply (M : Matrix m n α) :
    (Matrix.ofMeasurableEquiv m n α).symm M = Matrix.of.symm M := rfl

end Matrix
