/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Module.Presentation.Free
import Mathlib.Algebra.Module.Presentation.PiTensor

/-! # The tensor product of a finite family of free modules is free

-/

universe w w' u v

variable {R : Type u} [CommRing R] {ι : Type w} [Finite ι]
  {M : ι → Type v} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

open TensorProduct PiTensorProduct Module

namespace Basis

variable {α : ι → Type w'} (b : ∀ i, Basis (α i) R (M i))

variable [DecidableEq ι]

/-- A family of bases for a finite family of modules induces a basis
for their tensor product. -/
noncomputable def piTensorProduct : Basis (Π i, α i) R (⨂[R] i, M i) :=
  (Module.Presentation.piTensor (fun i ↦ (b i).presentation)).basis

@[simp]
lemma piTensorProduct_apply (v : Π i, α i) :
    piTensorProduct b v = tprod _ (fun i ↦ b i (v i)) :=
  Module.Relations.Solution.IsPresentation.basis_apply _ _

end Basis

instance Module.free_piTensorProduct
    [∀ i, Module.Free R (M i)] : Free R (⨂[R] i, M i) := by
  classical
  exact Free.of_basis (Basis.piTensorProduct (fun i ↦ Free.chooseBasis R (M i)))
