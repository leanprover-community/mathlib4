/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Generators

/-!
# A multiple tensor product of finitely generated modules is finitely generated

-/

open TensorProduct

namespace PiTensorProduct

instance finite {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Finite R (M i)] :
    Module.Finite R (⨂[R] i, M i) := by
  have hM i := Module.Finite.exists_fin (R := R) (M := M i)
  let γ i := Fin (hM i).choose
  let g ⦃i : ι⦄ : γ i → M i := (hM i).choose_spec.choose
  have hg (i : ι) : Submodule.span R (Set.range (fun (j : γ i) ↦ g j)) = ⊤ :=
    (hM i).choose_spec.choose_spec
  rw [Module.finite_def, ← submodule_span_eq_top hg]
  exact Submodule.fg_span (Set.finite_range _)

end PiTensorProduct
