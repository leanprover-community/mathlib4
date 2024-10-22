/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.RingTheory.Finiteness
import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Finite and free modules

We provide some instances for finite and free modules.

## Main results

* `Module.Free.ChooseBasisIndex.fintype` : If a free module is finite, then any basis is finite.
* `Module.Finite.of_basis` : A free module with a basis indexed by a `Fintype` is finite.
-/


universe u v w

/-- If a free module is finite, then the arbitrary basis is finite. -/
noncomputable instance Module.Free.ChooseBasisIndex.fintype (R : Type u) (M : Type v)
    [Semiring R] [AddCommMonoid M] [Module R M] [Module.Free R M] [Module.Finite R M] :
    Fintype (Module.Free.ChooseBasisIndex R M) := by
  refine @Fintype.ofFinite _ ?_
  cases subsingleton_or_nontrivial R
  · have := Module.subsingleton R M
    rw [ChooseBasisIndex]
    infer_instance
  · exact Module.Finite.finite_basis (chooseBasis _ _)

/-- A free module with a basis indexed by a `Fintype` is finite. -/
theorem Module.Finite.of_basis {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [_root_.Finite ι] (b : Basis ι R M) : Module.Finite R M := by
  cases nonempty_fintype ι
  classical
    refine ⟨⟨Finset.univ.image b, ?_⟩⟩
    simp only [Set.image_univ, Finset.coe_univ, Finset.coe_image, Basis.span_eq]

instance Module.Finite.matrix {R : Type u} [Semiring R]
    {ι₁ ι₂ : Type*} [_root_.Finite ι₁] [_root_.Finite ι₂] :
    Module.Finite R (Matrix ι₁ ι₂ R) := by
  cases nonempty_fintype ι₁
  cases nonempty_fintype ι₂
  exact Module.Finite.of_basis (Pi.basis fun _ => Pi.basisFun R _)
