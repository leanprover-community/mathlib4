/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.RingTheory.Finiteness.Cardinality

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

instance Module.Finite.matrix {R ι₁ ι₂ M : Type*}
    [Semiring R] [AddCommMonoid M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [_root_.Finite ι₁] [_root_.Finite ι₂] :
    Module.Finite R (Matrix ι₁ ι₂ M) := by
  cases nonempty_fintype ι₁
  cases nonempty_fintype ι₂
  exact Module.Finite.of_basis <| (Free.chooseBasis _ _).matrix _ _

example {ι₁ ι₂ R : Type*} [Semiring R] [Finite ι₁] [Finite ι₂] :
    Module.Finite R (Matrix ι₁ ι₂ R) := inferInstance
