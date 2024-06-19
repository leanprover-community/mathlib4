/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.RingTheory.Finiteness
import Mathlib.LinearAlgebra.FreeModule.Basic

#align_import linear_algebra.free_module.finite.basic from "leanprover-community/mathlib"@"59628387770d82eb6f6dd7b7107308aa2509ec95"

/-!
# Finite and free modules

We provide some instances for finite and free modules.

## Main results

* `Module.Free.ChooseBasisIndex.fintype` : If a free module is finite, then any basis is finite.
* `Module.Finite.of_basis` : A free module with a basis indexed by a `Fintype` is finite.
-/


universe u v w

variable (R : Type u) (M : Type v) (N : Type w)

namespace Module.Free

section Ring

variable [Ring R] [AddCommGroup M] [Module R M] [Module.Free R M]

/-- If a free module is finite, then the arbitrary basis is finite. -/
noncomputable instance ChooseBasisIndex.fintype [Module.Finite R M] :
    Fintype (Module.Free.ChooseBasisIndex R M) := by
  refine @Fintype.ofFinite _ ?_
  cases subsingleton_or_nontrivial R
  · have := Module.subsingleton R M
    rw [ChooseBasisIndex]
    infer_instance
  · exact Module.Finite.finite_basis (chooseBasis _ _)
#align module.free.choose_basis_index.fintype Module.Free.ChooseBasisIndex.fintype

end Ring

section CommRing

variable [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]
variable [AddCommGroup N] [Module R N] [Module.Free R N]
variable {R}

/-- A free module with a basis indexed by a `Fintype` is finite. -/
theorem _root_.Module.Finite.of_basis {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [_root_.Finite ι] (b : Basis ι R M) : Module.Finite R M := by
  cases nonempty_fintype ι
  classical
    refine ⟨⟨Finset.univ.image b, ?_⟩⟩
    simp only [Set.image_univ, Finset.coe_univ, Finset.coe_image, Basis.span_eq]
#align module.finite.of_basis Module.Finite.of_basis

instance _root_.Module.Finite.matrix {ι₁ ι₂ : Type*} [_root_.Finite ι₁] [_root_.Finite ι₂] :
    Module.Finite R (Matrix ι₁ ι₂ R) := by
  cases nonempty_fintype ι₁
  cases nonempty_fintype ι₂
  exact Module.Finite.of_basis (Pi.basis fun _ => Pi.basisFun R _)
#align module.finite.matrix Module.Finite.matrix

end CommRing

end Module.Free
