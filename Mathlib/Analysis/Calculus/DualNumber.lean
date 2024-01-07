/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.NormedSpace.DualNumber
import Mathlib.LinearAlgebra.Dual
/-!
# The link between `TrivSqZeroExt` and `fderiv`

This file defines `TrivSqZeroExt.extend`, which lifts a differentiable function into a function
between the square-zero extensions.
This underpins one approach to automatic differentiation.

## Main definitions

* `TrivSqZeroExt.extend`
* `DualNumber.extend`
-/

variable {𝕜 𝕜' 𝕜'' R R' R'' M : Type*}

namespace TrivSqZeroExt

variable [IsROrC 𝕜] [NormedRing R] [NormedRing R'] [NormedRing R''] [NormedAddCommGroup M]

variable [NormedAlgebra 𝕜 R] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
variable [NormedAlgebra 𝕜 R'] [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]
variable [NormedAlgebra 𝕜 R''] [Module R'' M] [Module R''ᵐᵒᵖ M] [IsCentralScalar R'' M]


variable [NormedSpace 𝕜 M] [IsScalarTower 𝕜 R M] [IsScalarTower 𝕜 R' M] [IsScalarTower 𝕜 R'' M]

local notation "tsze" => TrivSqZeroExt


/-- Extend a differentiable function to a function on the square zero extension. -/
def extend (f : R → R') {f' : R → R →L[𝕜] R'} (_h : ∀ x, HasFDerivAt f (f' x) x)
    (x : tsze R (M →L[𝕜] R)) : tsze R' (M →L[𝕜] R') :=
  .inl (f x.fst) + .inr (f' x.fst ∘L x.snd)

theorem extend_mul (f g : R → R') {f' g' : R → R →L[𝕜] R'}
  (hf : ∀ x, HasFDerivAt f (f' x) x) (hg : ∀ x, HasFDerivAt g (g' x) x) :
    extend (M := M) (f * g) (fun x => (hf x).mul' (hg x)) =
      (extend (M := M) f hf * extend (M := M) g hg) := by
  unfold extend
  ext x
  · dsimp
    simp_rw [add_zero]
  · dsimp
    simp_rw [add_zero, zero_add]

theorem extend_comp (f : R' → R'') (g : R → R') {f' : R' → R' →L[𝕜] R''} {g' : R → R →L[𝕜] R'}
  (hf : ∀ x, HasFDerivAt f (f' x) x) (hg : ∀ x, HasFDerivAt g (g' x) x) :
    extend (M := M) (f ∘ g) (fun x => .comp _ (hf _) (hg _)) =
      (extend (M := M) f hf ∘ extend (M := M) g hg) := by
  unfold extend
  ext x
  · dsimp
    simp_rw [add_zero]
  · dsimp
    simp_rw [add_zero, zero_add]

end TrivSqZeroExt

namespace DualNumber

variable [NontriviallyNormedField 𝕜]

/-- Extend a differentiable function to a function on the dual numbers. -/
def extend (f : 𝕜 → 𝕜) {f' : 𝕜 → 𝕜} (_h : ∀ x, HasDerivAt f (f' x) x) (x : DualNumber 𝕜) :
    DualNumber 𝕜 :=
  algebraMap _ _ (f x.fst) + x.snd • f' x.fst • .eps

theorem extend_mul (f g : 𝕜 → 𝕜) {f' g' : 𝕜 → 𝕜}
  (hf : ∀ x, HasDerivAt f (f' x) x) (hg : ∀ x, HasDerivAt g (g' x) x) :
    extend (f * g) (fun x => (hf x).mul (hg x)) = extend f hf * extend g hg := by
  ext x <;> dsimp [extend] <;> simp [TrivSqZeroExt.algebraMap_eq_inl, mul_add, add_comm,
    mul_assoc, mul_left_comm]

theorem extend_comp (f g : 𝕜 → 𝕜) {f' g' : 𝕜 → 𝕜}
  (hf : ∀ x, HasDerivAt f (f' x) x) (hg : ∀ x, HasDerivAt g (g' x) x) :
    extend (f ∘ g) (fun x => .comp x (hf _) (hg x)) = extend f hf ∘ extend g hg := by
  ext x
  · simp [extend, TrivSqZeroExt.algebraMap_eq_inl]
  · simp [extend, TrivSqZeroExt.algebraMap_eq_inl]
    ring

end DualNumber
