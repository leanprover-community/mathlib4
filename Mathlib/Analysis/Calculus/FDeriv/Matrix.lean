/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.Matrix
import Mathlib.Data.Matrix.Bilinear
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Data.Matrix.Hadamard
import Mathlib.Topology.UniformSpace.Matrix

/-!
# Fréchet derivatives of Matrices

This file proves results about `fderiv` and matrix operations.
-/

variable {ι : Type*} {𝕜 : Type*} {E F : Type*} {A : Type*} {m n p q : Type*}

variable [Fintype m] [Fintype n] [Fintype p] [Fintype q]

open scoped Kronecker
open Matrix

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

section elementwise

theorem hasFDerivAtFilter_matrix
    {M : E → Matrix m n F} {x : E} {M' : E →L[𝕜] Matrix m n F} {L : Filter E} :
    HasFDerivAtFilter M M' x L ↔ ∀ i j,
      HasFDerivAtFilter (fun x => M x i j)
        (⟨Matrix.entryLinearMap 𝕜 F i j, continuous_id.matrix_elem i j⟩ ∘L M') x L := by
  erw [hasFDerivAtFilter_pi']
  simp_rw [hasFDerivAtFilter_pi', ← ContinuousLinearMap.comp_assoc]
  rfl

theorem hasFDerivWithinAt_matrix
    {M : E → Matrix m n F} {s : Set E} {x : E} {M' : E →L[𝕜] Matrix m n F} :
    HasFDerivWithinAt M M' s x ↔ ∀ i j,
      HasFDerivWithinAt (fun x => M x i j)
        (⟨Matrix.entryLinearMap 𝕜 F i j, continuous_id.matrix_elem i j⟩ ∘L M') s x :=
  hasFDerivAtFilter_matrix

theorem hasFDerivAt_matrix {M : E → Matrix m n F} {x : E} {M' : E →L[𝕜] Matrix m n F} :
    HasFDerivAt M M' x ↔ ∀ i j,
      HasFDerivAt (fun x => M x i j)
        (⟨Matrix.entryLinearMap 𝕜 F i j, continuous_id.matrix_elem i j⟩ ∘L M') x :=
  hasFDerivAtFilter_matrix

theorem differentiableWithinAt_matrix {M : E → Matrix m n F} {s : Set E} {x : E} :
    DifferentiableWithinAt 𝕜 M s x ↔ ∀ i j, DifferentiableWithinAt 𝕜 (fun x => M x i j) s x := by
  erw [differentiableWithinAt_pi]
  simp_rw [differentiableWithinAt_pi]

theorem differentiableAt_matrix {M : E → Matrix m n F} {x : E} :
    DifferentiableAt 𝕜 M x ↔ ∀ i j, DifferentiableAt 𝕜 (fun x => M x i j) x := by
  erw [differentiableAt_pi]
  simp_rw [differentiableAt_pi]

theorem differentiableOn_matrix {M : E → Matrix m n F} {s : Set E} :
    DifferentiableOn 𝕜 M s ↔ ∀ i j, DifferentiableOn 𝕜 (fun x => M x i j) s := by
  erw [differentiableOn_pi]
  simp_rw [differentiableOn_pi]

theorem differentiable_matrix {M : E → Matrix m n F} :
    Differentiable 𝕜 M ↔ ∀ i j, Differentiable 𝕜 (fun x => M x i j) := by
  erw [differentiable_pi]
  simp_rw [differentiable_pi]

end elementwise

/-- `HasFDerivAt.mul` for rectangular matrices. -/
theorem HasFDerivAt.matrix_mul [NormedRing A] [NormedAlgebra 𝕜 A]
    {M : E → Matrix m n A} {N : E → Matrix n p A}
    {M' : E →L[𝕜] Matrix m n A} {N' : E →L[𝕜] Matrix n p A} {x : E}
    (hM : HasFDerivAt M M' x) (hN : HasFDerivAt N N' x) :
    HasFDerivAt (fun a => M a * N a)
      (⟨mulLeftLinearMap p 𝕜 (M x), continuous_const.matrix_mul continuous_id⟩ ∘L N' +
      ⟨mulRightLinearMap m 𝕜 (N x), continuous_id.matrix_mul continuous_const⟩ ∘L M') x := by
  rw [hasFDerivAt_matrix] at hM hN ⊢
  intro i j
  simp only [mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  refine (HasFDerivAt.sum fun k _hk => (hM _ _).mul' (hN _ _)).congr_fderiv ?_
  ext x
  simp [Finset.sum_add_distrib, Matrix.mul_apply]

section trace

theorem HasFDerivAtFilter.matrix_trace
    {M : E → Matrix m m F} {x : E} {M' : E →L[𝕜] Matrix m m F} {L : Filter E}
    (hM : HasFDerivAtFilter M M' x L) :
    HasFDerivAtFilter (fun a => (M a).trace)
      (⟨Matrix.traceLinearMap _ _ _, continuous_id.matrix_trace⟩ ∘L M') x L := by
  have := (HasFDerivAtFilter.sum fun i (hi : i ∈ Finset.univ) =>
    (hasFDerivAtFilter_matrix.mp hM : _) i i)
  convert this using 1
  ext
  simp [Matrix.trace]

theorem HasFDerivWithinAt.matrix_trace
    {M : E → Matrix m m F} {s : Set E} {x : E} {M' : E →L[𝕜] Matrix m m F}
    (hM : HasFDerivWithinAt M M' s x) :
    HasFDerivWithinAt (fun a => (M a).trace)
      (⟨Matrix.traceLinearMap _ _ _, continuous_id.matrix_trace⟩ ∘L M') s x :=
  HasFDerivAtFilter.matrix_trace hM

theorem HasFDerivAt.matrix_trace {M : E → Matrix m m F} {x : E} {M' : E →L[𝕜] Matrix m m F}
    (hM : HasFDerivAt M M' x) :
    HasFDerivAt (fun a => (M a).trace)
      (⟨Matrix.traceLinearMap _ _ _, continuous_id.matrix_trace⟩ ∘L M') x :=
  HasFDerivAtFilter.matrix_trace hM

theorem DifferentiableWithinAt.matrix_trace {M : E → Matrix m m F} {s : Set E} {x : E}
    (hM : DifferentiableWithinAt 𝕜 M s x) :
    DifferentiableWithinAt 𝕜 (fun a => (M a).trace) s x :=
  let ⟨_, hM⟩ := hM; hM.matrix_trace.differentiableWithinAt

theorem DifferentiableOn.matrix_trace {M : E → Matrix m m F} {s : Set E}
    (hM : DifferentiableOn 𝕜 M s) :
    DifferentiableOn 𝕜 (fun a => (M a).trace) s :=
  fun x hx => (hM x hx).matrix_trace

theorem DifferentiableAt.matrix_trace {M : E → Matrix m m F} {x : E}
    (hM : DifferentiableAt 𝕜 M x) :
    DifferentiableAt 𝕜 (fun a => (M a).trace) x :=
  let ⟨_, hM⟩ := hM; hM.matrix_trace.differentiableAt

theorem Differentiable.matrix_trace {M : E → Matrix m m F} (hM : Differentiable 𝕜 M) :
    Differentiable 𝕜 (fun a => (M a).trace) :=
  fun x => (hM x).matrix_trace

end trace

section transpose

theorem HasFDerivAtFilter.matrix_transpose
    {M : E → Matrix m n F} {M' : E →L[𝕜] Matrix m n F} {x : E} {L : Filter E}
    (hM : HasFDerivAtFilter M M' x L) :
    HasFDerivAtFilter (fun a => (M a)ᵀ)
      (⟨Matrix.transposeLinearEquiv m n 𝕜 F, continuous_id.matrix_transpose⟩ ∘L M') x L :=
  hasFDerivAtFilter_matrix.mpr fun i j => (hasFDerivAtFilter_matrix.mp hM : _) j i

theorem HasFDerivWithinAt.matrix_transpose
    {M : E → Matrix m n F} {M' : E →L[𝕜] Matrix m n F} {s : Set E} {x : E}
    (hM : HasFDerivWithinAt M M' s x) :
    HasFDerivWithinAt (fun a => (M a)ᵀ)
      (⟨Matrix.transposeLinearEquiv m n 𝕜 F, continuous_id.matrix_transpose⟩ ∘L M') s x :=
  HasFDerivAtFilter.matrix_transpose hM

theorem HasFDerivAt.matrix_transpose
    {M : E → Matrix m n F} {M' : E →L[𝕜] Matrix m n F} {x : E} (hM : HasFDerivAt M M' x) :
    HasFDerivAt (fun a => (M a)ᵀ)
      (⟨Matrix.transposeLinearEquiv m n 𝕜 F, continuous_id.matrix_transpose⟩ ∘L M') x :=
  HasFDerivAtFilter.matrix_transpose hM

theorem DifferentiableWithinAt.matrix_transpose {M : E → Matrix m n F} {s : Set E} {x : E}
    (hM : DifferentiableWithinAt 𝕜 M s x) :
    DifferentiableWithinAt 𝕜 (fun a => (M a)ᵀ) s x :=
  let ⟨_, hM⟩ := hM; let aux := hM.matrix_transpose
  by convert aux.differentiableWithinAt

theorem DifferentiableOn.matrix_transpose {M : E → Matrix m n F} {s : Set E}
    (hM : DifferentiableOn 𝕜 M s) :
    DifferentiableOn 𝕜 (fun a => (M a)ᵀ) s :=
  fun x hx => (hM x hx).matrix_transpose

theorem DifferentiableAt.matrix_transpose {M : E → Matrix m n F} {x : E}
    (hM : DifferentiableAt 𝕜 M x) :
    DifferentiableAt 𝕜 (fun a => (M a)ᵀ) x :=
  let ⟨_, hM⟩ := hM; hM.matrix_transpose.differentiableAt

theorem Differentiable.matrix_transpose {M : E → Matrix m n F} (hM : Differentiable 𝕜 M) :
    Differentiable 𝕜 (fun a => (M a)ᵀ) :=
  fun x => (hM x).matrix_transpose

end transpose

section conjTranspose
variable [StarRing 𝕜] [TrivialStar 𝕜] [StarAddMonoid F] [StarModule 𝕜 F] [ContinuousStar F]

theorem HasFDerivAtFilter.matrix_conjTranspose
    {M : E → Matrix m n F} {M' : E →L[𝕜] Matrix m n F} {x : E} {L : Filter E}
    (hM : HasFDerivAtFilter M M' x L) :
    HasFDerivAtFilter (fun a => (M a)ᴴ)
      (⟨{ Matrix.conjTransposeLinearEquiv m n 𝕜 F with map_smul' := by simp},
          continuous_id.matrix_conjTranspose⟩ ∘L M') x L :=
  (hasFDerivAtFilter_matrix.mpr fun i j => ((hasFDerivAtFilter_matrix.mp hM : _) j i).star)

theorem HasFDerivAt.matrix_conjTranspose
    {M : E → Matrix m n F} {M' : E →L[𝕜] Matrix m n F} {x : E} (hM : HasFDerivAt M M' x) :
    HasFDerivAt (fun a => (M a)ᴴ)
      (⟨{ Matrix.conjTransposeLinearEquiv m n 𝕜 F with map_smul' := by simp},
          continuous_id.matrix_conjTranspose⟩ ∘L M') x :=
  HasFDerivAtFilter.matrix_conjTranspose hM

end conjTranspose
