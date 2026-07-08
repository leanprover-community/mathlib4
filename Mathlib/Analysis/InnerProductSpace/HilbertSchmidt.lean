/-
Copyright (c) 2026 Zihua Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zihua Wu
-/
module

public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The Hilbert–Schmidt inner product on finite-dimensional operators

For linear maps `S T : E →ₗ[𝕜] F` between finite-dimensional inner product spaces, the
**Hilbert–Schmidt** (Frobenius) inner product is
`⟪S, T⟫ = trace (adjoint S ∘ₗ T) = ∑ᵢ ⟪S eᵢ, T eᵢ⟫` for any orthonormal basis `e` of `E`,
with norm `‖T‖ = √(∑ᵢ ‖T eᵢ‖²)`.

This mirrors the matrix Frobenius norm (`Matrix.frobeniusNormedAddCommGroup`, scoped in
`Matrix.Norms.Frobenius`), built through `InnerProductSpace.Core`. It is provided as a
`LinearMap.Norms.HilbertSchmidt`-scoped instance (rather
than global), since `E →ₗ[𝕜] F` should not carry a canonical norm — matching the
`Matrix.Norms.Frobenius` convention.

## Main definitions

- `LinearMap.hilbertSchmidtCore`: the `InnerProductSpace.Core` on `E →ₗ[𝕜] F`.
- `LinearMap.hilbertSchmidtNormedAddCommGroup` / `LinearMap.hilbertSchmidtInnerProductSpace`: the
  Frobenius norm and inner product, made `LinearMap.Norms.HilbertSchmidt`-scoped instances (activate
  with `open scoped LinearMap.Norms.HilbertSchmidt`).

## Main statements

- `LinearMap.hilbertSchmidt_inner_eq_trace`: `⟪S, T⟫ = trace (adjoint S ∘ₗ T)`.
- `LinearMap.hilbertSchmidt_norm_sq_eq_re_trace`: `‖T‖ ^ 2 = re (trace (adjoint T ∘ₗ T))`.
- `LinearMap.hilbertSchmidt_norm_sq_eq_sum_norm_sq`: `‖T‖ ^ 2 = ∑ i, ‖T (b i)‖ ^ 2` for any
  orthonormal basis `b`.
-/

@[expose] public section

open Module ComplexConjugate
open scoped InnerProductSpace

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- `trace (adjoint S ∘ₗ T) = ∑ᵢ ⟪S eᵢ, T eᵢ⟫` for any orthonormal basis `e` of `E`. -/
theorem trace_adjoint_comp_eq_sum_inner {ι : Type*} [Fintype ι]
    (S T : E →ₗ[𝕜] F) (b : OrthonormalBasis ι 𝕜 E) :
    LinearMap.trace 𝕜 E (adjoint S ∘ₗ T) = ∑ i, inner 𝕜 (S (b i)) (T (b i)) := by
  rw [LinearMap.trace_eq_sum_inner (adjoint S ∘ₗ T) b]
  exact Finset.sum_congr rfl fun i _ => by rw [LinearMap.comp_apply, adjoint_inner_right]

/-- The Hilbert–Schmidt inner product core `⟪S, T⟫ = trace (adjoint S ∘ₗ T)` on `E →ₗ[𝕜] F`. -/
@[implicit_reducible] noncomputable def hilbertSchmidtCore :
    InnerProductSpace.Core 𝕜 (E →ₗ[𝕜] F) where
  inner S T := LinearMap.trace 𝕜 E (adjoint S ∘ₗ T)
  conj_inner_symm S T := by
    rw [trace_adjoint_comp_eq_sum_inner T S (stdOrthonormalBasis 𝕜 E),
      trace_adjoint_comp_eq_sum_inner S T (stdOrthonormalBasis 𝕜 E), map_sum]
    exact Finset.sum_congr rfl fun i _ => inner_conj_symm _ _
  re_inner_nonneg T := by
    show 0 ≤ RCLike.re (LinearMap.trace 𝕜 E (adjoint T ∘ₗ T))
    rw [trace_adjoint_comp_eq_sum_inner T T (stdOrthonormalBasis 𝕜 E), map_sum]
    exact Finset.sum_nonneg fun i _ => by rw [inner_self_eq_norm_sq]; positivity
  add_left S T U := by
    change LinearMap.trace 𝕜 E (adjoint (S + T) ∘ₗ U)
      = LinearMap.trace 𝕜 E (adjoint S ∘ₗ U) + LinearMap.trace 𝕜 E (adjoint T ∘ₗ U)
    rw [map_add, LinearMap.add_comp, map_add]
  smul_left S T r := by
    change LinearMap.trace 𝕜 E (adjoint (r • S) ∘ₗ T)
      = conj r * LinearMap.trace 𝕜 E (adjoint S ∘ₗ T)
    rw [map_smulₛₗ, LinearMap.smul_comp, map_smul, smul_eq_mul]
  definite T h := by
    rw [trace_adjoint_comp_eq_sum_inner T T (stdOrthonormalBasis 𝕜 E)] at h
    have hre : ∑ i, ‖T (stdOrthonormalBasis 𝕜 E i)‖ ^ 2 = 0 := by
      simpa [map_sum, inner_self_eq_norm_sq] using congrArg RCLike.re h
    refine Basis.ext (stdOrthonormalBasis 𝕜 E).toBasis fun i => ?_
    simpa using (Finset.sum_eq_zero_iff_of_nonneg fun j _ => by positivity).mp hre i
      (Finset.mem_univ i)

/-- The Hilbert–Schmidt (Frobenius) `NormedAddCommGroup` on `E →ₗ[𝕜] F`. Not a global instance;
made a `LinearMap.Norms.HilbertSchmidt`-scoped instance below, mirroring
`Matrix.frobeniusNormedAddCommGroup`. -/
@[implicit_reducible, local instance]
noncomputable def hilbertSchmidtNormedAddCommGroup : NormedAddCommGroup (E →ₗ[𝕜] F) :=
  hilbertSchmidtCore.toNormedAddCommGroup

/-- The Hilbert–Schmidt (Frobenius) `InnerProductSpace` on `E →ₗ[𝕜] F`. Not a global instance;
made a `LinearMap.Norms.HilbertSchmidt`-scoped instance below. -/
@[implicit_reducible, local instance]
noncomputable def hilbertSchmidtInnerProductSpace : InnerProductSpace 𝕜 (E →ₗ[𝕜] F) :=
  letI := hilbertSchmidtCore (𝕜 := 𝕜) (E := E) (F := F)
  InnerProductSpace.ofCore _

theorem hilbertSchmidt_inner_eq_trace (S T : E →ₗ[𝕜] F) :
    inner 𝕜 S T = LinearMap.trace 𝕜 E (LinearMap.adjoint S ∘ₗ T) := rfl

/-- The defining identity of the Hilbert–Schmidt norm: `‖T‖² = re (trace (adjoint T ∘ₗ T))`. -/
theorem hilbertSchmidt_norm_sq_eq_re_trace (T : E →ₗ[𝕜] F) :
    ‖T‖ ^ 2 = RCLike.re (LinearMap.trace 𝕜 E (LinearMap.adjoint T ∘ₗ T)) := by
  rw [← hilbertSchmidt_inner_eq_trace T T]; exact (inner_self_eq_norm_sq (𝕜 := 𝕜) T).symm

/-- The Hilbert–Schmidt norm via any orthonormal basis: `‖T‖ ^ 2 = ∑ i, ‖T (b i)‖ ^ 2`. -/
theorem hilbertSchmidt_norm_sq_eq_sum_norm_sq {ι : Type*} [Fintype ι] (T : E →ₗ[𝕜] F)
    (b : OrthonormalBasis ι 𝕜 E) : ‖T‖ ^ 2 = ∑ i, ‖T (b i)‖ ^ 2 := by
  rw [hilbertSchmidt_norm_sq_eq_re_trace, trace_adjoint_comp_eq_sum_inner T T b, map_sum]
  exact Finset.sum_congr rfl fun i _ => inner_self_eq_norm_sq _

end LinearMap

/-! ### The `LinearMap.Norms.HilbertSchmidt`-scoped norm and inner product on `E →ₗ[𝕜] F`

Activate with `open scoped LinearMap.Norms.HilbertSchmidt`. -/

namespace LinearMap.Norms.HilbertSchmidt

attribute [scoped instance]
  LinearMap.hilbertSchmidtNormedAddCommGroup LinearMap.hilbertSchmidtInnerProductSpace

end LinearMap.Norms.HilbertSchmidt
