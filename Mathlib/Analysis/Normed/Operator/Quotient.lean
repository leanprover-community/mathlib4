/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Operator norms and quotient maps

For a submodule `S` of a seminormed space `E`, we compute the operator norms of the quotient map
`S.mkQL : E →L[𝕜] E ⧸ S` and of continuous linear maps out of the quotient `E ⧸ S`.

## Main results

* `ContinuousLinearMap.opNorm_comp_mkQL`: precomposition with the quotient map preserves the
  operator norm: `‖g.comp S.mkQL‖ = ‖g‖`.
* `Submodule.norm_mkQL`: the quotient map has norm `1` when the quotient is (topologically)
  nontrivial, i.e., when `S` is not dense.
* `Submodule.norm_mkQL_eq_zero`: the quotient map has norm `0` when the quotient is indiscrete,
  i.e., when `S` is dense.
* `Submodule.norm_liftQL`: the map induced on a quotient has the same norm as the original map.
* `ContinuousLinearMap.opNorm_le_mul_opNorm_comp_of_antilipschitz_liftQL`: if `f` has dense range
  and the induced map `E ⧸ f.ker →L[𝕜] E'` is `K`-antilipschitz, then `‖g‖ ≤ K * ‖g.comp f‖`.
-/

@[expose] public section

open NNReal

variable {𝕜 𝕜₂ E E' F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  {σ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup E'] [NormedSpace 𝕜 E'] [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F]

namespace Submodule

variable (S : Submodule 𝕜 E)

/-- The quotient map has norm at most `1`. -/
theorem norm_mkQL_le : ‖S.mkQL‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by
    simpa using Quotient.norm_mk_le S x

/-- The quotient map has norm `0` when the quotient is indiscrete, i.e., when `S` is dense. -/
theorem norm_mkQL_eq_zero [IndiscreteTopology (E ⧸ S)] : ‖S.mkQL‖ = 0 :=
  le_antisymm (ContinuousLinearMap.opNorm_le_bound _ le_rfl fun x ↦ by
    simp [IndiscreteTopology.norm_eq_zero]) (norm_nonneg _)

end Submodule

namespace ContinuousLinearMap

variable {S : Submodule 𝕜 E}

/-- Precomposition with the quotient map preserves the operator norm. -/
@[simp]
theorem opNorm_comp_mkQL (g : E ⧸ S →SL[σ] F) : ‖g.comp S.mkQL‖ = ‖g‖ := by
  refine le_antisymm (by grw [g.opNorm_comp_le _, S.norm_mkQL_le, mul_one]) ?_
  refine g.opNorm_le_bound (norm_nonneg _) fun x ↦ le_mul_of_forall_lt₀ fun C hC r hr ↦ ?_
  obtain ⟨m, rfl, hm⟩ := (QuotientAddGroup.norm_lt_iff (S := S.toAddSubgroup)).mp hr
  have hr : 0 < r := by grw [← hm]; positivity
  calc ‖g (QuotientAddGroup.mk m)‖ ≤ ‖g ∘SL S.mkQL‖ * ‖m‖ := (g.comp S.mkQL).le_opNorm m
    _ ≤ C * r := by grw [hm.le, hC.le]

/-- If `f` has dense range and the induced map `E ⧸ f.ker →L[𝕜] E'` is `K`-antilipschitz, then the
norm of a continuous linear map from the codomain of `f` is bounded by `K` multiplied by the norm
of the precomposition with `f`. -/
theorem opNorm_le_mul_opNorm_comp_of_antilipschitz_liftQL (g : E' →SL[σ] F) {f : E →L[𝕜] E'}
    (hf : DenseRange f) {K : ℝ≥0} (hK : AntilipschitzWith K (f.ker.liftQL f le_rfl)) :
    ‖g‖ ≤ K * ‖g.comp f‖ := by
  have hf' : DenseRange (f.ker.liftQL f le_rfl) := hf.of_comp (g := f.ker.mkQL)
  calc ‖g‖ ≤ K * ‖g.comp (f.ker.liftQL f _)‖ := g.opNorm_le_mul_opNorm_comp_of_antilipschitz hf' hK
    _ = K * ‖g.comp f‖ := by rw [← opNorm_comp_mkQL, comp_assoc, Submodule.liftQL_comp_mkQL]

end ContinuousLinearMap

namespace Submodule

variable (S : Submodule 𝕜 E)

/-- When the quotient is nontrivial (topologically), the quotient map has norm `1`.
This occurs precisely when the submodule is not dense. See
`Submodule.Quotient.nontrivialTopology_iff`. -/
@[simp]
theorem norm_mkQL [NontrivialTopology (E ⧸ S)] : ‖S.mkQL‖ = 1 := by
  simpa using (ContinuousLinearMap.id 𝕜 (E ⧸ S)).opNorm_comp_mkQL

/-- For a continuous linear map `f : E →SL[σ] F`, its operator norm coincides with the induced map
from any quotient `E ⧸ S →SL[σ] F` where `S` is contained in the kernel of `f`. -/
@[simp]
theorem norm_liftQL (f : E →SL[σ] F) (h : S ≤ f.ker) : ‖S.liftQL f h‖ = ‖f‖ := by
  rw [← ContinuousLinearMap.opNorm_comp_mkQL, liftQL_comp_mkQL]

end Submodule
