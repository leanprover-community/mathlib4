/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.LinearAlgebra.Finsupp.Span
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Linear Span

## Main statements

- `LinearMap.mem_span_iff_continuous_of_finite` A linear functional `φ` can be expressed as a linear
  combination of finitely many linear functionals `f₁,…,fₙ` if and only if `φ` is continuous with
  respect to the topology induced by `f₁,…,fₙ`.
- `LinearMap.mem_span_iff_continuous` A linear functional `φ` is in the span of a collection of
  linear functionals if and only if `φ` is continuous with respect to the topology induced by the
  collection of linear functionals.

## References

* [Rudin, *Functional Analysis*][rudin1991]

## Tags

span, continuous

-/

open Topology TopologicalSpace

namespace LinearMap

variable {ι 𝕜 E F : Type*}

section TopologicalRing

variable [Finite ι] [Field 𝕜] [t𝕜 : TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] [T0Space 𝕜]
  [AddCommGroup E] [Module 𝕜 E]

/- A linear functional `φ` can be expressed as a linear combination of finitely many linear
functionals `f₁,…,fₙ` if and only if `φ` is continuous with respect to the topology induced by
`f₁,…,fₙ`. See `LinearMap.mem_span_iff_continuous` for a result about arbitrary collections of
linear functionals. -/
theorem mem_span_iff_continuous_of_finite {f : ι → E →ₗ[𝕜] 𝕜} (φ : E →ₗ[𝕜] 𝕜) :
    φ ∈ Submodule.span 𝕜 (Set.range f) ↔ Continuous[⨅ i, induced (f i) t𝕜, t𝕜] φ := by
  let _ := ⨅ i, induced (f i) t𝕜
  refine ⟨Submodule.span_induction
      (Set.forall_mem_range.mpr fun i ↦ continuous_iInf_dom continuous_induced_dom) continuous_zero
      (fun _ _ _ _ ↦ .add) (fun c _ _ h ↦ h.const_smul c), fun φ_cont ↦ ?_⟩
  apply mem_span_of_iInf_ker_le_ker fun x hx ↦ ?_
  simp_rw [Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  have : Inseparable x 0 := by
    -- Maybe missing lemmas about `Inseparable`?
    simp_rw [Inseparable, nhds_iInf, nhds_induced, hx, map_zero]
  simpa [map_zero] using (this.map φ_cont).eq

end TopologicalRing

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/- A linear functional `φ` is in the span of a collection of linear functionals if and only if `φ`
is continuous with respect to the topology induced by the collection of linear functionals. See
`LinearMap.mem_span_iff_continuous_of_finite` for a result about finite collections of linear
functionals. -/
theorem mem_span_iff_continuous {f : ι → E →ₗ[𝕜] 𝕜} (φ : E →ₗ[𝕜] 𝕜) :
    φ ∈ Submodule.span 𝕜 (Set.range f) ↔
    Continuous[⨅ i, induced (f i) inferInstance, inferInstance] φ := by
  letI t𝕜 : TopologicalSpace 𝕜 := inferInstance
  letI t₁ : TopologicalSpace E := ⨅ i, induced (f i) t𝕜
  letI t₂ (s : Finset ι) : TopologicalSpace E := ⨅ i : s, induced (f i) t𝕜
  suffices
      Continuous[t₁, t𝕜] φ ↔ ∃ s : Finset ι, Continuous[t₂ s, t𝕜] φ by
    simp only [Submodule.span_range_eq_iSup, this, ← mem_span_iff_continuous_of_finite,
      iSup_subtype]
    rw [Submodule.mem_iSup_iff_exists_finset]
  have t₁_group : @IsTopologicalAddGroup E t₁ _ :=
    topologicalAddGroup_iInf fun _ ↦ topologicalAddGroup_induced _
  have t₂_group (s : Finset ι) : @IsTopologicalAddGroup E (t₂ s) _ :=
    topologicalAddGroup_iInf fun _ ↦ topologicalAddGroup_induced _
  have t₁_smul : @ContinuousSMul 𝕜 E _ _ t₁ :=
    continuousSMul_iInf fun _ ↦ continuousSMul_induced _
  have t₂_smul (s : Finset ι) : @ContinuousSMul 𝕜 E _ _ (t₂ s) :=
    continuousSMul_iInf fun _ ↦ continuousSMul_induced _
  simp only [Seminorm.continuous_iff_continuous_comp (norm_withSeminorms 𝕜 𝕜), forall_const]
  conv in Continuous _ => rw [Seminorm.continuous_iff one_pos, nhds_iInf]
  conv in Continuous _ =>
    rw [let _ := t₂ s; Seminorm.continuous_iff one_pos, nhds_iInf, iInf_subtype]
  rw [Filter.mem_iInf_finite]

end NontriviallyNormedField

end LinearMap
