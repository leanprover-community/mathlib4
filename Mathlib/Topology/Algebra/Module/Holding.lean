/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.Span
import Mathlib.Topology.Algebra.Module.WeakBilin

/-!
# Holding file

A holding file whilst I try moving stuff around. Come up with a better name once we know what goes
in here.

-/

open Topology TopologicalSpace

section TopologicalRing

variable {ι 𝕜 E F : Type*}

variable [Finite ι] [Field 𝕜] [t𝕜 : TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [T0Space 𝕜]

/- A linear functional `φ` can be expressed as a linear combination of linear functionals `f₁,…,fₙ`
if and only if `φ` is continuous with respect to the topology induced by `f₁,…,fₙ`. See
`LinearMap.mem_span_iff_continuous` for a result about arbitrary collections of linear functionals.
-/
theorem mem_span_iff_continuous_of_finite {f : ι → E →ₗ[𝕜] 𝕜} (φ : E →ₗ[𝕜] 𝕜) :
    φ ∈ Submodule.span 𝕜 (Set.range f) ↔ Continuous[⨅ i, induced (f i) t𝕜, t𝕜] φ := by
  let _ := ⨅ i, induced (f i) t𝕜
  constructor
  · exact Submodule.span_induction
      (Set.forall_mem_range.mpr fun i ↦ continuous_iInf_dom continuous_induced_dom) continuous_zero
      (fun _ _ _ _ ↦ .add) (fun c _ _ h ↦ h.const_smul c)
  · intro φ_cont
    refine mem_span_of_iInf_ker_le_ker fun x hx ↦ ?_
    simp_rw [Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
    have : Inseparable x 0 := by
      -- Maybe missing lemmas about `Inseparable`?
      simp_rw [Inseparable, nhds_iInf, nhds_induced, hx, map_zero]
    simpa only [map_zero] using (this.map φ_cont).eq

end TopologicalRing
