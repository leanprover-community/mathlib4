/-
Copyright © 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Heather Macbeth, Winston Yin
-/
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Analysis.NormedSpace.Units

#align_import geometry.manifold.instances.units_of_normed_algebra from "leanprover-community/mathlib"@"ef901ea68d3bb1dd08f8bc3034ab6b32b2e6ecdf"

/-!
# Units of a normed algebra

We construct the Lie group structure on the group of units of a complete normed `𝕜`-algebra `R`. The
group of units `Rˣ` has a natural smooth manifold structure modelled on `R` given by its embedding
into `R`. Together with the smoothness of the multiplication and inverse of its elements, `Rˣ` forms
a Lie group.

An important special case of this construction is the general linear group.  For a normed space `V`
over a field `𝕜`, the `𝕜`-linear endomorphisms of `V` are a normed `𝕜`-algebra (see
`ContinuousLinearMap.toNormedAlgebra`), so this construction provides a Lie group structure on
its group of units, the general linear group GL(`𝕜`, `V`), as demonstrated by:
```
example {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V] [Nontrivial V] :
  LieGroup 𝓘(𝕜, V →L[𝕜] V) (V →L[𝕜] V)ˣ := by infer_instance
```
-/


noncomputable section

open scoped Manifold

namespace Units

variable {R : Type*} [NormedRing R] [CompleteSpace R]

instance : ChartedSpace R Rˣ :=
  openEmbedding_val.singletonChartedSpace

theorem chartAt_apply {a : Rˣ} {b : Rˣ} : chartAt R a b = b :=
  rfl
#align units.chart_at_apply Units.chartAt_apply

theorem chartAt_source {a : Rˣ} : (chartAt R a).source = Set.univ :=
  rfl
#align units.chart_at_source Units.chartAt_source

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 R]

instance : SmoothManifoldWithCorners 𝓘(𝕜, R) Rˣ :=
  openEmbedding_val.singleton_smoothManifoldWithCorners 𝓘(𝕜, R)

/-- For a complete normed ring `R`, the embedding of the units `Rˣ` into `R` is a smooth map between
manifolds. -/
lemma contMDiff_val {m : WithTop ℕ} : ContMDiff 𝓘(𝕜, R) 𝓘(𝕜, R) m (val : Rˣ → R) :=
  contMDiff_openEmbedding 𝓘(𝕜, R) Units.openEmbedding_val

/-- For any map `f` from a manifold `M` to the units `Rˣ` of a complete normed ring `R`, the
smoothness of `val ∘ f`, where `val : Rˣ → R` is the embedding, implies the smoothness of `f`.

This can be used to show that ring multiplication `Rˣ × Rˣ → Rˣ` and inverse `Rˣ → Rˣ` are
smooth. -/
lemma ContMDiff.of_comp_units_val
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {n : WithTop ℕ} {f : M → Rˣ} (hf : ContMDiff I 𝓘(𝕜, R) n ((val : Rˣ → R) ∘ f)) :
    ContMDiff I 𝓘(𝕜, R) n f :=
  ContMDiff.of_comp_openEmbedding Units.openEmbedding_val hf

/-- The units of a complete normed ring form a Lie group. -/
instance : LieGroup 𝓘(𝕜, R) Rˣ where
  smooth_mul := by
    apply ContMDiff.of_comp_units_val
    have : (val : Rˣ → R) ∘ (fun x : Rˣ × Rˣ => x.1 * x.2) =
      (fun x : R × R => x.1 * x.2) ∘ (fun x : Rˣ × Rˣ => (x.1, x.2)) := by ext; simp
    rw [this]
    have : ContMDiff (𝓘(𝕜, R).prod 𝓘(𝕜, R)) 𝓘(𝕜, R × R) ∞
      (fun x : Rˣ × Rˣ => ((x.1 : R), (x.2 : R))) :=
      (contMDiff_val.comp contMDiff_fst).prod_mk_space (contMDiff_val.comp contMDiff_snd)
    refine' ContMDiff.comp _ this
    rw [contMDiff_iff_contDiff]
    exact contDiff_mul
  smooth_inv := by
    apply ContMDiff.of_comp_units_val
    have : (val : Rˣ → R) ∘ (fun x : Rˣ => x⁻¹) = Ring.inverse ∘ val := by ext; simp
    rw [this, ContMDiff]
    intro x
    refine' ContMDiffAt.comp x _ (contMDiff_val x)
    rw [contMDiffAt_iff_contDiffAt]
    exact contDiffAt_ring_inverse _ _

end Units
