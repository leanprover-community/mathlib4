/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Continuity of inner product

We show that the inner product is continuous, `continuous_inner`.

## Tags

inner product space, Hilbert space, norm

-/

noncomputable section

open RCLike Real Filter Topology ComplexConjugate Finsupp
open LinearMap renaming BilinForm → BilinForm

variable {𝕜 E F : Type*} [RCLike 𝕜]


section Continuous

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-!
### Continuity of the inner product
-/

/-- When an inner product space `E` over `𝕜` is considered as a real normed space, its inner
product satisfies `IsBoundedBilinearMap`.

In order to state these results, we need a `NormedSpace ℝ E` instance. We will later establish
such an instance by restriction-of-scalars, `InnerProductSpace.rclikeToReal 𝕜 E`, but this
instance may be not definitionally equal to some other “natural” instance. So, we assume
`[NormedSpace ℝ E]`.
-/
theorem _root_.isBoundedBilinearMap_inner [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] :
    IsBoundedBilinearMap ℝ fun p : E × E => ⟪p.1, p.2⟫ :=
  { add_left := inner_add_left
    smul_left := fun r x y => by
      simp only [← algebraMap_smul 𝕜 r x, algebraMap_eq_ofReal, inner_smul_real_left]
    add_right := inner_add_right
    smul_right := fun r x y => by
      simp only [← algebraMap_smul 𝕜 r y, algebraMap_eq_ofReal, inner_smul_real_right]
    bound :=
      ⟨1, zero_lt_one, fun x y => by
        rw [one_mul]
        exact norm_inner_le_norm x y⟩ }

theorem continuous_inner : Continuous fun p : E × E => ⟪p.1, p.2⟫ :=
  letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal 𝕜 E
  letI : IsScalarTower ℝ 𝕜 E := RestrictScalars.isScalarTower _ _ _
  isBoundedBilinearMap_inner.continuous

variable {α : Type*}

theorem Filter.Tendsto.inner {f g : α → E} {l : Filter α} {x y : E} (hf : Tendsto f l (𝓝 x))
    (hg : Tendsto g l (𝓝 y)) : Tendsto (fun t => ⟪f t, g t⟫) l (𝓝 ⟪x, y⟫) :=
  (continuous_inner.tendsto _).comp (hf.prodMk_nhds hg)

variable [TopologicalSpace α] {f g : α → E} {x : α} {s : Set α}

theorem ContinuousWithinAt.inner (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun t => ⟪f t, g t⟫) s x :=
  Filter.Tendsto.inner hf hg

@[fun_prop]
theorem ContinuousAt.inner (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun t => ⟪f t, g t⟫) x :=
  Filter.Tendsto.inner hf hg

@[fun_prop]
theorem ContinuousOn.inner (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun t => ⟪f t, g t⟫) s := fun x hx => (hf x hx).inner (hg x hx)

@[continuity, fun_prop]
theorem Continuous.inner (hf : Continuous f) (hg : Continuous g) : Continuous fun t => ⟪f t, g t⟫ :=
  continuous_iff_continuousAt.2 fun _x => by fun_prop

end Continuous
