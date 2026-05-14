/-
Copyright (c) 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Heather Macbeth, Winston Yin
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Algebra.Group.Invertible.Basic
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!
# Units of a normed algebra

We construct the Lie group structure on the group of units of a complete normed `𝕜`-algebra `R`. The
group of units `Rˣ` has a natural `C^n` manifold structure modelled on `R` given by its embedding
into `R`. Together with the smoothness of the multiplication and inverse of its elements, `Rˣ` forms
a Lie group.

An important special case of this construction is the general linear group.  For a normed space `V`
over a field `𝕜`, the `𝕜`-linear endomorphisms of `V` are a normed `𝕜`-algebra (see
`ContinuousLinearMap.toNormedAlgebra`), so this construction provides a Lie group structure on
its group of units, the general linear group GL(`𝕜`, `V`), as demonstrated by:
```
example {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V] (n : ℕ∞ω) :
    LieGroup 𝓘(𝕜, V →L[𝕜] V) n (V →L[𝕜] V)ˣ := inferInstance
```

We also prove that if `R` acts smoothly on a manifold, its group of units does as well;
in particular, the general linear group `(V →L[𝕜] V)ˣ` is a Lie group acting smoothly on `V`.
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace Units

variable {R : Type*} [NormedRing R] [CompleteSpace R] {n : ℕ∞ω}

instance : ChartedSpace R Rˣ :=
  isOpenEmbedding_val.singletonChartedSpace

theorem chartAt_apply {a : Rˣ} {b : Rˣ} : chartAt R a b = b :=
  rfl

theorem chartAt_source {a : Rˣ} : (chartAt R a).source = Set.univ :=
  rfl

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 R]
  {H : Type*} [TopologicalSpace H] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

instance : IsManifold 𝓘(𝕜, R) n Rˣ :=
  isOpenEmbedding_val.isManifold_singleton

/-- For a complete normed ring `R`, the embedding of the units `Rˣ` into `R` is a `C^n` map between
manifolds. -/
lemma contMDiff_val : ContMDiff 𝓘(𝕜, R) 𝓘(𝕜, R) n (val : Rˣ → R) :=
  contMDiff_isOpenEmbedding Units.isOpenEmbedding_val

/-- The units of a complete normed ring form a Lie group. -/
instance : LieGroup 𝓘(𝕜, R) n Rˣ where
  contMDiff_mul := by
    apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
    have : (val : Rˣ → R) ∘ (fun x : Rˣ × Rˣ => x.1 * x.2) =
      (fun x : R × R => x.1 * x.2) ∘ (fun x : Rˣ × Rˣ => (x.1, x.2)) := by ext; simp
    rw [this]
    have : ContMDiff (𝓘(𝕜, R).prod 𝓘(𝕜, R)) 𝓘(𝕜, R × R) n
      (fun x : Rˣ × Rˣ => ((x.1 : R), (x.2 : R))) :=
      (contMDiff_val.comp contMDiff_fst).prodMk_space (contMDiff_val.comp contMDiff_snd)
    refine ContMDiff.comp ?_ this
    rw [contMDiff_iff_contDiff]
    exact contDiff_mul
  contMDiff_inv := by
    apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
    have : (val : Rˣ → R) ∘ (fun x : Rˣ => x⁻¹) = Ring.inverse ∘ val := by ext; simp
    rw [this, ContMDiff]
    refine fun x => ContMDiffAt.comp x ?_ (contMDiff_val x)
    rw [contMDiffAt_iff_contDiffAt]
    exact contDiffAt_ringInverse _ _

/-- If a complete normed ring `R` acts continuously differentiably on a manifold `M`, its
submanifold of units does as well. -/
instance contMDiffSMul [MulAction R M] [ContMDiffSMul 𝓘(𝕜, R) I n R M] :
    ContMDiffSMul 𝓘(𝕜, R) I n Rˣ M :=
  MulAction.contMDiffSMul_compHom (f := coeHom R) contMDiff_val

/-- The general linear group `(V →L[𝕜] V)ˣ` of a Banach space `V` is a Lie group. -/
example {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V] (n : ℕ∞ω) :
    LieGroup 𝓘(𝕜, V →L[𝕜] V) n (V →L[𝕜] V)ˣ := inferInstance

/-- The general linear group `(V →L[𝕜] V)ˣ` of a Banach space `V` acts smoothly on `V`. -/
example {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V] (n : ℕ∞ω) :
    ContMDiffSMul 𝓘(𝕜, V →L[𝕜] V) 𝓘(𝕜, V) n (V →L[𝕜] V)ˣ V :=
  inferInstance

end Units
