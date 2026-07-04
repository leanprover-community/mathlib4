/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.LinearAlgebra.BilinearMap

/-! # Weak topologies on modules

Given a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`, the weak topology on `E` is the coarsest topology
such that for all `y : F` every map `(B · y)` is continuous; equivalently, it is the topology
on `E` induced by the map `(B · · : E → (F → 𝕜))`.

This file defines a `Prop`-valued typeclass `LinearMap.IsWeak` expressing that an existing topology
on `E` is the weak topology. Although this could be passed around explicitly as a hypothesis
`Topology.IsInducing (B · ·)`, given the ubiquity of weak topologies in functional analysis, the
numerous properties that can be deduced because the inducing map `B` is bilinear, the fact that
several theorems (e.g., one version of the bipolar theorem) require this hypothesis, and we can
instantiate this class for several extant types in Mathlib, we choose to make this a typeclass
instead.

Note that establishing `LinearMap.IsWeak` before proving theorems about a particular type can help
prevent abuse of definitional equalities. This because spaces equipped with a weak topology are
frequently type synonyms of some other type `E'`. For example, suppose `E'` is a type (potentially
with some extant topology other than the weak topology) and `B' : E' →ₗ[𝕜] F →ₗ[𝕜] 𝕜` is a
bilinear form. To consider the weak topology on `E'` induced by `B'`, in practice we must create a
type synonym `E` with an instance `TopologicalSpace E := .induced (B' · ·) Pi.topologicalSpace`.
It would then be tempting to create theorems such as:

```lean
example (y : F) : Continuous (fun x : E ↦ B' x y) := sorry
```

However, this statement contains an abuse of the the definitional equality `E := E'` since `x : E`,
but `B'` has domain `E'`. Morever, one might be tempted to say that `B'.IsWeak`, but this is
impossible because the domain of `B'` is `E'`, which is equipped with the incorrect topology.
Instead, what one should do is to first define a new bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` by
composing `B'` with the linear equivalence between `E` and `E'`, and then establish `B.IsWeak`.
If then one proves theorems about `E` using only the `LinearMap.IsWeak` API, then one can have more
confidence that the statements are type correct.

## Main definitions

+ `LinearMap.IsWeak`: a typeclass expressing that the topology on `E` is the weak topology induced
  by the bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`.
+ `LinearMap.IsWeak.eval`: the evaluation map `F →ₗ[𝕜] StrongDual 𝕜 E` sending `y : F` to the
  continuous linear functional `(B · y)`.

## Main results

We prove the following results characterizing the weak topology:

* `LinearMap.IsWeak.continuous_eval`: For any `y : F`, the evaluation mapping `(B · y)` is
  continuous.
* `LinearMap.IsWeak.continuous_of_continuous_eval`: For a mapping to `WeakBilin B` to be continuous,
  it suffices that its compositions with pairing with `B` at all points `y : F` is continuous.
* `LinearMap.IsWeak.tendsto_iff_forall_eval_tendsto`: Convergence in `WeakBilin B` can be
  characterized in terms of convergence of the evaluations at all points `y : F`.

-/

@[expose] public section

open Topology Filter

section Basic

variable {α 𝕜 E F E' F' : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜]
    [AddCommMonoid E] [Module 𝕜 E]
    [AddCommMonoid F] [Module 𝕜 F]

/-- Typeclass expressing that the topology on `E` is the weak topology induced
by the bilinear form `B`. -/
@[mk_iff]
class LinearMap.IsWeak [t : TopologicalSpace E] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : Prop where
  eq_induced : t = .induced (B · ·) Pi.topologicalSpace

variable [inst : TopologicalSpace E] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [hB : B.IsWeak]

namespace LinearMap.IsWeak

instance : B.flip.flip.IsWeak := hB

/-- The coercion `(B · ·) : E → (F → 𝕜)` is continuous. -/
theorem coeFn_continuous : Continuous (B · ·) :=
  hB.eq_induced ▸ continuous_induced_dom

/-- The evaluation map `(B · y) : E → 𝕜` is continuous for each `y : F`. -/
@[fun_prop]
lemma continuous_eval (y : F) : Continuous (B · y) :=
  continuous_pi_iff.mp (coeFn_continuous B) _

/-- A map `f : α → E` is continuous if all the maps `fun a ↦ B (f a) y` are continuous
for each `y : F`. -/
lemma continuous_of_continuous_eval {α : Type*} [TopologicalSpace α]
    {f : α → E} (hf : ∀ y, Continuous (fun x ↦ B (f x) y)) :
    Continuous f :=
  hB.eq_induced ▸ continuous_induced_rng.mpr (continuous_pi_iff.mpr hf)

lemma continuous_iff {α : Type*} [TopologicalSpace α] {f : α → E} :
    Continuous f ↔ ∀ y, Continuous (fun x ↦ B (f x) y) :=
  ⟨fun _ ↦ by fun_prop, hB.continuous_of_continuous_eval⟩

/-- The coercion `(B · ·) : E → (F → 𝕜)` is an embedding. -/
theorem isInducing : IsInducing (B · ·) where
  eq_induced := hB.eq_induced

variable {B} in
/-- The coercion `(B · ·) : E → (F → 𝕜)` is an embedding. -/
theorem isEmbedding (hB_inj : Function.Injective B) :
    IsEmbedding (B · ·) := by
  convert! (LinearMap.coe_injective.comp hB_inj |>.isEmbedding_induced)
  exact hB.eq_induced

variable {B} in
theorem tendsto_iff_forall_eval_tendsto {α : Type*} {l : Filter α} {f : α → E} {x : E}
    (hB_inj : Function.Injective B) :
    Tendsto f l (𝓝 x) ↔ ∀ y, Tendsto (fun i ↦ B (f i) y) l (𝓝 (B x y)) := by
  rw [← tendsto_pi_nhds, (isEmbedding hB_inj).tendsto_nhds_iff, Function.comp_def]

/-- Suppose `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` and `B' : E' →ₗ[𝕜] F' →ₗ[𝕜] 𝕜` are bilinear maps such that
`E ≃L[𝕜] E'` and `F ≃ₗ[𝕜] F'`. If `B.IsWeak`, then so also `B'.IsWeak`. -/
protected theorem congr [AddCommMonoid E'] [Module 𝕜 E']
    [AddCommMonoid F'] [Module 𝕜 F'] [TopologicalSpace E']
    (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (B' : E' →ₗ[𝕜] F' →ₗ[𝕜] 𝕜) (e : E ≃L[𝕜] E') (f : F ≃ₗ[𝕜] F')
    (hBB' : e.toLinearEquiv.arrowCongr (f.arrowCongr (.refl ..)) B = B') [hB : B.IsWeak] :
    B'.IsWeak where
  eq_induced := by
    rw [e.symm.toHomeomorph.induced_eq.symm]
    apply congr(TopologicalSpace.induced e.symm $(hB.eq_induced)).trans
    simp_rw [induced_compose, ← hBB', induced_to_pi]
    rw [f.toEquiv.iInf_congr]
    simp

/-- Map `F` into the topological dual of `E` with the weak topology induced by `F` -/
def eval [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜] : F →ₗ[𝕜] StrongDual 𝕜 E where
  toFun f := ⟨B.flip f, by fun_prop⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

include hB in
/-- Addition in `E` is continuous when `E` is equipped with a `LinearMap.IsWeak` topology. -/
theorem continuousAdd [ContinuousAdd 𝕜] : ContinuousAdd E where
  continuous_add := by
    let t₁ : TopologicalSpace E := .induced (B · ·) Pi.topologicalSpace
    have : B.IsWeak := ⟨rfl⟩
    rw [hB.eq_induced, continuous_induced_rng]
    simp only [Function.comp_def, map_add, add_apply]
    fun_prop

include hB in
/-- Scalar multiplication in `E` is continuous when `E` is equipped with a `LinearMap.IsWeak`
topology. -/
theorem continuousSMul [ContinuousSMul 𝕜 𝕜] : ContinuousSMul 𝕜 E where
  continuous_smul := by
    let t₁ : TopologicalSpace E := .induced (B · ·) Pi.topologicalSpace
    have : B.IsWeak := ⟨rfl⟩
    rw [hB.eq_induced, continuous_induced_rng]
    simp only [Function.comp_def, map_smul, smul_apply]
    fun_prop

/-- `E` is a `IsTopologicalAddGroup` when `E` is equipped with a `LinearMap.IsWeak` topology. -/
theorem isTopologicalAddGroup {𝕜 E F : Type*} [CommRing 𝕜] [TopologicalSpace 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace E]
    [ContinuousAdd 𝕜] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [hB : B.IsWeak] : IsTopologicalAddGroup E where
  toContinuousAdd := continuousAdd B
  continuous_neg := by
    let t₁ : TopologicalSpace E := .induced (B · ·) Pi.topologicalSpace
    have : B.IsWeak := ⟨rfl⟩
    rw [hB.eq_induced, continuous_induced_rng, continuous_pi_iff]
    simp_rw [Function.comp_apply, map_neg, neg_apply, ← map_neg (B _)]
    fun_prop

end LinearMap.IsWeak

end Basic
