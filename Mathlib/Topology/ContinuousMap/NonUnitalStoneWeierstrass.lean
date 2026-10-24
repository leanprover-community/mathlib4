/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Unitization
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Topology.ContinuousMap.ZeroAtInftyUnitization
import Mathlib.RingTheory.Adjoin.Basic

/-!
# The non-unital Stone-Weierstrass theorem

The Stone-Weierstrass theorem
(`ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints`) guarantees that a
(star) subalgebra of `C(X, 𝕜)`, for `X` compact and `RCLike 𝕜`, which separates points is dense.
The non-unital version is a statement about non-unital (star) subalgebras of `C₀(X, 𝕜)`, the
continuous functions vanishing at infinity on a not-necessarily-compact space `X`. In particular,
a non-unital (star) subalgebra of `C₀(X, 𝕜)` which separates points and is **nowhere vanishing**
(see `Set.NowhereVanishing`) is dense.

## Main statements

* `ZeroAtInftyContinuousMap.nonUnitalSubalgebra_topologicalClosure_eq_top_of_separatesPoints`:
  a non-unital subalgebra of `C₀(X, ℝ)` which separates points and vanishes nowhere is dense
* `ZeroAtInftyContinuousMap.nonUnitalStarSubalgebra_topologicalClosure_eq_top_of_separatesPoints`:
  a non-unital star subalgebra of `C₀(X, 𝕜)` which separates points and vanishes nowhere is dense

## Sketch

We deduce these from the unital versions by passing to the one-point compactification. There
are natural maps `ZeroAtInftyContinuousMap.toOnePoint : C₀(X, R) → C(OnePoint X, R)` sending
`f : C₀(X, R)` to the extension to `OnePoint X` that takes the value `f ∞ = 0`, and in the reverse
direction `ContinuousMap.toZeroAtInfty : C(OnePoint X, R) → C₀(X, R)` sending `f : C(OnePoint X, R)`
to the restriction `fun x : X ↦ f ↑x - f ∞`. The former is a non-unital algebra homomorphism, and
the latter is a continuous linear map (Lipschitz with constant `2`) which maps all the constant
functions to zero. Given a subalgebra `S` of `C₀(X, R)` which is nowhere vanishing and separates
points, the (non-unital) subalgebra `S' := map toOnePoint S` also separates points so the (unital)
subalgebra `adjoin R S'` also separates points, and by the unital version of Stone–Weierstrass
is dense in `C(OnePoint X, R)`. As a submodule, the `adjoin R S' = R ∙ 1 ⊔ S'`. Mapping this
back to `C₀(X, R)` we find that `toZeroAtInfty (adjoin R S') = ⊥ ⊔ toZeroAtInfty S' = S`
since `f.toOnePoint.toZeroAtInfty = f` for all `f : C₀(X, R)`. Since `toZeroAtInfty` is a continuous
surjection, `S` must be dense because `adjoin R S'` is dense.
-/

public section

open Filter Topology OnePoint ZeroAtInfty ZeroAtInftyContinuousMap ContinuousMap

variable {X 𝕜 : Type*} [TopologicalSpace X] [R1Space X] [RCLike 𝕜]

section StoneWeierstrass

/-- A non-unital subalgebra of `C₀(X, 𝕜)` which separates points and vanishes nowhere also
separates points in `C(OnePoint X, 𝕜)` under `ZeroAtInftyContinuousMap.toOnePoint` -/
theorem NonUnitalSubalgebra.SeparatesPoints.map_toOnePoint
    {S : NonUnitalSubalgebra 𝕜 C₀(X, 𝕜)} (hS : S.SeparatesPoints)
    (hS₀ : (S : Set (C₀(X, 𝕜))).NowhereVanishing) :
    (map (toOnePointNonUnitalAlgHom X 𝕜 𝕜) S).SeparatesPoints := by
  rintro y₁ y₂ hy
  wlog! hy₁ : y₁ ≠ ∞
  · simpa [ne_comm] using this hS hS₀ hy.symm (by grind)
  lift y₁ to X using hy₁
  cases y₂ using OnePoint.rec with
  | infty =>
    obtain ⟨f, hf, hfy⟩ := hS₀ y₁
    exact ⟨_, ⟨f.toOnePoint, ⟨f, hf, rfl⟩, rfl⟩, by simpa⟩
  | coe x =>
    obtain ⟨_, ⟨f, hf, rfl⟩, hfy⟩ := hS (by simpa using hy)
    exact ⟨_, ⟨f.toOnePoint, ⟨f, hf, rfl⟩, rfl⟩, by simpa⟩

/-- A non-unital star subalgebra of `C₀(X, 𝕜)` which separates points and vanishes nowhere also
separates points in `C(OnePoint X, 𝕜)` under `ZeroAtInftyContinuousMap.toOnePoint` -/
theorem NonUnitalStarSubalgebra.SeparatesPoints.map_toOnePoint
    {S : NonUnitalStarSubalgebra 𝕜 C₀(X, 𝕜)} (hS : S.SeparatesPoints)
    (hS₀ : (S : Set C₀(X, 𝕜)).NowhereVanishing) :
    (map (toOnePointNonUnitalStarAlgHom X 𝕜 𝕜) S).SeparatesPoints :=
  NonUnitalSubalgebra.SeparatesPoints.map_toOnePoint (S := S.toNonUnitalSubalgebra) hS hS₀

open Algebra NonUnitalSubalgebra Submodule in
/-- A non-unital subalgebra of `C₀(X, 𝕜)` whose (unital) adjoin in  `C(OnePoint X, 𝕜)` (under
`ZeroAtInftyContinuousMap.toOnePoint`) is dense is itself dense. -/
private theorem NonUnitalSubalgebra.topologicalClosure_eq_top_of_adjoin_map_toOnePoint
    {S : NonUnitalSubalgebra 𝕜 C₀(X, 𝕜)}
    (h : letI S' := map (toOnePointNonUnitalAlgHom X 𝕜 𝕜) S;
      (adjoin 𝕜 (S' : Set C(OnePoint X, 𝕜))) |>.topologicalClosure = ⊤) :
    S.topologicalClosure = ⊤ := by
  have := congr($(h.symm).toSubmodule.map (toZeroAtInftyContinuousLinearMap X 𝕜 𝕜).toLinearMap)
  rw [Algebra.top_toSubmodule, Submodule.map_top,
    LinearMap.range_eq_top_of_surjective _ (by simp)] at this
  apply toSubmodule_injective
  grw [NonUnitalAlgebra.top_toSubmodule, _root_.eq_top_iff, this,
    Subalgebra.toSubmodule_topologicalClosure, adjoin_nonUnitalSubalgebra_eq_span,
    Submodule.topologicalClosure_map]
  rw [Submodule.map_sup, toSubmodule_topologicalClosure, map_span]
  simp only [ContinuousLinearMap.coe_coe, coe_toZeroAtInftyContinuousLinearMap,
    Set.image_singleton, toZeroAtInfty_one, span_zero_singleton, bot_le,
    sup_of_le_right, map_toSubmodule, ← Submodule.map_comp]
  gcongr
  rintro - ⟨f, hf, rfl⟩
  simpa

open Algebra in
/-- The **Stone-Weierstrass theorem (non-unital)**: a non-unital subalgebra of `C₀(X, ℝ)` which
separates points and vanishes nowhere is dense. -/
theorem ZeroAtInftyContinuousMap.nonUnitalSubalgebra_topologicalClosure_eq_top
    (S : NonUnitalSubalgebra ℝ C₀(X, ℝ)) (hS : S.SeparatesPoints)
    (hS₀ : (S : Set C₀(X, ℝ)).NowhereVanishing) :
    S.topologicalClosure = ⊤ := by
  set S' := S.map (toOnePointNonUnitalAlgHom X ℝ ℝ)
  have hle : S' ≤ (adjoin ℝ (S' : Set C(OnePoint X, ℝ))).toNonUnitalSubalgebra :=
    fun _ hx ↦ subset_adjoin hx
  have hsep := (hS.map_toOnePoint hS₀).mono hle
  exact S.topologicalClosure_eq_top_of_adjoin_map_toOnePoint
    (subalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep)

open StarAlgebra StarSubalgebra NonUnitalStarSubalgebra in
/-- The **Stone-Weierstrass theorem (non-unital)**, `RCLike` version: a non-unital star subalgebra
of `C₀(X, 𝕜)` which separates points and vanishes nowhere is dense. -/
theorem ZeroAtInftyContinuousMap.nonUnitalStarSubalgebra_topologicalClosure_eq_top
    (S : NonUnitalStarSubalgebra 𝕜 C₀(X, 𝕜)) (hS : S.SeparatesPoints)
    (hS₀ : (S : Set C₀(X, 𝕜)).NowhereVanishing) :
    S.topologicalClosure = ⊤ := by
  set S' := S.map (toOnePointNonUnitalStarAlgHom X 𝕜 𝕜)
  have hle : S' ≤ (adjoin 𝕜 (S' : Set C(OnePoint X, 𝕜))).toNonUnitalStarSubalgebra :=
    fun _ hx ↦ subset_adjoin 𝕜 _ hx
  have hsep := hS.map_toOnePoint hS₀ |>.mono hle
  have := congr($(starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep).toSubalgebra)
  apply toNonUnitalSubalgebra_injective
  simp only [top_toSubalgebra, toSubalgebra_topologicalClosure, adjoin_toSubalgebra,
    StarMemClass.star_coe_eq, Set.union_self] at this
  simpa only [NonUnitalStarAlgebra.top_toNonUnitalSubalgebra,
    toNonUnitalSubalgebra_topologicalClosure]
    using NonUnitalSubalgebra.topologicalClosure_eq_top_of_adjoin_map_toOnePoint this

end StoneWeierstrass
