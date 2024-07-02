/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Topology.ContinuousFunction.Bounded
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Sets.Compacts
import Mathlib.Analysis.Normed.Group.InfiniteSum

#align_import topology.continuous_function.compact from "leanprover-community/mathlib"@"d3af0609f6db8691dffdc3e1fb7feb7da72698f2"

/-!
# Continuous functions on a compact space

Continuous functions `C(α, β)` from a compact space `α` to a metric space `β`
are automatically bounded, and so acquire various structures inherited from `α →ᵇ β`.

This file transfers these structures, and restates some lemmas
characterising these structures.

If you need a lemma which is proved about `α →ᵇ β` but not for `C(α, β)` when `α` is compact,
you should restate it here. You can also use
`ContinuousMap.equivBoundedOfCompact` to move functions back and forth.

-/

noncomputable section

open scoped Classical
open Topology NNReal BoundedContinuousFunction

open Set Filter Metric

open BoundedContinuousFunction

namespace ContinuousMap

variable {α β E : Type*} [TopologicalSpace α] [CompactSpace α] [MetricSpace β]
  [NormedAddCommGroup E]

section

variable (α β)

/-- When `α` is compact, the bounded continuous maps `α →ᵇ β` are
equivalent to `C(α, β)`.
-/
@[simps (config := .asFn)]
def equivBoundedOfCompact : C(α, β) ≃ (α →ᵇ β) :=
  ⟨mkOfCompact, BoundedContinuousFunction.toContinuousMap, fun f => by
    ext
    rfl, fun f => by
    ext
    rfl⟩
#align continuous_map.equiv_bounded_of_compact ContinuousMap.equivBoundedOfCompact

theorem uniformInducing_equivBoundedOfCompact : UniformInducing (equivBoundedOfCompact α β) :=
  UniformInducing.mk'
    (by
      simp only [hasBasis_compactConvergenceUniformity.mem_iff, uniformity_basis_dist_le.mem_iff]
      exact fun s =>
        ⟨fun ⟨⟨a, b⟩, ⟨_, ⟨ε, hε, hb⟩⟩, hs⟩ =>
          ⟨{ p | ∀ x, (p.1 x, p.2 x) ∈ b }, ⟨ε, hε, fun _ h x => hb ((dist_le hε.le).mp h x)⟩,
            fun f g h => hs fun x _ => h x⟩,
          fun ⟨_, ⟨ε, hε, ht⟩, hs⟩ =>
          ⟨⟨Set.univ, { p | dist p.1 p.2 ≤ ε }⟩, ⟨isCompact_univ, ⟨ε, hε, fun _ h => h⟩⟩,
            fun ⟨f, g⟩ h => hs _ _ (ht ((dist_le hε.le).mpr fun x => h x (mem_univ x)))⟩⟩)
#align continuous_map.uniform_inducing_equiv_bounded_of_compact ContinuousMap.uniformInducing_equivBoundedOfCompact

theorem uniformEmbedding_equivBoundedOfCompact : UniformEmbedding (equivBoundedOfCompact α β) :=
  { uniformInducing_equivBoundedOfCompact α β with inj := (equivBoundedOfCompact α β).injective }
#align continuous_map.uniform_embedding_equiv_bounded_of_compact ContinuousMap.uniformEmbedding_equivBoundedOfCompact

/-- When `α` is compact, the bounded continuous maps `α →ᵇ 𝕜` are
additively equivalent to `C(α, 𝕜)`.
-/
-- Porting note: the following `simps` received a "maximum recursion depth" error
-- @[simps! (config := .asFn) apply symm_apply]
def addEquivBoundedOfCompact [AddMonoid β] [LipschitzAdd β] : C(α, β) ≃+ (α →ᵇ β) :=
  ({ toContinuousMapAddHom α β, (equivBoundedOfCompact α β).symm with } : (α →ᵇ β) ≃+ C(α, β)).symm
#align continuous_map.add_equiv_bounded_of_compact ContinuousMap.addEquivBoundedOfCompact

-- Porting note: added this `simp` lemma manually because of the `simps` error above
@[simp]
theorem addEquivBoundedOfCompact_symm_apply [AddMonoid β] [LipschitzAdd β] :
    ⇑((addEquivBoundedOfCompact α β).symm) = toContinuousMapAddHom α β :=
  rfl

-- Porting note: added this `simp` lemma manually because of the `simps` error above
@[simp]
theorem addEquivBoundedOfCompact_apply [AddMonoid β] [LipschitzAdd β] :
    ⇑(addEquivBoundedOfCompact α β) = mkOfCompact :=
  rfl

instance metricSpace : MetricSpace C(α, β) :=
  (uniformEmbedding_equivBoundedOfCompact α β).comapMetricSpace _
#align continuous_map.metric_space ContinuousMap.metricSpace

/-- When `α` is compact, and `β` is a metric space, the bounded continuous maps `α →ᵇ β` are
isometric to `C(α, β)`.
-/
@[simps! (config := .asFn) toEquiv apply symm_apply]
def isometryEquivBoundedOfCompact : C(α, β) ≃ᵢ (α →ᵇ β) where
  isometry_toFun _ _ := rfl
  toEquiv := equivBoundedOfCompact α β
#align continuous_map.isometry_equiv_bounded_of_compact ContinuousMap.isometryEquivBoundedOfCompact

end

@[simp]
theorem _root_.BoundedContinuousFunction.dist_mkOfCompact (f g : C(α, β)) :
    dist (mkOfCompact f) (mkOfCompact g) = dist f g :=
  rfl
#align bounded_continuous_function.dist_mk_of_compact BoundedContinuousFunction.dist_mkOfCompact

@[simp]
theorem _root_.BoundedContinuousFunction.dist_toContinuousMap (f g : α →ᵇ β) :
    dist f.toContinuousMap g.toContinuousMap = dist f g :=
  rfl
#align bounded_continuous_function.dist_to_continuous_map BoundedContinuousFunction.dist_toContinuousMap

open BoundedContinuousFunction

section

variable {f g : C(α, β)} {C : ℝ}

/-- The pointwise distance is controlled by the distance between functions, by definition. -/
theorem dist_apply_le_dist (x : α) : dist (f x) (g x) ≤ dist f g := by
  simp only [← dist_mkOfCompact, dist_coe_le_dist, ← mkOfCompact_apply]
#align continuous_map.dist_apply_le_dist ContinuousMap.dist_apply_le_dist

/-- The distance between two functions is controlled by the supremum of the pointwise distances. -/
theorem dist_le (C0 : (0 : ℝ) ≤ C) : dist f g ≤ C ↔ ∀ x : α, dist (f x) (g x) ≤ C := by
  simp only [← dist_mkOfCompact, BoundedContinuousFunction.dist_le C0, mkOfCompact_apply]
#align continuous_map.dist_le ContinuousMap.dist_le

theorem dist_le_iff_of_nonempty [Nonempty α] : dist f g ≤ C ↔ ∀ x, dist (f x) (g x) ≤ C := by
  simp only [← dist_mkOfCompact, BoundedContinuousFunction.dist_le_iff_of_nonempty,
    mkOfCompact_apply]
#align continuous_map.dist_le_iff_of_nonempty ContinuousMap.dist_le_iff_of_nonempty

theorem dist_lt_iff_of_nonempty [Nonempty α] : dist f g < C ↔ ∀ x : α, dist (f x) (g x) < C := by
  simp only [← dist_mkOfCompact, dist_lt_iff_of_nonempty_compact, mkOfCompact_apply]
#align continuous_map.dist_lt_iff_of_nonempty ContinuousMap.dist_lt_iff_of_nonempty

theorem dist_lt_of_nonempty [Nonempty α] (w : ∀ x : α, dist (f x) (g x) < C) : dist f g < C :=
  dist_lt_iff_of_nonempty.2 w
#align continuous_map.dist_lt_of_nonempty ContinuousMap.dist_lt_of_nonempty

theorem dist_lt_iff (C0 : (0 : ℝ) < C) : dist f g < C ↔ ∀ x : α, dist (f x) (g x) < C := by
  rw [← dist_mkOfCompact, dist_lt_iff_of_compact C0]
  simp only [mkOfCompact_apply]
#align continuous_map.dist_lt_iff ContinuousMap.dist_lt_iff

end

instance [CompleteSpace β] : CompleteSpace C(α, β) :=
  (isometryEquivBoundedOfCompact α β).completeSpace

-- TODO at some point we will need lemmas characterising this norm!
-- At the moment the only way to reason about it is to transfer `f : C(α,E)` back to `α →ᵇ E`.
instance : Norm C(α, E) where norm x := dist x 0

@[simp]
theorem _root_.BoundedContinuousFunction.norm_mkOfCompact (f : C(α, E)) : ‖mkOfCompact f‖ = ‖f‖ :=
  rfl
#align bounded_continuous_function.norm_mk_of_compact BoundedContinuousFunction.norm_mkOfCompact

@[simp]
theorem _root_.BoundedContinuousFunction.norm_toContinuousMap_eq (f : α →ᵇ E) :
    ‖f.toContinuousMap‖ = ‖f‖ :=
  rfl
#align bounded_continuous_function.norm_to_continuous_map_eq BoundedContinuousFunction.norm_toContinuousMap_eq

open BoundedContinuousFunction

instance : NormedAddCommGroup C(α, E) :=
  { ContinuousMap.metricSpace _ _,
    ContinuousMap.instAddCommGroupContinuousMap with
    dist_eq := fun x y => by
      rw [← norm_mkOfCompact, ← dist_mkOfCompact, dist_eq_norm, mkOfCompact_sub]
    dist := dist
    norm := norm }

instance [Nonempty α] [One E] [NormOneClass E] : NormOneClass C(α, E) where
  norm_one := by simp only [← norm_mkOfCompact, mkOfCompact_one, norm_one]

section

variable (f : C(α, E))

-- The corresponding lemmas for `BoundedContinuousFunction` are stated with `{f}`,
-- and so can not be used in dot notation.
theorem norm_coe_le_norm (x : α) : ‖f x‖ ≤ ‖f‖ :=
  (mkOfCompact f).norm_coe_le_norm x
#align continuous_map.norm_coe_le_norm ContinuousMap.norm_coe_le_norm

/-- Distance between the images of any two points is at most twice the norm of the function. -/
theorem dist_le_two_norm (x y : α) : dist (f x) (f y) ≤ 2 * ‖f‖ :=
  (mkOfCompact f).dist_le_two_norm x y
#align continuous_map.dist_le_two_norm ContinuousMap.dist_le_two_norm

/-- The norm of a function is controlled by the supremum of the pointwise norms. -/
theorem norm_le {C : ℝ} (C0 : (0 : ℝ) ≤ C) : ‖f‖ ≤ C ↔ ∀ x : α, ‖f x‖ ≤ C :=
  @BoundedContinuousFunction.norm_le _ _ _ _ (mkOfCompact f) _ C0
#align continuous_map.norm_le ContinuousMap.norm_le

theorem norm_le_of_nonempty [Nonempty α] {M : ℝ} : ‖f‖ ≤ M ↔ ∀ x, ‖f x‖ ≤ M :=
  @BoundedContinuousFunction.norm_le_of_nonempty _ _ _ _ _ (mkOfCompact f) _
#align continuous_map.norm_le_of_nonempty ContinuousMap.norm_le_of_nonempty

theorem norm_lt_iff {M : ℝ} (M0 : 0 < M) : ‖f‖ < M ↔ ∀ x, ‖f x‖ < M :=
  @BoundedContinuousFunction.norm_lt_iff_of_compact _ _ _ _ _ (mkOfCompact f) _ M0
#align continuous_map.norm_lt_iff ContinuousMap.norm_lt_iff

theorem nnnorm_lt_iff {M : ℝ≥0} (M0 : 0 < M) : ‖f‖₊ < M ↔ ∀ x : α, ‖f x‖₊ < M :=
  f.norm_lt_iff M0
#align continuous_map.nnnorm_lt_iff ContinuousMap.nnnorm_lt_iff

theorem norm_lt_iff_of_nonempty [Nonempty α] {M : ℝ} : ‖f‖ < M ↔ ∀ x, ‖f x‖ < M :=
  @BoundedContinuousFunction.norm_lt_iff_of_nonempty_compact _ _ _ _ _ _ (mkOfCompact f) _
#align continuous_map.norm_lt_iff_of_nonempty ContinuousMap.norm_lt_iff_of_nonempty

theorem nnnorm_lt_iff_of_nonempty [Nonempty α] {M : ℝ≥0} : ‖f‖₊ < M ↔ ∀ x, ‖f x‖₊ < M :=
  f.norm_lt_iff_of_nonempty
#align continuous_map.nnnorm_lt_iff_of_nonempty ContinuousMap.nnnorm_lt_iff_of_nonempty

theorem apply_le_norm (f : C(α, ℝ)) (x : α) : f x ≤ ‖f‖ :=
  le_trans (le_abs.mpr (Or.inl (le_refl (f x)))) (f.norm_coe_le_norm x)
#align continuous_map.apply_le_norm ContinuousMap.apply_le_norm

theorem neg_norm_le_apply (f : C(α, ℝ)) (x : α) : -‖f‖ ≤ f x :=
  le_trans (neg_le_neg (f.norm_coe_le_norm x)) (neg_le.mp (neg_le_abs (f x)))
#align continuous_map.neg_norm_le_apply ContinuousMap.neg_norm_le_apply

theorem norm_eq_iSup_norm : ‖f‖ = ⨆ x : α, ‖f x‖ :=
  (mkOfCompact f).norm_eq_iSup_norm
#align continuous_map.norm_eq_supr_norm ContinuousMap.norm_eq_iSup_norm

theorem norm_restrict_mono_set {X : Type*} [TopologicalSpace X] (f : C(X, E))
    {K L : TopologicalSpace.Compacts X} (hKL : K ≤ L) : ‖f.restrict K‖ ≤ ‖f.restrict L‖ :=
  (norm_le _ (norm_nonneg _)).mpr fun x => norm_coe_le_norm (f.restrict L) <| Set.inclusion hKL x
#align continuous_map.norm_restrict_mono_set ContinuousMap.norm_restrict_mono_set

end

section

variable {R : Type*} [NormedRing R]

instance : NormedRing C(α, R) :=
  { (inferInstance : NormedAddCommGroup C(α, R)), ContinuousMap.instRing with
    norm_mul := fun f g => norm_mul_le (mkOfCompact f) (mkOfCompact g) }

end

section

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]

instance normedSpace : NormedSpace 𝕜 C(α, E) where
  norm_smul_le c f := (norm_smul_le c (mkOfCompact f) : _)
#align continuous_map.normed_space ContinuousMap.normedSpace

section

variable (α 𝕜 E)

/-- When `α` is compact and `𝕜` is a normed field,
the `𝕜`-algebra of bounded continuous maps `α →ᵇ β` is
`𝕜`-linearly isometric to `C(α, β)`.
-/
def linearIsometryBoundedOfCompact : C(α, E) ≃ₗᵢ[𝕜] α →ᵇ E :=
  { addEquivBoundedOfCompact α E with
    map_smul' := fun c f => by
      ext
      norm_cast
    norm_map' := fun f => rfl }
#align continuous_map.linear_isometry_bounded_of_compact ContinuousMap.linearIsometryBoundedOfCompact

variable {α E}

-- to match `BoundedContinuousFunction.evalCLM`
/-- The evaluation at a point, as a continuous linear map from `C(α, 𝕜)` to `𝕜`. -/
def evalCLM (x : α) : C(α, E) →L[𝕜] E :=
  (BoundedContinuousFunction.evalCLM 𝕜 x).comp
    (linearIsometryBoundedOfCompact α E 𝕜).toLinearIsometry.toContinuousLinearMap
#align continuous_map.eval_clm ContinuousMap.evalCLM

end

-- this lemma and the next are the analogues of those autogenerated by `@[simps]` for
-- `equivBoundedOfCompact`, `addEquivBoundedOfCompact`
@[simp]
theorem linearIsometryBoundedOfCompact_symm_apply (f : α →ᵇ E) :
    (linearIsometryBoundedOfCompact α E 𝕜).symm f = f.toContinuousMap :=
  rfl
#align continuous_map.linear_isometry_bounded_of_compact_symm_apply ContinuousMap.linearIsometryBoundedOfCompact_symm_apply

@[simp]
theorem linearIsometryBoundedOfCompact_apply_apply (f : C(α, E)) (a : α) :
    (linearIsometryBoundedOfCompact α E 𝕜 f) a = f a :=
  rfl
#align continuous_map.linear_isometry_bounded_of_compact_apply_apply ContinuousMap.linearIsometryBoundedOfCompact_apply_apply

@[simp]
theorem linearIsometryBoundedOfCompact_toIsometryEquiv :
    (linearIsometryBoundedOfCompact α E 𝕜).toIsometryEquiv = isometryEquivBoundedOfCompact α E :=
  rfl
#align continuous_map.linear_isometry_bounded_of_compact_to_isometry_equiv ContinuousMap.linearIsometryBoundedOfCompact_toIsometryEquiv

@[simp] -- Porting note: adjusted LHS because `simpNF` complained it simplified.
theorem linearIsometryBoundedOfCompact_toAddEquiv :
    ((linearIsometryBoundedOfCompact α E 𝕜).toLinearEquiv : C(α, E) ≃+ (α →ᵇ E)) =
      addEquivBoundedOfCompact α E :=
  rfl
#align continuous_map.linear_isometry_bounded_of_compact_to_add_equiv ContinuousMap.linearIsometryBoundedOfCompact_toAddEquiv

@[simp]
theorem linearIsometryBoundedOfCompact_of_compact_toEquiv :
    (linearIsometryBoundedOfCompact α E 𝕜).toLinearEquiv.toEquiv = equivBoundedOfCompact α E :=
  rfl
#align continuous_map.linear_isometry_bounded_of_compact_of_compact_to_equiv ContinuousMap.linearIsometryBoundedOfCompact_of_compact_toEquiv

end

section

variable {𝕜 : Type*} {γ : Type*} [NormedField 𝕜] [NormedRing γ] [NormedAlgebra 𝕜 γ]

instance : NormedAlgebra 𝕜 C(α, γ) :=
  { ContinuousMap.normedSpace, ContinuousMap.algebra with }

end

end ContinuousMap

namespace ContinuousMap

section UniformContinuity

variable {α β : Type*}
variable [MetricSpace α] [CompactSpace α] [MetricSpace β]

/-!
We now set up some declarations making it convenient to use uniform continuity.
-/


theorem uniform_continuity (f : C(α, β)) (ε : ℝ) (h : 0 < ε) :
    ∃ δ > 0, ∀ {x y}, dist x y < δ → dist (f x) (f y) < ε :=
  Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous f.continuous) ε h
#align continuous_map.uniform_continuity ContinuousMap.uniform_continuity

-- This definition allows us to separate the choice of some `δ`,
-- and the corresponding use of `dist a b < δ → dist (f a) (f b) < ε`,
-- even across different declarations.
/-- An arbitrarily chosen modulus of uniform continuity for a given function `f` and `ε > 0`. -/
def modulus (f : C(α, β)) (ε : ℝ) (h : 0 < ε) : ℝ :=
  Classical.choose (uniform_continuity f ε h)
#align continuous_map.modulus ContinuousMap.modulus

theorem modulus_pos (f : C(α, β)) {ε : ℝ} {h : 0 < ε} : 0 < f.modulus ε h :=
  (Classical.choose_spec (uniform_continuity f ε h)).1
#align continuous_map.modulus_pos ContinuousMap.modulus_pos

theorem dist_lt_of_dist_lt_modulus (f : C(α, β)) (ε : ℝ) (h : 0 < ε) {a b : α}
    (w : dist a b < f.modulus ε h) : dist (f a) (f b) < ε :=
  (Classical.choose_spec (uniform_continuity f ε h)).2 w
#align continuous_map.dist_lt_of_dist_lt_modulus ContinuousMap.dist_lt_of_dist_lt_modulus

end UniformContinuity

end ContinuousMap

section CompLeft

variable (X : Type*) {𝕜 β γ : Type*} [TopologicalSpace X] [CompactSpace X]
  [NontriviallyNormedField 𝕜]

variable [NormedAddCommGroup β] [NormedSpace 𝕜 β] [NormedAddCommGroup γ] [NormedSpace 𝕜 γ]

open ContinuousMap

/-- Postcomposition of continuous functions into a normed module by a continuous linear map is a
continuous linear map.
Transferred version of `ContinuousLinearMap.compLeftContinuousBounded`,
upgraded version of `ContinuousLinearMap.compLeftContinuous`,
similar to `LinearMap.compLeft`. -/
protected def ContinuousLinearMap.compLeftContinuousCompact (g : β →L[𝕜] γ) :
    C(X, β) →L[𝕜] C(X, γ) :=
  (linearIsometryBoundedOfCompact X γ 𝕜).symm.toLinearIsometry.toContinuousLinearMap.comp <|
    (g.compLeftContinuousBounded X).comp <|
      (linearIsometryBoundedOfCompact X β 𝕜).toLinearIsometry.toContinuousLinearMap
#align continuous_linear_map.comp_left_continuous_compact ContinuousLinearMap.compLeftContinuousCompact

@[simp]
theorem ContinuousLinearMap.toLinear_compLeftContinuousCompact (g : β →L[𝕜] γ) :
    (g.compLeftContinuousCompact X : C(X, β) →ₗ[𝕜] C(X, γ)) = g.compLeftContinuous 𝕜 X := by
  ext f
  rfl
#align continuous_linear_map.to_linear_comp_left_continuous_compact ContinuousLinearMap.toLinear_compLeftContinuousCompact

@[simp]
theorem ContinuousLinearMap.compLeftContinuousCompact_apply (g : β →L[𝕜] γ) (f : C(X, β)) (x : X) :
    g.compLeftContinuousCompact X f x = g (f x) :=
  rfl
#align continuous_linear_map.comp_left_continuous_compact_apply ContinuousLinearMap.compLeftContinuousCompact_apply

end CompLeft

namespace ContinuousMap

/-!
We now setup variations on `compRight* f`, where `f : C(X, Y)`
(that is, precomposition by a continuous map),
as a morphism `C(Y, T) → C(X, T)`, respecting various types of structure.

In particular:
* `compRightContinuousMap`, the bundled continuous map (for this we need `X Y` compact).
* `compRightHomeomorph`, when we precompose by a homeomorphism.
* `compRightAlgHom`, when `T = R` is a topological ring.
-/


section CompRight

/-- Precomposition by a continuous map is itself a continuous map between spaces of continuous maps.
-/
def compRightContinuousMap {X Y : Type*} (T : Type*) [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [MetricSpace T] (f : C(X, Y)) : C(C(Y, T), C(X, T)) where
  toFun g := g.comp f
  continuous_toFun := by
    refine Metric.continuous_iff.mpr ?_
    intro g ε ε_pos
    refine ⟨ε, ε_pos, fun g' h => ?_⟩
    rw [ContinuousMap.dist_lt_iff ε_pos] at h ⊢
    exact fun x => h (f x)
#align continuous_map.comp_right_continuous_map ContinuousMap.compRightContinuousMap

@[simp]
theorem compRightContinuousMap_apply {X Y : Type*} (T : Type*) [TopologicalSpace X]
    [CompactSpace X] [TopologicalSpace Y] [CompactSpace Y] [MetricSpace T] (f : C(X, Y))
    (g : C(Y, T)) : (compRightContinuousMap T f) g = g.comp f :=
  rfl
#align continuous_map.comp_right_continuous_map_apply ContinuousMap.compRightContinuousMap_apply

/-- Precomposition by a homeomorphism is itself a homeomorphism between spaces of continuous maps.
-/
def compRightHomeomorph {X Y : Type*} (T : Type*) [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [MetricSpace T] (f : X ≃ₜ Y) : C(Y, T) ≃ₜ C(X, T) where
  toFun := compRightContinuousMap T f.toContinuousMap
  continuous_toFun := by continuity
  invFun := compRightContinuousMap T f.symm.toContinuousMap
  continuous_invFun := by continuity
  left_inv g := ext fun _ => congr_arg g (f.apply_symm_apply _)
  right_inv g := ext fun _ => congr_arg g (f.symm_apply_apply _)
#align continuous_map.comp_right_homeomorph ContinuousMap.compRightHomeomorph

theorem compRightAlgHom_continuous {X Y : Type*} (R A : Type*) [TopologicalSpace X]
    [CompactSpace X] [TopologicalSpace Y] [CompactSpace Y] [CommSemiring R] [Semiring A]
    [MetricSpace A] [TopologicalSemiring A] [Algebra R A] (f : C(X, Y)) :
    Continuous (compRightAlgHom R A f) :=
  map_continuous (compRightContinuousMap A f)
#align continuous_map.comp_right_alg_hom_continuous ContinuousMap.compRightAlgHom_continuous

end CompRight

section LocalNormalConvergence

/-! ### Local normal convergence

A sum of continuous functions (on a locally compact space) is "locally normally convergent" if the
sum of its sup-norms on any compact subset is summable. This implies convergence in the topology
of `C(X, E)` (i.e. locally uniform convergence). -/


open TopologicalSpace

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

theorem summable_of_locally_summable_norm {ι : Type*} {F : ι → C(X, E)}
    (hF : ∀ K : Compacts X, Summable fun i => ‖(F i).restrict K‖) : Summable F := by
  refine (ContinuousMap.exists_tendsto_compactOpen_iff_forall _).2 fun K hK => ?_
  lift K to Compacts X using hK
  have A : ∀ s : Finset ι, restrict (↑K) (∑ i ∈ s, F i) = ∑ i ∈ s, restrict K (F i) := by
    intro s
    ext1 x
    simp
    -- This used to be the end of the proof before leanprover/lean4#2644
    erw [restrict_apply, restrict_apply, restrict_apply, restrict_apply]
    simp? says simp only [coe_sum, Finset.sum_apply]
    congr!
  simpa only [HasSum, A] using (hF K).of_norm
#align continuous_map.summable_of_locally_summable_norm ContinuousMap.summable_of_locally_summable_norm

end LocalNormalConvergence

/-!
### Star structures

In this section, if `β` is a normed ⋆-group, then so is the space of
continuous functions from `α` to `β`, by using the star operation pointwise.

Furthermore, if `α` is compact and `β` is a C⋆-ring, then `C(α, β)` is a C⋆-ring. -/


section NormedSpace

variable {α : Type*} {β : Type*}
variable [TopologicalSpace α] [NormedAddCommGroup β] [StarAddMonoid β] [NormedStarGroup β]

theorem _root_.BoundedContinuousFunction.mkOfCompact_star [CompactSpace α] (f : C(α, β)) :
    mkOfCompact (star f) = star (mkOfCompact f) :=
  rfl
#align bounded_continuous_function.mk_of_compact_star BoundedContinuousFunction.mkOfCompact_star

instance [CompactSpace α] : NormedStarGroup C(α, β) where
  norm_star f := by
    rw [← BoundedContinuousFunction.norm_mkOfCompact, BoundedContinuousFunction.mkOfCompact_star,
      norm_star, BoundedContinuousFunction.norm_mkOfCompact]

end NormedSpace

section CstarRing

variable {α : Type*} {β : Type*}
variable [TopologicalSpace α] [NormedRing β] [StarRing β]

instance [CompactSpace α] [CstarRing β] : CstarRing C(α, β) where
  norm_star_mul_self {f} := by
    refine le_antisymm ?_ ?_
    · rw [← sq, ContinuousMap.norm_le _ (sq_nonneg _)]
      intro x
      simp only [ContinuousMap.coe_mul, coe_star, Pi.mul_apply, Pi.star_apply,
        CstarRing.norm_star_mul_self, ← sq]
      refine sq_le_sq' ?_ ?_
      · linarith [norm_nonneg (f x), norm_nonneg f]
      · exact ContinuousMap.norm_coe_le_norm f x
    · rw [← sq, ← Real.le_sqrt (norm_nonneg _) (norm_nonneg _),
        ContinuousMap.norm_le _ (Real.sqrt_nonneg _)]
      intro x
      rw [Real.le_sqrt (norm_nonneg _) (norm_nonneg _), sq, ← CstarRing.norm_star_mul_self]
      exact ContinuousMap.norm_coe_le_norm (star f * f) x

end CstarRing

end ContinuousMap
