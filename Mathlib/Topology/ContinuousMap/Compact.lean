/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Star
public import Mathlib.Topology.ContinuousMap.Star
public import Mathlib.Topology.UniformSpace.Compact
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Sets.Compacts
public import Mathlib.Analysis.Normed.Group.InfiniteSum

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
set_option backward.defeqAttrib.useBackward true

@[expose] public section

noncomputable section

open NNReal BoundedContinuousFunction Set Metric

namespace ContinuousMap

variable {α β E : Type*}
variable [TopologicalSpace α] [CompactSpace α] [PseudoMetricSpace β] [SeminormedAddCommGroup E]

section

variable (α β)

/-- When `α` is compact, the bounded continuous maps `α →ᵇ β` are
equivalent to `C(α, β)`.
-/
@[simps -fullyApplied]
def equivBoundedOfCompact : C(α, β) ≃ (α →ᵇ β) :=
  ⟨mkOfCompact, BoundedContinuousFunction.toContinuousMap, fun f => by
    ext
    rfl, fun f => by
    ext
    rfl⟩

theorem isUniformInducing_equivBoundedOfCompact : IsUniformInducing (equivBoundedOfCompact α β) :=
  IsUniformInducing.mk'
    (by
      simp only [hasBasis_compactConvergenceUniformity.mem_iff, uniformity_basis_dist_le.mem_iff]
      exact fun s =>
        ⟨fun ⟨⟨a, b⟩, ⟨_, ⟨ε, hε, hb⟩⟩, hs⟩ =>
          ⟨{ p | ∀ x, (p.1 x, p.2 x) ∈ b }, ⟨ε, hε, fun _ h x => hb ((dist_le hε.le).mp h x)⟩,
            fun f g h => hs fun x _ => h x⟩,
          fun ⟨_, ⟨ε, hε, ht⟩, hs⟩ =>
          ⟨⟨Set.univ, { p | dist p.1 p.2 ≤ ε }⟩, ⟨isCompact_univ, ⟨ε, hε, fun _ h => h⟩⟩,
            fun ⟨f, g⟩ h => hs _ _ (ht ((dist_le hε.le).mpr fun x => h x (mem_univ x)))⟩⟩)

theorem isUniformEmbedding_equivBoundedOfCompact : IsUniformEmbedding (equivBoundedOfCompact α β) :=
  { isUniformInducing_equivBoundedOfCompact α β with
    injective := (equivBoundedOfCompact α β).injective }

/-- When `α` is compact, the bounded continuous maps `α →ᵇ 𝕜` are
additively equivalent to `C(α, 𝕜)`.
-/
@[simps! -fullyApplied apply symm_apply]
def addEquivBoundedOfCompact [AddMonoid β] [LipschitzAdd β] : C(α, β) ≃+ (α →ᵇ β) :=
  ({ toContinuousMapAddMonoidHom α β, (equivBoundedOfCompact α β).symm with } :
    (α →ᵇ β) ≃+ C(α, β)).symm

instance instPseudoMetricSpace : PseudoMetricSpace C(α, β) :=
  (isUniformEmbedding_equivBoundedOfCompact α β).comapPseudoMetricSpace _

instance instMetricSpace {β : Type*} [MetricSpace β] :
    MetricSpace C(α, β) :=
  (isUniformEmbedding_equivBoundedOfCompact α β).comapMetricSpace _


/-- When `α` is compact, and `β` is a metric space, the bounded continuous maps `α →ᵇ β` are
isometric to `C(α, β)`.
-/
@[simps! -fullyApplied toEquiv apply symm_apply]
def isometryEquivBoundedOfCompact : C(α, β) ≃ᵢ (α →ᵇ β) where
  isometry_toFun _ _ := rfl
  toEquiv := equivBoundedOfCompact α β

end

@[simp]
theorem _root_.BoundedContinuousFunction.dist_mkOfCompact (f g : C(α, β)) :
    dist (mkOfCompact f) (mkOfCompact g) = dist f g :=
  rfl

@[simp]
theorem _root_.BoundedContinuousFunction.dist_toContinuousMap (f g : α →ᵇ β) :
    dist f.toContinuousMap g.toContinuousMap = dist f g :=
  rfl

open BoundedContinuousFunction

section

variable {f g : C(α, β)} {C : ℝ}

/-- The pointwise distance is controlled by the distance between functions, by definition. -/
theorem dist_apply_le_dist (x : α) : dist (f x) (g x) ≤ dist f g := by
  simp only [← dist_mkOfCompact, dist_coe_le_dist, ← mkOfCompact_apply]

/-- The distance between two functions is controlled by the supremum of the pointwise distances. -/
theorem dist_le (C0 : (0 : ℝ) ≤ C) : dist f g ≤ C ↔ ∀ x : α, dist (f x) (g x) ≤ C := by
  simp only [← dist_mkOfCompact, BoundedContinuousFunction.dist_le C0, mkOfCompact_apply]

theorem dist_le_iff_of_nonempty [Nonempty α] : dist f g ≤ C ↔ ∀ x, dist (f x) (g x) ≤ C := by
  simp only [← dist_mkOfCompact, BoundedContinuousFunction.dist_le_iff_of_nonempty,
    mkOfCompact_apply]

theorem dist_lt_iff_of_nonempty [Nonempty α] : dist f g < C ↔ ∀ x : α, dist (f x) (g x) < C := by
  simp only [← dist_mkOfCompact, dist_lt_iff_of_nonempty_compact, mkOfCompact_apply]

theorem dist_lt_of_nonempty [Nonempty α] (w : ∀ x : α, dist (f x) (g x) < C) : dist f g < C :=
  dist_lt_iff_of_nonempty.2 w

theorem dist_lt_iff (C0 : (0 : ℝ) < C) : dist f g < C ↔ ∀ x : α, dist (f x) (g x) < C := by
  rw [← dist_mkOfCompact, dist_lt_iff_of_compact C0]
  simp only [mkOfCompact_apply]

theorem dist_eq_iSup : dist f g = ⨆ x, dist (f x) (g x) := by
  simp [← isometryEquivBoundedOfCompact α β |>.dist_eq f g,
    BoundedContinuousFunction.dist_eq_iSup]

theorem nndist_eq_iSup : nndist f g = ⨆ x, nndist (f x) (g x) := by
  simp [← isometryEquivBoundedOfCompact α β |>.nndist_eq f g,
    BoundedContinuousFunction.nndist_eq_iSup]

theorem edist_eq_iSup : edist f g = ⨆ (x : α), edist (f x) (g x) := by
  simp [← isometryEquivBoundedOfCompact α β |>.edist_eq f g,
    BoundedContinuousFunction.edist_eq_iSup]

instance {R} [Zero R] [Zero β] [PseudoMetricSpace R] [SMul R β] [IsBoundedSMul R β] :
    IsBoundedSMul R C(α, β) where
  dist_smul_pair' r f g := by
    simpa only [← dist_mkOfCompact] using dist_smul_pair r (mkOfCompact f) (mkOfCompact g)
  dist_pair_smul' r₁ r₂ f := by
    simpa only [← dist_mkOfCompact] using dist_pair_smul r₁ r₂ (mkOfCompact f)

end

-- TODO at some point we will need lemmas characterising this norm!
-- At the moment the only way to reason about it is to transfer `f : C(α,E)` back to `α →ᵇ E`.
instance : Norm C(α, E) where norm x := dist x 0

@[simp]
theorem _root_.BoundedContinuousFunction.norm_mkOfCompact (f : C(α, E)) : ‖mkOfCompact f‖ = ‖f‖ :=
  rfl

@[simp]
theorem _root_.BoundedContinuousFunction.norm_toContinuousMap_eq (f : α →ᵇ E) :
    ‖f.toContinuousMap‖ = ‖f‖ :=
  rfl

open BoundedContinuousFunction

instance : SeminormedAddCommGroup C(α, E) where
  __ := ContinuousMap.instPseudoMetricSpace _ _
  __ := ContinuousMap.instAddCommGroupContinuousMap
  dist_eq x y := by rw [← norm_mkOfCompact, ← dist_mkOfCompact, dist_eq_norm_neg_add,
    mkOfCompact_add, mkOfCompact_neg]
  dist := dist
  norm := norm

instance {E : Type*} [NormedAddCommGroup E] : NormedAddCommGroup C(α, E) where
  __ : SeminormedAddCommGroup C(α, E) := inferInstance
  __ : MetricSpace C(α, E) := inferInstance

instance [Nonempty α] [One E] [NormOneClass E] : NormOneClass C(α, E) where
  norm_one := by simp only [← norm_mkOfCompact, mkOfCompact_one, norm_one]

section

variable (f : C(α, E))

-- The corresponding lemmas for `BoundedContinuousFunction` are stated with `{f}`,
-- and so cannot be used in dot notation.
theorem norm_coe_le_norm (x : α) : ‖f x‖ ≤ ‖f‖ :=
  (mkOfCompact f).norm_coe_le_norm x

/-- Distance between the images of any two points is at most twice the norm of the function. -/
theorem dist_le_two_norm (x y : α) : dist (f x) (f y) ≤ 2 * ‖f‖ :=
  (mkOfCompact f).dist_le_two_norm x y

/-- The norm of a function is controlled by the supremum of the pointwise norms. -/
theorem norm_le {C : ℝ} (C0 : (0 : ℝ) ≤ C) : ‖f‖ ≤ C ↔ ∀ x : α, ‖f x‖ ≤ C :=
  @BoundedContinuousFunction.norm_le _ _ _ _ (mkOfCompact f) _ C0

theorem norm_le_of_nonempty [Nonempty α] {M : ℝ} : ‖f‖ ≤ M ↔ ∀ x, ‖f x‖ ≤ M :=
  @BoundedContinuousFunction.norm_le_of_nonempty _ _ _ _ _ (mkOfCompact f) _

theorem norm_lt_iff {M : ℝ} (M0 : 0 < M) : ‖f‖ < M ↔ ∀ x, ‖f x‖ < M :=
  @BoundedContinuousFunction.norm_lt_iff_of_compact _ _ _ _ _ (mkOfCompact f) _ M0

theorem nnnorm_lt_iff {M : ℝ≥0} (M0 : 0 < M) : ‖f‖₊ < M ↔ ∀ x : α, ‖f x‖₊ < M :=
  f.norm_lt_iff M0

theorem norm_lt_iff_of_nonempty [Nonempty α] {M : ℝ} : ‖f‖ < M ↔ ∀ x, ‖f x‖ < M :=
  @BoundedContinuousFunction.norm_lt_iff_of_nonempty_compact _ _ _ _ _ _ (mkOfCompact f) _

theorem nnnorm_lt_iff_of_nonempty [Nonempty α] {M : ℝ≥0} : ‖f‖₊ < M ↔ ∀ x, ‖f x‖₊ < M :=
  f.norm_lt_iff_of_nonempty

theorem apply_le_norm (f : C(α, ℝ)) (x : α) : f x ≤ ‖f‖ :=
  le_trans (le_abs.mpr (Or.inl (le_refl (f x)))) (f.norm_coe_le_norm x)

theorem neg_norm_le_apply (f : C(α, ℝ)) (x : α) : -‖f‖ ≤ f x :=
  le_trans (neg_le_neg (f.norm_coe_le_norm x)) (neg_le.mp (neg_le_abs (f x)))

theorem nnnorm_eq_iSup_nnnorm : ‖f‖₊ = ⨆ x : α, ‖f x‖₊ :=
  (mkOfCompact f).nnnorm_eq_iSup_nnnorm

theorem norm_eq_iSup_norm : ‖f‖ = ⨆ x : α, ‖f x‖ :=
  (mkOfCompact f).norm_eq_iSup_norm

theorem enorm_eq_iSup_enorm : ‖f‖ₑ = ⨆ x, ‖f x‖ₑ :=
  (mkOfCompact f).enorm_eq_iSup_enorm

-- A version with better keys
instance {X : Type*} [TopologicalSpace X] (K : TopologicalSpace.Compacts X) :
    CompactSpace (K : Set X) :=
  TopologicalSpace.Compacts.instCompactSpaceSubtypeMem ..

theorem norm_restrict_mono_set {X : Type*} [TopologicalSpace X] (f : C(X, E))
    {K L : TopologicalSpace.Compacts X} (hKL : K ≤ L) : ‖f.restrict K‖ ≤ ‖f.restrict L‖ :=
  (norm_le _ (norm_nonneg _)).mpr fun x => norm_coe_le_norm (f.restrict L) <| Set.inclusion hKL x

end

section

variable {R : Type*}

instance [NonUnitalSeminormedRing R] : NonUnitalSeminormedRing C(α, R) where
  __ : SeminormedAddCommGroup C(α, R) := inferInstance
  __ : NonUnitalRing C(α, R) := inferInstance
  norm_mul_le f g := norm_mul_le (mkOfCompact f) (mkOfCompact g)

instance [NonUnitalSeminormedCommRing R] : NonUnitalSeminormedCommRing C(α, R) where
  __ : NonUnitalSeminormedRing C(α, R) := inferInstance
  __ : NonUnitalCommRing C(α, R) := inferInstance

instance [SeminormedRing R] : SeminormedRing C(α, R) where
  __ : NonUnitalSeminormedRing C(α, R) := inferInstance
  __ : Ring C(α, R) := inferInstance

instance [SeminormedCommRing R] : SeminormedCommRing C(α, R) where
  __ : SeminormedRing C(α, R) := inferInstance
  __ : CommRing C(α, R) := inferInstance

instance [NonUnitalNormedRing R] : NonUnitalNormedRing C(α, R) where
  __ : NormedAddCommGroup C(α, R) := inferInstance
  __ : NonUnitalSeminormedRing C(α, R) := inferInstance

instance [NonUnitalNormedCommRing R] : NonUnitalNormedCommRing C(α, R) where
  __ : NonUnitalNormedRing C(α, R) := inferInstance
  __ : NonUnitalCommRing C(α, R) := inferInstance

instance [NormedRing R] : NormedRing C(α, R) where
  __ : NormedAddCommGroup C(α, R) := inferInstance
  __ : SeminormedRing C(α, R) := inferInstance

instance [NormedCommRing R] : NormedCommRing C(α, R) where
  __ : NormedRing C(α, R) := inferInstance
  __ : CommRing C(α, R) := inferInstance

end

section

variable {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

instance normedSpace {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E] : NormedSpace 𝕜 C(α, E) where
  norm_smul_le := norm_smul_le

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
    norm_map' := fun _ => rfl }

end

-- this lemma and the next are the analogues of those autogenerated by `@[simps]` for
-- `equivBoundedOfCompact`, `addEquivBoundedOfCompact`
@[simp]
theorem linearIsometryBoundedOfCompact_symm_apply (f : α →ᵇ E) :
    (linearIsometryBoundedOfCompact α E 𝕜).symm f = f.toContinuousMap :=
  rfl

@[simp]
theorem linearIsometryBoundedOfCompact_apply_apply (f : C(α, E)) (a : α) :
    (linearIsometryBoundedOfCompact α E 𝕜 f) a = f a :=
  rfl

@[simp]
theorem linearIsometryBoundedOfCompact_toIsometryEquiv :
    (linearIsometryBoundedOfCompact α E 𝕜).toIsometryEquiv = isometryEquivBoundedOfCompact α E :=
  rfl

@[simp]
theorem linearIsometryBoundedOfCompact_toAddEquiv :
    ((linearIsometryBoundedOfCompact α E 𝕜).toLinearEquiv : C(α, E) ≃+ (α →ᵇ E)) =
      addEquivBoundedOfCompact α E :=
  rfl

@[simp]
theorem linearIsometryBoundedOfCompact_of_compact_toEquiv :
    (linearIsometryBoundedOfCompact α E 𝕜).toLinearEquiv.toEquiv = equivBoundedOfCompact α E :=
  rfl

end

@[simp] lemma nnnorm_smul_const {R β : Type*} [SeminormedAddCommGroup β] [SeminormedRing R]
    [Module R β] [NormSMulClass R β] (f : C(α, R)) (b : β) :
    ‖f • const α b‖₊ = ‖f‖₊ * ‖b‖₊ := by
  simp only [nnnorm_eq_iSup_nnnorm, smul_apply', const_apply, nnnorm_smul, iSup_mul]

@[simp] lemma norm_smul_const {R β : Type*} [SeminormedAddCommGroup β] [SeminormedRing R]
    [Module R β] [NormSMulClass R β] (f : C(α, R)) (b : β) :
    ‖f • const α b‖ = ‖f‖ * ‖b‖ := by
  simp only [← coe_nnnorm, NNReal.coe_mul, nnnorm_smul_const]

section NormSum

variable {R : Type*} [NonUnitalSeminormedRing R] [IsCancelMulZero R]

open BoundedContinuousFunction

/-- If the product of continuous functions on a compact space is zero, then the norm of their sum
is the maximum of their norms. -/
lemma norm_add_eq_max {f g : C(α, R)} (h : f * g = 0) :
    ‖f + g‖ = max ‖f‖ ‖g‖ := by
  replace h : mkOfCompact f * mkOfCompact g = 0 := by ext x; simpa using congr($h x)
  simpa using BoundedContinuousFunction.norm_add_eq_max h

/-- If the product of continuous functions on a compact space is zero, then the norm of their sum
is the maximum of their norms. -/
lemma nnnorm_add_eq_max {f g : C(α, R)} (h : f * g = 0) :
    ‖f + g‖₊ = max ‖f‖₊ ‖g‖₊ :=
  NNReal.eq <| norm_add_eq_max h

lemma norm_sub_eq_max {f g : C(α, R)} (h : f * g = 0) :
    ‖f - g‖ = max ‖f‖ ‖g‖ := by
  simpa [sub_eq_add_neg] using norm_add_eq_max (f := f) (g := -g) (by simpa)

lemma nnnorm_sub_eq_max {f g : C(α, R)} (h : f * g = 0) :
    ‖f - g‖₊ = max ‖f‖₊ ‖g‖₊ :=
  NNReal.eq <| norm_sub_eq_max h

open scoped Function in
/-- If the pairwise products of continuous functions on a compact space are all zero, then the norm
of their sum is the maximum of their norms. -/
lemma nnnorm_sum_eq_sup {ι : Type*} {f : ι → C(α, R)} (s : Finset ι)
    (h : Pairwise ((· * · = 0) on f)) :
    ‖∑ i ∈ s, f i‖₊ = s.sup (‖f ·‖₊) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    suffices f j * ∑ i ∈ s, f i = 0 by simpa [hj, ← ih] using nnnorm_add_eq_max this
    simpa [Finset.mul_sum] using Finset.sum_eq_zero fun i hi ↦ h (by grind)

end NormSum

section

variable {𝕜 : Type*} {γ : Type*} [NormedField 𝕜] [SeminormedRing γ] [NormedAlgebra 𝕜 γ]

instance : NormedAlgebra 𝕜 C(α, γ) :=
  { ContinuousMap.normedSpace, ContinuousMap.algebra with }

end

end ContinuousMap

namespace ContinuousMap

section UniformContinuity

variable {α β : Type*}
variable [PseudoMetricSpace α] [CompactSpace α] [PseudoMetricSpace β]

/-!
We now set up some declarations making it convenient to use uniform continuity.
-/


theorem uniform_continuity (f : C(α, β)) (ε : ℝ) (h : 0 < ε) :
    ∃ δ > 0, ∀ {x y}, dist x y < δ → dist (f x) (f y) < ε :=
  Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous f.continuous) ε h

-- This definition allows us to separate the choice of some `δ`,
-- and the corresponding use of `dist a b < δ → dist (f a) (f b) < ε`,
-- even across different declarations.
/-- An arbitrarily chosen modulus of uniform continuity for a given function `f` and `ε > 0`. -/
def modulus (f : C(α, β)) (ε : ℝ) (h : 0 < ε) : ℝ :=
  Classical.choose (uniform_continuity f ε h)

theorem modulus_pos (f : C(α, β)) {ε : ℝ} {h : 0 < ε} : 0 < f.modulus ε h :=
  (Classical.choose_spec (uniform_continuity f ε h)).1

theorem dist_lt_of_dist_lt_modulus (f : C(α, β)) (ε : ℝ) (h : 0 < ε) {a b : α}
    (w : dist a b < f.modulus ε h) : dist (f a) (f b) < ε :=
  (Classical.choose_spec (uniform_continuity f ε h)).2 w

end UniformContinuity

end ContinuousMap

namespace ContinuousMap

section LocalNormalConvergence

/-! ### Local normal convergence

A sum of continuous functions (on a locally compact space) is "locally normally convergent" if the
sum of its sup-norms on any compact subset is summable. This implies convergence in the topology
of `C(X, E)` (i.e. locally uniform convergence). -/

open TopologicalSpace

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

theorem summable_of_locally_summable_norm {ι : Type*} {F : ι → C(X, E)}
    (hF : ∀ K : Compacts X, Summable fun i => ‖(F i).restrict K‖) : Summable F := by
  classical
  refine (ContinuousMap.exists_tendsto_compactOpen_iff_forall _).2 fun K hK => ?_
  lift K to Compacts X using hK
  have A : ∀ s : Finset ι, restrict K (∑ i ∈ s, F i) = ∑ i ∈ s, restrict K (F i) := by
    intro s
    ext1 x
    -- TODO: there is a non-confluence problem in the lemmas here,
    -- and `SetLike.coe_sort_coe` prevents `restrict_apply` from being used.
    simp [-SetLike.coe_sort_coe]
  simpa only [HasSum, A] using (hF K).of_norm

end LocalNormalConvergence

/-!
### Star structures

In this section, if `β` is a normed ⋆-group, then so is the space of
continuous functions from `α` to `β`, by using the star operation pointwise.

Furthermore, if `α` is compact and `β` is a C⋆-ring, then `C(α, β)` is a C⋆-ring. -/


section NormedSpace

variable {α : Type*} {β : Type*}
variable [TopologicalSpace α] [SeminormedAddCommGroup β] [StarAddMonoid β] [NormedStarGroup β]

theorem _root_.BoundedContinuousFunction.mkOfCompact_star [CompactSpace α] (f : C(α, β)) :
    mkOfCompact (star f) = star (mkOfCompact f) :=
  rfl

instance [CompactSpace α] : NormedStarGroup C(α, β) where
  norm_star_le f := by
    rw [← BoundedContinuousFunction.norm_mkOfCompact, BoundedContinuousFunction.mkOfCompact_star,
      norm_star, BoundedContinuousFunction.norm_mkOfCompact]

end NormedSpace

section CStarRing

variable {α : Type*} {β : Type*}
variable [TopologicalSpace α] [CompactSpace α]

instance [NonUnitalNormedRing β] [StarRing β] [CStarRing β] : CStarRing C(α, β) where
  norm_mul_self_le f := by
    rw [← sq, ← Real.le_sqrt (norm_nonneg _) (norm_nonneg _),
      ContinuousMap.norm_le _ (Real.sqrt_nonneg _)]
    intro x
    rw [Real.le_sqrt (norm_nonneg _) (norm_nonneg _), sq, ← CStarRing.norm_star_mul_self]
    exact ContinuousMap.norm_coe_le_norm (star f * f) x

end CStarRing

end ContinuousMap
