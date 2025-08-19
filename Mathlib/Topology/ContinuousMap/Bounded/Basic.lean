/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Mario Carneiro, Yury Kudryashov, Heather Macbeth
-/
import Mathlib.Topology.Algebra.Indicator
import Mathlib.Topology.Bornology.BoundedOperation
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Bounded continuous functions

The type of bounded continuous functions taking values in a metric space, with the uniform distance.
-/

assert_not_exists CStarRing

noncomputable section

open Topology Bornology NNReal UniformConvergence

open Set Filter Metric Function

universe u v w

variable {F : Type*} {α : Type u} {β : Type v} {γ : Type w}

/-- `α →ᵇ β` is the type of bounded continuous functions `α → β` from a topological space to a
metric space.

When possible, instead of parametrizing results over `(f : α →ᵇ β)`,
you should parametrize over `(F : Type*) [BoundedContinuousMapClass F α β] (f : F)`.

When you extend this structure, make sure to extend `BoundedContinuousMapClass`. -/
structure BoundedContinuousFunction (α : Type u) (β : Type v) [TopologicalSpace α]
    [PseudoMetricSpace β] : Type max u v extends ContinuousMap α β where
  map_bounded' : ∃ C, ∀ x y, dist (toFun x) (toFun y) ≤ C

@[inherit_doc] scoped[BoundedContinuousFunction] infixr:25 " →ᵇ " => BoundedContinuousFunction

section

/-- `BoundedContinuousMapClass F α β` states that `F` is a type of bounded continuous maps.

You should also extend this typeclass when you extend `BoundedContinuousFunction`. -/
class BoundedContinuousMapClass (F : Type*) (α β : outParam Type*) [TopologicalSpace α]
    [PseudoMetricSpace β] [FunLike F α β] : Prop extends ContinuousMapClass F α β where
  map_bounded (f : F) : ∃ C, ∀ x y, dist (f x) (f y) ≤ C

end

export BoundedContinuousMapClass (map_bounded)

namespace BoundedContinuousFunction

section Basics

variable [TopologicalSpace α] [PseudoMetricSpace β] [PseudoMetricSpace γ]
variable {f g : α →ᵇ β} {x : α} {C : ℝ}

instance instFunLike : FunLike (α →ᵇ β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

instance instBoundedContinuousMapClass : BoundedContinuousMapClass (α →ᵇ β) α β where
  map_continuous f := f.continuous_toFun
  map_bounded f := f.map_bounded'

instance instCoeTC [FunLike F α β] [BoundedContinuousMapClass F α β] : CoeTC F (α →ᵇ β) :=
  ⟨fun f ↦
    { toFun := f
      continuous_toFun := map_continuous f
      map_bounded' := map_bounded f }⟩

@[simp]
theorem coe_toContinuousMap (f : α →ᵇ β) : (f.toContinuousMap : α → β) = f := rfl

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (h : α →ᵇ β) : α → β := h

initialize_simps_projections BoundedContinuousFunction (toFun → apply)

protected theorem bounded (f : α →ᵇ β) : ∃ C, ∀ x y : α, dist (f x) (f y) ≤ C :=
  f.map_bounded'

protected theorem continuous (f : α →ᵇ β) : Continuous f :=
  f.toContinuousMap.continuous

@[ext]
theorem ext (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

theorem isBounded_range (f : α →ᵇ β) : IsBounded (range f) :=
  isBounded_range_iff.2 f.bounded

theorem isBounded_image (f : α →ᵇ β) (s : Set α) : IsBounded (f '' s) :=
  f.isBounded_range.subset <| image_subset_range _ _

theorem eq_of_empty [h : IsEmpty α] (f g : α →ᵇ β) : f = g :=
  ext <| h.elim

/-- A continuous function with an explicit bound is a bounded continuous function. -/
def mkOfBound (f : C(α, β)) (C : ℝ) (h : ∀ x y : α, dist (f x) (f y) ≤ C) : α →ᵇ β :=
  ⟨f, ⟨C, h⟩⟩

@[simp]
theorem mkOfBound_coe {f} {C} {h} : (mkOfBound f C h : α → β) = (f : α → β) := rfl

/-- A continuous function on a compact space is automatically a bounded continuous function. -/
def mkOfCompact [CompactSpace α] (f : C(α, β)) : α →ᵇ β :=
  ⟨f, isBounded_range_iff.1 (isCompact_range f.continuous).isBounded⟩

@[simp]
theorem mkOfCompact_apply [CompactSpace α] (f : C(α, β)) (a : α) : mkOfCompact f a = f a := rfl

/-- If a function is bounded on a discrete space, it is automatically continuous,
and therefore gives rise to an element of the type of bounded continuous functions. -/
@[simps]
def mkOfDiscrete [DiscreteTopology α] (f : α → β) (C : ℝ) (h : ∀ x y : α, dist (f x) (f y) ≤ C) :
    α →ᵇ β :=
  ⟨⟨f, continuous_of_discreteTopology⟩, ⟨C, h⟩⟩

/-- The uniform distance between two bounded continuous functions. -/
instance instDist : Dist (α →ᵇ β) :=
  ⟨fun f g ↦ sInf { C | 0 ≤ C ∧ ∀ x : α, dist (f x) (g x) ≤ C }⟩

theorem dist_eq : dist f g = sInf { C | 0 ≤ C ∧ ∀ x : α, dist (f x) (g x) ≤ C } := rfl

theorem dist_set_exists : ∃ C, 0 ≤ C ∧ ∀ x : α, dist (f x) (g x) ≤ C := by
  rcases isBounded_iff.1 (f.isBounded_range.union g.isBounded_range) with ⟨C, hC⟩
  refine ⟨max 0 C, le_max_left _ _, fun x ↦ (hC ?_ ?_).trans (le_max_right _ _)⟩
    <;> [left; right]
    <;> apply mem_range_self

/-- The pointwise distance is controlled by the distance between functions, by definition. -/
theorem dist_coe_le_dist (x : α) : dist (f x) (g x) ≤ dist f g :=
  le_csInf dist_set_exists fun _ hb ↦ hb.2 x

/- This lemma will be needed in the proof of the metric space instance, but it will become
useless afterwards as it will be superseded by the general result that the distance is nonnegative
in metric spaces. -/
private theorem dist_nonneg' : 0 ≤ dist f g :=
  le_csInf dist_set_exists fun _ ↦ And.left

/-- The distance between two functions is controlled by the supremum of the pointwise distances. -/
theorem dist_le (C0 : (0 : ℝ) ≤ C) : dist f g ≤ C ↔ ∀ x : α, dist (f x) (g x) ≤ C :=
  ⟨fun h x ↦ le_trans (dist_coe_le_dist x) h, fun H ↦ csInf_le ⟨0, fun _ ↦ And.left⟩ ⟨C0, H⟩⟩

theorem dist_le_iff_of_nonempty [Nonempty α] : dist f g ≤ C ↔ ∀ x, dist (f x) (g x) ≤ C :=
  ⟨fun h x ↦ le_trans (dist_coe_le_dist x) h,
    fun w ↦ (dist_le (le_trans dist_nonneg (w (Nonempty.some ‹_›)))).mpr w⟩

theorem dist_lt_of_nonempty_compact [Nonempty α] [CompactSpace α]
    (w : ∀ x : α, dist (f x) (g x) < C) : dist f g < C := by
  have c : Continuous fun x ↦ dist (f x) (g x) := by fun_prop
  obtain ⟨x, -, le⟩ :=
    IsCompact.exists_isMaxOn isCompact_univ Set.univ_nonempty (Continuous.continuousOn c)
  exact lt_of_le_of_lt (dist_le_iff_of_nonempty.mpr fun y ↦ le trivial) (w x)

theorem dist_lt_iff_of_compact [CompactSpace α] (C0 : (0 : ℝ) < C) :
    dist f g < C ↔ ∀ x : α, dist (f x) (g x) < C := by
  fconstructor
  · intro w x
    exact lt_of_le_of_lt (dist_coe_le_dist x) w
  · by_cases h : Nonempty α
    · exact dist_lt_of_nonempty_compact
    · rintro -
      convert C0
      apply le_antisymm _ dist_nonneg'
      rw [dist_eq]
      exact csInf_le ⟨0, fun C ↦ And.left⟩ ⟨le_rfl, fun x ↦ False.elim (h (Nonempty.intro x))⟩

theorem dist_lt_iff_of_nonempty_compact [Nonempty α] [CompactSpace α] :
    dist f g < C ↔ ∀ x : α, dist (f x) (g x) < C :=
  ⟨fun w x ↦ lt_of_le_of_lt (dist_coe_le_dist x) w, dist_lt_of_nonempty_compact⟩

/-- The type of bounded continuous functions, with the uniform distance, is a pseudometric space. -/
instance instPseudoMetricSpace : PseudoMetricSpace (α →ᵇ β) where
  dist_self f := le_antisymm ((dist_le le_rfl).2 fun x ↦ by simp) dist_nonneg'
  dist_comm f g := by simp [dist_eq, dist_comm]
  dist_triangle _ _ _ := (dist_le (add_nonneg dist_nonneg' dist_nonneg')).2
    fun _ ↦ le_trans (dist_triangle _ _ _) (add_le_add (dist_coe_le_dist _) (dist_coe_le_dist _))

/-- The type of bounded continuous functions, with the uniform distance, is a metric space. -/
instance instMetricSpace {β} [MetricSpace β] : MetricSpace (α →ᵇ β) where
  eq_of_dist_eq_zero hfg := by
    ext x
    exact eq_of_dist_eq_zero (le_antisymm (hfg ▸ dist_coe_le_dist _) dist_nonneg)

theorem nndist_eq : nndist f g = sInf { C | ∀ x : α, nndist (f x) (g x) ≤ C } :=
  Subtype.ext <| dist_eq.trans <| by
    rw [val_eq_coe, coe_sInf, coe_image]
    simp_rw [mem_setOf_eq, ← NNReal.coe_le_coe, coe_mk, exists_prop, coe_nndist]

theorem nndist_set_exists : ∃ C, ∀ x : α, nndist (f x) (g x) ≤ C :=
  Subtype.exists.mpr <| dist_set_exists.imp fun _ ⟨ha, h⟩ ↦ ⟨ha, h⟩

theorem nndist_coe_le_nndist (x : α) : nndist (f x) (g x) ≤ nndist f g :=
  dist_coe_le_dist x

/-- On an empty space, bounded continuous functions are at distance 0. -/
theorem dist_zero_of_empty [IsEmpty α] : dist f g = 0 := by
  rw [(ext isEmptyElim : f = g), dist_self]

theorem dist_eq_iSup : dist f g = ⨆ x : α, dist (f x) (g x) := by
  cases isEmpty_or_nonempty α
  · rw [iSup_of_empty', Real.sSup_empty, dist_zero_of_empty]
  refine (dist_le_iff_of_nonempty.mpr <| le_ciSup ?_).antisymm (ciSup_le dist_coe_le_dist)
  exact dist_set_exists.imp fun C hC ↦ forall_mem_range.2 hC.2

theorem nndist_eq_iSup : nndist f g = ⨆ x : α, nndist (f x) (g x) :=
  Subtype.ext <| dist_eq_iSup.trans <| by simp_rw [val_eq_coe, coe_iSup, coe_nndist]

theorem edist_eq_iSup : edist f g = ⨆ x, edist (f x) (g x) := by
  simp_rw [edist_nndist, nndist_eq_iSup]
  refine ENNReal.coe_iSup ⟨nndist f g, ?_⟩
  rintro - ⟨x, hx, rfl⟩
  exact nndist_coe_le_nndist x

theorem tendsto_iff_tendstoUniformly {ι : Type*} {F : ι → α →ᵇ β} {f : α →ᵇ β} {l : Filter ι} :
    Tendsto F l (𝓝 f) ↔ TendstoUniformly (fun i ↦ F i) f l :=
  Iff.intro
    (fun h ↦
      tendstoUniformly_iff.2 fun ε ε0 ↦
        (Metric.tendsto_nhds.mp h ε ε0).mp
          (Eventually.of_forall fun n hn x ↦
            lt_of_le_of_lt (dist_coe_le_dist x) (dist_comm (F n) f ▸ hn)))
    fun h ↦
    Metric.tendsto_nhds.mpr fun _ ε_pos ↦
      (h _ (dist_mem_uniformity <| half_pos ε_pos)).mp
        (Eventually.of_forall fun n hn ↦
          lt_of_le_of_lt
            ((dist_le (half_pos ε_pos).le).mpr fun x ↦ dist_comm (f x) (F n x) ▸ le_of_lt (hn x))
            (half_lt_self ε_pos))

/-- The topology on `α →ᵇ β` is exactly the topology induced by the natural map to `α →ᵤ β`. -/
theorem isInducing_coeFn : IsInducing (UniformFun.ofFun ∘ (⇑) : (α →ᵇ β) → α →ᵤ β) := by
  rw [isInducing_iff_nhds]
  refine fun f ↦ eq_of_forall_le_iff fun l ↦ ?_
  rw [← tendsto_iff_comap, ← tendsto_id', tendsto_iff_tendstoUniformly,
    UniformFun.tendsto_iff_tendstoUniformly]
  simp [comp_def]

-- TODO: upgrade to `IsUniformEmbedding`
theorem isEmbedding_coeFn : IsEmbedding (UniformFun.ofFun ∘ (⇑) : (α →ᵇ β) → α →ᵤ β) :=
  ⟨isInducing_coeFn, fun _ _ h ↦ ext fun x ↦ congr_fun h x⟩

variable (α) in
/-- Constant as a continuous bounded function. -/
@[simps! -fullyApplied]
def const (b : β) : α →ᵇ β :=
  ⟨ContinuousMap.const α b, 0, by simp⟩

theorem const_apply' (a : α) (b : β) : (const α b : α → β) a = b := rfl

/-- If the target space is inhabited, so is the space of bounded continuous functions. -/
instance [Inhabited β] : Inhabited (α →ᵇ β) :=
  ⟨const α default⟩

theorem lipschitz_evalx (x : α) : LipschitzWith 1 fun f : α →ᵇ β ↦ f x :=
  LipschitzWith.mk_one fun _ _ ↦ dist_coe_le_dist x

theorem uniformContinuous_coe : @UniformContinuous (α →ᵇ β) (α → β) _ _ (⇑) :=
  uniformContinuous_pi.2 fun x ↦ (lipschitz_evalx x).uniformContinuous

theorem continuous_coe : Continuous fun (f : α →ᵇ β) x ↦ f x :=
  UniformContinuous.continuous uniformContinuous_coe

/-- When `x` is fixed, `(f : α →ᵇ β) ↦ f x` is continuous. -/
@[continuity]
theorem continuous_eval_const {x : α} : Continuous fun f : α →ᵇ β ↦ f x :=
  (continuous_apply x).comp continuous_coe

/-- The evaluation map is continuous, as a joint function of `u` and `x`. -/
@[continuity]
theorem continuous_eval : Continuous fun p : (α →ᵇ β) × α ↦ p.1 p.2 :=
  (continuous_prod_of_continuous_lipschitzWith _ 1 fun f ↦ f.continuous) <| lipschitz_evalx

/-- Bounded continuous functions taking values in a complete space form a complete space. -/
instance instCompleteSpace [CompleteSpace β] : CompleteSpace (α →ᵇ β) :=
  complete_of_cauchySeq_tendsto fun (f : ℕ → α →ᵇ β) (hf : CauchySeq f) ↦ by
    /- We have to show that `f n` converges to a bounded continuous function.
      For this, we prove pointwise convergence to define the limit, then check
      it is a continuous bounded function, and then check the norm convergence. -/
    rcases cauchySeq_iff_le_tendsto_0.1 hf with ⟨b, b0, b_bound, b_lim⟩
    have f_bdd := fun x n m N hn hm ↦ le_trans (dist_coe_le_dist x) (b_bound n m N hn hm)
    have fx_cau : ∀ x, CauchySeq fun n ↦ f n x :=
      fun x ↦ cauchySeq_iff_le_tendsto_0.2 ⟨b, b0, f_bdd x, b_lim⟩
    choose F hF using fun x ↦ cauchySeq_tendsto_of_complete (fx_cau x)
    /- `F : α → β`, `hF : ∀ (x : α), Tendsto (fun n ↦ ↑(f n) x) atTop (𝓝 (F x))`
      `F` is the desired limit function. Check that it is uniformly approximated by `f N`. -/
    have fF_bdd : ∀ x N, dist (f N x) (F x) ≤ b N :=
      fun x N ↦ le_of_tendsto (tendsto_const_nhds.dist (hF x))
        (Filter.eventually_atTop.2 ⟨N, fun n hn ↦ f_bdd x N n N (le_refl N) hn⟩)
    refine ⟨⟨⟨F, ?_⟩, ?_⟩, ?_⟩
    · -- Check that `F` is continuous, as a uniform limit of continuous functions
      have : TendstoUniformly (fun n x ↦ f n x) F atTop := by
        refine Metric.tendstoUniformly_iff.2 fun ε ε0 ↦ ?_
        refine ((tendsto_order.1 b_lim).2 ε ε0).mono fun n hn x ↦ ?_
        rw [dist_comm]
        exact lt_of_le_of_lt (fF_bdd x n) hn
      exact this.continuous (Eventually.of_forall fun N ↦ (f N).continuous)
    · -- Check that `F` is bounded
      rcases (f 0).bounded with ⟨C, hC⟩
      refine ⟨C + (b 0 + b 0), fun x y ↦ ?_⟩
      calc
        dist (F x) (F y) ≤ dist (f 0 x) (f 0 y) + (dist (f 0 x) (F x) + dist (f 0 y) (F y)) :=
          dist_triangle4_left _ _ _ _
        _ ≤ C + (b 0 + b 0) := add_le_add (hC x y) (add_le_add (fF_bdd x 0) (fF_bdd y 0))
    · -- Check that `F` is close to `f N` in distance terms
      refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ ↦ dist_nonneg) ?_ b_lim)
      exact fun N ↦ (dist_le (b0 _)).2 fun x ↦ fF_bdd x N

/-- Composition of a bounded continuous function and a continuous function. -/
def compContinuous {δ : Type*} [TopologicalSpace δ] (f : α →ᵇ β) (g : C(δ, α)) : δ →ᵇ β where
  toContinuousMap := f.1.comp g
  map_bounded' := f.map_bounded'.imp fun _ hC _ _ ↦ hC _ _

@[simp]
theorem coe_compContinuous {δ : Type*} [TopologicalSpace δ] (f : α →ᵇ β) (g : C(δ, α)) :
    ⇑(f.compContinuous g) = f ∘ g := rfl

@[simp]
theorem compContinuous_apply {δ : Type*} [TopologicalSpace δ] (f : α →ᵇ β) (g : C(δ, α)) (x : δ) :
    f.compContinuous g x = f (g x) := rfl

theorem lipschitz_compContinuous {δ : Type*} [TopologicalSpace δ] (g : C(δ, α)) :
    LipschitzWith 1 fun f : α →ᵇ β ↦ f.compContinuous g :=
  LipschitzWith.mk_one fun _ _ ↦ (dist_le dist_nonneg).2 fun x ↦ dist_coe_le_dist (g x)

theorem continuous_compContinuous {δ : Type*} [TopologicalSpace δ] (g : C(δ, α)) :
    Continuous fun f : α →ᵇ β ↦ f.compContinuous g :=
  (lipschitz_compContinuous g).continuous

/-- Restrict a bounded continuous function to a set. -/
def restrict (f : α →ᵇ β) (s : Set α) : s →ᵇ β :=
  f.compContinuous <| (ContinuousMap.id _).restrict s

@[simp]
theorem coe_restrict (f : α →ᵇ β) (s : Set α) : ⇑(f.restrict s) = f ∘ (↑) := rfl

@[simp]
theorem restrict_apply (f : α →ᵇ β) (s : Set α) (x : s) : f.restrict s x = f x := rfl

/-- Composition (in the target) of a bounded continuous function with a Lipschitz map again
gives a bounded continuous function. -/
def comp (G : β → γ) {C : ℝ≥0} (H : LipschitzWith C G) (f : α →ᵇ β) : α →ᵇ γ :=
  ⟨⟨fun x ↦ G (f x), H.continuous.comp f.continuous⟩,
    let ⟨D, hD⟩ := f.bounded
    ⟨max C 0 * D, fun x y ↦
      calc
        dist (G (f x)) (G (f y)) ≤ C * dist (f x) (f y) := H.dist_le_mul _ _
        _ ≤ max C 0 * dist (f x) (f y) := by gcongr; apply le_max_left
        _ ≤ max C 0 * D := by gcongr; apply hD
        ⟩⟩

@[simp]
theorem comp_apply (G : β → γ) {C : ℝ≥0} (H : LipschitzWith C G) (f : α →ᵇ β) (a : α) :
    (f.comp G H) a = G (f a) := rfl

/-- The composition operator (in the target) with a Lipschitz map is Lipschitz. -/
theorem lipschitz_comp {G : β → γ} {C : ℝ≥0} (H : LipschitzWith C G) :
    LipschitzWith C (comp G H : (α →ᵇ β) → α →ᵇ γ) :=
  LipschitzWith.of_dist_le_mul fun f g ↦
    (dist_le (mul_nonneg C.2 dist_nonneg)).2 fun x ↦
      calc
        dist (G (f x)) (G (g x)) ≤ C * dist (f x) (g x) := H.dist_le_mul _ _
        _ ≤ C * dist f g := by gcongr; apply dist_coe_le_dist

/-- The composition operator (in the target) with a Lipschitz map is uniformly continuous. -/
theorem uniformContinuous_comp {G : β → γ} {C : ℝ≥0} (H : LipschitzWith C G) :
    UniformContinuous (comp G H : (α →ᵇ β) → α →ᵇ γ) :=
  (lipschitz_comp H).uniformContinuous

/-- The composition operator (in the target) with a Lipschitz map is continuous. -/
theorem continuous_comp {G : β → γ} {C : ℝ≥0} (H : LipschitzWith C G) :
    Continuous (comp G H : (α →ᵇ β) → α →ᵇ γ) :=
  (lipschitz_comp H).continuous

/-- Restriction (in the target) of a bounded continuous function taking values in a subset. -/
def codRestrict (s : Set β) (f : α →ᵇ β) (H : ∀ x, f x ∈ s) : α →ᵇ s :=
  ⟨⟨s.codRestrict f H, f.continuous.subtype_mk _⟩, f.bounded⟩

section Extend

variable {δ : Type*} [TopologicalSpace δ] [DiscreteTopology δ]

/-- A version of `Function.extend` for bounded continuous maps. We assume that the domain has
discrete topology, so we only need to verify boundedness. -/
nonrec def extend (f : α ↪ δ) (g : α →ᵇ β) (h : δ →ᵇ β) : δ →ᵇ β where
  toFun := extend f g h
  continuous_toFun := continuous_of_discreteTopology
  map_bounded' := by
    rw [← isBounded_range_iff, range_extend f.injective]
    exact g.isBounded_range.union (h.isBounded_image _)

@[simp]
theorem extend_apply (f : α ↪ δ) (g : α →ᵇ β) (h : δ →ᵇ β) (x : α) : extend f g h (f x) = g x :=
  f.injective.extend_apply _ _ _

@[simp]
nonrec theorem extend_comp (f : α ↪ δ) (g : α →ᵇ β) (h : δ →ᵇ β) : extend f g h ∘ f = g :=
  extend_comp f.injective _ _

nonrec theorem extend_apply' {f : α ↪ δ} {x : δ} (hx : x ∉ range f) (g : α →ᵇ β) (h : δ →ᵇ β) :
    extend f g h x = h x :=
  extend_apply' _ _ _ hx

theorem extend_of_empty [IsEmpty α] (f : α ↪ δ) (g : α →ᵇ β) (h : δ →ᵇ β) : extend f g h = h :=
  DFunLike.coe_injective <| Function.extend_of_isEmpty f g h

@[simp]
theorem dist_extend_extend (f : α ↪ δ) (g₁ g₂ : α →ᵇ β) (h₁ h₂ : δ →ᵇ β) :
    dist (g₁.extend f h₁) (g₂.extend f h₂) =
      max (dist g₁ g₂) (dist (h₁.restrict (range f)ᶜ) (h₂.restrict (range f)ᶜ)) := by
  refine le_antisymm ((dist_le <| le_max_iff.2 <| Or.inl dist_nonneg).2 fun x ↦ ?_) (max_le ?_ ?_)
  · rcases em (∃ y, f y = x) with (⟨x, rfl⟩ | hx)
    · simp only [extend_apply]
      exact (dist_coe_le_dist x).trans (le_max_left _ _)
    · simp only [extend_apply' hx]
      lift x to ((range f)ᶜ : Set δ) using hx
      calc
        dist (h₁ x) (h₂ x) = dist (h₁.restrict (range f)ᶜ x) (h₂.restrict (range f)ᶜ x) := rfl
        _ ≤ dist (h₁.restrict (range f)ᶜ) (h₂.restrict (range f)ᶜ) := dist_coe_le_dist x
        _ ≤ _ := le_max_right _ _
  · refine (dist_le dist_nonneg).2 fun x ↦ ?_
    rw [← extend_apply f g₁ h₁, ← extend_apply f g₂ h₂]
    exact dist_coe_le_dist _
  · refine (dist_le dist_nonneg).2 fun x ↦ ?_
    calc
      dist (h₁ x) (h₂ x) = dist (extend f g₁ h₁ x) (extend f g₂ h₂ x) := by
        rw [extend_apply' x.coe_prop, extend_apply' x.coe_prop]
      _ ≤ _ := dist_coe_le_dist _

theorem isometry_extend (f : α ↪ δ) (h : δ →ᵇ β) : Isometry fun g : α →ᵇ β ↦ extend f g h :=
  Isometry.of_dist_eq fun g₁ g₂ ↦ by simp

end Extend

/-- The indicator function of a clopen set, as a bounded continuous function. -/
@[simps]
noncomputable def indicator (s : Set α) (hs : IsClopen s) : BoundedContinuousFunction α ℝ where
  toFun := s.indicator 1
  continuous_toFun := continuous_indicator (by simp [hs]) <| continuous_const.continuousOn
  map_bounded' := ⟨1, fun x y ↦ by by_cases hx : x ∈ s <;> by_cases hy : y ∈ s <;> simp [hx, hy]⟩

end Basics

section One

variable [TopologicalSpace α] [PseudoMetricSpace β] [One β]

@[to_additive] instance instOne : One (α →ᵇ β) := ⟨const α 1⟩

@[to_additive (attr := simp)]
theorem coe_one : ((1 : α →ᵇ β) : α → β) = 1 := rfl

@[to_additive (attr := simp)]
theorem mkOfCompact_one [CompactSpace α] : mkOfCompact (1 : C(α, β)) = 1 := rfl

@[to_additive]
theorem forall_coe_one_iff_one (f : α →ᵇ β) : (∀ x, f x = 1) ↔ f = 1 :=
  (@DFunLike.ext_iff _ _ _ _ f 1).symm

@[to_additive (attr := simp)]
theorem one_compContinuous [TopologicalSpace γ] (f : C(γ, α)) : (1 : α →ᵇ β).compContinuous f = 1 :=
  rfl

end One

section mul

variable {R : Type*} [TopologicalSpace α] [PseudoMetricSpace R]

@[to_additive]
instance instMul [Mul R] [BoundedMul R] [ContinuousMul R] :
    Mul (α →ᵇ R) where
  mul f g :=
    { toFun := fun x ↦ f x * g x
      continuous_toFun := f.continuous.mul g.continuous
      map_bounded' := mul_bounded_of_bounded_of_bounded (map_bounded f) (map_bounded g) }

@[to_additive (attr := simp)]
theorem coe_mul [Mul R] [BoundedMul R] [ContinuousMul R] (f g : α →ᵇ R) : ⇑(f * g) = f * g := rfl

@[to_additive]
theorem mul_apply [Mul R] [BoundedMul R] [ContinuousMul R] (f g : α →ᵇ R) (x : α) :
    (f * g) x = f x * g x := rfl

@[simp]
theorem coe_nsmulRec [PseudoMetricSpace β] [AddMonoid β] [BoundedAdd β] [ContinuousAdd β]
    (f : α →ᵇ β) : ∀ n, ⇑(nsmulRec n f) = n • ⇑f
  | 0 => by rw [nsmulRec, zero_smul, coe_zero]
  | n + 1 => by rw [nsmulRec, succ_nsmul, coe_add, coe_nsmulRec _ n]

instance instSMulNat [PseudoMetricSpace β] [AddMonoid β] [BoundedAdd β] [ContinuousAdd β] :
    SMul ℕ (α →ᵇ β) where
  smul n f :=
    { toContinuousMap := n • f.toContinuousMap
      map_bounded' := by simpa [coe_nsmulRec] using (nsmulRec n f).map_bounded' }

@[to_additive existing instSMulNat]
instance instPow [Monoid R] [BoundedMul R] [ContinuousMul R] : Pow (α →ᵇ R) ℕ where
  pow f n :=
    { toFun := fun x ↦ (f x) ^ n
      continuous_toFun := f.continuous.pow n
      map_bounded' := by
        obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp <| isBounded_pow (isBounded_range f) n
        exact ⟨C, fun x y ↦ hC (by simp) (by simp)⟩ }

@[to_additive]
theorem coe_pow [Monoid R] [BoundedMul R] [ContinuousMul R] (n : ℕ) (f : α →ᵇ R) :
    ⇑(f ^ n) = (⇑f) ^ n := rfl

@[to_additive (attr := simp)]
theorem pow_apply [Monoid R] [BoundedMul R] [ContinuousMul R] (n : ℕ) (f : α →ᵇ R) (x : α) :
    (f ^ n) x = f x ^ n := rfl

@[to_additive]
instance instMonoid [Monoid R] [BoundedMul R] [ContinuousMul R] :
    Monoid (α →ᵇ R) :=
  Injective.monoid _ DFunLike.coe_injective' rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[to_additive]
instance instCommMonoid [CommMonoid R] [BoundedMul R] [ContinuousMul R] :
    CommMonoid (α →ᵇ R) where
  __ := instMonoid
  mul_comm f g := by ext x; simp [mul_apply, mul_comm]

@[to_additive]
instance instMulOneClass [MulOneClass R] [BoundedMul R] [ContinuousMul R] : MulOneClass (α →ᵇ R) :=
  DFunLike.coe_injective.mulOneClass _ coe_one coe_mul

/-- Composition on the left by a (lipschitz-continuous) homomorphism of topological monoids, as a
`MonoidHom`. Similar to `MonoidHom.compLeftContinuous`. -/
@[to_additive (attr := simps)
/-- Composition on the left by a (lipschitz-continuous) homomorphism of topological `AddMonoid`s,
as a `AddMonoidHom`. Similar to `AddMonoidHom.compLeftContinuous`. -/]
protected def _root_.MonoidHom.compLeftContinuousBounded (α : Type*)
    [TopologicalSpace α] [PseudoMetricSpace β] [Monoid β] [BoundedMul β] [ContinuousMul β]
    [PseudoMetricSpace γ] [Monoid γ] [BoundedMul γ] [ContinuousMul γ]
    (g : β →* γ) {C : NNReal} (hg : LipschitzWith C g) :
    (α →ᵇ β) →* (α →ᵇ γ) where
  toFun f := f.comp g hg
  map_one' := ext fun _ ↦ g.map_one
  map_mul' _ _ := ext fun _ ↦ g.map_mul _ _

end mul

section add

variable [TopologicalSpace α] [PseudoMetricSpace β]
variable {C : ℝ}

@[simp]
theorem mkOfCompact_add [CompactSpace α] [Add β] [BoundedAdd β] [ContinuousAdd β] (f g : C(α, β)) :
    mkOfCompact (f + g) = mkOfCompact f + mkOfCompact g := rfl

theorem add_compContinuous [Add β] [BoundedAdd β] [ContinuousAdd β] [TopologicalSpace γ]
    (f g : α →ᵇ β) (h : C(γ, α)) :
    (g + f).compContinuous h = g.compContinuous h + f.compContinuous h := rfl

/-- Coercion of a `NormedAddGroupHom` is an `AddMonoidHom`. Similar to `AddMonoidHom.coeFn`. -/
@[simps]
def coeFnAddHom [AddMonoid β] [BoundedAdd β] [ContinuousAdd β] : (α →ᵇ β) →+ α → β where
  toFun := (⇑)
  map_zero' := coe_zero
  map_add' := coe_add

variable (α β)

/-- The additive map forgetting that a bounded continuous function is bounded. -/
@[simps]
def toContinuousMapAddHom [AddMonoid β] [BoundedAdd β] [ContinuousAdd β] : (α →ᵇ β) →+ C(α, β) where
  toFun := toContinuousMap
  map_zero' := rfl
  map_add' := by
    intros
    ext
    simp

end add

section comm_add

variable [TopologicalSpace α]
variable [PseudoMetricSpace β] [AddCommMonoid β] [BoundedAdd β] [ContinuousAdd β]

@[simp]
theorem coe_sum {ι : Type*} (s : Finset ι) (f : ι → α →ᵇ β) :
    ⇑(∑ i ∈ s, f i) = ∑ i ∈ s, (f i : α → β) :=
  map_sum coeFnAddHom f s

theorem sum_apply {ι : Type*} (s : Finset ι) (f : ι → α →ᵇ β) (a : α) :
    (∑ i ∈ s, f i) a = ∑ i ∈ s, f i a := by simp

end comm_add

section LipschitzAdd

/- In this section, if `β` is an `AddMonoid` whose addition operation is Lipschitz, then we show
that the space of bounded continuous functions from `α` to `β` inherits a topological `AddMonoid`
structure, by using pointwise operations and checking that they are compatible with the uniform
distance.

Implementation note: The material in this section could have been written for `LipschitzMul`
and transported by `@[to_additive]`. We choose not to do this because this causes a few lemma
names (for example, `coe_mul`) to conflict with later lemma names for normed rings; this is only a
trivial inconvenience, but in any case there are no obvious applications of the multiplicative
version. -/

variable [TopologicalSpace α] [PseudoMetricSpace β] [AddMonoid β] [LipschitzAdd β]
variable (f g : α →ᵇ β) {x : α} {C : ℝ}

instance instLipschitzAdd : LipschitzAdd (α →ᵇ β) where
  lipschitz_add :=
    ⟨LipschitzAdd.C β, by
      have C_nonneg := (LipschitzAdd.C β).coe_nonneg
      rw [lipschitzWith_iff_dist_le_mul]
      rintro ⟨f₁, g₁⟩ ⟨f₂, g₂⟩
      rw [dist_le (mul_nonneg C_nonneg dist_nonneg)]
      intro x
      refine le_trans (lipschitz_with_lipschitz_const_add ⟨f₁ x, g₁ x⟩ ⟨f₂ x, g₂ x⟩) ?_
      gcongr
      apply max_le_max <;> exact dist_coe_le_dist x⟩

end LipschitzAdd

section sub

variable [TopologicalSpace α]
variable {R : Type*} [PseudoMetricSpace R] [Sub R] [BoundedSub R] [ContinuousSub R]
variable (f g : α →ᵇ R)

/-- The pointwise difference of two bounded continuous functions is again bounded continuous. -/
instance instSub : Sub (α →ᵇ R) where
  sub f g :=
    { toFun := fun x ↦ (f x - g x),
      map_bounded' := sub_bounded_of_bounded_of_bounded f.map_bounded' g.map_bounded' }

theorem sub_apply {x : α} : (f - g) x = f x - g x := rfl

@[simp]
theorem coe_sub : ⇑(f - g) = f - g := rfl

end sub

section casts

variable [TopologicalSpace α] {β : Type*} [PseudoMetricSpace β]

instance [NatCast β] : NatCast (α →ᵇ β) := ⟨fun n ↦ BoundedContinuousFunction.const _ n⟩

@[simp]
theorem natCast_apply [NatCast β] (n : ℕ) (x : α) : (n : α →ᵇ β) x = n := rfl

instance [IntCast β] : IntCast (α →ᵇ β) := ⟨fun m ↦ BoundedContinuousFunction.const _ m⟩

@[simp]
theorem intCast_apply [IntCast β] (m : ℤ) (x : α) : (m : α →ᵇ β) x = m := rfl

end casts

instance instSemiring {R : Type*} [TopologicalSpace α] [PseudoMetricSpace R]
    [Semiring R] [BoundedMul R] [ContinuousMul R] [BoundedAdd R] [ContinuousAdd R] :
    Semiring (α →ᵇ R) :=
  Injective.semiring _ DFunLike.coe_injective'
    rfl rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)

section IsBoundedSMul

/-!
### `IsBoundedSMul` (in particular, topological module) structure

In this section, if `β` is a metric space and a `𝕜`-module whose addition and scalar multiplication
are compatible with the metric structure, then we show that the space of bounded continuous
functions from `α` to `β` inherits a so-called `IsBoundedSMul` structure (in particular, a
`ContinuousMul` structure, which is the mathlib formulation of being a topological module), by
using pointwise operations and checking that they are compatible with the uniform distance. -/


variable {𝕜 : Type*} [PseudoMetricSpace 𝕜] [TopologicalSpace α] [PseudoMetricSpace β]

section SMul

variable [Zero 𝕜] [Zero β] [SMul 𝕜 β] [IsBoundedSMul 𝕜 β]

instance instSMul : SMul 𝕜 (α →ᵇ β) where
  smul c f :=
    { toContinuousMap := c • f.toContinuousMap
      map_bounded' :=
        let ⟨b, hb⟩ := f.bounded
        ⟨dist c 0 * b, fun x y ↦ by
          refine (dist_smul_pair c (f x) (f y)).trans ?_
          gcongr
          apply hb⟩ }

@[simp]
theorem coe_smul (c : 𝕜) (f : α →ᵇ β) : ⇑(c • f) = fun x ↦ c • f x := rfl

theorem smul_apply (c : 𝕜) (f : α →ᵇ β) (x : α) : (c • f) x = c • f x := rfl

instance instIsScalarTower {𝕜' : Type*} [PseudoMetricSpace 𝕜'] [Zero 𝕜'] [SMul 𝕜' β]
    [IsBoundedSMul 𝕜' β] [SMul 𝕜' 𝕜] [IsScalarTower 𝕜' 𝕜 β] :
    IsScalarTower 𝕜' 𝕜 (α →ᵇ β) where
  smul_assoc _ _ _ := ext fun _ ↦ smul_assoc ..

instance instSMulCommClass {𝕜' : Type*} [PseudoMetricSpace 𝕜'] [Zero 𝕜'] [SMul 𝕜' β]
    [IsBoundedSMul 𝕜' β] [SMulCommClass 𝕜' 𝕜 β] :
    SMulCommClass 𝕜' 𝕜 (α →ᵇ β) where
  smul_comm _ _ _ := ext fun _ ↦ smul_comm ..

instance instIsCentralScalar [SMul 𝕜ᵐᵒᵖ β] [IsCentralScalar 𝕜 β] : IsCentralScalar 𝕜 (α →ᵇ β) where
  op_smul_eq_smul _ _ := ext fun _ ↦ op_smul_eq_smul _ _

instance instIsBoundedSMul : IsBoundedSMul 𝕜 (α →ᵇ β) where
  dist_smul_pair' c f₁ f₂ := by
    rw [dist_le (mul_nonneg dist_nonneg dist_nonneg)]
    intro x
    refine (dist_smul_pair c (f₁ x) (f₂ x)).trans ?_
    gcongr
    apply dist_coe_le_dist
  dist_pair_smul' c₁ c₂ f := by
    rw [dist_le (by positivity)]
    intro x
    refine (dist_pair_smul c₁ c₂ (f x)).trans ?_
    gcongr
    apply dist_coe_le_dist (g := 0)

end SMul

section MulAction

variable [MonoidWithZero 𝕜] [Zero β] [MulAction 𝕜 β] [IsBoundedSMul 𝕜 β]

instance instMulAction : MulAction 𝕜 (α →ᵇ β) :=
  DFunLike.coe_injective.mulAction _ coe_smul

end MulAction

section DistribMulAction

variable [MonoidWithZero 𝕜] [AddMonoid β] [DistribMulAction 𝕜 β] [IsBoundedSMul 𝕜 β]
variable [BoundedAdd β] [ContinuousAdd β]

instance instDistribMulAction : DistribMulAction 𝕜 (α →ᵇ β) :=
  DFunLike.coe_injective.distribMulAction ⟨⟨_, coe_zero⟩, coe_add⟩ coe_smul

end DistribMulAction

section Module

variable [Semiring 𝕜] [AddCommMonoid β] [Module 𝕜 β] [IsBoundedSMul 𝕜 β]
variable {f g : α →ᵇ β} {x : α} {C : ℝ}
variable [BoundedAdd β] [ContinuousAdd β]

instance instModule : Module 𝕜 (α →ᵇ β) :=
  DFunLike.coe_injective.module _ ⟨⟨_, coe_zero⟩, coe_add⟩  coe_smul

variable (𝕜)

/-- The evaluation at a point, as a continuous linear map from `α →ᵇ β` to `β`. -/
@[simps]
def evalCLM (x : α) : (α →ᵇ β) →L[𝕜] β where
  toFun f := f x
  map_add' _ _ := add_apply _ _ _
  map_smul' _ _ := smul_apply _ _ _

variable (α β)

/-- The linear map forgetting that a bounded continuous function is bounded. -/
@[simps]
def toContinuousMapLinearMap : (α →ᵇ β) →ₗ[𝕜] C(α, β) where
  toFun := toContinuousMap
  map_smul' _ _ := rfl
  map_add' _ _ := rfl

end Module

end IsBoundedSMul

theorem NNReal.upper_bound {α : Type*} [TopologicalSpace α] (f : α →ᵇ ℝ≥0) (x : α) :
    f x ≤ nndist f 0 := by
  have key : nndist (f x) ((0 : α →ᵇ ℝ≥0) x) ≤ nndist f 0 := @dist_coe_le_dist α ℝ≥0 _ _ f 0 x
  simp only [coe_zero, Pi.zero_apply] at key
  rwa [NNReal.nndist_zero_eq_val' (f x)] at key

end BoundedContinuousFunction
