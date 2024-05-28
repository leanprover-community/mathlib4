/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
import Mathlib.Analysis.NormedSpace.OperatorNorm.Bilinear
import Mathlib.Analysis.NormedSpace.OperatorNorm.NNNorm

/-!
# Operators on complete normed spaces

This file contains statements about norms of operators on complete normed spaces, such as a
version of the Banach-Alaoglu theorem (`ContinuousLinearMap.isCompact_image_coe_closedBall`).
-/

suppress_compilation

-- make instances connecting normed things and algebra have higher priority
open scoped AlgebraNormedInstances

open Bornology Metric Set Real
open Filter hiding map_smul
open scoped Classical NNReal Topology Uniformity

-- the `ₗ` subscript variables are for special cases about linear (as opposed to semilinear) maps
variable {𝕜 𝕜₂ 𝕜₃ E Eₗ F Fₗ G Gₗ 𝓕 : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NormedAddCommGroup Fₗ]

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G] [NormedSpace 𝕜 Fₗ] (c : 𝕜)
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} (f g : E →SL[σ₁₂] F) (x y z : E)

namespace ContinuousLinearMap

section Completeness

variable {E' : Type*} [SeminormedAddCommGroup E'] [NormedSpace 𝕜 E'] [RingHomIsometric σ₁₂]

/-- Construct a bundled continuous (semi)linear map from a map `f : E → F` and a proof of the fact
that it belongs to the closure of the image of a bounded set `s : Set (E →SL[σ₁₂] F)` under coercion
to function. Coercion to function of the result is definitionally equal to `f`. -/
@[simps! (config := .asFn) apply]
def ofMemClosureImageCoeBounded (f : E' → F) {s : Set (E' →SL[σ₁₂] F)} (hs : IsBounded s)
    (hf : f ∈ closure (((↑) : (E' →SL[σ₁₂] F) → E' → F) '' s)) : E' →SL[σ₁₂] F := by
  -- `f` is a linear map due to `linearMapOfMemClosureRangeCoe`
  refine' (linearMapOfMemClosureRangeCoe f _).mkContinuousOfExistsBound _
  · refine' closure_mono (image_subset_iff.2 fun g _ => _) hf
    exact ⟨g, rfl⟩
  · -- We need to show that `f` has bounded norm. Choose `C` such that `‖g‖ ≤ C` for all `g ∈ s`.
    rcases isBounded_iff_forall_norm_le.1 hs with ⟨C, hC⟩
    -- Then `‖g x‖ ≤ C * ‖x‖` for all `g ∈ s`, `x : E`, hence `‖f x‖ ≤ C * ‖x‖` for all `x`.
    have : ∀ x, IsClosed { g : E' → F | ‖g x‖ ≤ C * ‖x‖ } := fun x =>
      isClosed_Iic.preimage (@continuous_apply E' (fun _ => F) _ x).norm
    refine' ⟨C, fun x => (this x).closure_subset_iff.2 (image_subset_iff.2 fun g hg => _) hf⟩
    exact g.le_of_opNorm_le (hC _ hg) _
#align continuous_linear_map.of_mem_closure_image_coe_bounded ContinuousLinearMap.ofMemClosureImageCoeBounded

/-- Let `f : E → F` be a map, let `g : α → E →SL[σ₁₂] F` be a family of continuous (semi)linear maps
that takes values in a bounded set and converges to `f` pointwise along a nontrivial filter. Then
`f` is a continuous (semi)linear map. -/
@[simps! (config := .asFn) apply]
def ofTendstoOfBoundedRange {α : Type*} {l : Filter α} [l.NeBot] (f : E' → F)
    (g : α → E' →SL[σ₁₂] F) (hf : Tendsto (fun a x => g a x) l (𝓝 f))
    (hg : IsBounded (Set.range g)) : E' →SL[σ₁₂] F :=
  ofMemClosureImageCoeBounded f hg <| mem_closure_of_tendsto hf <|
    eventually_of_forall fun _ => mem_image_of_mem _ <| Set.mem_range_self _
#align continuous_linear_map.of_tendsto_of_bounded_range ContinuousLinearMap.ofTendstoOfBoundedRange

/-- If a Cauchy sequence of continuous linear map converges to a continuous linear map pointwise,
then it converges to the same map in norm. This lemma is used to prove that the space of continuous
linear maps is complete provided that the codomain is a complete space. -/
theorem tendsto_of_tendsto_pointwise_of_cauchySeq {f : ℕ → E' →SL[σ₁₂] F} {g : E' →SL[σ₁₂] F}
    (hg : Tendsto (fun n x => f n x) atTop (𝓝 g)) (hf : CauchySeq f) : Tendsto f atTop (𝓝 g) := by
  /- Since `f` is a Cauchy sequence, there exists `b → 0` such that `‖f n - f m‖ ≤ b N` for any
    `m, n ≥ N`. -/
  rcases cauchySeq_iff_le_tendsto_0.1 hf with ⟨b, hb₀, hfb, hb_lim⟩
  -- Since `b → 0`, it suffices to show that `‖f n x - g x‖ ≤ b n * ‖x‖` for all `n` and `x`.
  suffices ∀ n x, ‖f n x - g x‖ ≤ b n * ‖x‖ from
    tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero (fun n => norm_nonneg _) (fun n => opNorm_le_bound _ (hb₀ n) (this n)) hb_lim)
  intro n x
  -- Note that `f m x → g x`, hence `‖f n x - f m x‖ → ‖f n x - g x‖` as `m → ∞`
  have : Tendsto (fun m => ‖f n x - f m x‖) atTop (𝓝 ‖f n x - g x‖) :=
    (tendsto_const_nhds.sub <| tendsto_pi_nhds.1 hg _).norm
  -- Thus it suffices to verify `‖f n x - f m x‖ ≤ b n * ‖x‖` for `m ≥ n`.
  refine le_of_tendsto this (eventually_atTop.2 ⟨n, fun m hm => ?_⟩)
  -- This inequality follows from `‖f n - f m‖ ≤ b n`.
  exact (f n - f m).le_of_opNorm_le (hfb _ _ _ le_rfl hm) _
#align continuous_linear_map.tendsto_of_tendsto_pointwise_of_cauchy_seq ContinuousLinearMap.tendsto_of_tendsto_pointwise_of_cauchySeq

/-- If the target space is complete, the space of continuous linear maps with its norm is also
complete. This works also if the source space is seminormed. -/
instance [CompleteSpace F] : CompleteSpace (E' →SL[σ₁₂] F) := by
  -- We show that every Cauchy sequence converges.
  refine' Metric.complete_of_cauchySeq_tendsto fun f hf => _
  -- The evaluation at any point `v : E` is Cauchy.
  have cau : ∀ v, CauchySeq fun n => f n v := fun v => hf.map (lipschitz_apply v).uniformContinuous
  -- We assemble the limits points of those Cauchy sequences
  -- (which exist as `F` is complete)
  -- into a function which we call `G`.
  choose G hG using fun v => cauchySeq_tendsto_of_complete (cau v)
  -- Next, we show that this `G` is a continuous linear map.
  -- This is done in `ContinuousLinearMap.ofTendstoOfBoundedRange`.
  set Glin : E' →SL[σ₁₂] F :=
    ofTendstoOfBoundedRange _ _ (tendsto_pi_nhds.mpr hG) hf.isBounded_range
  -- Finally, `f n` converges to `Glin` in norm because of
  -- `ContinuousLinearMap.tendsto_of_tendsto_pointwise_of_cauchySeq`
  exact ⟨Glin, tendsto_of_tendsto_pointwise_of_cauchySeq (tendsto_pi_nhds.2 hG) hf⟩

/-- Let `s` be a bounded set in the space of continuous (semi)linear maps `E →SL[σ] F` taking values
in a proper space. Then `s` interpreted as a set in the space of maps `E → F` with topology of
pointwise convergence is precompact: its closure is a compact set. -/
theorem isCompact_closure_image_coe_of_bounded [ProperSpace F] {s : Set (E' →SL[σ₁₂] F)}
    (hb : IsBounded s) : IsCompact (closure (((↑) : (E' →SL[σ₁₂] F) → E' → F) '' s)) :=
  have : ∀ x, IsCompact (closure (apply' F σ₁₂ x '' s)) := fun x =>
    ((apply' F σ₁₂ x).lipschitz.isBounded_image hb).isCompact_closure
  (isCompact_pi_infinite this).closure_of_subset
    (image_subset_iff.2 fun _ hg _ => subset_closure <| mem_image_of_mem _ hg)
#align continuous_linear_map.is_compact_closure_image_coe_of_bounded ContinuousLinearMap.isCompact_closure_image_coe_of_bounded

/-- Let `s` be a bounded set in the space of continuous (semi)linear maps `E →SL[σ] F` taking values
in a proper space. If `s` interpreted as a set in the space of maps `E → F` with topology of
pointwise convergence is closed, then it is compact.

TODO: reformulate this in terms of a type synonym with the right topology. -/
theorem isCompact_image_coe_of_bounded_of_closed_image [ProperSpace F] {s : Set (E' →SL[σ₁₂] F)}
    (hb : IsBounded s) (hc : IsClosed (((↑) : (E' →SL[σ₁₂] F) → E' → F) '' s)) :
    IsCompact (((↑) : (E' →SL[σ₁₂] F) → E' → F) '' s) :=
  hc.closure_eq ▸ isCompact_closure_image_coe_of_bounded hb
#align continuous_linear_map.is_compact_image_coe_of_bounded_of_closed_image ContinuousLinearMap.isCompact_image_coe_of_bounded_of_closed_image

/-- If a set `s` of semilinear functions is bounded and is closed in the weak-* topology, then its
image under coercion to functions `E → F` is a closed set. We don't have a name for `E →SL[σ] F`
with weak-* topology in `mathlib`, so we use an equivalent condition (see `isClosed_induced_iff'`).

TODO: reformulate this in terms of a type synonym with the right topology. -/
theorem isClosed_image_coe_of_bounded_of_weak_closed {s : Set (E' →SL[σ₁₂] F)} (hb : IsBounded s)
    (hc : ∀ f : E' →SL[σ₁₂] F,
      (⇑f : E' → F) ∈ closure (((↑) : (E' →SL[σ₁₂] F) → E' → F) '' s) → f ∈ s) :
    IsClosed (((↑) : (E' →SL[σ₁₂] F) → E' → F) '' s) :=
  isClosed_of_closure_subset fun f hf =>
    ⟨ofMemClosureImageCoeBounded f hb hf, hc (ofMemClosureImageCoeBounded f hb hf) hf, rfl⟩
#align continuous_linear_map.is_closed_image_coe_of_bounded_of_weak_closed ContinuousLinearMap.isClosed_image_coe_of_bounded_of_weak_closed

/-- If a set `s` of semilinear functions is bounded and is closed in the weak-* topology, then its
image under coercion to functions `E → F` is a compact set. We don't have a name for `E →SL[σ] F`
with weak-* topology in `mathlib`, so we use an equivalent condition (see `isClosed_induced_iff'`).
-/
theorem isCompact_image_coe_of_bounded_of_weak_closed [ProperSpace F] {s : Set (E' →SL[σ₁₂] F)}
    (hb : IsBounded s) (hc : ∀ f : E' →SL[σ₁₂] F,
      (⇑f : E' → F) ∈ closure (((↑) : (E' →SL[σ₁₂] F) → E' → F) '' s) → f ∈ s) :
    IsCompact (((↑) : (E' →SL[σ₁₂] F) → E' → F) '' s) :=
  isCompact_image_coe_of_bounded_of_closed_image hb <|
    isClosed_image_coe_of_bounded_of_weak_closed hb hc
#align continuous_linear_map.is_compact_image_coe_of_bounded_of_weak_closed ContinuousLinearMap.isCompact_image_coe_of_bounded_of_weak_closed

/-- A closed ball is closed in the weak-* topology. We don't have a name for `E →SL[σ] F` with
weak-* topology in `mathlib`, so we use an equivalent condition (see `isClosed_induced_iff'`). -/
theorem is_weak_closed_closedBall (f₀ : E' →SL[σ₁₂] F) (r : ℝ) ⦃f : E' →SL[σ₁₂] F⦄
    (hf : ⇑f ∈ closure (((↑) : (E' →SL[σ₁₂] F) → E' → F) '' closedBall f₀ r)) :
    f ∈ closedBall f₀ r := by
  have hr : 0 ≤ r := nonempty_closedBall.1 (closure_nonempty_iff.1 ⟨_, hf⟩).of_image
  refine mem_closedBall_iff_norm.2 (opNorm_le_bound _ hr fun x => ?_)
  have : IsClosed { g : E' → F | ‖g x - f₀ x‖ ≤ r * ‖x‖ } :=
    isClosed_Iic.preimage ((@continuous_apply E' (fun _ => F) _ x).sub continuous_const).norm
  refine this.closure_subset_iff.2 (image_subset_iff.2 fun g hg => ?_) hf
  exact (g - f₀).le_of_opNorm_le (mem_closedBall_iff_norm.1 hg) _
#align continuous_linear_map.is_weak_closed_closed_ball ContinuousLinearMap.is_weak_closed_closedBall

/-- The set of functions `f : E → F` that represent continuous linear maps `f : E →SL[σ₁₂] F`
at distance `≤ r` from `f₀ : E →SL[σ₁₂] F` is closed in the topology of pointwise convergence.
This is one of the key steps in the proof of the **Banach-Alaoglu** theorem. -/
theorem isClosed_image_coe_closedBall (f₀ : E →SL[σ₁₂] F) (r : ℝ) :
    IsClosed (((↑) : (E →SL[σ₁₂] F) → E → F) '' closedBall f₀ r) :=
  isClosed_image_coe_of_bounded_of_weak_closed isBounded_closedBall (is_weak_closed_closedBall f₀ r)
#align continuous_linear_map.is_closed_image_coe_closed_ball ContinuousLinearMap.isClosed_image_coe_closedBall

/-- **Banach-Alaoglu** theorem. The set of functions `f : E → F` that represent continuous linear
maps `f : E →SL[σ₁₂] F` at distance `≤ r` from `f₀ : E →SL[σ₁₂] F` is compact in the topology of
pointwise convergence. Other versions of this theorem can be found in
`Analysis.NormedSpace.WeakDual`. -/
theorem isCompact_image_coe_closedBall [ProperSpace F] (f₀ : E →SL[σ₁₂] F) (r : ℝ) :
    IsCompact (((↑) : (E →SL[σ₁₂] F) → E → F) '' closedBall f₀ r) :=
  isCompact_image_coe_of_bounded_of_weak_closed isBounded_closedBall <|
    is_weak_closed_closedBall f₀ r
#align continuous_linear_map.is_compact_image_coe_closed_ball ContinuousLinearMap.isCompact_image_coe_closedBall

end Completeness

section UniformlyExtend

variable [CompleteSpace F] (e : E →L[𝕜] Fₗ) (h_dense : DenseRange e)

section

variable (h_e : UniformInducing e)

/-- Extension of a continuous linear map `f : E →SL[σ₁₂] F`, with `E` a normed space and `F` a
complete normed space, along a uniform and dense embedding `e : E →L[𝕜] Fₗ`.  -/
def extend : Fₗ →SL[σ₁₂] F :=
  -- extension of `f` is continuous
  have cont := (uniformContinuous_uniformly_extend h_e h_dense f.uniformContinuous).continuous
  -- extension of `f` agrees with `f` on the domain of the embedding `e`
  have eq := uniformly_extend_of_ind h_e h_dense f.uniformContinuous
  { toFun := (h_e.denseInducing h_dense).extend f
    map_add' := by
      refine' h_dense.induction_on₂ _ _
      · exact isClosed_eq (cont.comp continuous_add)
          ((cont.comp continuous_fst).add (cont.comp continuous_snd))
      · intro x y
        simp only [eq, ← e.map_add]
        exact f.map_add _ _
    map_smul' := fun k => by
      refine' fun b => h_dense.induction_on b _ _
      · exact isClosed_eq (cont.comp (continuous_const_smul _))
          ((continuous_const_smul _).comp cont)
      · intro x
        rw [← map_smul]
        simp only [eq]
        exact ContinuousLinearMap.map_smulₛₗ _ _ _
    cont }
#align continuous_linear_map.extend ContinuousLinearMap.extend

-- Porting note: previously `(h_e.denseInducing h_dense)` was inferred.
@[simp]
theorem extend_eq (x : E) : extend f e h_dense h_e (e x) = f x :=
  DenseInducing.extend_eq (h_e.denseInducing h_dense) f.cont _
#align continuous_linear_map.extend_eq ContinuousLinearMap.extend_eq

theorem extend_unique (g : Fₗ →SL[σ₁₂] F) (H : g.comp e = f) : extend f e h_dense h_e = g :=
  ContinuousLinearMap.coeFn_injective <|
    uniformly_extend_unique h_e h_dense (ContinuousLinearMap.ext_iff.1 H) g.continuous
#align continuous_linear_map.extend_unique ContinuousLinearMap.extend_unique

@[simp]
theorem extend_zero : extend (0 : E →SL[σ₁₂] F) e h_dense h_e = 0 :=
  extend_unique _ _ _ _ _ (zero_comp _)
#align continuous_linear_map.extend_zero ContinuousLinearMap.extend_zero

end

section

variable {N : ℝ≥0} (h_e : ∀ x, ‖x‖ ≤ N * ‖e x‖) [RingHomIsometric σ₁₂]

/-- If a dense embedding `e : E →L[𝕜] G` expands the norm by a constant factor `N⁻¹`, then the
norm of the extension of `f` along `e` is bounded by `N * ‖f‖`. -/
theorem opNorm_extend_le :
    ‖f.extend e h_dense (uniformEmbedding_of_bound _ h_e).toUniformInducing‖ ≤ N * ‖f‖ := by
  -- Add `opNorm_le_of_dense`?
  refine opNorm_le_bound _ ?_ (isClosed_property h_dense (isClosed_le ?_ ?_) fun x ↦ ?_)
  · cases le_total 0 N with
    | inl hN => exact mul_nonneg hN (norm_nonneg _)
    | inr hN =>
      have : Unique E := ⟨⟨0⟩, fun x ↦ norm_le_zero_iff.mp <|
        (h_e x).trans (mul_nonpos_of_nonpos_of_nonneg hN (norm_nonneg _))⟩
      obtain rfl : f = 0 := Subsingleton.elim ..
      simp
  · exact (cont _).norm
  · exact continuous_const.mul continuous_norm
  · rw [extend_eq]
    calc
      ‖f x‖ ≤ ‖f‖ * ‖x‖ := le_opNorm _ _
      _ ≤ ‖f‖ * (N * ‖e x‖) := mul_le_mul_of_nonneg_left (h_e x) (norm_nonneg _)
      _ ≤ N * ‖f‖ * ‖e x‖ := by rw [mul_comm ↑N ‖f‖, mul_assoc]
#align continuous_linear_map.op_norm_extend_le ContinuousLinearMap.opNorm_extend_le

@[deprecated] alias op_norm_extend_le := opNorm_extend_le -- deprecated on 2024-02-02

end

end UniformlyExtend

end ContinuousLinearMap
