/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.RCLike.Lemmas

/-!
# The orthogonal projection

Given a nonempty subspace `K` of an inner product space `E` such that `K`
admits an orthogonal projection, this file constructs
`K.orthogonalProjection : E →L[𝕜] K`, the orthogonal projection of `E` onto `K`. This map
satisfies: for any point `u` in `E`, the point `v = K.orthogonalProjection u` in `K` minimizes the
distance `‖u - v‖` to `u`.

This file also defines `K.starProjection : E →L[𝕜] E` which is the
orthogonal projection of `E` onto `K` but as a map from `E` to `E` instead of `E` to `K`.

Basic API for `orthogonalProjection` and `starProjection` is developed.

## References

The orthogonal projection construction is adapted from
* [Clément & Martin, *The Lax-Milgram Theorem. A detailed proof to be formalized in Coq*]
* [Clément & Martin, *A Coq formal proof of the Lax–Milgram theorem*]

The Coq code is available at the following address: <http://www.lri.fr/~sboldo/elfic/index.html>
-/

@[expose] public section

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
local notation "absR" => @abs ℝ _ _

namespace Submodule

/-- A subspace `K : Submodule 𝕜 E` has an orthogonal projection if every vector `v : E` admits an
orthogonal projection to `K`. -/
class HasOrthogonalProjection (K : Submodule 𝕜 E) : Prop where
  exists_orthogonal (v : E) : ∃ w ∈ K, v - w ∈ Kᗮ

variable (K : Submodule 𝕜 E)

instance (priority := 100) HasOrthogonalProjection.ofCompleteSpace [CompleteSpace K] :
    K.HasOrthogonalProjection where
  exists_orthogonal v := by
    rcases K.exists_norm_eq_iInf_of_complete_subspace (completeSpace_coe_iff_isComplete.mp ‹_›) v
      with ⟨w, hwK, hw⟩
    refine ⟨w, hwK, (K.mem_orthogonal' _).2 ?_⟩
    rwa [← K.norm_eq_iInf_iff_inner_eq_zero hwK]

instance [K.HasOrthogonalProjection] : Kᗮ.HasOrthogonalProjection where
  exists_orthogonal v := by
    rcases HasOrthogonalProjection.exists_orthogonal (K := K) v with ⟨w, hwK, hw⟩
    refine ⟨_, hw, ?_⟩
    rw [sub_sub_cancel]
    exact K.le_orthogonal_orthogonal hwK

instance HasOrthogonalProjection.map_linearIsometryEquiv [K.HasOrthogonalProjection]
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E') :
    (K.map (f.toLinearEquiv : E →ₗ[𝕜] E')).HasOrthogonalProjection where
  exists_orthogonal v := by
    rcases HasOrthogonalProjection.exists_orthogonal (K := K) (f.symm v) with ⟨w, hwK, hw⟩
    refine ⟨f w, Submodule.mem_map_of_mem hwK, Set.forall_mem_image.2 fun u hu ↦ ?_⟩
    erw [← f.symm.inner_map_map, f.symm_apply_apply, map_sub, f.symm_apply_apply, hw u hu]

instance HasOrthogonalProjection.map_linearIsometryEquiv' [K.HasOrthogonalProjection]
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E') :
    (K.map (f.toLinearIsometry : E →ₗ[𝕜] E')).HasOrthogonalProjection :=
  HasOrthogonalProjection.map_linearIsometryEquiv K f

instance : (⊤ : Submodule 𝕜 E).HasOrthogonalProjection := ⟨fun v ↦ ⟨v, trivial, by simp⟩⟩

instance (K : ClosedSubmodule 𝕜 E) [CompleteSpace E] : K.HasOrthogonalProjection := by
  letI := K.isClosed'
  infer_instance

noncomputable section

section orthogonalProjection

variable [K.HasOrthogonalProjection]

/-- The orthogonal projection onto a complete subspace, as an
unbundled function. This definition is only intended for use in
setting up the bundled version `orthogonalProjection` and should not
be used once that is defined. -/
def orthogonalProjectionFn (v : E) :=
  (HasOrthogonalProjection.exists_orthogonal (K := K) v).choose

variable {K}

/-- The unbundled orthogonal projection is in the given subspace.
This lemma is only intended for use in setting up the bundled version
and should not be used once that is defined. -/
theorem orthogonalProjectionFn_mem (v : E) : K.orthogonalProjectionFn v ∈ K :=
  (HasOrthogonalProjection.exists_orthogonal (K := K) v).choose_spec.left

/-- The characterization of the unbundled orthogonal projection.  This
lemma is only intended for use in setting up the bundled version
and should not be used once that is defined. -/
theorem orthogonalProjectionFn_inner_eq_zero (v : E) :
    ∀ w ∈ K, ⟪v - K.orthogonalProjectionFn v, w⟫ = 0 :=
  (K.mem_orthogonal' _).1 (HasOrthogonalProjection.exists_orthogonal (K := K) v).choose_spec.right

/-- The unbundled orthogonal projection is the unique point in `K`
with the orthogonality property. This lemma is only intended for use
in setting up the bundled version and should not be used once that is
defined. -/
theorem eq_orthogonalProjectionFn_of_mem_of_inner_eq_zero {u v : E} (hvm : v ∈ K)
    (hvo : ∀ w ∈ K, ⟪u - v, w⟫ = 0) : K.orthogonalProjectionFn u = v := by
  rw [← sub_eq_zero, ← @inner_self_eq_zero 𝕜]
  have hvs : K.orthogonalProjectionFn u - v ∈ K :=
    Submodule.sub_mem K (orthogonalProjectionFn_mem u) hvm
  have huo : ⟪u - K.orthogonalProjectionFn u, K.orthogonalProjectionFn u - v⟫ = 0 :=
    orthogonalProjectionFn_inner_eq_zero u _ hvs
  have huv : ⟪u - v, K.orthogonalProjectionFn u - v⟫ = 0 := hvo _ hvs
  have houv : ⟪u - v - (u - K.orthogonalProjectionFn u), K.orthogonalProjectionFn u - v⟫ = 0 := by
    rw [inner_sub_left, huo, huv, sub_zero]
  rwa [sub_sub_sub_cancel_left] at houv

variable (K)

theorem orthogonalProjectionFn_norm_sq (v : E) :
    ‖v‖ * ‖v‖ =
      ‖v - K.orthogonalProjectionFn v‖ * ‖v - K.orthogonalProjectionFn v‖ +
        ‖K.orthogonalProjectionFn v‖ * ‖K.orthogonalProjectionFn v‖ := by
  set p := K.orthogonalProjectionFn v
  have h' : ⟪v - p, p⟫ = 0 :=
    orthogonalProjectionFn_inner_eq_zero _ _ (orthogonalProjectionFn_mem v)
  convert norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (v - p) p h' using 2 <;> simp

/-- The orthogonal projection onto a complete subspace. -/
def orthogonalProjection : E →L[𝕜] K :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟨K.orthogonalProjectionFn v, orthogonalProjectionFn_mem v⟩
      map_add' := fun x y => by
        have hm : K.orthogonalProjectionFn x + K.orthogonalProjectionFn y ∈ K :=
          Submodule.add_mem K (orthogonalProjectionFn_mem x) (orthogonalProjectionFn_mem y)
        have ho :
          ∀ w ∈ K, ⟪x + y - (K.orthogonalProjectionFn x + K.orthogonalProjectionFn y), w⟫ = 0 := by
          intro w hw
          rw [add_sub_add_comm, inner_add_left, orthogonalProjectionFn_inner_eq_zero _ w hw,
            orthogonalProjectionFn_inner_eq_zero _ w hw, add_zero]
        ext
        simp [eq_orthogonalProjectionFn_of_mem_of_inner_eq_zero hm ho]
      map_smul' := fun c x => by
        have hm : c • K.orthogonalProjectionFn x ∈ K :=
          Submodule.smul_mem K _ (orthogonalProjectionFn_mem x)
        have ho : ∀ w ∈ K, ⟪c • x - c • K.orthogonalProjectionFn x, w⟫ = 0 := by
          intro w hw
          rw [← smul_sub, inner_smul_left, orthogonalProjectionFn_inner_eq_zero _ w hw,
            mul_zero]
        ext
        simp [eq_orthogonalProjectionFn_of_mem_of_inner_eq_zero hm ho] }
    1 fun x => by
    simp only [one_mul, LinearMap.coe_mk]
    refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
    change ‖K.orthogonalProjectionFn x‖ ^ 2 ≤ ‖x‖ ^ 2
    nlinarith [K.orthogonalProjectionFn_norm_sq x]

variable {K}

@[simp]
theorem orthogonalProjectionFn_eq (v : E) :
    K.orthogonalProjectionFn v = (K.orthogonalProjection v : E) :=
  rfl

/-- The orthogonal projection onto a subspace as a map from the full space to itself,
as opposed to `Submodule.orthogonalProjection`, which maps into the subtype. This
version is important as it satisfies `IsStarProjection`. -/
def starProjection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    E →L[𝕜] E := U.subtypeL ∘L U.orthogonalProjection

lemma starProjection_apply (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (v : E) :
    U.starProjection v = U.orthogonalProjection v := rfl

@[simp]
lemma coe_orthogonalProjection_apply (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (v : E) :
     U.orthogonalProjection v = U.starProjection v := rfl

@[simp]
lemma starProjection_apply_mem (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (x : E) :
    U.starProjection x ∈ U := by
  simp only [starProjection_apply, SetLike.coe_mem]

/-- The characterization of the orthogonal projection. -/
@[simp]
theorem starProjection_inner_eq_zero (v : E) :
    ∀ w ∈ K, ⟪v - K.starProjection v, w⟫ = 0 :=
  orthogonalProjectionFn_inner_eq_zero v

/-- The difference of `v` from its orthogonal projection onto `K` is in `Kᗮ`. -/
@[simp]
theorem sub_starProjection_mem_orthogonal (v : E) : v - K.starProjection v ∈ Kᗮ := by
  intro w hw
  rw [inner_eq_zero_symm]
  exact starProjection_inner_eq_zero _ _ hw

/-- The orthogonal projection is the unique point in `K` with the
orthogonality property. -/
theorem eq_starProjection_of_mem_of_inner_eq_zero {u v : E} (hvm : v ∈ K)
    (hvo : ∀ w ∈ K, ⟪u - v, w⟫ = 0) : K.starProjection u = v :=
  eq_orthogonalProjectionFn_of_mem_of_inner_eq_zero hvm hvo

/-- A point in `K` with the orthogonality property (here characterized in terms of `Kᗮ`) must be the
orthogonal projection. -/
theorem eq_starProjection_of_mem_orthogonal {u v : E} (hv : v ∈ K)
    (hvo : u - v ∈ Kᗮ) : K.starProjection u = v :=
  eq_orthogonalProjectionFn_of_mem_of_inner_eq_zero hv <| (Submodule.mem_orthogonal' _ _).1 hvo

/-- A point in `K` with the orthogonality property (here characterized in terms of `Kᗮ`) must be the
orthogonal projection. -/
theorem eq_starProjection_of_mem_orthogonal' {u v z : E}
    (hv : v ∈ K) (hz : z ∈ Kᗮ) (hu : u = v + z) : K.starProjection u = v :=
  eq_starProjection_of_mem_orthogonal hv (by simpa [hu])

@[simp]
theorem starProjection_orthogonal_val (u : E) :
    Kᗮ.starProjection u = u - K.starProjection u :=
  eq_starProjection_of_mem_orthogonal' (sub_starProjection_mem_orthogonal _)
    (K.le_orthogonal_orthogonal (K.orthogonalProjection u).2) <| (sub_add_cancel _ _).symm

theorem orthogonalProjection_orthogonal (u : E) :
    Kᗮ.orthogonalProjection u =
      ⟨u - K.starProjection u, sub_starProjection_mem_orthogonal _⟩ :=
  Subtype.ext <| starProjection_orthogonal_val _

lemma starProjection_orthogonal (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    Uᗮ.starProjection = ContinuousLinearMap.id 𝕜 E - U.starProjection := by
  ext
  simp only [starProjection, ContinuousLinearMap.comp_apply,
    orthogonalProjection_orthogonal]
  simp

lemma starProjection_orthogonal' (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    Uᗮ.starProjection = 1 - U.starProjection := starProjection_orthogonal U

/-- The orthogonal projection of `y` on `U` minimizes the distance `‖y - x‖` for `x ∈ U`. -/
theorem starProjection_minimal {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (y : E) :
    ‖y - U.starProjection y‖ = ⨅ x : U, ‖y - x‖ := by
  rw [starProjection_apply, U.norm_eq_iInf_iff_inner_eq_zero (Submodule.coe_mem _)]
  exact starProjection_inner_eq_zero _

/-- The orthogonal projection sends elements of `K` to themselves. -/
@[simp]
theorem orthogonalProjection_mem_subspace_eq_self (v : K) : K.orthogonalProjection v = v := by
  ext
  apply eq_starProjection_of_mem_of_inner_eq_zero <;> simp

@[simp]
theorem starProjection_mem_subspace_eq_self (v : K) :
    K.starProjection v = v := by simp [starProjection_apply]

/-- A point equals its orthogonal projection if and only if it lies in the subspace. -/
theorem starProjection_eq_self_iff {v : E} : K.starProjection v = v ↔ v ∈ K := by
  refine ⟨fun h => ?_, fun h => eq_starProjection_of_mem_of_inner_eq_zero h ?_⟩
  · rw [← h]
    simp
  · simp

variable (K) in
@[simp]
lemma isIdempotentElem_starProjection : IsIdempotentElem K.starProjection :=
  ContinuousLinearMap.ext fun x ↦ starProjection_eq_self_iff.mpr <| by simp

@[simp]
lemma range_starProjection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    U.starProjection.range = U := by
  ext x
  exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ coe_mem (U.orthogonalProjection y),
    fun h ↦ ⟨x, starProjection_eq_self_iff.mpr h⟩⟩

lemma starProjection_top : (⊤ : Submodule 𝕜 E).starProjection = ContinuousLinearMap.id 𝕜 E := by
  ext
  exact starProjection_eq_self_iff.mpr trivial

lemma starProjection_top' : (⊤ : Submodule 𝕜 E).starProjection = 1 :=
  starProjection_top

@[simp]
theorem orthogonalProjection_eq_zero_iff {v : E} : K.orthogonalProjection v = 0 ↔ v ∈ Kᗮ := by
  refine ⟨fun h ↦ ?_, fun h ↦ Subtype.ext <| eq_starProjection_of_mem_orthogonal
    (zero_mem _) ?_⟩
  · rw [← sub_zero v, ← coe_zero (p := K), ← h]
    exact sub_starProjection_mem_orthogonal (K := K) v
  · simpa

@[simp]
theorem ker_orthogonalProjection : K.orthogonalProjection.ker = Kᗮ := by
  ext; exact orthogonalProjection_eq_zero_iff

open ContinuousLinearMap in
@[simp]
lemma ker_starProjection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    U.starProjection.ker = Uᗮ := by
  rw [LinearMap.IsIdempotentElem.ker_eq_range U.isIdempotentElem_starProjection.toLinearMap,
    ← range_starProjection Uᗮ, starProjection_orthogonal, coe_sub', coe_id]

theorem _root_.LinearIsometry.map_starProjection {E E' : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E →ₗᵢ[𝕜] E')
    (p : Submodule 𝕜 E) [p.HasOrthogonalProjection] [(p.map f.toLinearMap).HasOrthogonalProjection]
    (x : E) : f (p.starProjection x) = (p.map f.toLinearMap).starProjection (f x) := by
  refine (eq_starProjection_of_mem_of_inner_eq_zero ?_ fun y hy => ?_).symm
  · refine Submodule.apply_coe_mem_map _ _
  rcases hy with ⟨x', hx', rfl : f x' = y⟩
  rw [← f.map_sub, f.inner_map_map, starProjection_inner_eq_zero x x' hx']

theorem _root_.LinearIsometry.map_starProjection' {E E' : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E →ₗᵢ[𝕜] E')
    (p : Submodule 𝕜 E) [p.HasOrthogonalProjection]
    [(p.map (f : E →ₗ[𝕜] E')).HasOrthogonalProjection] (x : E) :
    f (p.starProjection x) = (p.map (f : E →ₗ[𝕜] E')).starProjection (f x) :=
  have : (p.map f.toLinearMap).HasOrthogonalProjection := ‹_›
  f.map_starProjection p x

/-- Orthogonal projection onto the `Submodule.map` of a subspace. -/
theorem starProjection_map_apply {E E' : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E')
    (p : Submodule 𝕜 E) [p.HasOrthogonalProjection] (x : E') :
    (p.map (f.toLinearEquiv : E →ₗ[𝕜] E')).starProjection x =
      f (p.starProjection (f.symm x)) := by
  simpa only [f.coe_toLinearIsometry, f.apply_symm_apply] using
    (f.toLinearIsometry.map_starProjection' p (f.symm x)).symm

/-- The orthogonal projection onto the trivial submodule is the zero map. -/
@[simp]
theorem orthogonalProjection_bot : (⊥ : Submodule 𝕜 E).orthogonalProjection = 0 := by ext

@[simp]
lemma starProjection_bot : (⊥ : Submodule 𝕜 E).starProjection = 0 := by
  rw [starProjection, orthogonalProjection_bot, ContinuousLinearMap.comp_zero]

variable (K)

/-- The orthogonal projection has norm `≤ 1`. -/
theorem orthogonalProjection_norm_le : ‖K.orthogonalProjection‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ (by simp) _

theorem starProjection_norm_le : ‖K.starProjection‖ ≤ 1 :=
  K.orthogonalProjection_norm_le

theorem norm_orthogonalProjection_apply {v : E} (hv : v ∈ K) :
    ‖orthogonalProjection K v‖ = ‖v‖ :=
  congr(‖$(K.starProjection_eq_self_iff.mpr hv)‖)

theorem norm_starProjection_apply {v : E} (hv : v ∈ K) :
    ‖K.starProjection v‖ = ‖v‖ :=
  norm_orthogonalProjection_apply _ hv

/-- The orthogonal projection onto a closed subspace is norm non-increasing. -/
theorem norm_orthogonalProjection_apply_le (v : E) :
    ‖orthogonalProjection K v‖ ≤ ‖v‖ := by calc
  ‖orthogonalProjection K v‖ ≤ ‖orthogonalProjection K‖ * ‖v‖ := K.orthogonalProjection.le_opNorm _
  _ ≤ 1 * ‖v‖ := by gcongr; exact orthogonalProjection_norm_le K
  _ = _ := by simp

theorem norm_starProjection_apply_le (v : E) :
    ‖K.starProjection v‖ ≤ ‖v‖ := K.norm_orthogonalProjection_apply_le v

/-- The orthogonal projection onto a closed subspace is a `1`-Lipschitz map. -/
theorem lipschitzWith_orthogonalProjection :
    LipschitzWith 1 (orthogonalProjection K) :=
  ContinuousLinearMap.lipschitzWith_of_opNorm_le (orthogonalProjection_norm_le K)

theorem lipschitzWith_starProjection :
    LipschitzWith 1 K.starProjection :=
  ContinuousLinearMap.lipschitzWith_of_opNorm_le (starProjection_norm_le K)

/-- The operator norm of the orthogonal projection onto a nontrivial subspace is `1`. -/
theorem norm_orthogonalProjection (hK : K ≠ ⊥) :
    ‖K.orthogonalProjection‖ = 1 := by
  refine le_antisymm K.orthogonalProjection_norm_le ?_
  obtain ⟨x, hxK, hx_ne_zero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  simpa [K.norm_orthogonalProjection_apply hxK, norm_eq_zero, hx_ne_zero]
    using K.orthogonalProjection.ratio_le_opNorm x

theorem norm_starProjection (hK : K ≠ ⊥) :
    ‖K.starProjection‖ = 1 :=
  K.norm_orthogonalProjection hK

variable (𝕜)

theorem smul_starProjection_singleton {v : E} (w : E) :
    ((‖v‖ ^ 2 : ℝ) : 𝕜) • (𝕜 ∙ v).starProjection w = ⟪v, w⟫ • v := by
  suffices ((𝕜 ∙ v).starProjection (((‖v‖ : 𝕜) ^ 2) • w)) = ⟪v, w⟫ • v by
    simpa using this
  apply eq_starProjection_of_mem_of_inner_eq_zero
  · rw [Submodule.mem_span_singleton]
    use ⟪v, w⟫
  · rw [← Submodule.mem_orthogonal', Submodule.mem_orthogonal_singleton_iff_inner_left]
    simp [inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K, mul_comm]

/-- Formula for orthogonal projection onto a single vector. -/
theorem starProjection_singleton {v : E} (w : E) :
    (𝕜 ∙ v).starProjection w = (⟪v, w⟫ / ((‖v‖ ^ 2 : ℝ) : 𝕜)) • v := by
  by_cases hv : v = 0
  · rw [hv]
    simp [Submodule.span_zero_singleton 𝕜]
  have hv' : ‖v‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr hv)
  have key :
    (((‖v‖ ^ 2 : ℝ) : 𝕜)⁻¹ * ((‖v‖ ^ 2 : ℝ) : 𝕜)) • (𝕜 ∙ v).starProjection w =
      (((‖v‖ ^ 2 : ℝ) : 𝕜)⁻¹ * ⟪v, w⟫) • v := by
    simp [mul_smul, smul_starProjection_singleton 𝕜 w, -map_pow]
  convert key using 1 <;> match_scalars <;> field_simp [hv']

/-- Formula for orthogonal projection onto a single unit vector. -/
theorem starProjection_unit_singleton {v : E} (hv : ‖v‖ = 1) (w : E) :
    (𝕜 ∙ v).starProjection w = ⟪v, w⟫ • v := by
  rw [← smul_starProjection_singleton 𝕜 w]
  simp [hv]

end orthogonalProjection

variable {K}

/-- If `K` is complete, any `v` in `E` can be expressed as a sum of elements of `K` and `Kᗮ`. -/
theorem exists_add_mem_mem_orthogonal [K.HasOrthogonalProjection] (v : E) :
    ∃ y ∈ K, ∃ z ∈ Kᗮ, v = y + z :=
  ⟨K.orthogonalProjection v, Subtype.coe_prop _, v - K.orthogonalProjection v,
    sub_starProjection_mem_orthogonal _, by simp⟩

/-- The orthogonal projection onto `K` of an element of `Kᗮ` is zero. -/
theorem orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero [K.HasOrthogonalProjection]
    {v : E} (hv : v ∈ Kᗮ) : K.orthogonalProjection v = 0 := orthogonalProjection_eq_zero_iff.mpr hv

/-- The projection into `U` from an orthogonal submodule `V` is the zero map. -/
theorem IsOrtho.orthogonalProjection_comp_subtypeL {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (h : U ⟂ V) : U.orthogonalProjection ∘L V.subtypeL = 0 :=
  ContinuousLinearMap.ext fun v =>
    orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero <| h.symm v.prop

theorem IsOrtho.starProjection_comp_starProjection {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : U ⟂ V) :
    U.starProjection ∘L V.starProjection = 0 :=
  calc _ = U.subtypeL ∘L (U.orthogonalProjection ∘L V.subtypeL) ∘L V.orthogonalProjection := by
        simp only [starProjection, ContinuousLinearMap.comp_assoc]
    _ = 0 := by simp [h.orthogonalProjection_comp_subtypeL]

/-- The projection into `U` from `V` is the zero map if and only if `U` and `V` are orthogonal. -/
theorem orthogonalProjection_comp_subtypeL_eq_zero_iff {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] : U.orthogonalProjection ∘L V.subtypeL = 0 ↔ U ⟂ V :=
  ⟨fun h u hu v hv => by
    convert starProjection_inner_eq_zero v u hu using 2
    have : U.orthogonalProjection v = 0 := DFunLike.congr_fun h (⟨_, hv⟩ : V)
    rw [starProjection_apply, this, Submodule.coe_zero, sub_zero],
    Submodule.IsOrtho.orthogonalProjection_comp_subtypeL⟩

/-- `U.starProjection ∘ V.starProjection = 0` iff `U` and `V` are pairwise orthogonal. -/
theorem starProjection_comp_starProjection_eq_zero_iff {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.starProjection ∘L V.starProjection = 0 ↔ U ⟂ V := by
  refine ⟨fun h => ?_, fun h => h.starProjection_comp_starProjection⟩
  rw [← orthogonalProjection_comp_subtypeL_eq_zero_iff]
  simp only [ContinuousLinearMap.ext_iff, ContinuousLinearMap.comp_apply, subtypeL_apply,
    starProjection_apply, zero_apply, coe_eq_zero] at h ⊢
  intro x
  simpa using h (x : E)

/-- The orthogonal projection onto `Kᗮ` of an element of `K` is zero. -/
theorem orthogonalProjection_orthogonal_apply_eq_zero
    [Kᗮ.HasOrthogonalProjection] {v : E} (hv : v ∈ K) : Kᗮ.orthogonalProjection v = 0 :=
  orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero (K.le_orthogonal_orthogonal hv)

theorem starProjection_orthogonal_apply_eq_zero
    [Kᗮ.HasOrthogonalProjection] {v : E} (hv : v ∈ K) :
    Kᗮ.starProjection v = 0 := by
  rw [starProjection_apply, coe_eq_zero]
  exact orthogonalProjection_orthogonal_apply_eq_zero hv

/-- If `U ≤ V`, then projecting on `V` and then on `U` is the same as projecting on `U`. -/
theorem orthogonalProjection_starProjection_of_le {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : U ≤ V) (x : E) :
    U.orthogonalProjection (V.starProjection x) = U.orthogonalProjection x :=
  Eq.symm <| by
    simpa only [sub_eq_zero, map_sub] using
      orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero
        (Submodule.orthogonal_le h (sub_starProjection_mem_orthogonal x))

theorem starProjection_comp_starProjection_of_le {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : U ≤ V) :
    U.starProjection ∘L V.starProjection = U.starProjection := ContinuousLinearMap.ext fun _ => by
  nth_rw 1 [starProjection]
  simp [orthogonalProjection_starProjection_of_le h]

open ContinuousLinearMap in
theorem _root_.ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range [CompleteSpace E]
    {p : E →L[𝕜] E} (hp : IsIdempotentElem p) : p.range.HasOrthogonalProjection :=
  have := hp.isClosed_range.completeSpace_coe
  .ofCompleteSpace _

open LinearMap in
theorem _root_.LinearMap.IsSymmetricProjection.hasOrthogonalProjection_range
    {p : E →ₗ[𝕜] E} (hp : p.IsSymmetricProjection) :
    (range p).HasOrthogonalProjection :=
  ⟨fun v => ⟨p v, by
    simp [hp.isIdempotentElem.isSymmetric_iff_orthogonal_range.mp hp.isSymmetric,
      ← Module.End.mul_apply, hp.isIdempotentElem.eq]⟩⟩

/-- The orthogonal projection onto `(𝕜 ∙ v)ᗮ` of `v` is zero. -/
theorem orthogonalProjection_orthogonalComplement_singleton_eq_zero (v : E) :
    (𝕜 ∙ v)ᗮ.orthogonalProjection v = 0 :=
  orthogonalProjection_orthogonal_apply_eq_zero
    (Submodule.mem_span_singleton_self v)

theorem starProjection_orthogonalComplement_singleton_eq_zero (v : E) :
    (𝕜 ∙ v)ᗮ.starProjection v = 0 := by
  rw [starProjection_apply, coe_eq_zero]
  exact orthogonalProjection_orthogonalComplement_singleton_eq_zero v

/-- If the orthogonal projection to `K` is well-defined, then a vector splits as the sum of its
orthogonal projections onto a complete submodule `K` and onto the orthogonal complement of `K`. -/
theorem starProjection_add_starProjection_orthogonal [K.HasOrthogonalProjection]
    (w : E) : K.starProjection w + Kᗮ.starProjection w = w := by
  simp

/-- The Pythagorean theorem, for an orthogonal projection. -/
theorem norm_sq_eq_add_norm_sq_projection (x : E) (S : Submodule 𝕜 E) [S.HasOrthogonalProjection] :
    ‖x‖ ^ 2 = ‖S.orthogonalProjection x‖ ^ 2 + ‖Sᗮ.orthogonalProjection x‖ ^ 2 :=
  calc
    ‖x‖ ^ 2 = ‖S.starProjection x + Sᗮ.starProjection x‖ ^ 2 := by
      rw [starProjection_add_starProjection_orthogonal]
    _ = ‖S.orthogonalProjection x‖ ^ 2 + ‖Sᗮ.orthogonalProjection x‖ ^ 2 := by
      simp only [sq]
      exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ <|
        (S.mem_orthogonal _).1 (Sᗮ.orthogonalProjection x).2 _ (S.orthogonalProjection x).2

theorem norm_sq_eq_add_norm_sq_starProjection (x : E) (S : Submodule 𝕜 E)
    [S.HasOrthogonalProjection] :
    ‖x‖ ^ 2 = ‖S.starProjection x‖ ^ 2 + ‖Sᗮ.starProjection x‖ ^ 2 :=
  norm_sq_eq_add_norm_sq_projection x S

theorem mem_iff_norm_starProjection (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (v : E) :
    v ∈ U ↔ ‖U.starProjection v‖ = ‖v‖ := by
  refine ⟨fun h => norm_starProjection_apply _ h, fun h => ?_⟩
  simpa [h, sub_eq_zero, eq_comm (a := v), starProjection_eq_self_iff] using
    U.norm_sq_eq_add_norm_sq_starProjection v

/-- In a complete space `E`, the projection maps onto a complete subspace `K` and its orthogonal
complement sum to the identity. -/
theorem id_eq_sum_starProjection_self_orthogonalComplement [K.HasOrthogonalProjection] :
    ContinuousLinearMap.id 𝕜 E =
      K.starProjection + Kᗮ.starProjection := by
  ext w
  exact (K.starProjection_add_starProjection_orthogonal w).symm

-- The priority should be higher than `Submodule.coe_inner`.
@[simp high]
theorem inner_orthogonalProjection_eq_of_mem_right [K.HasOrthogonalProjection] (u : K) (v : E) :
    ⟪K.orthogonalProjection v, u⟫ = ⟪v, u⟫ :=
  calc
    ⟪K.orthogonalProjection v, u⟫ = ⟪K.starProjection v, u⟫ := K.coe_inner _ _
    _ = ⟪K.starProjection v, u⟫ + ⟪v - K.starProjection v, u⟫ := by
      rw [starProjection_inner_eq_zero _ _ (Submodule.coe_mem _), add_zero]
    _ = ⟪v, u⟫ := by rw [← inner_add_left, add_sub_cancel]

-- The priority should be higher than `Submodule.coe_inner`.
@[simp high]
theorem inner_orthogonalProjection_eq_of_mem_left [K.HasOrthogonalProjection] (u : K) (v : E) :
    ⟪u, K.orthogonalProjection v⟫ = ⟪(u : E), v⟫ := by
  rw [← inner_conj_symm, ← inner_conj_symm (u : E), inner_orthogonalProjection_eq_of_mem_right]

variable (K)

/-- The orthogonal projection is self-adjoint. -/
theorem inner_starProjection_left_eq_right [K.HasOrthogonalProjection] (u v : E) :
    ⟪K.starProjection u, v⟫ = ⟪u, K.starProjection v⟫ := by
  simp_rw [starProjection_apply, ← inner_orthogonalProjection_eq_of_mem_left,
    inner_orthogonalProjection_eq_of_mem_right]

/-- The orthogonal projection is symmetric. -/
theorem starProjection_isSymmetric [K.HasOrthogonalProjection] :
    (K.starProjection : E →ₗ[𝕜] E).IsSymmetric :=
  inner_starProjection_left_eq_right K

open ContinuousLinearMap in
/-- `U.starProjection` is a symmetric projection. -/
@[simp]
theorem isSymmetricProjection_starProjection
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    U.starProjection.IsSymmetricProjection :=
  ⟨U.isIdempotentElem_starProjection.toLinearMap, U.starProjection_isSymmetric⟩

open LinearMap in
/-- An operator is a symmetric projection if and only if it is an orthogonal projection. -/
theorem _root_.LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range {p : E →ₗ[𝕜] E} :
    p.IsSymmetricProjection ↔ ∃ (_ : (LinearMap.range p).HasOrthogonalProjection),
    p = (LinearMap.range p).starProjection := by
  refine ⟨fun hp ↦ ?_, fun ⟨h, hp⟩ ↦ hp ▸ isSymmetricProjection_starProjection _⟩
  have : (LinearMap.range p).HasOrthogonalProjection := hp.hasOrthogonalProjection_range
  refine ⟨this, Eq.symm ?_⟩
  ext x
  refine Submodule.eq_starProjection_of_mem_orthogonal (by simp) ?_
  rw [hp.isIdempotentElem.isSymmetric_iff_orthogonal_range.mp hp.isSymmetric]
  simpa using congr($hp.isIdempotentElem.mul_one_sub_self x)

lemma _root_.LinearMap.isSymmetricProjection_iff_eq_coe_starProjection {p : E →ₗ[𝕜] E} :
    p.IsSymmetricProjection
      ↔ ∃ (K : Submodule 𝕜 E) (_ : K.HasOrthogonalProjection), p = K.starProjection :=
  ⟨fun h ↦ ⟨LinearMap.range p, p.isSymmetricProjection_iff_eq_coe_starProjection_range.mp h⟩,
    by rintro ⟨_, _, rfl⟩; exact isSymmetricProjection_starProjection _⟩

theorem starProjection_apply_eq_zero_iff [K.HasOrthogonalProjection] {v : E} :
    K.starProjection v = 0 ↔ v ∈ Kᗮ := by
  refine ⟨fun h w hw => ?_, fun hv => ?_⟩
  · rw [← starProjection_eq_self_iff.mpr hw, inner_starProjection_left_eq_right, h,
      inner_zero_right]
  · simp [starProjection_apply, orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero hv]

open RCLike

lemma re_inner_starProjection_eq_normSq [K.HasOrthogonalProjection] (v : E) :
    re ⟪K.starProjection v, v⟫ = ‖K.orthogonalProjection v‖ ^ 2 := by
  rw [starProjection_apply,
    re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
    div_eq_iff (NeZero.ne' 2).symm, pow_two, add_sub_assoc, ← eq_sub_iff_add_eq', coe_norm,
    ← mul_sub_one, show (2 : ℝ) - 1 = 1 by norm_num, mul_one, sub_eq_iff_eq_add', norm_sub_rev]
  exact orthogonalProjectionFn_norm_sq K v

lemma re_inner_starProjection_nonneg [K.HasOrthogonalProjection] (v : E) :
    0 ≤ re ⟪K.starProjection v, v⟫ := by
  rw [re_inner_starProjection_eq_normSq K v]
  exact sq_nonneg ‖K.orthogonalProjection v‖

end

end Submodule
