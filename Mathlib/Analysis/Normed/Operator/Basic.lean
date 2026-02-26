/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Algebra.Module.StrongTopology
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Tactic.SuppressCompilation

/-!
# Operator norm on the space of continuous linear maps

Define the operator (semi)-norm on the space of continuous (semi)linear maps between (semi)-normed
spaces, and prove its basic properties. In particular, show that this space is itself a semi-normed
space.

Since a lot of elementary properties don't require `‖x‖ = 0 → x = 0` we start setting up the
theory for `SeminormedAddCommGroup`. Later we will specialize to `NormedAddCommGroup` in the
file `NormedSpace.lean`.

Note that most of statements that apply to semilinear maps only hold when the ring homomorphism
is isometric, as expressed by the typeclass `[RingHomIsometric σ]`.

## Main Results
* `ball_subset_range_iff_surjective` (and its variants) shows that a semi-linear map between normed
  spaces is surjective if and only if it contains a ball.

-/

@[expose] public section

suppress_compilation

open Bornology Metric
open Filter hiding map_smul
open scoped NNReal Topology Uniformity

-- the `ₗ` subscript variables are for special cases about linear (as opposed to semilinear) maps
variable {𝕜 𝕜₂ 𝕜₃ E F Fₗ G 𝓕 : Type*}

section SemiNormed

variable [AddCommGroup E] [SeminormedAddCommGroup E] [AddCommGroup F] [SeminormedAddCommGroup F] [AddCommGroup Fₗ] [SeminormedAddCommGroup Fₗ]
  [AddCommGroup G] [SeminormedAddCommGroup G]

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜 Fₗ] [NormedSpace 𝕜₃ G]
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable [FunLike 𝓕 E F]

section

variable [SemilinearMapClass 𝓕 σ₁₂ E F]

theorem ball_zero_subset_range_iff_surjective [RingHomSurjective σ₁₂] {f : 𝓕} {r : ℝ}
    (hr : 0 < r) : ball 0 r ⊆ Set.range f ↔ (⇑f).Surjective :=
  absorbent_ball (by simpa) |>.subset_range_iff_surjective (f := (f : E →ₛₗ[σ₁₂] F))

theorem ball_subset_range_iff_surjective [RingHomSurjective σ₁₂] {f : 𝓕} {x : F} {r : ℝ}
    (hr : 0 < r) : ball x r ⊆ Set.range f ↔ (⇑f).Surjective := by
  refine ⟨fun h ↦ ?_, by simp_all⟩
  rw [← ball_zero_subset_range_iff_surjective hr, ← LinearMap.coe_coe]
  simp_rw [← LinearMap.coe_range, Set.subset_def, SetLike.mem_coe] at h ⊢
  intro _ _
  rw [← Submodule.add_mem_iff_left (f : E →ₛₗ[σ₁₂] F).range (h _ <| mem_ball_self hr)]
  apply h
  simp_all

theorem closedBall_subset_range_iff_surjective [RingHomSurjective σ₁₂] {f : 𝓕} (x : F) {r : ℝ}
    (hr : 0 < r) : closedBall (x : F) r ⊆ Set.range f ↔ (⇑f).Surjective :=
  ⟨fun h ↦ (ball_subset_range_iff_surjective hr).mp <| subset_trans ball_subset_closedBall h,
    by simp_all⟩

variable {F' 𝓕' : Type*} [AddCommGroup F'] [NormedAddCommGroup F'] [NormedSpace ℝ F'] [Nontrivial F']
{τ : 𝕜 →+* ℝ} [FunLike 𝓕' E F'] [SemilinearMapClass 𝓕' τ E F']

theorem sphere_subset_range_iff_surjective [RingHomSurjective τ] {f : 𝓕'} {x : F'} {r : ℝ}
    (hr : 0 < r) : sphere x r ⊆ Set.range f ↔ (⇑f).Surjective := by
  refine ⟨fun h ↦ ?_, by simp_all⟩
  grw [← (closedBall_subset_range_iff_surjective x hr), ← convexHull_sphere_eq_closedBall x hr.le,
    convexHull_mono h, (convexHull_eq_self (𝕜 := ℝ) (s := Set.range ↑f)).mpr]
  exact Submodule.Convex.semilinear_range (E := F') (F' := E) (σ := τ) f

end

/-- If `‖x‖ = 0` and `f` is continuous then `‖f x‖ = 0`. -/
theorem norm_image_of_norm_eq_zero [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕) (hf : Continuous f)
    {x : E} (hx : ‖x‖ = 0) : ‖f x‖ = 0 := by
  rw [← mem_closure_zero_iff_norm, ← specializes_iff_mem_closure, ← map_zero f] at *
  exact hx.map hf

@[deprecated (since := "2025-11-15")] alias norm_image_of_norm_zero := norm_image_of_norm_eq_zero

section

variable [RingHomIsometric σ₁₂]

theorem SemilinearMapClass.bound_of_shell_semi_normed [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕)
    {ε C : ℝ} (ε_pos : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖)
    (hf : ∀ x, ε / ‖c‖ ≤ ‖x‖ → ‖x‖ < ε → ‖f x‖ ≤ C * ‖x‖) {x : E} (hx : ‖x‖ ≠ 0) :
    ‖f x‖ ≤ C * ‖x‖ :=
  (normSeminorm 𝕜 E).bound_of_shell ((normSeminorm 𝕜₂ F).comp ⟨⟨f, map_add f⟩, map_smulₛₗ f⟩)
    ε_pos hc hf hx

/-- A continuous linear map between seminormed spaces is bounded when the field is nontrivially
normed. The continuity ensures boundedness on a ball of some radius `ε`. The nontriviality of the
norm is then used to rescale any element into an element of norm in `[ε/C, ε]`, whose image has a
controlled norm. The norm control for the original element follows by rescaling. -/
theorem SemilinearMapClass.bound_of_continuous [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕)
    (hf : Continuous f) : ∃ C, 0 < C ∧ ∀ x : E, ‖f x‖ ≤ C * ‖x‖ :=
  let φ : E →ₛₗ[σ₁₂] F := ⟨⟨f, map_add f⟩, map_smulₛₗ f⟩
  ((normSeminorm 𝕜₂ F).comp φ).bound_of_continuous_normedSpace (continuous_norm.comp hf)

theorem SemilinearMapClass.nnbound_of_continuous [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕)
    (hf : Continuous f) : ∃ C : ℝ≥0, 0 < C ∧ ∀ x : E, ‖f x‖₊ ≤ C * ‖x‖₊ :=
  let ⟨c, hc, hcf⟩ := SemilinearMapClass.bound_of_continuous f hf; ⟨⟨c, hc.le⟩, hc, hcf⟩

theorem SemilinearMapClass.ebound_of_continuous [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕)
    (hf : Continuous f) : ∃ C : ℝ≥0, 0 < C ∧ ∀ x : E, ‖f x‖ₑ ≤ C * ‖x‖ₑ :=
  let ⟨c, hc, hcf⟩ := SemilinearMapClass.nnbound_of_continuous f hf
  ⟨c, hc, fun x => ENNReal.coe_mono <| hcf x⟩

end

namespace ContinuousLinearMap

theorem bound [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) : ∃ C, 0 < C ∧ ∀ x : E, ‖f x‖ ≤ C * ‖x‖ :=
  SemilinearMapClass.bound_of_continuous f f.2

theorem nnbound [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ x : E, ‖f x‖₊ ≤ C * ‖x‖₊ :=
  SemilinearMapClass.nnbound_of_continuous f f.2

theorem ebound [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ x : E, ‖f x‖ₑ ≤ C * ‖x‖ₑ :=
  SemilinearMapClass.ebound_of_continuous f f.2

section

open Filter

variable (𝕜 E)

/-- Given a unit-length element `x` of a normed space `E` over a field `𝕜`, the natural linear
isometry map from `𝕜` to `E` by taking multiples of `x`. -/
def _root_.LinearIsometry.toSpanSingleton {v : E} (hv : ‖v‖ = 1) : 𝕜 →ₗᵢ[𝕜] E :=
  { LinearMap.toSpanSingleton 𝕜 E v with norm_map' := fun x => by simp [norm_smul, hv] }

variable {𝕜 E}

@[simp]
theorem _root_.LinearIsometry.toSpanSingleton_apply {v : E} (hv : ‖v‖ = 1) (a : 𝕜) :
    LinearIsometry.toSpanSingleton 𝕜 E hv a = a • v :=
  rfl

@[simp]
theorem _root_.LinearIsometry.coe_toSpanSingleton {v : E} (hv : ‖v‖ = 1) :
    (LinearIsometry.toSpanSingleton 𝕜 E hv).toLinearMap = LinearMap.toSpanSingleton 𝕜 E v :=
  rfl

end

section OpNorm

open Set Real

/-- The operator norm of a continuous linear map is the inf of all its bounds. -/
def opNorm (f : E →SL[σ₁₂] F) :=
  sInf { c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖ }

instance hasOpNorm : Norm (E →SL[σ₁₂] F) :=
  ⟨opNorm⟩

theorem norm_def (f : E →SL[σ₁₂] F) : ‖f‖ = sInf { c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖ } :=
  rfl

-- So that invocations of `le_csInf` make sense: we show that the set of
-- bounds is nonempty and bounded below.
theorem bounds_nonempty [RingHomIsometric σ₁₂] {f : E →SL[σ₁₂] F} :
    ∃ c, c ∈ { c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖ } :=
  let ⟨M, hMp, hMb⟩ := f.bound
  ⟨M, le_of_lt hMp, hMb⟩

theorem bounds_bddBelow {f : E →SL[σ₁₂] F} : BddBelow { c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖ } :=
  ⟨0, fun _ ⟨hn, _⟩ => hn⟩

theorem isLeast_opNorm [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) :
    IsLeast {c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖} ‖f‖ := by
  refine IsClosed.isLeast_csInf ?_ bounds_nonempty bounds_bddBelow
  simp only [setOf_and, setOf_forall]
  refine isClosed_Ici.inter <| isClosed_iInter fun _ ↦ isClosed_le ?_ ?_ <;> continuity

/-- If one controls the norm of every `A x`, then one controls the norm of `A`. -/
theorem opNorm_le_bound (f : E →SL[σ₁₂] F) {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) :
    ‖f‖ ≤ M :=
  csInf_le bounds_bddBelow ⟨hMp, hM⟩

/-- If one controls the norm of every `A x`, `‖x‖ ≠ 0`, then one controls the norm of `A`. -/
theorem opNorm_le_bound' (f : E →SL[σ₁₂] F) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ x, ‖x‖ ≠ 0 → ‖f x‖ ≤ M * ‖x‖) : ‖f‖ ≤ M :=
  opNorm_le_bound f hMp fun x =>
    (ne_or_eq ‖x‖ 0).elim (hM x) fun h => by
      simp only [h, mul_zero, norm_image_of_norm_eq_zero f f.2 h, le_refl]

theorem opNorm_eq_of_bounds {φ : E →SL[σ₁₂] F} {M : ℝ} (M_nonneg : 0 ≤ M)
    (h_above : ∀ x, ‖φ x‖ ≤ M * ‖x‖) (h_below : ∀ N ≥ 0, (∀ x, ‖φ x‖ ≤ N * ‖x‖) → M ≤ N) :
    ‖φ‖ = M :=
  le_antisymm (φ.opNorm_le_bound M_nonneg h_above)
    ((le_csInf_iff ContinuousLinearMap.bounds_bddBelow ⟨M, M_nonneg, h_above⟩).mpr
      fun N ⟨N_nonneg, hN⟩ => h_below N N_nonneg hN)

theorem opNorm_neg (f : E →SL[σ₁₂] F) : ‖-f‖ = ‖f‖ := by simp only [norm_def, neg_apply, norm_neg]

theorem opNorm_nonneg (f : E →SL[σ₁₂] F) : 0 ≤ ‖f‖ :=
  Real.sInf_nonneg fun _ ↦ And.left

/-- The norm of the `0` operator is `0`. -/
theorem opNorm_zero : ‖(0 : E →SL[σ₁₂] F)‖ = 0 :=
  le_antisymm (opNorm_le_bound _ le_rfl fun _ ↦ by simp) (opNorm_nonneg _)

/-- The norm of the identity is at most `1`. It is in fact `1`, except when the space is trivial
where it is `0`. It means that one cannot do better than an inequality in general. -/
theorem norm_id_le : ‖ContinuousLinearMap.id 𝕜 E‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun x => by simp

section

variable [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₃] (f g : E →SL[σ₁₂] F) (h : F →SL[σ₂₃] G)
  (x : E)

/-- The fundamental property of the operator norm: `‖f x‖ ≤ ‖f‖ * ‖x‖`. -/
theorem le_opNorm : ‖f x‖ ≤ ‖f‖ * ‖x‖ := (isLeast_opNorm f).1.2 x

theorem dist_le_opNorm (x y : E) : dist (f x) (f y) ≤ ‖f‖ * dist x y := by
  simp_rw [dist_eq_norm, ← map_sub, f.le_opNorm]

theorem le_of_opNorm_le_of_le {x} {a b : ℝ} (hf : ‖f‖ ≤ a) (hx : ‖x‖ ≤ b) :
    ‖f x‖ ≤ a * b :=
  (f.le_opNorm x).trans <| by gcongr; exact (opNorm_nonneg f).trans hf

theorem le_opNorm_of_le {c : ℝ} {x} (h : ‖x‖ ≤ c) : ‖f x‖ ≤ ‖f‖ * c :=
  f.le_of_opNorm_le_of_le le_rfl h

theorem le_of_opNorm_le {c : ℝ} (h : ‖f‖ ≤ c) (x : E) : ‖f x‖ ≤ c * ‖x‖ :=
  f.le_of_opNorm_le_of_le h le_rfl

theorem opNorm_le_iff {f : E →SL[σ₁₂] F} {M : ℝ} (hMp : 0 ≤ M) :
    ‖f‖ ≤ M ↔ ∀ x, ‖f x‖ ≤ M * ‖x‖ :=
  ⟨f.le_of_opNorm_le, opNorm_le_bound f hMp⟩

theorem ratio_le_opNorm : ‖f x‖ / ‖x‖ ≤ ‖f‖ :=
  div_le_of_le_mul₀ (norm_nonneg _) f.opNorm_nonneg (le_opNorm _ _)

/-- The image of the unit ball under a continuous linear map is bounded. -/
theorem unit_le_opNorm : ‖x‖ ≤ 1 → ‖f x‖ ≤ ‖f‖ :=
  mul_one ‖f‖ ▸ f.le_opNorm_of_le

theorem opNorm_le_of_shell {f : E →SL[σ₁₂] F} {ε C : ℝ} (ε_pos : 0 < ε) (hC : 0 ≤ C) {c : 𝕜}
    (hc : 1 < ‖c‖) (hf : ∀ x, ε / ‖c‖ ≤ ‖x‖ → ‖x‖ < ε → ‖f x‖ ≤ C * ‖x‖) : ‖f‖ ≤ C :=
  f.opNorm_le_bound' hC fun _ hx => SemilinearMapClass.bound_of_shell_semi_normed f ε_pos hc hf hx

theorem opNorm_le_of_ball {f : E →SL[σ₁₂] F} {ε : ℝ} {C : ℝ} (ε_pos : 0 < ε) (hC : 0 ≤ C)
    (hf : ∀ x ∈ ball (0 : E) ε, ‖f x‖ ≤ C * ‖x‖) : ‖f‖ ≤ C := by
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  refine opNorm_le_of_shell ε_pos hC hc fun x _ hx => hf x ?_
  rwa [ball_zero_eq]

theorem opNorm_le_of_nhds_zero {f : E →SL[σ₁₂] F} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ᶠ x in 𝓝 (0 : E), ‖f x‖ ≤ C * ‖x‖) : ‖f‖ ≤ C :=
  let ⟨_, ε0, hε⟩ := Metric.eventually_nhds_iff_ball.1 hf
  opNorm_le_of_ball ε0 hC hε

theorem opNorm_le_of_shell' {f : E →SL[σ₁₂] F} {ε C : ℝ} (ε_pos : 0 < ε) (hC : 0 ≤ C) {c : 𝕜}
    (hc : ‖c‖ < 1) (hf : ∀ x, ε * ‖c‖ ≤ ‖x‖ → ‖x‖ < ε → ‖f x‖ ≤ C * ‖x‖) : ‖f‖ ≤ C := by
  by_cases h0 : c = 0
  · refine opNorm_le_of_ball ε_pos hC fun x hx => hf x ?_ ?_
    · simp [h0]
    · rwa [ball_zero_eq] at hx
  · rw [← inv_inv c, norm_inv, inv_lt_one₀ (norm_pos_iff.2 <| inv_ne_zero h0)] at hc
    refine opNorm_le_of_shell ε_pos hC hc ?_
    rwa [norm_inv, div_eq_mul_inv, inv_inv]

/-- For a continuous real linear map `f`, if one controls the norm of every `f x`, `‖x‖ = 1`, then
one controls the norm of `f`. -/
theorem opNorm_le_of_unit_norm [NormedAlgebra ℝ 𝕜] {f : E →SL[σ₁₂] F} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x, ‖x‖ = 1 → ‖f x‖ ≤ C) : ‖f‖ ≤ C := by
  refine opNorm_le_bound' f hC fun x hx => ?_
  have H₁ : ‖algebraMap _ 𝕜 ‖x‖⁻¹ • x‖ = 1 := by simp [norm_smul, inv_mul_cancel₀ hx]
  have H₂ : ‖x‖⁻¹ * ‖f x‖ ≤ C := by simpa [norm_smul] using hf _ H₁
  rwa [← div_eq_inv_mul, div_le_iff₀] at H₂
  exact (norm_nonneg x).lt_of_ne' hx

/-- The operator norm satisfies the triangle inequality. -/
theorem opNorm_add_le : ‖f + g‖ ≤ ‖f‖ + ‖g‖ :=
  (f + g).opNorm_le_bound (add_nonneg f.opNorm_nonneg g.opNorm_nonneg) fun x =>
    (norm_add_le_of_le (f.le_opNorm x) (g.le_opNorm x)).trans_eq (add_mul _ _ _).symm

/-- If a normed space is (topologically) non-trivial, then the norm of the identity equals `1`. -/
theorem norm_id [NontrivialTopology E] : ‖ContinuousLinearMap.id 𝕜 E‖ = 1 :=
  le_antisymm norm_id_le <| by
    let ⟨x, hx⟩ := exists_norm_ne_zero E
    have := (ContinuousLinearMap.id 𝕜 E).ratio_le_opNorm x
    rwa [id_apply, div_self hx] at this

instance normOneClass [NontrivialTopology E] : NormOneClass (E →L[𝕜] E) :=
  ⟨norm_id⟩

/-- If there is an element with norm different from `0`, then the norm of the identity equals `1`.
(Since we are working with seminorms supposing that the space is non-trivial is not enough.) -/
@[deprecated norm_id (since := "2025-09-03")]
theorem norm_id_of_nontrivial_seminorm (h : ∃ x : E, ‖x‖ ≠ 0) : ‖ContinuousLinearMap.id 𝕜 E‖ = 1 :=
  letI : NontrivialTopology E := .of_exists_norm_ne_zero h
  norm_id

theorem opNorm_smul_le {𝕜' : Type*} [DistribSMul 𝕜' F] [SMulCommClass 𝕜₂ 𝕜' F]
    [AddCommGroup 𝕜'] [SeminormedAddCommGroup 𝕜'] [IsBoundedSMul 𝕜' F]
    (c : 𝕜') (f : E →SL[σ₁₂] F) : ‖c • f‖ ≤ ‖c‖ * ‖f‖ :=
  (c • f).opNorm_le_bound (mul_nonneg (norm_nonneg _) (opNorm_nonneg _)) fun _ => by
    grw [smul_apply, norm_smul_le, mul_assoc, le_opNorm]

theorem opNorm_le_iff_lipschitz {f : E →SL[σ₁₂] F} {K : ℝ≥0} :
    ‖f‖ ≤ K ↔ LipschitzWith K f :=
  ⟨fun h ↦ by simpa using AddMonoidHomClass.lipschitz_of_bound f K <| le_of_opNorm_le f h,
    fun hf ↦ f.opNorm_le_bound K.2 <| hf.norm_le_mul (map_zero f)⟩

alias ⟨lipschitzWith_of_opNorm_le, opNorm_le_of_lipschitz⟩ := opNorm_le_iff_lipschitz

/-- Operator seminorm on the space of continuous (semi)linear maps, as `Seminorm`.

We use this seminorm to define a `SeminormedGroup` structure on `E →SL[σ] F`,
but we have to override the projection `UniformSpace`
so that it is definitionally equal to the one coming from the topologies on `E` and `F`. -/
protected noncomputable def seminorm : Seminorm 𝕜₂ (E →SL[σ₁₂] F) :=
  .ofSMulLE norm opNorm_zero opNorm_add_le opNorm_smul_le

set_option backward.privateInPublic true in
private lemma uniformity_eq_seminorm :
    𝓤 (E →SL[σ₁₂] F) = ⨅ r > 0, 𝓟 {f | ‖-f.1 + f.2‖ < r} := by
  have A (f : (E →SL[σ₁₂] F) × (E →SL[σ₁₂] F)) : ‖-f.1 + f.2‖ = ‖f.1 - f.2‖ := by
    rw [← opNorm_neg, neg_add, neg_neg, sub_eq_add_neg]
  simp only [A]
  refine ContinuousLinearMap.seminorm (σ₁₂ := σ₁₂) (E := E) (F := F) |>.uniformity_eq_of_hasBasis
    (ContinuousLinearMap.hasBasis_nhds_zero_of_basis Metric.nhds_basis_closedBall)
    ?_ fun (s, r) ⟨hs, hr⟩ ↦ ?_
  · rcases NormedField.exists_lt_norm 𝕜 1 with ⟨c, hc⟩
    refine ⟨‖c‖, ContinuousLinearMap.hasBasis_nhds_zero.mem_iff.2
      ⟨(closedBall 0 1, closedBall 0 1), ?_⟩⟩
    suffices ∀ f : E →SL[σ₁₂] F, (∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ 1) → ‖f‖ ≤ ‖c‖ by
      simpa [NormedSpace.isVonNBounded_closedBall, closedBall_mem_nhds, subset_def] using this
    intro f hf
    refine opNorm_le_of_shell (f := f) one_pos (norm_nonneg c) hc fun x hcx hx ↦ ?_
    exact (hf x hx.le).trans ((div_le_iff₀' <| one_pos.trans hc).1 hcx)
  · rcases (NormedSpace.isVonNBounded_iff' _).1 hs with ⟨ε, hε⟩
    rcases exists_pos_mul_lt hr ε with ⟨δ, hδ₀, hδ⟩
    refine ⟨δ, hδ₀, fun f hf x hx ↦ ?_⟩
    simp only [Seminorm.mem_ball_zero, mem_closedBall_zero_iff] at hf ⊢
    rw [mul_comm] at hδ
    exact le_trans (le_of_opNorm_le_of_le _ hf.le (hε _ hx)) hδ.le

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance toPseudoMetricSpace : PseudoMetricSpace (E →SL[σ₁₂] F) := .replaceUniformity
  ContinuousLinearMap.seminorm.toSeminormedAddCommGroup.toPseudoMetricSpace uniformity_eq_seminorm

/-- Continuous linear maps themselves form a seminormed space with respect to the operator norm. -/
instance toSeminormedAddCommGroup : SeminormedAddCommGroup (E →SL[σ₁₂] F) where

/-- If a normed space is (topologically) non-trivial, then the norm of the identity equals `1`. -/
@[simp]
theorem nnnorm_id [NontrivialTopology E] : ‖ContinuousLinearMap.id 𝕜 E‖₊ = 1 :=
  NNReal.eq norm_id

instance toNormedSpace {𝕜' : Type*} [NormedField 𝕜'] [NormedSpace 𝕜' F] [SMulCommClass 𝕜₂ 𝕜' F] :
    NormedSpace 𝕜' (E →SL[σ₁₂] F) :=
  ⟨opNorm_smul_le⟩

/-- The operator norm is submultiplicative. -/
theorem opNorm_comp_le (f : E →SL[σ₁₂] F) : ‖h.comp f‖ ≤ ‖h‖ * ‖f‖ :=
  csInf_le bounds_bddBelow ⟨by positivity, fun x => by
    rw [mul_assoc]
    exact h.le_opNorm_of_le (f.le_opNorm x)⟩

/-- Continuous linear maps form a seminormed ring with respect to the operator norm. -/
instance toSeminormedRing : SeminormedRing (E →L[𝕜] E) :=
  { toSeminormedAddCommGroup, ring with norm_mul_le := opNorm_comp_le }

/-- For a normed space `E`, continuous linear endomorphisms form a normed algebra with
respect to the operator norm. -/
instance toNormedAlgebra : NormedAlgebra 𝕜 (E →L[𝕜] E) := { toNormedSpace, algebra with }

end

variable [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F)

@[simp, nontriviality]
theorem opNorm_subsingleton [Subsingleton E] : ‖f‖ = 0 := norm_of_subsingleton f

/-- The fundamental property of the operator norm, expressed with extended norms:
`‖f x‖ₑ ≤ ‖f‖ₑ * ‖x‖ₑ`. -/
lemma le_opNorm_enorm (x : E) : ‖f x‖ₑ ≤ ‖f‖ₑ * ‖x‖ₑ := by
  simp_rw [← ofReal_norm]
  rw [← ENNReal.ofReal_mul (by positivity)]
  gcongr
  exact f.le_opNorm x

variable {f} in
theorem homothety_norm [NontrivialTopology E] (f : E →SL[σ₁₂] F) {a : ℝ}
    (hf : ∀ x, ‖f x‖ = a * ‖x‖) : ‖f‖ = a := by
  obtain ⟨x, hx⟩ := exists_norm_ne_zero E
  replace hx : 0 < ‖x‖ := lt_of_le_of_ne' (norm_nonneg _) hx
  have ha : 0 ≤ a := by simpa only [hf, hx, mul_nonneg_iff_of_pos_right] using norm_nonneg (f x)
  apply le_antisymm (f.opNorm_le_bound ha fun y => le_of_eq (hf y))
  simpa only [hf, hx, mul_le_mul_iff_left₀] using f.le_opNorm x

end OpNorm

section RestrictScalars

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
variable [NormedSpace 𝕜' E] [IsScalarTower 𝕜' 𝕜 E]
variable [NormedSpace 𝕜' Fₗ] [IsScalarTower 𝕜' 𝕜 Fₗ]

@[simp]
theorem norm_restrictScalars (f : E →L[𝕜] Fₗ) : ‖f.restrictScalars 𝕜'‖ = ‖f‖ :=
  le_antisymm (opNorm_le_bound _ (norm_nonneg _) fun x => f.le_opNorm x)
    (opNorm_le_bound _ (norm_nonneg _) fun x => f.le_opNorm x)

variable (𝕜 E Fₗ 𝕜') (𝕜'' : Type*) [Ring 𝕜'']
variable [Module 𝕜'' Fₗ] [ContinuousConstSMul 𝕜'' Fₗ]
  [SMulCommClass 𝕜 𝕜'' Fₗ] [SMulCommClass 𝕜' 𝕜'' Fₗ]

/-- `ContinuousLinearMap.restrictScalars` as a `LinearIsometry`. -/
def restrictScalarsIsometry : (E →L[𝕜] Fₗ) →ₗᵢ[𝕜''] E →L[𝕜'] Fₗ :=
  ⟨restrictScalarsₗ 𝕜 E Fₗ 𝕜' 𝕜'', norm_restrictScalars⟩

variable {𝕜''}

@[simp]
theorem coe_restrictScalarsIsometry :
    ⇑(restrictScalarsIsometry 𝕜 E Fₗ 𝕜' 𝕜'') = restrictScalars 𝕜' :=
  rfl

@[simp]
theorem restrictScalarsIsometry_toLinearMap :
    (restrictScalarsIsometry 𝕜 E Fₗ 𝕜' 𝕜'').toLinearMap = restrictScalarsₗ 𝕜 E Fₗ 𝕜' 𝕜'' :=
  rfl

end RestrictScalars

lemma norm_pi_le_of_le {ι : Type*} [Fintype ι]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, SeminormedAddCommGroup (M i)] [∀ i, NormedSpace 𝕜 (M i)] {C : ℝ}
    {L : (i : ι) → (E →L[𝕜] M i)} (hL : ∀ i, ‖L i‖ ≤ C) (hC : 0 ≤ C) :
    ‖pi L‖ ≤ C := by
  refine opNorm_le_bound _ hC (fun x ↦ ?_)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i ↦ ?_)
  exact (L i).le_of_opNorm_le (hL i) _

end ContinuousLinearMap

namespace LinearMap

/-- If a continuous linear map is constructed from a linear map via the constructor `mkContinuous`,
then its norm is bounded by the bound given to the constructor if it is nonnegative. -/
theorem mkContinuous_norm_le (f : E →ₛₗ[σ₁₂] F) {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    ‖f.mkContinuous C h‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC h

/-- If a continuous linear map is constructed from a linear map via the constructor `mkContinuous`,
then its norm is bounded by the bound or zero if bound is negative. -/
theorem mkContinuous_norm_le' (f : E →ₛₗ[σ₁₂] F) {C : ℝ} (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    ‖f.mkContinuous C h‖ ≤ max C 0 :=
  ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ _) fun x => (h x).trans <| by
    gcongr; apply le_max_left

end LinearMap

namespace LinearIsometry

theorem norm_toContinuousLinearMap_le (f : E →ₛₗᵢ[σ₁₂] F) : ‖f.toContinuousLinearMap‖ ≤ 1 :=
  f.toContinuousLinearMap.opNorm_le_bound zero_le_one fun x => by simp

end LinearIsometry

namespace Submodule

set_option backward.isDefEq.respectTransparency false in
theorem norm_subtypeL_le (K : Submodule 𝕜 E) : ‖K.subtypeL‖ ≤ 1 :=
  K.subtypeₗᵢ.norm_toContinuousLinearMap_le

end Submodule

end SemiNormed
