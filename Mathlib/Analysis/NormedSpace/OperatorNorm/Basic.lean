/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Algebra.Module.StrongTopology
import Mathlib.Analysis.NormedSpace.LinearIsometry
import Mathlib.Analysis.NormedSpace.ContinuousLinearMap
import Mathlib.Tactic.SuppressCompilation

#align_import analysis.normed_space.operator_norm from "leanprover-community/mathlib"@"f7ebde7ee0d1505dfccac8644ae12371aa3c1c9f"

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

-/

suppress_compilation

-- make instances connecting normed things and algebra have higher priority
open scoped AlgebraNormedInstances

open Bornology
open Filter hiding map_smul
open scoped Classical NNReal Topology Uniformity

-- the `ₗ` subscript variables are for special cases about linear (as opposed to semilinear) maps
variable {𝕜 𝕜₂ 𝕜₃ E Eₗ F Fₗ G Gₗ 𝓕 : Type*}

section SemiNormed

open Metric ContinuousLinearMap

variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup Eₗ] [SeminormedAddCommGroup F]
  [SeminormedAddCommGroup Fₗ] [SeminormedAddCommGroup G] [SeminormedAddCommGroup Gₗ]

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 Eₗ] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜 Fₗ] [NormedSpace 𝕜₃ G]
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable [FunLike 𝓕 E F]

/-- If `‖x‖ = 0` and `f` is continuous then `‖f x‖ = 0`. -/
theorem norm_image_of_norm_zero [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕) (hf : Continuous f) {x : E}
    (hx : ‖x‖ = 0) : ‖f x‖ = 0 := by
  rw [← mem_closure_zero_iff_norm, ← specializes_iff_mem_closure, ← map_zero f] at *
  exact hx.map hf
#align norm_image_of_norm_zero norm_image_of_norm_zero

section

variable [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₃]

theorem SemilinearMapClass.bound_of_shell_semi_normed [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕)
    {ε C : ℝ} (ε_pos : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖)
    (hf : ∀ x, ε / ‖c‖ ≤ ‖x‖ → ‖x‖ < ε → ‖f x‖ ≤ C * ‖x‖) {x : E} (hx : ‖x‖ ≠ 0) :
    ‖f x‖ ≤ C * ‖x‖ :=
  (normSeminorm 𝕜 E).bound_of_shell ((normSeminorm 𝕜₂ F).comp ⟨⟨f, map_add f⟩, map_smulₛₗ f⟩)
    ε_pos hc hf hx
#align semilinear_map_class.bound_of_shell_semi_normed SemilinearMapClass.bound_of_shell_semi_normed

/-- A continuous linear map between seminormed spaces is bounded when the field is nontrivially
normed. The continuity ensures boundedness on a ball of some radius `ε`. The nontriviality of the
norm is then used to rescale any element into an element of norm in `[ε/C, ε]`, whose image has a
controlled norm. The norm control for the original element follows by rescaling. -/
theorem SemilinearMapClass.bound_of_continuous [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕)
    (hf : Continuous f) : ∃ C, 0 < C ∧ ∀ x : E, ‖f x‖ ≤ C * ‖x‖ :=
  let φ : E →ₛₗ[σ₁₂] F := ⟨⟨f, map_add f⟩, map_smulₛₗ f⟩
  ((normSeminorm 𝕜₂ F).comp φ).bound_of_continuous_normedSpace (continuous_norm.comp hf)
#align semilinear_map_class.bound_of_continuous SemilinearMapClass.bound_of_continuous

end

namespace ContinuousLinearMap

theorem bound [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) : ∃ C, 0 < C ∧ ∀ x : E, ‖f x‖ ≤ C * ‖x‖ :=
  SemilinearMapClass.bound_of_continuous f f.2
#align continuous_linear_map.bound ContinuousLinearMap.bound

section

open Filter

variable (𝕜 E)

/-- Given a unit-length element `x` of a normed space `E` over a field `𝕜`, the natural linear
    isometry map from `𝕜` to `E` by taking multiples of `x`. -/
def _root_.LinearIsometry.toSpanSingleton {v : E} (hv : ‖v‖ = 1) : 𝕜 →ₗᵢ[𝕜] E :=
  { LinearMap.toSpanSingleton 𝕜 E v with norm_map' := fun x => by simp [norm_smul, hv] }
#align linear_isometry.to_span_singleton LinearIsometry.toSpanSingleton

variable {𝕜 E}

@[simp]
theorem _root_.LinearIsometry.toSpanSingleton_apply {v : E} (hv : ‖v‖ = 1) (a : 𝕜) :
    LinearIsometry.toSpanSingleton 𝕜 E hv a = a • v :=
  rfl
#align linear_isometry.to_span_singleton_apply LinearIsometry.toSpanSingleton_apply

@[simp]
theorem _root_.LinearIsometry.coe_toSpanSingleton {v : E} (hv : ‖v‖ = 1) :
    (LinearIsometry.toSpanSingleton 𝕜 E hv).toLinearMap = LinearMap.toSpanSingleton 𝕜 E v :=
  rfl
#align linear_isometry.coe_to_span_singleton LinearIsometry.coe_toSpanSingleton

end

section OpNorm

open Set Real

/-- The operator norm of a continuous linear map is the inf of all its bounds. -/
def opNorm (f : E →SL[σ₁₂] F) :=
  sInf { c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖ }
#align continuous_linear_map.op_norm ContinuousLinearMap.opNorm

instance hasOpNorm : Norm (E →SL[σ₁₂] F) :=
  ⟨opNorm⟩
#align continuous_linear_map.has_op_norm ContinuousLinearMap.hasOpNorm

theorem norm_def (f : E →SL[σ₁₂] F) : ‖f‖ = sInf { c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖ } :=
  rfl
#align continuous_linear_map.norm_def ContinuousLinearMap.norm_def

-- So that invocations of `le_csInf` make sense: we show that the set of
-- bounds is nonempty and bounded below.
theorem bounds_nonempty [RingHomIsometric σ₁₂] {f : E →SL[σ₁₂] F} :
    ∃ c, c ∈ { c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖ } :=
  let ⟨M, hMp, hMb⟩ := f.bound
  ⟨M, le_of_lt hMp, hMb⟩
#align continuous_linear_map.bounds_nonempty ContinuousLinearMap.bounds_nonempty

theorem bounds_bddBelow {f : E →SL[σ₁₂] F} : BddBelow { c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖ } :=
  ⟨0, fun _ ⟨hn, _⟩ => hn⟩
#align continuous_linear_map.bounds_bdd_below ContinuousLinearMap.bounds_bddBelow

theorem isLeast_opNorm [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) :
    IsLeast {c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖} ‖f‖ := by
  refine IsClosed.isLeast_csInf ?_ bounds_nonempty bounds_bddBelow
  simp only [setOf_and, setOf_forall]
  refine isClosed_Ici.inter <| isClosed_iInter fun _ ↦ isClosed_le ?_ ?_ <;> continuity

@[deprecated] alias isLeast_op_norm := isLeast_opNorm -- deprecated on 2024-02-02

/-- If one controls the norm of every `A x`, then one controls the norm of `A`. -/
theorem opNorm_le_bound (f : E →SL[σ₁₂] F) {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) :
    ‖f‖ ≤ M :=
  csInf_le bounds_bddBelow ⟨hMp, hM⟩
#align continuous_linear_map.op_norm_le_bound ContinuousLinearMap.opNorm_le_bound

@[deprecated] alias op_norm_le_bound := opNorm_le_bound -- deprecated on 2024-02-02

/-- If one controls the norm of every `A x`, `‖x‖ ≠ 0`, then one controls the norm of `A`. -/
theorem opNorm_le_bound' (f : E →SL[σ₁₂] F) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ x, ‖x‖ ≠ 0 → ‖f x‖ ≤ M * ‖x‖) : ‖f‖ ≤ M :=
  opNorm_le_bound f hMp fun x =>
    (ne_or_eq ‖x‖ 0).elim (hM x) fun h => by
      simp only [h, mul_zero, norm_image_of_norm_zero f f.2 h, le_refl]
#align continuous_linear_map.op_norm_le_bound' ContinuousLinearMap.opNorm_le_bound'

@[deprecated] alias op_norm_le_bound' := opNorm_le_bound' -- deprecated on 2024-02-02

theorem opNorm_le_of_lipschitz {f : E →SL[σ₁₂] F} {K : ℝ≥0} (hf : LipschitzWith K f) : ‖f‖ ≤ K :=
  f.opNorm_le_bound K.2 fun x => by
    simpa only [dist_zero_right, f.map_zero] using hf.dist_le_mul x 0
#align continuous_linear_map.op_norm_le_of_lipschitz ContinuousLinearMap.opNorm_le_of_lipschitz

@[deprecated] alias op_norm_le_of_lipschitz := opNorm_le_of_lipschitz -- 2024-02-02

theorem opNorm_eq_of_bounds {φ : E →SL[σ₁₂] F} {M : ℝ} (M_nonneg : 0 ≤ M)
    (h_above : ∀ x, ‖φ x‖ ≤ M * ‖x‖) (h_below : ∀ N ≥ 0, (∀ x, ‖φ x‖ ≤ N * ‖x‖) → M ≤ N) :
    ‖φ‖ = M :=
  le_antisymm (φ.opNorm_le_bound M_nonneg h_above)
    ((le_csInf_iff ContinuousLinearMap.bounds_bddBelow ⟨M, M_nonneg, h_above⟩).mpr
      fun N ⟨N_nonneg, hN⟩ => h_below N N_nonneg hN)
#align continuous_linear_map.op_norm_eq_of_bounds ContinuousLinearMap.opNorm_eq_of_bounds

@[deprecated] alias op_norm_eq_of_bounds := opNorm_eq_of_bounds -- deprecated on 2024-02-02

theorem opNorm_neg (f : E →SL[σ₁₂] F) : ‖-f‖ = ‖f‖ := by simp only [norm_def, neg_apply, norm_neg]
#align continuous_linear_map.op_norm_neg ContinuousLinearMap.opNorm_neg

@[deprecated] alias op_norm_neg := opNorm_neg -- deprecated on 2024-02-02

theorem opNorm_nonneg (f : E →SL[σ₁₂] F) : 0 ≤ ‖f‖ :=
  Real.sInf_nonneg _ fun _ ↦ And.left
#align continuous_linear_map.op_norm_nonneg ContinuousLinearMap.opNorm_nonneg

@[deprecated] alias op_norm_nonneg := opNorm_nonneg -- deprecated on 2024-02-02

/-- The norm of the `0` operator is `0`. -/
theorem opNorm_zero : ‖(0 : E →SL[σ₁₂] F)‖ = 0 :=
  le_antisymm (opNorm_le_bound _ le_rfl fun _ ↦ by simp) (opNorm_nonneg _)
#align continuous_linear_map.op_norm_zero ContinuousLinearMap.opNorm_zero

@[deprecated] alias op_norm_zero := opNorm_zero -- deprecated on 2024-02-02

/-- The norm of the identity is at most `1`. It is in fact `1`, except when the space is trivial
where it is `0`. It means that one can not do better than an inequality in general. -/
theorem norm_id_le : ‖id 𝕜 E‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun x => by simp
#align continuous_linear_map.norm_id_le ContinuousLinearMap.norm_id_le

section

variable [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₃] (f g : E →SL[σ₁₂] F) (h : F →SL[σ₂₃] G)
  (x : E)

/-- The fundamental property of the operator norm: `‖f x‖ ≤ ‖f‖ * ‖x‖`. -/
theorem le_opNorm : ‖f x‖ ≤ ‖f‖ * ‖x‖ := (isLeast_opNorm f).1.2 x
#align continuous_linear_map.le_op_norm ContinuousLinearMap.le_opNorm

@[deprecated] alias le_op_norm := le_opNorm -- deprecated on 2024-02-02

theorem dist_le_opNorm (x y : E) : dist (f x) (f y) ≤ ‖f‖ * dist x y := by
  simp_rw [dist_eq_norm, ← map_sub, f.le_opNorm]
#align continuous_linear_map.dist_le_op_norm ContinuousLinearMap.dist_le_opNorm

@[deprecated] alias dist_le_op_norm := dist_le_opNorm -- deprecated on 2024-02-02

theorem le_of_opNorm_le_of_le {x} {a b : ℝ} (hf : ‖f‖ ≤ a) (hx : ‖x‖ ≤ b) :
    ‖f x‖ ≤ a * b :=
  (f.le_opNorm x).trans <| by gcongr; exact (opNorm_nonneg f).trans hf

@[deprecated] alias le_of_op_norm_le_of_le := le_of_opNorm_le_of_le -- deprecated on 2024-02-02

theorem le_opNorm_of_le {c : ℝ} {x} (h : ‖x‖ ≤ c) : ‖f x‖ ≤ ‖f‖ * c :=
  f.le_of_opNorm_le_of_le le_rfl h
#align continuous_linear_map.le_op_norm_of_le ContinuousLinearMap.le_opNorm_of_le

@[deprecated] alias le_op_norm_of_le := le_opNorm_of_le -- deprecated on 2024-02-02

theorem le_of_opNorm_le {c : ℝ} (h : ‖f‖ ≤ c) (x : E) : ‖f x‖ ≤ c * ‖x‖ :=
  f.le_of_opNorm_le_of_le h le_rfl
#align continuous_linear_map.le_of_op_norm_le ContinuousLinearMap.le_of_opNorm_le

@[deprecated] alias le_of_op_norm_le := le_of_opNorm_le -- deprecated on 2024-02-02

theorem opNorm_le_iff {f : E →SL[σ₁₂] F} {M : ℝ} (hMp : 0 ≤ M) :
    ‖f‖ ≤ M ↔ ∀ x, ‖f x‖ ≤ M * ‖x‖ :=
  ⟨f.le_of_opNorm_le, opNorm_le_bound f hMp⟩

@[deprecated] alias op_norm_le_iff := opNorm_le_iff -- deprecated on 2024-02-02

theorem ratio_le_opNorm : ‖f x‖ / ‖x‖ ≤ ‖f‖ :=
  div_le_of_nonneg_of_le_mul (norm_nonneg _) f.opNorm_nonneg (le_opNorm _ _)
#align continuous_linear_map.ratio_le_op_norm ContinuousLinearMap.ratio_le_opNorm

@[deprecated] alias ratio_le_op_norm := ratio_le_opNorm -- deprecated on 2024-02-02

/-- The image of the unit ball under a continuous linear map is bounded. -/
theorem unit_le_opNorm : ‖x‖ ≤ 1 → ‖f x‖ ≤ ‖f‖ :=
  mul_one ‖f‖ ▸ f.le_opNorm_of_le
#align continuous_linear_map.unit_le_op_norm ContinuousLinearMap.unit_le_opNorm

@[deprecated] alias unit_le_op_norm := unit_le_opNorm -- deprecated on 2024-02-02

theorem opNorm_le_of_shell {f : E →SL[σ₁₂] F} {ε C : ℝ} (ε_pos : 0 < ε) (hC : 0 ≤ C) {c : 𝕜}
    (hc : 1 < ‖c‖) (hf : ∀ x, ε / ‖c‖ ≤ ‖x‖ → ‖x‖ < ε → ‖f x‖ ≤ C * ‖x‖) : ‖f‖ ≤ C :=
  f.opNorm_le_bound' hC fun _ hx => SemilinearMapClass.bound_of_shell_semi_normed f ε_pos hc hf hx
#align continuous_linear_map.op_norm_le_of_shell ContinuousLinearMap.opNorm_le_of_shell

@[deprecated] alias op_norm_le_of_shell := opNorm_le_of_shell -- deprecated on 2024-02-02

theorem opNorm_le_of_ball {f : E →SL[σ₁₂] F} {ε : ℝ} {C : ℝ} (ε_pos : 0 < ε) (hC : 0 ≤ C)
    (hf : ∀ x ∈ ball (0 : E) ε, ‖f x‖ ≤ C * ‖x‖) : ‖f‖ ≤ C := by
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  refine opNorm_le_of_shell ε_pos hC hc fun x _ hx => hf x ?_
  rwa [ball_zero_eq]
#align continuous_linear_map.op_norm_le_of_ball ContinuousLinearMap.opNorm_le_of_ball

@[deprecated] alias op_norm_le_of_ball := opNorm_le_of_ball -- deprecated on 2024-02-02

theorem opNorm_le_of_nhds_zero {f : E →SL[σ₁₂] F} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ᶠ x in 𝓝 (0 : E), ‖f x‖ ≤ C * ‖x‖) : ‖f‖ ≤ C :=
  let ⟨_, ε0, hε⟩ := Metric.eventually_nhds_iff_ball.1 hf
  opNorm_le_of_ball ε0 hC hε
#align continuous_linear_map.op_norm_le_of_nhds_zero ContinuousLinearMap.opNorm_le_of_nhds_zero

@[deprecated] alias op_norm_le_of_nhds_zero := opNorm_le_of_nhds_zero -- deprecated on 2024-02-02

theorem opNorm_le_of_shell' {f : E →SL[σ₁₂] F} {ε C : ℝ} (ε_pos : 0 < ε) (hC : 0 ≤ C) {c : 𝕜}
    (hc : ‖c‖ < 1) (hf : ∀ x, ε * ‖c‖ ≤ ‖x‖ → ‖x‖ < ε → ‖f x‖ ≤ C * ‖x‖) : ‖f‖ ≤ C := by
  by_cases h0 : c = 0
  · refine opNorm_le_of_ball ε_pos hC fun x hx => hf x ?_ ?_
    · simp [h0]
    · rwa [ball_zero_eq] at hx
  · rw [← inv_inv c, norm_inv, inv_lt_one_iff_of_pos (norm_pos_iff.2 <| inv_ne_zero h0)] at hc
    refine opNorm_le_of_shell ε_pos hC hc ?_
    rwa [norm_inv, div_eq_mul_inv, inv_inv]
#align continuous_linear_map.op_norm_le_of_shell' ContinuousLinearMap.opNorm_le_of_shell'

@[deprecated] alias op_norm_le_of_shell' := opNorm_le_of_shell' -- deprecated on 2024-02-02

/-- For a continuous real linear map `f`, if one controls the norm of every `f x`, `‖x‖ = 1`, then
one controls the norm of `f`. -/
theorem opNorm_le_of_unit_norm [NormedSpace ℝ E] [NormedSpace ℝ F] {f : E →L[ℝ] F} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x, ‖x‖ = 1 → ‖f x‖ ≤ C) : ‖f‖ ≤ C := by
  refine opNorm_le_bound' f hC fun x hx => ?_
  have H₁ : ‖‖x‖⁻¹ • x‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel hx]
  have H₂ := hf _ H₁
  rwa [map_smul, norm_smul, norm_inv, norm_norm, ← div_eq_inv_mul, _root_.div_le_iff] at H₂
  exact (norm_nonneg x).lt_of_ne' hx
#align continuous_linear_map.op_norm_le_of_unit_norm ContinuousLinearMap.opNorm_le_of_unit_norm

@[deprecated] alias op_norm_le_of_unit_norm := opNorm_le_of_unit_norm -- deprecated on 2024-02-02

/-- The operator norm satisfies the triangle inequality. -/
theorem opNorm_add_le : ‖f + g‖ ≤ ‖f‖ + ‖g‖ :=
  (f + g).opNorm_le_bound (add_nonneg f.opNorm_nonneg g.opNorm_nonneg) fun x =>
    (norm_add_le_of_le (f.le_opNorm x) (g.le_opNorm x)).trans_eq (add_mul _ _ _).symm
#align continuous_linear_map.op_norm_add_le ContinuousLinearMap.opNorm_add_le

@[deprecated] alias op_norm_add_le := opNorm_add_le -- deprecated on 2024-02-02

/-- If there is an element with norm different from `0`, then the norm of the identity equals `1`.
(Since we are working with seminorms supposing that the space is non-trivial is not enough.) -/
theorem norm_id_of_nontrivial_seminorm (h : ∃ x : E, ‖x‖ ≠ 0) : ‖id 𝕜 E‖ = 1 :=
  le_antisymm norm_id_le <| by
    let ⟨x, hx⟩ := h
    have := (id 𝕜 E).ratio_le_opNorm x
    rwa [id_apply, div_self hx] at this
#align continuous_linear_map.norm_id_of_nontrivial_seminorm ContinuousLinearMap.norm_id_of_nontrivial_seminorm

theorem opNorm_smul_le {𝕜' : Type*} [NormedField 𝕜'] [NormedSpace 𝕜' F] [SMulCommClass 𝕜₂ 𝕜' F]
    (c : 𝕜') (f : E →SL[σ₁₂] F) : ‖c • f‖ ≤ ‖c‖ * ‖f‖ :=
  (c • f).opNorm_le_bound (mul_nonneg (norm_nonneg _) (opNorm_nonneg _)) fun _ => by
    rw [smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (le_opNorm _ _) (norm_nonneg _)
#align continuous_linear_map.op_norm_smul_le ContinuousLinearMap.opNorm_smul_le

@[deprecated] alias op_norm_smul_le := opNorm_smul_le -- deprecated on 2024-02-02

/-- Operator seminorm on the space of continuous (semi)linear maps, as `Seminorm`.

We use this seminorm to define a `SeminormedGroup` structure on `E →SL[σ] F`,
but we have to override the projection `UniformSpace`
so that it is definitionally equal to the one coming from the topologies on `E` and `F`. -/
protected def seminorm : Seminorm 𝕜₂ (E →SL[σ₁₂] F) :=
  .ofSMulLE norm opNorm_zero opNorm_add_le opNorm_smul_le

private lemma uniformity_eq_seminorm :
    𝓤 (E →SL[σ₁₂] F) = ⨅ r > 0, 𝓟 {f | ‖f.1 - f.2‖ < r} := by
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
    exact (hf x hx.le).trans ((div_le_iff' <| one_pos.trans hc).1 hcx)
  · rcases (NormedSpace.isVonNBounded_iff' _ _ _).1 hs with ⟨ε, hε⟩
    rcases exists_pos_mul_lt hr ε with ⟨δ, hδ₀, hδ⟩
    refine ⟨δ, hδ₀, fun f hf x hx ↦ ?_⟩
    simp only [Seminorm.mem_ball_zero, mem_closedBall_zero_iff] at hf ⊢
    rw [mul_comm] at hδ
    exact le_trans (le_of_opNorm_le_of_le _ hf.le (hε _ hx)) hδ.le

instance toPseudoMetricSpace : PseudoMetricSpace (E →SL[σ₁₂] F) := .replaceUniformity
  ContinuousLinearMap.seminorm.toSeminormedAddCommGroup.toPseudoMetricSpace uniformity_eq_seminorm
#align continuous_linear_map.to_pseudo_metric_space ContinuousLinearMap.toPseudoMetricSpace

/-- Continuous linear maps themselves form a seminormed space with respect to
    the operator norm. -/
instance toSeminormedAddCommGroup : SeminormedAddCommGroup (E →SL[σ₁₂] F) where
  dist_eq _ _ := rfl
#align continuous_linear_map.to_seminormed_add_comm_group ContinuousLinearMap.toSeminormedAddCommGroup

#noalign continuous_linear_map.tmp_seminormed_add_comm_group
#noalign continuous_linear_map.tmp_pseudo_metric_space
#noalign continuous_linear_map.tmp_uniform_space
#noalign continuous_linear_map.tmp_topological_space
#noalign continuous_linear_map.tmp_topological_add_group
#noalign continuous_linear_map.tmp_closed_ball_div_subset
#noalign continuous_linear_map.tmp_topology_eq
#noalign continuous_linear_map.tmp_uniform_space_eq

instance toNormedSpace {𝕜' : Type*} [NormedField 𝕜'] [NormedSpace 𝕜' F] [SMulCommClass 𝕜₂ 𝕜' F] :
    NormedSpace 𝕜' (E →SL[σ₁₂] F) :=
  ⟨opNorm_smul_le⟩
#align continuous_linear_map.to_normed_space ContinuousLinearMap.toNormedSpace

/-- The operator norm is submultiplicative. -/
theorem opNorm_comp_le (f : E →SL[σ₁₂] F) : ‖h.comp f‖ ≤ ‖h‖ * ‖f‖ :=
  csInf_le bounds_bddBelow
    ⟨mul_nonneg (opNorm_nonneg _) (opNorm_nonneg _), fun x => by
      rw [mul_assoc]
      exact h.le_opNorm_of_le (f.le_opNorm x)⟩
#align continuous_linear_map.op_norm_comp_le ContinuousLinearMap.opNorm_comp_le

@[deprecated] alias op_norm_comp_le := opNorm_comp_le -- deprecated on 2024-02-02

/-- Continuous linear maps form a seminormed ring with respect to the operator norm. -/
instance toSemiNormedRing : SeminormedRing (E →L[𝕜] E) :=
  { ContinuousLinearMap.toSeminormedAddCommGroup, ContinuousLinearMap.ring with
    norm_mul := fun f g => opNorm_comp_le f g }
#align continuous_linear_map.to_semi_normed_ring ContinuousLinearMap.toSemiNormedRing

/-- For a normed space `E`, continuous linear endomorphisms form a normed algebra with
respect to the operator norm. -/
instance toNormedAlgebra : NormedAlgebra 𝕜 (E →L[𝕜] E) :=
  { algebra with
    norm_smul_le := by
      intro c f
      apply opNorm_smul_le c f}
#align continuous_linear_map.to_normed_algebra ContinuousLinearMap.toNormedAlgebra

end

variable [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F)

@[simp, nontriviality]
theorem opNorm_subsingleton [Subsingleton E] : ‖f‖ = 0 := by
  refine le_antisymm ?_ (norm_nonneg _)
  apply opNorm_le_bound _ rfl.ge
  intro x
  simp [Subsingleton.elim x 0]
#align continuous_linear_map.op_norm_subsingleton ContinuousLinearMap.opNorm_subsingleton

@[deprecated] alias op_norm_subsingleton := opNorm_subsingleton -- deprecated on 2024-02-02

end OpNorm

section RestrictScalars

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
variable [NormedSpace 𝕜' E] [IsScalarTower 𝕜' 𝕜 E]
variable [NormedSpace 𝕜' Fₗ] [IsScalarTower 𝕜' 𝕜 Fₗ]

@[simp]
theorem norm_restrictScalars (f : E →L[𝕜] Fₗ) : ‖f.restrictScalars 𝕜'‖ = ‖f‖ :=
  le_antisymm (opNorm_le_bound _ (norm_nonneg _) fun x => f.le_opNorm x)
    (opNorm_le_bound _ (norm_nonneg _) fun x => f.le_opNorm x)
#align continuous_linear_map.norm_restrict_scalars ContinuousLinearMap.norm_restrictScalars

variable (𝕜 E Fₗ 𝕜') (𝕜'' : Type*) [Ring 𝕜'']
variable [Module 𝕜'' Fₗ] [ContinuousConstSMul 𝕜'' Fₗ]
  [SMulCommClass 𝕜 𝕜'' Fₗ] [SMulCommClass 𝕜' 𝕜'' Fₗ]

/-- `ContinuousLinearMap.restrictScalars` as a `LinearIsometry`. -/
def restrictScalarsIsometry : (E →L[𝕜] Fₗ) →ₗᵢ[𝕜''] E →L[𝕜'] Fₗ :=
  ⟨restrictScalarsₗ 𝕜 E Fₗ 𝕜' 𝕜'', norm_restrictScalars⟩
#align continuous_linear_map.restrict_scalars_isometry ContinuousLinearMap.restrictScalarsIsometry

variable {𝕜''}

@[simp]
theorem coe_restrictScalarsIsometry :
    ⇑(restrictScalarsIsometry 𝕜 E Fₗ 𝕜' 𝕜'') = restrictScalars 𝕜' :=
  rfl
#align continuous_linear_map.coe_restrict_scalars_isometry ContinuousLinearMap.coe_restrictScalarsIsometry

@[simp]
theorem restrictScalarsIsometry_toLinearMap :
    (restrictScalarsIsometry 𝕜 E Fₗ 𝕜' 𝕜'').toLinearMap = restrictScalarsₗ 𝕜 E Fₗ 𝕜' 𝕜'' :=
  rfl
#align continuous_linear_map.restrict_scalars_isometry_to_linear_map ContinuousLinearMap.restrictScalarsIsometry_toLinearMap

variable (𝕜'')

set_option linter.uppercaseLean3 false

/-- `ContinuousLinearMap.restrictScalars` as a `ContinuousLinearMap`. -/
def restrictScalarsL : (E →L[𝕜] Fₗ) →L[𝕜''] E →L[𝕜'] Fₗ :=
  (restrictScalarsIsometry 𝕜 E Fₗ 𝕜' 𝕜'').toContinuousLinearMap
#align continuous_linear_map.restrict_scalarsL ContinuousLinearMap.restrictScalarsL

variable {𝕜 E Fₗ 𝕜' 𝕜''}

@[simp]
theorem coe_restrictScalarsL : (restrictScalarsL 𝕜 E Fₗ 𝕜' 𝕜'' : (E →L[𝕜] Fₗ) →ₗ[𝕜''] E →L[𝕜'] Fₗ) =
    restrictScalarsₗ 𝕜 E Fₗ 𝕜' 𝕜'' :=
  rfl
#align continuous_linear_map.coe_restrict_scalarsL ContinuousLinearMap.coe_restrictScalarsL

@[simp]
theorem coe_restrict_scalarsL' : ⇑(restrictScalarsL 𝕜 E Fₗ 𝕜' 𝕜'') = restrictScalars 𝕜' :=
  rfl
#align continuous_linear_map.coe_restrict_scalarsL' ContinuousLinearMap.coe_restrict_scalarsL'

end RestrictScalars

lemma norm_pi_le_of_le {ι : Type*} [Fintype ι]
    {M : ι → Type*} [∀ i, SeminormedAddCommGroup (M i)] [∀ i, NormedSpace 𝕜 (M i)] {C : ℝ}
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
#align linear_map.mk_continuous_norm_le LinearMap.mkContinuous_norm_le

/-- If a continuous linear map is constructed from a linear map via the constructor `mkContinuous`,
then its norm is bounded by the bound or zero if bound is negative. -/
theorem mkContinuous_norm_le' (f : E →ₛₗ[σ₁₂] F) {C : ℝ} (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    ‖f.mkContinuous C h‖ ≤ max C 0 :=
  ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ _) fun x =>
    (h x).trans <| mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg x)
#align linear_map.mk_continuous_norm_le' LinearMap.mkContinuous_norm_le'

end LinearMap

namespace LinearIsometry

theorem norm_toContinuousLinearMap_le (f : E →ₛₗᵢ[σ₁₂] F) : ‖f.toContinuousLinearMap‖ ≤ 1 :=
  f.toContinuousLinearMap.opNorm_le_bound zero_le_one fun x => by simp
#align linear_isometry.norm_to_continuous_linear_map_le LinearIsometry.norm_toContinuousLinearMap_le

end LinearIsometry

namespace Submodule

theorem norm_subtypeL_le (K : Submodule 𝕜 E) : ‖K.subtypeL‖ ≤ 1 :=
  K.subtypeₗᵢ.norm_toContinuousLinearMap_le
set_option linter.uppercaseLean3 false in
#align submodule.norm_subtypeL_le Submodule.norm_subtypeL_le

end Submodule

end SemiNormed
