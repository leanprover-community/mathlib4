/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.NormedSpace.ContinuousLinearMap
import Mathlib.Analysis.NormedSpace.LinearIsometry
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Algebra.Module.StrongTopology
import Mathlib.Tactic.SuppressCompilation

#align_import analysis.normed_space.operator_norm from "leanprover-community/mathlib"@"f7ebde7ee0d1505dfccac8644ae12371aa3c1c9f"

/-!
# Operator norm on the space of continuous linear maps

Define the operator norm on the space of continuous (semi)linear maps between normed spaces, and
prove its basic properties. In particular, show that this space is itself a normed space.

Since a lot of elementary properties don't require `‖x‖ = 0 → x = 0` we start setting up the
theory for `SeminormedAddCommGroup` and we specialize to `NormedAddCommGroup` at the end.

Note that most of statements that apply to semilinear maps only hold when the ring homomorphism
is isometric, as expressed by the typeclass `[RingHomIsometric σ]`.

-/

suppress_compilation

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
  [NormedSpace 𝕜 Gₗ] {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

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
    isometry map from `𝕜` to `E` by taking multiples of `x`.-/
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

theorem isLeast_op_norm [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) :
    IsLeast {c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖} ‖f‖ := by
  refine IsClosed.isLeast_csInf ?_ bounds_nonempty bounds_bddBelow
  simp only [setOf_and, setOf_forall]
  refine isClosed_Ici.inter <| isClosed_iInter fun _ ↦ isClosed_le ?_ ?_ <;> continuity

/-- If one controls the norm of every `A x`, then one controls the norm of `A`. -/
theorem op_norm_le_bound (f : E →SL[σ₁₂] F) {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) :
    ‖f‖ ≤ M :=
  csInf_le bounds_bddBelow ⟨hMp, hM⟩
#align continuous_linear_map.op_norm_le_bound ContinuousLinearMap.op_norm_le_bound

/-- If one controls the norm of every `A x`, `‖x‖ ≠ 0`, then one controls the norm of `A`. -/
theorem op_norm_le_bound' (f : E →SL[σ₁₂] F) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ x, ‖x‖ ≠ 0 → ‖f x‖ ≤ M * ‖x‖) : ‖f‖ ≤ M :=
  op_norm_le_bound f hMp fun x =>
    (ne_or_eq ‖x‖ 0).elim (hM x) fun h => by
      simp only [h, mul_zero, norm_image_of_norm_zero f f.2 h, le_refl]
#align continuous_linear_map.op_norm_le_bound' ContinuousLinearMap.op_norm_le_bound'

theorem op_norm_le_of_lipschitz {f : E →SL[σ₁₂] F} {K : ℝ≥0} (hf : LipschitzWith K f) : ‖f‖ ≤ K :=
  f.op_norm_le_bound K.2 fun x => by
    simpa only [dist_zero_right, f.map_zero] using hf.dist_le_mul x 0
#align continuous_linear_map.op_norm_le_of_lipschitz ContinuousLinearMap.op_norm_le_of_lipschitz

theorem op_norm_eq_of_bounds {φ : E →SL[σ₁₂] F} {M : ℝ} (M_nonneg : 0 ≤ M)
    (h_above : ∀ x, ‖φ x‖ ≤ M * ‖x‖) (h_below : ∀ N ≥ 0, (∀ x, ‖φ x‖ ≤ N * ‖x‖) → M ≤ N) :
    ‖φ‖ = M :=
  le_antisymm (φ.op_norm_le_bound M_nonneg h_above)
    ((le_csInf_iff ContinuousLinearMap.bounds_bddBelow ⟨M, M_nonneg, h_above⟩).mpr
      fun N ⟨N_nonneg, hN⟩ => h_below N N_nonneg hN)
#align continuous_linear_map.op_norm_eq_of_bounds ContinuousLinearMap.op_norm_eq_of_bounds

theorem op_norm_neg (f : E →SL[σ₁₂] F) : ‖-f‖ = ‖f‖ := by simp only [norm_def, neg_apply, norm_neg]
#align continuous_linear_map.op_norm_neg ContinuousLinearMap.op_norm_neg

theorem op_norm_nonneg (f : E →SL[σ₁₂] F) : 0 ≤ ‖f‖ :=
  Real.sInf_nonneg _ fun _ ↦ And.left
#align continuous_linear_map.op_norm_nonneg ContinuousLinearMap.op_norm_nonneg

/-- The norm of the `0` operator is `0`. -/
theorem op_norm_zero : ‖(0 : E →SL[σ₁₂] F)‖ = 0 :=
  le_antisymm (op_norm_le_bound _ le_rfl fun _ ↦ by simp) (op_norm_nonneg _)
#align continuous_linear_map.op_norm_zero ContinuousLinearMap.op_norm_zero

/-- The norm of the identity is at most `1`. It is in fact `1`, except when the space is trivial
where it is `0`. It means that one can not do better than an inequality in general. -/
theorem norm_id_le : ‖id 𝕜 E‖ ≤ 1 :=
  op_norm_le_bound _ zero_le_one fun x => by simp
#align continuous_linear_map.norm_id_le ContinuousLinearMap.norm_id_le

section

variable [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₃] (f g : E →SL[σ₁₂] F) (h : F →SL[σ₂₃] G)
  (x : E)

/-- The fundamental property of the operator norm: `‖f x‖ ≤ ‖f‖ * ‖x‖`. -/
theorem le_op_norm : ‖f x‖ ≤ ‖f‖ * ‖x‖ := (isLeast_op_norm f).1.2 x
#align continuous_linear_map.le_op_norm ContinuousLinearMap.le_op_norm

theorem dist_le_op_norm (x y : E) : dist (f x) (f y) ≤ ‖f‖ * dist x y := by
  simp_rw [dist_eq_norm, ← map_sub, f.le_op_norm]
#align continuous_linear_map.dist_le_op_norm ContinuousLinearMap.dist_le_op_norm

theorem le_of_op_norm_le_of_le {x} {a b : ℝ} (hf : ‖f‖ ≤ a) (hx : ‖x‖ ≤ b) :
    ‖f x‖ ≤ a * b :=
  (f.le_op_norm x).trans <| by gcongr; exact (op_norm_nonneg f).trans hf

theorem le_op_norm_of_le {c : ℝ} {x} (h : ‖x‖ ≤ c) : ‖f x‖ ≤ ‖f‖ * c :=
  f.le_of_op_norm_le_of_le le_rfl h
#align continuous_linear_map.le_op_norm_of_le ContinuousLinearMap.le_op_norm_of_le

theorem le_of_op_norm_le {c : ℝ} (h : ‖f‖ ≤ c) (x : E) : ‖f x‖ ≤ c * ‖x‖ :=
  f.le_of_op_norm_le_of_le h le_rfl
#align continuous_linear_map.le_of_op_norm_le ContinuousLinearMap.le_of_op_norm_le

theorem op_norm_le_iff {f : E →SL[σ₁₂] F} {M : ℝ} (hMp : 0 ≤ M) :
    ‖f‖ ≤ M ↔ ∀ x, ‖f x‖ ≤ M * ‖x‖ :=
  ⟨f.le_of_op_norm_le, op_norm_le_bound f hMp⟩

theorem ratio_le_op_norm : ‖f x‖ / ‖x‖ ≤ ‖f‖ :=
  div_le_of_nonneg_of_le_mul (norm_nonneg _) f.op_norm_nonneg (le_op_norm _ _)
#align continuous_linear_map.ratio_le_op_norm ContinuousLinearMap.ratio_le_op_norm

/-- The image of the unit ball under a continuous linear map is bounded. -/
theorem unit_le_op_norm : ‖x‖ ≤ 1 → ‖f x‖ ≤ ‖f‖ :=
  mul_one ‖f‖ ▸ f.le_op_norm_of_le
#align continuous_linear_map.unit_le_op_norm ContinuousLinearMap.unit_le_op_norm

theorem op_norm_le_of_shell {f : E →SL[σ₁₂] F} {ε C : ℝ} (ε_pos : 0 < ε) (hC : 0 ≤ C) {c : 𝕜}
    (hc : 1 < ‖c‖) (hf : ∀ x, ε / ‖c‖ ≤ ‖x‖ → ‖x‖ < ε → ‖f x‖ ≤ C * ‖x‖) : ‖f‖ ≤ C :=
  f.op_norm_le_bound' hC fun _ hx => SemilinearMapClass.bound_of_shell_semi_normed f ε_pos hc hf hx
#align continuous_linear_map.op_norm_le_of_shell ContinuousLinearMap.op_norm_le_of_shell

theorem op_norm_le_of_ball {f : E →SL[σ₁₂] F} {ε : ℝ} {C : ℝ} (ε_pos : 0 < ε) (hC : 0 ≤ C)
    (hf : ∀ x ∈ ball (0 : E) ε, ‖f x‖ ≤ C * ‖x‖) : ‖f‖ ≤ C := by
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  refine' op_norm_le_of_shell ε_pos hC hc fun x _ hx => hf x _
  rwa [ball_zero_eq]
#align continuous_linear_map.op_norm_le_of_ball ContinuousLinearMap.op_norm_le_of_ball

theorem op_norm_le_of_nhds_zero {f : E →SL[σ₁₂] F} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ᶠ x in 𝓝 (0 : E), ‖f x‖ ≤ C * ‖x‖) : ‖f‖ ≤ C :=
  let ⟨_, ε0, hε⟩ := Metric.eventually_nhds_iff_ball.1 hf
  op_norm_le_of_ball ε0 hC hε
#align continuous_linear_map.op_norm_le_of_nhds_zero ContinuousLinearMap.op_norm_le_of_nhds_zero

theorem op_norm_le_of_shell' {f : E →SL[σ₁₂] F} {ε C : ℝ} (ε_pos : 0 < ε) (hC : 0 ≤ C) {c : 𝕜}
    (hc : ‖c‖ < 1) (hf : ∀ x, ε * ‖c‖ ≤ ‖x‖ → ‖x‖ < ε → ‖f x‖ ≤ C * ‖x‖) : ‖f‖ ≤ C := by
  by_cases h0 : c = 0
  · refine' op_norm_le_of_ball ε_pos hC fun x hx => hf x _ _
    · simp [h0]
    · rwa [ball_zero_eq] at hx
  · rw [← inv_inv c, norm_inv, inv_lt_one_iff_of_pos (norm_pos_iff.2 <| inv_ne_zero h0)] at hc
    refine' op_norm_le_of_shell ε_pos hC hc _
    rwa [norm_inv, div_eq_mul_inv, inv_inv]
#align continuous_linear_map.op_norm_le_of_shell' ContinuousLinearMap.op_norm_le_of_shell'

/-- For a continuous real linear map `f`, if one controls the norm of every `f x`, `‖x‖ = 1`, then
one controls the norm of `f`. -/
theorem op_norm_le_of_unit_norm [NormedSpace ℝ E] [NormedSpace ℝ F] {f : E →L[ℝ] F} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x, ‖x‖ = 1 → ‖f x‖ ≤ C) : ‖f‖ ≤ C := by
  refine' op_norm_le_bound' f hC fun x hx => _
  have H₁ : ‖‖x‖⁻¹ • x‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel hx]
  have H₂ := hf _ H₁
  rwa [map_smul, norm_smul, norm_inv, norm_norm, ← div_eq_inv_mul, _root_.div_le_iff] at H₂
  exact (norm_nonneg x).lt_of_ne' hx
#align continuous_linear_map.op_norm_le_of_unit_norm ContinuousLinearMap.op_norm_le_of_unit_norm

/-- The operator norm satisfies the triangle inequality. -/
theorem op_norm_add_le : ‖f + g‖ ≤ ‖f‖ + ‖g‖ :=
  (f + g).op_norm_le_bound (add_nonneg f.op_norm_nonneg g.op_norm_nonneg) fun x =>
    (norm_add_le_of_le (f.le_op_norm x) (g.le_op_norm x)).trans_eq (add_mul _ _ _).symm
#align continuous_linear_map.op_norm_add_le ContinuousLinearMap.op_norm_add_le

/-- If there is an element with norm different from `0`, then the norm of the identity equals `1`.
(Since we are working with seminorms supposing that the space is non-trivial is not enough.) -/
theorem norm_id_of_nontrivial_seminorm (h : ∃ x : E, ‖x‖ ≠ 0) : ‖id 𝕜 E‖ = 1 :=
  le_antisymm norm_id_le <| by
    let ⟨x, hx⟩ := h
    have := (id 𝕜 E).ratio_le_op_norm x
    rwa [id_apply, div_self hx] at this
#align continuous_linear_map.norm_id_of_nontrivial_seminorm ContinuousLinearMap.norm_id_of_nontrivial_seminorm

theorem op_norm_smul_le {𝕜' : Type*} [NormedField 𝕜'] [NormedSpace 𝕜' F] [SMulCommClass 𝕜₂ 𝕜' F]
    (c : 𝕜') (f : E →SL[σ₁₂] F) : ‖c • f‖ ≤ ‖c‖ * ‖f‖ :=
  (c • f).op_norm_le_bound (mul_nonneg (norm_nonneg _) (op_norm_nonneg _)) fun _ => by
    erw [norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (le_op_norm _ _) (norm_nonneg _)
#align continuous_linear_map.op_norm_smul_le ContinuousLinearMap.op_norm_smul_le

/-- Operator seminorm on the space of continuous (semi)linear maps, as `Seminorm`.

We use this seminorm to define a `SeminormedGroup` structure on `E →SL[σ] F`,
but we have to override the projection `UniformSpace`
so that it is definitionally equal to the one coming from the topologies on `E` and `F`. -/
protected def seminorm : Seminorm 𝕜₂ (E →SL[σ₁₂] F) :=
  .ofSMulLE norm op_norm_zero op_norm_add_le op_norm_smul_le

private lemma uniformity_eq_seminorm :
    𝓤 (E →SL[σ₁₂] F) = ⨅ r > 0, 𝓟 {f | ‖f.1 - f.2‖ < r} := by
  refine ContinuousLinearMap.seminorm.uniformity_eq_of_hasBasis
    (ContinuousLinearMap.hasBasis_nhds_zero_of_basis Metric.nhds_basis_closedBall)
    ?_ fun (s, r) ⟨hs, hr⟩ ↦ ?_
  · rcases NormedField.exists_lt_norm 𝕜 1 with ⟨c, hc⟩
    refine ⟨‖c‖, ContinuousLinearMap.hasBasis_nhds_zero.mem_iff.2
      ⟨(closedBall 0 1, closedBall 0 1), ?_⟩⟩
    suffices ∀ f : E →SL[σ₁₂] F, (∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ 1) → ‖f‖ ≤ ‖c‖ by
      simpa [NormedSpace.isVonNBounded_closedBall, closedBall_mem_nhds, subset_def] using this
    intro f hf
    refine op_norm_le_of_shell (f := f) one_pos (norm_nonneg c) hc fun x hcx hx ↦ ?_
    exact (hf x hx.le).trans ((div_le_iff' <| one_pos.trans hc).1 hcx)
  · rcases (NormedSpace.isVonNBounded_iff' _ _ _).1 hs with ⟨ε, hε⟩
    rcases exists_pos_mul_lt hr ε with ⟨δ, hδ₀, hδ⟩
    refine ⟨δ, hδ₀, fun f hf x hx ↦ ?_⟩
    simp only [Seminorm.mem_ball_zero, mem_closedBall_zero_iff] at hf ⊢
    rw [mul_comm] at hδ
    exact le_trans (le_of_op_norm_le_of_le _ hf.le (hε _ hx)) hδ.le

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

theorem nnnorm_def (f : E →SL[σ₁₂] F) : ‖f‖₊ = sInf { c | ∀ x, ‖f x‖₊ ≤ c * ‖x‖₊ } := by
  ext
  rw [NNReal.coe_sInf, coe_nnnorm, norm_def, NNReal.coe_image]
  simp_rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm, mem_setOf_eq, NNReal.coe_mk,
    exists_prop]
#align continuous_linear_map.nnnorm_def ContinuousLinearMap.nnnorm_def

/-- If one controls the norm of every `A x`, then one controls the norm of `A`. -/
theorem op_nnnorm_le_bound (f : E →SL[σ₁₂] F) (M : ℝ≥0) (hM : ∀ x, ‖f x‖₊ ≤ M * ‖x‖₊) : ‖f‖₊ ≤ M :=
  op_norm_le_bound f (zero_le M) hM
#align continuous_linear_map.op_nnnorm_le_bound ContinuousLinearMap.op_nnnorm_le_bound

/-- If one controls the norm of every `A x`, `‖x‖₊ ≠ 0`, then one controls the norm of `A`. -/
theorem op_nnnorm_le_bound' (f : E →SL[σ₁₂] F) (M : ℝ≥0) (hM : ∀ x, ‖x‖₊ ≠ 0 → ‖f x‖₊ ≤ M * ‖x‖₊) :
    ‖f‖₊ ≤ M :=
  op_norm_le_bound' f (zero_le M) fun x hx => hM x <| by rwa [← NNReal.coe_ne_zero]
#align continuous_linear_map.op_nnnorm_le_bound' ContinuousLinearMap.op_nnnorm_le_bound'

/-- For a continuous real linear map `f`, if one controls the norm of every `f x`, `‖x‖₊ = 1`, then
one controls the norm of `f`. -/
theorem op_nnnorm_le_of_unit_nnnorm [NormedSpace ℝ E] [NormedSpace ℝ F] {f : E →L[ℝ] F} {C : ℝ≥0}
    (hf : ∀ x, ‖x‖₊ = 1 → ‖f x‖₊ ≤ C) : ‖f‖₊ ≤ C :=
  op_norm_le_of_unit_norm C.coe_nonneg fun x hx => hf x <| by rwa [← NNReal.coe_eq_one]
#align continuous_linear_map.op_nnnorm_le_of_unit_nnnorm ContinuousLinearMap.op_nnnorm_le_of_unit_nnnorm

theorem op_nnnorm_le_of_lipschitz {f : E →SL[σ₁₂] F} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ‖f‖₊ ≤ K :=
  op_norm_le_of_lipschitz hf
#align continuous_linear_map.op_nnnorm_le_of_lipschitz ContinuousLinearMap.op_nnnorm_le_of_lipschitz

theorem op_nnnorm_eq_of_bounds {φ : E →SL[σ₁₂] F} (M : ℝ≥0) (h_above : ∀ x, ‖φ x‖₊ ≤ M * ‖x‖₊)
    (h_below : ∀ N, (∀ x, ‖φ x‖₊ ≤ N * ‖x‖₊) → M ≤ N) : ‖φ‖₊ = M :=
  Subtype.ext <| op_norm_eq_of_bounds (zero_le M) h_above <| Subtype.forall'.mpr h_below
#align continuous_linear_map.op_nnnorm_eq_of_bounds ContinuousLinearMap.op_nnnorm_eq_of_bounds

theorem op_nnnorm_le_iff {f : E →SL[σ₁₂] F} {C : ℝ≥0} : ‖f‖₊ ≤ C ↔ ∀ x, ‖f x‖₊ ≤ C * ‖x‖₊ :=
  op_norm_le_iff C.2

theorem isLeast_op_nnnorm : IsLeast {C : ℝ≥0 | ∀ x, ‖f x‖₊ ≤ C * ‖x‖₊} ‖f‖₊ := by
  simpa only [← op_nnnorm_le_iff] using isLeast_Ici

instance toNormedSpace {𝕜' : Type*} [NormedField 𝕜'] [NormedSpace 𝕜' F] [SMulCommClass 𝕜₂ 𝕜' F] :
    NormedSpace 𝕜' (E →SL[σ₁₂] F) :=
  ⟨op_norm_smul_le⟩
#align continuous_linear_map.to_normed_space ContinuousLinearMap.toNormedSpace

/-- The operator norm is submultiplicative. -/
theorem op_norm_comp_le (f : E →SL[σ₁₂] F) : ‖h.comp f‖ ≤ ‖h‖ * ‖f‖ :=
  csInf_le bounds_bddBelow
    ⟨mul_nonneg (op_norm_nonneg _) (op_norm_nonneg _), fun x => by
      rw [mul_assoc]
      exact h.le_op_norm_of_le (f.le_op_norm x)⟩
#align continuous_linear_map.op_norm_comp_le ContinuousLinearMap.op_norm_comp_le

theorem op_nnnorm_comp_le [RingHomIsometric σ₁₃] (f : E →SL[σ₁₂] F) : ‖h.comp f‖₊ ≤ ‖h‖₊ * ‖f‖₊ :=
  op_norm_comp_le h f
#align continuous_linear_map.op_nnnorm_comp_le ContinuousLinearMap.op_nnnorm_comp_le

/-- Continuous linear maps form a seminormed ring with respect to the operator norm. -/
instance toSemiNormedRing : SeminormedRing (E →L[𝕜] E) :=
  { ContinuousLinearMap.toSeminormedAddCommGroup, ContinuousLinearMap.ring with
    norm_mul := fun f g => op_norm_comp_le f g }
#align continuous_linear_map.to_semi_normed_ring ContinuousLinearMap.toSemiNormedRing

/-- For a normed space `E`, continuous linear endomorphisms form a normed algebra with
respect to the operator norm. -/
instance toNormedAlgebra : NormedAlgebra 𝕜 (E →L[𝕜] E) :=
  { algebra with
    norm_smul_le := by
      intro c f
      apply op_norm_smul_le c f}
#align continuous_linear_map.to_normed_algebra ContinuousLinearMap.toNormedAlgebra

theorem le_op_nnnorm : ‖f x‖₊ ≤ ‖f‖₊ * ‖x‖₊ :=
  f.le_op_norm x
#align continuous_linear_map.le_op_nnnorm ContinuousLinearMap.le_op_nnnorm

theorem nndist_le_op_nnnorm (x y : E) : nndist (f x) (f y) ≤ ‖f‖₊ * nndist x y :=
  dist_le_op_norm f x y
#align continuous_linear_map.nndist_le_op_nnnorm ContinuousLinearMap.nndist_le_op_nnnorm

/-- continuous linear maps are Lipschitz continuous. -/
theorem lipschitz : LipschitzWith ‖f‖₊ f :=
  AddMonoidHomClass.lipschitz_of_bound_nnnorm f _ f.le_op_nnnorm
#align continuous_linear_map.lipschitz ContinuousLinearMap.lipschitz

/-- Evaluation of a continuous linear map `f` at a point is Lipschitz continuous in `f`. -/
theorem lipschitz_apply (x : E) : LipschitzWith ‖x‖₊ fun f : E →SL[σ₁₂] F => f x :=
  lipschitzWith_iff_norm_sub_le.2 fun f g => ((f - g).le_op_norm x).trans_eq (mul_comm _ _)
#align continuous_linear_map.lipschitz_apply ContinuousLinearMap.lipschitz_apply

end

section Sup

variable [RingHomIsometric σ₁₂]

theorem exists_mul_lt_apply_of_lt_op_nnnorm (f : E →SL[σ₁₂] F) {r : ℝ≥0} (hr : r < ‖f‖₊) :
    ∃ x, r * ‖x‖₊ < ‖f x‖₊ := by
  simpa only [not_forall, not_le, Set.mem_setOf] using
    not_mem_of_lt_csInf (nnnorm_def f ▸ hr : r < sInf { c : ℝ≥0 | ∀ x, ‖f x‖₊ ≤ c * ‖x‖₊ })
      (OrderBot.bddBelow _)
#align continuous_linear_map.exists_mul_lt_apply_of_lt_op_nnnorm ContinuousLinearMap.exists_mul_lt_apply_of_lt_op_nnnorm

theorem exists_mul_lt_of_lt_op_norm (f : E →SL[σ₁₂] F) {r : ℝ} (hr₀ : 0 ≤ r) (hr : r < ‖f‖) :
    ∃ x, r * ‖x‖ < ‖f x‖ := by
  lift r to ℝ≥0 using hr₀
  exact f.exists_mul_lt_apply_of_lt_op_nnnorm hr
#align continuous_linear_map.exists_mul_lt_of_lt_op_norm ContinuousLinearMap.exists_mul_lt_of_lt_op_norm

theorem exists_lt_apply_of_lt_op_nnnorm {𝕜 𝕜₂ E F : Type*} [NormedAddCommGroup E]
    [SeminormedAddCommGroup F] [DenselyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
    [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) {r : ℝ≥0}
    (hr : r < ‖f‖₊) : ∃ x : E, ‖x‖₊ < 1 ∧ r < ‖f x‖₊ := by
  obtain ⟨y, hy⟩ := f.exists_mul_lt_apply_of_lt_op_nnnorm hr
  have hy' : ‖y‖₊ ≠ 0 :=
    nnnorm_ne_zero_iff.2 fun heq => by
      simp [heq, nnnorm_zero, map_zero, not_lt_zero'] at hy
  have hfy : ‖f y‖₊ ≠ 0 := (zero_le'.trans_lt hy).ne'
  rw [← inv_inv ‖f y‖₊, NNReal.lt_inv_iff_mul_lt (inv_ne_zero hfy), mul_assoc, mul_comm ‖y‖₊, ←
    mul_assoc, ← NNReal.lt_inv_iff_mul_lt hy'] at hy
  obtain ⟨k, hk₁, hk₂⟩ := NormedField.exists_lt_nnnorm_lt 𝕜 hy
  refine' ⟨k • y, (nnnorm_smul k y).symm ▸ (NNReal.lt_inv_iff_mul_lt hy').1 hk₂, _⟩
  have : ‖σ₁₂ k‖₊ = ‖k‖₊ := Subtype.ext RingHomIsometric.is_iso
  rwa [map_smulₛₗ f, nnnorm_smul, ← NNReal.div_lt_iff hfy, div_eq_mul_inv, this]
#align continuous_linear_map.exists_lt_apply_of_lt_op_nnnorm ContinuousLinearMap.exists_lt_apply_of_lt_op_nnnorm

theorem exists_lt_apply_of_lt_op_norm {𝕜 𝕜₂ E F : Type*} [NormedAddCommGroup E]
    [SeminormedAddCommGroup F] [DenselyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
    [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) {r : ℝ}
    (hr : r < ‖f‖) : ∃ x : E, ‖x‖ < 1 ∧ r < ‖f x‖ := by
  by_cases hr₀ : r < 0
  · exact ⟨0, by simpa using hr₀⟩
  · lift r to ℝ≥0 using not_lt.1 hr₀
    exact f.exists_lt_apply_of_lt_op_nnnorm hr
#align continuous_linear_map.exists_lt_apply_of_lt_op_norm ContinuousLinearMap.exists_lt_apply_of_lt_op_norm

theorem sSup_unit_ball_eq_nnnorm {𝕜 𝕜₂ E F : Type*} [NormedAddCommGroup E]
    [SeminormedAddCommGroup F] [DenselyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
    [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) :
    sSup ((fun x => ‖f x‖₊) '' ball 0 1) = ‖f‖₊ := by
  refine' csSup_eq_of_forall_le_of_forall_lt_exists_gt ((nonempty_ball.mpr zero_lt_one).image _) _
    fun ub hub => _
  · rintro - ⟨x, hx, rfl⟩
    simpa only [mul_one] using f.le_op_norm_of_le (mem_ball_zero_iff.1 hx).le
  · obtain ⟨x, hx, hxf⟩ := f.exists_lt_apply_of_lt_op_nnnorm hub
    exact ⟨_, ⟨x, mem_ball_zero_iff.2 hx, rfl⟩, hxf⟩
#align continuous_linear_map.Sup_unit_ball_eq_nnnorm ContinuousLinearMap.sSup_unit_ball_eq_nnnorm

theorem sSup_unit_ball_eq_norm {𝕜 𝕜₂ E F : Type*} [NormedAddCommGroup E] [SeminormedAddCommGroup F]
    [DenselyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂} [NormedSpace 𝕜 E]
    [NormedSpace 𝕜₂ F] [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) :
    sSup ((fun x => ‖f x‖) '' ball 0 1) = ‖f‖ := by
  simpa only [NNReal.coe_sSup, Set.image_image] using NNReal.coe_eq.2 f.sSup_unit_ball_eq_nnnorm
#align continuous_linear_map.Sup_unit_ball_eq_norm ContinuousLinearMap.sSup_unit_ball_eq_norm

theorem sSup_unit_closedBall_eq_nnnorm {𝕜 𝕜₂ E F : Type*} [NormedAddCommGroup E]
    [SeminormedAddCommGroup F] [DenselyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
    [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) :
    sSup ((fun x => ‖f x‖₊) '' closedBall 0 1) = ‖f‖₊ := by
  have hbdd : ∀ y ∈ (fun x => ‖f x‖₊) '' closedBall 0 1, y ≤ ‖f‖₊ := by
    rintro - ⟨x, hx, rfl⟩
    exact f.unit_le_op_norm x (mem_closedBall_zero_iff.1 hx)
  refine' le_antisymm (csSup_le ((nonempty_closedBall.mpr zero_le_one).image _) hbdd) _
  rw [← sSup_unit_ball_eq_nnnorm]
  exact csSup_le_csSup ⟨‖f‖₊, hbdd⟩ ((nonempty_ball.2 zero_lt_one).image _)
    (Set.image_subset _ ball_subset_closedBall)
#align continuous_linear_map.Sup_closed_unit_ball_eq_nnnorm ContinuousLinearMap.sSup_unit_closedBall_eq_nnnorm

theorem sSup_unit_closedBall_eq_norm {𝕜 𝕜₂ E F : Type*} [NormedAddCommGroup E]
    [SeminormedAddCommGroup F] [DenselyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
    [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) :
    sSup ((fun x => ‖f x‖) '' closedBall 0 1) = ‖f‖ := by
  simpa only [NNReal.coe_sSup, Set.image_image] using
    NNReal.coe_eq.2 f.sSup_unit_closedBall_eq_nnnorm
#align continuous_linear_map.Sup_closed_unit_ball_eq_norm ContinuousLinearMap.sSup_unit_closedBall_eq_norm

end Sup

section

theorem op_norm_ext [RingHomIsometric σ₁₃] (f : E →SL[σ₁₂] F) (g : E →SL[σ₁₃] G)
    (h : ∀ x, ‖f x‖ = ‖g x‖) : ‖f‖ = ‖g‖ :=
  op_norm_eq_of_bounds (norm_nonneg _)
    (fun x => by
      rw [h x]
      exact le_op_norm _ _)
    fun c hc h₂ =>
    op_norm_le_bound _ hc fun z => by
      rw [← h z]
      exact h₂ z
#align continuous_linear_map.op_norm_ext ContinuousLinearMap.op_norm_ext

variable [RingHomIsometric σ₂₃]

theorem op_norm_le_bound₂ (f : E →SL[σ₁₃] F →SL[σ₂₃] G) {C : ℝ} (h0 : 0 ≤ C)
    (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) : ‖f‖ ≤ C :=
  f.op_norm_le_bound h0 fun x => (f x).op_norm_le_bound (mul_nonneg h0 (norm_nonneg _)) <| hC x
#align continuous_linear_map.op_norm_le_bound₂ ContinuousLinearMap.op_norm_le_bound₂

theorem le_op_norm₂ [RingHomIsometric σ₁₃] (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (x : E) (y : F) :
    ‖f x y‖ ≤ ‖f‖ * ‖x‖ * ‖y‖ :=
  (f x).le_of_op_norm_le (f.le_op_norm x) y
#align continuous_linear_map.le_op_norm₂ ContinuousLinearMap.le_op_norm₂

-- porting note: new theorem
theorem le_of_op_norm₂_le_of_le [RingHomIsometric σ₁₃] (f : E →SL[σ₁₃] F →SL[σ₂₃] G) {x : E} {y : F}
    {a b c : ℝ} (hf : ‖f‖ ≤ a) (hx : ‖x‖ ≤ b) (hy : ‖y‖ ≤ c) :
    ‖f x y‖ ≤ a * b * c :=
  (f x).le_of_op_norm_le_of_le (f.le_of_op_norm_le_of_le hf hx) hy

end

@[simp]
theorem op_norm_prod (f : E →L[𝕜] Fₗ) (g : E →L[𝕜] Gₗ) : ‖f.prod g‖ = ‖(f, g)‖ :=
  le_antisymm
      (op_norm_le_bound _ (norm_nonneg _) fun x => by
        simpa only [prod_apply, Prod.norm_def, max_mul_of_nonneg, norm_nonneg] using
          max_le_max (le_op_norm f x) (le_op_norm g x)) <|
    max_le
      (op_norm_le_bound _ (norm_nonneg _) fun x =>
        (le_max_left _ _).trans ((f.prod g).le_op_norm x))
      (op_norm_le_bound _ (norm_nonneg _) fun x =>
        (le_max_right _ _).trans ((f.prod g).le_op_norm x))
#align continuous_linear_map.op_norm_prod ContinuousLinearMap.op_norm_prod

@[simp]
theorem op_nnnorm_prod (f : E →L[𝕜] Fₗ) (g : E →L[𝕜] Gₗ) : ‖f.prod g‖₊ = ‖(f, g)‖₊ :=
  Subtype.ext <| op_norm_prod f g
#align continuous_linear_map.op_nnnorm_prod ContinuousLinearMap.op_nnnorm_prod

/-- `ContinuousLinearMap.prod` as a `LinearIsometryEquiv`. -/
def prodₗᵢ (R : Type*) [Semiring R] [Module R Fₗ] [Module R Gₗ] [ContinuousConstSMul R Fₗ]
    [ContinuousConstSMul R Gₗ] [SMulCommClass 𝕜 R Fₗ] [SMulCommClass 𝕜 R Gₗ] :
    (E →L[𝕜] Fₗ) × (E →L[𝕜] Gₗ) ≃ₗᵢ[R] E →L[𝕜] Fₗ × Gₗ :=
  ⟨prodₗ R, fun ⟨f, g⟩ => op_norm_prod f g⟩
#align continuous_linear_map.prodₗᵢ ContinuousLinearMap.prodₗᵢ

variable [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F)

@[simp, nontriviality]
theorem op_norm_subsingleton [Subsingleton E] : ‖f‖ = 0 := by
  refine' le_antisymm _ (norm_nonneg _)
  apply op_norm_le_bound _ rfl.ge
  intro x
  simp [Subsingleton.elim x 0]
#align continuous_linear_map.op_norm_subsingleton ContinuousLinearMap.op_norm_subsingleton

end OpNorm

section IsO

set_option linter.uppercaseLean3 false

variable [RingHomIsometric σ₁₂] (c : 𝕜) (f g : E →SL[σ₁₂] F) (h : F →SL[σ₂₃] G) (x y z : E)

open Asymptotics

theorem isBigOWith_id (l : Filter E) : IsBigOWith ‖f‖ l f fun x => x :=
  isBigOWith_of_le' _ f.le_op_norm
#align continuous_linear_map.is_O_with_id ContinuousLinearMap.isBigOWith_id

theorem isBigO_id (l : Filter E) : f =O[l] fun x => x :=
  (f.isBigOWith_id l).isBigO
#align continuous_linear_map.is_O_id ContinuousLinearMap.isBigO_id

theorem isBigOWith_comp [RingHomIsometric σ₂₃] {α : Type*} (g : F →SL[σ₂₃] G) (f : α → F)
    (l : Filter α) : IsBigOWith ‖g‖ l (fun x' => g (f x')) f :=
  (g.isBigOWith_id ⊤).comp_tendsto le_top
#align continuous_linear_map.is_O_with_comp ContinuousLinearMap.isBigOWith_comp

theorem isBigO_comp [RingHomIsometric σ₂₃] {α : Type*} (g : F →SL[σ₂₃] G) (f : α → F)
    (l : Filter α) : (fun x' => g (f x')) =O[l] f :=
  (g.isBigOWith_comp f l).isBigO
#align continuous_linear_map.is_O_comp ContinuousLinearMap.isBigO_comp

theorem isBigOWith_sub (f : E →SL[σ₁₂] F) (l : Filter E) (x : E) :
    IsBigOWith ‖f‖ l (fun x' => f (x' - x)) fun x' => x' - x :=
  f.isBigOWith_comp _ l
#align continuous_linear_map.is_O_with_sub ContinuousLinearMap.isBigOWith_sub

theorem isBigO_sub (f : E →SL[σ₁₂] F) (l : Filter E) (x : E) :
    (fun x' => f (x' - x)) =O[l] fun x' => x' - x :=
  f.isBigO_comp _ l
#align continuous_linear_map.is_O_sub ContinuousLinearMap.isBigO_sub

end IsO

end ContinuousLinearMap

namespace LinearIsometry

theorem norm_toContinuousLinearMap_le (f : E →ₛₗᵢ[σ₁₂] F) : ‖f.toContinuousLinearMap‖ ≤ 1 :=
  f.toContinuousLinearMap.op_norm_le_bound zero_le_one fun x => by simp
#align linear_isometry.norm_to_continuous_linear_map_le LinearIsometry.norm_toContinuousLinearMap_le

end LinearIsometry

namespace LinearMap

/-- If a continuous linear map is constructed from a linear map via the constructor `mkContinuous`,
then its norm is bounded by the bound given to the constructor if it is nonnegative. -/
theorem mkContinuous_norm_le (f : E →ₛₗ[σ₁₂] F) {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    ‖f.mkContinuous C h‖ ≤ C :=
  ContinuousLinearMap.op_norm_le_bound _ hC h
#align linear_map.mk_continuous_norm_le LinearMap.mkContinuous_norm_le

/-- If a continuous linear map is constructed from a linear map via the constructor `mkContinuous`,
then its norm is bounded by the bound or zero if bound is negative. -/
theorem mkContinuous_norm_le' (f : E →ₛₗ[σ₁₂] F) {C : ℝ} (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    ‖f.mkContinuous C h‖ ≤ max C 0 :=
  ContinuousLinearMap.op_norm_le_bound _ (le_max_right _ _) fun x =>
    (h x).trans <| mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg x)
#align linear_map.mk_continuous_norm_le' LinearMap.mkContinuous_norm_le'

variable [RingHomIsometric σ₂₃]

lemma norm_mkContinuous₂_aux (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) (C : ℝ)
    (h : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) (x : E) :
    ‖(f x).mkContinuous (C * ‖x‖) (h x)‖ ≤ max C 0 * ‖x‖ :=
  (mkContinuous_norm_le' (f x) (h x)).trans_eq <| by
    rw [max_mul_of_nonneg _ _ (norm_nonneg x), zero_mul]

/-- Create a bilinear map (represented as a map `E →L[𝕜] F →L[𝕜] G`) from the corresponding linear
map and existence of a bound on the norm of the image. The linear map can be constructed using
`LinearMap.mk₂`.

If you have an explicit bound, use `LinearMap.mkContinuous₂` instead, as a norm estimate will
follow automatically in `LinearMap.mkContinuous₂_norm_le`. -/
def mkContinuousOfExistsBound₂ (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G)
    (h : ∃ C, ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) : E →SL[σ₁₃] F →SL[σ₂₃] G :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun x => (f x).mkContinuousOfExistsBound <| let ⟨C, hC⟩ := h; ⟨C * ‖x‖, hC x⟩
      map_add' := fun x y => by
        ext z
        simp
      map_smul' := fun c x => by
        ext z
        simp } <|
    let ⟨C, hC⟩ := h; ⟨max C 0, norm_mkContinuous₂_aux f C hC⟩

/-- Create a bilinear map (represented as a map `E →L[𝕜] F →L[𝕜] G`) from the corresponding linear
map and a bound on the norm of the image. The linear map can be constructed using
`LinearMap.mk₂`. Lemmas `LinearMap.mkContinuous₂_norm_le'` and `LinearMap.mkContinuous₂_norm_le`
provide estimates on the norm of an operator constructed using this function. -/
def mkContinuous₂ (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) (C : ℝ) (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) :
    E →SL[σ₁₃] F →SL[σ₂₃] G :=
  mkContinuousOfExistsBound₂ f ⟨C, hC⟩
#align linear_map.mk_continuous₂ LinearMap.mkContinuous₂

@[simp]
theorem mkContinuous₂_apply (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) {C : ℝ}
    (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) (x : E) (y : F) : f.mkContinuous₂ C hC x y = f x y :=
  rfl
#align linear_map.mk_continuous₂_apply LinearMap.mkContinuous₂_apply

theorem mkContinuous₂_norm_le' (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) {C : ℝ}
    (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) : ‖f.mkContinuous₂ C hC‖ ≤ max C 0 :=
  mkContinuous_norm_le _ (le_max_iff.2 <| Or.inr le_rfl) (norm_mkContinuous₂_aux f C hC)
#align linear_map.mk_continuous₂_norm_le' LinearMap.mkContinuous₂_norm_le'

theorem mkContinuous₂_norm_le (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) {C : ℝ} (h0 : 0 ≤ C)
    (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) : ‖f.mkContinuous₂ C hC‖ ≤ C :=
  (f.mkContinuous₂_norm_le' hC).trans_eq <| max_eq_left h0
#align linear_map.mk_continuous₂_norm_le LinearMap.mkContinuous₂_norm_le

end LinearMap

namespace ContinuousLinearMap

variable [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃]

/-- Flip the order of arguments of a continuous bilinear map.
For a version bundled as `LinearIsometryEquiv`, see
`ContinuousLinearMap.flipL`. -/
def flip (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : F →SL[σ₂₃] E →SL[σ₁₃] G :=
  LinearMap.mkContinuous₂
    -- Porting note: the `simp only`s below used to be `rw`.
    -- Now that doesn't work as we need to do some beta reduction along the way.
    (LinearMap.mk₂'ₛₗ σ₂₃ σ₁₃ (fun y x => f x y) (fun x y z => (f z).map_add x y)
      (fun c y x => (f x).map_smulₛₗ c y) (fun z x y => by simp only [f.map_add, add_apply])
        (fun c y x => by simp only [f.map_smulₛₗ, smul_apply]))
    ‖f‖ fun y x => (f.le_op_norm₂ x y).trans_eq <| by simp only [mul_right_comm]
#align continuous_linear_map.flip ContinuousLinearMap.flip

private theorem le_norm_flip (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : ‖f‖ ≤ ‖flip f‖ :=
  f.op_norm_le_bound₂ (norm_nonneg _) fun x y => by
    rw [mul_right_comm]
    exact (flip f).le_op_norm₂ y x

@[simp]
theorem flip_apply (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (x : E) (y : F) : f.flip y x = f x y :=
  rfl
#align continuous_linear_map.flip_apply ContinuousLinearMap.flip_apply

@[simp]
theorem flip_flip (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : f.flip.flip = f := by
  ext
  rfl
#align continuous_linear_map.flip_flip ContinuousLinearMap.flip_flip

@[simp]
theorem op_norm_flip (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : ‖f.flip‖ = ‖f‖ :=
  le_antisymm (by simpa only [flip_flip] using le_norm_flip f.flip) (le_norm_flip f)
#align continuous_linear_map.op_norm_flip ContinuousLinearMap.op_norm_flip

@[simp]
theorem flip_add (f g : E →SL[σ₁₃] F →SL[σ₂₃] G) : (f + g).flip = f.flip + g.flip :=
  rfl
#align continuous_linear_map.flip_add ContinuousLinearMap.flip_add

@[simp]
theorem flip_smul (c : 𝕜₃) (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : (c • f).flip = c • f.flip :=
  rfl
#align continuous_linear_map.flip_smul ContinuousLinearMap.flip_smul

variable (E F G σ₁₃ σ₂₃)

/-- Flip the order of arguments of a continuous bilinear map.
This is a version bundled as a `LinearIsometryEquiv`.
For an unbundled version see `ContinuousLinearMap.flip`. -/
def flipₗᵢ' : (E →SL[σ₁₃] F →SL[σ₂₃] G) ≃ₗᵢ[𝕜₃] F →SL[σ₂₃] E →SL[σ₁₃] G where
  toFun := flip
  invFun := flip
  map_add' := flip_add
  map_smul' := flip_smul
  left_inv := flip_flip
  right_inv := flip_flip
  norm_map' := op_norm_flip
#align continuous_linear_map.flipₗᵢ' ContinuousLinearMap.flipₗᵢ'

variable {E F G σ₁₃ σ₂₃}

@[simp]
theorem flipₗᵢ'_symm : (flipₗᵢ' E F G σ₂₃ σ₁₃).symm = flipₗᵢ' F E G σ₁₃ σ₂₃ :=
  rfl
#align continuous_linear_map.flipₗᵢ'_symm ContinuousLinearMap.flipₗᵢ'_symm

@[simp]
theorem coe_flipₗᵢ' : ⇑(flipₗᵢ' E F G σ₂₃ σ₁₃) = flip :=
  rfl
#align continuous_linear_map.coe_flipₗᵢ' ContinuousLinearMap.coe_flipₗᵢ'

variable (𝕜 E Fₗ Gₗ)

/-- Flip the order of arguments of a continuous bilinear map.
This is a version bundled as a `LinearIsometryEquiv`.
For an unbundled version see `ContinuousLinearMap.flip`. -/
def flipₗᵢ : (E →L[𝕜] Fₗ →L[𝕜] Gₗ) ≃ₗᵢ[𝕜] Fₗ →L[𝕜] E →L[𝕜] Gₗ where
  toFun := flip
  invFun := flip
  map_add' := flip_add
  map_smul' := flip_smul
  left_inv := flip_flip
  right_inv := flip_flip
  norm_map' := op_norm_flip
#align continuous_linear_map.flipₗᵢ ContinuousLinearMap.flipₗᵢ

variable {𝕜 E Fₗ Gₗ}

@[simp]
theorem flipₗᵢ_symm : (flipₗᵢ 𝕜 E Fₗ Gₗ).symm = flipₗᵢ 𝕜 Fₗ E Gₗ :=
  rfl
#align continuous_linear_map.flipₗᵢ_symm ContinuousLinearMap.flipₗᵢ_symm

@[simp]
theorem coe_flipₗᵢ : ⇑(flipₗᵢ 𝕜 E Fₗ Gₗ) = flip :=
  rfl
#align continuous_linear_map.coe_flipₗᵢ ContinuousLinearMap.coe_flipₗᵢ

variable (F σ₁₂) [RingHomIsometric σ₁₂]

/-- The continuous semilinear map obtained by applying a continuous semilinear map at a given
vector.

This is the continuous version of `LinearMap.applyₗ`. -/
def apply' : E →SL[σ₁₂] (E →SL[σ₁₂] F) →L[𝕜₂] F :=
  flip (id 𝕜₂ (E →SL[σ₁₂] F))
#align continuous_linear_map.apply' ContinuousLinearMap.apply'

variable {F σ₁₂}

@[simp]
theorem apply_apply' (v : E) (f : E →SL[σ₁₂] F) : apply' F σ₁₂ v f = f v :=
  rfl
#align continuous_linear_map.apply_apply' ContinuousLinearMap.apply_apply'

variable (𝕜 Fₗ)

/-- The continuous semilinear map obtained by applying a continuous semilinear map at a given
vector.

This is the continuous version of `LinearMap.applyₗ`. -/
def apply : E →L[𝕜] (E →L[𝕜] Fₗ) →L[𝕜] Fₗ :=
  flip (id 𝕜 (E →L[𝕜] Fₗ))
#align continuous_linear_map.apply ContinuousLinearMap.apply

variable {𝕜 Fₗ}

@[simp]
theorem apply_apply (v : E) (f : E →L[𝕜] Fₗ) : apply 𝕜 Fₗ v f = f v :=
  rfl
#align continuous_linear_map.apply_apply ContinuousLinearMap.apply_apply

variable (σ₁₂ σ₂₃ E F G)

set_option linter.uppercaseLean3 false

/-- Composition of continuous semilinear maps as a continuous semibilinear map. -/
def compSL : (F →SL[σ₂₃] G) →L[𝕜₃] (E →SL[σ₁₂] F) →SL[σ₂₃] E →SL[σ₁₃] G :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (RingHom.id 𝕜₃) σ₂₃ comp add_comp smul_comp comp_add fun c f g => by
      ext
      simp only [ContinuousLinearMap.map_smulₛₗ, coe_smul', coe_comp', Function.comp_apply,
        Pi.smul_apply])
    1 fun f g => by simpa only [one_mul] using op_norm_comp_le f g
#align continuous_linear_map.compSL ContinuousLinearMap.compSL

theorem norm_compSL_le :
    -- porting note: added
    letI : Norm ((F →SL[σ₂₃] G) →L[𝕜₃] (E →SL[σ₁₂] F) →SL[σ₂₃] E →SL[σ₁₃] G) :=
      hasOpNorm (E := F →SL[σ₂₃] G) (F := (E →SL[σ₁₂] F) →SL[σ₂₃] E →SL[σ₁₃] G)
    ‖compSL E F G σ₁₂ σ₂₃‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _
#align continuous_linear_map.norm_compSL_le ContinuousLinearMap.norm_compSL_le

variable {σ₁₂ σ₂₃ E F G}

@[simp]
theorem compSL_apply (f : F →SL[σ₂₃] G) (g : E →SL[σ₁₂] F) : compSL E F G σ₁₂ σ₂₃ f g = f.comp g :=
  rfl
#align continuous_linear_map.compSL_apply ContinuousLinearMap.compSL_apply

theorem _root_.Continuous.const_clm_comp {X} [TopologicalSpace X] {f : X → E →SL[σ₁₂] F}
    (hf : Continuous f) (g : F →SL[σ₂₃] G) :
    Continuous (fun x => g.comp (f x) : X → E →SL[σ₁₃] G) :=
  (compSL E F G σ₁₂ σ₂₃ g).continuous.comp hf
#align continuous.const_clm_comp Continuous.const_clm_comp

-- Giving the implicit argument speeds up elaboration significantly
theorem _root_.Continuous.clm_comp_const {X} [TopologicalSpace X] {g : X → F →SL[σ₂₃] G}
    (hg : Continuous g) (f : E →SL[σ₁₂] F) :
    Continuous (fun x => (g x).comp f : X → E →SL[σ₁₃] G) :=
  (@ContinuousLinearMap.flip _ _ _ _ _ (E →SL[σ₁₃] G) _ _ _ _ _ _ _ _ _ _ _ _ _
    (compSL E F G σ₁₂ σ₂₃) f).continuous.comp hg
#align continuous.clm_comp_const Continuous.clm_comp_const

variable (𝕜 σ₁₂ σ₂₃ E Fₗ Gₗ)

/-- Composition of continuous linear maps as a continuous bilinear map. -/
def compL : (Fₗ →L[𝕜] Gₗ) →L[𝕜] (E →L[𝕜] Fₗ) →L[𝕜] E →L[𝕜] Gₗ :=
  compSL E Fₗ Gₗ (RingHom.id 𝕜) (RingHom.id 𝕜)
#align continuous_linear_map.compL ContinuousLinearMap.compL

theorem norm_compL_le :
    letI : Norm ((Fₗ →L[𝕜] Gₗ) →L[𝕜] (E →L[𝕜] Fₗ) →L[𝕜] E →L[𝕜] Gₗ) :=
      hasOpNorm (E := Fₗ →L[𝕜] Gₗ) (F := (E →L[𝕜] Fₗ) →L[𝕜] E →L[𝕜] Gₗ)
    ‖compL 𝕜 E Fₗ Gₗ‖ ≤ 1 :=
  norm_compSL_le _ _ _ _ _
#align continuous_linear_map.norm_compL_le ContinuousLinearMap.norm_compL_le

@[simp]
theorem compL_apply (f : Fₗ →L[𝕜] Gₗ) (g : E →L[𝕜] Fₗ) : compL 𝕜 E Fₗ Gₗ f g = f.comp g :=
  rfl
#align continuous_linear_map.compL_apply ContinuousLinearMap.compL_apply

variable (Eₗ) {𝕜 E Fₗ Gₗ}

/-- Apply `L(x,-)` pointwise to bilinear maps, as a continuous bilinear map -/
@[simps! apply]
def precompR (L : E →L[𝕜] Fₗ →L[𝕜] Gₗ) : E →L[𝕜] (Eₗ →L[𝕜] Fₗ) →L[𝕜] Eₗ →L[𝕜] Gₗ :=
  (compL 𝕜 Eₗ Fₗ Gₗ).comp L
#align continuous_linear_map.precompR ContinuousLinearMap.precompR

/-- Apply `L(-,y)` pointwise to bilinear maps, as a continuous bilinear map -/
def precompL (L : E →L[𝕜] Fₗ →L[𝕜] Gₗ) : (Eₗ →L[𝕜] E) →L[𝕜] Fₗ →L[𝕜] Eₗ →L[𝕜] Gₗ :=
  (precompR Eₗ (flip L)).flip
#align continuous_linear_map.precompL ContinuousLinearMap.precompL

theorem norm_precompR_le (L : E →L[𝕜] Fₗ →L[𝕜] Gₗ) :
    -- porting note: added
    letI : SeminormedAddCommGroup ((Eₗ →L[𝕜] Fₗ) →L[𝕜] Eₗ →L[𝕜] Gₗ) := inferInstance
    letI : NormedSpace 𝕜 ((Eₗ →L[𝕜] Fₗ) →L[𝕜] Eₗ →L[𝕜] Gₗ) := inferInstance
    ‖precompR Eₗ L‖ ≤ ‖L‖ :=
  calc
    ‖precompR Eₗ L‖ ≤ ‖compL 𝕜 Eₗ Fₗ Gₗ‖ * ‖L‖ := op_norm_comp_le _ _
    _ ≤ 1 * ‖L‖ := (mul_le_mul_of_nonneg_right (norm_compL_le _ _ _ _) (norm_nonneg _))
    _ = ‖L‖ := by rw [one_mul]
#align continuous_linear_map.norm_precompR_le ContinuousLinearMap.norm_precompR_le

theorem norm_precompL_le (L : E →L[𝕜] Fₗ →L[𝕜] Gₗ) :
    -- porting note: added
    letI : Norm ((Eₗ →L[𝕜] E) →L[𝕜] Fₗ →L[𝕜] Eₗ →L[𝕜] Gₗ) :=
      hasOpNorm (E := Eₗ →L[𝕜] E) (F := Fₗ →L[𝕜] Eₗ →L[𝕜] Gₗ)
    ‖precompL Eₗ L‖ ≤ ‖L‖ := by
  rw [precompL, op_norm_flip, ← op_norm_flip L]
  exact norm_precompR_le _ L.flip
#align continuous_linear_map.norm_precompL_le ContinuousLinearMap.norm_precompL_le

section Prod

universe u₁ u₂ u₃ u₄

variable (M₁ : Type u₁) [SeminormedAddCommGroup M₁] [NormedSpace 𝕜 M₁] (M₂ : Type u₂)
  [SeminormedAddCommGroup M₂] [NormedSpace 𝕜 M₂] (M₃ : Type u₃) [SeminormedAddCommGroup M₃]
  [NormedSpace 𝕜 M₃] (M₄ : Type u₄) [SeminormedAddCommGroup M₄] [NormedSpace 𝕜 M₄]

variable {Eₗ} (𝕜)

/-- `ContinuousLinearMap.prodMap` as a continuous linear map. -/
def prodMapL : (M₁ →L[𝕜] M₂) × (M₃ →L[𝕜] M₄) →L[𝕜] M₁ × M₃ →L[𝕜] M₂ × M₄ :=
  ContinuousLinearMap.copy
    (have Φ₁ : (M₁ →L[𝕜] M₂) →L[𝕜] M₁ →L[𝕜] M₂ × M₄ :=
      ContinuousLinearMap.compL 𝕜 M₁ M₂ (M₂ × M₄) (ContinuousLinearMap.inl 𝕜 M₂ M₄)
    have Φ₂ : (M₃ →L[𝕜] M₄) →L[𝕜] M₃ →L[𝕜] M₂ × M₄ :=
      ContinuousLinearMap.compL 𝕜 M₃ M₄ (M₂ × M₄) (ContinuousLinearMap.inr 𝕜 M₂ M₄)
    have Φ₁' :=
      (ContinuousLinearMap.compL 𝕜 (M₁ × M₃) M₁ (M₂ × M₄)).flip (ContinuousLinearMap.fst 𝕜 M₁ M₃)
    have Φ₂' :=
      (ContinuousLinearMap.compL 𝕜 (M₁ × M₃) M₃ (M₂ × M₄)).flip (ContinuousLinearMap.snd 𝕜 M₁ M₃)
    have Ψ₁ : (M₁ →L[𝕜] M₂) × (M₃ →L[𝕜] M₄) →L[𝕜] M₁ →L[𝕜] M₂ :=
      ContinuousLinearMap.fst 𝕜 (M₁ →L[𝕜] M₂) (M₃ →L[𝕜] M₄)
    have Ψ₂ : (M₁ →L[𝕜] M₂) × (M₃ →L[𝕜] M₄) →L[𝕜] M₃ →L[𝕜] M₄ :=
      ContinuousLinearMap.snd 𝕜 (M₁ →L[𝕜] M₂) (M₃ →L[𝕜] M₄)
    Φ₁' ∘L Φ₁ ∘L Ψ₁ + Φ₂' ∘L Φ₂ ∘L Ψ₂)
    (fun p : (M₁ →L[𝕜] M₂) × (M₃ →L[𝕜] M₄) => p.1.prodMap p.2) (by
      apply funext
      rintro ⟨φ, ψ⟩
      refine' ContinuousLinearMap.ext fun ⟨x₁, x₂⟩ => _
      dsimp
      simp)
#align continuous_linear_map.prod_mapL ContinuousLinearMap.prodMapL

variable {M₁ M₂ M₃ M₄}

@[simp]
theorem prodMapL_apply (p : (M₁ →L[𝕜] M₂) × (M₃ →L[𝕜] M₄)) :
    ContinuousLinearMap.prodMapL 𝕜 M₁ M₂ M₃ M₄ p = p.1.prodMap p.2 :=
  rfl
#align continuous_linear_map.prod_mapL_apply ContinuousLinearMap.prodMapL_apply

variable {X : Type*} [TopologicalSpace X]

theorem _root_.Continuous.prod_mapL {f : X → M₁ →L[𝕜] M₂} {g : X → M₃ →L[𝕜] M₄} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => (f x).prodMap (g x) :=
  (prodMapL 𝕜 M₁ M₂ M₃ M₄).continuous.comp (hf.prod_mk hg)
#align continuous.prod_mapL Continuous.prod_mapL

theorem _root_.Continuous.prod_map_equivL {f : X → M₁ ≃L[𝕜] M₂} {g : X → M₃ ≃L[𝕜] M₄}
    (hf : Continuous fun x => (f x : M₁ →L[𝕜] M₂)) (hg : Continuous fun x => (g x : M₃ →L[𝕜] M₄)) :
    Continuous fun x => ((f x).prod (g x) : M₁ × M₃ →L[𝕜] M₂ × M₄) :=
  (prodMapL 𝕜 M₁ M₂ M₃ M₄).continuous.comp (hf.prod_mk hg)
#align continuous.prod_map_equivL Continuous.prod_map_equivL

theorem _root_.ContinuousOn.prod_mapL {f : X → M₁ →L[𝕜] M₂} {g : X → M₃ →L[𝕜] M₄} {s : Set X}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => (f x).prodMap (g x)) s :=
  ((prodMapL 𝕜 M₁ M₂ M₃ M₄).continuous.comp_continuousOn (hf.prod hg) : _)
#align continuous_on.prod_mapL ContinuousOn.prod_mapL

theorem _root_.ContinuousOn.prod_map_equivL {f : X → M₁ ≃L[𝕜] M₂} {g : X → M₃ ≃L[𝕜] M₄} {s : Set X}
    (hf : ContinuousOn (fun x => (f x : M₁ →L[𝕜] M₂)) s)
    (hg : ContinuousOn (fun x => (g x : M₃ →L[𝕜] M₄)) s) :
    ContinuousOn (fun x => ((f x).prod (g x) : M₁ × M₃ →L[𝕜] M₂ × M₄)) s :=
  (prodMapL 𝕜 M₁ M₂ M₃ M₄).continuous.comp_continuousOn (hf.prod hg)
#align continuous_on.prod_map_equivL ContinuousOn.prod_map_equivL

end Prod

section MultiplicationLinear

section NonUnital

variable (𝕜) (𝕜' : Type*) [NonUnitalSeminormedRing 𝕜']

variable [NormedSpace 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' 𝕜'] [SMulCommClass 𝕜 𝕜' 𝕜']

/-- Multiplication in a non-unital normed algebra as a continuous bilinear map. -/
def mul : 𝕜' →L[𝕜] 𝕜' →L[𝕜] 𝕜' :=
  (LinearMap.mul 𝕜 𝕜').mkContinuous₂ 1 fun x y => by simpa using norm_mul_le x y
#align continuous_linear_map.mul ContinuousLinearMap.mul

@[simp]
theorem mul_apply' (x y : 𝕜') : mul 𝕜 𝕜' x y = x * y :=
  rfl
#align continuous_linear_map.mul_apply' ContinuousLinearMap.mul_apply'

@[simp]
theorem op_norm_mul_apply_le (x : 𝕜') : ‖mul 𝕜 𝕜' x‖ ≤ ‖x‖ :=
  op_norm_le_bound _ (norm_nonneg x) (norm_mul_le x)
#align continuous_linear_map.op_norm_mul_apply_le ContinuousLinearMap.op_norm_mul_apply_le

theorem op_norm_mul_le : ‖mul 𝕜 𝕜'‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _
#align continuous_linear_map.op_norm_mul_le ContinuousLinearMap.op_norm_mul_le

/-- Multiplication on the left in a non-unital normed algebra `𝕜'` as a non-unital algebra
homomorphism into the algebra of *continuous* linear maps. This is the left regular representation
of `A` acting on itself.

This has more algebraic structure than `ContinuousLinearMap.mul`, but there is no longer continuity
bundled in the first coordinate.  An alternative viewpoint is that this upgrades
`NonUnitalAlgHom.lmul` from a homomorphism into linear maps to a homomorphism into *continuous*
linear maps. -/
def _root_.NonUnitalAlgHom.Lmul : 𝕜' →ₙₐ[𝕜] 𝕜' →L[𝕜] 𝕜' :=
  { mul 𝕜 𝕜' with
    map_mul' := fun _ _ ↦ ext fun _ ↦ mul_assoc _ _ _
    map_zero' := ext fun _ ↦ zero_mul _ }

variable {𝕜 𝕜'} in
@[simp]
theorem _root_.NonUnitalAlgHom.coe_Lmul : ⇑(NonUnitalAlgHom.Lmul 𝕜 𝕜') = mul 𝕜 𝕜' :=
  rfl

/-- Simultaneous left- and right-multiplication in a non-unital normed algebra, considered as a
continuous trilinear map. This is akin to its non-continuous version `LinearMap.mulLeftRight`,
but there is a minor difference: `LinearMap.mulLeftRight` is uncurried. -/
def mulLeftRight : 𝕜' →L[𝕜] 𝕜' →L[𝕜] 𝕜' →L[𝕜] 𝕜' :=
  ((compL 𝕜 𝕜' 𝕜' 𝕜').comp (mul 𝕜 𝕜').flip).flip.comp (mul 𝕜 𝕜')
#align continuous_linear_map.mul_left_right ContinuousLinearMap.mulLeftRight

@[simp]
theorem mulLeftRight_apply (x y z : 𝕜') : mulLeftRight 𝕜 𝕜' x y z = x * z * y :=
  rfl
#align continuous_linear_map.mul_left_right_apply ContinuousLinearMap.mulLeftRight_apply

theorem op_norm_mulLeftRight_apply_apply_le (x y : 𝕜') : ‖mulLeftRight 𝕜 𝕜' x y‖ ≤ ‖x‖ * ‖y‖ :=
  (op_norm_comp_le _ _).trans <|
    (mul_comm _ _).trans_le <|
      mul_le_mul (op_norm_mul_apply_le _ _ _)
        (op_norm_le_bound _ (norm_nonneg _) fun _ => (norm_mul_le _ _).trans_eq (mul_comm _ _))
        (norm_nonneg _) (norm_nonneg _)
#align continuous_linear_map.op_norm_mul_left_right_apply_apply_le ContinuousLinearMap.op_norm_mulLeftRight_apply_apply_le

theorem op_norm_mulLeftRight_apply_le (x : 𝕜') : ‖mulLeftRight 𝕜 𝕜' x‖ ≤ ‖x‖ :=
  op_norm_le_bound _ (norm_nonneg x) (op_norm_mulLeftRight_apply_apply_le 𝕜 𝕜' x)
#align continuous_linear_map.op_norm_mul_left_right_apply_le ContinuousLinearMap.op_norm_mulLeftRight_apply_le

theorem op_norm_mulLeftRight_le :
    letI : Norm (𝕜' →L[𝕜] 𝕜' →L[𝕜] 𝕜' →L[𝕜] 𝕜') := hasOpNorm (E := 𝕜') (F := 𝕜' →L[𝕜] 𝕜' →L[𝕜] 𝕜')
    ‖mulLeftRight 𝕜 𝕜'‖ ≤ 1 :=
  op_norm_le_bound _ zero_le_one fun x => (one_mul ‖x‖).symm ▸ op_norm_mulLeftRight_apply_le 𝕜 𝕜' x
#align continuous_linear_map.op_norm_mul_left_right_le ContinuousLinearMap.op_norm_mulLeftRight_le

/-- This is a mixin class for non-unital normed algebras which states that the left-regular
representation of the algebra on itself is isometric. Every unital normed algebra with `‖1‖ = 1` is
a regular normed algebra (see `NormedAlgebra.instRegularNormedAlgebra`). In addition, so is every
C⋆-algebra, non-unital included (see `CstarRing.instRegularNormedAlgebra`), but there are yet other
examples. Any algebra with an approximate identity (e.g., $$L^1$$) is also regular.

This is a useful class because it gives rise to a nice norm on the unitization; in particular it is
a C⋆-norm when the norm on `A` is a C⋆-norm. -/
class _root_.RegularNormedAlgebra : Prop :=
  /-- The left regular representation of the algebra on itself is an isometry. -/
  isometry_mul' : Isometry (mul 𝕜 𝕜')

/-- Every (unital) normed algebra such that `‖1‖ = 1` is a `RegularNormedAlgebra`. -/
instance _root_.NormedAlgebra.instRegularNormedAlgebra {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormOneClass 𝕜'] : RegularNormedAlgebra 𝕜 𝕜' where
  isometry_mul' := AddMonoidHomClass.isometry_of_norm (mul 𝕜 𝕜') <|
    fun x => le_antisymm (op_norm_mul_apply_le _ _ _) <| by
      convert ratio_le_op_norm ((mul 𝕜 𝕜') x) (1 : 𝕜')
      simp [norm_one]

variable [RegularNormedAlgebra 𝕜 𝕜']

lemma isometry_mul : Isometry (mul 𝕜 𝕜') :=
  RegularNormedAlgebra.isometry_mul'

@[simp]
lemma op_norm_mul_apply (x : 𝕜') : ‖mul 𝕜 𝕜' x‖ = ‖x‖ :=
  (AddMonoidHomClass.isometry_iff_norm (mul 𝕜 𝕜')).mp (isometry_mul 𝕜 𝕜') x
#align continuous_linear_map.op_norm_mul_apply ContinuousLinearMap.op_norm_mul_applyₓ

@[simp]
lemma op_nnnorm_mul_apply (x : 𝕜') : ‖mul 𝕜 𝕜' x‖₊ = ‖x‖₊ :=
  Subtype.ext <| op_norm_mul_apply 𝕜 𝕜' x

/-- Multiplication in a normed algebra as a linear isometry to the space of
continuous linear maps. -/
def mulₗᵢ : 𝕜' →ₗᵢ[𝕜] 𝕜' →L[𝕜] 𝕜' where
  toLinearMap := mul 𝕜 𝕜'
  norm_map' x := op_norm_mul_apply 𝕜 𝕜' x
#align continuous_linear_map.mulₗᵢ ContinuousLinearMap.mulₗᵢₓ

@[simp]
theorem coe_mulₗᵢ : ⇑(mulₗᵢ 𝕜 𝕜') = mul 𝕜 𝕜' :=
  rfl
#align continuous_linear_map.coe_mulₗᵢ ContinuousLinearMap.coe_mulₗᵢₓ

end NonUnital

section RingEquiv

variable (𝕜 E)

/-- If `M` is a normed space over `𝕜`, then the space of maps `𝕜 →L[𝕜] M` is linearly equivalent
to `M`. (See `ring_lmap_equiv_self` for a stronger statement.) -/
def ring_lmap_equiv_selfₗ : (𝕜 →L[𝕜] E) ≃ₗ[𝕜] E where
  toFun := fun f ↦ f 1
  invFun := (ContinuousLinearMap.id 𝕜 𝕜).smulRight
  map_smul' := fun a f ↦ by simp only [coe_smul', Pi.smul_apply, RingHom.id_apply]
  map_add' := fun f g ↦ by simp only [add_apply]
  left_inv := fun f ↦ by ext; simp only [smulRight_apply, coe_id', id.def, one_smul]
  right_inv := fun m ↦ by simp only [smulRight_apply, id_apply, one_smul]

/-- If `M` is a normed space over `𝕜`, then the space of maps `𝕜 →L[𝕜] M` is linearly isometrically
equivalent to `M`. -/
def ring_lmap_equiv_self : (𝕜 →L[𝕜] E) ≃ₗᵢ[𝕜] E where
  toLinearEquiv := ring_lmap_equiv_selfₗ 𝕜 E
  norm_map' := by
    refine fun f ↦ le_antisymm ?_ ?_
    · simpa only [norm_one, mul_one] using le_op_norm f 1
    · refine op_norm_le_bound' f (norm_nonneg <| f 1) (fun x _ ↦ ?_)
      rw [(by rw [smul_eq_mul, mul_one] : f x = f (x • 1)), ContinuousLinearMap.map_smul,
        norm_smul, mul_comm, (by rfl : ring_lmap_equiv_selfₗ 𝕜 E f = f 1)]

end RingEquiv

end MultiplicationLinear

section SMulLinear

variable (𝕜) (𝕜' : Type*) [NormedField 𝕜']

variable [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]

/-- Scalar multiplication as a continuous bilinear map. -/
def lsmul : 𝕜' →L[𝕜] E →L[𝕜] E :=
  ((Algebra.lsmul 𝕜 𝕜 E).toLinearMap : 𝕜' →ₗ[𝕜] E →ₗ[𝕜] E).mkContinuous₂ 1 fun c x => by
    simpa only [one_mul] using norm_smul_le c x
#align continuous_linear_map.lsmul ContinuousLinearMap.lsmul

@[simp]
theorem lsmul_apply (c : 𝕜') (x : E) : lsmul 𝕜 𝕜' c x = c • x :=
  rfl
#align continuous_linear_map.lsmul_apply ContinuousLinearMap.lsmul_apply

variable {𝕜'}

theorem norm_toSpanSingleton (x : E) : ‖toSpanSingleton 𝕜 x‖ = ‖x‖ := by
  refine' op_norm_eq_of_bounds (norm_nonneg _) (fun x => _) fun N _ h => _
  · rw [toSpanSingleton_apply, norm_smul, mul_comm]
  · specialize h 1
    rw [toSpanSingleton_apply, norm_smul, mul_comm] at h
    exact (mul_le_mul_right (by simp)).mp h
#align continuous_linear_map.norm_to_span_singleton ContinuousLinearMap.norm_toSpanSingleton

variable {𝕜}

theorem op_norm_lsmul_apply_le (x : 𝕜') : ‖(lsmul 𝕜 𝕜' x : E →L[𝕜] E)‖ ≤ ‖x‖ :=
  ContinuousLinearMap.op_norm_le_bound _ (norm_nonneg x) fun y => norm_smul_le x y
#align continuous_linear_map.op_norm_lsmul_apply_le ContinuousLinearMap.op_norm_lsmul_apply_le

/-- The norm of `lsmul` is at most 1 in any semi-normed group. -/
theorem op_norm_lsmul_le : ‖(lsmul 𝕜 𝕜' : 𝕜' →L[𝕜] E →L[𝕜] E)‖ ≤ 1 := by
  refine' ContinuousLinearMap.op_norm_le_bound _ zero_le_one fun x => _
  simp_rw [one_mul]
  exact op_norm_lsmul_apply_le _
#align continuous_linear_map.op_norm_lsmul_le ContinuousLinearMap.op_norm_lsmul_le

end SMulLinear

section RestrictScalars

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]

variable [NormedSpace 𝕜' E] [IsScalarTower 𝕜' 𝕜 E]

variable [NormedSpace 𝕜' Fₗ] [IsScalarTower 𝕜' 𝕜 Fₗ]

@[simp]
theorem norm_restrictScalars (f : E →L[𝕜] Fₗ) : ‖f.restrictScalars 𝕜'‖ = ‖f‖ :=
  le_antisymm (op_norm_le_bound _ (norm_nonneg _) fun x => f.le_op_norm x)
    (op_norm_le_bound _ (norm_nonneg _) fun x => f.le_op_norm x)
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

end ContinuousLinearMap

namespace Submodule

theorem norm_subtypeL_le (K : Submodule 𝕜 E) : ‖K.subtypeL‖ ≤ 1 :=
  K.subtypeₗᵢ.norm_toContinuousLinearMap_le
set_option linter.uppercaseLean3 false in
#align submodule.norm_subtypeL_le Submodule.norm_subtypeL_le

end Submodule

namespace ContinuousLinearEquiv

set_option linter.uppercaseLean3 false

section

variable {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] [RingHomIsometric σ₁₂]

variable (e : E ≃SL[σ₁₂] F)

protected theorem lipschitz : LipschitzWith ‖(e : E →SL[σ₁₂] F)‖₊ e :=
  (e : E →SL[σ₁₂] F).lipschitz
#align continuous_linear_equiv.lipschitz ContinuousLinearEquiv.lipschitz

theorem isBigO_comp {α : Type*} (f : α → E) (l : Filter α) : (fun x' => e (f x')) =O[l] f :=
  (e : E →SL[σ₁₂] F).isBigO_comp f l
#align continuous_linear_equiv.is_O_comp ContinuousLinearEquiv.isBigO_comp

theorem isBigO_sub (l : Filter E) (x : E) : (fun x' => e (x' - x)) =O[l] fun x' => x' - x :=
  (e : E →SL[σ₁₂] F).isBigO_sub l x
#align continuous_linear_equiv.is_O_sub ContinuousLinearEquiv.isBigO_sub

end

variable {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

variable [RingHomIsometric σ₂₁] (e : E ≃SL[σ₁₂] F)

theorem isBigO_comp_rev {α : Type*} (f : α → E) (l : Filter α) : f =O[l] fun x' => e (f x') :=
  (e.symm.isBigO_comp _ l).congr_left fun _ => e.symm_apply_apply _
#align continuous_linear_equiv.is_O_comp_rev ContinuousLinearEquiv.isBigO_comp_rev

theorem isBigO_sub_rev (l : Filter E) (x : E) : (fun x' => x' - x) =O[l] fun x' => e (x' - x) :=
  e.isBigO_comp_rev _ _
#align continuous_linear_equiv.is_O_sub_rev ContinuousLinearEquiv.isBigO_sub_rev

end ContinuousLinearEquiv

variable {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

namespace ContinuousLinearMap

variable {E' F' : Type*} [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F']

variable {𝕜₁' : Type*} {𝕜₂' : Type*} [NontriviallyNormedField 𝕜₁'] [NontriviallyNormedField 𝕜₂']
  [NormedSpace 𝕜₁' E'] [NormedSpace 𝕜₂' F'] {σ₁' : 𝕜₁' →+* 𝕜} {σ₁₃' : 𝕜₁' →+* 𝕜₃} {σ₂' : 𝕜₂' →+* 𝕜₂}
  {σ₂₃' : 𝕜₂' →+* 𝕜₃} [RingHomCompTriple σ₁' σ₁₃ σ₁₃'] [RingHomCompTriple σ₂' σ₂₃ σ₂₃']
  [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃'] [RingHomIsometric σ₂₃']

/-- Compose a bilinear map `E →SL[σ₁₃] F →SL[σ₂₃] G` with two linear maps
`E' →SL[σ₁'] E` and `F' →SL[σ₂'] F`.  -/
def bilinearComp (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (gE : E' →SL[σ₁'] E) (gF : F' →SL[σ₂'] F) :
    E' →SL[σ₁₃'] F' →SL[σ₂₃'] G :=
  ((f.comp gE).flip.comp gF).flip
#align continuous_linear_map.bilinear_comp ContinuousLinearMap.bilinearComp

@[simp]
theorem bilinearComp_apply (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (gE : E' →SL[σ₁'] E) (gF : F' →SL[σ₂'] F)
    (x : E') (y : F') : f.bilinearComp gE gF x y = f (gE x) (gF y) :=
  rfl
#align continuous_linear_map.bilinear_comp_apply ContinuousLinearMap.bilinearComp_apply

variable [RingHomIsometric σ₁₃] [RingHomIsometric σ₁'] [RingHomIsometric σ₂']

/-- Derivative of a continuous bilinear map `f : E →L[𝕜] F →L[𝕜] G` interpreted as a map `E × F → G`
at point `p : E × F` evaluated at `q : E × F`, as a continuous bilinear map. -/
def deriv₂ (f : E →L[𝕜] Fₗ →L[𝕜] Gₗ) : E × Fₗ →L[𝕜] E × Fₗ →L[𝕜] Gₗ :=
  f.bilinearComp (fst _ _ _) (snd _ _ _) + f.flip.bilinearComp (snd _ _ _) (fst _ _ _)
#align continuous_linear_map.deriv₂ ContinuousLinearMap.deriv₂

@[simp]
theorem coe_deriv₂ (f : E →L[𝕜] Fₗ →L[𝕜] Gₗ) (p : E × Fₗ) :
    ⇑(f.deriv₂ p) = fun q : E × Fₗ => f p.1 q.2 + f q.1 p.2 :=
  rfl
#align continuous_linear_map.coe_deriv₂ ContinuousLinearMap.coe_deriv₂

theorem map_add_add (f : E →L[𝕜] Fₗ →L[𝕜] Gₗ) (x x' : E) (y y' : Fₗ) :
    f (x + x') (y + y') = f x y + f.deriv₂ (x, y) (x', y') + f x' y' := by
  simp only [map_add, add_apply, coe_deriv₂, add_assoc]
  abel
#align continuous_linear_map.map_add_add ContinuousLinearMap.map_add_add

end ContinuousLinearMap

end SemiNormed

section Normed

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NormedAddCommGroup Fₗ]

open Metric ContinuousLinearMap

section

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G] [NormedSpace 𝕜 Fₗ] (c : 𝕜)
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} (f g : E →SL[σ₁₂] F) (x y z : E)

namespace LinearMap

theorem bound_of_shell [RingHomIsometric σ₁₂] (f : E →ₛₗ[σ₁₂] F) {ε C : ℝ} (ε_pos : 0 < ε) {c : 𝕜}
    (hc : 1 < ‖c‖) (hf : ∀ x, ε / ‖c‖ ≤ ‖x‖ → ‖x‖ < ε → ‖f x‖ ≤ C * ‖x‖) (x : E) :
    ‖f x‖ ≤ C * ‖x‖ := by
  by_cases hx : x = 0; · simp [hx]
  exact SemilinearMapClass.bound_of_shell_semi_normed f ε_pos hc hf (norm_ne_zero_iff.2 hx)
#align linear_map.bound_of_shell LinearMap.bound_of_shell

/-- `LinearMap.bound_of_ball_bound'` is a version of this lemma over a field satisfying `IsROrC`
that produces a concrete bound.
-/
theorem bound_of_ball_bound {r : ℝ} (r_pos : 0 < r) (c : ℝ) (f : E →ₗ[𝕜] Fₗ)
    (h : ∀ z ∈ Metric.ball (0 : E) r, ‖f z‖ ≤ c) : ∃ C, ∀ z : E, ‖f z‖ ≤ C * ‖z‖ := by
  cases' @NontriviallyNormedField.non_trivial 𝕜 _ with k hk
  use c * (‖k‖ / r)
  intro z
  refine' bound_of_shell _ r_pos hk (fun x hko hxo => _) _
  calc
    ‖f x‖ ≤ c := h _ (mem_ball_zero_iff.mpr hxo)
    _ ≤ c * (‖x‖ * ‖k‖ / r) := (le_mul_of_one_le_right ?_ ?_)
    _ = _ := by ring
  · exact le_trans (norm_nonneg _) (h 0 (by simp [r_pos]))
  · rw [div_le_iff (zero_lt_one.trans hk)] at hko
    exact (one_le_div r_pos).mpr hko
#align linear_map.bound_of_ball_bound LinearMap.bound_of_ball_bound

theorem antilipschitz_of_comap_nhds_le [h : RingHomIsometric σ₁₂] (f : E →ₛₗ[σ₁₂] F)
    (hf : (𝓝 0).comap f ≤ 𝓝 0) : ∃ K, AntilipschitzWith K f := by
  rcases ((nhds_basis_ball.comap _).le_basis_iff nhds_basis_ball).1 hf 1 one_pos with ⟨ε, ε0, hε⟩
  simp only [Set.subset_def, Set.mem_preimage, mem_ball_zero_iff] at hε
  lift ε to ℝ≥0 using ε0.le
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  refine' ⟨ε⁻¹ * ‖c‖₊, AddMonoidHomClass.antilipschitz_of_bound f fun x => _⟩
  by_cases hx : f x = 0
  · rw [← hx] at hf
    obtain rfl : x = 0 := Specializes.eq (specializes_iff_pure.2 <|
      ((Filter.tendsto_pure_pure _ _).mono_right (pure_le_nhds _)).le_comap.trans hf)
    exact norm_zero.trans_le (mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg _))
  have hc₀ : c ≠ 0 := norm_pos_iff.1 (one_pos.trans hc)
  rw [← h.1] at hc
  rcases rescale_to_shell_zpow hc ε0 hx with ⟨n, -, hlt, -, hle⟩
  simp only [← map_zpow₀, h.1, ← map_smulₛₗ] at hlt hle
  calc
    ‖x‖ = ‖c ^ n‖⁻¹ * ‖c ^ n • x‖ := by
      rwa [← norm_inv, ← norm_smul, inv_smul_smul₀ (zpow_ne_zero _ _)]
    _ ≤ ‖c ^ n‖⁻¹ * 1 := (mul_le_mul_of_nonneg_left (hε _ hlt).le (inv_nonneg.2 (norm_nonneg _)))
    _ ≤ ε⁻¹ * ‖c‖ * ‖f x‖ := by rwa [mul_one]
#align linear_map.antilipschitz_of_comap_nhds_le LinearMap.antilipschitz_of_comap_nhds_le

end LinearMap

namespace ContinuousLinearMap

section OpNorm

open Set Real

/-- An operator is zero iff its norm vanishes. -/
theorem op_norm_zero_iff [RingHomIsometric σ₁₂] : ‖f‖ = 0 ↔ f = 0 :=
  Iff.intro
    (fun hn => ContinuousLinearMap.ext fun x => norm_le_zero_iff.1
      (calc
        _ ≤ ‖f‖ * ‖x‖ := le_op_norm _ _
        _ = _ := by rw [hn, zero_mul]))
    (by
      rintro rfl
      exact op_norm_zero)
#align continuous_linear_map.op_norm_zero_iff ContinuousLinearMap.op_norm_zero_iff

/-- If a normed space is non-trivial, then the norm of the identity equals `1`. -/
@[simp]
theorem norm_id [Nontrivial E] : ‖id 𝕜 E‖ = 1 := by
  refine' norm_id_of_nontrivial_seminorm _
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  exact ⟨x, ne_of_gt (norm_pos_iff.2 hx)⟩
#align continuous_linear_map.norm_id ContinuousLinearMap.norm_id

@[simp]
lemma nnnorm_id [Nontrivial E] : ‖id 𝕜 E‖₊ = 1 := NNReal.eq norm_id

instance normOneClass [Nontrivial E] : NormOneClass (E →L[𝕜] E) :=
  ⟨norm_id⟩
#align continuous_linear_map.norm_one_class ContinuousLinearMap.normOneClass

/-- Continuous linear maps themselves form a normed space with respect to
    the operator norm. -/
instance toNormedAddCommGroup [RingHomIsometric σ₁₂] : NormedAddCommGroup (E →SL[σ₁₂] F) :=
  NormedAddCommGroup.ofSeparation fun f => (op_norm_zero_iff f).mp
#align continuous_linear_map.to_normed_add_comm_group ContinuousLinearMap.toNormedAddCommGroup

/-- Continuous linear maps form a normed ring with respect to the operator norm. -/
instance toNormedRing : NormedRing (E →L[𝕜] E) :=
  { ContinuousLinearMap.toNormedAddCommGroup, ContinuousLinearMap.toSemiNormedRing with }
#align continuous_linear_map.to_normed_ring ContinuousLinearMap.toNormedRing

variable {f}

theorem homothety_norm [RingHomIsometric σ₁₂] [Nontrivial E] (f : E →SL[σ₁₂] F) {a : ℝ}
    (hf : ∀ x, ‖f x‖ = a * ‖x‖) : ‖f‖ = a := by
  obtain ⟨x, hx⟩ : ∃ x : E, x ≠ 0 := exists_ne 0
  rw [← norm_pos_iff] at hx
  have ha : 0 ≤ a := by simpa only [hf, hx, mul_nonneg_iff_of_pos_right] using norm_nonneg (f x)
  apply le_antisymm (f.op_norm_le_bound ha fun y => le_of_eq (hf y))
  simpa only [hf, hx, mul_le_mul_right] using f.le_op_norm x
#align continuous_linear_map.homothety_norm ContinuousLinearMap.homothety_norm

variable (f)

/-- If a continuous linear map is a topology embedding, then it is expands the distances
by a positive factor.-/
theorem antilipschitz_of_embedding (f : E →L[𝕜] Fₗ) (hf : Embedding f) :
    ∃ K, AntilipschitzWith K f :=
  f.toLinearMap.antilipschitz_of_comap_nhds_le <| map_zero f ▸ (hf.nhds_eq_comap 0).ge
#align continuous_linear_map.antilipschitz_of_embedding ContinuousLinearMap.antilipschitz_of_embedding

section Completeness

open Topology

open Filter

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
    exact g.le_of_op_norm_le (hC _ hg) _
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
  suffices : ∀ n x, ‖f n x - g x‖ ≤ b n * ‖x‖
  exact tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero (fun n => norm_nonneg _) (fun n => op_norm_le_bound _ (hb₀ n) (this n)) hb_lim)
  intro n x
  -- Note that `f m x → g x`, hence `‖f n x - f m x‖ → ‖f n x - g x‖` as `m → ∞`
  have : Tendsto (fun m => ‖f n x - f m x‖) atTop (𝓝 ‖f n x - g x‖) :=
    (tendsto_const_nhds.sub <| tendsto_pi_nhds.1 hg _).norm
  -- Thus it suffices to verify `‖f n x - f m x‖ ≤ b n * ‖x‖` for `m ≥ n`.
  refine' le_of_tendsto this (eventually_atTop.2 ⟨n, fun m hm => _⟩)
  -- This inequality follows from `‖f n - f m‖ ≤ b n`.
  exact (f n - f m).le_of_op_norm_le (hfb _ _ _ le_rfl hm) _
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
  refine' mem_closedBall_iff_norm.2 (op_norm_le_bound _ hr fun x => _)
  have : IsClosed { g : E' → F | ‖g x - f₀ x‖ ≤ r * ‖x‖ } :=
    isClosed_Iic.preimage ((@continuous_apply E' (fun _ => F) _ x).sub continuous_const).norm
  refine' this.closure_subset_iff.2 (image_subset_iff.2 fun g hg => _) hf
  exact (g - f₀).le_of_op_norm_le (mem_closedBall_iff_norm.1 hg) _
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
theorem op_norm_extend_le :
    ‖f.extend e h_dense (uniformEmbedding_of_bound _ h_e).toUniformInducing‖ ≤ N * ‖f‖ := by
  -- Add `op_norm_le_of_dense`?
  refine op_norm_le_bound _ ?_ (isClosed_property h_dense (isClosed_le ?_ ?_) fun x ↦ ?_)
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
      ‖f x‖ ≤ ‖f‖ * ‖x‖ := le_op_norm _ _
      _ ≤ ‖f‖ * (N * ‖e x‖) := (mul_le_mul_of_nonneg_left (h_e x) (norm_nonneg _))
      _ ≤ N * ‖f‖ * ‖e x‖ := by rw [mul_comm ↑N ‖f‖, mul_assoc]
#align continuous_linear_map.op_norm_extend_le ContinuousLinearMap.op_norm_extend_le

end

end UniformlyExtend

end OpNorm

end ContinuousLinearMap

namespace LinearIsometry

@[simp]
theorem norm_toContinuousLinearMap [Nontrivial E] [RingHomIsometric σ₁₂] (f : E →ₛₗᵢ[σ₁₂] F) :
    ‖f.toContinuousLinearMap‖ = 1 :=
  f.toContinuousLinearMap.homothety_norm <| by simp
#align linear_isometry.norm_to_continuous_linear_map LinearIsometry.norm_toContinuousLinearMap

variable {σ₁₃ : 𝕜 →+* 𝕜₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

/-- Postcomposition of a continuous linear map with a linear isometry preserves
the operator norm. -/
theorem norm_toContinuousLinearMap_comp [RingHomIsometric σ₁₂] (f : F →ₛₗᵢ[σ₂₃] G)
    {g : E →SL[σ₁₂] F} : ‖f.toContinuousLinearMap.comp g‖ = ‖g‖ :=
  op_norm_ext (f.toContinuousLinearMap.comp g) g fun x => by
    simp only [norm_map, coe_toContinuousLinearMap, coe_comp', Function.comp_apply]
#align linear_isometry.norm_to_continuous_linear_map_comp LinearIsometry.norm_toContinuousLinearMap_comp

end LinearIsometry

end

namespace ContinuousLinearMap

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G] [NormedSpace 𝕜 Fₗ] (c : 𝕜)
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃}

variable {𝕜₂' : Type*} [NontriviallyNormedField 𝕜₂'] {F' : Type*} [NormedAddCommGroup F']
  [NormedSpace 𝕜₂' F'] {σ₂' : 𝕜₂' →+* 𝕜₂} {σ₂'' : 𝕜₂ →+* 𝕜₂'} {σ₂₃' : 𝕜₂' →+* 𝕜₃}
  [RingHomInvPair σ₂' σ₂''] [RingHomInvPair σ₂'' σ₂'] [RingHomCompTriple σ₂' σ₂₃ σ₂₃']
  [RingHomCompTriple σ₂'' σ₂₃' σ₂₃] [RingHomIsometric σ₂₃] [RingHomIsometric σ₂']
  [RingHomIsometric σ₂''] [RingHomIsometric σ₂₃']

/-- Precomposition with a linear isometry preserves the operator norm. -/
theorem op_norm_comp_linearIsometryEquiv (f : F →SL[σ₂₃] G) (g : F' ≃ₛₗᵢ[σ₂'] F) :
    ‖f.comp g.toLinearIsometry.toContinuousLinearMap‖ = ‖f‖ := by
  cases subsingleton_or_nontrivial F'
  · haveI := g.symm.toLinearEquiv.toEquiv.subsingleton
    simp
  refine' le_antisymm _ _
  · convert f.op_norm_comp_le g.toLinearIsometry.toContinuousLinearMap
    simp [g.toLinearIsometry.norm_toContinuousLinearMap]
  · convert (f.comp g.toLinearIsometry.toContinuousLinearMap).op_norm_comp_le
        g.symm.toLinearIsometry.toContinuousLinearMap
    · ext
      simp
    haveI := g.symm.surjective.nontrivial
    simp [g.symm.toLinearIsometry.norm_toContinuousLinearMap]
#align continuous_linear_map.op_norm_comp_linear_isometry_equiv ContinuousLinearMap.op_norm_comp_linearIsometryEquiv

/-- The norm of the tensor product of a scalar linear map and of an element of a normed space
is the product of the norms. -/
@[simp]
theorem norm_smulRight_apply (c : E →L[𝕜] 𝕜) (f : Fₗ) : ‖smulRight c f‖ = ‖c‖ * ‖f‖ := by
  refine' le_antisymm _ _
  · refine' op_norm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) fun x => _
    calc
      ‖c x • f‖ = ‖c x‖ * ‖f‖ := norm_smul _ _
      _ ≤ ‖c‖ * ‖x‖ * ‖f‖ := (mul_le_mul_of_nonneg_right (le_op_norm _ _) (norm_nonneg _))
      _ = ‖c‖ * ‖f‖ * ‖x‖ := by ring
  · by_cases h : f = 0
    · simp [h]
    · have : 0 < ‖f‖ := norm_pos_iff.2 h
      rw [← le_div_iff this]
      refine' op_norm_le_bound _ (div_nonneg (norm_nonneg _) (norm_nonneg f)) fun x => _
      rw [div_mul_eq_mul_div, le_div_iff this]
      calc
        ‖c x‖ * ‖f‖ = ‖c x • f‖ := (norm_smul _ _).symm
        _ = ‖smulRight c f x‖ := rfl
        _ ≤ ‖smulRight c f‖ * ‖x‖ := le_op_norm _ _
#align continuous_linear_map.norm_smul_right_apply ContinuousLinearMap.norm_smulRight_apply

/-- The non-negative norm of the tensor product of a scalar linear map and of an element of a normed
space is the product of the non-negative norms. -/
@[simp]
theorem nnnorm_smulRight_apply (c : E →L[𝕜] 𝕜) (f : Fₗ) : ‖smulRight c f‖₊ = ‖c‖₊ * ‖f‖₊ :=
  NNReal.eq <| c.norm_smulRight_apply f
#align continuous_linear_map.nnnorm_smul_right_apply ContinuousLinearMap.nnnorm_smulRight_apply

variable (𝕜 E Fₗ)

set_option linter.uppercaseLean3 false

/-- `ContinuousLinearMap.smulRight` as a continuous trilinear map:
`smulRightL (c : E →L[𝕜] 𝕜) (f : F) (x : E) = c x • f`. -/
def smulRightL : (E →L[𝕜] 𝕜) →L[𝕜] Fₗ →L[𝕜] E →L[𝕜] Fₗ :=
  LinearMap.mkContinuous₂
    { toFun := smulRightₗ
      map_add' := fun c₁ c₂ => by
        ext x
        simp only [add_smul, coe_smulRightₗ, add_apply, smulRight_apply, LinearMap.add_apply]
      map_smul' := fun m c => by
        ext x
        simp only [smul_smul, coe_smulRightₗ, Algebra.id.smul_eq_mul, coe_smul', smulRight_apply,
          LinearMap.smul_apply, RingHom.id_apply, Pi.smul_apply] }
    1 fun c x => by
      simp only [coe_smulRightₗ, one_mul, norm_smulRight_apply, LinearMap.coe_mk, AddHom.coe_mk,
        le_refl]
#align continuous_linear_map.smul_rightL ContinuousLinearMap.smulRightL

variable {𝕜 E Fₗ}

@[simp]
theorem norm_smulRightL_apply (c : E →L[𝕜] 𝕜) (f : Fₗ) : ‖smulRightL 𝕜 E Fₗ c f‖ = ‖c‖ * ‖f‖ :=
  norm_smulRight_apply c f
#align continuous_linear_map.norm_smul_rightL_apply ContinuousLinearMap.norm_smulRightL_apply

@[simp]
theorem norm_smulRightL (c : E →L[𝕜] 𝕜) [Nontrivial Fₗ] : ‖smulRightL 𝕜 E Fₗ c‖ = ‖c‖ :=
  ContinuousLinearMap.homothety_norm _ c.norm_smulRight_apply
#align continuous_linear_map.norm_smul_rightL ContinuousLinearMap.norm_smulRightL

variable (𝕜) (𝕜' : Type*)

section

variable [NonUnitalNormedRing 𝕜'] [NormedSpace 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' 𝕜']
variable [SMulCommClass 𝕜 𝕜' 𝕜'] [RegularNormedAlgebra 𝕜 𝕜'] [Nontrivial 𝕜']

@[simp]
theorem op_norm_mul : ‖mul 𝕜 𝕜'‖ = 1 :=
  (mulₗᵢ 𝕜 𝕜').norm_toContinuousLinearMap
#align continuous_linear_map.op_norm_mul ContinuousLinearMap.op_norm_mulₓ

@[simp]
theorem op_nnnorm_mul : ‖mul 𝕜 𝕜'‖₊ = 1 :=
  Subtype.ext <| op_norm_mul 𝕜 𝕜'
#align continuous_linear_map.op_nnnorm_mul ContinuousLinearMap.op_nnnorm_mulₓ

end

/-- The norm of `lsmul` equals 1 in any nontrivial normed group.

This is `ContinuousLinearMap.op_norm_lsmul_le` as an equality. -/
@[simp]
theorem op_norm_lsmul [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' E]
    [IsScalarTower 𝕜 𝕜' E] [Nontrivial E] : ‖(lsmul 𝕜 𝕜' : 𝕜' →L[𝕜] E →L[𝕜] E)‖ = 1 := by
  refine' ContinuousLinearMap.op_norm_eq_of_bounds zero_le_one (fun x => _) fun N _ h => _
  · rw [one_mul]
    apply op_norm_lsmul_apply_le
  obtain ⟨y, hy⟩ := exists_ne (0 : E)
  have := le_of_op_norm_le _ (h 1) y
  simp_rw [lsmul_apply, one_smul, norm_one, mul_one] at this
  refine' le_of_mul_le_mul_right _ (norm_pos_iff.mpr hy)
  simp_rw [one_mul, this]
#align continuous_linear_map.op_norm_lsmul ContinuousLinearMap.op_norm_lsmul

end ContinuousLinearMap

namespace Submodule

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂}

theorem norm_subtypeL (K : Submodule 𝕜 E) [Nontrivial K] : ‖K.subtypeL‖ = 1 :=
  K.subtypeₗᵢ.norm_toContinuousLinearMap
set_option linter.uppercaseLean3 false in
#align submodule.norm_subtypeL Submodule.norm_subtypeL

end Submodule

namespace ContinuousLinearEquiv

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁]
  [RingHomInvPair σ₂₁ σ₁₂]

section

variable [RingHomIsometric σ₂₁]

protected theorem antilipschitz (e : E ≃SL[σ₁₂] F) :
    AntilipschitzWith ‖(e.symm : F →SL[σ₂₁] E)‖₊ e :=
  e.symm.lipschitz.to_rightInverse e.left_inv
#align continuous_linear_equiv.antilipschitz ContinuousLinearEquiv.antilipschitz

theorem one_le_norm_mul_norm_symm [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F) :
    1 ≤ ‖(e : E →SL[σ₁₂] F)‖ * ‖(e.symm : F →SL[σ₂₁] E)‖ := by
  rw [mul_comm]
  convert (e.symm : F →SL[σ₂₁] E).op_norm_comp_le (e : E →SL[σ₁₂] F)
  rw [e.coe_symm_comp_coe, ContinuousLinearMap.norm_id]
#align continuous_linear_equiv.one_le_norm_mul_norm_symm ContinuousLinearEquiv.one_le_norm_mul_norm_symm

theorem norm_pos [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F) :
    0 < ‖(e : E →SL[σ₁₂] F)‖ :=
  pos_of_mul_pos_left (lt_of_lt_of_le zero_lt_one e.one_le_norm_mul_norm_symm) (norm_nonneg _)
#align continuous_linear_equiv.norm_pos ContinuousLinearEquiv.norm_pos

theorem norm_symm_pos [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F) :
    0 < ‖(e.symm : F →SL[σ₂₁] E)‖ :=
  pos_of_mul_pos_right (zero_lt_one.trans_le e.one_le_norm_mul_norm_symm) (norm_nonneg _)
#align continuous_linear_equiv.norm_symm_pos ContinuousLinearEquiv.norm_symm_pos

theorem nnnorm_symm_pos [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F) :
    0 < ‖(e.symm : F →SL[σ₂₁] E)‖₊ :=
  e.norm_symm_pos
#align continuous_linear_equiv.nnnorm_symm_pos ContinuousLinearEquiv.nnnorm_symm_pos

theorem subsingleton_or_norm_symm_pos [RingHomIsometric σ₁₂] (e : E ≃SL[σ₁₂] F) :
    Subsingleton E ∨ 0 < ‖(e.symm : F →SL[σ₂₁] E)‖ := by
  rcases subsingleton_or_nontrivial E with (_i | _i) <;> skip
  · left
    infer_instance
  · right
    exact e.norm_symm_pos
#align continuous_linear_equiv.subsingleton_or_norm_symm_pos ContinuousLinearEquiv.subsingleton_or_norm_symm_pos

theorem subsingleton_or_nnnorm_symm_pos [RingHomIsometric σ₁₂] (e : E ≃SL[σ₁₂] F) :
    Subsingleton E ∨ 0 < ‖(e.symm : F →SL[σ₂₁] E)‖₊ :=
  subsingleton_or_norm_symm_pos e
#align continuous_linear_equiv.subsingleton_or_nnnorm_symm_pos ContinuousLinearEquiv.subsingleton_or_nnnorm_symm_pos

variable (𝕜)

@[simp]
theorem coord_norm (x : E) (h : x ≠ 0) : ‖coord 𝕜 x h‖ = ‖x‖⁻¹ := by
  have hx : 0 < ‖x‖ := norm_pos_iff.mpr h
  haveI : Nontrivial (𝕜 ∙ x) := Submodule.nontrivial_span_singleton h
  exact ContinuousLinearMap.homothety_norm _ fun y =>
    homothety_inverse _ hx _ (toSpanNonzeroSingleton_homothety 𝕜 x h) _
#align continuous_linear_equiv.coord_norm ContinuousLinearEquiv.coord_norm

end

end ContinuousLinearEquiv

end Normed

/-- A bounded bilinear form `B` in a real normed space is *coercive*
if there is some positive constant C such that `C * ‖u‖ * ‖u‖ ≤ B u u`.
-/
def IsCoercive [NormedAddCommGroup E] [NormedSpace ℝ E] (B : E →L[ℝ] E →L[ℝ] ℝ) : Prop :=
  ∃ C, 0 < C ∧ ∀ u, C * ‖u‖ * ‖u‖ ≤ B u u
#align is_coercive IsCoercive

section Equicontinuous

variable {ι : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
  [RingHomIsometric σ₁₂] [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] (f : ι → E →SL[σ₁₂] F)

/-- Equivalent characterizations for equicontinuity of a family of continuous linear maps
between normed spaces. See also `WithSeminorms.equicontinuous_TFAE` for similar characterizations
between spaces satisfying `WithSeminorms`. -/
protected theorem NormedSpace.equicontinuous_TFAE : List.TFAE
    [ EquicontinuousAt ((↑) ∘ f) 0,
      Equicontinuous ((↑) ∘ f),
      UniformEquicontinuous ((↑) ∘ f),
      ∃ C, ∀ i x, ‖f i x‖ ≤ C * ‖x‖,
      ∃ C ≥ 0, ∀ i x, ‖f i x‖ ≤ C * ‖x‖,
      ∃ C, ∀ i, ‖f i‖ ≤ C,
      ∃ C ≥ 0, ∀ i, ‖f i‖ ≤ C,
      BddAbove (Set.range (‖f ·‖)),
      (⨆ i, (‖f i‖₊ : ENNReal)) < ⊤ ] := by
  -- `1 ↔ 2 ↔ 3` follows from `uniformEquicontinuous_of_equicontinuousAt_zero`
  tfae_have 1 → 3
  · exact uniformEquicontinuous_of_equicontinuousAt_zero f
  tfae_have 3 → 2
  · exact UniformEquicontinuous.equicontinuous
  tfae_have 2 → 1
  · exact fun H ↦ H 0
  -- `4 ↔ 5 ↔ 6 ↔ 7 ↔ 8 ↔ 9` is morally trivial, we just have to use a lot of rewriting
  -- and `congr` lemmas
  tfae_have 4 ↔ 5
  · rw [exists_ge_and_iff_exists]
    exact fun C₁ C₂ hC ↦ forall₂_imp fun i x ↦ le_trans' <| by gcongr
  tfae_have 5 ↔ 7
  · refine exists_congr (fun C ↦ and_congr_right fun hC ↦ forall_congr' fun i ↦ ?_)
    rw [ContinuousLinearMap.op_norm_le_iff hC]
  tfae_have 7 ↔ 8
  · simp_rw [bddAbove_iff_exists_ge (0 : ℝ), Set.forall_range_iff]
  tfae_have 6 ↔ 8
  · simp_rw [bddAbove_def, Set.forall_range_iff]
  tfae_have 8 ↔ 9
  · rw [ENNReal.iSup_coe_lt_top, ← NNReal.bddAbove_coe, ← Set.range_comp]
    rfl
  -- `3 ↔ 4` is the interesting part of the result. It is essentially a combination of
  -- `WithSeminorms.uniformEquicontinuous_iff_exists_continuous_seminorm` which turns
  -- equicontinuity into existence of some continuous seminorm and
  -- `Seminorm.bound_of_continuous_normedSpace` which characterize such seminorms.
  tfae_have 3 ↔ 4
  · refine ((norm_withSeminorms 𝕜₂ F).uniformEquicontinuous_iff_exists_continuous_seminorm _).trans
      ?_
    rw [forall_const]
    constructor
    · intro ⟨p, hp, hpf⟩
      rcases p.bound_of_continuous_normedSpace hp with ⟨C, -, hC⟩
      exact ⟨C, fun i x ↦ (hpf i x).trans (hC x)⟩
    · intro ⟨C, hC⟩
      refine ⟨C.toNNReal • normSeminorm 𝕜 E,
        ((norm_withSeminorms 𝕜 E).continuous_seminorm 0).const_smul C.toNNReal, fun i x ↦ ?_⟩
      refine (hC i x).trans (mul_le_mul_of_nonneg_right (C.le_coe_toNNReal) (norm_nonneg x))
  tfae_finish

end Equicontinuous
