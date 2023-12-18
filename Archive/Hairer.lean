/-
Copyright (c) 2023 Floris Van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Sébastien Gouëzel, Patrick Massot, Ruben Van de Velde, Floris Van Doorn,
Junyan Xu
-/
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.FieldTheory.Finite.Polynomial
import Mathlib.Data.MvPolynomial.Funext

/-!
# Smooth functions whose integral calculates the values of polynomials

In any space `ℝᵈ` and given any `N`, we construct a smooth function supported in the unit ball
whose integral against a multivariate polynomial `P` of total degree at most `N` is `P 0`.

This is a test of the state of the library suggested by Martin Hairer.
-/

noncomputable section

open Metric Set MeasureTheory
open MvPolynomial hiding support
open Function hiding eval

section normed
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E E' F  : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜 E F) in
/-- The set of smooth functions supported in a set `s`, as a submodule of the space of functions. -/
def SmoothSupportedOn (n : ℕ∞) (s : Set E) : Submodule 𝕜 (E → F) where
  carrier := { f : E → F | tsupport f ⊆ s ∧ ContDiff 𝕜 n f }
  add_mem' hf hg := ⟨tsupport_add.trans <| union_subset hf.1 hg.1, hf.2.add hg.2⟩
  zero_mem' :=
    ⟨(tsupport_eq_empty_iff.mpr rfl).subset.trans (empty_subset _), contDiff_const (c := 0)⟩
  smul_mem' r f hf :=
    ⟨(closure_mono <| support_smul_subset_right r f).trans hf.1, contDiff_const.smul hf.2⟩

namespace SmoothSupportedOn

variable {n : ℕ∞} {s : Set E}

instance : FunLike (SmoothSupportedOn 𝕜 E F n s) E (fun _ ↦ F) where
  coe := Subtype.val
  coe_injective' := Subtype.coe_injective

@[simp]
lemma coe_mk (f : E → F) (h) : (⟨f, h⟩ : SmoothSupportedOn 𝕜 E F n s) = f := rfl

lemma tsupport_subset (f : SmoothSupportedOn 𝕜 E F n s) : tsupport f ⊆ s := f.2.1

lemma support_subset (f : SmoothSupportedOn 𝕜 E F n s) :
    support f ⊆ s := subset_tsupport _ |>.trans (tsupport_subset f)

lemma contDiff (f : SmoothSupportedOn 𝕜 E F n s) :
    ContDiff 𝕜 n f := f.2.2

theorem continuous (f : SmoothSupportedOn 𝕜 E F n s) : Continuous f :=
  ContDiff.continuous <| SmoothSupportedOn.contDiff _

lemma hasCompactSupport [ProperSpace E] (f : SmoothSupportedOn 𝕜 E F n (closedBall 0 1)) :
    HasCompactSupport f :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 1) (support_subset f)

end SmoothSupportedOn

end normed
open SmoothSupportedOn

section missing_polynomial
open MvPolynomial Submodule

variable {R σ : Type*} [CommSemiring R] (n : ℕ)

lemma restrictTotalDegree_eq_span {n : ℕ} :
    restrictTotalDegree σ R n =
    span R ((fun c : σ →₀ ℕ ↦ monomial c (1 : R)) '' {s : σ →₀ ℕ | s.sum (fun _ e ↦ e) ≤ n}) := by
  ext P; constructor <;> intro h
  · rw [← P.support_sum_monomial_coeff]
    refine sum_mem fun c hc ↦ ?_
    rw [← mul_one (coeff c P), ← smul_eq_mul, ← smul_monomial]
    rw [mem_restrictTotalDegree] at h
    exact smul_mem _ _ (subset_span <| mem_image_of_mem _ <| (le_totalDegree hc).trans h)
  · refine span_le.mpr ?_ h
    rintro x ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, mem_restrictTotalDegree]
    cases subsingleton_or_nontrivial R
    · rw [Subsingleton.elim ((fun c ↦ monomial c 1) c) 0, totalDegree_zero]; apply zero_le
    · rw [totalDegree_monomial _ one_ne_zero]; exact hc

/- Can be obtained by combining `LinearMap.proj` and `MvPolynomial.evalₗ`. -/
/-- The evaluation of a multivariate polynomial at a point, as a linear map. -/
def evalAtₗ {R σ : Type*} [CommSemiring R] (x : σ → R) : MvPolynomial σ R →ₗ[R] R where
  toFun P := eval x P
  map_add' := by simp
  map_smul' := by simp

/- what we actually want -/
lemma analyticOn_eval {R σ : Type*} [Fintype σ] [IsROrC R] (P : MvPolynomial σ R) :
    AnalyticOn R (fun x ↦ eval (EuclideanSpace.equiv σ R x) P) univ := fun x _ ↦ by
  apply P.induction_on (fun r ↦ ?_) (fun p q hp hq ↦ ?_) fun p i hp ↦ ?_ -- refine doesn't work
  · simp_rw [eval_C]; exact analyticAt_const
  · simp_rw [eval_add]; exact hp.add hq
  · simp_rw [eval_mul, eval_X]; exact hp.mul ((ContinuousLinearMap.proj (R := R) i).analyticAt x)

lemma finite_stuff' [Finite σ] (N : ℕ) : {s : Multiset σ | Multiset.card s ≤ N}.Finite := by
  classical
  have := Fintype.ofFinite σ
  let S := N • (Finset.univ.val : Multiset σ)
  apply Finset.finite_toSet (Multiset.toFinset (Multiset.powerset S)) |>.subset
  intro s hs
  rw [Set.mem_setOf] at hs
  rw [Finset.mem_coe, Multiset.mem_toFinset, Multiset.mem_powerset, Multiset.le_iff_count]
  intro x
  simp only [S, Multiset.count_nsmul, Multiset.count_univ, mul_one]
  exact le_trans (s.count_le_card x) hs

lemma finite_stuff [Finite σ] (N : ℕ) : {s : σ →₀ ℕ | s.sum (fun _ e ↦ e) ≤ N}.Finite := by
  classical
  change {s : σ →₀ ℕ | s.sum (fun _ => id) ≤ N}.Finite
  simp only [← Finsupp.card_toMultiset]
  refine Set.Finite.of_finite_image ?_ (Multiset.toFinsupp.symm.injective.injOn _)
  convert finite_stuff' (σ := σ) N
  ext x
  rw [← AddEquiv.coe_toEquiv, Set.mem_image_equiv]
  simp

instance [Finite σ] : Module.Finite R (restrictTotalDegree σ R n) := by
  rw [Module.finite_def, fg_top, restrictTotalDegree_eq_span]
  exact Submodule.fg_span ((finite_stuff _).image _)

end missing_polynomial

open Metric Set MeasureTheory Module
open MvPolynomial hiding support
open Function hiding eval

variable {ι : Type*} [Fintype ι]
lemma MvPolynomial.continuous_eval (p : MvPolynomial ι ℝ) :
    Continuous fun x ↦ (eval x) p := by
  continuity

theorem SmoothSupportedOn.integrable_eval_mul (p : MvPolynomial ι ℝ)
    (f : SmoothSupportedOn ℝ (EuclideanSpace ℝ ι) ℝ ⊤ (closedBall 0 1)) :
    Integrable fun (x : EuclideanSpace ℝ ι) ↦ (eval x) p • f x := by
  simp only [smul_eq_mul]
  apply Continuous.integrable_of_hasCompactSupport
  · apply Continuous.mul
    · apply p.continuous_eval
    · apply ContDiff.continuous <| SmoothSupportedOn.contDiff _
  exact (hasCompactSupport f).mul_left

/-- Interpreting a multivariate polynomial as an element of the dual of smooth functions supported
in the unit ball, via integration against Lebesgue measure. -/
def L : MvPolynomial ι ℝ →ₗ[ℝ]
    Dual ℝ (SmoothSupportedOn ℝ (EuclideanSpace ℝ ι) ℝ ⊤ (closedBall 0 1)) where
  toFun p :=
    { toFun := fun f ↦ ∫ x : EuclideanSpace ℝ ι, eval x p • f x
      map_add' := fun f g ↦ by
        rw [← integral_add]
        · simp only [← smul_add]; rfl
        all_goals apply SmoothSupportedOn.integrable_eval_mul
      map_smul' := fun r f ↦ by
        rw [← integral_smul]
        dsimp only [id_eq, RingHom.id_apply]
        simp only [smul_comm r]
        rfl }
  map_add' := fun p₁ p₂ ↦ by
    ext f
    dsimp only [id_eq, eq_mpr_eq_cast, AddHom.toFun_eq_coe, AddHom.coe_mk,
      RingHom.id_apply, LinearMap.coe_mk, LinearMap.add_apply]
    rw [← integral_add]
    · simp only [← add_smul, eval_add]
    all_goals apply SmoothSupportedOn.integrable_eval_mul
  map_smul' := fun r p ↦ by
    ext f
    dsimp only [id_eq, eq_mpr_eq_cast, AddHom.toFun_eq_coe, AddHom.coe_mk,
      RingHom.id_apply, LinearMap.coe_mk, LinearMap.smul_apply]
    rw [← integral_smul]
    simp only [← evalₗ_apply, SMulHomClass.map_smul, ← smul_assoc]
    rfl

lemma inj_L (ι : Type*) [Fintype ι] : Injective (L (ι := ι)) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  suffices H : ∀ᵐ x : EuclideanSpace ℝ ι, x ∈ ball 0 1 → eval x p = 0 by
    simp_rw [MvPolynomial.funext_iff, map_zero]
    refine fun x ↦ (analyticOn_eval p).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      ?_ (z₀ := 0) trivial ?_ trivial
    · rw [← preconnectedSpace_iff_univ]; infer_instance
    · refine Filter.mem_of_superset (Metric.ball_mem_nhds 0 zero_lt_one) ?_
      rw [← ae_restrict_iff'₀ measurableSet_ball.nullMeasurableSet] at H
      apply Measure.eqOn_of_ae_eq H
      · exact (analyticOn_eval p).continuous.continuousOn
      · exact continuousOn_const
      · rw [isOpen_ball.interior_eq]; apply subset_closure
  have h2p : LocallyIntegrableOn (fun x : EuclideanSpace ℝ ι ↦ eval x p) (ball 0 1) :=
    continuous_eval p |>.locallyIntegrable |>.locallyIntegrableOn _
  apply isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero h2p
  intro g hg _h2g g_supp
  let ϕ : SmoothSupportedOn ℝ (EuclideanSpace ℝ ι) ℝ ⊤ (closedBall 0 1) :=
    ⟨g, g_supp.trans ball_subset_closedBall, hg⟩
  apply_fun (· ϕ) at hp
  simpa [mul_comm (g _), L] using hp

lemma hairer (N : ℕ) (ι : Type*) [Fintype ι] :
    ∃ (ρ : EuclideanSpace ℝ ι → ℝ), tsupport ρ ⊆ closedBall 0 1 ∧ ContDiff ℝ ⊤ ρ ∧
    ∀ (p : MvPolynomial ι ℝ), p.totalDegree ≤ N →
    ∫ x : EuclideanSpace ℝ ι, eval x p • ρ x = eval 0 p := by
  have := (inj_L ι).comp (restrictTotalDegree ι ℝ N).injective_subtype
  rw [← LinearMap.coe_comp] at this
  obtain ⟨⟨φ, supφ, difφ⟩, hφ⟩ :=
    LinearMap.flip_surjective_iff₁.2 this ((evalAtₗ 0).comp <| Submodule.subtype _)
  refine ⟨φ, supφ, difφ, fun P hP ↦ ?_⟩
  exact FunLike.congr_fun hφ ⟨P, (mem_restrictTotalDegree ι N P).mpr hP⟩
