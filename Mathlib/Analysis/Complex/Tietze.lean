/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.IsROrC.Lemmas
import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.NormedSpace.HomeomorphBall
import Mathlib.Analysis.NormedSpace.IsROrC
/-!
# `ℂ` satisfies the Tietze extension theorem

We provide this result here in order to avoid pulling unnecessary imports into either of
`Topology.TietzeExtension` or `Analysis.Complex.Basic`.
-/

universe u u₁ v w

-- this is not an instance because Lean cannot determine `𝕜`.
theorem TietzeExtension.of_tvs (𝕜 : Type v) [NontriviallyNormedField 𝕜] {E : Type w}
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [TopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    [T2Space E] [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] [TietzeExtension.{u, v} 𝕜] :
    TietzeExtension.{u, w} E :=
  Basis.ofVectorSpace 𝕜 E |>.equivFun.toContinuousLinearEquiv.toHomeomorph |> .of_homeo

instance Complex.instTietzeExtension : TietzeExtension ℂ :=
  TietzeExtension.of_tvs ℝ

instance IsROrC.instTietzeExtension {𝕜 : Type*} [IsROrC 𝕜] : TietzeExtension 𝕜 :=
  TietzeExtension.of_tvs ℝ

instance IsROrC.instTietzeExtensionTVS {𝕜 : Type v} [IsROrC 𝕜] {E : Type w}
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [TopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E] :
    TietzeExtension.{u, w} E :=
  TietzeExtension.of_tvs 𝕜

instance Set.instTietzeExtensionUnitBall {𝕜 : Type v} [IsROrC 𝕜] {E : Type w}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
    TietzeExtension.{u, w} (Metric.ball (0 : E) 1) :=
  have : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  .of_homeo Homeomorph.unitBall.symm

instance Set.instTietzeExtensionUnitClosedBall {𝕜 : Type v} [IsROrC 𝕜] {E : Type w}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
    TietzeExtension.{u, w} (Metric.closedBall (0 : E) 1) := by
  have : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have : IsScalarTower ℝ 𝕜 E := Real.isScalarTower
  -- I didn't find this retract in Mathlib.
  let g : E → E := fun x ↦ ‖x‖⁻¹ • x
  classical
  suffices this : Continuous (piecewise (Metric.closedBall 0 1) id g) by
    refine .of_retract ⟨Subtype.val, by continuity⟩ ⟨_, this.codRestrict fun x ↦ ?_⟩ ?_
    · by_cases hx : x ∈ Metric.closedBall 0 1
      · simpa [piecewise_eq_of_mem (hi := hx)] using hx
      · simp only [piecewise_eq_of_not_mem (hi := hx), IsROrC.real_smul_eq_coe_smul (K := 𝕜)]
        by_cases hx' : x = 0 <;> simp [hx']
    · ext x
      simp [piecewise_eq_of_mem (hi := x.property)]
  refine continuous_piecewise (fun x hx ↦ ?_) continuousOn_id ?_
  · replace hx : ‖x‖ = 1 := by simpa [frontier_closedBall (0 : E) one_ne_zero] using hx
    simp [hx]
  · refine continuousOn_id.norm.inv₀ ?_ |>.smul continuousOn_id
    simp only [closure_compl, interior_closedBall (0 : E) one_ne_zero, mem_compl_iff,
      Metric.mem_ball, dist_zero_right, not_lt, id_eq, ne_eq, norm_eq_zero]
    exact fun x hx ↦ norm_pos_iff.mp <| one_pos.trans_le hx

def DilationEquiv.toHomeomorph {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    (e : X ≃ᵈ Y) : X ≃ₜ Y where
  continuous_toFun := Dilation.toContinuous e
  continuous_invFun := Dilation.toContinuous e.symm
  __ := e.toEquiv

@[simp]
lemma DilationEquiv.coe_toHomeomorph {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    {e : X ≃ᵈ Y} : ⇑e.toHomeomorph = e :=
  rfl

@[simp]
lemma DilationEquiv.toHomeomorph_symm {X Y : Type*} [PseudoEMetricSpace X]
    [PseudoEMetricSpace Y] {e : X ≃ᵈ Y} : e.toHomeomorph.symm = e.symm.toHomeomorph :=
  rfl

open NNReal

@[simps]
def NormedSpace.dilationEquiv (𝕜 : Type*) {E : Type*} [IsROrC 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (y : E) {r : ℝ} (hr : 0 < r) :
    E ≃ᵈ E where
  toFun w := (‖r‖ : 𝕜) • w + y
  invFun w := (‖r‖⁻¹ : 𝕜) • (w - y)
  left_inv w := by simp [smul_smul, inv_mul_cancel (show ((|r| : ℝ) : 𝕜) ≠ 0 by simpa using hr.ne')]
  right_inv w := by simp [smul_smul, mul_inv_cancel (show ((|r| : ℝ) : 𝕜) ≠ 0 by simpa using hr.ne')]
  edist_eq' := by
    lift r to ℝ≥0 using hr.le
    simp only [ne_eq, Real.norm_eq_abs, edist_add_right]
    refine ⟨r, by exact_mod_cast hr.ne', fun w₁ w₁ ↦ ?_⟩
    simp only [NNReal.abs_eq, edist_eq_coe_nnnorm_sub, ← smul_sub, sub_sub_sub_cancel_right,
      nnnorm_smul, ENNReal.coe_mul]
    norm_cast
    ext
    simp

def Homeomorph.subtype {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {p : X → Prop}
    {q : Y → Prop} (e : X ≃ₜ Y) (he : ∀ x, p x ↔ q (e x)) :
    {x // p x} ≃ₜ {y // q y} where
  toFun := Subtype.map e (he · |>.mp)
  invFun := Subtype.map e.symm fun y hy ↦ he _ |>.mpr ((e.apply_symm_apply y).symm ▸ hy)
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  continuous_toFun := by simp only; exact e.continuous.subtype_map _
  continuous_invFun := by simp only; exact e.symm.continuous.subtype_map _

def Homeomorph.sets {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {s : Set X}
    {t : Set Y} (e : X ≃ₜ Y) (he : s = e ⁻¹' t) :
    s ≃ₜ t :=
  Homeomorph.subtype e <| Set.ext_iff.mp he

theorem Metric.instTietzeExtensionBall {𝕜 : Type v} [IsROrC 𝕜] {E : Type w}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] {r : ℝ} (hr : 0 < r) :
    TietzeExtension.{u, w} (Metric.ball (0 : E) r) :=
  have : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  .of_homeo <| show (Metric.ball (0 : E) r) ≃ₜ (Metric.ball (0 : E) 1) from
    PartialHomeomorph.unitBallBall (0 : E) r hr |>.toHomeomorphSourceTarget.symm

theorem Metric.instTietzeExtensionClosedBall (𝕜 : Type v) [IsROrC 𝕜] {E : Type w}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] (y : E) {r : ℝ} (hr : 0 < r) :
    TietzeExtension.{u, w} (Metric.closedBall y r) :=
  .of_homeo <| by
    show (Metric.closedBall y r) ≃ₜ (Metric.closedBall (0 : E) 1)
    symm
    refine NormedSpace.dilationEquiv 𝕜 y hr |>.toHomeomorph.sets ?_
    ext x
    simp only [Metric.mem_closedBall, dist_zero_right, Set.mem_preimage,
      DilationEquiv.coe_toHomeomorph, NormedSpace.dilationEquiv_apply, Real.norm_eq_abs,
      dist_add_self_left, norm_smul]
    rw [IsROrC.norm_ofReal, abs_abs, abs_of_nonneg hr.le]
    exact (mul_le_iff_le_one_right hr).symm

instance Unique.instTietzeExtension {Y : Type v} [TopologicalSpace Y] [Unique Y] :
    TietzeExtension.{u, v} Y where
  exists_restrict_eq' _ _ f := ⟨.const _ default, by ext x; exact Subsingleton.elim _ _⟩


-- why don't we have this instance?
instance {X : Type*} [PartialOrder X] (x : X) : Unique (Set.Icc x x) where
  default := ⟨x, Set.left_mem_Icc.mpr le_rfl⟩
  uniq y := Subtype.ext <| have h := Set.mem_Icc.mp y.property; le_antisymm h.2 h.1

theorem Set.instTietzeExtensionIcc {a b : ℝ} (hab : a ≤ b) :
    TietzeExtension.{u, 0} (Icc a b) := by
  by_cases hab' : a = b
  · exact .of_homeo <| .setCongr (show Icc a b = Icc b b by rw [hab'])
  · replace hab := lt_of_le_of_ne hab hab'
    have := Metric.instTietzeExtensionClosedBall ℝ ((a + b) / 2) (show 0 < (b - a) / 2 by linarith)
    exact .of_homeo <| .setCongr (Real.Icc_eq_closedBall a b)

variable {X : Type u} [TopologicalSpace X] [NormalSpace X] {s : Set X} (hs : IsClosed s)
variable (𝕜 : Type v) [IsROrC 𝕜] [TietzeExtension.{u, v} 𝕜]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

namespace BoundedContinuousFunction

/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version with a closed
embedding and bundled composition. If `e : C(X, Y)` is a closed embedding of a topological space
into a normal topological space and `f : X →ᵇ ℝ` is a bounded continuous function, then there exists
a bounded continuous function `g : Y →ᵇ ℝ` of the same norm such that `g ∘ e = f`. -/
theorem exists_norm_eq_restrict_eq (f : s →ᵇ E) :
    ∃ g : X →ᵇ E, ‖g‖ = ‖f‖ ∧ g.restrict s = f := by
  by_cases hf : ‖f‖ = 0; · exact ⟨0, by aesop⟩
  have := Metric.instTietzeExtensionClosedBall.{u, v} 𝕜 (0 : E) (by aesop : 0 < ‖f‖)
  have hf' x : f x ∈ Metric.closedBall 0 ‖f‖ := by simpa using f.norm_coe_le_norm x
  obtain ⟨g, hg_mem, hg⟩ := (f : C(s, E)).exists_forall_mem_restrict_eq hs hf'
  simp only [Metric.mem_closedBall, dist_zero_right] at hg_mem
  let g' : X →ᵇ E := .ofNormedAddCommGroup g (map_continuous g) ‖f‖ hg_mem
  refine ⟨g', ?_, by ext x; congrm($(hg) x)⟩
  apply le_antisymm ((g'.norm_le <| by positivity).mpr hg_mem)
  refine (f.norm_le <| by positivity).mpr fun x ↦ ?_
  have hx : f x = g' x := by simpa using congr($(hg) x).symm
  rw [hx]
  exact g'.norm_le (norm_nonneg g') |>.mp le_rfl x

theorem exists_forall_mem_Icc_restrict_eq (f : s →ᵇ ℝ) {a b : ℝ}  (hf : ∀ x, f x ∈ Set.Icc a b)
    (hle : a ≤ b) : ∃ g : X →ᵇ ℝ, (∀ x, g x ∈ Set.Icc a b) ∧ g.restrict s = f := by
  have := Set.instTietzeExtensionIcc hle
  obtain ⟨g, hg_mem, hg⟩ := (f : C(s, ℝ)).exists_forall_mem_restrict_eq hs hf
  let g' : X →ᵇ ℝ := by
    refine .ofNormedAddCommGroup g (map_continuous g) (max |a| |b|) fun x ↦ ?_
    simp only [Set.mem_Icc] at hg_mem
    simp only [Real.norm_eq_abs]
    exact abs_le_max_abs_abs (hg_mem x).1 (hg_mem x).2
  exact ⟨g', hg_mem, by ext x; congrm($(hg) x)⟩
