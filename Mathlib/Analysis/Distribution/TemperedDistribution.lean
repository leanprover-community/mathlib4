/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.Holder

/-!
# TemperedDistribution

## Main definitions

* `TemperedDistribution 𝕜 E F V`: The space `𝓢(E, F) →L[𝕜] V` with the weak operator topology
* `TemperedDistribution.derivCLM`: The one-dimensional distributional derivative
* `TemperedDistribution.pderivCLM`: Partial distributional derivatives
* `SchwartzMap.toTemperedDistributionCLM`: The canonical embedding of `𝓢(E, F)` into
`𝓢'(𝕜, E, F →L[𝕜] V, V)`.
* `Function.HasTemperateGrowth.toTemperedDistribution`: Every function of temperate growth is a
tempered distribution.
* `MeasureTheory.Measure.HasTemperateGrowth`: Every measure of temperate growth is a tempered
distribution.

## Main statements

* `derivCLM_toTemperedDistributionCLM_eq`: The equality of the distributional derivative and the
classical derivative.

## Notation

* `𝓢'(𝕜, E, F, V)`: The space of tempered distributions `TemperedDistribution 𝕜 E F V` localized
in `SchwartzSpace`



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

noncomputable section

open SchwartzMap ContinuousLinearMap
open MeasureTheory MeasureTheory.Measure

open scoped Nat NNReal ContDiff

variable {𝕜 𝕜' H D E F G V W R : Type*}

variable [RCLike 𝕜] [NormedAddCommGroup D] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup G] [NormedAddCommGroup H] [NormedAddCommGroup V] [NormedAddCommGroup W]

section definition

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace 𝕜 V] [NormedSpace 𝕜 F]
variable (𝕜 E F V)

abbrev TemperedDistribution := 𝓢(E, F) →WOT[𝕜] V

scoped[SchwartzMap] notation "𝓢'(" 𝕜 ", " E ", " F ", " V ")" => TemperedDistribution 𝕜 E F V

end definition

section DiracDelta

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace 𝕜 V] [NormedSpace 𝕜 F]

variable (𝕜 F) in
/-- The Dirac delta distribution -/
def delta' (x : E) : 𝓢'(𝕜, E, F, F) :=
  ContinuousLinearMap.toWOT 𝕜 𝓢(E, F) F
    ((BoundedContinuousFunction.evalCLM 𝕜 x).comp (toBoundedContinuousFunctionCLM 𝕜 E F))

@[simp]
theorem delta'_apply (x₀ : E) (f : 𝓢(E, F)) : delta' 𝕜 F x₀ f = f x₀ :=
  rfl

end DiracDelta

namespace SchwartzMap

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace 𝕜 V] [NormedSpace 𝕜 F]

section pairing

variable [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]

def pairingLM : 𝓢(E, F) →ₗ[𝕜] 𝓢(E, F →L[𝕜] V) →L[𝕜] 𝓢(E, V) where
  toFun f := bilinLeftSchwartzCLM (.id 𝕜 _) f
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
theorem pairingLM_apply_apply (f : 𝓢(E, F)) (g : 𝓢(E, F →L[𝕜] V)) (x : E) :
    pairingLM f g x = g x (f x) := by
  simp [pairingLM]

theorem pairingLM_apply (f : 𝓢(E, F)) (g : 𝓢(E, F →L[𝕜] V)) :
    pairingLM f g = fun x ↦ g x (f x) := by
  ext x
  simp

end pairing

open scoped ENNReal
open MeasureTheory

end SchwartzMap

section pairingCLM


variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace 𝕜 V] [NormedSpace 𝕜 F]
variable [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]


def pairingCLM (g : 𝓢(E, F →L[𝕜] V)) : 𝓢(E, F) →L[𝕜] 𝓢(E, V) :=
  mkCLM (fun f => pairingLM f g)
  (fun _ _ _ => by simp)
  (fun _ _ _ => by simp)
  (fun f => by
    convert ((ContinuousLinearMap.restrictScalarsL _ F _ ℝ ℝ).contDiff.fun_comp
      (g.smooth ⊤)).clm_apply (f.smooth ⊤)
    simp)
  (by
      intro (k, n)
      simp only [pairingLM_apply]
      use Finset.Iic (k, n), (Finset.card (Finset.range (n+1))) • ((2 ^ n) *
        (((Finset.Iic (0, n)).sup (schwartzSeminormFamily 𝕜 _ _)) g) * (2 ^ k)), by positivity
      intro f x
      have := ((ContinuousLinearMap.id 𝕜 (F →L[𝕜] V)).bilinearRestrictScalars
          ℝ).norm_iteratedFDeriv_le_of_bilinear_of_le_one (g.smooth ⊤) (f.smooth ⊤) x (n := n) (by
        simp only [WithTop.le_def, WithTop.coe_eq_coe, forall_eq', le_top, and_true]
        use n
        simp only [WithTop.coe_natCast]) (by simp only [norm_bilinearRestrictScalars, norm_id_le])
      simp only [bilinearRestrictScalars_apply_apply, coe_id', id_eq] at this
      grw [this]
      rw [Finset.mul_sum, smul_mul_assoc]
      apply Finset.sum_le_card_nsmul
      intro i hi
      simp only [Finset.mem_range] at hi
      have hg : ‖iteratedFDeriv ℝ i g x‖ ≤
          ((Finset.Iic (0, n)).sup (schwartzSeminormFamily 𝕜 _ _)) g := by
        grw [norm_iteratedFDeriv_le_seminorm 𝕜 g]
        rw [← schwartzSeminormFamily_apply]
        apply Seminorm.le_finset_sup_apply
        simp only [Finset.mem_Iic, Prod.mk_le_mk, le_refl, true_and]
        exact Nat.le_of_lt_succ hi
      grw [Nat.choose_le_two_pow _ _, hg]
      move_mul [((Finset.Iic (0, n)).sup (schwartzSeminormFamily 𝕜 _ _)) g]
      apply mul_le_mul_of_nonneg_right _ (apply_nonneg _ _)
      simp only [Nat.cast_pow, Nat.cast_ofNat]
      move_mul [2 ^ n]
      have hf : ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖ ≤
          ((Finset.Iic (k, n)).sup (schwartzSeminormFamily 𝕜 _ _)) f := by
        grw [le_seminorm 𝕜]
        rw [← schwartzSeminormFamily_apply]
        apply Seminorm.le_finset_sup_apply
        simp only [Finset.mem_Iic, Prod.mk_le_mk, le_refl, tsub_le_iff_right,
          le_add_iff_nonneg_right, zero_le, and_self]
      grw [hf]
      move_mul [((Finset.Iic (k, n)).sup (schwartzSeminormFamily 𝕜 _ _)) f]
      apply mul_le_mul_of_nonneg_right _ (apply_nonneg _ _)
      exact le_mul_of_one_le_right (pow_nonneg zero_le_two _) (one_le_pow₀ one_le_two))

end pairingCLM

section measure_theory

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace 𝕜 V] [NormedSpace 𝕜 F]
variable [MeasurableSpace E] {μ : Measure E} [hμ : μ.HasTemperateGrowth]
variable [BorelSpace E] [SecondCountableTopology E]

variable (𝕜 F μ) in
def MeasureTheory.Measure.toTemperedDistribution : 𝓢'(𝕜, E, F, F) :=
  (toWOT _ _ _) (integralCLM 𝕜 μ)

variable (𝕜) in
@[simp]
theorem MeasureTheory.Measure.toTemperedDistribution_apply (g : 𝓢(E, F)) :
    Measure.toTemperedDistribution 𝕜 F μ g = ∫ (x : E), g x ∂μ := by
  rfl

end measure_theory

namespace Function.HasTemperateGrowth

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace 𝕜 V] [NormedSpace 𝕜 F]
variable [MeasurableSpace E] {μ : Measure E} [hμ : μ.HasTemperateGrowth]
variable [BorelSpace E] [SecondCountableTopology E]

variable [NormedSpace ℝ V]

variable (𝕜 V) in
def toTemperedDistribution (f : E → F) : 𝓢'(𝕜, E, F →L[𝕜] V, V) :=
    (ContinuousLinearMap.toWOT _ _ _) ((integralCLM 𝕜 μ) ∘L (bilinLeftCLM (.id 𝕜 _) f))

@[simp]
theorem toTemperedDistribution_apply {f : E → F} (hf : f.HasTemperateGrowth) (g : 𝓢(E, F →L[𝕜] V)) :
    toTemperedDistribution 𝕜 V (μ := μ) f g = ∫ (x : E), (g x) (f x) ∂μ := by
  simp [toTemperedDistribution, ContinuousLinearMap.toWOT_apply, hf]

end Function.HasTemperateGrowth

section LpSpace

namespace MeasureTheory.Lp

open scoped ENNReal

variable [NormedSpace ℝ E] [NormedSpace 𝕜 V] [NormedSpace 𝕜 F]
variable [MeasurableSpace E] {μ : Measure E} [hμ : μ.HasTemperateGrowth]
variable [BorelSpace E] [SecondCountableTopology E]
variable [NormedSpace ℝ V] [CompleteSpace V]

theorem _root_.ENNReal.inv_one_sub_inv' (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] :
    p.HolderConjugate (1 - p⁻¹)⁻¹ := by
  rw [ENNReal.holderConjugate_iff]
  simp only [inv_inv]
  refine add_tsub_cancel_of_le ?_
  simpa only [ENNReal.inv_le_one] using hp.elim

/-- Create a tempered distribution from a L^p function.

This is a helper definition with unnecessary parameters. -/
def toTemperedDistribution_aux (p q : ℝ≥0∞) (hp : Fact (1 ≤ p)) (hq : Fact (1 ≤ q))
    (hpq : ENNReal.HolderConjugate p q) (f : Lp F p μ) :
    𝓢'(𝕜, E, F →L[𝕜] V, V) :=
  (ContinuousLinearMap.toWOT _ _ _)
    (((ContinuousLinearMap.id 𝕜 (F →L[𝕜] V)).flip.lpPairing μ p q f) ∘L (toLpCLM 𝕜 (F →L[𝕜] V) q μ))

variable (𝕜 V) in
/-- Create a tempered distribution from a L^p function. -/
def toTemperedDistribution {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (f : Lp F p μ) :
    𝓢'(𝕜, E, F →L[𝕜] V, V) :=
  toTemperedDistribution_aux p ((1 - p⁻¹)⁻¹) hp (by simp [fact_iff]) p.inv_one_sub_inv' f

@[simp]
theorem toTemperedDistribution_apply {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (f : Lp F p μ)
    (g : 𝓢(E, F →L[𝕜] V)) :
    (toTemperedDistribution 𝕜 V f) g = ∫ (x : E), ((g.toLp (1 - p⁻¹)⁻¹ μ) x) (f x) ∂μ := by
  unfold Lp.toTemperedDistribution Lp.toTemperedDistribution_aux
  simp [toWOT_apply, lpPairing_eq_integral]


variable (𝕜 F V μ) in
/-- The natural embedding of L^p into tempered distributions. -/
def toTemperedDistributionCLM (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] :
    Lp F p μ →L[𝕜] 𝓢'(𝕜, E, F →L[𝕜] V, V) where
  toFun := toTemperedDistribution 𝕜 V
  map_add' f g := by
    ext x
    unfold Lp.toTemperedDistribution Lp.toTemperedDistribution_aux
    simp only [map_add, add_comp, ContinuousLinearMapWOT.add_apply]
  map_smul' a f := by
    ext x
    unfold Lp.toTemperedDistribution Lp.toTemperedDistribution_aux
    simp
  cont := by
    apply ContinuousLinearMapWOT.continuous_of_dual_apply_continuous
    intro g y
    apply y.cont.comp
    set q := (1 - p⁻¹)⁻¹
    have hq : Fact (1 ≤ q) := by simp [q, fact_iff]
    have hpq : ENNReal.HolderConjugate p q := p.inv_one_sub_inv'
    exact (((ContinuousLinearMap.id 𝕜 (F →L[𝕜] V)).flip.lpPairing μ p q).flip (g.toLp q μ)).cont

@[simp]
theorem toTemperedDistributionCLM_apply {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (f : Lp F p μ) :
    toTemperedDistributionCLM 𝕜 F V μ p f = toTemperedDistribution 𝕜 V f := rfl

variable [FiniteDimensional ℝ E] [NormedSpace ℝ F] [CompleteSpace F] [IsLocallyFiniteMeasure μ]

theorem injective_toTemperedDistributionCLM {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] :
    LinearMap.ker (MeasureTheory.Lp.toTemperedDistributionCLM 𝕜 F F μ p) = ⊥ := by
  refine LinearMap.ker_eq_bot'.mpr ?_
  intro f hf
  rw [eq_zero_iff_ae_eq_zero]
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
  · exact MemLp.locallyIntegrable (μ := μ) (Lp.memLp f) hp.elim
  · intro g g_smooth g_cpt
    have hg1 : HasCompactSupport (fun (x : E) ↦ g x • (ContinuousLinearMap.id 𝕜 F)) := by
      apply g_cpt.smul_right
    have hg2 : ContDiff ℝ ∞ (fun (x : E) ↦ g x • (ContinuousLinearMap.id 𝕜 F)) := by fun_prop
    have : (fun x ↦ (((hg1.toSchwartzMap hg2).toLp (1 - p⁻¹)⁻¹ μ) x) (f x)) =ᵐ[μ]
        g • f := by
      filter_upwards [coeFn_toLp (hg1.toSchwartzMap hg2) (1 - p⁻¹)⁻¹ μ] with x hgg
      simp [hgg]
    have hf_applied : (toTemperedDistributionCLM 𝕜 F F μ p) f (hg1.toSchwartzMap hg2) = 0 := by
      rw [hf, ContinuousLinearMapWOT.zero_apply]
    simpa [integral_congr_ae this] using hf_applied

end MeasureTheory.Lp

end LpSpace

namespace SchwartzMap

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace 𝕜 V] [NormedSpace 𝕜 F]
variable [SecondCountableTopology E] [NormedSpace ℝ V]

section MeasurableSpace

variable [MeasurableSpace E] [BorelSpace E]

variable (𝕜 E F V) in
def toTemperedDistributionCLM (μ : Measure E := by volume_tac) [hμ : μ.HasTemperateGrowth] :
    𝓢(E, F) →L[𝕜] 𝓢'(𝕜, E, F →L[𝕜] V, V) where
  toFun f := (toWOT _ _ _) ((integralCLM 𝕜 μ) ∘L (pairingLM f))
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  cont := by
    apply ContinuousLinearMapWOT.continuous_of_dual_apply_continuous
    intro g y
    exact y.cont.comp ((integralCLM 𝕜 μ).cont.comp (pairingCLM g).cont)

variable (f : 𝓢(E, F)) (g : 𝓢(E, F →L[𝕜] V)) (x : E)

@[simp]
theorem toTemperedDistributionCLM_apply_apply (μ : Measure E := by volume_tac)
    [hμ : μ.HasTemperateGrowth] (f : 𝓢(E, F)) (g : 𝓢(E, F →L[𝕜] V)) :
    toTemperedDistributionCLM 𝕜 E F V μ f g = ∫ (x : E), (g x) (f x) ∂μ := by
  simp [toTemperedDistributionCLM, ContinuousLinearMap.toWOT_apply]

end MeasurableSpace

variable [MeasureSpace E] [BorelSpace E]

instance instCoeToTemperedDistribution [(volume (α := E)).HasTemperateGrowth] :
    Coe 𝓢(E, F) 𝓢'(𝕜, E, F →L[𝕜] V, V) where
  coe := toTemperedDistributionCLM 𝕜 E F V volume

end SchwartzMap

section Composition

variable [NormedSpace ℝ E] [NormedSpace 𝕜 V]
variable [MeasurableSpace E] {μ : Measure E} [hμ : μ.HasTemperateGrowth]
variable [BorelSpace E] [SecondCountableTopology E]
variable [NormedSpace ℝ V]

variable [NormedSpace 𝕜 F] [NormedSpace ℝ F] [CompleteSpace V]

variable (f : 𝓢(E, V))

@[simp]
theorem eq_embeddings (f : 𝓢(E, F)) : Lp.toTemperedDistribution 𝕜 V (f.toLp 2 μ) =
    SchwartzMap.toTemperedDistributionCLM 𝕜 E F V μ f := by
  ext g y
  congr 1
  simp only [Lp.toTemperedDistribution_apply, toTemperedDistributionCLM_apply_apply]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp 2 μ, g.coeFn_toLp (1 - 2⁻¹)⁻¹ μ] with x hf hg
  rw [hf, hg]


end Composition

section Construction

variable [NormedSpace ℝ E] [NormedSpace ℝ D]
  [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  [NormedSpace ℝ G] [NormedSpace 𝕜 G]
  [NormedSpace 𝕜 V] [NormedSpace 𝕜 W]

variable (V W) in
def mkCLM (A : (𝓢(E, F) →L[𝕜] V) →ₗ[𝕜] (𝓢(D, G) →L[𝕜] W))
  (hbound : ∀ (f : 𝓢(D, G)) (a : W →L[𝕜] 𝕜), ∃ (s : Finset (𝓢(E, F) × (V →L[𝕜] 𝕜))) (C : ℝ≥0),
  ∀ (B : 𝓢(E, F) →L[𝕜] V), ∃ (g : 𝓢(E, F)) (b : V →L[𝕜] 𝕜) (_hb : (g, b) ∈ s),
  ‖a ((A B) f)‖ ≤ C • ‖b (B g)‖) : 𝓢'(𝕜, E, F, V) →L[𝕜] 𝓢'(𝕜, D, G, W) where
  __ := (toWOT _ _ _).toLinearMap.comp (A.comp (toWOT _ _ _).symm.toLinearMap)
  cont := by
    apply Seminorm.continuous_from_bounded ContinuousLinearMapWOT.withSeminorms
      ContinuousLinearMapWOT.withSeminorms
    intro (f, a)
    rcases hbound f a with ⟨s, C, h⟩
    use s, C
    rw [← Seminorm.finset_sup_smul]
    intro B
    rcases h ((toWOT _ _ _).symm B) with ⟨g, b, hb, h'⟩
    refine le_trans ?_ (Seminorm.le_finset_sup_apply hb)
    unfold ContinuousLinearMapWOT.seminormFamily
    simpa using h'

variable (V) in
def mkCompCLM (A : 𝓢(D, G) →L[𝕜] 𝓢(E, F)) : 𝓢'(𝕜, E, F, V) →L[𝕜] 𝓢'(𝕜, D, G, V) :=
    mkCLM V V
      {toFun f := f ∘L A, map_add' f g := by simp, map_smul' := by simp}
      (by
        intro f a
        use {(A f, a)}, 1
        simp)

@[simp]
theorem mkCompCLM_apply_apply (A : 𝓢(D, G) →L[𝕜] 𝓢(E, F)) (f : 𝓢'(𝕜, E, F, V)) (g : 𝓢(D, G)) :
    (mkCompCLM V A) f g = f (A g) := rfl

theorem mkCompCLM_comp (A B : 𝓢(E, F) →L[𝕜] 𝓢(E, F)) :
    (mkCompCLM V A) ∘L (mkCompCLM V B) = mkCompCLM V (B ∘L A) := by
  ext f g y
  simp only [coe_comp', Function.comp_apply, mkCompCLM_apply_apply]

theorem mkCompCLM_id : (mkCompCLM V (.id 𝕜 𝓢(E, F))) = .id _ _ := by
  ext f g y
  simp only [mkCompCLM_apply_apply, coe_id', id_eq]

end Construction

section Multiplication

variable [NormedSpace ℝ D]
  [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  [NormedSpace ℝ G] [NormedSpace 𝕜 G]
  [NormedSpace 𝕜 V]

variable (V) in
/-- The map `f ↦ (x ↦ B (f x) (g x))` as a continuous `𝕜`-linear map on Schwartz space,
where `B` is a continuous `𝕜`-linear map and `g` is a function of temperate growth. -/
def bilinLeftCLM (B : E →L[𝕜] F →L[𝕜] G) (g : D → F) :
    𝓢'(𝕜, D, G, V) →L[𝕜] 𝓢'(𝕜, D, E, V) := mkCompCLM V (SchwartzMap.bilinLeftCLM B g)

variable [NonUnitalNormedRing R] [NormedSpace 𝕜 R] [NormedSpace ℝ R] [IsScalarTower 𝕜 R R]
  [SMulCommClass 𝕜 R R]

def mulLeftCLM (g : D → R) : 𝓢'(𝕜, D, R, V) →L[𝕜] 𝓢'(𝕜, D, R, V) :=
    bilinLeftCLM V (ContinuousLinearMap.mul 𝕜 R) g

variable (E V) in
def smulLeftCLM (g : D → 𝕜) : 𝓢'(𝕜, D, E, V) →L[𝕜] 𝓢'(𝕜, D, E, V) :=
    bilinLeftCLM V (ContinuousLinearMap.lsmul 𝕜 𝕜).flip g

@[simp]
theorem smulLeftCLM_apply_apply (g : D → 𝕜) (f : 𝓢'(𝕜, D, E, V)) (f' : 𝓢(D, E)) :
    smulLeftCLM E V g f f' = f (SchwartzMap.smulLeftCLM 𝕜 _ g f') := by
  rfl

theorem mul_smulLeftCLM {g₁ g₂ : D → 𝕜} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) :
    smulLeftCLM E V g₂ ∘L smulLeftCLM E V g₁ = smulLeftCLM E V (g₁ * g₂) := by
  ext f f' y
  congr 1
  have := DFunLike.congr_fun (smulLeftCLM_mul hg₁ hg₂ (𝕜 := 𝕜) (E := E)) f'
  simp only [coe_comp', Function.comp_apply] at this
  simp [this]

variable [MeasurableSpace D] [BorelSpace D] [SecondCountableTopology D] {μ : Measure D}
  [μ.HasTemperateGrowth] [NormedSpace ℝ V]

theorem smulLeftCLM_toTemperedDistributionCLM_eq {g : D → 𝕜} (hg : g.HasTemperateGrowth)
    (f : 𝓢(D, E)) : smulLeftCLM (E →L[𝕜] V) V g (toTemperedDistributionCLM 𝕜 D E V μ f) =
    toTemperedDistributionCLM 𝕜 D E V μ (SchwartzMap.smulLeftCLM 𝕜 E g f) := by
  ext f' y
  simp [hg]

end Multiplication


section deriv

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [NormedSpace 𝕜 V]

variable (V) in
/-- The 1-dimensional derivative on Schwartz space as a continuous `𝕜`-linear map. -/
def derivCLM : 𝓢'(𝕜, ℝ, F, V) →L[𝕜] 𝓢'(𝕜, ℝ, F, V) := mkCompCLM V (-SchwartzMap.derivCLM 𝕜)

@[simp]
theorem derivCLM_apply_apply (f : 𝓢'(𝕜, ℝ, F, V)) (g : 𝓢(ℝ, F)) :
    derivCLM V f g = f (-derivCLM 𝕜 g) := rfl

open scoped ENNReal

variable [NormedSpace ℝ V]

/-- The distributional derivative and the classical derivative coincide on `𝓢(ℝ, F)`. -/
theorem derivCLM_toTemperedDistributionCLM_eq (f : 𝓢(ℝ, F)) :
    derivCLM V (toTemperedDistributionCLM 𝕜 ℝ F V volume f) =
    toTemperedDistributionCLM 𝕜 ℝ F V volume f.deriv := by
  ext g y
  simp
  simp [integral_clm_comp_deriv_right_eq_neg_left, integral_neg]

end deriv

section pderiv

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [NormedSpace 𝕜 V]

variable (V) in
def TemperedDistribution.pderivCLM (m : E) : 𝓢'(𝕜, E, F, V) →L[𝕜] 𝓢'(𝕜, E, F, V) :=
  mkCompCLM V (-SchwartzMap.pderivCLM 𝕜 m)

lemma pderivCLM_apply (m : E) (f : 𝓢'(𝕜, E, F, V)) (g : 𝓢(E, F)) :
    TemperedDistribution.pderivCLM V m f g = f (-SchwartzMap.pderivCLM 𝕜 m g) := by rfl

end pderiv

section fourier

namespace TemperedDistribution

open FourierTransform

variable
  [NormedSpace ℂ E]
  [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E]
  [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]
  [NormedSpace 𝕜 V]

variable (𝕜 H E V) in
def fourierTransformCLM : 𝓢'(𝕜, H, E, V) →L[𝕜] 𝓢'(𝕜, H, E, V) :=
  mkCompCLM V (SchwartzMap.fourierTransformCLM 𝕜)

instance instFourierTransform : FourierTransform 𝓢'(𝕜, H, E, V) 𝓢'(𝕜, H, E, V) where
  fourierTransform := fourierTransformCLM 𝕜 H E V

@[simp]
theorem fourierTransformCLM_apply (f : 𝓢'(𝕜, H, E, V)) :
    fourierTransformCLM 𝕜 H E V f = 𝓕 f := rfl

@[simp]
theorem fourierTransform_apply (f : 𝓢'(𝕜, H, E, V)) (g : 𝓢(H, E)) : 𝓕 f g = f (𝓕 g) := rfl

section FourierTransformInv

variable [CompleteSpace E]

variable (𝕜 H E V) in
def fourierTransformInvCLM : 𝓢'(𝕜, H, E, V) →L[𝕜] 𝓢'(𝕜, H, E, V) :=
  mkCompCLM V (SchwartzMap.fourierTransformCLE 𝕜).symm.toContinuousLinearMap

instance instFourierTransformInv : FourierTransformInv 𝓢'(𝕜, H, E, V) 𝓢'(𝕜, H, E, V) where
  fourierTransformInv := fourierTransformInvCLM 𝕜 H E V

@[simp]
theorem fourierTransformInvCLM_apply (f : 𝓢'(𝕜, H, E, V)) :
    fourierTransformInvCLM 𝕜 H E V f = 𝓕⁻ f := rfl

@[simp]
theorem fourierTransformInv_apply (f : 𝓢'(𝕜, H, E, V)) (g : 𝓢(H, E)) : 𝓕⁻ f g = f (𝓕⁻ g) := rfl

noncomputable
instance instFourierPair : FourierPair 𝓢'(𝕜, H, E, V) 𝓢'(𝕜, H, E, V) where
  inv_fourier f := by ext; simp

noncomputable
instance instFourierPairInv : FourierPairInv 𝓢'(𝕜, H, E, V) 𝓢'(𝕜, H, E, V) where
  fourier_inv f := by ext; simp

end FourierTransformInv

variable (f : 𝓢(H, E))

variable [NormedSpace ℂ V]
variable [CompleteSpace E] [CompleteSpace V]

/-- The distributional Fourier transform and the classical Fourier transform coincide on
`𝓢(ℝ, F)`. -/
theorem fourierTransformCLM_toTemperedDistributionCLM_eq (f : 𝓢(H, E)) :
    𝓕 (f : 𝓢'(ℂ, H, E →L[ℂ] V, V)) = 𝓕 f := by
  ext g
  congr 1
  simp only [fourierTransform_apply, toTemperedDistributionCLM_apply_apply,
    SchwartzMap.fourierTransform_apply]
  exact integral_bilin_fourierIntegral_eq_flip g f (.id ℂ _)

theorem fourierTransformInv_toTemperedDistributionCLM_eq (f : 𝓢(H, E)) :
    𝓕⁻ (f : 𝓢'(ℂ, H, E →L[ℂ] V, V)) = 𝓕⁻ f := by
  have := fourierTransformCLM_toTemperedDistributionCLM_eq (V := V) (𝓕⁻ f)
  apply_fun 𝓕⁻ at this
  simp only [FourierPair.inv_fourier, FourierPairInv.fourier_inv] at this
  rw [this]

example : 𝓕 (delta' 𝕜 E (0 : H)) = volume.toTemperedDistribution 𝕜 E := by
  ext f x
  simp [SchwartzMap.fourierTransform_apply, Real.fourierIntegral_eq]

end TemperedDistribution

end fourier
