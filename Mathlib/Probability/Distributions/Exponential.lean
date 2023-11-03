import Mathlib.Analysis.SpecialFunctions.Gaussian
import Mathlib.Probability.Notation
import Mathlib.Probability.Cdf

/-! # Exponential distributions over ℝ

Define the Exponential Measure over the Reals

## Main definitions
* `exponentialPdfReal`: the function `rate x ↦ rate * (Real.exp (-(↑rate * ↑x))` for `0 ≤ x` or `0` else,
  which is the probability density function of a exponential distribution with rate `rate` (when `ratePos : 0 < rate`).
* `exponentialPdf`: `ℝ≥0∞`-valued pdf, `exponentialPdf rate ratePos = ENNReal.ofReal (exponentialPdfReal rate ratePos)`.
* `expMeasure`: an exponential measure on `ℝ`, parametrized by its rate `rate`.
* `exponentialCdfReal` : the Cdf given by the Definition of CDF in `ProbabilityTheory.Cdf` on

## Main results
* `ExpCDF_eq`: Proof that the `exponentialCdfReal` given by the Definition equals the known
  function given as `rate x ↦ 1 - (Real.exp (-(↑rate * ↑x))` for `0 ≤ x` or `0` else.
-/

open scoped ENNReal NNReal Real

open MeasureTheory

@[simp]
lemma comp_of_ge : {x : ℝ | x ≥ 0}ᶜ =  {x | x < 0} := by
  ext x;
  constructor <;>
  simp only [ge_iff_le, Set.mem_compl_iff, Set.mem_setOf_eq, not_le, imp_self]

  /-- A Lebesgue Integral from -∞ to y can be expressed as the sum of one from -∞ to 0 and 0 to x-/
lemma lintegral_split_bounded {y z : ℝ}(f: ℝ → ENNReal) (ygez: z ≤ y) :
    ∫⁻ (x : ℝ) in Set.Iic y, f x  =  (∫⁻ (x : ℝ) in Set.Iio z, f x) +  ∫⁻ (x : ℝ) in Set.Icc z y, f x := by
  have union : Set.Iic y = Set.Iio z ∪ Set.Icc z y := by
    ext x; constructor
    . simp only [Set.mem_Iic, ge_iff_le, not_le, gt_iff_lt, Set.mem_union, Set.mem_Iio, Set.mem_Icc]
      intro hxy; by_cases x < z; left; exact h; right; constructor <;> linarith
    simp only [ge_iff_le, not_le, gt_iff_lt, Set.mem_union, Set.mem_Iio, Set.mem_Icc, Set.mem_Iic];
    intro hxy; rcases hxy with h | h;
    . linarith
    . linarith
  rw[union]; apply lintegral_union; exact measurableSet_Icc;
  rw [Set.disjoint_iff]; rintro x ⟨h1, h2⟩;
  simp only [Set.mem_Iio] at h1 ; simp only [gt_iff_lt, not_lt, ge_iff_le, Set.mem_Icc] at h2
  linarith

lemma lintegral_split (f: ℝ → ENNReal) (c : ℝ) :  ∫⁻ (x : ℝ), f x  =
    (∫⁻ (x : ℝ) in {x | x ≥ c}, f x) +  ∫⁻ (x : ℝ) in {x | x < c}, f x := by
  have union : Set.univ = {x: ℝ | x ≥ c} ∪ {x : ℝ | x < c} := by
    ext x; constructor;
    . intro _; by_cases x ≥ c;
      . left; exact h;
      . push_neg at h; right; exact h
    . intro hx; rcases hx  <;> trivial
  have : IsOpen {x : ℝ | x < c} := by exact isOpen_gt' c
  calc
  ∫⁻ (x : ℝ), f x = ∫⁻ (x : ℝ) in Set.univ, f x ∂ volume := by exact (set_lintegral_univ fun x => f x).symm
  _ = ∫⁻ (x : ℝ) in {x | x ≥ c} ∪ {x | x < c} , f x ∂ volume := by rw [<-union]
  _ = _ := by
    apply lintegral_union;
    . refine  IsOpen.measurableSet this
    . rw [@Set.disjoint_iff]; rintro x ⟨hxge, hxlt⟩; dsimp only [Set.mem_setOf_eq] at *; linarith

namespace ProbabilityTheory

section ExponentialPdf

/-- Define the PDF of the exponential distribution depending on its rate-/
noncomputable
def exponentialPdfReal (rate : ℝ) (ratePos : 0 < rate) (x : ℝ): ℝ :=
ite (0 ≤ x) (rate*(Real.exp (-(↑rate*↑x)))) 0

/- The PDF on the extended real Numbers-/
noncomputable
def exponentialPdf (rate : ℝ) (ratePos : rate > 0) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (exponentialPdfReal rate ratePos x)

lemma antiDeriv_expDeriv_pos' {rate : ℝ} (ratePos : 0 < rate)  : ∀ x ∈ (Set.Ici 0),
    HasDerivAt (fun a => -1/(↑rate) * (Real.exp (-(↑rate * a)))) (Real.exp (-(↑rate * x))) x := by
  intro x _; convert (((hasDerivAt_id x).const_mul (-↑rate)).exp.const_mul (-1/(↑ rate))) using 1;
  . simp only [id_eq, neg_mul];
  . simp only [id_eq, neg_mul, mul_one, mul_neg]
    rw[mul_comm (rexp _),<-neg_mul (-1/rate),<- neg_div, <-mul_assoc]; simp only [neg_neg,
      one_div, ne_eq]; rw[inv_mul_cancel ?_]; ring; exact ne_of_gt ratePos

/-- the Lebesgue-Integral of the exponential PDF over nonpositive Reals equals 0-/
lemma lintegral_nonpos {x rate : ℝ} (ratePos: 0 < rate) (xNonpos: x ≤ 0) :
    ∫⁻ (y : ℝ) in Set.Iio x, (exponentialPdf rate ratePos y) = ENNReal.ofReal 0 := by
  unfold exponentialPdf exponentialPdfReal;
  rw [set_lintegral_congr_fun (g:=(fun _ => 0)) measurableSet_Iio];
  . rw [@lintegral_zero]; exact ENNReal.ofReal_zero.symm
  . refine ae_of_all _ ?_; intro a ha; simp only [Set.mem_Iio] at ha;
    simp only [ge_iff_le, ENNReal.ofReal_eq_zero]
    rw [if_neg]; linarith


/-- The exponential pdf is measurable. -/
lemma measurable_exponentialPdfReal (rate : ℝ) (ratePos : rate > 0) :
    Measurable (exponentialPdfReal rate ratePos) := by
  unfold exponentialPdfReal;
  refine Measurable.ite ?hp ((measurable_id'.const_mul rate).neg.exp.const_mul rate) ?hg;
  . refine MeasurableSet.of_compl ?hp.h;
    apply  IsOpen.measurableSet; rw [comp_of_ge]; exact isOpen_gt' 0 ;
  . exact measurable_const


/-- The exponential Pdf is strongly measurable. Needed to transfer lintegral to integral -/
lemma stronglyMeasurable_exponentialPdfReal (rate : ℝ) (ratePos : rate > 0) :
    StronglyMeasurable (exponentialPdfReal rate ratePos) :=
  (measurable_exponentialPdfReal rate ratePos).stronglyMeasurable

/-- the exponential Pdf is positive for all positive reals-/
lemma exponentialPdfReal_pos (xPos : 0 < x) : exponentialPdfReal rate ratePos x > 0 := by
  unfold exponentialPdfReal
  conv =>
    lhs
    rw[if_pos (le_of_lt xPos)]
  exact mul_pos ratePos (Real.exp_pos _)

/-- The exponential Pdf is nonnegative-/
lemma exponentialPdfReal_nonneg :∀ x : ℝ, exponentialPdfReal rate ratePos x ≥ 0 := by
  unfold exponentialPdfReal
  intro x;
  by_cases x ≥  0
  . conv =>
      lhs
      rw[if_pos h]
    exact mul_nonneg (le_of_lt ratePos) (le_of_lt (Real.exp_pos _))
  . conv  =>
      lhs
      rw[if_neg h]

/-- A negative exponential function is integrable on Intervals in R≥0 -/
lemma exp_neg_integrableOn_Ioc {b x : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x => rexp (-(b * x))) (Set.Ioc 0 x) := by
  simp only [neg_mul_eq_neg_mul]
  apply IntegrableOn.mono_set (t:=Set.Ioi 0) (exp_neg_integrableOn_Ioi _ hb) Set.Ioc_subset_Ioi_self

lemma if_eval_pos : ∀ᵐ  x : ℝ ∂ volume , (x ∈ {x|x < 0} →
    ENNReal.ofReal (if ((x : ℝ) ≥  0) then ( (rate * rexp (-(↑rate * x)))) else 0 ) = 0 ):= by
  apply ae_of_all
  intro x hx; split_ifs with h; simp only [ge_iff_le] at h ;
  . contrapose h; push_neg; exact hx
  . exact ENNReal.ofReal_zero

lemma if_eval_neg :  ∀ᵐ  x : ℝ ∂ volume , (x ∈ {x|x ≥ 0} →
    ENNReal.ofReal (ite ((x : ℝ) ≥  0) (rate * rexp (-(↑rate * x))) 0 ) =
    ENNReal.ofReal (rate * rexp (-(↑rate * x)))):= by
  apply ae_of_all
  intro x hx; split_ifs with h; simp only [ge_iff_le] at h ;
  . rfl
  . contrapose h; simp only [ge_iff_le, not_le, not_lt]; exact hx

lemma antiDerivTendsZero {rate : ℝ} (ratePos : 0 < rate) :
    Filter.Tendsto (fun x => -1/(rate) * (Real.exp (-(rate * x)))) Filter.atTop (nhds 0) := by
  rw [@Metric.tendsto_atTop]; intro ε εpos;
  by_cases ε * rate < 1
  . use (2*(-(rate)⁻¹*(Real.log (ε * rate)))); intro n hn
    simp only [dist_zero_right, norm_mul, norm_div, norm_neg, norm_one, Real.norm_eq_abs, abs_eq,
    Real.abs_exp, one_div, ne_eq, NNReal.coe_eq_zero];
    apply lt_of_mul_lt_mul_left _ (le_of_lt ratePos);
    rw[<-mul_assoc, abs_eq_self.2 (le_of_lt ratePos) , mul_inv_cancel (by linarith), one_mul,
      <-Real.lt_log_iff_exp_lt (mul_pos ratePos εpos), neg_lt];
    have invPos: (0 : ℝ) < (↑rate)⁻¹  := by apply inv_pos.2 ratePos
    apply lt_of_mul_lt_mul_left (b:=-Real.log (↑rate * ε)) _ (le_of_lt invPos);
    simp only [NNReal.val_eq_coe, NNReal.coe_inv, mul_neg, NNReal.coe_eq_zero]
    rw[<-mul_assoc, inv_mul_cancel (by linarith), one_mul]
    apply lt_of_le_of_lt' hn; rw[mul_comm ε, neg_mul];
    nth_rw 1 [<-one_mul (-((↑rate)⁻¹ * Real.log (↑rate * ε)))]
    apply mul_lt_mul_of_pos_right; norm_num; simp only [Left.neg_pos_iff];
    apply mul_neg_of_pos_of_neg invPos;
    apply Real.log_neg; exact mul_pos ratePos εpos; linarith
  . push_neg at h
    use 1; intro n hn; simp only [dist_zero_right, norm_mul, norm_div, norm_neg, norm_one,
      Real.norm_eq_abs, one_div, Real.abs_exp, abs_eq_self.2 (le_of_lt ratePos)];
    apply lt_of_mul_lt_mul_left _ (le_of_lt ratePos);
    rw[<-mul_assoc, mul_inv_cancel, one_mul, mul_comm rate ε];
    apply lt_of_le_of_lt' h; refine Real.exp_lt_one_iff.mpr ?_; refine neg_lt_zero.mpr ?_;
    exact lt_mul_of_lt_of_one_le_of_nonneg ratePos hn (le_of_lt ratePos)
    linarith

open Measure

lemma lintegral_exponentialPdfReal_eq_one (rate : ℝ) (ratePos : 0 < rate) :
    ∫⁻ (x : ℝ), exponentialPdf rate ratePos x = 1 := by
  rw [lintegral_split (exponentialPdf rate ratePos) 0, ←ENNReal.toReal_eq_one_iff];
  have leftSide: ∫⁻ (x : ℝ) in {x | x < 0}, exponentialPdf rate ratePos x = 0 := by
    unfold exponentialPdf exponentialPdfReal;
    rw [set_lintegral_congr_fun ( IsOpen.measurableSet (isOpen_gt' 0)) if_eval_pos];
    exact lintegral_zero
  have rightSide: ∫⁻ (x : ℝ) in {x | x ≥ 0}, exponentialPdf rate ratePos x
    = ∫⁻ (x : ℝ) in {x | x ≥ 0}, ENNReal.ofReal (rate * rexp (-(rate * x))) := by
      unfold exponentialPdf exponentialPdfReal; apply set_lintegral_congr_fun _ _
      . refine MeasurableSet.of_compl ?h; rw [comp_of_ge];
        refine IsOpen.measurableSet ?h.h; exact isOpen_gt' 0;
      . exact if_eval_neg
  rw [leftSide]; simp only [ge_iff_le, add_zero];
  rw [rightSide, ENNReal.toReal_eq_one_iff, ←ENNReal.toReal_eq_one_iff]
  have hf : 0 ≤ᵐ[(restrictₗ {x:ℝ | x ≥ 0}) ℙ] (fun x => rate * (rexp (-(rate * x)))) := by
    apply ae_of_all _ ?a;
    simp only [Pi.zero_apply, gt_iff_lt, NNReal.coe_pos]; intro a; apply le_of_lt;
    rw[<-zero_mul 0]; apply mul_lt_mul'' ratePos (Real.exp_pos (-(rate * a))); trivial; trivial
  rw [← @restrictₗ_apply, ← integral_eq_lintegral_of_nonneg_ae hf ?_]
  . simp only [ge_iff_le, restrictₗ_apply]; rw [@integral_mul_left, Set.Ici_def];
    rw [@integral_Ici_eq_integral_Ioi]
    have IntegrOn : IntegrableOn (fun x => rexp (-(rate * x))) (Set.Ioi 0) := by
      simp only [<-neg_mul]; apply exp_neg_integrableOn_Ioi 0 ratePos
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' (antiDeriv_expDeriv_pos' ratePos) IntegrOn (antiDerivTendsZero ratePos)]
    simp only [mul_zero, neg_zero, Real.exp_zero, mul_one, _root_.zero_sub]; rw [neg_div];
    simp only [one_div,neg_neg, ne_eq, NNReal.coe_eq_zero]; rw[mul_inv_cancel]; linarith
  . apply ((measurable_id'.const_mul rate).neg.exp.const_mul rate).stronglyMeasurable.aestronglyMeasurable

/-- The Pdf of the exponential Distribution integrates to 1-/
@[simp]
lemma lintegral_exponentialPdf_eq_one (rate : ℝ) (ratePos : (0 : ℝ) < rate) :
    ∫⁻ x, exponentialPdf rate ratePos x = 1 :=
  lintegral_exponentialPdfReal_eq_one rate ratePos

end ExponentialPdf

open MeasureTheory

/- Measure defined by the exponential Distribution -/

noncomputable
def expMeasure (rate : ℝ) (ratePos : rate > 0) : Measure ℝ :=
  volume.withDensity (exponentialPdf rate ratePos)

instance instIsProbabilityMeasureExponential (rate : ℝ) (ratePos: 0 < rate) :
    IsProbabilityMeasure (expMeasure rate ratePos) where
  measure_univ := by unfold expMeasure; simp only [MeasurableSet.univ, withDensity_apply,
    Measure.restrict_univ, lintegral_exponentialPdf_eq_one]

/-- CDF of the exponential Distribution -/
noncomputable
def exponentialCdfReal (rate : ℝ) (ratePos : 0 < rate) : StieltjesFunction :=
    ProbabilityTheory.cdf (expMeasure rate ratePos)

lemma ExpCDF_eq_integral (rate : ℝ) (ratePos: 0 < rate) :
    ((exponentialCdfReal rate ratePos)) = fun x => ∫ x in (Set.Iic x), exponentialPdfReal rate ratePos x := by
  ext x;
  unfold exponentialCdfReal; rw [ProbabilityTheory.cdf_eq_toReal];
  unfold expMeasure; simp only [measurableSet_Iic, withDensity_apply];
  rw [integral_eq_lintegral_of_nonneg_ae]; exact rfl;
  . apply ae_of_all _ ?a; simp only [Pi.zero_apply]; intro a; exact exponentialPdfReal_nonneg a
  . refine AEStronglyMeasurable.restrict ?hfm.hfm;
    refine Measurable.aestronglyMeasurable ?hfm.hfm.hf;
    exact measurable_exponentialPdfReal rate ratePos

lemma ExpCDF_eq_lintegral (rate : ℝ) (ratePos: 0 < rate) : ((exponentialCdfReal rate ratePos)) =
    fun x => ENNReal.toReal (∫⁻ x in (Set.Iic x), (exponentialPdf rate ratePos x)) := by
  ext x;
  unfold exponentialPdf exponentialCdfReal; rw [ProbabilityTheory.cdf_eq_toReal];
  unfold expMeasure; simp only [measurableSet_Iic, withDensity_apply];
  exact rfl

open Topology

lemma antiDeriv_expDeriv_pos {rate : ℝ} : ∀ x ∈ (Set.Ici 0),
    HasDerivAt (fun a => -1* (Real.exp (-(↑rate * a)))) (rate * Real.exp (-(↑rate * x))) x := by
  intro x _; convert (((hasDerivAt_id x).const_mul (-↑rate)).exp.const_mul (-1)) using 1;
  . simp only [id_eq, neg_mul];
  simp only [id_eq, neg_mul, mul_one, mul_neg, one_mul, neg_neg, mul_comm]


lemma lint_eq_antiDeriv (rate : ℝ) (ratePos: 0 < rate) : ∀ x:ℝ,
    (∫⁻ y in (Set.Iic x),  (exponentialPdf rate ratePos y) =
    ENNReal.ofReal ( ite (0 ≤ x) (1 - Real.exp (-(rate * x))) 0)) := by
  intro x'; split_ifs with h
  case neg; unfold exponentialPdf exponentialPdfReal;
  rw [set_lintegral_congr_fun (g:=(fun _ => 0)), @lintegral_zero]; exact ENNReal.ofReal_zero.symm
  exact measurableSet_Iic
  refine ae_of_all ℙ ?_; intro a ha; simp only [Set.mem_Iic] at ha;
  simp only [ge_iff_le, ENNReal.ofReal_eq_zero]
  rw [if_neg]; linarith
  rw [lintegral_split_bounded _ h, lintegral_nonpos _ (le_refl 0), ENNReal.ofReal_zero, zero_add];
  unfold exponentialPdf exponentialPdfReal;
  rw[set_lintegral_congr_fun (g:=(fun x => ENNReal.ofReal (rate * rexp (-(rate * x))))) measurableSet_Icc ?ifpos]
  case ifpos; refine ae_of_all ℙ ?ifpos.a;
  simp only [ge_iff_le, not_le, gt_iff_lt, Set.mem_Icc, and_imp]; intro a h0a _; rw [if_pos h0a]
  rw [<-ENNReal.toReal_eq_toReal,  <-integral_eq_lintegral_of_nonneg_ae];
  rw [@integral_Icc_eq_integral_Ioc, <-(Set.uIoc_of_le h)]
  have : (∫ a in Set.uIoc 0 x', rate * rexp (-(rate * a))) =
    (∫ a in (0)..x', rate * rexp (-(rate * a))) := by
      rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, smul_eq_mul, if_pos h, one_mul]
  rw[this]
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le h (f:= fun a => -1* (rexp (-(↑rate * a)))) _ _]
  simp only [neg_mul, one_mul, mul_zero, neg_zero, Real.exp_zero, mul_one, sub_neg_eq_add,
    sub_nonneg, Real.exp_le_one_iff, Left.neg_nonpos_iff, gt_iff_lt]
  rw [ENNReal.toReal_ofReal_eq_iff.2 _]; linarith
  simp only [sub_nonneg, Real.exp_le_one_iff, Left.neg_nonpos_iff, gt_iff_lt];
  exact (zero_le_mul_left ratePos).mpr h
  rw [@intervalIntegrable_iff, (Set.uIoc_of_le h), ← @integrableOn_Icc_iff_integrableOn_Ioc];
  rw [@integrableOn_Icc_iff_integrableOn_Ioc]; apply Integrable.const_mul;
  exact exp_neg_integrableOn_Ioc ratePos; refine Continuous.continuousOn ?h;
  have : Continuous (fun a => rexp (-(rate * a))) := by
    simp only [<-neg_mul]; refine Continuous.exp ?inter; exact continuous_mul_left (-rate)
  refine Continuous.comp' ?hg this; exact continuous_mul_left (-1);
  intro x hx; refine HasDerivAt.hasDerivWithinAt ?hx; apply antiDeriv_expDeriv_pos
  simp only [Set.mem_Ici]; simp only [gt_iff_lt, not_lt, ge_iff_le, Set.mem_Ioo] at hx; linarith
  apply Filter.eventually_of_forall
  intro x; simp only [Pi.zero_apply, gt_iff_lt]; exact le_of_lt (mul_pos ratePos (Real.exp_pos _))
  refine Integrable.aestronglyMeasurable ?_; apply Integrable.const_mul; rw [← @integrableOn_def];
  rw [@integrableOn_Icc_iff_integrableOn_Ioc]; exact exp_neg_integrableOn_Ioc ratePos
  refine LT.lt.ne ?_; refine IntegrableOn.set_lintegral_lt_top ?_;
  rw [@integrableOn_Icc_iff_integrableOn_Ioc];
  apply Integrable.const_mul (exp_neg_integrableOn_Ioc ratePos)
  exact ENNReal.ofReal_ne_top


/-- The Definition of the CDF equals the known Formular ``1 - exp (-(rate * x))``-/

lemma ExpCDF_eq : (exponentialCdfReal rate ratePos) =
  fun x => ite (0 ≤ x) (1 - Real.exp (-(rate * x))) 0 := by
    rw[ExpCDF_eq_lintegral]; ext x; rw [lint_eq_antiDeriv]; rw[@ENNReal.toReal_ofReal_eq_iff]
    split_ifs with h
    . simp only [sub_nonneg, Real.exp_le_one_iff, Left.neg_nonpos_iff, gt_iff_lt]
      exact (mul_nonneg ratePos.le h)
    . linarith
