/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/
import Mathlib.Probability.Notation
import Mathlib.Probability.Process.Stopping

#align_import probability.martingale.basic from "leanprover-community/mathlib"@"ba074af83b6cf54c3104e59402b39410ddbd6dca"

/-!
# Martingales

A family of functions `f : ι → Ω → E` is a martingale with respect to a filtration `ℱ` if every
`f i` is integrable, `f` is adapted with respect to `ℱ` and for all `i ≤ j`,
`μ[f j | ℱ i] =ᵐ[μ] f i`. On the other hand, `f : ι → Ω → E` is said to be a supermartingale
with respect to the filtration `ℱ` if `f i` is integrable, `f` is adapted with resepct to `ℱ`
and for all `i ≤ j`, `μ[f j | ℱ i] ≤ᵐ[μ] f i`. Finally, `f : ι → Ω → E` is said to be a
submartingale with respect to the filtration `ℱ` if `f i` is integrable, `f` is adapted with
resepct to `ℱ` and for all `i ≤ j`, `f i ≤ᵐ[μ] μ[f j | ℱ i]`.

The definitions of filtration and adapted can be found in `Probability.Process.Stopping`.

### Definitions

* `MeasureTheory.Martingale f ℱ μ`: `f` is a martingale with respect to filtration `ℱ` and
  measure `μ`.
* `MeasureTheory.Supermartingale f ℱ μ`: `f` is a supermartingale with respect to
  filtration `ℱ` and measure `μ`.
* `MeasureTheory.Submartingale f ℱ μ`: `f` is a submartingale with respect to filtration `ℱ` and
  measure `μ`.

### Results

* `MeasureTheory.martingale_condexp f ℱ μ`: the sequence `fun i => μ[f | ℱ i, ℱ.le i])` is a
  martingale with respect to `ℱ` and `μ`.

-/


open TopologicalSpace Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

namespace MeasureTheory

variable {Ω E ι : Type*} [Preorder ι] {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f g : ι → Ω → E} {ℱ : Filtration ι m0}

/-- A family of functions `f : ι → Ω → E` is a martingale with respect to a filtration `ℱ` if `f`
is adapted with respect to `ℱ` and for all `i ≤ j`, `μ[f j | ℱ i] =ᵐ[μ] f i`. -/
def Martingale (f : ι → Ω → E) (ℱ : Filtration ι m0) (μ : Measure Ω) : Prop :=
  Adapted ℱ f ∧ ∀ i j, i ≤ j → μ[f j|ℱ i] =ᵐ[μ] f i
#align measure_theory.martingale MeasureTheory.Martingale

/-- A family of integrable functions `f : ι → Ω → E` is a supermartingale with respect to a
filtration `ℱ` if `f` is adapted with respect to `ℱ` and for all `i ≤ j`,
`μ[f j | ℱ.le i] ≤ᵐ[μ] f i`. -/
def Supermartingale [LE E] (f : ι → Ω → E) (ℱ : Filtration ι m0) (μ : Measure Ω) : Prop :=
  Adapted ℱ f ∧ (∀ i j, i ≤ j → μ[f j|ℱ i] ≤ᵐ[μ] f i) ∧ ∀ i, Integrable (f i) μ
#align measure_theory.supermartingale MeasureTheory.Supermartingale

/-- A family of integrable functions `f : ι → Ω → E` is a submartingale with respect to a
filtration `ℱ` if `f` is adapted with respect to `ℱ` and for all `i ≤ j`,
`f i ≤ᵐ[μ] μ[f j | ℱ.le i]`. -/
def Submartingale [LE E] (f : ι → Ω → E) (ℱ : Filtration ι m0) (μ : Measure Ω) : Prop :=
  Adapted ℱ f ∧ (∀ i j, i ≤ j → f i ≤ᵐ[μ] μ[f j|ℱ i]) ∧ ∀ i, Integrable (f i) μ
#align measure_theory.submartingale MeasureTheory.Submartingale

theorem martingale_const (ℱ : Filtration ι m0) (μ : Measure Ω) [IsFiniteMeasure μ] (x : E) :
    Martingale (fun _ _ => x) ℱ μ :=
  ⟨adapted_const ℱ _, fun i j _ => by rw [condexp_const (ℱ.le _)]⟩
#align measure_theory.martingale_const MeasureTheory.martingale_const

theorem martingale_const_fun [OrderBot ι] (ℱ : Filtration ι m0) (μ : Measure Ω) [IsFiniteMeasure μ]
    {f : Ω → E} (hf : StronglyMeasurable[ℱ ⊥] f) (hfint : Integrable f μ) :
    Martingale (fun _ => f) ℱ μ := by
  refine ⟨fun i => hf.mono <| ℱ.mono bot_le, fun i j _ => ?_⟩
  rw [condexp_of_stronglyMeasurable (ℱ.le _) (hf.mono <| ℱ.mono bot_le) hfint]
#align measure_theory.martingale_const_fun MeasureTheory.martingale_const_fun

variable (E)

theorem martingale_zero (ℱ : Filtration ι m0) (μ : Measure Ω) : Martingale (0 : ι → Ω → E) ℱ μ :=
  ⟨adapted_zero E ℱ, fun i j _ => by rw [Pi.zero_apply, condexp_zero]; simp⟩
#align measure_theory.martingale_zero MeasureTheory.martingale_zero

variable {E}

namespace Martingale

protected theorem adapted (hf : Martingale f ℱ μ) : Adapted ℱ f :=
  hf.1
#align measure_theory.martingale.adapted MeasureTheory.Martingale.adapted

protected theorem stronglyMeasurable (hf : Martingale f ℱ μ) (i : ι) :
    StronglyMeasurable[ℱ i] (f i) :=
  hf.adapted i
#align measure_theory.martingale.strongly_measurable MeasureTheory.Martingale.stronglyMeasurable

theorem condexp_ae_eq (hf : Martingale f ℱ μ) {i j : ι} (hij : i ≤ j) : μ[f j|ℱ i] =ᵐ[μ] f i :=
  hf.2 i j hij
#align measure_theory.martingale.condexp_ae_eq MeasureTheory.Martingale.condexp_ae_eq

protected theorem integrable (hf : Martingale f ℱ μ) (i : ι) : Integrable (f i) μ :=
  integrable_condexp.congr (hf.condexp_ae_eq (le_refl i))
#align measure_theory.martingale.integrable MeasureTheory.Martingale.integrable

theorem setIntegral_eq [SigmaFiniteFiltration μ ℱ] (hf : Martingale f ℱ μ) {i j : ι} (hij : i ≤ j)
    {s : Set Ω} (hs : MeasurableSet[ℱ i] s) : ∫ ω in s, f i ω ∂μ = ∫ ω in s, f j ω ∂μ := by
  rw [← @setIntegral_condexp _ _ _ _ _ (ℱ i) m0 _ _ _ (ℱ.le i) _ (hf.integrable j) hs]
  refine setIntegral_congr_ae (ℱ.le i s hs) ?_
  filter_upwards [hf.2 i j hij] with _ heq _ using heq.symm
#align measure_theory.martingale.set_integral_eq MeasureTheory.Martingale.setIntegral_eq

@[deprecated (since := "2024-04-17")]
alias set_integral_eq := setIntegral_eq

theorem add (hf : Martingale f ℱ μ) (hg : Martingale g ℱ μ) : Martingale (f + g) ℱ μ := by
  refine ⟨hf.adapted.add hg.adapted, fun i j hij => ?_⟩
  exact (condexp_add (hf.integrable j) (hg.integrable j)).trans ((hf.2 i j hij).add (hg.2 i j hij))
#align measure_theory.martingale.add MeasureTheory.Martingale.add

theorem neg (hf : Martingale f ℱ μ) : Martingale (-f) ℱ μ :=
  ⟨hf.adapted.neg, fun i j hij => (condexp_neg (f j)).trans (hf.2 i j hij).neg⟩
#align measure_theory.martingale.neg MeasureTheory.Martingale.neg

theorem sub (hf : Martingale f ℱ μ) (hg : Martingale g ℱ μ) : Martingale (f - g) ℱ μ := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg
#align measure_theory.martingale.sub MeasureTheory.Martingale.sub

theorem smul (c : ℝ) (hf : Martingale f ℱ μ) : Martingale (c • f) ℱ μ := by
  refine ⟨hf.adapted.smul c, fun i j hij => ?_⟩
  refine (condexp_smul c (f j)).trans ((hf.2 i j hij).mono fun x hx => ?_)
  simp only [Pi.smul_apply, hx]
#align measure_theory.martingale.smul MeasureTheory.Martingale.smul

theorem supermartingale [Preorder E] (hf : Martingale f ℱ μ) : Supermartingale f ℱ μ :=
  ⟨hf.1, fun i j hij => (hf.2 i j hij).le, fun i => hf.integrable i⟩
#align measure_theory.martingale.supermartingale MeasureTheory.Martingale.supermartingale

theorem submartingale [Preorder E] (hf : Martingale f ℱ μ) : Submartingale f ℱ μ :=
  ⟨hf.1, fun i j hij => (hf.2 i j hij).symm.le, fun i => hf.integrable i⟩
#align measure_theory.martingale.submartingale MeasureTheory.Martingale.submartingale

end Martingale

theorem martingale_iff [PartialOrder E] :
    Martingale f ℱ μ ↔ Supermartingale f ℱ μ ∧ Submartingale f ℱ μ :=
  ⟨fun hf => ⟨hf.supermartingale, hf.submartingale⟩, fun ⟨hf₁, hf₂⟩ =>
    ⟨hf₁.1, fun i j hij => (hf₁.2.1 i j hij).antisymm (hf₂.2.1 i j hij)⟩⟩
#align measure_theory.martingale_iff MeasureTheory.martingale_iff

theorem martingale_condexp (f : Ω → E) (ℱ : Filtration ι m0) (μ : Measure Ω)
    [SigmaFiniteFiltration μ ℱ] : Martingale (fun i => μ[f|ℱ i]) ℱ μ :=
  ⟨fun _ => stronglyMeasurable_condexp, fun _ j hij => condexp_condexp_of_le (ℱ.mono hij) (ℱ.le j)⟩
#align measure_theory.martingale_condexp MeasureTheory.martingale_condexp

namespace Supermartingale

protected theorem adapted [LE E] (hf : Supermartingale f ℱ μ) : Adapted ℱ f :=
  hf.1
#align measure_theory.supermartingale.adapted MeasureTheory.Supermartingale.adapted

protected theorem stronglyMeasurable [LE E] (hf : Supermartingale f ℱ μ) (i : ι) :
    StronglyMeasurable[ℱ i] (f i) :=
  hf.adapted i
#align measure_theory.supermartingale.strongly_measurable MeasureTheory.Supermartingale.stronglyMeasurable

protected theorem integrable [LE E] (hf : Supermartingale f ℱ μ) (i : ι) : Integrable (f i) μ :=
  hf.2.2 i
#align measure_theory.supermartingale.integrable MeasureTheory.Supermartingale.integrable

theorem condexp_ae_le [LE E] (hf : Supermartingale f ℱ μ) {i j : ι} (hij : i ≤ j) :
    μ[f j|ℱ i] ≤ᵐ[μ] f i :=
  hf.2.1 i j hij
#align measure_theory.supermartingale.condexp_ae_le MeasureTheory.Supermartingale.condexp_ae_le

theorem setIntegral_le [SigmaFiniteFiltration μ ℱ] {f : ι → Ω → ℝ} (hf : Supermartingale f ℱ μ)
    {i j : ι} (hij : i ≤ j) {s : Set Ω} (hs : MeasurableSet[ℱ i] s) :
    ∫ ω in s, f j ω ∂μ ≤ ∫ ω in s, f i ω ∂μ := by
  rw [← setIntegral_condexp (ℱ.le i) (hf.integrable j) hs]
  refine setIntegral_mono_ae integrable_condexp.integrableOn (hf.integrable i).integrableOn ?_
  filter_upwards [hf.2.1 i j hij] with _ heq using heq
#align measure_theory.supermartingale.set_integral_le MeasureTheory.Supermartingale.setIntegral_le

@[deprecated (since := "2024-04-17")]
alias set_integral_le := setIntegral_le

theorem add [Preorder E] [CovariantClass E E (· + ·) (· ≤ ·)] (hf : Supermartingale f ℱ μ)
    (hg : Supermartingale g ℱ μ) : Supermartingale (f + g) ℱ μ := by
  refine ⟨hf.1.add hg.1, fun i j hij => ?_, fun i => (hf.2.2 i).add (hg.2.2 i)⟩
  refine (condexp_add (hf.integrable j) (hg.integrable j)).le.trans ?_
  filter_upwards [hf.2.1 i j hij, hg.2.1 i j hij]
  intros
  refine add_le_add ?_ ?_ <;> assumption
#align measure_theory.supermartingale.add MeasureTheory.Supermartingale.add

theorem add_martingale [Preorder E] [CovariantClass E E (· + ·) (· ≤ ·)]
    (hf : Supermartingale f ℱ μ) (hg : Martingale g ℱ μ) : Supermartingale (f + g) ℱ μ :=
  hf.add hg.supermartingale
#align measure_theory.supermartingale.add_martingale MeasureTheory.Supermartingale.add_martingale

theorem neg [Preorder E] [CovariantClass E E (· + ·) (· ≤ ·)] (hf : Supermartingale f ℱ μ) :
    Submartingale (-f) ℱ μ := by
  refine ⟨hf.1.neg, fun i j hij => ?_, fun i => (hf.2.2 i).neg⟩
  refine EventuallyLE.trans ?_ (condexp_neg (f j)).symm.le
  filter_upwards [hf.2.1 i j hij] with _ _
  simpa
#align measure_theory.supermartingale.neg MeasureTheory.Supermartingale.neg

end Supermartingale

namespace Submartingale

protected theorem adapted [LE E] (hf : Submartingale f ℱ μ) : Adapted ℱ f :=
  hf.1
#align measure_theory.submartingale.adapted MeasureTheory.Submartingale.adapted

protected theorem stronglyMeasurable [LE E] (hf : Submartingale f ℱ μ) (i : ι) :
    StronglyMeasurable[ℱ i] (f i) :=
  hf.adapted i
#align measure_theory.submartingale.strongly_measurable MeasureTheory.Submartingale.stronglyMeasurable

protected theorem integrable [LE E] (hf : Submartingale f ℱ μ) (i : ι) : Integrable (f i) μ :=
  hf.2.2 i
#align measure_theory.submartingale.integrable MeasureTheory.Submartingale.integrable

theorem ae_le_condexp [LE E] (hf : Submartingale f ℱ μ) {i j : ι} (hij : i ≤ j) :
    f i ≤ᵐ[μ] μ[f j|ℱ i] :=
  hf.2.1 i j hij
#align measure_theory.submartingale.ae_le_condexp MeasureTheory.Submartingale.ae_le_condexp

theorem add [Preorder E] [CovariantClass E E (· + ·) (· ≤ ·)] (hf : Submartingale f ℱ μ)
    (hg : Submartingale g ℱ μ) : Submartingale (f + g) ℱ μ := by
  refine ⟨hf.1.add hg.1, fun i j hij => ?_, fun i => (hf.2.2 i).add (hg.2.2 i)⟩
  refine EventuallyLE.trans ?_ (condexp_add (hf.integrable j) (hg.integrable j)).symm.le
  filter_upwards [hf.2.1 i j hij, hg.2.1 i j hij]
  intros
  refine add_le_add ?_ ?_ <;> assumption
#align measure_theory.submartingale.add MeasureTheory.Submartingale.add

theorem add_martingale [Preorder E] [CovariantClass E E (· + ·) (· ≤ ·)] (hf : Submartingale f ℱ μ)
    (hg : Martingale g ℱ μ) : Submartingale (f + g) ℱ μ :=
  hf.add hg.submartingale
#align measure_theory.submartingale.add_martingale MeasureTheory.Submartingale.add_martingale

theorem neg [Preorder E] [CovariantClass E E (· + ·) (· ≤ ·)] (hf : Submartingale f ℱ μ) :
    Supermartingale (-f) ℱ μ := by
  refine ⟨hf.1.neg, fun i j hij => (condexp_neg (f j)).le.trans ?_, fun i => (hf.2.2 i).neg⟩
  filter_upwards [hf.2.1 i j hij] with _ _
  simpa
#align measure_theory.submartingale.neg MeasureTheory.Submartingale.neg

/-- The converse of this lemma is `MeasureTheory.submartingale_of_setIntegral_le`. -/
theorem setIntegral_le [SigmaFiniteFiltration μ ℱ] {f : ι → Ω → ℝ} (hf : Submartingale f ℱ μ)
    {i j : ι} (hij : i ≤ j) {s : Set Ω} (hs : MeasurableSet[ℱ i] s) :
    ∫ ω in s, f i ω ∂μ ≤ ∫ ω in s, f j ω ∂μ := by
  rw [← neg_le_neg_iff, ← integral_neg, ← integral_neg]
  exact Supermartingale.setIntegral_le hf.neg hij hs
#align measure_theory.submartingale.set_integral_le MeasureTheory.Submartingale.setIntegral_le

@[deprecated (since := "2024-04-17")]
alias set_integral_le := setIntegral_le

theorem sub_supermartingale [Preorder E] [CovariantClass E E (· + ·) (· ≤ ·)]
    (hf : Submartingale f ℱ μ) (hg : Supermartingale g ℱ μ) : Submartingale (f - g) ℱ μ := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg
#align measure_theory.submartingale.sub_supermartingale MeasureTheory.Submartingale.sub_supermartingale

theorem sub_martingale [Preorder E] [CovariantClass E E (· + ·) (· ≤ ·)] (hf : Submartingale f ℱ μ)
    (hg : Martingale g ℱ μ) : Submartingale (f - g) ℱ μ :=
  hf.sub_supermartingale hg.supermartingale
#align measure_theory.submartingale.sub_martingale MeasureTheory.Submartingale.sub_martingale

protected theorem sup {f g : ι → Ω → ℝ} (hf : Submartingale f ℱ μ) (hg : Submartingale g ℱ μ) :
    Submartingale (f ⊔ g) ℱ μ := by
  refine ⟨fun i => @StronglyMeasurable.sup _ _ _ _ (ℱ i) _ _ _ (hf.adapted i) (hg.adapted i),
    fun i j hij => ?_, fun i => Integrable.sup (hf.integrable _) (hg.integrable _)⟩
  refine EventuallyLE.sup_le ?_ ?_
  · exact EventuallyLE.trans (hf.2.1 i j hij)
      (condexp_mono (hf.integrable _) (Integrable.sup (hf.integrable j) (hg.integrable j))
        (eventually_of_forall fun x => le_max_left _ _))
  · exact EventuallyLE.trans (hg.2.1 i j hij)
      (condexp_mono (hg.integrable _) (Integrable.sup (hf.integrable j) (hg.integrable j))
        (eventually_of_forall fun x => le_max_right _ _))
#align measure_theory.submartingale.sup MeasureTheory.Submartingale.sup

protected theorem pos {f : ι → Ω → ℝ} (hf : Submartingale f ℱ μ) : Submartingale (f⁺) ℱ μ :=
  hf.sup (martingale_zero _ _ _).submartingale
#align measure_theory.submartingale.pos MeasureTheory.Submartingale.pos

end Submartingale

section Submartingale

theorem submartingale_of_setIntegral_le [IsFiniteMeasure μ] {f : ι → Ω → ℝ} (hadp : Adapted ℱ f)
    (hint : ∀ i, Integrable (f i) μ) (hf : ∀ i j : ι,
      i ≤ j → ∀ s : Set Ω, MeasurableSet[ℱ i] s → ∫ ω in s, f i ω ∂μ ≤ ∫ ω in s, f j ω ∂μ) :
    Submartingale f ℱ μ := by
  refine ⟨hadp, fun i j hij => ?_, hint⟩
  suffices f i ≤ᵐ[μ.trim (ℱ.le i)] μ[f j|ℱ i] by exact ae_le_of_ae_le_trim this
  suffices 0 ≤ᵐ[μ.trim (ℱ.le i)] μ[f j|ℱ i] - f i by
    filter_upwards [this] with x hx
    rwa [← sub_nonneg]
  refine ae_nonneg_of_forall_setIntegral_nonneg
    ((integrable_condexp.sub (hint i)).trim _ (stronglyMeasurable_condexp.sub <| hadp i))
      fun s hs _ => ?_
  specialize hf i j hij s hs
  rwa [← setIntegral_trim _ (stronglyMeasurable_condexp.sub <| hadp i) hs,
    integral_sub' integrable_condexp.integrableOn (hint i).integrableOn, sub_nonneg,
    setIntegral_condexp (ℱ.le i) (hint j) hs]
#align measure_theory.submartingale_of_set_integral_le MeasureTheory.submartingale_of_setIntegral_le

@[deprecated (since := "2024-04-17")]
alias submartingale_of_set_integral_le := submartingale_of_setIntegral_le

theorem submartingale_of_condexp_sub_nonneg [IsFiniteMeasure μ] {f : ι → Ω → ℝ} (hadp : Adapted ℱ f)
    (hint : ∀ i, Integrable (f i) μ) (hf : ∀ i j, i ≤ j → 0 ≤ᵐ[μ] μ[f j - f i|ℱ i]) :
    Submartingale f ℱ μ := by
  refine ⟨hadp, fun i j hij => ?_, hint⟩
  rw [← condexp_of_stronglyMeasurable (ℱ.le _) (hadp _) (hint _), ← eventually_sub_nonneg]
  exact EventuallyLE.trans (hf i j hij) (condexp_sub (hint _) (hint _)).le
#align measure_theory.submartingale_of_condexp_sub_nonneg MeasureTheory.submartingale_of_condexp_sub_nonneg

theorem Submartingale.condexp_sub_nonneg {f : ι → Ω → ℝ} (hf : Submartingale f ℱ μ) {i j : ι}
    (hij : i ≤ j) : 0 ≤ᵐ[μ] μ[f j - f i|ℱ i] := by
  by_cases h : SigmaFinite (μ.trim (ℱ.le i))
  swap; · rw [condexp_of_not_sigmaFinite (ℱ.le i) h]
  refine EventuallyLE.trans ?_ (condexp_sub (hf.integrable _) (hf.integrable _)).symm.le
  rw [eventually_sub_nonneg,
    condexp_of_stronglyMeasurable (ℱ.le _) (hf.adapted _) (hf.integrable _)]
  exact hf.2.1 i j hij
#align measure_theory.submartingale.condexp_sub_nonneg MeasureTheory.Submartingale.condexp_sub_nonneg

theorem submartingale_iff_condexp_sub_nonneg [IsFiniteMeasure μ] {f : ι → Ω → ℝ} :
    Submartingale f ℱ μ ↔
      Adapted ℱ f ∧ (∀ i, Integrable (f i) μ) ∧ ∀ i j, i ≤ j → 0 ≤ᵐ[μ] μ[f j - f i|ℱ i] :=
  ⟨fun h => ⟨h.adapted, h.integrable, fun _ _ => h.condexp_sub_nonneg⟩, fun ⟨hadp, hint, h⟩ =>
    submartingale_of_condexp_sub_nonneg hadp hint h⟩
#align measure_theory.submartingale_iff_condexp_sub_nonneg MeasureTheory.submartingale_iff_condexp_sub_nonneg

end Submartingale

namespace Supermartingale

theorem sub_submartingale [Preorder E] [CovariantClass E E (· + ·) (· ≤ ·)]
    (hf : Supermartingale f ℱ μ) (hg : Submartingale g ℱ μ) : Supermartingale (f - g) ℱ μ := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg
#align measure_theory.supermartingale.sub_submartingale MeasureTheory.Supermartingale.sub_submartingale

theorem sub_martingale [Preorder E] [CovariantClass E E (· + ·) (· ≤ ·)]
    (hf : Supermartingale f ℱ μ) (hg : Martingale g ℱ μ) : Supermartingale (f - g) ℱ μ :=
  hf.sub_submartingale hg.submartingale
#align measure_theory.supermartingale.sub_martingale MeasureTheory.Supermartingale.sub_martingale

section

variable {F : Type*} [NormedLatticeAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [OrderedSMul ℝ F]

theorem smul_nonneg {f : ι → Ω → F} {c : ℝ} (hc : 0 ≤ c) (hf : Supermartingale f ℱ μ) :
    Supermartingale (c • f) ℱ μ := by
  refine ⟨hf.1.smul c, fun i j hij => ?_, fun i => (hf.2.2 i).smul c⟩
  refine (condexp_smul c (f j)).le.trans ?_
  filter_upwards [hf.2.1 i j hij] with _ hle
  simp_rw [Pi.smul_apply]
  exact smul_le_smul_of_nonneg_left hle hc
#align measure_theory.supermartingale.smul_nonneg MeasureTheory.Supermartingale.smul_nonneg

theorem smul_nonpos {f : ι → Ω → F} {c : ℝ} (hc : c ≤ 0) (hf : Supermartingale f ℱ μ) :
    Submartingale (c • f) ℱ μ := by
  rw [← neg_neg c, (by ext (i x); simp : - -c • f = -(-c • f))]
  exact (hf.smul_nonneg <| neg_nonneg.2 hc).neg
#align measure_theory.supermartingale.smul_nonpos MeasureTheory.Supermartingale.smul_nonpos

end

end Supermartingale

namespace Submartingale

section

variable {F : Type*} [NormedLatticeAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [OrderedSMul ℝ F]

theorem smul_nonneg {f : ι → Ω → F} {c : ℝ} (hc : 0 ≤ c) (hf : Submartingale f ℱ μ) :
    Submartingale (c • f) ℱ μ := by
  rw [← neg_neg c, (by ext (i x); simp : - -c • f = -(c • -f))]
  exact Supermartingale.neg (hf.neg.smul_nonneg hc)
#align measure_theory.submartingale.smul_nonneg MeasureTheory.Submartingale.smul_nonneg

theorem smul_nonpos {f : ι → Ω → F} {c : ℝ} (hc : c ≤ 0) (hf : Submartingale f ℱ μ) :
    Supermartingale (c • f) ℱ μ := by
  rw [← neg_neg c, (by ext (i x); simp : - -c • f = -(-c • f))]
  exact (hf.smul_nonneg <| neg_nonneg.2 hc).neg
#align measure_theory.submartingale.smul_nonpos MeasureTheory.Submartingale.smul_nonpos

end

end Submartingale

section Nat

variable {𝒢 : Filtration ℕ m0}

theorem submartingale_of_setIntegral_le_succ [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ}
    (hadp : Adapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i, ∀ s : Set Ω, MeasurableSet[𝒢 i] s → ∫ ω in s, f i ω ∂μ ≤ ∫ ω in s, f (i + 1) ω ∂μ) :
    Submartingale f 𝒢 μ := by
  refine submartingale_of_setIntegral_le hadp hint fun i j hij s hs => ?_
  induction' hij with k hk₁ hk₂
  · exact le_rfl
  · exact le_trans hk₂ (hf k s (𝒢.mono hk₁ _ hs))
#align measure_theory.submartingale_of_set_integral_le_succ MeasureTheory.submartingale_of_setIntegral_le_succ

@[deprecated (since := "2024-04-17")]
alias submartingale_of_set_integral_le_succ := submartingale_of_setIntegral_le_succ

theorem supermartingale_of_setIntegral_succ_le [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ}
    (hadp : Adapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i, ∀ s : Set Ω, MeasurableSet[𝒢 i] s → ∫ ω in s, f (i + 1) ω ∂μ ≤ ∫ ω in s, f i ω ∂μ) :
    Supermartingale f 𝒢 μ := by
  rw [← neg_neg f]
  refine (submartingale_of_setIntegral_le_succ hadp.neg (fun i => (hint i).neg) ?_).neg
  simpa only [integral_neg, Pi.neg_apply, neg_le_neg_iff]
#align measure_theory.supermartingale_of_set_integral_succ_le MeasureTheory.supermartingale_of_setIntegral_succ_le

@[deprecated (since := "2024-04-17")]
alias supermartingale_of_set_integral_succ_le := supermartingale_of_setIntegral_succ_le

theorem martingale_of_setIntegral_eq_succ [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} (hadp : Adapted 𝒢 f)
    (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i, ∀ s : Set Ω, MeasurableSet[𝒢 i] s → ∫ ω in s, f i ω ∂μ = ∫ ω in s, f (i + 1) ω ∂μ) :
    Martingale f 𝒢 μ :=
  martingale_iff.2 ⟨supermartingale_of_setIntegral_succ_le hadp hint fun i s hs => (hf i s hs).ge,
    submartingale_of_setIntegral_le_succ hadp hint fun i s hs => (hf i s hs).le⟩
#align measure_theory.martingale_of_set_integral_eq_succ MeasureTheory.martingale_of_setIntegral_eq_succ

@[deprecated (since := "2024-04-17")]
alias martingale_of_set_integral_eq_succ := martingale_of_setIntegral_eq_succ

theorem submartingale_nat [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} (hadp : Adapted 𝒢 f)
    (hint : ∀ i, Integrable (f i) μ) (hf : ∀ i, f i ≤ᵐ[μ] μ[f (i + 1)|𝒢 i]) :
    Submartingale f 𝒢 μ := by
  refine submartingale_of_setIntegral_le_succ hadp hint fun i s hs => ?_
  have : ∫ ω in s, f (i + 1) ω ∂μ = ∫ ω in s, (μ[f (i + 1)|𝒢 i]) ω ∂μ :=
    (setIntegral_condexp (𝒢.le i) (hint _) hs).symm
  rw [this]
  exact setIntegral_mono_ae (hint i).integrableOn integrable_condexp.integrableOn (hf i)
#align measure_theory.submartingale_nat MeasureTheory.submartingale_nat

theorem supermartingale_nat [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} (hadp : Adapted 𝒢 f)
    (hint : ∀ i, Integrable (f i) μ) (hf : ∀ i, μ[f (i + 1)|𝒢 i] ≤ᵐ[μ] f i) :
    Supermartingale f 𝒢 μ := by
  rw [← neg_neg f]
  refine (submartingale_nat hadp.neg (fun i => (hint i).neg) fun i =>
    EventuallyLE.trans ?_ (condexp_neg _).symm.le).neg
  filter_upwards [hf i] with x hx using neg_le_neg hx
#align measure_theory.supermartingale_nat MeasureTheory.supermartingale_nat

theorem martingale_nat [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} (hadp : Adapted 𝒢 f)
    (hint : ∀ i, Integrable (f i) μ) (hf : ∀ i, f i =ᵐ[μ] μ[f (i + 1)|𝒢 i]) : Martingale f 𝒢 μ :=
  martingale_iff.2 ⟨supermartingale_nat hadp hint fun i => (hf i).symm.le,
    submartingale_nat hadp hint fun i => (hf i).le⟩
#align measure_theory.martingale_nat MeasureTheory.martingale_nat

theorem submartingale_of_condexp_sub_nonneg_nat [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ}
    (hadp : Adapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i, 0 ≤ᵐ[μ] μ[f (i + 1) - f i|𝒢 i]) : Submartingale f 𝒢 μ := by
  refine submartingale_nat hadp hint fun i => ?_
  rw [← condexp_of_stronglyMeasurable (𝒢.le _) (hadp _) (hint _), ← eventually_sub_nonneg]
  exact EventuallyLE.trans (hf i) (condexp_sub (hint _) (hint _)).le
#align measure_theory.submartingale_of_condexp_sub_nonneg_nat MeasureTheory.submartingale_of_condexp_sub_nonneg_nat

theorem supermartingale_of_condexp_sub_nonneg_nat [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ}
    (hadp : Adapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i, 0 ≤ᵐ[μ] μ[f i - f (i + 1)|𝒢 i]) : Supermartingale f 𝒢 μ := by
  rw [← neg_neg f]
  refine (submartingale_of_condexp_sub_nonneg_nat hadp.neg (fun i => (hint i).neg) ?_).neg
  simpa only [Pi.zero_apply, Pi.neg_apply, neg_sub_neg]
#align measure_theory.supermartingale_of_condexp_sub_nonneg_nat MeasureTheory.supermartingale_of_condexp_sub_nonneg_nat

theorem martingale_of_condexp_sub_eq_zero_nat [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ}
    (hadp : Adapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i, μ[f (i + 1) - f i|𝒢 i] =ᵐ[μ] 0) : Martingale f 𝒢 μ := by
  refine martingale_iff.2 ⟨supermartingale_of_condexp_sub_nonneg_nat hadp hint fun i => ?_,
    submartingale_of_condexp_sub_nonneg_nat hadp hint fun i => (hf i).symm.le⟩
  rw [← neg_sub]
  refine (EventuallyEq.trans ?_ (condexp_neg _).symm).le
  filter_upwards [hf i] with x hx
  simpa only [Pi.zero_apply, Pi.neg_apply, zero_eq_neg]
#align measure_theory.martingale_of_condexp_sub_eq_zero_nat MeasureTheory.martingale_of_condexp_sub_eq_zero_nat

-- Note that one cannot use `Submartingale.zero_le_of_predictable` to prove the other two
-- corresponding lemmas without imposing more restrictions to the ordering of `E`
/-- A predictable submartingale is a.e. greater equal than its initial state. -/
theorem Submartingale.zero_le_of_predictable [Preorder E] [SigmaFiniteFiltration μ 𝒢]
    {f : ℕ → Ω → E} (hfmgle : Submartingale f 𝒢 μ) (hfadp : Adapted 𝒢 fun n => f (n + 1)) (n : ℕ) :
    f 0 ≤ᵐ[μ] f n := by
  induction' n with k ih
  · rfl
  · exact ih.trans ((hfmgle.2.1 k (k + 1) k.le_succ).trans_eq <| Germ.coe_eq.mp <|
    congr_arg Germ.ofFun <| condexp_of_stronglyMeasurable (𝒢.le _) (hfadp _) <| hfmgle.integrable _)
#align measure_theory.submartingale.zero_le_of_predictable MeasureTheory.Submartingale.zero_le_of_predictable

/-- A predictable supermartingale is a.e. less equal than its initial state. -/
theorem Supermartingale.le_zero_of_predictable [Preorder E] [SigmaFiniteFiltration μ 𝒢]
    {f : ℕ → Ω → E} (hfmgle : Supermartingale f 𝒢 μ) (hfadp : Adapted 𝒢 fun n => f (n + 1))
    (n : ℕ) : f n ≤ᵐ[μ] f 0 := by
  induction' n with k ih
  · rfl
  · exact ((Germ.coe_eq.mp <| congr_arg Germ.ofFun <| condexp_of_stronglyMeasurable (𝒢.le _)
      (hfadp _) <| hfmgle.integrable _).symm.trans_le (hfmgle.2.1 k (k + 1) k.le_succ)).trans ih
#align measure_theory.supermartingale.le_zero_of_predictable MeasureTheory.Supermartingale.le_zero_of_predictable

/-- A predictable martingale is a.e. equal to its initial state. -/
theorem Martingale.eq_zero_of_predictable [SigmaFiniteFiltration μ 𝒢] {f : ℕ → Ω → E}
    (hfmgle : Martingale f 𝒢 μ) (hfadp : Adapted 𝒢 fun n => f (n + 1)) (n : ℕ) : f n =ᵐ[μ] f 0 := by
  induction' n with k ih
  · rfl
  · exact ((Germ.coe_eq.mp (congr_arg Germ.ofFun <| condexp_of_stronglyMeasurable (𝒢.le _) (hfadp _)
      (hfmgle.integrable _))).symm.trans (hfmgle.2 k (k + 1) k.le_succ)).trans ih
#align measure_theory.martingale.eq_zero_of_predictable MeasureTheory.Martingale.eq_zero_of_predictable

namespace Submartingale

protected theorem integrable_stoppedValue [LE E] {f : ℕ → Ω → E} (hf : Submartingale f 𝒢 μ)
    {τ : Ω → ℕ} (hτ : IsStoppingTime 𝒢 τ) {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) :
    Integrable (stoppedValue f τ) μ :=
  integrable_stoppedValue ℕ hτ hf.integrable hbdd
#align measure_theory.submartingale.integrable_stopped_value MeasureTheory.Submartingale.integrable_stoppedValue

end Submartingale

theorem Submartingale.sum_mul_sub [IsFiniteMeasure μ] {R : ℝ} {ξ f : ℕ → Ω → ℝ}
    (hf : Submartingale f 𝒢 μ) (hξ : Adapted 𝒢 ξ) (hbdd : ∀ n ω, ξ n ω ≤ R)
    (hnonneg : ∀ n ω, 0 ≤ ξ n ω) :
    Submartingale (fun n => ∑ k ∈ Finset.range n, ξ k * (f (k + 1) - f k)) 𝒢 μ := by
  have hξbdd : ∀ i, ∃ C, ∀ ω, |ξ i ω| ≤ C := fun i =>
    ⟨R, fun ω => (abs_of_nonneg (hnonneg i ω)).trans_le (hbdd i ω)⟩
  have hint : ∀ m, Integrable (∑ k ∈ Finset.range m, ξ k * (f (k + 1) - f k)) μ := fun m =>
    integrable_finset_sum' _ fun i _ => Integrable.bdd_mul ((hf.integrable _).sub (hf.integrable _))
      hξ.stronglyMeasurable.aestronglyMeasurable (hξbdd _)
  have hadp : Adapted 𝒢 fun n => ∑ k ∈ Finset.range n, ξ k * (f (k + 1) - f k) := by
    intro m
    refine Finset.stronglyMeasurable_sum' _ fun i hi => ?_
    rw [Finset.mem_range] at hi
    exact (hξ.stronglyMeasurable_le hi.le).mul
      ((hf.adapted.stronglyMeasurable_le (Nat.succ_le_of_lt hi)).sub
        (hf.adapted.stronglyMeasurable_le hi.le))
  refine submartingale_of_condexp_sub_nonneg_nat hadp hint fun i => ?_
  simp only [← Finset.sum_Ico_eq_sub _ (Nat.le_succ _), Finset.sum_apply, Pi.mul_apply,
    Pi.sub_apply, Nat.Ico_succ_singleton, Finset.sum_singleton]
  exact EventuallyLE.trans (EventuallyLE.mul_nonneg (eventually_of_forall (hnonneg _))
    (hf.condexp_sub_nonneg (Nat.le_succ _))) (condexp_stronglyMeasurable_mul (hξ _)
    (((hf.integrable _).sub (hf.integrable _)).bdd_mul
      hξ.stronglyMeasurable.aestronglyMeasurable (hξbdd _))
    ((hf.integrable _).sub (hf.integrable _))).symm.le
#align measure_theory.submartingale.sum_mul_sub MeasureTheory.Submartingale.sum_mul_sub

/-- Given a discrete submartingale `f` and a predictable process `ξ` (i.e. `ξ (n + 1)` is adapted)
the process defined by `fun n => ∑ k ∈ Finset.range n, ξ (k + 1) * (f (k + 1) - f k)` is also a
submartingale. -/
theorem Submartingale.sum_mul_sub' [IsFiniteMeasure μ] {R : ℝ} {ξ f : ℕ → Ω → ℝ}
    (hf : Submartingale f 𝒢 μ) (hξ : Adapted 𝒢 fun n => ξ (n + 1)) (hbdd : ∀ n ω, ξ n ω ≤ R)
    (hnonneg : ∀ n ω, 0 ≤ ξ n ω) :
    Submartingale (fun n => ∑ k ∈ Finset.range n, ξ (k + 1) * (f (k + 1) - f k)) 𝒢 μ :=
  hf.sum_mul_sub hξ (fun _ => hbdd _) fun _ => hnonneg _
#align measure_theory.submartingale.sum_mul_sub' MeasureTheory.Submartingale.sum_mul_sub'

end Nat

end MeasureTheory
