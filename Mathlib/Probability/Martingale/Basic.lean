/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.Probability.Process.Predictable
public import Mathlib.Probability.Process.Stopping

/-!
# Martingales

A family of functions `f : ι → Ω → E` is a martingale with respect to a filtration `ℱ` if every
`f i` is integrable, `f` is strongly adapted with respect to `ℱ` and for all `i ≤ j`,
`μ[f j | ℱ i] =ᵐ[μ] f i`. On the other hand, `f : ι → Ω → E` is said to be a supermartingale
with respect to the filtration `ℱ` if `f i` is integrable, `f` is strongly adapted with respect to
`ℱ` and for all `i ≤ j`, `μ[f j | ℱ i] ≤ᵐ[μ] f i`. Finally, `f : ι → Ω → E` is said to be a
submartingale with respect to the filtration `ℱ` if `f i` is integrable, `f` is strongly adapted
with respect to `ℱ` and for all `i ≤ j`, `f i ≤ᵐ[μ] μ[f j | ℱ i]`.

### Definitions

* `MeasureTheory.Martingale f ℱ μ`: `f` is a martingale with respect to filtration `ℱ` and
  measure `μ`.
* `MeasureTheory.Supermartingale f ℱ μ`: `f` is a supermartingale with respect to
  filtration `ℱ` and measure `μ`.
* `MeasureTheory.Submartingale f ℱ μ`: `f` is a submartingale with respect to filtration `ℱ` and
  measure `μ`.

### Results

* `MeasureTheory.martingale_condExp f ℱ μ`: the sequence `fun i => μ[f | ℱ i]` is a
  martingale with respect to `ℱ` and `μ`.

-/

@[expose] public section


open TopologicalSpace Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

namespace MeasureTheory

variable {Ω E ι : Type*} [Preorder ι] {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f g : ι → Ω → E} {ℱ : Filtration ι m0}

/-- A family of functions `f : ι → Ω → E` is a martingale with respect to a filtration `ℱ` if `f`
is strongly adapted with respect to `ℱ` and for all `i ≤ j`, `μ[f j | ℱ i] =ᵐ[μ] f i`. -/
def Martingale (f : ι → Ω → E) (ℱ : Filtration ι m0) (μ : Measure Ω) : Prop :=
  StronglyAdapted ℱ f ∧ ∀ i j, i ≤ j → μ[f j | ℱ i] =ᵐ[μ] f i

/-- A family of integrable functions `f : ι → Ω → E` is a supermartingale with respect to a
filtration `ℱ` if `f` is strongly adapted with respect to `ℱ` and for all `i ≤ j`,
`μ[f j | ℱ.le i] ≤ᵐ[μ] f i`. -/
def Supermartingale [LE E] (f : ι → Ω → E) (ℱ : Filtration ι m0) (μ : Measure Ω) : Prop :=
  StronglyAdapted ℱ f ∧ (∀ i j, i ≤ j → μ[f j | ℱ i] ≤ᵐ[μ] f i) ∧ ∀ i, Integrable (f i) μ

/-- A family of integrable functions `f : ι → Ω → E` is a submartingale with respect to a
filtration `ℱ` if `f` is strongly adapted with respect to `ℱ` and for all `i ≤ j`,
`f i ≤ᵐ[μ] μ[f j | ℱ.le i]`. -/
def Submartingale [LE E] (f : ι → Ω → E) (ℱ : Filtration ι m0) (μ : Measure Ω) : Prop :=
  StronglyAdapted ℱ f ∧ (∀ i j, i ≤ j → f i ≤ᵐ[μ] μ[f j | ℱ i]) ∧ ∀ i, Integrable (f i) μ

theorem martingale_const (ℱ : Filtration ι m0) (μ : Measure Ω) [IsFiniteMeasure μ] (x : E) :
    Martingale (fun _ _ => x) ℱ μ :=
  ⟨stronglyAdapted_const ℱ _, fun i j _ => by rw [condExp_const (ℱ.le _)]⟩

theorem martingale_const_fun [OrderBot ι] (ℱ : Filtration ι m0) (μ : Measure Ω)
    [SigmaFiniteFiltration μ ℱ]
    {f : Ω → E} (hf : StronglyMeasurable[ℱ ⊥] f) (hfint : Integrable f μ) :
    Martingale (fun _ => f) ℱ μ := by
  refine ⟨fun i => hf.mono <| ℱ.mono bot_le, fun i j _ => ?_⟩
  rw [condExp_of_stronglyMeasurable (ℱ.le _) (hf.mono <| ℱ.mono bot_le) hfint]

variable (E) in
theorem martingale_zero (ℱ : Filtration ι m0) (μ : Measure Ω) : Martingale (0 : ι → Ω → E) ℱ μ :=
  ⟨stronglyAdapted_zero E ℱ, fun i j _ => by simp⟩

namespace Martingale

protected theorem stronglyAdapted (hf : Martingale f ℱ μ) : StronglyAdapted ℱ f :=
  hf.1

protected theorem stronglyMeasurable (hf : Martingale f ℱ μ) (i : ι) :
    StronglyMeasurable[ℱ i] (f i) :=
  hf.stronglyAdapted i

theorem condExp_ae_eq (hf : Martingale f ℱ μ) {i j : ι} (hij : i ≤ j) : μ[f j | ℱ i] =ᵐ[μ] f i :=
  hf.2 i j hij

protected theorem integrable (hf : Martingale f ℱ μ) (i : ι) : Integrable (f i) μ :=
  integrable_condExp.congr (hf.condExp_ae_eq (le_refl i))

theorem setIntegral_eq [SigmaFiniteFiltration μ ℱ] (hf : Martingale f ℱ μ) {i j : ι} (hij : i ≤ j)
    {s : Set Ω} (hs : MeasurableSet[ℱ i] s) : ∫ ω in s, f i ω ∂μ = ∫ ω in s, f j ω ∂μ := by
  rw [← setIntegral_condExp (ℱ.le i) (hf.integrable j) hs]
  refine setIntegral_congr_ae (ℱ.le i s hs) ?_
  filter_upwards [hf.2 i j hij] with _ heq _ using heq.symm

theorem add (hf : Martingale f ℱ μ) (hg : Martingale g ℱ μ) : Martingale (f + g) ℱ μ := by
  refine ⟨hf.stronglyAdapted.add hg.stronglyAdapted, fun i j hij => ?_⟩
  exact (condExp_add (hf.integrable j) (hg.integrable j) _).trans
    ((hf.2 i j hij).add (hg.2 i j hij))

theorem neg (hf : Martingale f ℱ μ) : Martingale (-f) ℱ μ :=
  ⟨hf.stronglyAdapted.neg, fun i j hij => (condExp_neg ..).trans (hf.2 i j hij).neg⟩

theorem sub (hf : Martingale f ℱ μ) (hg : Martingale g ℱ μ) : Martingale (f - g) ℱ μ := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

theorem smul (c : ℝ) (hf : Martingale f ℱ μ) : Martingale (c • f) ℱ μ := by
  refine ⟨hf.stronglyAdapted.smul c, fun i j hij => ?_⟩
  refine (condExp_smul ..).trans ((hf.2 i j hij).mono fun x hx => ?_)
  simp only [Pi.smul_apply, hx]

theorem supermartingale [Preorder E] (hf : Martingale f ℱ μ) : Supermartingale f ℱ μ :=
  ⟨hf.1, fun i j hij => (hf.2 i j hij).le, fun i => hf.integrable i⟩

theorem submartingale [Preorder E] (hf : Martingale f ℱ μ) : Submartingale f ℱ μ :=
  ⟨hf.1, fun i j hij => (hf.2 i j hij).symm.le, fun i => hf.integrable i⟩

end Martingale

theorem martingale_iff [PartialOrder E] :
    Martingale f ℱ μ ↔ Supermartingale f ℱ μ ∧ Submartingale f ℱ μ :=
  ⟨fun hf => ⟨hf.supermartingale, hf.submartingale⟩, fun ⟨hf₁, hf₂⟩ =>
    ⟨hf₁.1, fun i j hij => (hf₁.2.1 i j hij).antisymm (hf₂.2.1 i j hij)⟩⟩

theorem martingale_condExp (f : Ω → E) (ℱ : Filtration ι m0) (μ : Measure Ω)
    [SigmaFiniteFiltration μ ℱ] : Martingale (fun i => μ[f | ℱ i]) ℱ μ :=
  ⟨fun _ => stronglyMeasurable_condExp, fun _ j hij => condExp_condExp_of_le (ℱ.mono hij) (ℱ.le j)⟩

namespace Supermartingale

protected theorem stronglyAdapted [LE E] (hf : Supermartingale f ℱ μ) : StronglyAdapted ℱ f :=
  hf.1

protected theorem stronglyMeasurable [LE E] (hf : Supermartingale f ℱ μ) (i : ι) :
    StronglyMeasurable[ℱ i] (f i) :=
  hf.stronglyAdapted i

protected theorem integrable [LE E] (hf : Supermartingale f ℱ μ) (i : ι) : Integrable (f i) μ :=
  hf.2.2 i

theorem condExp_ae_le [LE E] (hf : Supermartingale f ℱ μ) {i j : ι} (hij : i ≤ j) :
    μ[f j | ℱ i] ≤ᵐ[μ] f i :=
  hf.2.1 i j hij

theorem setIntegral_le [PartialOrder E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
    [ClosedIciTopology E] [SigmaFiniteFiltration μ ℱ] {f : ι → Ω → E} (hf : Supermartingale f ℱ μ)
    {i j : ι} (hij : i ≤ j) {s : Set Ω} (hs : MeasurableSet[ℱ i] s) :
    ∫ ω in s, f j ω ∂μ ≤ ∫ ω in s, f i ω ∂μ := by
  rw [← setIntegral_condExp (ℱ.le i) (hf.integrable j) hs]
  refine setIntegral_mono_ae integrable_condExp.integrableOn (hf.integrable i).integrableOn ?_
  filter_upwards [hf.2.1 i j hij] with _ heq using heq

theorem add [Preorder E] [AddLeftMono E] (hf : Supermartingale f ℱ μ)
    (hg : Supermartingale g ℱ μ) : Supermartingale (f + g) ℱ μ := by
  refine ⟨hf.1.add hg.1, fun i j hij => ?_, fun i => (hf.2.2 i).add (hg.2.2 i)⟩
  refine (condExp_add (hf.integrable j) (hg.integrable j) _).le.trans ?_
  filter_upwards [hf.2.1 i j hij, hg.2.1 i j hij]
  intros
  refine add_le_add ?_ ?_ <;> assumption

theorem add_martingale [Preorder E] [AddLeftMono E]
    (hf : Supermartingale f ℱ μ) (hg : Martingale g ℱ μ) : Supermartingale (f + g) ℱ μ :=
  hf.add hg.supermartingale

theorem neg [Preorder E] [AddLeftMono E] (hf : Supermartingale f ℱ μ) :
    Submartingale (-f) ℱ μ := by
  refine ⟨hf.1.neg, fun i j hij => ?_, fun i => (hf.2.2 i).neg⟩
  refine EventuallyLE.trans ?_ (condExp_neg ..).symm.le
  filter_upwards [hf.2.1 i j hij] with _ _
  simpa

end Supermartingale

namespace Submartingale

protected theorem stronglyAdapted [LE E] (hf : Submartingale f ℱ μ) : StronglyAdapted ℱ f :=
  hf.1

protected theorem stronglyMeasurable [LE E] (hf : Submartingale f ℱ μ) (i : ι) :
    StronglyMeasurable[ℱ i] (f i) :=
  hf.stronglyAdapted i

protected theorem integrable [LE E] (hf : Submartingale f ℱ μ) (i : ι) : Integrable (f i) μ :=
  hf.2.2 i

theorem ae_le_condExp [LE E] (hf : Submartingale f ℱ μ) {i j : ι} (hij : i ≤ j) :
    f i ≤ᵐ[μ] μ[f j | ℱ i] :=
  hf.2.1 i j hij

theorem add [Preorder E] [AddLeftMono E] (hf : Submartingale f ℱ μ)
    (hg : Submartingale g ℱ μ) : Submartingale (f + g) ℱ μ := by
  refine ⟨hf.1.add hg.1, fun i j hij => ?_, fun i => (hf.2.2 i).add (hg.2.2 i)⟩
  refine EventuallyLE.trans ?_ (condExp_add (hf.integrable j) (hg.integrable j) _).symm.le
  filter_upwards [hf.2.1 i j hij, hg.2.1 i j hij]
  intros
  refine add_le_add ?_ ?_ <;> assumption

theorem add_martingale [Preorder E] [AddLeftMono E] (hf : Submartingale f ℱ μ)
    (hg : Martingale g ℱ μ) : Submartingale (f + g) ℱ μ :=
  hf.add hg.submartingale

theorem neg [Preorder E] [AddLeftMono E] (hf : Submartingale f ℱ μ) :
    Supermartingale (-f) ℱ μ := by
  refine ⟨hf.1.neg, fun i j hij => (condExp_neg ..).le.trans ?_, fun i => (hf.2.2 i).neg⟩
  filter_upwards [hf.2.1 i j hij] with _ _
  simpa

/-- The converse of this lemma is `MeasureTheory.submartingale_of_setIntegral_le`. -/
theorem setIntegral_le [PartialOrder E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
    [ClosedIciTopology E] [SigmaFiniteFiltration μ ℱ] {f : ι → Ω → E} (hf : Submartingale f ℱ μ)
    {i j : ι} (hij : i ≤ j) {s : Set Ω} (hs : MeasurableSet[ℱ i] s) :
    ∫ ω in s, f i ω ∂μ ≤ ∫ ω in s, f j ω ∂μ := by
  rw [← neg_le_neg_iff, ← integral_neg, ← integral_neg]
  exact Supermartingale.setIntegral_le hf.neg hij hs

theorem sub_supermartingale [Preorder E] [AddLeftMono E]
    (hf : Submartingale f ℱ μ) (hg : Supermartingale g ℱ μ) : Submartingale (f - g) ℱ μ := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

theorem sub_martingale [Preorder E] [AddLeftMono E] (hf : Submartingale f ℱ μ)
    (hg : Martingale g ℱ μ) : Submartingale (f - g) ℱ μ :=
  hf.sub_supermartingale hg.supermartingale

protected theorem sup [Lattice E] [ContinuousSup E] [HasSolidNorm E] [IsOrderedAddMonoid E]
    [IsOrderedModule ℝ E] {f g : ι → Ω → E} (hf : Submartingale f ℱ μ)
    (hg : Submartingale g ℱ μ) :
    Submartingale (f ⊔ g) ℱ μ := by
  refine ⟨fun i =>
    @StronglyMeasurable.sup _ _ _ _ (ℱ i) _ _ _ (hf.stronglyAdapted i) (hg.stronglyAdapted i),
    fun i j hij => ?_, fun i => Integrable.sup (hf.integrable _) (hg.integrable _)⟩
  refine EventuallyLE.sup_le ?_ ?_
  · exact EventuallyLE.trans (hf.2.1 i j hij)
      (condExp_mono (hf.integrable _) (Integrable.sup (hf.integrable j) (hg.integrable j))
        (Eventually.of_forall fun x => le_sup_left))
  · exact EventuallyLE.trans (hg.2.1 i j hij)
      (condExp_mono (hg.integrable _) (Integrable.sup (hf.integrable j) (hg.integrable j))
        (Eventually.of_forall fun x => le_sup_right))

protected theorem pos [Lattice E] [ContinuousSup E] [HasSolidNorm E] [IsOrderedAddMonoid E]
    [IsOrderedModule ℝ E] {f : ι → Ω → E} (hf : Submartingale f ℱ μ) :
    Submartingale (f⁺) ℱ μ :=
  hf.sup (martingale_zero _ _ _).submartingale

end Submartingale

section Submartingale

theorem submartingale_of_setIntegral_le [SigmaFiniteFiltration μ ℱ]
    {f : ι → Ω → ℝ} (hadp : StronglyAdapted ℱ f)
    (hint : ∀ i, Integrable (f i) μ) (hf : ∀ i j : ι,
      i ≤ j → ∀ s : Set Ω, MeasurableSet[ℱ i] s → ∫ ω in s, f i ω ∂μ ≤ ∫ ω in s, f j ω ∂μ) :
    Submartingale f ℱ μ := by
  refine ⟨hadp, fun i j hij => ?_, hint⟩
  suffices f i ≤ᵐ[μ.trim (ℱ.le i)] μ[f j | ℱ i] by exact ae_le_of_ae_le_trim this
  suffices 0 ≤ᵐ[μ.trim (ℱ.le i)] μ[f j | ℱ i] - f i by
    filter_upwards [this] with x hx
    rwa [← sub_nonneg]
  refine ae_nonneg_of_forall_setIntegral_nonneg
    ((integrable_condExp.sub (hint i)).trim _ (stronglyMeasurable_condExp.sub <| hadp i))
      fun s hs _ => ?_
  specialize hf i j hij s hs
  rwa [← setIntegral_trim _ (stronglyMeasurable_condExp.sub <| hadp i) hs,
    integral_sub' integrable_condExp.integrableOn (hint i).integrableOn, sub_nonneg,
    setIntegral_condExp (ℱ.le i) (hint j) hs]

theorem submartingale_of_condExp_sub_nonneg [PartialOrder E] [IsOrderedAddMonoid E]
    [SigmaFiniteFiltration μ ℱ] {f : ι → Ω → E} (hadp : StronglyAdapted ℱ f)
    (hint : ∀ i, Integrable (f i) μ) (hf : ∀ i j, i ≤ j → 0 ≤ᵐ[μ] μ[f j - f i | ℱ i]) :
    Submartingale f ℱ μ := by
  refine ⟨hadp, fun i j hij => ?_, hint⟩
  rw [← condExp_of_stronglyMeasurable (ℱ.le _) (hadp _) (hint _), ← eventually_sub_nonneg]
  exact EventuallyLE.trans (hf i j hij) (condExp_sub (hint _) (hint _) _).le

theorem Submartingale.condExp_sub_nonneg [PartialOrder E] [IsOrderedAddMonoid E]
    {f : ι → Ω → E} (hf : Submartingale f ℱ μ) {i j : ι}
    (hij : i ≤ j) : 0 ≤ᵐ[μ] μ[f j - f i | ℱ i] := by
  by_cases h : SigmaFinite (μ.trim (ℱ.le i))
  swap; · rw [condExp_of_not_sigmaFinite (ℱ.le i) h]
  refine EventuallyLE.trans ?_ (condExp_sub (hf.integrable _) (hf.integrable _) _).symm.le
  rw [eventually_sub_nonneg,
    condExp_of_stronglyMeasurable (ℱ.le _) (hf.stronglyAdapted _) (hf.integrable _)]
  exact hf.2.1 i j hij

theorem submartingale_iff_condExp_sub_nonneg [PartialOrder E] [IsOrderedAddMonoid E]
    [SigmaFiniteFiltration μ ℱ] {f : ι → Ω → E} :
    Submartingale f ℱ μ ↔
      StronglyAdapted ℱ f ∧ (∀ i, Integrable (f i) μ) ∧ ∀ i j, i ≤ j → 0 ≤ᵐ[μ] μ[f j - f i | ℱ i] :=
  ⟨fun h => ⟨h.stronglyAdapted, h.integrable, fun _ _ => h.condExp_sub_nonneg⟩,
   fun ⟨hadp, hint, h⟩ => submartingale_of_condExp_sub_nonneg hadp hint h⟩

end Submartingale

namespace Supermartingale

theorem sub_submartingale [Preorder E] [AddLeftMono E]
    (hf : Supermartingale f ℱ μ) (hg : Submartingale g ℱ μ) : Supermartingale (f - g) ℱ μ := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

theorem sub_martingale [Preorder E] [AddLeftMono E]
    (hf : Supermartingale f ℱ μ) (hg : Martingale g ℱ μ) : Supermartingale (f - g) ℱ μ :=
  hf.sub_submartingale hg.submartingale

section

variable {F : Type*} [NormedAddCommGroup F] [PartialOrder F] [NormedSpace ℝ F] [CompleteSpace F]
  [IsOrderedModule ℝ F]

theorem smul_nonneg {f : ι → Ω → F} {c : ℝ} (hc : 0 ≤ c) (hf : Supermartingale f ℱ μ) :
    Supermartingale (c • f) ℱ μ := by
  refine ⟨hf.1.smul c, fun i j hij => ?_, fun i => (hf.2.2 i).smul c⟩
  filter_upwards [condExp_smul c (f j) (ℱ i), hf.2.1 i j hij] with ω hω hle
  simpa only [hω, Pi.smul_apply] using smul_le_smul_of_nonneg_left hle hc

theorem smul_nonpos [IsOrderedAddMonoid F] {f : ι → Ω → F} {c : ℝ}
    (hc : c ≤ 0) (hf : Supermartingale f ℱ μ) :
    Submartingale (c • f) ℱ μ := by
  rw [← neg_neg c, neg_smul]
  exact (hf.smul_nonneg <| neg_nonneg.2 hc).neg

end

end Supermartingale

namespace Submartingale

section

variable {F : Type*} [NormedAddCommGroup F] [PartialOrder F] [IsOrderedAddMonoid F]
  [NormedSpace ℝ F] [CompleteSpace F] [IsOrderedModule ℝ F]

theorem smul_nonneg {f : ι → Ω → F} {c : ℝ} (hc : 0 ≤ c) (hf : Submartingale f ℱ μ) :
    Submartingale (c • f) ℱ μ := by
  rw [← neg_neg (c • f), ← smul_neg]
  exact Supermartingale.neg (hf.neg.smul_nonneg hc)

theorem smul_nonpos {f : ι → Ω → F} {c : ℝ} (hc : c ≤ 0) (hf : Submartingale f ℱ μ) :
    Supermartingale (c • f) ℱ μ := by
  rw [← neg_neg c, neg_smul]
  exact (hf.smul_nonneg <| neg_nonneg.2 hc).neg

end

end Submartingale

section Nat

open Order

variable {η : Type*} [LinearOrder η] [LocallyFiniteOrder η] [OrderBot η] [SuccOrder η]
  [IsFiniteMeasure μ] {𝒢 : Filtration η m0} {f : η → Ω → ℝ}

section SubSuper

section OfSetIntegral

theorem submartingale_of_setIntegral_le_succ
    (hadp : StronglyAdapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i, ∀ s : Set Ω, MeasurableSet[𝒢 i] s → ∫ ω in s, f i ω ∂μ ≤ ∫ ω in s, f (succ i) ω ∂μ) :
    Submartingale f 𝒢 μ := by
  refine submartingale_of_setIntegral_le hadp hint fun i j hij s hs => ?_
  have : PredOrder η := LinearLocallyFiniteOrder.predOrder η
  refine todo (P := fun j hij ↦ ∫ (ω : Ω) in s, f i ω ∂μ ≤ ∫ (ω : Ω) in s, f j ω ∂μ) ?_ ?_ j hij
  · simp
  · exact fun j hij h_le ↦ h_le.trans (hf _ s (𝒢.mono hij _ hs))
  -- suffices h_succ : ∀ m, i ≤ m → ∫ ω in s, f i ω ∂μ ≤ ∫ ω in s, f m ω ∂μ →
  --     ∫ ω in s, f i ω ∂μ ≤ ∫ ω in s, f (succ m) ω ∂μ by
  --   by_cases hij_eq : i = j
  --   · rw [hij_eq]
  --   sorry
  -- intro k hk₁ hk₂
  -- exact hk₂.trans (hf _ s (𝒢.mono hk₁ _ hs))

theorem supermartingale_of_setIntegral_succ_le
    (hadp : StronglyAdapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i, ∀ s : Set Ω, MeasurableSet[𝒢 i] s → ∫ ω in s, f (succ i) ω ∂μ ≤ ∫ ω in s, f i ω ∂μ) :
    Supermartingale f 𝒢 μ := by
  rw [← neg_neg f]
  refine (submartingale_of_setIntegral_le_succ hadp.neg (fun i => (hint i).neg) ?_).neg
  simpa only [integral_neg, Pi.neg_apply, neg_le_neg_iff]

end OfSetIntegral

section OfSucc

variable [PartialOrder E] [IsOrderedAddMonoid E] [ClosedIciTopology E] [IsOrderedModule ℝ E]

theorem submartingale_nat (hadp : StronglyAdapted 𝒢 f)
    (hint : ∀ i, Integrable (f i) μ) (hf : ∀ i, f i ≤ᵐ[μ] μ[f (succ i) | 𝒢 i]) :
    Submartingale f 𝒢 μ := by
  refine submartingale_of_setIntegral_le_succ hadp hint fun i s hs => ?_
  have : ∫ ω in s, f (succ i) ω ∂μ = ∫ ω in s, (μ[f (succ i)|𝒢 i]) ω ∂μ :=
    (setIntegral_condExp (𝒢.le i) (hint _) hs).symm
  rw [this]
  exact setIntegral_mono_ae (hint i).integrableOn integrable_condExp.integrableOn (hf i)
  -- refine ⟨hadp, fun i j hij ↦ ?_, hint⟩
  -- induction j, hij using Nat.le_induction with
  -- | base =>
  --   refine ae_of_all _ fun _ ↦ ?_
  --   rw [condExp_of_stronglyMeasurable (𝒢.le i) (hadp i) (hint i)]
  -- | succ k hik hk =>
  --   filter_upwards [hk, condExp_mono (hint k) integrable_condExp (hf k),
  --     𝒢.condExp_condExp (f (k + 1)) hik] with ω hω1 hω2 hω3
  --   grw [hω1, hω2, hω3]

theorem supermartingale_nat (hadp : StronglyAdapted 𝒢 f)
    (hint : ∀ i, Integrable (f i) μ) (hf : ∀ i, μ[f (succ i) | 𝒢 i] ≤ᵐ[μ] f i) :
    Supermartingale f 𝒢 μ := by
  rw [← neg_neg f]
  refine (submartingale_nat hadp.neg (fun i => (hint i).neg) fun i =>
    EventuallyLE.trans ?_ (condExp_neg ..).symm.le).neg
  filter_upwards [hf i] with x hx using neg_le_neg hx

theorem submartingale_of_condExp_sub_nonneg_nat
    (hadp : StronglyAdapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i, 0 ≤ᵐ[μ] μ[f (succ i) - f i | 𝒢 i]) : Submartingale f 𝒢 μ := by
  refine submartingale_nat hadp hint fun i => ?_
  rw [← condExp_of_stronglyMeasurable (𝒢.le _) (hadp _) (hint _), ← eventually_sub_nonneg]
  exact EventuallyLE.trans (hf i) (condExp_sub (hint _) (hint _) _).le

theorem supermartingale_of_condExp_sub_nonneg_nat
    (hadp : StronglyAdapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i, 0 ≤ᵐ[μ] μ[f i - f (succ i) | 𝒢 i]) : Supermartingale f 𝒢 μ := by
  rw [← neg_neg f]
  refine (submartingale_of_condExp_sub_nonneg_nat hadp.neg (fun i => (hint i).neg) ?_).neg
  simpa only [Pi.zero_apply, Pi.neg_apply, neg_sub_neg]

end OfSucc

section Preorder

variable [Preorder E]

omit [IsFiniteMeasure μ] in
-- Note that one cannot use `Submartingale.zero_le_of_predictable` to prove the other two
-- corresponding lemmas without imposing more restrictions to the ordering of `E`
/-- A predictable submartingale is a.e. greater equal than its initial state. -/
theorem Submartingale.zero_le_of_predictable [SigmaFiniteFiltration μ 𝒢] {f : η → Ω → E}
    (hfmgle : Submartingale f 𝒢 μ) (hfadp : StronglyAdapted 𝒢 fun n ↦ f (succ n)) (n : η) :
    f ⊥ ≤ᵐ[μ] f n := by
  have : PredOrder η := LinearLocallyFiniteOrder.predOrder η
  refine todo' (P := fun n ↦ f ⊥ ≤ᵐ[μ] f n) ?_ ?_ n
  · rfl
  · intro k ih
    exact ih.trans ((hfmgle.2.1 k (succ k) (le_succ k)).trans_eq <| Germ.coe_eq.mp <|
    congr_arg Germ.ofFun <| condExp_of_stronglyMeasurable (𝒢.le _) (hfadp _) <| hfmgle.integrable _)

omit [IsFiniteMeasure μ] in
/-- A predictable supermartingale is a.e. less equal than its initial state. -/
theorem Supermartingale.le_zero_of_predictable [SigmaFiniteFiltration μ 𝒢] {f : η → Ω → E}
    (hfmgle : Supermartingale f 𝒢 μ) (hfadp : StronglyAdapted 𝒢 fun n ↦ f (succ n)) (n : η) :
    f n ≤ᵐ[μ] f ⊥ := by
  have : PredOrder η := LinearLocallyFiniteOrder.predOrder η
  refine todo' (P := fun n ↦ f n ≤ᵐ[μ] f ⊥) ?_ ?_ n
  · rfl
  · intro k ih
    exact ((Germ.coe_eq.mp <| congr_arg Germ.ofFun <| condExp_of_stronglyMeasurable (𝒢.le _)
      (hfadp _) <| hfmgle.integrable _).symm.trans_le (hfmgle.2.1 k (succ k) (le_succ k))).trans ih

end Preorder

end SubSuper

theorem martingale_nat (hadp : StronglyAdapted 𝒢 f)
    (hint : ∀ i, Integrable (f i) μ) (hf : ∀ i, f i =ᵐ[μ] μ[f (succ i) | 𝒢 i]) :
    Martingale f 𝒢 μ :=
  martingale_iff.2 ⟨supermartingale_nat hadp hint fun i => (hf i).symm.le,
    submartingale_nat hadp hint fun i => (hf i).le⟩

theorem martingale_of_setIntegral_eq_succ
    (hadp : StronglyAdapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i, ∀ s : Set Ω, MeasurableSet[𝒢 i] s → ∫ ω in s, f i ω ∂μ = ∫ ω in s, f (succ i) ω ∂μ) :
    Martingale f 𝒢 μ :=
  martingale_iff.2 ⟨supermartingale_of_setIntegral_succ_le hadp hint fun i s hs => (hf i s hs).ge,
    submartingale_of_setIntegral_le_succ hadp hint fun i s hs => (hf i s hs).le⟩

theorem martingale_of_condExp_sub_eq_zero_nat
    (hadp : StronglyAdapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i, μ[f (succ i) - f i | 𝒢 i] =ᵐ[μ] 0) : Martingale f 𝒢 μ := by
  refine martingale_iff.2 ⟨supermartingale_of_condExp_sub_nonneg_nat hadp hint fun i => ?_,
    submartingale_of_condExp_sub_nonneg_nat hadp hint fun i => (hf i).symm.le⟩
  rw [← neg_sub]
  refine (EventuallyEq.trans ?_ (condExp_neg ..).symm).le
  filter_upwards [hf i] with x hx
  simpa only [Pi.zero_apply, Pi.neg_apply, zero_eq_neg]

omit [IsFiniteMeasure μ] in
/-- A predictable martingale is a.e. equal to its initial state. -/
theorem Martingale.eq_zero_of_predictable [SigmaFiniteFiltration μ 𝒢] {f : η → Ω → E}
    (hfmgle : Martingale f 𝒢 μ) (hfadp : StronglyAdapted 𝒢 fun n ↦ f (succ n)) (n : η) :
    f n =ᵐ[μ] f ⊥ := by
  have : PredOrder η := LinearLocallyFiniteOrder.predOrder η
  refine todo' (P := fun n ↦ f n =ᵐ[μ] f ⊥) ?_ ?_ n
  · rfl
  · intro k ih
    exact ((Germ.coe_eq.mp (congr_arg Germ.ofFun <| condExp_of_stronglyMeasurable (𝒢.le _) (hfadp _)
      (hfmgle.integrable _))).symm.trans (hfmgle.2 k (succ k) (le_succ k))).trans ih

section IsPredictable

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {𝒢 : Filtration ℕ m0}

omit [IsFiniteMeasure μ]

/-- A predictable submartingale is a.e. greater than or equal to its initial state.

In contrast to the non-primed version, this result requires second countability as
`StronglyAdapted` is defined using strong measurability while `IsPredictable` only provides
measurable. -/
theorem Submartingale.zero_le_of_predictable' [Preorder E] [SigmaFiniteFiltration μ 𝒢]
    {f : ℕ → Ω → E} (hfmgle : Submartingale f 𝒢 μ) (hf : IsPredictable 𝒢 f) (n : ℕ) :
    f 0 ≤ᵐ[μ] f n :=
  zero_le_of_predictable hfmgle (fun _ ↦ (hf.measurable_add_one _).stronglyMeasurable) n

/-- A predictable supermartingale is a.e. less than or equal to its initial state.

In contrast to the non-primed version, this result requires second countability as `StronglyAdapted`
is defined using strong measurability while `IsPredictable` only provides measurable. -/
theorem Supermartingale.le_zero_of_predictable' [Preorder E] [SigmaFiniteFiltration μ 𝒢]
    {f : ℕ → Ω → E} (hfmgle : Supermartingale f 𝒢 μ) (hfadp : IsPredictable 𝒢 f)
    (n : ℕ) : f n ≤ᵐ[μ] f 0 :=
  le_zero_of_predictable hfmgle (fun _ ↦ (hfadp.measurable_add_one _).stronglyMeasurable) n

/-- A predictable martingale is a.e. equal to its initial state.

In contrast to the non-primed version, this result requires second countability as `StronglyAdapted`
is defined using strong measurability while `IsPredictable` only provides measurable. -/
theorem Martingale.eq_zero_of_predictable' [SigmaFiniteFiltration μ 𝒢] {f : ℕ → Ω → E}
    (hfmgle : Martingale f 𝒢 μ) (hfadp : IsPredictable 𝒢 f) (n : ℕ) : f n =ᵐ[μ] f 0 :=
  eq_zero_of_predictable hfmgle (fun _ ↦ (hfadp.measurable_add_one _).stronglyMeasurable) n

end IsPredictable

namespace Submartingale

omit [IsFiniteMeasure μ] [SuccOrder η] in
protected theorem integrable_stoppedValue [LE E] {f : η → Ω → E} (hf : Submartingale f 𝒢 μ)
    {τ : Ω → WithTop η} (hτ : IsStoppingTime 𝒢 τ) {N : η} (hbdd : ∀ ω, τ ω ≤ N) :
    Integrable (stoppedValue f τ) μ :=
  integrable_stoppedValue η hτ hf.integrable hbdd

end Submartingale

section SumSMul

variable [PartialOrder E] [IsOrderedModule ℝ E] [ClosedIciTopology E] [IsOrderedAddMonoid E]

lemma _root_.Finset.sum_Iio_add_sum_Ico {M : Type*} [AddCommMonoid M] (f : η → M) {m n : η}
    (h : m ≤ n) :
    ((∑ k ∈ Finset.Iio m, f k) + ∑ k ∈ Finset.Ico m n, f k) = ∑ k ∈ Finset.Iio n, f k := by
  sorry

lemma _root_.Finset.sum_Ico_eq_sub' {δ : Type*} [AddCommGroup δ] (f : η → δ) {m n : η} (h : m ≤ n) :
    ∑ k ∈ Finset.Ico m n, f k = (∑ k ∈ Finset.Iio n, f k) - ∑ k ∈ Finset.Iio m, f k := by
  sorry

lemma _root_.Finset.sum_Iio_succ_sub_sum {M : Type*} [AddCommGroup M] {f : η → M} (n : η) :
    ((∑ i ∈ Finset.Iio (succ n), f i) - ∑ i ∈ Finset.Iio n, f i) = f n :=
  sorry

lemma _root_.Finset.eq_sum_Iio_sub {G : Type*} [AddCommGroup G] (f : η → G) (n : η) :
    f n = f ⊥ + ∑ i ∈ Finset.Iio n, (f (succ i) - f i) := by
  sorry

theorem Submartingale.sum_mul_sub [NoMaxOrder η] {R : ℝ} {ξ f : η → Ω → ℝ}
    (hf : Submartingale f 𝒢 μ) (hξ : StronglyAdapted 𝒢 ξ) (hbdd : ∀ n ω, ξ n ω ≤ R)
    (hnonneg : ∀ n ω, 0 ≤ ξ n ω) :
    Submartingale (fun n => ∑ k ∈ Finset.Iio n, ξ k * (f (succ k) - f k)) 𝒢 μ := by
  have hξbdd : ∀ i, ∃ C, ∀ ω, |ξ i ω| ≤ C := fun i =>
    ⟨R, fun ω => (abs_of_nonneg (hnonneg i ω)).trans_le (hbdd i ω)⟩
  choose C hC using hξbdd
  have hint : ∀ m, Integrable (∑ k ∈ Finset.Iio m, ξ k * (f (succ k) - f k)) μ := fun m =>
    integrable_finset_sum' _ fun i _ => Integrable.bdd_mul ((hf.integrable _).sub (hf.integrable _))
      hξ.stronglyMeasurable.aestronglyMeasurable (ae_of_all _ (hC _))
  have hadp : StronglyAdapted 𝒢 fun n => ∑ k ∈ Finset.Iio n, ξ k * (f (succ k) - f k) := by
    intro m
    refine Finset.stronglyMeasurable_sum _ fun i hi => ?_
    rw [Finset.mem_Iio] at hi
    exact (hξ.stronglyMeasurable_le hi.le).mul
      ((hf.stronglyAdapted.stronglyMeasurable_le (succ_le_of_lt hi)).sub
        (hf.stronglyAdapted.stronglyMeasurable_le hi.le))
  refine submartingale_of_condExp_sub_nonneg_nat hadp hint fun i => ?_
  simp only [← Finset.sum_Ico_eq_sub' _ (le_succ _)]
  simp only [Finset.Ico_succ_right_eq_Icc, Finset.Icc_self, Finset.sum_singleton]
  exact EventuallyLE.trans (EventuallyLE.mul_nonneg (Eventually.of_forall (hnonneg _))
    (hf.condExp_sub_nonneg (le_succ _))) (condExp_mul_of_stronglyMeasurable_left (hξ _)
    (((hf.integrable _).sub (hf.integrable _)).bdd_mul
      hξ.stronglyMeasurable.aestronglyMeasurable (ae_of_all _ (hC _)))
    ((hf.integrable _).sub (hf.integrable _))).symm.le

theorem Submartingale.sum_mul_sub_nat {R : ℝ} {ξ f : ℕ → Ω → ℝ} {𝒢 : Filtration ℕ m0}
    (hf : Submartingale f 𝒢 μ) (hξ : StronglyAdapted 𝒢 ξ) (hbdd : ∀ n ω, ξ n ω ≤ R)
    (hnonneg : ∀ n ω, 0 ≤ ξ n ω) :
    Submartingale (fun n => ∑ k ∈ Finset.range n, ξ k * (f (k + 1) - f k)) 𝒢 μ := by
  convert hf.sum_mul_sub hξ (fun _ => hbdd _) fun _ => hnonneg _ using 3 with n
  rw [Nat.Iio_eq_range]

/-- Given a discrete submartingale `f` and a predictable process `ξ` (i.e. `ξ (n + 1)` is adapted)
the process defined by `fun n => ∑ k ∈ Finset.range n, ξ (k + 1) * (f (k + 1) - f k)` is also a
submartingale. -/
theorem Submartingale.sum_mul_sub' [NoMaxOrder η] {R : ℝ} {ξ f : η → Ω → ℝ}
    (hf : Submartingale f 𝒢 μ) (hξ : StronglyAdapted 𝒢 fun n => ξ (succ n))
    (hbdd : ∀ n ω, ξ n ω ≤ R) (hnonneg : ∀ n ω, 0 ≤ ξ n ω) :
    Submartingale (fun n => ∑ k ∈ Finset.Iio n, ξ (succ k) * (f (succ k) - f k)) 𝒢 μ :=
  hf.sum_mul_sub hξ (fun _ => hbdd _) fun _ => hnonneg _

/-- Given a discrete submartingale `f` and a predictable process `ξ` (i.e. `ξ (n + 1)` is adapted)
the process defined by `fun n => ∑ k ∈ Finset.range n, ξ (k + 1) * (f (k + 1) - f k)` is also a
submartingale. -/
theorem Submartingale.sum_mul_sub_nat' {R : ℝ} {ξ f : ℕ → Ω → ℝ} {𝒢 : Filtration ℕ m0}
    (hf : Submartingale f 𝒢 μ) (hξ : StronglyAdapted 𝒢 fun n => ξ (n + 1)) (hbdd : ∀ n ω, ξ n ω ≤ R)
    (hnonneg : ∀ n ω, 0 ≤ ξ n ω) :
    Submartingale (fun n => ∑ k ∈ Finset.range n, ξ (k + 1) * (f (k + 1) - f k)) 𝒢 μ := by
  convert hf.sum_mul_sub' hξ (fun _ => hbdd _) fun _ => hnonneg _ using 3 with n
  rw [Nat.Iio_eq_range]

end SumSMul

end Nat

end MeasureTheory
