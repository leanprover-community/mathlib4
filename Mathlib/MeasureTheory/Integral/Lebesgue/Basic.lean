/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
import Mathlib.MeasureTheory.Function.SimpleFunc

/-!
# Lower Lebesgue integral for `ℝ≥0∞`-valued functions

We define the lower Lebesgue integral of an `ℝ≥0∞`-valued function.

## Notation

We introduce the following notation for the lower Lebesgue integral of a function `f : α → ℝ≥0∞`.

* `∫⁻ x, f x ∂μ`: integral of a function `f : α → ℝ≥0∞` with respect to a measure `μ`;
* `∫⁻ x, f x`: integral of a function `f : α → ℝ≥0∞` with respect to the canonical measure
  `volume` on `α`;
* `∫⁻ x in s, f x ∂μ`: integral of a function `f : α → ℝ≥0∞` over a set `s` with respect
  to a measure `μ`, defined as `∫⁻ x, f x ∂(μ.restrict s)`;
* `∫⁻ x in s, f x`: integral of a function `f : α → ℝ≥0∞` over a set `s` with respect
  to the canonical measure `volume`, defined as `∫⁻ x, f x ∂(volume.restrict s)`.
-/

assert_not_exists Basis Norm MeasureTheory.MeasurePreserving MeasureTheory.Measure.dirac

open Set hiding restrict restrict_apply

open Filter ENNReal Topology NNReal

namespace MeasureTheory

local infixr:25 " →ₛ " => SimpleFunc

variable {α β γ : Type*}

open SimpleFunc

variable {m : MeasurableSpace α} {μ ν : Measure α} {s : Set α}

/-- The **lower Lebesgue integral** of a function `f` with respect to a measure `μ`. -/
noncomputable irreducible_def lintegral (μ : Measure α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (g : α →ₛ ℝ≥0∞) (_ : ⇑g ≤ f), g.lintegral μ

/-! In the notation for integrals, an expression like `∫⁻ x, g ‖x‖ ∂μ` will not be parsed correctly,
  and needs parentheses. We do not set the binding power of `r` to `0`, because then
  `∫⁻ x, f x = 0` will be parsed incorrectly. -/

@[inherit_doc MeasureTheory.lintegral]
notation3 "∫⁻ "(...)", "r:60:(scoped f => f)" ∂"μ:70 => lintegral μ r

@[inherit_doc MeasureTheory.lintegral]
notation3 "∫⁻ "(...)", "r:60:(scoped f => lintegral volume f) => r

@[inherit_doc MeasureTheory.lintegral]
notation3"∫⁻ "(...)" in "s", "r:60:(scoped f => f)" ∂"μ:70 => lintegral (Measure.restrict μ s) r

@[inherit_doc MeasureTheory.lintegral]
notation3"∫⁻ "(...)" in "s", "r:60:(scoped f => lintegral (Measure.restrict volume s) f) => r

theorem SimpleFunc.lintegral_eq_lintegral {m : MeasurableSpace α} (f : α →ₛ ℝ≥0∞) (μ : Measure α) :
    ∫⁻ a, f a ∂μ = f.lintegral μ := by
  rw [MeasureTheory.lintegral]
  exact le_antisymm (iSup₂_le fun g hg => lintegral_mono hg <| le_rfl)
    (le_iSup₂_of_le f le_rfl le_rfl)

@[gcongr, mono]
theorem lintegral_mono' {m : MeasurableSpace α} ⦃μ ν : Measure α⦄ (hμν : μ ≤ ν) ⦃f g : α → ℝ≥0∞⦄
    (hfg : f ≤ g) : ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂ν := by
  rw [lintegral, lintegral]
  exact iSup_mono fun φ => iSup_mono' fun hφ => ⟨le_trans hφ hfg, lintegral_mono (le_refl φ) hμν⟩

-- version where `hfg` is an explicit forall, so that `@[gcongr]` can recognize it
@[gcongr] theorem lintegral_mono_fn' ⦃f g : α → ℝ≥0∞⦄ (hfg : ∀ x, f x ≤ g x) (h2 : μ ≤ ν) :
    ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂ν :=
  lintegral_mono' h2 hfg

theorem lintegral_mono ⦃f g : α → ℝ≥0∞⦄ (hfg : f ≤ g) : ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂μ :=
  lintegral_mono' (le_refl μ) hfg

-- version where `hfg` is an explicit forall, so that `@[gcongr]` can recognize it
@[gcongr] theorem lintegral_mono_fn ⦃f g : α → ℝ≥0∞⦄ (hfg : ∀ x, f x ≤ g x) :
    ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂μ :=
  lintegral_mono hfg

theorem lintegral_mono_nnreal {f g : α → ℝ≥0} (h : f ≤ g) : ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂μ :=
  lintegral_mono fun a => ENNReal.coe_le_coe.2 (h a)

theorem iSup_lintegral_measurable_le_eq_lintegral (f : α → ℝ≥0∞) :
    ⨆ (g : α → ℝ≥0∞) (_ : Measurable g) (_ : g ≤ f), ∫⁻ a, g a ∂μ = ∫⁻ a, f a ∂μ := by
  apply le_antisymm
  · exact iSup_le fun i => iSup_le fun _ => iSup_le fun h'i => lintegral_mono h'i
  · rw [lintegral]
    refine iSup₂_le fun i hi => le_iSup₂_of_le i i.measurable <| le_iSup_of_le hi ?_
    exact le_of_eq (i.lintegral_eq_lintegral _).symm

theorem lintegral_mono_set {_ : MeasurableSpace α} ⦃μ : Measure α⦄ {s t : Set α} {f : α → ℝ≥0∞}
    (hst : s ⊆ t) : ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in t, f x ∂μ :=
  lintegral_mono' (Measure.restrict_mono hst (le_refl μ)) (le_refl f)

theorem lintegral_mono_set' {_ : MeasurableSpace α} ⦃μ : Measure α⦄ {s t : Set α} {f : α → ℝ≥0∞}
    (hst : s ≤ᵐ[μ] t) : ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in t, f x ∂μ :=
  lintegral_mono' (Measure.restrict_mono' hst (le_refl μ)) (le_refl f)

theorem monotone_lintegral {_ : MeasurableSpace α} (μ : Measure α) : Monotone (lintegral μ) :=
  lintegral_mono

@[simp]
theorem lintegral_const (c : ℝ≥0∞) : ∫⁻ _, c ∂μ = c * μ univ := by
  rw [← SimpleFunc.const_lintegral, ← SimpleFunc.lintegral_eq_lintegral, SimpleFunc.coe_const]
  rfl

theorem lintegral_zero : ∫⁻ _ : α, 0 ∂μ = 0 := by simp

theorem lintegral_zero_fun : lintegral μ (0 : α → ℝ≥0∞) = 0 :=
  lintegral_zero

theorem lintegral_one : ∫⁻ _, (1 : ℝ≥0∞) ∂μ = μ univ := by rw [lintegral_const, one_mul]

theorem setLIntegral_const (s : Set α) (c : ℝ≥0∞) : ∫⁻ _ in s, c ∂μ = c * μ s := by
  rw [lintegral_const, Measure.restrict_apply_univ]

theorem setLIntegral_one (s) : ∫⁻ _ in s, 1 ∂μ = μ s := by rw [setLIntegral_const, one_mul]

variable (μ) in
/-- For any function `f : α → ℝ≥0∞`, there exists a measurable function `g ≤ f` with the same
integral. -/
theorem exists_measurable_le_lintegral_eq (f : α → ℝ≥0∞) :
    ∃ g : α → ℝ≥0∞, Measurable g ∧ g ≤ f ∧ ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ := by
  rcases eq_or_ne (∫⁻ a, f a ∂μ) 0 with h₀ | h₀
  · exact ⟨0, measurable_zero, zero_le f, h₀.trans lintegral_zero.symm⟩
  rcases exists_seq_strictMono_tendsto' h₀.bot_lt with ⟨L, _, hLf, hL_tendsto⟩
  have : ∀ n, ∃ g : α → ℝ≥0∞, Measurable g ∧ g ≤ f ∧ L n < ∫⁻ a, g a ∂μ := by
    intro n
    simpa only [← iSup_lintegral_measurable_le_eq_lintegral f, lt_iSup_iff, exists_prop] using
      (hLf n).2
  choose g hgm hgf hLg using this
  refine
    ⟨fun x => ⨆ n, g n x, .iSup hgm, fun x => iSup_le fun n => hgf n x, le_antisymm ?_ ?_⟩
  · refine le_of_tendsto' hL_tendsto fun n => (hLg n).le.trans <| lintegral_mono fun x => ?_
    exact le_iSup (fun n => g n x) n
  · exact lintegral_mono fun x => iSup_le fun n => hgf n x

/-- `∫⁻ a in s, f a ∂μ` is defined as the supremum of integrals of simple functions
`φ : α →ₛ ℝ≥0∞` such that `φ ≤ f`. This lemma says that it suffices to take
functions `φ : α →ₛ ℝ≥0`. -/
theorem lintegral_eq_nnreal {m : MeasurableSpace α} (f : α → ℝ≥0∞) (μ : Measure α) :
    ∫⁻ a, f a ∂μ =
      ⨆ (φ : α →ₛ ℝ≥0) (_ : ∀ x, ↑(φ x) ≤ f x), (φ.map ((↑) : ℝ≥0 → ℝ≥0∞)).lintegral μ := by
  rw [lintegral]
  refine
    le_antisymm (iSup₂_le fun φ hφ ↦ ?_) (iSup_mono' fun φ ↦ ⟨φ.map ((↑) : ℝ≥0 → ℝ≥0∞), le_rfl⟩)
  by_cases h : ∀ᵐ a ∂μ, φ a ≠ ∞
  · let ψ := φ.map ENNReal.toNNReal
    replace h : ψ.map ((↑) : ℝ≥0 → ℝ≥0∞) =ᵐ[μ] φ := h.mono fun a => ENNReal.coe_toNNReal
    have : ∀ x, ↑(ψ x) ≤ f x := fun x => le_trans ENNReal.coe_toNNReal_le_self (hφ x)
    exact le_iSup₂_of_le (φ.map ENNReal.toNNReal) this (ge_of_eq <| lintegral_congr h)
  · have h_meas : μ (φ ⁻¹' {∞}) ≠ 0 := mt measure_zero_iff_ae_not_mem.1 h
    refine le_trans le_top (ge_of_eq <| (iSup_eq_top _).2 fun b hb => ?_)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, b < n * μ (φ ⁻¹' {∞}) := exists_nat_mul_gt h_meas (ne_of_lt hb)
    use (const α (n : ℝ≥0)).restrict (φ ⁻¹' {∞})
    simp only [lt_iSup_iff, exists_prop, coe_restrict, φ.measurableSet_preimage, coe_const,
      ENNReal.coe_indicator, map_coe_ennreal_restrict, SimpleFunc.map_const, ENNReal.coe_natCast,
      restrict_const_lintegral]
    refine ⟨indicator_le fun x hx => le_trans ?_ (hφ _), hn⟩
    simp only [mem_preimage, mem_singleton_iff] at hx
    simp only [hx, le_top]

theorem exists_simpleFunc_forall_lintegral_sub_lt_of_pos {f : α → ℝ≥0∞} (h : ∫⁻ x, f x ∂μ ≠ ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ φ : α →ₛ ℝ≥0,
      (∀ x, ↑(φ x) ≤ f x) ∧
        ∀ ψ : α →ₛ ℝ≥0, (∀ x, ↑(ψ x) ≤ f x) → (map (↑) (ψ - φ)).lintegral μ < ε := by
  rw [lintegral_eq_nnreal] at h
  have := ENNReal.lt_add_right h hε
  erw [ENNReal.biSup_add] at this <;> [skip; exact ⟨0, fun x => zero_le _⟩]
  simp_rw [lt_iSup_iff, iSup_lt_iff, iSup_le_iff] at this
  rcases this with ⟨φ, hle : ∀ x, ↑(φ x) ≤ f x, b, hbφ, hb⟩
  refine ⟨φ, hle, fun ψ hψ => ?_⟩
  have : (map (↑) φ).lintegral μ ≠ ∞ := ne_top_of_le_ne_top h (by exact le_iSup₂ (α := ℝ≥0∞) φ hle)
  rw [← ENNReal.add_lt_add_iff_left this, ← add_lintegral, ← SimpleFunc.map_add @ENNReal.coe_add]
  refine (hb _ fun x => le_trans ?_ (max_le (hle x) (hψ x))).trans_lt hbφ
  norm_cast
  simp only [add_apply, sub_apply, add_tsub_eq_max]
  rfl

theorem iSup_lintegral_le {ι : Sort*} (f : ι → α → ℝ≥0∞) :
    ⨆ i, ∫⁻ a, f i a ∂μ ≤ ∫⁻ a, ⨆ i, f i a ∂μ := by
  simp only [← iSup_apply]
  exact (monotone_lintegral μ).le_map_iSup

theorem iSup₂_lintegral_le {ι : Sort*} {ι' : ι → Sort*} (f : ∀ i, ι' i → α → ℝ≥0∞) :
    ⨆ (i) (j), ∫⁻ a, f i j a ∂μ ≤ ∫⁻ a, ⨆ (i) (j), f i j a ∂μ := by
  convert (monotone_lintegral μ).le_map_iSup₂ f with a
  simp only [iSup_apply]

theorem le_iInf_lintegral {ι : Sort*} (f : ι → α → ℝ≥0∞) :
    ∫⁻ a, ⨅ i, f i a ∂μ ≤ ⨅ i, ∫⁻ a, f i a ∂μ := by
  simp only [← iInf_apply]
  exact (monotone_lintegral μ).map_iInf_le

theorem le_iInf₂_lintegral {ι : Sort*} {ι' : ι → Sort*} (f : ∀ i, ι' i → α → ℝ≥0∞) :
    ∫⁻ a, ⨅ (i) (h : ι' i), f i h a ∂μ ≤ ⨅ (i) (h : ι' i), ∫⁻ a, f i h a ∂μ := by
  convert (monotone_lintegral μ).map_iInf₂_le f with a
  simp only [iInf_apply]

theorem lintegral_mono_ae {f g : α → ℝ≥0∞} (h : ∀ᵐ a ∂μ, f a ≤ g a) :
    ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂μ := by
  rcases exists_measurable_superset_of_null h with ⟨t, hts, ht, ht0⟩
  have : ∀ᵐ x ∂μ, x ∉ t := measure_zero_iff_ae_not_mem.1 ht0
  rw [lintegral, lintegral]
  refine iSup₂_le fun s hfs ↦ le_iSup₂_of_le (s.restrict tᶜ) ?_ ?_
  · intro a
    by_cases h : a ∈ t <;>
      simp only [restrict_apply s ht.compl, mem_compl_iff, h, not_true, not_false_eq_true,
        indicator_of_not_mem, zero_le, not_false_eq_true, indicator_of_mem]
    exact le_trans (hfs a) (by_contradiction fun hnfg => h (hts hnfg))
  · refine le_of_eq (SimpleFunc.lintegral_congr <| this.mono fun a hnt => ?_)
    by_cases hat : a ∈ t <;> simp only [restrict_apply s ht.compl, mem_compl_iff, hat, not_true,
      not_false_eq_true, indicator_of_not_mem, not_false_eq_true, indicator_of_mem]
    exact (hnt hat).elim

/-- Lebesgue integral over a set is monotone in function.

This version assumes that the upper estimate is an a.e. measurable function
and the estimate holds a.e. on the set.
See also `setLIntegral_mono_ae'` for a version that assumes measurability of the set
but assumes no regularity of either function. -/
theorem setLIntegral_mono_ae {s : Set α} {f g : α → ℝ≥0∞} (hg : AEMeasurable g (μ.restrict s))
    (hfg : ∀ᵐ x ∂μ, x ∈ s → f x ≤ g x) : ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in s, g x ∂μ := by
  rcases exists_measurable_le_lintegral_eq (μ.restrict s) f with ⟨f', hf'm, hle, hf'⟩
  rw [hf']
  apply lintegral_mono_ae
  rw [ae_restrict_iff₀]
  · exact hfg.mono fun x hx hxs ↦ (hle x).trans (hx hxs)
  · exact nullMeasurableSet_le hf'm.aemeasurable hg

theorem setLIntegral_mono {s : Set α} {f g : α → ℝ≥0∞} (hg : Measurable g)
    (hfg : ∀ x ∈ s, f x ≤ g x) : ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in s, g x ∂μ :=
  setLIntegral_mono_ae hg.aemeasurable (ae_of_all _ hfg)

theorem setLIntegral_mono_ae' {s : Set α} {f g : α → ℝ≥0∞} (hs : MeasurableSet s)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → f x ≤ g x) : ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in s, g x ∂μ :=
  lintegral_mono_ae <| (ae_restrict_iff' hs).2 hfg

theorem setLIntegral_mono' {s : Set α} {f g : α → ℝ≥0∞} (hs : MeasurableSet s)
    (hfg : ∀ x ∈ s, f x ≤ g x) : ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in s, g x ∂μ :=
  setLIntegral_mono_ae' hs (ae_of_all _ hfg)

theorem setLIntegral_le_lintegral (s : Set α) (f : α → ℝ≥0∞) :
    ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x, f x ∂μ :=
  lintegral_mono' Measure.restrict_le_self le_rfl

theorem lintegral_congr_ae {f g : α → ℝ≥0∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ :=
  le_antisymm (lintegral_mono_ae <| h.le) (lintegral_mono_ae <| h.symm.le)

theorem lintegral_congr {f g : α → ℝ≥0∞} (h : ∀ a, f a = g a) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ := by
  simp only [h]

theorem setLIntegral_congr {f : α → ℝ≥0∞} {s t : Set α} (h : s =ᵐ[μ] t) :
    ∫⁻ x in s, f x ∂μ = ∫⁻ x in t, f x ∂μ := by rw [Measure.restrict_congr_set h]

theorem setLIntegral_congr_fun {f g : α → ℝ≥0∞} {s : Set α} (hs : MeasurableSet s)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → f x = g x) : ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ := by
  rw [lintegral_congr_ae]
  rw [EventuallyEq]
  rwa [ae_restrict_iff' hs]

section

/-- The Lebesgue integral is zero iff the function is a.e. zero.

The measurability assumption is necessary, otherwise there are counterexamples: for instance, the
conclusion fails if `f` is the characteristic function of a Vitali set. -/
@[simp]
theorem lintegral_eq_zero_iff' {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0 := by
  -- The proof implicitly uses Markov's inequality,
  -- but it has been inlined for the sake of imports
  refine ⟨fun h ↦ ?_, fun h ↦ (lintegral_congr_ae h).trans lintegral_zero⟩
  have meas_levels_0 : ∀ ε > 0, μ { x | ε ≤ f x } = 0 := fun ε εpos ↦ by
    by_contra! h'; rw [← zero_lt_iff] at h'
    refine ((mul_pos_iff.mpr ⟨εpos, h'⟩).trans_le ?_).ne' h
    calc
      _ ≥ ∫⁻ a in {x | ε ≤ f x}, f a ∂μ := setLIntegral_le_lintegral _ _
      _ ≥ ∫⁻ _ in {x | ε ≤ f x}, ε ∂μ :=
        setLIntegral_mono_ae hf.restrict (ae_of_all μ fun _ ↦ id)
      _ = _ := setLIntegral_const _ _
  obtain ⟨u, -, bu, tu⟩ := exists_seq_strictAnti_tendsto' (α := ℝ≥0∞) zero_lt_one
  have u_union : {x | f x ≠ 0} = ⋃ n, {x | u n ≤ f x} := by
    ext x; rw [mem_iUnion, mem_setOf_eq, ← zero_lt_iff]
    rw [ENNReal.tendsto_atTop_zero] at tu
    constructor <;> intro h'
    · obtain ⟨n, hn⟩ := tu _ h'; use n, hn _ le_rfl
    · obtain ⟨n, hn⟩ := h'; exact (bu n).1.trans_le hn
  have res := measure_iUnion_null_iff.mpr fun n ↦ meas_levels_0 _ (bu n).1
  rwa [← u_union] at res

/-- The measurability assumption is necessary, otherwise there are counterexamples: for instance,
the conclusion fails if `f` is the characteristic function of a Vitali set. -/
@[simp]
theorem lintegral_eq_zero_iff {f : α → ℝ≥0∞} (hf : Measurable f) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0 :=
  lintegral_eq_zero_iff' hf.aemeasurable

/-- The measurability assumption is necessary, otherwise there are counterexamples: for instance,
the conclusion fails if `s = univ` and `f` is the characteristic function of a Vitali set. -/
theorem setLIntegral_eq_zero_iff' {s : Set α} (hs : MeasurableSet s)
    {f : α → ℝ≥0∞} (hf : AEMeasurable f (μ.restrict s)) :
    ∫⁻ a in s, f a ∂μ = 0 ↔ ∀ᵐ x ∂μ, x ∈ s → f x = 0 :=
  (lintegral_eq_zero_iff' hf).trans (ae_restrict_iff' hs)

theorem setLIntegral_eq_zero_iff {s : Set α} (hs : MeasurableSet s) {f : α → ℝ≥0∞}
    (hf : Measurable f) : ∫⁻ a in s, f a ∂μ = 0 ↔ ∀ᵐ x ∂μ, x ∈ s → f x = 0 :=
  setLIntegral_eq_zero_iff' hs hf.aemeasurable

theorem lintegral_pos_iff_support {f : α → ℝ≥0∞} (hf : Measurable f) :
    (0 < ∫⁻ a, f a ∂μ) ↔ 0 < μ (Function.support f) := by
  simp [pos_iff_ne_zero, hf, Filter.EventuallyEq, ae_iff, Function.support]

theorem setLIntegral_pos_iff {f : α → ℝ≥0∞} (hf : Measurable f) {s : Set α} :
    0 < ∫⁻ a in s, f a ∂μ ↔ 0 < μ (Function.support f ∩ s) := by
  rw [lintegral_pos_iff_support hf, Measure.restrict_apply (measurableSet_support hf)]

@[deprecated (since := "2025-04-22")] alias setLintegral_pos_iff := setLIntegral_pos_iff

end

/-- If `f` has finite integral, then `∫⁻ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. This lemma states this fact in terms of `ε` and `δ`. -/
theorem exists_pos_setLIntegral_lt_of_measure_lt {f : α → ℝ≥0∞} (h : ∫⁻ x, f x ∂μ ≠ ∞) {ε : ℝ≥0∞}
    (hε : ε ≠ 0) : ∃ δ > 0, ∀ s, μ s < δ → ∫⁻ x in s, f x ∂μ < ε := by
  rcases exists_between (pos_iff_ne_zero.mpr hε) with ⟨ε₂, hε₂0, hε₂ε⟩
  rcases exists_between hε₂0 with ⟨ε₁, hε₁0, hε₁₂⟩
  rcases exists_simpleFunc_forall_lintegral_sub_lt_of_pos h hε₁0.ne' with ⟨φ, _, hφ⟩
  rcases φ.exists_forall_le with ⟨C, hC⟩
  use (ε₂ - ε₁) / C, ENNReal.div_pos_iff.2 ⟨(tsub_pos_iff_lt.2 hε₁₂).ne', ENNReal.coe_ne_top⟩
  refine fun s hs => lt_of_le_of_lt ?_ hε₂ε
  simp only [lintegral_eq_nnreal, iSup_le_iff]
  intro ψ hψ
  calc
    (map (↑) ψ).lintegral (μ.restrict s) ≤
        (map (↑) φ).lintegral (μ.restrict s) + (map (↑) (ψ - φ)).lintegral (μ.restrict s) := by
      rw [← SimpleFunc.add_lintegral, ← SimpleFunc.map_add @ENNReal.coe_add]
      refine SimpleFunc.lintegral_mono (fun x => ?_) le_rfl
      simp only [add_tsub_eq_max, le_max_right, coe_map, Function.comp_apply, SimpleFunc.coe_add,
        SimpleFunc.coe_sub, Pi.add_apply, Pi.sub_apply, ENNReal.coe_max (φ x) (ψ x)]
    _ ≤ (map (↑) φ).lintegral (μ.restrict s) + ε₁ := by
      gcongr
      refine le_trans ?_ (hφ _ hψ).le
      exact SimpleFunc.lintegral_mono le_rfl Measure.restrict_le_self
    _ ≤ (SimpleFunc.const α (C : ℝ≥0∞)).lintegral (μ.restrict s) + ε₁ := by
      gcongr
      exact fun x ↦ ENNReal.coe_le_coe.2 (hC x)
    _ = C * μ s + ε₁ := by
      simp only [← SimpleFunc.lintegral_eq_lintegral, coe_const, lintegral_const,
        Measure.restrict_apply, MeasurableSet.univ, univ_inter, Function.const]
    _ ≤ C * ((ε₂ - ε₁) / C) + ε₁ := by gcongr
    _ ≤ ε₂ - ε₁ + ε₁ := by gcongr; apply mul_div_le
    _ = ε₂ := tsub_add_cancel_of_le hε₁₂.le

/-- If `f` has finite integral, then `∫⁻ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. -/
theorem tendsto_setLIntegral_zero {ι} {f : α → ℝ≥0∞} (h : ∫⁻ x, f x ∂μ ≠ ∞) {l : Filter ι}
    {s : ι → Set α} (hl : Tendsto (μ ∘ s) l (𝓝 0)) :
    Tendsto (fun i => ∫⁻ x in s i, f x ∂μ) l (𝓝 0) := by
  simp only [ENNReal.nhds_zero, tendsto_iInf, tendsto_principal, mem_Iio,
    ← pos_iff_ne_zero] at hl ⊢
  intro ε ε0
  rcases exists_pos_setLIntegral_lt_of_measure_lt h ε0.ne' with ⟨δ, δ0, hδ⟩
  exact (hl δ δ0).mono fun i => hδ _

@[simp]
theorem lintegral_smul_measure {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (c : R) (f : α → ℝ≥0∞) : ∫⁻ a, f a ∂c • μ = c • ∫⁻ a, f a ∂μ := by
  simp only [lintegral, iSup_subtype', SimpleFunc.lintegral_smul, ENNReal.smul_iSup]

lemma setLIntegral_smul_measure {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (c : R) (f : α → ℝ≥0∞) (s : Set α) :
    ∫⁻ a in s, f a ∂(c • μ) = c • ∫⁻ a in s, f a ∂μ := by
  rw [Measure.restrict_smul, lintegral_smul_measure]

@[simp]
theorem lintegral_zero_measure {m : MeasurableSpace α} (f : α → ℝ≥0∞) :
    ∫⁻ a, f a ∂(0 : Measure α) = 0 := by
  simp [lintegral]

@[simp]
theorem lintegral_add_measure (f : α → ℝ≥0∞) (μ ν : Measure α) :
    ∫⁻ a, f a ∂(μ + ν) = ∫⁻ a, f a ∂μ + ∫⁻ a, f a ∂ν := by
  simp only [lintegral, SimpleFunc.lintegral_add, iSup_subtype']
  refine (ENNReal.iSup_add_iSup ?_).symm
  rintro ⟨φ, hφ⟩ ⟨ψ, hψ⟩
  refine ⟨⟨φ ⊔ ψ, sup_le hφ hψ⟩, ?_⟩
  apply_rules [add_le_add, SimpleFunc.lintegral_mono, le_rfl] -- TODO: use `gcongr`
  exacts [le_sup_left, le_sup_right]

@[simp]
theorem lintegral_finset_sum_measure {ι} (s : Finset ι) (f : α → ℝ≥0∞) (μ : ι → Measure α) :
    ∫⁻ a, f a ∂(∑ i ∈ s, μ i) = ∑ i ∈ s, ∫⁻ a, f a ∂μ i :=
  let F : Measure α →+ ℝ≥0∞ :=
    { toFun := (lintegral · f),
      map_zero' := lintegral_zero_measure f,
      map_add' := lintegral_add_measure f }
  map_sum F μ s

@[simp]
theorem lintegral_sum_measure {m : MeasurableSpace α} {ι} (f : α → ℝ≥0∞) (μ : ι → Measure α) :
    ∫⁻ a, f a ∂Measure.sum μ = ∑' i, ∫⁻ a, f a ∂μ i := by
  simp_rw [ENNReal.tsum_eq_iSup_sum, ← lintegral_finset_sum_measure,
    lintegral, SimpleFunc.lintegral_sum, ENNReal.tsum_eq_iSup_sum,
    SimpleFunc.lintegral_finset_sum, iSup_comm (ι := Finset ι)]

theorem hasSum_lintegral_measure {ι} {_ : MeasurableSpace α} (f : α → ℝ≥0∞) (μ : ι → Measure α) :
    HasSum (fun i => ∫⁻ a, f a ∂μ i) (∫⁻ a, f a ∂Measure.sum μ) :=
  (lintegral_sum_measure f μ).symm ▸ ENNReal.summable.hasSum

@[simp]
theorem lintegral_of_isEmpty {α} [MeasurableSpace α] [IsEmpty α] (μ : Measure α) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = 0 := by
  have : Subsingleton (Measure α) := inferInstance
  convert lintegral_zero_measure f

theorem setLIntegral_empty (f : α → ℝ≥0∞) : ∫⁻ x in ∅, f x ∂μ = 0 := by
  rw [Measure.restrict_empty, lintegral_zero_measure]

theorem setLIntegral_univ (f : α → ℝ≥0∞) : ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ := by
  rw [Measure.restrict_univ]

theorem setLIntegral_measure_zero (s : Set α) (f : α → ℝ≥0∞) (hs' : μ s = 0) :
    ∫⁻ x in s, f x ∂μ = 0 := by
  convert lintegral_zero_measure _
  exact Measure.restrict_eq_zero.2 hs'

-- TODO: Need a better way of rewriting inside of an integral
theorem lintegral_rw₁ {f f' : α → β} (h : f =ᵐ[μ] f') (g : β → ℝ≥0∞) :
    ∫⁻ a, g (f a) ∂μ = ∫⁻ a, g (f' a) ∂μ :=
  lintegral_congr_ae <| h.mono fun a h => by dsimp only; rw [h]

-- TODO: Need a better way of rewriting inside of an integral
theorem lintegral_rw₂ {f₁ f₁' : α → β} {f₂ f₂' : α → γ} (h₁ : f₁ =ᵐ[μ] f₁') (h₂ : f₂ =ᵐ[μ] f₂')
    (g : β → γ → ℝ≥0∞) : ∫⁻ a, g (f₁ a) (f₂ a) ∂μ = ∫⁻ a, g (f₁' a) (f₂' a) ∂μ :=
  lintegral_congr_ae <| h₁.mp <| h₂.mono fun _ h₂ h₁ => by dsimp only; rw [h₁, h₂]

theorem lintegral_indicator_le (f : α → ℝ≥0∞) (s : Set α) :
    ∫⁻ a, s.indicator f a ∂μ ≤ ∫⁻ a in s, f a ∂μ := by
  simp only [lintegral]
  apply iSup_le (fun g ↦ (iSup_le (fun hg ↦ ?_)))
  have : g ≤ f := hg.trans (indicator_le_self s f)
  refine le_iSup_of_le g (le_iSup_of_le this (le_of_eq ?_))
  rw [lintegral_restrict, SimpleFunc.lintegral]
  congr with t
  by_cases H : t = 0
  · simp [H]
  congr with x
  simp only [mem_preimage, mem_singleton_iff, mem_inter_iff, iff_self_and]
  rintro rfl
  contrapose! H
  simpa [H] using hg x

@[simp]
theorem lintegral_indicator {s : Set α} (hs : MeasurableSet s) (f : α → ℝ≥0∞) :
    ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f a ∂μ := by
  apply le_antisymm (lintegral_indicator_le f s)
  simp only [lintegral, ← restrict_lintegral_eq_lintegral_restrict _ hs, iSup_subtype']
  refine iSup_mono' (Subtype.forall.2 fun φ hφ => ?_)
  refine ⟨⟨φ.restrict s, fun x => ?_⟩, le_rfl⟩
  simp [hφ x, hs, indicator_le_indicator]

lemma setLIntegral_indicator {s t : Set α} (hs : MeasurableSet s) (f : α → ℝ≥0∞) :
    ∫⁻ a in t, s.indicator f a ∂μ = ∫⁻ a in s ∩ t, f a ∂μ := by
  rw [lintegral_indicator hs, Measure.restrict_restrict hs]

theorem lintegral_indicator₀ {s : Set α} (hs : NullMeasurableSet s μ) (f : α → ℝ≥0∞) :
    ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f a ∂μ := by
  rw [← lintegral_congr_ae (indicator_ae_eq_of_ae_eq_set hs.toMeasurable_ae_eq),
    lintegral_indicator (measurableSet_toMeasurable _ _),
    Measure.restrict_congr_set hs.toMeasurable_ae_eq]

lemma setLIntegral_indicator₀ (f : α → ℝ≥0∞) {s t : Set α}
    (hs : NullMeasurableSet s (μ.restrict t)) :
    ∫⁻ a in t, s.indicator f a ∂μ = ∫⁻ a in s ∩ t, f a ∂μ := by
  rw [lintegral_indicator₀ hs, Measure.restrict_restrict₀ hs]

theorem lintegral_indicator_const_le (s : Set α) (c : ℝ≥0∞) :
    ∫⁻ a, s.indicator (fun _ => c) a ∂μ ≤ c * μ s :=
  (lintegral_indicator_le _ _).trans (setLIntegral_const s c).le

theorem lintegral_indicator_const₀ {s : Set α} (hs : NullMeasurableSet s μ) (c : ℝ≥0∞) :
    ∫⁻ a, s.indicator (fun _ => c) a ∂μ = c * μ s := by
  rw [lintegral_indicator₀ hs, setLIntegral_const]

theorem lintegral_indicator_const {s : Set α} (hs : MeasurableSet s) (c : ℝ≥0∞) :
    ∫⁻ a, s.indicator (fun _ => c) a ∂μ = c * μ s :=
  lintegral_indicator_const₀ hs.nullMeasurableSet c

lemma setLIntegral_eq_of_support_subset {s : Set α} {f : α → ℝ≥0∞} (hsf : f.support ⊆ s) :
    ∫⁻ x in s, f x ∂μ = ∫⁻ x, f x ∂μ := by
  apply le_antisymm (setLIntegral_le_lintegral s fun x ↦ f x)
  apply le_trans (le_of_eq _) (lintegral_indicator_le _ _)
  congr with x
  simp only [indicator]
  split_ifs with h
  · rfl
  · exact Function.support_subset_iff'.1 hsf x h

theorem setLIntegral_eq_const {f : α → ℝ≥0∞} (hf : Measurable f) (r : ℝ≥0∞) :
    ∫⁻ x in { x | f x = r }, f x ∂μ = r * μ { x | f x = r } := by
  have : ∀ᵐ x ∂μ, x ∈ { x | f x = r } → f x = r := ae_of_all μ fun _ hx => hx
  rw [setLIntegral_congr_fun _ this]
  · rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  · exact hf (measurableSet_singleton r)

theorem lintegral_indicator_one_le (s : Set α) : ∫⁻ a, s.indicator 1 a ∂μ ≤ μ s :=
  (lintegral_indicator_const_le _ _).trans <| (one_mul _).le

@[simp]
theorem lintegral_indicator_one₀ {s : Set α} (hs : NullMeasurableSet s μ) :
    ∫⁻ a, s.indicator 1 a ∂μ = μ s :=
  (lintegral_indicator_const₀ hs _).trans <| one_mul _

theorem lintegral_indicator_one {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ a, s.indicator 1 a ∂μ = μ s := by
  simp [hs]

theorem Measure.ext_iff_lintegral (ν : Measure α) :
    μ = ν ↔ ∀ f : α → ℝ≥0∞, Measurable f → ∫⁻ a, f a ∂μ = ∫⁻ a, f a ∂ν := by
  refine ⟨fun h _ _ ↦ by rw [h], ?_⟩
  intro h
  ext s hs
  simp only [← lintegral_indicator_one hs]
  exact h (s.indicator 1) ((measurable_indicator_const_iff 1).mpr hs)

theorem Measure.ext_of_lintegral (ν : Measure α)
    (hμν : ∀ f : α → ℝ≥0∞, Measurable f → ∫⁻ a, f a ∂μ = ∫⁻ a, f a ∂ν) : μ = ν :=
  (μ.ext_iff_lintegral ν).mpr hμν

open Measure

open scoped Function -- required for scoped `on` notation

theorem lintegral_iUnion₀ [Countable β] {s : β → Set α} (hm : ∀ i, NullMeasurableSet (s i) μ)
    (hd : Pairwise (AEDisjoint μ on s)) (f : α → ℝ≥0∞) :
    ∫⁻ a in ⋃ i, s i, f a ∂μ = ∑' i, ∫⁻ a in s i, f a ∂μ := by
  simp only [Measure.restrict_iUnion_ae hd hm, lintegral_sum_measure]

theorem lintegral_iUnion [Countable β] {s : β → Set α} (hm : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (f : α → ℝ≥0∞) :
    ∫⁻ a in ⋃ i, s i, f a ∂μ = ∑' i, ∫⁻ a in s i, f a ∂μ :=
  lintegral_iUnion₀ (fun i => (hm i).nullMeasurableSet) hd.aedisjoint f

theorem lintegral_biUnion₀ {t : Set β} {s : β → Set α} (ht : t.Countable)
    (hm : ∀ i ∈ t, NullMeasurableSet (s i) μ) (hd : t.Pairwise (AEDisjoint μ on s)) (f : α → ℝ≥0∞) :
    ∫⁻ a in ⋃ i ∈ t, s i, f a ∂μ = ∑' i : t, ∫⁻ a in s i, f a ∂μ := by
  haveI := ht.toEncodable
  rw [biUnion_eq_iUnion, lintegral_iUnion₀ (SetCoe.forall'.1 hm) (hd.subtype _ _)]

theorem lintegral_biUnion {t : Set β} {s : β → Set α} (ht : t.Countable)
    (hm : ∀ i ∈ t, MeasurableSet (s i)) (hd : t.PairwiseDisjoint s) (f : α → ℝ≥0∞) :
    ∫⁻ a in ⋃ i ∈ t, s i, f a ∂μ = ∑' i : t, ∫⁻ a in s i, f a ∂μ :=
  lintegral_biUnion₀ ht (fun i hi => (hm i hi).nullMeasurableSet) hd.aedisjoint f

theorem lintegral_biUnion_finset₀ {s : Finset β} {t : β → Set α}
    (hd : Set.Pairwise (↑s) (AEDisjoint μ on t)) (hm : ∀ b ∈ s, NullMeasurableSet (t b) μ)
    (f : α → ℝ≥0∞) : ∫⁻ a in ⋃ b ∈ s, t b, f a ∂μ = ∑ b ∈ s, ∫⁻ a in t b, f a ∂μ := by
  simp only [← Finset.mem_coe, lintegral_biUnion₀ s.countable_toSet hm hd, ← Finset.tsum_subtype']

theorem lintegral_biUnion_finset {s : Finset β} {t : β → Set α} (hd : Set.PairwiseDisjoint (↑s) t)
    (hm : ∀ b ∈ s, MeasurableSet (t b)) (f : α → ℝ≥0∞) :
    ∫⁻ a in ⋃ b ∈ s, t b, f a ∂μ = ∑ b ∈ s, ∫⁻ a in t b, f a ∂μ :=
  lintegral_biUnion_finset₀ hd.aedisjoint (fun b hb => (hm b hb).nullMeasurableSet) f

theorem lintegral_iUnion_le [Countable β] (s : β → Set α) (f : α → ℝ≥0∞) :
    ∫⁻ a in ⋃ i, s i, f a ∂μ ≤ ∑' i, ∫⁻ a in s i, f a ∂μ := by
  rw [← lintegral_sum_measure]
  exact lintegral_mono' restrict_iUnion_le le_rfl

theorem lintegral_union {f : α → ℝ≥0∞} {A B : Set α} (hB : MeasurableSet B) (hAB : Disjoint A B) :
    ∫⁻ a in A ∪ B, f a ∂μ = ∫⁻ a in A, f a ∂μ + ∫⁻ a in B, f a ∂μ := by
  rw [restrict_union hAB hB, lintegral_add_measure]

theorem lintegral_union_le (f : α → ℝ≥0∞) (s t : Set α) :
    ∫⁻ a in s ∪ t, f a ∂μ ≤ ∫⁻ a in s, f a ∂μ + ∫⁻ a in t, f a ∂μ := by
  rw [← lintegral_add_measure]
  exact lintegral_mono' (restrict_union_le _ _) le_rfl

theorem lintegral_inter_add_diff {B : Set α} (f : α → ℝ≥0∞) (A : Set α) (hB : MeasurableSet B) :
    ∫⁻ x in A ∩ B, f x ∂μ + ∫⁻ x in A \ B, f x ∂μ = ∫⁻ x in A, f x ∂μ := by
  rw [← lintegral_add_measure, restrict_inter_add_diff _ hB]

theorem lintegral_add_compl (f : α → ℝ≥0∞) {A : Set α} (hA : MeasurableSet A) :
    ∫⁻ x in A, f x ∂μ + ∫⁻ x in Aᶜ, f x ∂μ = ∫⁻ x, f x ∂μ := by
  rw [← lintegral_add_measure, Measure.restrict_add_restrict_compl hA]

lemma lintegral_piecewise (hs : MeasurableSet s) (f g : α → ℝ≥0∞) [∀ j, Decidable (j ∈ s)] :
    ∫⁻ a, s.piecewise f g a ∂μ = ∫⁻ a in s, f a ∂μ + ∫⁻ a in sᶜ, g a ∂μ := by
  rw [← lintegral_add_compl _ hs]
  congr 1
  · exact setLIntegral_congr_fun hs <| ae_of_all μ fun _ ↦ Set.piecewise_eq_of_mem _ _ _
  · exact setLIntegral_congr_fun hs.compl <| ae_of_all μ fun _ ↦ Set.piecewise_eq_of_not_mem _ _ _

theorem setLIntegral_compl {f : α → ℝ≥0∞} {s : Set α} (hsm : MeasurableSet s)
    (hfs : ∫⁻ x in s, f x ∂μ ≠ ∞) :
    ∫⁻ x in sᶜ, f x ∂μ = ∫⁻ x, f x ∂μ - ∫⁻ x in s, f x ∂μ := by
  rw [← lintegral_add_compl (μ := μ) f hsm, ENNReal.add_sub_cancel_left hfs]

@[deprecated (since := "2025-04-22")] alias setLintegral_compl := setLIntegral_compl

theorem setLIntegral_iUnion_of_directed {ι : Type*} [Countable ι]
    (f : α → ℝ≥0∞) {s : ι → Set α} (hd : Directed (· ⊆ ·) s) :
    ∫⁻ x in ⋃ i, s i, f x ∂μ = ⨆ i, ∫⁻ x in s i, f x ∂μ := by
  simp only [lintegral_def, iSup_comm (ι := ι),
    SimpleFunc.lintegral_restrict_iUnion_of_directed _ hd]

theorem lintegral_max {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ x, max (f x) (g x) ∂μ =
      ∫⁻ x in { x | f x ≤ g x }, g x ∂μ + ∫⁻ x in { x | g x < f x }, f x ∂μ := by
  have hm : MeasurableSet { x | f x ≤ g x } := measurableSet_le hf hg
  rw [← lintegral_add_compl (fun x => max (f x) (g x)) hm]
  simp only [← compl_setOf, ← not_le]
  refine congr_arg₂ (· + ·) (setLIntegral_congr_fun hm ?_) (setLIntegral_congr_fun hm.compl ?_)
  exacts [ae_of_all _ fun x => max_eq_right (a := f x) (b := g x),
    ae_of_all _ fun x (hx : ¬ f x ≤ g x) => max_eq_left (not_le.1 hx).le]

theorem setLIntegral_max {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (s : Set α) :
    ∫⁻ x in s, max (f x) (g x) ∂μ =
      ∫⁻ x in s ∩ { x | f x ≤ g x }, g x ∂μ + ∫⁻ x in s ∩ { x | g x < f x }, f x ∂μ := by
  rw [lintegral_max hf hg, restrict_restrict, restrict_restrict, inter_comm s, inter_comm s]
  exacts [measurableSet_lt hg hf, measurableSet_le hf hg]

/-- Lebesgue integral of a bounded function over a set of finite measure is finite.
Note that this lemma assumes no regularity of either `f` or `s`. -/
theorem setLIntegral_lt_top_of_le_nnreal {s : Set α} (hs : μ s ≠ ∞) {f : α → ℝ≥0∞}
    (hbdd : ∃ y : ℝ≥0, ∀ x ∈ s, f x ≤ y) : ∫⁻ x in s, f x ∂μ < ∞ := by
  obtain ⟨M, hM⟩ := hbdd
  refine lt_of_le_of_lt (setLIntegral_mono measurable_const hM) ?_
  simp [ENNReal.mul_lt_top, hs.lt_top]

/-- Lebesgue integral of a bounded function over a set of finite measure is finite.
Note that this lemma assumes no regularity of either `f` or `s`. -/
theorem setLIntegral_lt_top_of_bddAbove {s : Set α} (hs : μ s ≠ ∞) {f : α → ℝ≥0}
    (hbdd : BddAbove (f '' s)) : ∫⁻ x in s, f x ∂μ < ∞ :=
  setLIntegral_lt_top_of_le_nnreal hs <| hbdd.imp fun _M hM _x hx ↦
    ENNReal.coe_le_coe.2 <| hM (mem_image_of_mem f hx)

theorem setLIntegral_lt_top_of_isCompact [TopologicalSpace α] {s : Set α}
    (hs : μ s ≠ ∞) (hsc : IsCompact s) {f : α → ℝ≥0} (hf : Continuous f) :
    ∫⁻ x in s, f x ∂μ < ∞ :=
  setLIntegral_lt_top_of_bddAbove hs (hsc.image hf).bddAbove

end MeasureTheory
