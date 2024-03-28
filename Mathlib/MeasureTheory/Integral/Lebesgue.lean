/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.IndicatorConstPointwise

#align_import measure_theory.integral.lebesgue from "leanprover-community/mathlib"@"c14c8fcde993801fca8946b0d80131a1a81d1520"

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

assert_not_exists NormedSpace

set_option autoImplicit true

noncomputable section

open Set hiding restrict restrict_apply

open Filter ENNReal

open Function (support)

open scoped Classical
open Topology BigOperators NNReal ENNReal MeasureTheory

namespace MeasureTheory

-- mathport name: «expr →ₛ »
local infixr:25 " →ₛ " => SimpleFunc

variable {α β γ δ : Type*}

section Lintegral

open SimpleFunc

variable {m : MeasurableSpace α} {μ ν : Measure α}

/-- The **lower Lebesgue integral** of a function `f` with respect to a measure `μ`. -/
irreducible_def lintegral {_ : MeasurableSpace α} (μ : Measure α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (g : α →ₛ ℝ≥0∞) (_ : ⇑g ≤ f), g.lintegral μ
#align measure_theory.lintegral MeasureTheory.lintegral

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
#align measure_theory.simple_func.lintegral_eq_lintegral MeasureTheory.SimpleFunc.lintegral_eq_lintegral

@[mono]
theorem lintegral_mono' {m : MeasurableSpace α} ⦃μ ν : Measure α⦄ (hμν : μ ≤ ν) ⦃f g : α → ℝ≥0∞⦄
    (hfg : f ≤ g) : ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂ν := by
  rw [lintegral, lintegral]
  exact iSup_mono fun φ => iSup_mono' fun hφ => ⟨le_trans hφ hfg, lintegral_mono (le_refl φ) hμν⟩
#align measure_theory.lintegral_mono' MeasureTheory.lintegral_mono'

-- workaround for the known eta-reduction issue with `@[gcongr]`
@[gcongr] theorem lintegral_mono_fn' ⦃f g : α → ℝ≥0∞⦄ (hfg : ∀ x, f x ≤ g x) (h2 : μ ≤ ν) :
    lintegral μ f ≤ lintegral ν g :=
  lintegral_mono' h2 hfg

theorem lintegral_mono ⦃f g : α → ℝ≥0∞⦄ (hfg : f ≤ g) : ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂μ :=
  lintegral_mono' (le_refl μ) hfg
#align measure_theory.lintegral_mono MeasureTheory.lintegral_mono

-- workaround for the known eta-reduction issue with `@[gcongr]`
@[gcongr] theorem lintegral_mono_fn ⦃f g : α → ℝ≥0∞⦄ (hfg : ∀ x, f x ≤ g x) :
    lintegral μ f ≤ lintegral μ g :=
  lintegral_mono hfg

theorem lintegral_mono_nnreal {f g : α → ℝ≥0} (h : f ≤ g) : ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂μ :=
  lintegral_mono fun a => ENNReal.coe_le_coe.2 (h a)
#align measure_theory.lintegral_mono_nnreal MeasureTheory.lintegral_mono_nnreal

theorem iSup_lintegral_measurable_le_eq_lintegral (f : α → ℝ≥0∞) :
    ⨆ (g : α → ℝ≥0∞) (_ : Measurable g) (_ : g ≤ f), ∫⁻ a, g a ∂μ = ∫⁻ a, f a ∂μ := by
  apply le_antisymm
  · exact iSup_le fun i => iSup_le fun _ => iSup_le fun h'i => lintegral_mono h'i
  · rw [lintegral]
    refine' iSup₂_le fun i hi => le_iSup₂_of_le i i.measurable <| le_iSup_of_le hi _
    exact le_of_eq (i.lintegral_eq_lintegral _).symm
#align measure_theory.supr_lintegral_measurable_le_eq_lintegral MeasureTheory.iSup_lintegral_measurable_le_eq_lintegral

theorem lintegral_mono_set {_ : MeasurableSpace α} ⦃μ : Measure α⦄ {s t : Set α} {f : α → ℝ≥0∞}
    (hst : s ⊆ t) : ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in t, f x ∂μ :=
  lintegral_mono' (Measure.restrict_mono hst (le_refl μ)) (le_refl f)
#align measure_theory.lintegral_mono_set MeasureTheory.lintegral_mono_set

theorem lintegral_mono_set' {_ : MeasurableSpace α} ⦃μ : Measure α⦄ {s t : Set α} {f : α → ℝ≥0∞}
    (hst : s ≤ᵐ[μ] t) : ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in t, f x ∂μ :=
  lintegral_mono' (Measure.restrict_mono' hst (le_refl μ)) (le_refl f)
#align measure_theory.lintegral_mono_set' MeasureTheory.lintegral_mono_set'

theorem monotone_lintegral {_ : MeasurableSpace α} (μ : Measure α) : Monotone (lintegral μ) :=
  lintegral_mono
#align measure_theory.monotone_lintegral MeasureTheory.monotone_lintegral

@[simp]
theorem lintegral_const (c : ℝ≥0∞) : ∫⁻ _, c ∂μ = c * μ univ := by
  rw [← SimpleFunc.const_lintegral, ← SimpleFunc.lintegral_eq_lintegral, SimpleFunc.coe_const]
  rfl
#align measure_theory.lintegral_const MeasureTheory.lintegral_const

theorem lintegral_zero : ∫⁻ _ : α, 0 ∂μ = 0 := by simp
#align measure_theory.lintegral_zero MeasureTheory.lintegral_zero

theorem lintegral_zero_fun : lintegral μ (0 : α → ℝ≥0∞) = 0 :=
  lintegral_zero
#align measure_theory.lintegral_zero_fun MeasureTheory.lintegral_zero_fun

-- @[simp] -- Porting note (#10618): simp can prove this
theorem lintegral_one : ∫⁻ _, (1 : ℝ≥0∞) ∂μ = μ univ := by rw [lintegral_const, one_mul]
#align measure_theory.lintegral_one MeasureTheory.lintegral_one

theorem set_lintegral_const (s : Set α) (c : ℝ≥0∞) : ∫⁻ _ in s, c ∂μ = c * μ s := by
  rw [lintegral_const, Measure.restrict_apply_univ]
#align measure_theory.set_lintegral_const MeasureTheory.set_lintegral_const

theorem set_lintegral_one (s) : ∫⁻ _ in s, 1 ∂μ = μ s := by rw [set_lintegral_const, one_mul]
#align measure_theory.set_lintegral_one MeasureTheory.set_lintegral_one

theorem set_lintegral_const_lt_top [IsFiniteMeasure μ] (s : Set α) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    ∫⁻ _ in s, c ∂μ < ∞ := by
  rw [lintegral_const]
  exact ENNReal.mul_lt_top hc (measure_ne_top (μ.restrict s) univ)
#align measure_theory.set_lintegral_const_lt_top MeasureTheory.set_lintegral_const_lt_top

theorem lintegral_const_lt_top [IsFiniteMeasure μ] {c : ℝ≥0∞} (hc : c ≠ ∞) : ∫⁻ _, c ∂μ < ∞ := by
  simpa only [Measure.restrict_univ] using set_lintegral_const_lt_top (univ : Set α) hc
#align measure_theory.lintegral_const_lt_top MeasureTheory.lintegral_const_lt_top

section

variable (μ)

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
  refine'
    ⟨fun x => ⨆ n, g n x, measurable_iSup hgm, fun x => iSup_le fun n => hgf n x, le_antisymm _ _⟩
  · refine' le_of_tendsto' hL_tendsto fun n => (hLg n).le.trans <| lintegral_mono fun x => _
    exact le_iSup (fun n => g n x) n
  · exact lintegral_mono fun x => iSup_le fun n => hgf n x
#align measure_theory.exists_measurable_le_lintegral_eq MeasureTheory.exists_measurable_le_lintegral_eq

end

/-- `∫⁻ a in s, f a ∂μ` is defined as the supremum of integrals of simple functions
`φ : α →ₛ ℝ≥0∞` such that `φ ≤ f`. This lemma says that it suffices to take
functions `φ : α →ₛ ℝ≥0`. -/
theorem lintegral_eq_nnreal {m : MeasurableSpace α} (f : α → ℝ≥0∞) (μ : Measure α) :
    ∫⁻ a, f a ∂μ =
      ⨆ (φ : α →ₛ ℝ≥0) (_ : ∀ x, ↑(φ x) ≤ f x), (φ.map ((↑) : ℝ≥0 → ℝ≥0∞)).lintegral μ := by
  rw [lintegral]
  refine'
    le_antisymm (iSup₂_le fun φ hφ => _) (iSup_mono' fun φ => ⟨φ.map ((↑) : ℝ≥0 → ℝ≥0∞), le_rfl⟩)
  by_cases h : ∀ᵐ a ∂μ, φ a ≠ ∞
  · let ψ := φ.map ENNReal.toNNReal
    replace h : ψ.map ((↑) : ℝ≥0 → ℝ≥0∞) =ᵐ[μ] φ := h.mono fun a => ENNReal.coe_toNNReal
    have : ∀ x, ↑(ψ x) ≤ f x := fun x => le_trans ENNReal.coe_toNNReal_le_self (hφ x)
    exact
      le_iSup_of_le (φ.map ENNReal.toNNReal) (le_iSup_of_le this (ge_of_eq <| lintegral_congr h))
  · have h_meas : μ (φ ⁻¹' {∞}) ≠ 0 := mt measure_zero_iff_ae_nmem.1 h
    refine' le_trans le_top (ge_of_eq <| (iSup_eq_top _).2 fun b hb => _)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, b < n * μ (φ ⁻¹' {∞}) := exists_nat_mul_gt h_meas (ne_of_lt hb)
    use (const α (n : ℝ≥0)).restrict (φ ⁻¹' {∞})
    simp only [lt_iSup_iff, exists_prop, coe_restrict, φ.measurableSet_preimage, coe_const,
      ENNReal.coe_indicator, map_coe_ennreal_restrict, SimpleFunc.map_const, ENNReal.coe_nat,
      restrict_const_lintegral]
    refine' ⟨indicator_le fun x hx => le_trans _ (hφ _), hn⟩
    simp only [mem_preimage, mem_singleton_iff] at hx
    simp only [hx, le_top]
#align measure_theory.lintegral_eq_nnreal MeasureTheory.lintegral_eq_nnreal

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
  refine' ⟨φ, hle, fun ψ hψ => _⟩
  have : (map (↑) φ).lintegral μ ≠ ∞ := ne_top_of_le_ne_top h (by exact le_iSup₂ (α := ℝ≥0∞) φ hle)
  rw [← ENNReal.add_lt_add_iff_left this, ← add_lintegral, ← SimpleFunc.map_add @ENNReal.coe_add]
  refine' (hb _ fun x => le_trans _ (max_le (hle x) (hψ x))).trans_lt hbφ
  norm_cast
  simp only [add_apply, sub_apply, add_tsub_eq_max]
  rfl
#align measure_theory.exists_simple_func_forall_lintegral_sub_lt_of_pos MeasureTheory.exists_simpleFunc_forall_lintegral_sub_lt_of_pos

theorem iSup_lintegral_le {ι : Sort*} (f : ι → α → ℝ≥0∞) :
    ⨆ i, ∫⁻ a, f i a ∂μ ≤ ∫⁻ a, ⨆ i, f i a ∂μ := by
  simp only [← iSup_apply]
  exact (monotone_lintegral μ).le_map_iSup
#align measure_theory.supr_lintegral_le MeasureTheory.iSup_lintegral_le

theorem iSup₂_lintegral_le {ι : Sort*} {ι' : ι → Sort*} (f : ∀ i, ι' i → α → ℝ≥0∞) :
    ⨆ (i) (j), ∫⁻ a, f i j a ∂μ ≤ ∫⁻ a, ⨆ (i) (j), f i j a ∂μ := by
  convert (monotone_lintegral μ).le_map_iSup₂ f with a
  simp only [iSup_apply]
#align measure_theory.supr₂_lintegral_le MeasureTheory.iSup₂_lintegral_le

theorem le_iInf_lintegral {ι : Sort*} (f : ι → α → ℝ≥0∞) :
    ∫⁻ a, ⨅ i, f i a ∂μ ≤ ⨅ i, ∫⁻ a, f i a ∂μ := by
  simp only [← iInf_apply]
  exact (monotone_lintegral μ).map_iInf_le
#align measure_theory.le_infi_lintegral MeasureTheory.le_iInf_lintegral

theorem le_iInf₂_lintegral {ι : Sort*} {ι' : ι → Sort*} (f : ∀ i, ι' i → α → ℝ≥0∞) :
    ∫⁻ a, ⨅ (i) (h : ι' i), f i h a ∂μ ≤ ⨅ (i) (h : ι' i), ∫⁻ a, f i h a ∂μ := by
  convert (monotone_lintegral μ).map_iInf₂_le f with a
  simp only [iInf_apply]
#align measure_theory.le_infi₂_lintegral MeasureTheory.le_iInf₂_lintegral

theorem lintegral_mono_ae {f g : α → ℝ≥0∞} (h : ∀ᵐ a ∂μ, f a ≤ g a) :
    ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂μ := by
  rcases exists_measurable_superset_of_null h with ⟨t, hts, ht, ht0⟩
  have : ∀ᵐ x ∂μ, x ∉ t := measure_zero_iff_ae_nmem.1 ht0
  rw [lintegral, lintegral]
  refine' iSup_le fun s => iSup_le fun hfs => le_iSup_of_le (s.restrict tᶜ) <| le_iSup_of_le _ _
  · intro a
    by_cases h : a ∈ t <;>
      simp only [restrict_apply s ht.compl, mem_compl_iff, h, not_true, not_false_eq_true,
        indicator_of_not_mem, zero_le, not_false_eq_true, indicator_of_mem]
    exact le_trans (hfs a) (_root_.by_contradiction fun hnfg => h (hts hnfg))
  · refine' le_of_eq (SimpleFunc.lintegral_congr <| this.mono fun a hnt => _)
    by_cases hat : a ∈ t <;> simp only [restrict_apply s ht.compl, mem_compl_iff, hat, not_true,
      not_false_eq_true, indicator_of_not_mem, not_false_eq_true, indicator_of_mem]
    exact (hnt hat).elim
#align measure_theory.lintegral_mono_ae MeasureTheory.lintegral_mono_ae

theorem set_lintegral_mono_ae {s : Set α} {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → f x ≤ g x) : ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in s, g x ∂μ :=
  lintegral_mono_ae <| (ae_restrict_iff <| measurableSet_le hf hg).2 hfg
#align measure_theory.set_lintegral_mono_ae MeasureTheory.set_lintegral_mono_ae

theorem set_lintegral_mono {s : Set α} {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ x ∈ s, f x ≤ g x) : ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in s, g x ∂μ :=
  set_lintegral_mono_ae hf hg (ae_of_all _ hfg)
#align measure_theory.set_lintegral_mono MeasureTheory.set_lintegral_mono

theorem set_lintegral_mono_ae' {s : Set α} {f g : α → ℝ≥0∞} (hs : MeasurableSet s)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → f x ≤ g x) : ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in s, g x ∂μ :=
  lintegral_mono_ae <| (ae_restrict_iff' hs).2 hfg

theorem set_lintegral_mono' {s : Set α} {f g : α → ℝ≥0∞} (hs : MeasurableSet s)
    (hfg : ∀ x ∈ s, f x ≤ g x) : ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in s, g x ∂μ :=
  set_lintegral_mono_ae' hs (ae_of_all _ hfg)

theorem set_lintegral_le_lintegral (s : Set α) (f : α → ℝ≥0∞) :
    ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x, f x ∂μ :=
  lintegral_mono' Measure.restrict_le_self le_rfl

theorem lintegral_congr_ae {f g : α → ℝ≥0∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ :=
  le_antisymm (lintegral_mono_ae <| h.le) (lintegral_mono_ae <| h.symm.le)
#align measure_theory.lintegral_congr_ae MeasureTheory.lintegral_congr_ae

theorem lintegral_congr {f g : α → ℝ≥0∞} (h : ∀ a, f a = g a) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ := by
  simp only [h]
#align measure_theory.lintegral_congr MeasureTheory.lintegral_congr

theorem set_lintegral_congr {f : α → ℝ≥0∞} {s t : Set α} (h : s =ᵐ[μ] t) :
    ∫⁻ x in s, f x ∂μ = ∫⁻ x in t, f x ∂μ := by rw [Measure.restrict_congr_set h]
#align measure_theory.set_lintegral_congr MeasureTheory.set_lintegral_congr

theorem set_lintegral_congr_fun {f g : α → ℝ≥0∞} {s : Set α} (hs : MeasurableSet s)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → f x = g x) : ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ := by
  rw [lintegral_congr_ae]
  rw [EventuallyEq]
  rwa [ae_restrict_iff' hs]
#align measure_theory.set_lintegral_congr_fun MeasureTheory.set_lintegral_congr_fun

theorem lintegral_ofReal_le_lintegral_nnnorm (f : α → ℝ) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ∫⁻ x, ‖f x‖₊ ∂μ := by
  simp_rw [← ofReal_norm_eq_coe_nnnorm]
  refine' lintegral_mono fun x => ENNReal.ofReal_le_ofReal _
  rw [Real.norm_eq_abs]
  exact le_abs_self (f x)
#align measure_theory.lintegral_of_real_le_lintegral_nnnorm MeasureTheory.lintegral_ofReal_le_lintegral_nnnorm

theorem lintegral_nnnorm_eq_of_ae_nonneg {f : α → ℝ} (h_nonneg : 0 ≤ᵐ[μ] f) :
    ∫⁻ x, ‖f x‖₊ ∂μ = ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  apply lintegral_congr_ae
  filter_upwards [h_nonneg] with x hx
  rw [Real.nnnorm_of_nonneg hx, ENNReal.ofReal_eq_coe_nnreal hx]
#align measure_theory.lintegral_nnnorm_eq_of_ae_nonneg MeasureTheory.lintegral_nnnorm_eq_of_ae_nonneg

theorem lintegral_nnnorm_eq_of_nonneg {f : α → ℝ} (h_nonneg : 0 ≤ f) :
    ∫⁻ x, ‖f x‖₊ ∂μ = ∫⁻ x, ENNReal.ofReal (f x) ∂μ :=
  lintegral_nnnorm_eq_of_ae_nonneg (Filter.eventually_of_forall h_nonneg)
#align measure_theory.lintegral_nnnorm_eq_of_nonneg MeasureTheory.lintegral_nnnorm_eq_of_nonneg

/-- **Monotone convergence theorem** -- sometimes called **Beppo-Levi convergence**.
See `lintegral_iSup_directed` for a more general form. -/
theorem lintegral_iSup {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, Measurable (f n)) (h_mono : Monotone f) :
    ∫⁻ a, ⨆ n, f n a ∂μ = ⨆ n, ∫⁻ a, f n a ∂μ := by
  set c : ℝ≥0 → ℝ≥0∞ := (↑)
  set F := fun a : α => ⨆ n, f n a
  refine' le_antisymm _ (iSup_lintegral_le _)
  rw [lintegral_eq_nnreal]
  refine' iSup_le fun s => iSup_le fun hsf => _
  refine' ENNReal.le_of_forall_lt_one_mul_le fun a ha => _
  rcases ENNReal.lt_iff_exists_coe.1 ha with ⟨r, rfl, _⟩
  have ha : r < 1 := ENNReal.coe_lt_coe.1 ha
  let rs := s.map fun a => r * a
  have eq_rs : rs.map c = (const α r : α →ₛ ℝ≥0∞) * map c s := rfl
  have eq : ∀ p, rs.map c ⁻¹' {p} = ⋃ n, rs.map c ⁻¹' {p} ∩ { a | p ≤ f n a } := by
    intro p
    rw [← inter_iUnion]; nth_rw 1 [← inter_univ (map c rs ⁻¹' {p})]
    refine' Set.ext fun x => and_congr_right fun hx => true_iff_iff.2 _
    by_cases p_eq : p = 0
    · simp [p_eq]
    simp only [coe_map, mem_preimage, Function.comp_apply, mem_singleton_iff] at hx
    subst hx
    have : r * s x ≠ 0 := by rwa [Ne, ← ENNReal.coe_eq_zero]
    have : s x ≠ 0 := by
      refine' mt _ this
      intro h
      rw [h, mul_zero]
    have : (rs.map c) x < ⨆ n : ℕ, f n x := by
      refine' lt_of_lt_of_le (ENNReal.coe_lt_coe.2 _) (hsf x)
      suffices r * s x < 1 * s x by simpa
      exact mul_lt_mul_of_pos_right ha (pos_iff_ne_zero.2 this)
    rcases lt_iSup_iff.1 this with ⟨i, hi⟩
    exact mem_iUnion.2 ⟨i, le_of_lt hi⟩
  have mono : ∀ r : ℝ≥0∞, Monotone fun n => rs.map c ⁻¹' {r} ∩ { a | r ≤ f n a } := by
    intro r i j h
    refine' inter_subset_inter (Subset.refl _) _
    intro x (hx : r ≤ f i x)
    exact le_trans hx (h_mono h x)
  have h_meas : ∀ n, MeasurableSet {a : α | map c rs a ≤ f n a} := fun n =>
    measurableSet_le (SimpleFunc.measurable _) (hf n)
  calc
    (r : ℝ≥0∞) * (s.map c).lintegral μ = ∑ r in (rs.map c).range, r * μ (rs.map c ⁻¹' {r}) := by
      rw [← const_mul_lintegral, eq_rs, SimpleFunc.lintegral]
    _ = ∑ r in (rs.map c).range, r * μ (⋃ n, rs.map c ⁻¹' {r} ∩ { a | r ≤ f n a }) := by
      simp only [(eq _).symm]
    _ = ∑ r in (rs.map c).range, ⨆ n, r * μ (rs.map c ⁻¹' {r} ∩ { a | r ≤ f n a }) :=
      (Finset.sum_congr rfl fun x _ => by
        rw [measure_iUnion_eq_iSup (mono x).directed_le, ENNReal.mul_iSup])
    _ = ⨆ n, ∑ r in (rs.map c).range, r * μ (rs.map c ⁻¹' {r} ∩ { a | r ≤ f n a }) := by
      rw [ENNReal.finset_sum_iSup_nat]
      intro p i j h
      exact mul_le_mul_left' (measure_mono <| mono p h) _
    _ ≤ ⨆ n : ℕ, ((rs.map c).restrict { a | (rs.map c) a ≤ f n a }).lintegral μ := by
      gcongr with n
      rw [restrict_lintegral _ (h_meas n)]
      · refine' le_of_eq (Finset.sum_congr rfl fun r _ => _)
        congr 2 with a
        refine' and_congr_right _
        simp (config := { contextual := true })
    _ ≤ ⨆ n, ∫⁻ a, f n a ∂μ := by
      gcongr with n
      rw [← SimpleFunc.lintegral_eq_lintegral]
      gcongr with a
      simp only [map_apply] at h_meas
      simp only [coe_map, restrict_apply _ (h_meas _), (· ∘ ·)]
      exact indicator_apply_le id
#align measure_theory.lintegral_supr MeasureTheory.lintegral_iSup

/-- Monotone convergence theorem -- sometimes called Beppo-Levi convergence. Version with
ae_measurable functions. -/
theorem lintegral_iSup' {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, AEMeasurable (f n) μ)
    (h_mono : ∀ᵐ x ∂μ, Monotone fun n => f n x) : ∫⁻ a, ⨆ n, f n a ∂μ = ⨆ n, ∫⁻ a, f n a ∂μ := by
  simp_rw [← iSup_apply]
  let p : α → (ℕ → ℝ≥0∞) → Prop := fun _ f' => Monotone f'
  have hp : ∀ᵐ x ∂μ, p x fun i => f i x := h_mono
  have h_ae_seq_mono : Monotone (aeSeq hf p) := by
    intro n m hnm x
    by_cases hx : x ∈ aeSeqSet hf p
    · exact aeSeq.prop_of_mem_aeSeqSet hf hx hnm
    · simp only [aeSeq, hx, if_false]
      exact le_rfl
  rw [lintegral_congr_ae (aeSeq.iSup hf hp).symm]
  simp_rw [iSup_apply]
  rw [@lintegral_iSup _ _ μ _ (aeSeq.measurable hf p) h_ae_seq_mono]
  congr
  exact funext fun n => lintegral_congr_ae (aeSeq.aeSeq_n_eq_fun_n_ae hf hp n)
#align measure_theory.lintegral_supr' MeasureTheory.lintegral_iSup'

/-- Monotone convergence theorem expressed with limits -/
theorem lintegral_tendsto_of_tendsto_of_monotone {f : ℕ → α → ℝ≥0∞} {F : α → ℝ≥0∞}
    (hf : ∀ n, AEMeasurable (f n) μ) (h_mono : ∀ᵐ x ∂μ, Monotone fun n => f n x)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 <| F x)) :
    Tendsto (fun n => ∫⁻ x, f n x ∂μ) atTop (𝓝 <| ∫⁻ x, F x ∂μ) := by
  have : Monotone fun n => ∫⁻ x, f n x ∂μ := fun i j hij =>
    lintegral_mono_ae (h_mono.mono fun x hx => hx hij)
  suffices key : ∫⁻ x, F x ∂μ = ⨆ n, ∫⁻ x, f n x ∂μ by
    rw [key]
    exact tendsto_atTop_iSup this
  rw [← lintegral_iSup' hf h_mono]
  refine' lintegral_congr_ae _
  filter_upwards [h_mono,
    h_tendsto] with _ hx_mono hx_tendsto using tendsto_nhds_unique hx_tendsto
      (tendsto_atTop_iSup hx_mono)
#align measure_theory.lintegral_tendsto_of_tendsto_of_monotone MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone

theorem lintegral_eq_iSup_eapprox_lintegral {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a, f a ∂μ = ⨆ n, (eapprox f n).lintegral μ :=
  calc
    ∫⁻ a, f a ∂μ = ∫⁻ a, ⨆ n, (eapprox f n : α → ℝ≥0∞) a ∂μ := by
      congr; ext a; rw [iSup_eapprox_apply f hf]
    _ = ⨆ n, ∫⁻ a, (eapprox f n : α → ℝ≥0∞) a ∂μ := by
      rw [lintegral_iSup]
      · measurability
      · intro i j h
        exact monotone_eapprox f h
    _ = ⨆ n, (eapprox f n).lintegral μ := by
      congr; ext n; rw [(eapprox f n).lintegral_eq_lintegral]
#align measure_theory.lintegral_eq_supr_eapprox_lintegral MeasureTheory.lintegral_eq_iSup_eapprox_lintegral

/-- If `f` has finite integral, then `∫⁻ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. This lemma states states this fact in terms of `ε` and `δ`. -/
theorem exists_pos_set_lintegral_lt_of_measure_lt {f : α → ℝ≥0∞} (h : ∫⁻ x, f x ∂μ ≠ ∞) {ε : ℝ≥0∞}
    (hε : ε ≠ 0) : ∃ δ > 0, ∀ s, μ s < δ → ∫⁻ x in s, f x ∂μ < ε := by
  rcases exists_between hε.bot_lt with ⟨ε₂, hε₂0 : 0 < ε₂, hε₂ε⟩
  rcases exists_between hε₂0 with ⟨ε₁, hε₁0, hε₁₂⟩
  rcases exists_simpleFunc_forall_lintegral_sub_lt_of_pos h hε₁0.ne' with ⟨φ, _, hφ⟩
  rcases φ.exists_forall_le with ⟨C, hC⟩
  use (ε₂ - ε₁) / C, ENNReal.div_pos_iff.2 ⟨(tsub_pos_iff_lt.2 hε₁₂).ne', ENNReal.coe_ne_top⟩
  refine' fun s hs => lt_of_le_of_lt _ hε₂ε
  simp only [lintegral_eq_nnreal, iSup_le_iff]
  intro ψ hψ
  calc
    (map (↑) ψ).lintegral (μ.restrict s) ≤
        (map (↑) φ).lintegral (μ.restrict s) + (map (↑) (ψ - φ)).lintegral (μ.restrict s) := by
      rw [← SimpleFunc.add_lintegral, ← SimpleFunc.map_add @ENNReal.coe_add]
      refine' SimpleFunc.lintegral_mono (fun x => _) le_rfl
      simp only [add_tsub_eq_max, le_max_right, coe_map, Function.comp_apply, SimpleFunc.coe_add,
        SimpleFunc.coe_sub, Pi.add_apply, Pi.sub_apply, ENNReal.coe_max (φ x) (ψ x)]
    _ ≤ (map (↑) φ).lintegral (μ.restrict s) + ε₁ := by
      gcongr
      refine' le_trans _ (hφ _ hψ).le
      exact SimpleFunc.lintegral_mono le_rfl Measure.restrict_le_self
    _ ≤ (SimpleFunc.const α (C : ℝ≥0∞)).lintegral (μ.restrict s) + ε₁ :=
      (add_le_add (SimpleFunc.lintegral_mono (fun x => by exact coe_le_coe.2 (hC x)) le_rfl) le_rfl)
    _ = C * μ s + ε₁ := by
      simp only [← SimpleFunc.lintegral_eq_lintegral, coe_const, lintegral_const,
        Measure.restrict_apply, MeasurableSet.univ, univ_inter, Function.const]
    _ ≤ C * ((ε₂ - ε₁) / C) + ε₁ := by gcongr
    _ ≤ ε₂ - ε₁ + ε₁ := by gcongr; apply mul_div_le
    _ = ε₂ := tsub_add_cancel_of_le hε₁₂.le
#align measure_theory.exists_pos_set_lintegral_lt_of_measure_lt MeasureTheory.exists_pos_set_lintegral_lt_of_measure_lt

/-- If `f` has finite integral, then `∫⁻ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. -/
theorem tendsto_set_lintegral_zero {ι} {f : α → ℝ≥0∞} (h : ∫⁻ x, f x ∂μ ≠ ∞) {l : Filter ι}
    {s : ι → Set α} (hl : Tendsto (μ ∘ s) l (𝓝 0)) :
    Tendsto (fun i => ∫⁻ x in s i, f x ∂μ) l (𝓝 0) := by
  simp only [ENNReal.nhds_zero, tendsto_iInf, tendsto_principal, mem_Iio,
    ← pos_iff_ne_zero] at hl ⊢
  intro ε ε0
  rcases exists_pos_set_lintegral_lt_of_measure_lt h ε0.ne' with ⟨δ, δ0, hδ⟩
  exact (hl δ δ0).mono fun i => hδ _
#align measure_theory.tendsto_set_lintegral_zero MeasureTheory.tendsto_set_lintegral_zero

/-- The sum of the lower Lebesgue integrals of two functions is less than or equal to the integral
of their sum. The other inequality needs one of these functions to be (a.e.-)measurable. -/
theorem le_lintegral_add (f g : α → ℝ≥0∞) :
    ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ ≤ ∫⁻ a, f a + g a ∂μ := by
  simp only [lintegral]
  refine' ENNReal.biSup_add_biSup_le' (p := fun h : α →ₛ ℝ≥0∞ => h ≤ f)
    (q := fun h : α →ₛ ℝ≥0∞ => h ≤ g) ⟨0, zero_le f⟩ ⟨0, zero_le g⟩ fun f' hf' g' hg' => _
  exact le_iSup₂_of_le (f' + g') (add_le_add hf' hg') (add_lintegral _ _).ge
#align measure_theory.le_lintegral_add MeasureTheory.le_lintegral_add

-- Use stronger lemmas `lintegral_add_left`/`lintegral_add_right` instead
theorem lintegral_add_aux {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ :=
  calc
    ∫⁻ a, f a + g a ∂μ =
        ∫⁻ a, (⨆ n, (eapprox f n : α → ℝ≥0∞) a) + ⨆ n, (eapprox g n : α → ℝ≥0∞) a ∂μ :=
      by simp only [iSup_eapprox_apply, hf, hg]
    _ = ∫⁻ a, ⨆ n, (eapprox f n + eapprox g n : α → ℝ≥0∞) a ∂μ := by
      congr; funext a
      rw [ENNReal.iSup_add_iSup_of_monotone]; · rfl
      · intro i j h
        exact monotone_eapprox _ h a
      · intro i j h
        exact monotone_eapprox _ h a
    _ = ⨆ n, (eapprox f n).lintegral μ + (eapprox g n).lintegral μ := by
      rw [lintegral_iSup]
      · congr
        funext n
        rw [← SimpleFunc.add_lintegral, ← SimpleFunc.lintegral_eq_lintegral]
        simp only [Pi.add_apply, SimpleFunc.coe_add]
      · measurability
      · intro i j h a
        exact add_le_add (monotone_eapprox _ h _) (monotone_eapprox _ h _)
    _ = (⨆ n, (eapprox f n).lintegral μ) + ⨆ n, (eapprox g n).lintegral μ := by
      refine' (ENNReal.iSup_add_iSup_of_monotone _ _).symm <;>
        · intro i j h
          exact SimpleFunc.lintegral_mono (monotone_eapprox _ h) (le_refl μ)
    _ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ := by
      rw [lintegral_eq_iSup_eapprox_lintegral hf, lintegral_eq_iSup_eapprox_lintegral hg]
#align measure_theory.lintegral_add_aux MeasureTheory.lintegral_add_aux

/-- If `f g : α → ℝ≥0∞` are two functions and one of them is (a.e.) measurable, then the Lebesgue
integral of `f + g` equals the sum of integrals. This lemma assumes that `f` is integrable, see also
`MeasureTheory.lintegral_add_right` and primed versions of these lemmas. -/
@[simp]
theorem lintegral_add_left {f : α → ℝ≥0∞} (hf : Measurable f) (g : α → ℝ≥0∞) :
    ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ := by
  refine' le_antisymm _ (le_lintegral_add _ _)
  rcases exists_measurable_le_lintegral_eq μ fun a => f a + g a with ⟨φ, hφm, hφ_le, hφ_eq⟩
  calc
    ∫⁻ a, f a + g a ∂μ = ∫⁻ a, φ a ∂μ := hφ_eq
    _ ≤ ∫⁻ a, f a + (φ a - f a) ∂μ := (lintegral_mono fun a => le_add_tsub)
    _ = ∫⁻ a, f a ∂μ + ∫⁻ a, φ a - f a ∂μ := (lintegral_add_aux hf (hφm.sub hf))
    _ ≤ ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ :=
      add_le_add_left (lintegral_mono fun a => tsub_le_iff_left.2 <| hφ_le a) _
#align measure_theory.lintegral_add_left MeasureTheory.lintegral_add_left

theorem lintegral_add_left' {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (g : α → ℝ≥0∞) :
    ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ := by
  rw [lintegral_congr_ae hf.ae_eq_mk, ← lintegral_add_left hf.measurable_mk,
    lintegral_congr_ae (hf.ae_eq_mk.add (ae_eq_refl g))]
#align measure_theory.lintegral_add_left' MeasureTheory.lintegral_add_left'

theorem lintegral_add_right' (f : α → ℝ≥0∞) {g : α → ℝ≥0∞} (hg : AEMeasurable g μ) :
    ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ := by
  simpa only [add_comm] using lintegral_add_left' hg f
#align measure_theory.lintegral_add_right' MeasureTheory.lintegral_add_right'

/-- If `f g : α → ℝ≥0∞` are two functions and one of them is (a.e.) measurable, then the Lebesgue
integral of `f + g` equals the sum of integrals. This lemma assumes that `g` is integrable, see also
`MeasureTheory.lintegral_add_left` and primed versions of these lemmas. -/
@[simp]
theorem lintegral_add_right (f : α → ℝ≥0∞) {g : α → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ :=
  lintegral_add_right' f hg.aemeasurable
#align measure_theory.lintegral_add_right MeasureTheory.lintegral_add_right

@[simp]
theorem lintegral_smul_measure (c : ℝ≥0∞) (f : α → ℝ≥0∞) : ∫⁻ a, f a ∂c • μ = c * ∫⁻ a, f a ∂μ :=
  by simp only [lintegral, iSup_subtype', SimpleFunc.lintegral_smul, ENNReal.mul_iSup, smul_eq_mul]
#align measure_theory.lintegral_smul_measure MeasureTheory.lintegral_smul_measure

lemma set_lintegral_smul_measure (c : ℝ≥0∞) (f : α → ℝ≥0∞) (s : Set α) :
    ∫⁻ a in s, f a ∂(c • μ) = c * ∫⁻ a in s, f a ∂μ := by
  rw [Measure.restrict_smul, lintegral_smul_measure]

@[simp]
theorem lintegral_sum_measure {m : MeasurableSpace α} {ι} (f : α → ℝ≥0∞) (μ : ι → Measure α) :
    ∫⁻ a, f a ∂Measure.sum μ = ∑' i, ∫⁻ a, f a ∂μ i := by
  simp only [lintegral, iSup_subtype', SimpleFunc.lintegral_sum, ENNReal.tsum_eq_iSup_sum]
  rw [iSup_comm]
  congr; funext s
  induction' s using Finset.induction_on with i s hi hs
  · apply bot_unique
    simp
  simp only [Finset.sum_insert hi, ← hs]
  refine' (ENNReal.iSup_add_iSup _).symm
  intro φ ψ
  exact
    ⟨⟨φ ⊔ ψ, fun x => sup_le (φ.2 x) (ψ.2 x)⟩,
      add_le_add (SimpleFunc.lintegral_mono le_sup_left le_rfl)
        (Finset.sum_le_sum fun j _ => SimpleFunc.lintegral_mono le_sup_right le_rfl)⟩
#align measure_theory.lintegral_sum_measure MeasureTheory.lintegral_sum_measure

theorem hasSum_lintegral_measure {ι} {_ : MeasurableSpace α} (f : α → ℝ≥0∞) (μ : ι → Measure α) :
    HasSum (fun i => ∫⁻ a, f a ∂μ i) (∫⁻ a, f a ∂Measure.sum μ) :=
  (lintegral_sum_measure f μ).symm ▸ ENNReal.summable.hasSum
#align measure_theory.has_sum_lintegral_measure MeasureTheory.hasSum_lintegral_measure

@[simp]
theorem lintegral_add_measure {m : MeasurableSpace α} (f : α → ℝ≥0∞) (μ ν : Measure α) :
    ∫⁻ a, f a ∂(μ + ν) = ∫⁻ a, f a ∂μ + ∫⁻ a, f a ∂ν := by
  simpa [tsum_fintype] using lintegral_sum_measure f fun b => cond b μ ν
#align measure_theory.lintegral_add_measure MeasureTheory.lintegral_add_measure

@[simp]
theorem lintegral_finset_sum_measure {ι} {m : MeasurableSpace α} (s : Finset ι) (f : α → ℝ≥0∞)
    (μ : ι → Measure α) : ∫⁻ a, f a ∂(∑ i in s, μ i) = ∑ i in s, ∫⁻ a, f a ∂μ i := by
  rw [← Measure.sum_coe_finset, lintegral_sum_measure, ← Finset.tsum_subtype']
  rfl
#align measure_theory.lintegral_finset_sum_measure MeasureTheory.lintegral_finset_sum_measure

@[simp]
theorem lintegral_zero_measure {m : MeasurableSpace α} (f : α → ℝ≥0∞) :
    (∫⁻ a, f a ∂(0 : Measure α)) = 0 :=
  bot_unique <| by simp [lintegral]
#align measure_theory.lintegral_zero_measure MeasureTheory.lintegral_zero_measure

@[simp]
theorem lintegral_of_isEmpty {α} [MeasurableSpace α] [IsEmpty α] (μ : Measure α) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = 0 := by convert lintegral_zero_measure f

theorem set_lintegral_empty (f : α → ℝ≥0∞) : ∫⁻ x in ∅, f x ∂μ = 0 := by
  rw [Measure.restrict_empty, lintegral_zero_measure]
#align measure_theory.set_lintegral_empty MeasureTheory.set_lintegral_empty

theorem set_lintegral_univ (f : α → ℝ≥0∞) : ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ := by
  rw [Measure.restrict_univ]
#align measure_theory.set_lintegral_univ MeasureTheory.set_lintegral_univ

theorem set_lintegral_measure_zero (s : Set α) (f : α → ℝ≥0∞) (hs' : μ s = 0) :
    ∫⁻ x in s, f x ∂μ = 0 := by
  convert lintegral_zero_measure _
  exact Measure.restrict_eq_zero.2 hs'
#align measure_theory.set_lintegral_measure_zero MeasureTheory.set_lintegral_measure_zero

theorem lintegral_finset_sum' (s : Finset β) {f : β → α → ℝ≥0∞}
    (hf : ∀ b ∈ s, AEMeasurable (f b) μ) :
    ∫⁻ a, ∑ b in s, f b a ∂μ = ∑ b in s, ∫⁻ a, f b a ∂μ := by
  induction' s using Finset.induction_on with a s has ih
  · simp
  · simp only [Finset.sum_insert has]
    rw [Finset.forall_mem_insert] at hf
    rw [lintegral_add_left' hf.1, ih hf.2]
#align measure_theory.lintegral_finset_sum' MeasureTheory.lintegral_finset_sum'

theorem lintegral_finset_sum (s : Finset β) {f : β → α → ℝ≥0∞} (hf : ∀ b ∈ s, Measurable (f b)) :
    ∫⁻ a, ∑ b in s, f b a ∂μ = ∑ b in s, ∫⁻ a, f b a ∂μ :=
  lintegral_finset_sum' s fun b hb => (hf b hb).aemeasurable
#align measure_theory.lintegral_finset_sum MeasureTheory.lintegral_finset_sum

@[simp]
theorem lintegral_const_mul (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ :=
  calc
    ∫⁻ a, r * f a ∂μ = ∫⁻ a, ⨆ n, (const α r * eapprox f n) a ∂μ := by
      congr
      funext a
      rw [← iSup_eapprox_apply f hf, ENNReal.mul_iSup]
      rfl
    _ = ⨆ n, r * (eapprox f n).lintegral μ := by
      rw [lintegral_iSup]
      · congr
        funext n
        rw [← SimpleFunc.const_mul_lintegral, ← SimpleFunc.lintegral_eq_lintegral]
      · intro n
        exact SimpleFunc.measurable _
      · intro i j h a
        exact mul_le_mul_left' (monotone_eapprox _ h _) _
    _ = r * ∫⁻ a, f a ∂μ := by rw [← ENNReal.mul_iSup, lintegral_eq_iSup_eapprox_lintegral hf]
#align measure_theory.lintegral_const_mul MeasureTheory.lintegral_const_mul

theorem lintegral_const_mul'' (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ := by
  have A : ∫⁻ a, f a ∂μ = ∫⁻ a, hf.mk f a ∂μ := lintegral_congr_ae hf.ae_eq_mk
  have B : ∫⁻ a, r * f a ∂μ = ∫⁻ a, r * hf.mk f a ∂μ :=
    lintegral_congr_ae (EventuallyEq.fun_comp hf.ae_eq_mk _)
  rw [A, B, lintegral_const_mul _ hf.measurable_mk]
#align measure_theory.lintegral_const_mul'' MeasureTheory.lintegral_const_mul''

theorem lintegral_const_mul_le (r : ℝ≥0∞) (f : α → ℝ≥0∞) :
    (r * ∫⁻ a, f a ∂μ) ≤ ∫⁻ a, r * f a ∂μ := by
  rw [lintegral, ENNReal.mul_iSup]
  refine' iSup_le fun s => _
  rw [ENNReal.mul_iSup]
  simp only [iSup_le_iff]
  intro hs
  rw [← SimpleFunc.const_mul_lintegral, lintegral]
  refine' le_iSup_of_le (const α r * s) (le_iSup_of_le (fun x => _) le_rfl)
  exact mul_le_mul_left' (hs x) _
#align measure_theory.lintegral_const_mul_le MeasureTheory.lintegral_const_mul_le

theorem lintegral_const_mul' (r : ℝ≥0∞) (f : α → ℝ≥0∞) (hr : r ≠ ∞) :
    ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ := by
  by_cases h : r = 0
  · simp [h]
  apply le_antisymm _ (lintegral_const_mul_le r f)
  have rinv : r * r⁻¹ = 1 := ENNReal.mul_inv_cancel h hr
  have rinv' : r⁻¹ * r = 1 := by
    rw [mul_comm]
    exact rinv
  have := lintegral_const_mul_le (μ := μ) r⁻¹ fun x => r * f x
  simp? [(mul_assoc _ _ _).symm, rinv'] at this says
    simp only [(mul_assoc _ _ _).symm, rinv', one_mul] at this
  simpa [(mul_assoc _ _ _).symm, rinv] using mul_le_mul_left' this r
#align measure_theory.lintegral_const_mul' MeasureTheory.lintegral_const_mul'

theorem lintegral_mul_const (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a, f a * r ∂μ = (∫⁻ a, f a ∂μ) * r := by simp_rw [mul_comm, lintegral_const_mul r hf]
#align measure_theory.lintegral_mul_const MeasureTheory.lintegral_mul_const

theorem lintegral_mul_const'' (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∫⁻ a, f a * r ∂μ = (∫⁻ a, f a ∂μ) * r := by simp_rw [mul_comm, lintegral_const_mul'' r hf]
#align measure_theory.lintegral_mul_const'' MeasureTheory.lintegral_mul_const''

theorem lintegral_mul_const_le (r : ℝ≥0∞) (f : α → ℝ≥0∞) : (∫⁻ a, f a ∂μ) * r ≤ ∫⁻ a, f a * r ∂μ :=
  by simp_rw [mul_comm, lintegral_const_mul_le r f]
#align measure_theory.lintegral_mul_const_le MeasureTheory.lintegral_mul_const_le

theorem lintegral_mul_const' (r : ℝ≥0∞) (f : α → ℝ≥0∞) (hr : r ≠ ∞) :
    ∫⁻ a, f a * r ∂μ = (∫⁻ a, f a ∂μ) * r := by simp_rw [mul_comm, lintegral_const_mul' r f hr]
#align measure_theory.lintegral_mul_const' MeasureTheory.lintegral_mul_const'

/- A double integral of a product where each factor contains only one variable
  is a product of integrals -/
theorem lintegral_lintegral_mul {β} [MeasurableSpace β] {ν : Measure β} {f : α → ℝ≥0∞}
    {g : β → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g ν) :
    ∫⁻ x, ∫⁻ y, f x * g y ∂ν ∂μ = (∫⁻ x, f x ∂μ) * ∫⁻ y, g y ∂ν := by
  simp [lintegral_const_mul'' _ hg, lintegral_mul_const'' _ hf]
#align measure_theory.lintegral_lintegral_mul MeasureTheory.lintegral_lintegral_mul

-- TODO: Need a better way of rewriting inside of an integral
theorem lintegral_rw₁ {f f' : α → β} (h : f =ᵐ[μ] f') (g : β → ℝ≥0∞) :
    ∫⁻ a, g (f a) ∂μ = ∫⁻ a, g (f' a) ∂μ :=
  lintegral_congr_ae <| h.mono fun a h => by dsimp only; rw [h]
#align measure_theory.lintegral_rw₁ MeasureTheory.lintegral_rw₁

-- TODO: Need a better way of rewriting inside of an integral
theorem lintegral_rw₂ {f₁ f₁' : α → β} {f₂ f₂' : α → γ} (h₁ : f₁ =ᵐ[μ] f₁') (h₂ : f₂ =ᵐ[μ] f₂')
    (g : β → γ → ℝ≥0∞) : ∫⁻ a, g (f₁ a) (f₂ a) ∂μ = ∫⁻ a, g (f₁' a) (f₂' a) ∂μ :=
  lintegral_congr_ae <| h₁.mp <| h₂.mono fun _ h₂ h₁ => by dsimp only; rw [h₁, h₂]
#align measure_theory.lintegral_rw₂ MeasureTheory.lintegral_rw₂

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
theorem lintegral_indicator (f : α → ℝ≥0∞) {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f a ∂μ := by
  apply le_antisymm (lintegral_indicator_le f s)
  simp only [lintegral, ← restrict_lintegral_eq_lintegral_restrict _ hs, iSup_subtype']
  refine' iSup_mono' (Subtype.forall.2 fun φ hφ => _)
  refine' ⟨⟨φ.restrict s, fun x => _⟩, le_rfl⟩
  simp [hφ x, hs, indicator_le_indicator]
#align measure_theory.lintegral_indicator MeasureTheory.lintegral_indicator

theorem lintegral_indicator₀ (f : α → ℝ≥0∞) {s : Set α} (hs : NullMeasurableSet s μ) :
    ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f a ∂μ := by
  rw [← lintegral_congr_ae (indicator_ae_eq_of_ae_eq_set hs.toMeasurable_ae_eq),
    lintegral_indicator _ (measurableSet_toMeasurable _ _),
    Measure.restrict_congr_set hs.toMeasurable_ae_eq]
#align measure_theory.lintegral_indicator₀ MeasureTheory.lintegral_indicator₀

theorem lintegral_indicator_const_le (s : Set α) (c : ℝ≥0∞) :
    ∫⁻ a, s.indicator (fun _ => c) a ∂μ ≤ c * μ s :=
  (lintegral_indicator_le _ _).trans (set_lintegral_const s c).le

theorem lintegral_indicator_const₀ {s : Set α} (hs : NullMeasurableSet s μ) (c : ℝ≥0∞) :
    ∫⁻ a, s.indicator (fun _ => c) a ∂μ = c * μ s := by
  rw [lintegral_indicator₀ _ hs, set_lintegral_const]

theorem lintegral_indicator_const {s : Set α} (hs : MeasurableSet s) (c : ℝ≥0∞) :
    ∫⁻ a, s.indicator (fun _ => c) a ∂μ = c * μ s :=
  lintegral_indicator_const₀ hs.nullMeasurableSet c
#align measure_theory.lintegral_indicator_const MeasureTheory.lintegral_indicator_const

theorem set_lintegral_eq_const {f : α → ℝ≥0∞} (hf : Measurable f) (r : ℝ≥0∞) :
    ∫⁻ x in { x | f x = r }, f x ∂μ = r * μ { x | f x = r } := by
  have : ∀ᵐ x ∂μ, x ∈ { x | f x = r } → f x = r := ae_of_all μ fun _ hx => hx
  rw [set_lintegral_congr_fun _ this]
  rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  exact hf (measurableSet_singleton r)
#align measure_theory.set_lintegral_eq_const MeasureTheory.set_lintegral_eq_const

theorem lintegral_indicator_one_le (s : Set α) : ∫⁻ a, s.indicator 1 a ∂μ ≤ μ s :=
  (lintegral_indicator_const_le _ _).trans <| (one_mul _).le

@[simp]
theorem lintegral_indicator_one₀ (hs : NullMeasurableSet s μ) : ∫⁻ a, s.indicator 1 a ∂μ = μ s :=
  (lintegral_indicator_const₀ hs _).trans <| one_mul _

@[simp]
theorem lintegral_indicator_one (hs : MeasurableSet s) : ∫⁻ a, s.indicator 1 a ∂μ = μ s :=
  (lintegral_indicator_const hs _).trans <| one_mul _
#align measure_theory.lintegral_indicator_one MeasureTheory.lintegral_indicator_one

/-- A version of **Markov's inequality** for two functions. It doesn't follow from the standard
Markov's inequality because we only assume measurability of `g`, not `f`. -/
theorem lintegral_add_mul_meas_add_le_le_lintegral {f g : α → ℝ≥0∞} (hle : f ≤ᵐ[μ] g)
    (hg : AEMeasurable g μ) (ε : ℝ≥0∞) :
    ∫⁻ a, f a ∂μ + ε * μ { x | f x + ε ≤ g x } ≤ ∫⁻ a, g a ∂μ := by
  rcases exists_measurable_le_lintegral_eq μ f with ⟨φ, hφm, hφ_le, hφ_eq⟩
  calc
    ∫⁻ x, f x ∂μ + ε * μ { x | f x + ε ≤ g x } = ∫⁻ x, φ x ∂μ + ε * μ { x | f x + ε ≤ g x } :=
      by rw [hφ_eq]
    _ ≤ ∫⁻ x, φ x ∂μ + ε * μ { x | φ x + ε ≤ g x } := by
      gcongr
      exact fun x => (add_le_add_right (hφ_le _) _).trans
    _ = ∫⁻ x, φ x + indicator { x | φ x + ε ≤ g x } (fun _ => ε) x ∂μ := by
      rw [lintegral_add_left hφm, lintegral_indicator₀, set_lintegral_const]
      exact measurableSet_le (hφm.nullMeasurable.measurable'.add_const _) hg.nullMeasurable
    _ ≤ ∫⁻ x, g x ∂μ := lintegral_mono_ae (hle.mono fun x hx₁ => ?_)
  simp only [indicator_apply]; split_ifs with hx₂
  exacts [hx₂, (add_zero _).trans_le <| (hφ_le x).trans hx₁]
#align measure_theory.lintegral_add_mul_meas_add_le_le_lintegral MeasureTheory.lintegral_add_mul_meas_add_le_le_lintegral

/-- **Markov's inequality** also known as **Chebyshev's first inequality**. -/
theorem mul_meas_ge_le_lintegral₀ {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (ε : ℝ≥0∞) :
    ε * μ { x | ε ≤ f x } ≤ ∫⁻ a, f a ∂μ := by
  simpa only [lintegral_zero, zero_add] using
    lintegral_add_mul_meas_add_le_le_lintegral (ae_of_all _ fun x => zero_le (f x)) hf ε
#align measure_theory.mul_meas_ge_le_lintegral₀ MeasureTheory.mul_meas_ge_le_lintegral₀

/-- **Markov's inequality** also known as **Chebyshev's first inequality**. For a version assuming
`AEMeasurable`, see `mul_meas_ge_le_lintegral₀`. -/
theorem mul_meas_ge_le_lintegral {f : α → ℝ≥0∞} (hf : Measurable f) (ε : ℝ≥0∞) :
    ε * μ { x | ε ≤ f x } ≤ ∫⁻ a, f a ∂μ :=
  mul_meas_ge_le_lintegral₀ hf.aemeasurable ε
#align measure_theory.mul_meas_ge_le_lintegral MeasureTheory.mul_meas_ge_le_lintegral

lemma meas_le_lintegral₀ {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    {s : Set α} (hs : ∀ x ∈ s, 1 ≤ f x) : μ s ≤ ∫⁻ a, f a ∂μ := by
  apply le_trans _ (mul_meas_ge_le_lintegral₀ hf 1)
  rw [one_mul]
  exact measure_mono hs

lemma lintegral_le_meas {s : Set α} {f : α → ℝ≥0∞} (hf : ∀ a, f a ≤ 1) (h'f : ∀ a ∈ sᶜ, f a = 0) :
    ∫⁻ a, f a ∂μ ≤ μ s := by
  apply (lintegral_mono (fun x ↦ ?_)).trans (lintegral_indicator_one_le s)
  by_cases hx : x ∈ s
  · simpa [hx] using hf x
  · simpa [hx] using h'f x hx

theorem lintegral_eq_top_of_measure_eq_top_ne_zero {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hμf : μ {x | f x = ∞} ≠ 0) : ∫⁻ x, f x ∂μ = ∞ :=
  eq_top_iff.mpr <|
    calc
      ∞ = ∞ * μ { x | ∞ ≤ f x } := by simp [mul_eq_top, hμf]
      _ ≤ ∫⁻ x, f x ∂μ := mul_meas_ge_le_lintegral₀ hf ∞
#align measure_theory.lintegral_eq_top_of_measure_eq_top_ne_zero MeasureTheory.lintegral_eq_top_of_measure_eq_top_ne_zero

theorem setLintegral_eq_top_of_measure_eq_top_ne_zero (hf : AEMeasurable f (μ.restrict s))
    (hμf : μ ({x ∈ s | f x = ∞}) ≠ 0) : ∫⁻ x in s, f x ∂μ = ∞ :=
  lintegral_eq_top_of_measure_eq_top_ne_zero hf <|
    mt (eq_bot_mono <| by rw [← setOf_inter_eq_sep]; exact Measure.le_restrict_apply _ _) hμf
#align measure_theory.set_lintegral_eq_top_of_measure_eq_top_ne_zero MeasureTheory.setLintegral_eq_top_of_measure_eq_top_ne_zero

theorem measure_eq_top_of_lintegral_ne_top (hf : AEMeasurable f μ) (hμf : ∫⁻ x, f x ∂μ ≠ ∞) :
    μ {x | f x = ∞} = 0 :=
  of_not_not fun h => hμf <| lintegral_eq_top_of_measure_eq_top_ne_zero hf h
#align measure_theory.measure_eq_top_of_lintegral_ne_top MeasureTheory.measure_eq_top_of_lintegral_ne_top

theorem measure_eq_top_of_setLintegral_ne_top (hf : AEMeasurable f (μ.restrict s))
    (hμf : ∫⁻ x in s, f x ∂μ ≠ ∞) : μ ({x ∈ s | f x = ∞}) = 0 :=
  of_not_not fun h => hμf <| setLintegral_eq_top_of_measure_eq_top_ne_zero hf h
#align measure_theory.measure_eq_top_of_set_lintegral_ne_top MeasureTheory.measure_eq_top_of_setLintegral_ne_top

/-- **Markov's inequality** also known as **Chebyshev's first inequality**. -/
theorem meas_ge_le_lintegral_div {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) {ε : ℝ≥0∞} (hε : ε ≠ 0)
    (hε' : ε ≠ ∞) : μ { x | ε ≤ f x } ≤ (∫⁻ a, f a ∂μ) / ε :=
  (ENNReal.le_div_iff_mul_le (Or.inl hε) (Or.inl hε')).2 <| by
    rw [mul_comm]
    exact mul_meas_ge_le_lintegral₀ hf ε
#align measure_theory.meas_ge_le_lintegral_div MeasureTheory.meas_ge_le_lintegral_div

theorem ae_eq_of_ae_le_of_lintegral_le {f g : α → ℝ≥0∞} (hfg : f ≤ᵐ[μ] g) (hf : ∫⁻ x, f x ∂μ ≠ ∞)
    (hg : AEMeasurable g μ) (hgf : ∫⁻ x, g x ∂μ ≤ ∫⁻ x, f x ∂μ) : f =ᵐ[μ] g := by
  have : ∀ n : ℕ, ∀ᵐ x ∂μ, g x < f x + (n : ℝ≥0∞)⁻¹ := by
    intro n
    simp only [ae_iff, not_lt]
    have : ∫⁻ x, f x ∂μ + (↑n)⁻¹ * μ { x : α | f x + (n : ℝ≥0∞)⁻¹ ≤ g x } ≤ ∫⁻ x, f x ∂μ :=
      (lintegral_add_mul_meas_add_le_le_lintegral hfg hg n⁻¹).trans hgf
    rw [(ENNReal.cancel_of_ne hf).add_le_iff_nonpos_right, nonpos_iff_eq_zero, mul_eq_zero] at this
    exact this.resolve_left (ENNReal.inv_ne_zero.2 (ENNReal.nat_ne_top _))
  refine' hfg.mp ((ae_all_iff.2 this).mono fun x hlt hle => hle.antisymm _)
  suffices Tendsto (fun n : ℕ => f x + (n : ℝ≥0∞)⁻¹) atTop (𝓝 (f x)) from
    ge_of_tendsto' this fun i => (hlt i).le
  simpa only [inv_top, add_zero] using
    tendsto_const_nhds.add (ENNReal.tendsto_inv_iff.2 ENNReal.tendsto_nat_nhds_top)
#align measure_theory.ae_eq_of_ae_le_of_lintegral_le MeasureTheory.ae_eq_of_ae_le_of_lintegral_le

@[simp]
theorem lintegral_eq_zero_iff' {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0 :=
  have : ∫⁻ _ : α, 0 ∂μ ≠ ∞ := by simp [lintegral_zero, zero_ne_top]
  ⟨fun h =>
    (ae_eq_of_ae_le_of_lintegral_le (ae_of_all _ <| zero_le f) this hf
        (h.trans lintegral_zero.symm).le).symm,
    fun h => (lintegral_congr_ae h).trans lintegral_zero⟩
#align measure_theory.lintegral_eq_zero_iff' MeasureTheory.lintegral_eq_zero_iff'

@[simp]
theorem lintegral_eq_zero_iff {f : α → ℝ≥0∞} (hf : Measurable f) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0 :=
  lintegral_eq_zero_iff' hf.aemeasurable
#align measure_theory.lintegral_eq_zero_iff MeasureTheory.lintegral_eq_zero_iff

theorem lintegral_pos_iff_support {f : α → ℝ≥0∞} (hf : Measurable f) :
    (0 < ∫⁻ a, f a ∂μ) ↔ 0 < μ (Function.support f) := by
  simp [pos_iff_ne_zero, hf, Filter.EventuallyEq, ae_iff, Function.support]
#align measure_theory.lintegral_pos_iff_support MeasureTheory.lintegral_pos_iff_support

/-- Weaker version of the monotone convergence theorem-/
theorem lintegral_iSup_ae {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, Measurable (f n))
    (h_mono : ∀ n, ∀ᵐ a ∂μ, f n a ≤ f n.succ a) : ∫⁻ a, ⨆ n, f n a ∂μ = ⨆ n, ∫⁻ a, f n a ∂μ :=
  let ⟨s, hs⟩ := exists_measurable_superset_of_null (ae_iff.1 (ae_all_iff.2 h_mono))
  let g n a := if a ∈ s then 0 else f n a
  have g_eq_f : ∀ᵐ a ∂μ, ∀ n, g n a = f n a :=
    (measure_zero_iff_ae_nmem.1 hs.2.2).mono fun a ha n => if_neg ha
  calc
    ∫⁻ a, ⨆ n, f n a ∂μ = ∫⁻ a, ⨆ n, g n a ∂μ :=
      lintegral_congr_ae <| g_eq_f.mono fun a ha => by simp only [ha]
    _ = ⨆ n, ∫⁻ a, g n a ∂μ :=
      (lintegral_iSup (fun n => measurable_const.piecewise hs.2.1 (hf n))
        (monotone_nat_of_le_succ fun n a =>
          _root_.by_cases (fun h : a ∈ s => by simp [g, if_pos h]) fun h : a ∉ s => by
            simp only [g, if_neg h]; have := hs.1; rw [subset_def] at this; have := mt (this a) h
            simp only [Classical.not_not, mem_setOf_eq] at this; exact this n))
    _ = ⨆ n, ∫⁻ a, f n a ∂μ := by simp only [lintegral_congr_ae (g_eq_f.mono fun _a ha => ha _)]
#align measure_theory.lintegral_supr_ae MeasureTheory.lintegral_iSup_ae

theorem lintegral_sub' {f g : α → ℝ≥0∞} (hg : AEMeasurable g μ) (hg_fin : ∫⁻ a, g a ∂μ ≠ ∞)
    (h_le : g ≤ᵐ[μ] f) : ∫⁻ a, f a - g a ∂μ = ∫⁻ a, f a ∂μ - ∫⁻ a, g a ∂μ := by
  refine' ENNReal.eq_sub_of_add_eq hg_fin _
  rw [← lintegral_add_right' _ hg]
  exact lintegral_congr_ae (h_le.mono fun x hx => tsub_add_cancel_of_le hx)
#align measure_theory.lintegral_sub' MeasureTheory.lintegral_sub'

theorem lintegral_sub {f g : α → ℝ≥0∞} (hg : Measurable g) (hg_fin : ∫⁻ a, g a ∂μ ≠ ∞)
    (h_le : g ≤ᵐ[μ] f) : ∫⁻ a, f a - g a ∂μ = ∫⁻ a, f a ∂μ - ∫⁻ a, g a ∂μ :=
  lintegral_sub' hg.aemeasurable hg_fin h_le
#align measure_theory.lintegral_sub MeasureTheory.lintegral_sub

theorem lintegral_sub_le' (f g : α → ℝ≥0∞) (hf : AEMeasurable f μ) :
    (∫⁻ x, g x ∂μ - ∫⁻ x, f x ∂μ) ≤ ∫⁻ x, g x - f x ∂μ := by
  rw [tsub_le_iff_right]
  by_cases hfi : ∫⁻ x, f x ∂μ = ∞
  · rw [hfi, add_top]
    exact le_top
  · rw [← lintegral_add_right' _ hf]
    gcongr
    exact le_tsub_add
#align measure_theory.lintegral_sub_le' MeasureTheory.lintegral_sub_le'

theorem lintegral_sub_le (f g : α → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, g x ∂μ - ∫⁻ x, f x ∂μ) ≤ ∫⁻ x, g x - f x ∂μ :=
  lintegral_sub_le' f g hf.aemeasurable
#align measure_theory.lintegral_sub_le MeasureTheory.lintegral_sub_le

theorem lintegral_strict_mono_of_ae_le_of_frequently_ae_lt {f g : α → ℝ≥0∞} (hg : AEMeasurable g μ)
    (hfi : ∫⁻ x, f x ∂μ ≠ ∞) (h_le : f ≤ᵐ[μ] g) (h : ∃ᵐ x ∂μ, f x ≠ g x) :
    ∫⁻ x, f x ∂μ < ∫⁻ x, g x ∂μ := by
  contrapose! h
  simp only [not_frequently, Ne.def, Classical.not_not]
  exact ae_eq_of_ae_le_of_lintegral_le h_le hfi hg h
#align measure_theory.lintegral_strict_mono_of_ae_le_of_frequently_ae_lt MeasureTheory.lintegral_strict_mono_of_ae_le_of_frequently_ae_lt

theorem lintegral_strict_mono_of_ae_le_of_ae_lt_on {f g : α → ℝ≥0∞} (hg : AEMeasurable g μ)
    (hfi : ∫⁻ x, f x ∂μ ≠ ∞) (h_le : f ≤ᵐ[μ] g) {s : Set α} (hμs : μ s ≠ 0)
    (h : ∀ᵐ x ∂μ, x ∈ s → f x < g x) : ∫⁻ x, f x ∂μ < ∫⁻ x, g x ∂μ :=
  lintegral_strict_mono_of_ae_le_of_frequently_ae_lt hg hfi h_le <|
    ((frequently_ae_mem_iff.2 hμs).and_eventually h).mono fun _x hx => (hx.2 hx.1).ne
#align measure_theory.lintegral_strict_mono_of_ae_le_of_ae_lt_on MeasureTheory.lintegral_strict_mono_of_ae_le_of_ae_lt_on

theorem lintegral_strict_mono {f g : α → ℝ≥0∞} (hμ : μ ≠ 0) (hg : AEMeasurable g μ)
    (hfi : ∫⁻ x, f x ∂μ ≠ ∞) (h : ∀ᵐ x ∂μ, f x < g x) : ∫⁻ x, f x ∂μ < ∫⁻ x, g x ∂μ := by
  rw [Ne.def, ← Measure.measure_univ_eq_zero] at hμ
  refine' lintegral_strict_mono_of_ae_le_of_ae_lt_on hg hfi (ae_le_of_ae_lt h) hμ _
  simpa using h
#align measure_theory.lintegral_strict_mono MeasureTheory.lintegral_strict_mono

theorem set_lintegral_strict_mono {f g : α → ℝ≥0∞} {s : Set α} (hsm : MeasurableSet s)
    (hs : μ s ≠ 0) (hg : Measurable g) (hfi : ∫⁻ x in s, f x ∂μ ≠ ∞)
    (h : ∀ᵐ x ∂μ, x ∈ s → f x < g x) : ∫⁻ x in s, f x ∂μ < ∫⁻ x in s, g x ∂μ :=
  lintegral_strict_mono (by simp [hs]) hg.aemeasurable hfi ((ae_restrict_iff' hsm).mpr h)
#align measure_theory.set_lintegral_strict_mono MeasureTheory.set_lintegral_strict_mono

/-- Monotone convergence theorem for nonincreasing sequences of functions -/
theorem lintegral_iInf_ae {f : ℕ → α → ℝ≥0∞} (h_meas : ∀ n, Measurable (f n))
    (h_mono : ∀ n : ℕ, f n.succ ≤ᵐ[μ] f n) (h_fin : ∫⁻ a, f 0 a ∂μ ≠ ∞) :
    ∫⁻ a, ⨅ n, f n a ∂μ = ⨅ n, ∫⁻ a, f n a ∂μ :=
  have fn_le_f0 : ∫⁻ a, ⨅ n, f n a ∂μ ≤ ∫⁻ a, f 0 a ∂μ :=
    lintegral_mono fun a => iInf_le_of_le 0 le_rfl
  have fn_le_f0' : ⨅ n, ∫⁻ a, f n a ∂μ ≤ ∫⁻ a, f 0 a ∂μ := iInf_le_of_le 0 le_rfl
  (ENNReal.sub_right_inj h_fin fn_le_f0 fn_le_f0').1 <|
    show ∫⁻ a, f 0 a ∂μ - ∫⁻ a, ⨅ n, f n a ∂μ = ∫⁻ a, f 0 a ∂μ - ⨅ n, ∫⁻ a, f n a ∂μ from
      calc
        ∫⁻ a, f 0 a ∂μ - ∫⁻ a, ⨅ n, f n a ∂μ = ∫⁻ a, f 0 a - ⨅ n, f n a ∂μ :=
          (lintegral_sub (measurable_iInf h_meas)
              (ne_top_of_le_ne_top h_fin <| lintegral_mono fun a => iInf_le _ _)
              (ae_of_all _ fun a => iInf_le _ _)).symm
        _ = ∫⁻ a, ⨆ n, f 0 a - f n a ∂μ := (congr rfl (funext fun a => ENNReal.sub_iInf))
        _ = ⨆ n, ∫⁻ a, f 0 a - f n a ∂μ :=
          (lintegral_iSup_ae (fun n => (h_meas 0).sub (h_meas n)) fun n =>
            (h_mono n).mono fun a ha => tsub_le_tsub le_rfl ha)
        _ = ⨆ n, ∫⁻ a, f 0 a ∂μ - ∫⁻ a, f n a ∂μ :=
          (have h_mono : ∀ᵐ a ∂μ, ∀ n : ℕ, f n.succ a ≤ f n a := ae_all_iff.2 h_mono
          have h_mono : ∀ n, ∀ᵐ a ∂μ, f n a ≤ f 0 a := fun n =>
            h_mono.mono fun a h => by
              induction' n with n ih
              · exact le_rfl
              · exact le_trans (h n) ih
          congr_arg iSup <|
            funext fun n =>
              lintegral_sub (h_meas _) (ne_top_of_le_ne_top h_fin <| lintegral_mono_ae <| h_mono n)
                (h_mono n))
        _ = ∫⁻ a, f 0 a ∂μ - ⨅ n, ∫⁻ a, f n a ∂μ := ENNReal.sub_iInf.symm
#align measure_theory.lintegral_infi_ae MeasureTheory.lintegral_iInf_ae

/-- Monotone convergence theorem for nonincreasing sequences of functions -/
theorem lintegral_iInf {f : ℕ → α → ℝ≥0∞} (h_meas : ∀ n, Measurable (f n)) (h_anti : Antitone f)
    (h_fin : ∫⁻ a, f 0 a ∂μ ≠ ∞) : ∫⁻ a, ⨅ n, f n a ∂μ = ⨅ n, ∫⁻ a, f n a ∂μ :=
  lintegral_iInf_ae h_meas (fun n => ae_of_all _ <| h_anti n.le_succ) h_fin
#align measure_theory.lintegral_infi MeasureTheory.lintegral_iInf

theorem lintegral_iInf' {f : ℕ → α → ℝ≥0∞} (h_meas : ∀ n, AEMeasurable (f n) μ)
    (h_anti : ∀ᵐ a ∂μ, Antitone (fun i ↦ f i a)) (h_fin : ∫⁻ a, f 0 a ∂μ ≠ ∞) :
    ∫⁻ a, ⨅ n, f n a ∂μ = ⨅ n, ∫⁻ a, f n a ∂μ := by
  simp_rw [← iInf_apply]
  let p : α → (ℕ → ℝ≥0∞) → Prop := fun _ f' => Antitone f'
  have hp : ∀ᵐ x ∂μ, p x fun i => f i x := h_anti
  have h_ae_seq_mono : Antitone (aeSeq h_meas p) := by
    intro n m hnm x
    by_cases hx : x ∈ aeSeqSet h_meas p
    · exact aeSeq.prop_of_mem_aeSeqSet h_meas hx hnm
    · simp only [aeSeq, hx, if_false]
      exact le_rfl
  rw [lintegral_congr_ae (aeSeq.iInf h_meas hp).symm]
  simp_rw [iInf_apply]
  rw [lintegral_iInf (aeSeq.measurable h_meas p) h_ae_seq_mono]
  · congr
    exact funext fun n ↦ lintegral_congr_ae (aeSeq.aeSeq_n_eq_fun_n_ae h_meas hp n)
  · rwa [lintegral_congr_ae (aeSeq.aeSeq_n_eq_fun_n_ae h_meas hp 0)]

/-- Monotone convergence for an infimum over a directed family and indexed by a countable type -/
theorem lintegral_iInf_directed_of_measurable {mα : MeasurableSpace α} [Countable β]
    {f : β → α → ℝ≥0∞} {μ : Measure α} (hμ : μ ≠ 0) (hf : ∀ b, Measurable (f b))
    (hf_int : ∀ b, ∫⁻ a, f b a ∂μ ≠ ∞) (h_directed : Directed (· ≥ ·) f) :
    ∫⁻ a, ⨅ b, f b a ∂μ = ⨅ b, ∫⁻ a, f b a ∂μ := by
  cases nonempty_encodable β
  cases isEmpty_or_nonempty β
  · -- Porting note: the next `simp only` doesn't do anything, so added a workaround below.
    -- simp only [WithTop.iInf_empty, lintegral_const]
    conv =>
      lhs
      congr
      · skip
      · ext x
        rw [WithTop.iInf_empty]
    rw [WithTop.iInf_empty, lintegral_const]
    rw [ENNReal.top_mul', if_neg]
    simp only [Measure.measure_univ_eq_zero, hμ, not_false_iff]
  inhabit β
  have : ∀ a, ⨅ b, f b a = ⨅ n, f (h_directed.sequence f n) a := by
    refine' fun a =>
      le_antisymm (le_iInf fun n => iInf_le _ _)
        (le_iInf fun b => iInf_le_of_le (Encodable.encode b + 1) _)
    exact h_directed.sequence_le b a
  -- Porting note: used `∘` below to deal with its reduced reducibility
  calc
    ∫⁻ a, ⨅ b, f b a ∂μ
    _ = ∫⁻ a, ⨅ n, (f ∘ h_directed.sequence f) n a ∂μ := by simp only [this, Function.comp_apply]
    _ = ⨅ n, ∫⁻ a, (f ∘ h_directed.sequence f) n a ∂μ := by
      rw [lintegral_iInf ?_ h_directed.sequence_anti]
      · exact hf_int _
      · exact fun n => hf _
    _ = ⨅ b, ∫⁻ a, f b a ∂μ := by
      refine' le_antisymm (le_iInf fun b => _) (le_iInf fun n => _)
      · exact iInf_le_of_le (Encodable.encode b + 1) (lintegral_mono <| h_directed.sequence_le b)
      · exact iInf_le (fun b => ∫⁻ a, f b a ∂μ) _
#align lintegral_infi_directed_of_measurable MeasureTheory.lintegral_iInf_directed_of_measurable

/-- Known as Fatou's lemma, version with `AEMeasurable` functions -/
theorem lintegral_liminf_le' {f : ℕ → α → ℝ≥0∞} (h_meas : ∀ n, AEMeasurable (f n) μ) :
    ∫⁻ a, liminf (fun n => f n a) atTop ∂μ ≤ liminf (fun n => ∫⁻ a, f n a ∂μ) atTop :=
  calc
    ∫⁻ a, liminf (fun n => f n a) atTop ∂μ = ∫⁻ a, ⨆ n : ℕ, ⨅ i ≥ n, f i a ∂μ := by
      simp only [liminf_eq_iSup_iInf_of_nat]
    _ = ⨆ n : ℕ, ∫⁻ a, ⨅ i ≥ n, f i a ∂μ :=
      (lintegral_iSup' (fun n => aemeasurable_biInf _ (to_countable _) (fun i _ ↦ h_meas i))
        (ae_of_all μ fun a n m hnm => iInf_le_iInf_of_subset fun i hi => le_trans hnm hi))
    _ ≤ ⨆ n : ℕ, ⨅ i ≥ n, ∫⁻ a, f i a ∂μ := (iSup_mono fun n => le_iInf₂_lintegral _)
    _ = atTop.liminf fun n => ∫⁻ a, f n a ∂μ := Filter.liminf_eq_iSup_iInf_of_nat.symm
#align measure_theory.lintegral_liminf_le' MeasureTheory.lintegral_liminf_le'

/-- Known as Fatou's lemma -/
theorem lintegral_liminf_le {f : ℕ → α → ℝ≥0∞} (h_meas : ∀ n, Measurable (f n)) :
    ∫⁻ a, liminf (fun n => f n a) atTop ∂μ ≤ liminf (fun n => ∫⁻ a, f n a ∂μ) atTop :=
  lintegral_liminf_le' fun n => (h_meas n).aemeasurable
#align measure_theory.lintegral_liminf_le MeasureTheory.lintegral_liminf_le

theorem limsup_lintegral_le {f : ℕ → α → ℝ≥0∞} {g : α → ℝ≥0∞} (hf_meas : ∀ n, Measurable (f n))
    (h_bound : ∀ n, f n ≤ᵐ[μ] g) (h_fin : ∫⁻ a, g a ∂μ ≠ ∞) :
    limsup (fun n => ∫⁻ a, f n a ∂μ) atTop ≤ ∫⁻ a, limsup (fun n => f n a) atTop ∂μ :=
  calc
    limsup (fun n => ∫⁻ a, f n a ∂μ) atTop = ⨅ n : ℕ, ⨆ i ≥ n, ∫⁻ a, f i a ∂μ :=
      limsup_eq_iInf_iSup_of_nat
    _ ≤ ⨅ n : ℕ, ∫⁻ a, ⨆ i ≥ n, f i a ∂μ := (iInf_mono fun n => iSup₂_lintegral_le _)
    _ = ∫⁻ a, ⨅ n : ℕ, ⨆ i ≥ n, f i a ∂μ := by
      refine' (lintegral_iInf _ _ _).symm
      · intro n
        exact measurable_biSup _ (to_countable _) (fun i _ ↦ hf_meas i)
      · intro n m hnm a
        exact iSup_le_iSup_of_subset fun i hi => le_trans hnm hi
      · refine' ne_top_of_le_ne_top h_fin (lintegral_mono_ae _)
        refine' (ae_all_iff.2 h_bound).mono fun n hn => _
        exact iSup_le fun i => iSup_le fun _ => hn i
    _ = ∫⁻ a, limsup (fun n => f n a) atTop ∂μ := by simp only [limsup_eq_iInf_iSup_of_nat]
#align measure_theory.limsup_lintegral_le MeasureTheory.limsup_lintegral_le

/-- Dominated convergence theorem for nonnegative functions -/
theorem tendsto_lintegral_of_dominated_convergence {F : ℕ → α → ℝ≥0∞} {f : α → ℝ≥0∞}
    (bound : α → ℝ≥0∞) (hF_meas : ∀ n, Measurable (F n)) (h_bound : ∀ n, F n ≤ᵐ[μ] bound)
    (h_fin : ∫⁻ a, bound a ∂μ ≠ ∞) (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => ∫⁻ a, F n a ∂μ) atTop (𝓝 (∫⁻ a, f a ∂μ)) :=
  tendsto_of_le_liminf_of_limsup_le
    (calc
      ∫⁻ a, f a ∂μ = ∫⁻ a, liminf (fun n : ℕ => F n a) atTop ∂μ :=
        lintegral_congr_ae <| h_lim.mono fun a h => h.liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ a, F n a ∂μ) atTop := lintegral_liminf_le hF_meas
      )
    (calc
      limsup (fun n : ℕ => ∫⁻ a, F n a ∂μ) atTop ≤ ∫⁻ a, limsup (fun n => F n a) atTop ∂μ :=
        limsup_lintegral_le hF_meas h_bound h_fin
      _ = ∫⁻ a, f a ∂μ := lintegral_congr_ae <| h_lim.mono fun a h => h.limsup_eq
      )
#align measure_theory.tendsto_lintegral_of_dominated_convergence MeasureTheory.tendsto_lintegral_of_dominated_convergence

/-- Dominated convergence theorem for nonnegative functions which are just almost everywhere
measurable. -/
theorem tendsto_lintegral_of_dominated_convergence' {F : ℕ → α → ℝ≥0∞} {f : α → ℝ≥0∞}
    (bound : α → ℝ≥0∞) (hF_meas : ∀ n, AEMeasurable (F n) μ) (h_bound : ∀ n, F n ≤ᵐ[μ] bound)
    (h_fin : ∫⁻ a, bound a ∂μ ≠ ∞) (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => ∫⁻ a, F n a ∂μ) atTop (𝓝 (∫⁻ a, f a ∂μ)) := by
  have : ∀ n, ∫⁻ a, F n a ∂μ = ∫⁻ a, (hF_meas n).mk (F n) a ∂μ := fun n =>
    lintegral_congr_ae (hF_meas n).ae_eq_mk
  simp_rw [this]
  apply
    tendsto_lintegral_of_dominated_convergence bound (fun n => (hF_meas n).measurable_mk) _ h_fin
  · have : ∀ n, ∀ᵐ a ∂μ, (hF_meas n).mk (F n) a = F n a := fun n => (hF_meas n).ae_eq_mk.symm
    have : ∀ᵐ a ∂μ, ∀ n, (hF_meas n).mk (F n) a = F n a := ae_all_iff.mpr this
    filter_upwards [this, h_lim] with a H H'
    simp_rw [H]
    exact H'
  · intro n
    filter_upwards [h_bound n, (hF_meas n).ae_eq_mk] with a H H'
    rwa [H'] at H
#align measure_theory.tendsto_lintegral_of_dominated_convergence' MeasureTheory.tendsto_lintegral_of_dominated_convergence'

/-- Dominated convergence theorem for filters with a countable basis -/
theorem tendsto_lintegral_filter_of_dominated_convergence {ι} {l : Filter ι}
    [l.IsCountablyGenerated] {F : ι → α → ℝ≥0∞} {f : α → ℝ≥0∞} (bound : α → ℝ≥0∞)
    (hF_meas : ∀ᶠ n in l, Measurable (F n)) (h_bound : ∀ᶠ n in l, ∀ᵐ a ∂μ, F n a ≤ bound a)
    (h_fin : ∫⁻ a, bound a ∂μ ≠ ∞) (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) l (𝓝 (f a))) :
    Tendsto (fun n => ∫⁻ a, F n a ∂μ) l (𝓝 <| ∫⁻ a, f a ∂μ) := by
  rw [tendsto_iff_seq_tendsto]
  intro x xl
  have hxl := by
    rw [tendsto_atTop'] at xl
    exact xl
  have h := inter_mem hF_meas h_bound
  replace h := hxl _ h
  rcases h with ⟨k, h⟩
  rw [← tendsto_add_atTop_iff_nat k]
  refine' tendsto_lintegral_of_dominated_convergence _ _ _ _ _
  · exact bound
  · intro
    refine' (h _ _).1
    exact Nat.le_add_left _ _
  · intro
    refine' (h _ _).2
    exact Nat.le_add_left _ _
  · assumption
  · refine' h_lim.mono fun a h_lim => _
    apply @Tendsto.comp _ _ _ (fun n => x (n + k)) fun n => F n a
    · assumption
    rw [tendsto_add_atTop_iff_nat]
    assumption
#align measure_theory.tendsto_lintegral_filter_of_dominated_convergence MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence

theorem lintegral_tendsto_of_tendsto_of_antitone {f : ℕ → α → ℝ≥0∞} {F : α → ℝ≥0∞}
    (hf : ∀ n, AEMeasurable (f n) μ) (h_anti : ∀ᵐ x ∂μ, Antitone fun n ↦ f n x)
    (h0 : ∫⁻ a, f 0 a ∂μ ≠ ∞)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (F x))) :
    Tendsto (fun n ↦ ∫⁻ x, f n x ∂μ) atTop (𝓝 (∫⁻ x, F x ∂μ)) := by
  have : Antitone fun n ↦ ∫⁻ x, f n x ∂μ := fun i j hij ↦
    lintegral_mono_ae (h_anti.mono fun x hx ↦ hx hij)
  suffices key : ∫⁻ x, F x ∂μ = ⨅ n, ∫⁻ x, f n x ∂μ by
    rw [key]
    exact tendsto_atTop_iInf this
  rw [← lintegral_iInf' hf h_anti h0]
  refine lintegral_congr_ae ?_
  filter_upwards [h_anti, h_tendsto] with _ hx_anti hx_tendsto
    using tendsto_nhds_unique hx_tendsto (tendsto_atTop_iInf hx_anti)

section

open Encodable

/-- Monotone convergence for a supremum over a directed family and indexed by a countable type -/
theorem lintegral_iSup_directed_of_measurable [Countable β] {f : β → α → ℝ≥0∞}
    (hf : ∀ b, Measurable (f b)) (h_directed : Directed (· ≤ ·) f) :
    ∫⁻ a, ⨆ b, f b a ∂μ = ⨆ b, ∫⁻ a, f b a ∂μ := by
  cases nonempty_encodable β
  cases isEmpty_or_nonempty β
  · simp [iSup_of_empty]
  inhabit β
  have : ∀ a, ⨆ b, f b a = ⨆ n, f (h_directed.sequence f n) a := by
    intro a
    refine' le_antisymm (iSup_le fun b => _) (iSup_le fun n => le_iSup (fun n => f n a) _)
    exact le_iSup_of_le (encode b + 1) (h_directed.le_sequence b a)
  calc
    ∫⁻ a, ⨆ b, f b a ∂μ = ∫⁻ a, ⨆ n, f (h_directed.sequence f n) a ∂μ := by simp only [this]
    _ = ⨆ n, ∫⁻ a, f (h_directed.sequence f n) a ∂μ :=
      (lintegral_iSup (fun n => hf _) h_directed.sequence_mono)
    _ = ⨆ b, ∫⁻ a, f b a ∂μ := by
      refine' le_antisymm (iSup_le fun n => _) (iSup_le fun b => _)
      · exact le_iSup (fun b => ∫⁻ a, f b a ∂μ) _
      · exact le_iSup_of_le (encode b + 1) (lintegral_mono <| h_directed.le_sequence b)
#align measure_theory.lintegral_supr_directed_of_measurable MeasureTheory.lintegral_iSup_directed_of_measurable

/-- Monotone convergence for a supremum over a directed family and indexed by a countable type. -/
theorem lintegral_iSup_directed [Countable β] {f : β → α → ℝ≥0∞} (hf : ∀ b, AEMeasurable (f b) μ)
    (h_directed : Directed (· ≤ ·) f) : ∫⁻ a, ⨆ b, f b a ∂μ = ⨆ b, ∫⁻ a, f b a ∂μ := by
  simp_rw [← iSup_apply]
  let p : α → (β → ENNReal) → Prop := fun x f' => Directed LE.le f'
  have hp : ∀ᵐ x ∂μ, p x fun i => f i x := by
    filter_upwards [] with x i j
    obtain ⟨z, hz₁, hz₂⟩ := h_directed i j
    exact ⟨z, hz₁ x, hz₂ x⟩
  have h_ae_seq_directed : Directed LE.le (aeSeq hf p) := by
    intro b₁ b₂
    obtain ⟨z, hz₁, hz₂⟩ := h_directed b₁ b₂
    refine' ⟨z, _, _⟩ <;>
      · intro x
        by_cases hx : x ∈ aeSeqSet hf p
        · repeat' rw [aeSeq.aeSeq_eq_fun_of_mem_aeSeqSet hf hx]
          apply_rules [hz₁, hz₂]
        · simp only [aeSeq, hx, if_false]
          exact le_rfl
  convert lintegral_iSup_directed_of_measurable (aeSeq.measurable hf p) h_ae_seq_directed using 1
  · simp_rw [← iSup_apply]
    rw [lintegral_congr_ae (aeSeq.iSup hf hp).symm]
  · congr 1
    ext1 b
    rw [lintegral_congr_ae]
    apply EventuallyEq.symm
    exact aeSeq.aeSeq_n_eq_fun_n_ae hf hp _
#align measure_theory.lintegral_supr_directed MeasureTheory.lintegral_iSup_directed

end

theorem lintegral_tsum [Countable β] {f : β → α → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) μ) :
    ∫⁻ a, ∑' i, f i a ∂μ = ∑' i, ∫⁻ a, f i a ∂μ := by
  simp only [ENNReal.tsum_eq_iSup_sum]
  rw [lintegral_iSup_directed]
  · simp [lintegral_finset_sum' _ fun i _ => hf i]
  · intro b
    exact Finset.aemeasurable_sum _ fun i _ => hf i
  · intro s t
    use s ∪ t
    constructor
    · exact fun a => Finset.sum_le_sum_of_subset (Finset.subset_union_left _ _)
    · exact fun a => Finset.sum_le_sum_of_subset (Finset.subset_union_right _ _)
#align measure_theory.lintegral_tsum MeasureTheory.lintegral_tsum

open Measure

theorem lintegral_iUnion₀ [Countable β] {s : β → Set α} (hm : ∀ i, NullMeasurableSet (s i) μ)
    (hd : Pairwise (AEDisjoint μ on s)) (f : α → ℝ≥0∞) :
    ∫⁻ a in ⋃ i, s i, f a ∂μ = ∑' i, ∫⁻ a in s i, f a ∂μ := by
  simp only [Measure.restrict_iUnion_ae hd hm, lintegral_sum_measure]
#align measure_theory.lintegral_Union₀ MeasureTheory.lintegral_iUnion₀

theorem lintegral_iUnion [Countable β] {s : β → Set α} (hm : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (f : α → ℝ≥0∞) :
    ∫⁻ a in ⋃ i, s i, f a ∂μ = ∑' i, ∫⁻ a in s i, f a ∂μ :=
  lintegral_iUnion₀ (fun i => (hm i).nullMeasurableSet) hd.aedisjoint f
#align measure_theory.lintegral_Union MeasureTheory.lintegral_iUnion

theorem lintegral_biUnion₀ {t : Set β} {s : β → Set α} (ht : t.Countable)
    (hm : ∀ i ∈ t, NullMeasurableSet (s i) μ) (hd : t.Pairwise (AEDisjoint μ on s)) (f : α → ℝ≥0∞) :
    ∫⁻ a in ⋃ i ∈ t, s i, f a ∂μ = ∑' i : t, ∫⁻ a in s i, f a ∂μ := by
  haveI := ht.toEncodable
  rw [biUnion_eq_iUnion, lintegral_iUnion₀ (SetCoe.forall'.1 hm) (hd.subtype _ _)]
#align measure_theory.lintegral_bUnion₀ MeasureTheory.lintegral_biUnion₀

theorem lintegral_biUnion {t : Set β} {s : β → Set α} (ht : t.Countable)
    (hm : ∀ i ∈ t, MeasurableSet (s i)) (hd : t.PairwiseDisjoint s) (f : α → ℝ≥0∞) :
    ∫⁻ a in ⋃ i ∈ t, s i, f a ∂μ = ∑' i : t, ∫⁻ a in s i, f a ∂μ :=
  lintegral_biUnion₀ ht (fun i hi => (hm i hi).nullMeasurableSet) hd.aedisjoint f
#align measure_theory.lintegral_bUnion MeasureTheory.lintegral_biUnion

theorem lintegral_biUnion_finset₀ {s : Finset β} {t : β → Set α}
    (hd : Set.Pairwise (↑s) (AEDisjoint μ on t)) (hm : ∀ b ∈ s, NullMeasurableSet (t b) μ)
    (f : α → ℝ≥0∞) : ∫⁻ a in ⋃ b ∈ s, t b, f a ∂μ = ∑ b in s, ∫⁻ a in t b, f a ∂μ := by
  simp only [← Finset.mem_coe, lintegral_biUnion₀ s.countable_toSet hm hd, ← Finset.tsum_subtype']
#align measure_theory.lintegral_bUnion_finset₀ MeasureTheory.lintegral_biUnion_finset₀

theorem lintegral_biUnion_finset {s : Finset β} {t : β → Set α} (hd : Set.PairwiseDisjoint (↑s) t)
    (hm : ∀ b ∈ s, MeasurableSet (t b)) (f : α → ℝ≥0∞) :
    ∫⁻ a in ⋃ b ∈ s, t b, f a ∂μ = ∑ b in s, ∫⁻ a in t b, f a ∂μ :=
  lintegral_biUnion_finset₀ hd.aedisjoint (fun b hb => (hm b hb).nullMeasurableSet) f
#align measure_theory.lintegral_bUnion_finset MeasureTheory.lintegral_biUnion_finset

theorem lintegral_iUnion_le [Countable β] (s : β → Set α) (f : α → ℝ≥0∞) :
    ∫⁻ a in ⋃ i, s i, f a ∂μ ≤ ∑' i, ∫⁻ a in s i, f a ∂μ := by
  rw [← lintegral_sum_measure]
  exact lintegral_mono' restrict_iUnion_le le_rfl
#align measure_theory.lintegral_Union_le MeasureTheory.lintegral_iUnion_le

theorem lintegral_union {f : α → ℝ≥0∞} {A B : Set α} (hB : MeasurableSet B) (hAB : Disjoint A B) :
    ∫⁻ a in A ∪ B, f a ∂μ = ∫⁻ a in A, f a ∂μ + ∫⁻ a in B, f a ∂μ := by
  rw [restrict_union hAB hB, lintegral_add_measure]
#align measure_theory.lintegral_union MeasureTheory.lintegral_union

theorem lintegral_union_le (f : α → ℝ≥0∞) (s t : Set α) :
    ∫⁻ a in s ∪ t, f a ∂μ ≤ ∫⁻ a in s, f a ∂μ + ∫⁻ a in t, f a ∂μ := by
  rw [← lintegral_add_measure]
  exact lintegral_mono' (restrict_union_le _ _) le_rfl

theorem lintegral_inter_add_diff {B : Set α} (f : α → ℝ≥0∞) (A : Set α) (hB : MeasurableSet B) :
    ∫⁻ x in A ∩ B, f x ∂μ + ∫⁻ x in A \ B, f x ∂μ = ∫⁻ x in A, f x ∂μ := by
  rw [← lintegral_add_measure, restrict_inter_add_diff _ hB]
#align measure_theory.lintegral_inter_add_diff MeasureTheory.lintegral_inter_add_diff

theorem lintegral_add_compl (f : α → ℝ≥0∞) {A : Set α} (hA : MeasurableSet A) :
    ∫⁻ x in A, f x ∂μ + ∫⁻ x in Aᶜ, f x ∂μ = ∫⁻ x, f x ∂μ := by
  rw [← lintegral_add_measure, Measure.restrict_add_restrict_compl hA]
#align measure_theory.lintegral_add_compl MeasureTheory.lintegral_add_compl

theorem set_lintegral_compl {f : α → ℝ≥0∞} {s : Set α} (hsm : MeasurableSet s)
    (hfs : ∫⁻ x in s, f x ∂μ ≠ ∞) :
    ∫⁻ x in sᶜ, f x ∂μ = ∫⁻ x, f x ∂μ - ∫⁻ x in s, f x ∂μ := by
  rw [← lintegral_add_compl (μ := μ) f hsm, ENNReal.add_sub_cancel_left hfs]

theorem lintegral_max {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ x, max (f x) (g x) ∂μ =
      ∫⁻ x in { x | f x ≤ g x }, g x ∂μ + ∫⁻ x in { x | g x < f x }, f x ∂μ := by
  have hm : MeasurableSet { x | f x ≤ g x } := measurableSet_le hf hg
  rw [← lintegral_add_compl (fun x => max (f x) (g x)) hm]
  simp only [← compl_setOf, ← not_le]
  refine' congr_arg₂ (· + ·) (set_lintegral_congr_fun hm _) (set_lintegral_congr_fun hm.compl _)
  exacts [ae_of_all _ fun x => max_eq_right (a := f x) (b := g x),
    ae_of_all _ fun x (hx : ¬ f x ≤ g x) => max_eq_left (not_le.1 hx).le]
#align measure_theory.lintegral_max MeasureTheory.lintegral_max

theorem set_lintegral_max {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (s : Set α) :
    ∫⁻ x in s, max (f x) (g x) ∂μ =
      ∫⁻ x in s ∩ { x | f x ≤ g x }, g x ∂μ + ∫⁻ x in s ∩ { x | g x < f x }, f x ∂μ := by
  rw [lintegral_max hf hg, restrict_restrict, restrict_restrict, inter_comm s, inter_comm s]
  exacts [measurableSet_lt hg hf, measurableSet_le hf hg]
#align measure_theory.set_lintegral_max MeasureTheory.set_lintegral_max

theorem lintegral_map {mβ : MeasurableSpace β} {f : β → ℝ≥0∞} {g : α → β} (hf : Measurable f)
    (hg : Measurable g) : ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a) ∂μ := by
  erw [lintegral_eq_iSup_eapprox_lintegral hf, lintegral_eq_iSup_eapprox_lintegral (hf.comp hg)]
  congr with n : 1
  convert SimpleFunc.lintegral_map _ hg
  ext1 x; simp only [eapprox_comp hf hg, coe_comp]
#align measure_theory.lintegral_map MeasureTheory.lintegral_map

theorem lintegral_map' {mβ : MeasurableSpace β} {f : β → ℝ≥0∞} {g : α → β}
    (hf : AEMeasurable f (Measure.map g μ)) (hg : AEMeasurable g μ) :
    ∫⁻ a, f a ∂Measure.map g μ = ∫⁻ a, f (g a) ∂μ :=
  calc
    ∫⁻ a, f a ∂Measure.map g μ = ∫⁻ a, hf.mk f a ∂Measure.map g μ :=
      lintegral_congr_ae hf.ae_eq_mk
    _ = ∫⁻ a, hf.mk f a ∂Measure.map (hg.mk g) μ := by
      congr 1
      exact Measure.map_congr hg.ae_eq_mk
    _ = ∫⁻ a, hf.mk f (hg.mk g a) ∂μ := (lintegral_map hf.measurable_mk hg.measurable_mk)
    _ = ∫⁻ a, hf.mk f (g a) ∂μ := (lintegral_congr_ae <| hg.ae_eq_mk.symm.fun_comp _)
    _ = ∫⁻ a, f (g a) ∂μ := lintegral_congr_ae (ae_eq_comp hg hf.ae_eq_mk.symm)
#align measure_theory.lintegral_map' MeasureTheory.lintegral_map'

theorem lintegral_map_le {mβ : MeasurableSpace β} (f : β → ℝ≥0∞) {g : α → β} (hg : Measurable g) :
    (∫⁻ a, f a ∂Measure.map g μ) ≤ ∫⁻ a, f (g a) ∂μ := by
  rw [← iSup_lintegral_measurable_le_eq_lintegral, ← iSup_lintegral_measurable_le_eq_lintegral]
  refine' iSup₂_le fun i hi => iSup_le fun h'i => _
  refine' le_iSup₂_of_le (i ∘ g) (hi.comp hg) _
  exact le_iSup_of_le (fun x => h'i (g x)) (le_of_eq (lintegral_map hi hg))
#align measure_theory.lintegral_map_le MeasureTheory.lintegral_map_le

theorem lintegral_comp [MeasurableSpace β] {f : β → ℝ≥0∞} {g : α → β} (hf : Measurable f)
    (hg : Measurable g) : lintegral μ (f ∘ g) = ∫⁻ a, f a ∂map g μ :=
  (lintegral_map hf hg).symm
#align measure_theory.lintegral_comp MeasureTheory.lintegral_comp

theorem set_lintegral_map [MeasurableSpace β] {f : β → ℝ≥0∞} {g : α → β} {s : Set β}
    (hs : MeasurableSet s) (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ y in s, f y ∂map g μ = ∫⁻ x in g ⁻¹' s, f (g x) ∂μ := by
  rw [restrict_map hg hs, lintegral_map hf hg]
#align measure_theory.set_lintegral_map MeasureTheory.set_lintegral_map

theorem lintegral_indicator_const_comp {mβ : MeasurableSpace β} {f : α → β} {s : Set β}
    (hf : Measurable f) (hs : MeasurableSet s) (c : ℝ≥0∞) :
    ∫⁻ a, s.indicator (fun _ => c) (f a) ∂μ = c * μ (f ⁻¹' s) := by
  erw [lintegral_comp (measurable_const.indicator hs) hf, lintegral_indicator_const hs,
    Measure.map_apply hf hs]
#align measure_theory.lintegral_indicator_const_comp MeasureTheory.lintegral_indicator_const_comp

/-- If `g : α → β` is a measurable embedding and `f : β → ℝ≥0∞` is any function (not necessarily
measurable), then `∫⁻ a, f a ∂(map g μ) = ∫⁻ a, f (g a) ∂μ`. Compare with `lintegral_map` which
applies to any measurable `g : α → β` but requires that `f` is measurable as well. -/
theorem _root_.MeasurableEmbedding.lintegral_map [MeasurableSpace β] {g : α → β}
    (hg : MeasurableEmbedding g) (f : β → ℝ≥0∞) : ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a) ∂μ := by
  rw [lintegral, lintegral]
  refine' le_antisymm (iSup₂_le fun f₀ hf₀ => _) (iSup₂_le fun f₀ hf₀ => _)
  · rw [SimpleFunc.lintegral_map _ hg.measurable]
    have : (f₀.comp g hg.measurable : α → ℝ≥0∞) ≤ f ∘ g := fun x => hf₀ (g x)
    exact le_iSup_of_le (comp f₀ g hg.measurable) (by exact le_iSup (α := ℝ≥0∞) _ this)
  · rw [← f₀.extend_comp_eq hg (const _ 0), ← SimpleFunc.lintegral_map, ←
      SimpleFunc.lintegral_eq_lintegral, ← lintegral]
    refine' lintegral_mono_ae (hg.ae_map_iff.2 <| eventually_of_forall fun x => _)
    exact (extend_apply _ _ _ _).trans_le (hf₀ _)
#align measurable_embedding.lintegral_map MeasurableEmbedding.lintegral_map

/-- The `lintegral` transforms appropriately under a measurable equivalence `g : α ≃ᵐ β`.
(Compare `lintegral_map`, which applies to a wider class of functions `g : α → β`, but requires
measurability of the function being integrated.) -/
theorem lintegral_map_equiv [MeasurableSpace β] (f : β → ℝ≥0∞) (g : α ≃ᵐ β) :
    ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a) ∂μ :=
  g.measurableEmbedding.lintegral_map f
#align measure_theory.lintegral_map_equiv MeasureTheory.lintegral_map_equiv

protected theorem MeasurePreserving.lintegral_map_equiv [MeasurableSpace β] {ν : Measure β}
    (f : β → ℝ≥0∞) (g : α ≃ᵐ β) (hg : MeasurePreserving g μ ν) :
    ∫⁻ a, f a ∂ν = ∫⁻ a, f (g a) ∂μ := by
  rw [← MeasureTheory.lintegral_map_equiv f g, hg.map_eq]

theorem MeasurePreserving.lintegral_comp {mb : MeasurableSpace β} {ν : Measure β} {g : α → β}
    (hg : MeasurePreserving g μ ν) {f : β → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a, f (g a) ∂μ = ∫⁻ b, f b ∂ν := by rw [← hg.map_eq, lintegral_map hf hg.measurable]
#align measure_theory.measure_preserving.lintegral_comp MeasureTheory.MeasurePreserving.lintegral_comp

theorem MeasurePreserving.lintegral_comp_emb {mb : MeasurableSpace β} {ν : Measure β} {g : α → β}
    (hg : MeasurePreserving g μ ν) (hge : MeasurableEmbedding g) (f : β → ℝ≥0∞) :
    ∫⁻ a, f (g a) ∂μ = ∫⁻ b, f b ∂ν := by rw [← hg.map_eq, hge.lintegral_map]
#align measure_theory.measure_preserving.lintegral_comp_emb MeasureTheory.MeasurePreserving.lintegral_comp_emb

theorem MeasurePreserving.set_lintegral_comp_preimage {mb : MeasurableSpace β} {ν : Measure β}
    {g : α → β} (hg : MeasurePreserving g μ ν) {s : Set β} (hs : MeasurableSet s) {f : β → ℝ≥0∞}
    (hf : Measurable f) : ∫⁻ a in g ⁻¹' s, f (g a) ∂μ = ∫⁻ b in s, f b ∂ν := by
  rw [← hg.map_eq, set_lintegral_map hs hf hg.measurable]
#align measure_theory.measure_preserving.set_lintegral_comp_preimage MeasureTheory.MeasurePreserving.set_lintegral_comp_preimage

theorem MeasurePreserving.set_lintegral_comp_preimage_emb {mb : MeasurableSpace β} {ν : Measure β}
    {g : α → β} (hg : MeasurePreserving g μ ν) (hge : MeasurableEmbedding g) (f : β → ℝ≥0∞)
    (s : Set β) : ∫⁻ a in g ⁻¹' s, f (g a) ∂μ = ∫⁻ b in s, f b ∂ν := by
  rw [← hg.map_eq, hge.restrict_map, hge.lintegral_map]
#align measure_theory.measure_preserving.set_lintegral_comp_preimage_emb MeasureTheory.MeasurePreserving.set_lintegral_comp_preimage_emb

theorem MeasurePreserving.set_lintegral_comp_emb {mb : MeasurableSpace β} {ν : Measure β}
    {g : α → β} (hg : MeasurePreserving g μ ν) (hge : MeasurableEmbedding g) (f : β → ℝ≥0∞)
    (s : Set α) : ∫⁻ a in s, f (g a) ∂μ = ∫⁻ b in g '' s, f b ∂ν := by
  rw [← hg.set_lintegral_comp_preimage_emb hge, preimage_image_eq _ hge.injective]
#align measure_theory.measure_preserving.set_lintegral_comp_emb MeasureTheory.MeasurePreserving.set_lintegral_comp_emb

theorem lintegral_subtype_comap {s : Set α} (hs : MeasurableSet s) (f : α → ℝ≥0∞) :
    ∫⁻ x : s, f x ∂(μ.comap (↑)) = ∫⁻ x in s, f x ∂μ := by
  rw [← (MeasurableEmbedding.subtype_coe hs).lintegral_map, map_comap_subtype_coe hs]

theorem set_lintegral_subtype {s : Set α} (hs : MeasurableSet s) (t : Set s) (f : α → ℝ≥0∞) :
    ∫⁻ x in t, f x ∂(μ.comap (↑)) = ∫⁻ x in (↑) '' t, f x ∂μ := by
  rw [(MeasurableEmbedding.subtype_coe hs).restrict_comap, lintegral_subtype_comap hs,
    restrict_restrict hs, inter_eq_right.2 (Subtype.coe_image_subset _ _)]

section UnifTight

/-- If `f : α → ℝ≥0∞` has finite integral, then there exists a measurable set `s` of finite measure
such that the integral of `f` over `sᶜ` is less than a given positive number.

Also used to prove an `Lᵖ`-norm version in `MeasureTheory.Memℒp.exists_snorm_indicator_compl_le`. -/
theorem exists_set_lintegral_compl_lt {f : α → ℝ≥0∞} (hf : ∫⁻ a, f a ∂μ ≠ ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ s : Set α, MeasurableSet s ∧ μ s < ∞ ∧ ∫⁻ a in sᶜ, f a ∂μ < ε := by
  by_cases hf₀ : ∫⁻ a, f a ∂μ = 0
  · exact ⟨∅, .empty, by simp, by simpa [hf₀, pos_iff_ne_zero]⟩
  obtain ⟨g, hgf, hg_meas, hgsupp, hgε⟩ :
      ∃ g ≤ f, Measurable g ∧ μ (support g) < ∞ ∧ ∫⁻ a, f a ∂μ - ε < ∫⁻ a, g a ∂μ := by
    obtain ⟨g, hgf, hgε⟩ : ∃ (g : α →ₛ ℝ≥0∞) (_ : g ≤ f), ∫⁻ a, f a ∂μ - ε < g.lintegral μ := by
      simpa only [← lt_iSup_iff, ← lintegral_def] using ENNReal.sub_lt_self hf hf₀ hε
    refine ⟨g, hgf, g.measurable, ?_, by rwa [g.lintegral_eq_lintegral]⟩
    exact SimpleFunc.FinMeasSupp.of_lintegral_ne_top <| ne_top_of_le_ne_top hf <|
      g.lintegral_eq_lintegral μ ▸ lintegral_mono hgf
  refine ⟨_, measurableSet_support hg_meas, hgsupp, ?_⟩
  calc
    ∫⁻ a in (support g)ᶜ, f a ∂μ
      = ∫⁻ a in (support g)ᶜ, f a - g a ∂μ := set_lintegral_congr_fun
      (measurableSet_support hg_meas).compl <| ae_of_all _ <| by intro; simp_all
    _ ≤ ∫⁻ a, f a - g a ∂μ := set_lintegral_le_lintegral _ _
    _ = ∫⁻ a, f a ∂μ - ∫⁻ a, g a ∂μ :=
      lintegral_sub hg_meas (ne_top_of_le_ne_top hf <| lintegral_mono hgf) (ae_of_all _ hgf)
    _ < ε := ENNReal.sub_lt_of_lt_add (lintegral_mono hgf) <|
      ENNReal.lt_add_of_sub_lt_left (.inl hf) hgε

/-- For any function `f : α → ℝ≥0∞`, there exists a measurable function `g ≤ f` with the same
integral over any measurable set. -/
theorem exists_measurable_le_set_lintegral_eq_of_integrable {f : α → ℝ≥0∞} (hf : ∫⁻ a, f a ∂μ ≠ ∞) :
    ∃ (g : α → ℝ≥0∞), Measurable g ∧ g ≤ f ∧ ∀ s : Set α, MeasurableSet s →
      ∫⁻ a in s, f a ∂μ = ∫⁻ a in s, g a ∂μ := by
  obtain ⟨g, hmg, hgf, hifg⟩ := exists_measurable_le_lintegral_eq (μ := μ) f
  use g, hmg, hgf
  refine fun s hms ↦ le_antisymm ?_ (lintegral_mono hgf)
  rw [← compl_compl s, set_lintegral_compl hms.compl, set_lintegral_compl hms.compl, hifg]
  · gcongr; apply hgf
  · rw [hifg] at hf
    exact ne_top_of_le_ne_top hf (set_lintegral_le_lintegral _ _)
  · exact ne_top_of_le_ne_top hf (set_lintegral_le_lintegral _ _)

end UnifTight

section DiracAndCount
variable [MeasurableSpace α]

theorem lintegral_dirac' (a : α) {f : α → ℝ≥0∞} (hf : Measurable f) : ∫⁻ a, f a ∂dirac a = f a :=
  by simp [lintegral_congr_ae (ae_eq_dirac' hf)]
#align measure_theory.lintegral_dirac' MeasureTheory.lintegral_dirac'

theorem lintegral_dirac [MeasurableSingletonClass α] (a : α) (f : α → ℝ≥0∞) :
    ∫⁻ a, f a ∂dirac a = f a := by simp [lintegral_congr_ae (ae_eq_dirac f)]
#align measure_theory.lintegral_dirac MeasureTheory.lintegral_dirac

theorem set_lintegral_dirac' {a : α} {f : α → ℝ≥0∞} (hf : Measurable f) {s : Set α}
    (hs : MeasurableSet s) [Decidable (a ∈ s)] :
    ∫⁻ x in s, f x ∂Measure.dirac a = if a ∈ s then f a else 0 := by
  rw [restrict_dirac' hs]
  split_ifs
  · exact lintegral_dirac' _ hf
  · exact lintegral_zero_measure _
#align measure_theory.set_lintegral_dirac' MeasureTheory.set_lintegral_dirac'

theorem set_lintegral_dirac {a : α} (f : α → ℝ≥0∞) (s : Set α) [MeasurableSingletonClass α]
    [Decidable (a ∈ s)] : ∫⁻ x in s, f x ∂Measure.dirac a = if a ∈ s then f a else 0 := by
  rw [restrict_dirac]
  split_ifs
  · exact lintegral_dirac _ _
  · exact lintegral_zero_measure _
#align measure_theory.set_lintegral_dirac MeasureTheory.set_lintegral_dirac

theorem lintegral_count' {f : α → ℝ≥0∞} (hf : Measurable f) : ∫⁻ a, f a ∂count = ∑' a, f a := by
  rw [count, lintegral_sum_measure]
  congr
  exact funext fun a => lintegral_dirac' a hf
#align measure_theory.lintegral_count' MeasureTheory.lintegral_count'

theorem lintegral_count [MeasurableSingletonClass α] (f : α → ℝ≥0∞) :
    ∫⁻ a, f a ∂count = ∑' a, f a := by
  rw [count, lintegral_sum_measure]
  congr
  exact funext fun a => lintegral_dirac a f
#align measure_theory.lintegral_count MeasureTheory.lintegral_count

theorem _root_.ENNReal.tsum_const_eq [MeasurableSingletonClass α] (c : ℝ≥0∞) :
    ∑' _ : α, c = c * Measure.count (univ : Set α) := by rw [← lintegral_count, lintegral_const]
#align ennreal.tsum_const_eq ENNReal.tsum_const_eq

/-- Markov's inequality for the counting measure with hypothesis using `tsum` in `ℝ≥0∞`. -/
theorem _root_.ENNReal.count_const_le_le_of_tsum_le [MeasurableSingletonClass α] {a : α → ℝ≥0∞}
    (a_mble : Measurable a) {c : ℝ≥0∞} (tsum_le_c : ∑' i, a i ≤ c) {ε : ℝ≥0∞} (ε_ne_zero : ε ≠ 0)
    (ε_ne_top : ε ≠ ∞) : Measure.count { i : α | ε ≤ a i } ≤ c / ε := by
  rw [← lintegral_count] at tsum_le_c
  apply (MeasureTheory.meas_ge_le_lintegral_div a_mble.aemeasurable ε_ne_zero ε_ne_top).trans
  exact ENNReal.div_le_div tsum_le_c rfl.le
#align ennreal.count_const_le_le_of_tsum_le ENNReal.count_const_le_le_of_tsum_le

/-- Markov's inequality for counting measure with hypothesis using `tsum` in `ℝ≥0`. -/
theorem _root_.NNReal.count_const_le_le_of_tsum_le [MeasurableSingletonClass α] {a : α → ℝ≥0}
    (a_mble : Measurable a) (a_summable : Summable a) {c : ℝ≥0} (tsum_le_c : ∑' i, a i ≤ c)
    {ε : ℝ≥0} (ε_ne_zero : ε ≠ 0) : Measure.count { i : α | ε ≤ a i } ≤ c / ε := by
  rw [show (fun i => ε ≤ a i) = fun i => (ε : ℝ≥0∞) ≤ ((↑) ∘ a) i by
      funext i
      simp only [ENNReal.coe_le_coe, Function.comp]]
  apply
    ENNReal.count_const_le_le_of_tsum_le (measurable_coe_nnreal_ennreal.comp a_mble) _
      (mod_cast ε_ne_zero) (@ENNReal.coe_ne_top ε)
  convert ENNReal.coe_le_coe.mpr tsum_le_c
  simp_rw [Function.comp_apply]
  rw [ENNReal.tsum_coe_eq a_summable.hasSum]
#align nnreal.count_const_le_le_of_tsum_le NNReal.count_const_le_le_of_tsum_le

end DiracAndCount

section Countable

/-!
### Lebesgue integral over finite and countable types and sets
-/


theorem lintegral_countable' [Countable α] [MeasurableSingletonClass α] (f : α → ℝ≥0∞) :
    ∫⁻ a, f a ∂μ = ∑' a, f a * μ {a} := by
  conv_lhs => rw [← sum_smul_dirac μ, lintegral_sum_measure]
  congr 1 with a : 1
  rw [lintegral_smul_measure, lintegral_dirac, mul_comm]
#align measure_theory.lintegral_countable' MeasureTheory.lintegral_countable'

theorem lintegral_singleton' {f : α → ℝ≥0∞} (hf : Measurable f) (a : α) :
    ∫⁻ x in {a}, f x ∂μ = f a * μ {a} := by
  simp only [restrict_singleton, lintegral_smul_measure, lintegral_dirac' _ hf, mul_comm]
#align measure_theory.lintegral_singleton' MeasureTheory.lintegral_singleton'

theorem lintegral_singleton [MeasurableSingletonClass α] (f : α → ℝ≥0∞) (a : α) :
    ∫⁻ x in {a}, f x ∂μ = f a * μ {a} := by
  simp only [restrict_singleton, lintegral_smul_measure, lintegral_dirac, mul_comm]
#align measure_theory.lintegral_singleton MeasureTheory.lintegral_singleton

theorem lintegral_countable [MeasurableSingletonClass α] (f : α → ℝ≥0∞) {s : Set α}
    (hs : s.Countable) : ∫⁻ a in s, f a ∂μ = ∑' a : s, f a * μ {(a : α)} :=
  calc
    ∫⁻ a in s, f a ∂μ = ∫⁻ a in ⋃ x ∈ s, {x}, f a ∂μ := by rw [biUnion_of_singleton]
    _ = ∑' a : s, ∫⁻ x in {(a : α)}, f x ∂μ :=
      (lintegral_biUnion hs (fun _ _ => measurableSet_singleton _) (pairwiseDisjoint_fiber id s) _)
    _ = ∑' a : s, f a * μ {(a : α)} := by simp only [lintegral_singleton]
#align measure_theory.lintegral_countable MeasureTheory.lintegral_countable

theorem lintegral_insert [MeasurableSingletonClass α] {a : α} {s : Set α} (h : a ∉ s)
    (f : α → ℝ≥0∞) : ∫⁻ x in insert a s, f x ∂μ = f a * μ {a} + ∫⁻ x in s, f x ∂μ := by
  rw [← union_singleton, lintegral_union (measurableSet_singleton a), lintegral_singleton,
    add_comm]
  rwa [disjoint_singleton_right]
#align measure_theory.lintegral_insert MeasureTheory.lintegral_insert

theorem lintegral_finset [MeasurableSingletonClass α] (s : Finset α) (f : α → ℝ≥0∞) :
    ∫⁻ x in s, f x ∂μ = ∑ x in s, f x * μ {x} := by
  simp only [lintegral_countable _ s.countable_toSet, ← Finset.tsum_subtype']
#align measure_theory.lintegral_finset MeasureTheory.lintegral_finset

theorem lintegral_fintype [MeasurableSingletonClass α] [Fintype α] (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = ∑ x, f x * μ {x} := by
  rw [← lintegral_finset, Finset.coe_univ, Measure.restrict_univ]
#align measure_theory.lintegral_fintype MeasureTheory.lintegral_fintype

theorem lintegral_unique [Unique α] (f : α → ℝ≥0∞) : ∫⁻ x, f x ∂μ = f default * μ univ :=
  calc
    ∫⁻ x, f x ∂μ = ∫⁻ _, f default ∂μ := lintegral_congr <| Unique.forall_iff.2 rfl
    _ = f default * μ univ := lintegral_const _
#align measure_theory.lintegral_unique MeasureTheory.lintegral_unique

end Countable

theorem ae_lt_top {f : α → ℝ≥0∞} (hf : Measurable f) (h2f : ∫⁻ x, f x ∂μ ≠ ∞) :
    ∀ᵐ x ∂μ, f x < ∞ := by
  simp_rw [ae_iff, ENNReal.not_lt_top]
  by_contra h
  apply h2f.lt_top.not_le
  have : (f ⁻¹' {∞}).indicator ⊤ ≤ f := by
    intro x
    by_cases hx : x ∈ f ⁻¹' {∞} <;> [simpa [indicator_of_mem hx]; simp [indicator_of_not_mem hx]]
  convert lintegral_mono this
  rw [lintegral_indicator _ (hf (measurableSet_singleton ∞))]
  simp [ENNReal.top_mul', preimage, h]
#align measure_theory.ae_lt_top MeasureTheory.ae_lt_top

theorem ae_lt_top' {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (h2f : ∫⁻ x, f x ∂μ ≠ ∞) :
    ∀ᵐ x ∂μ, f x < ∞ :=
  haveI h2f_meas : ∫⁻ x, hf.mk f x ∂μ ≠ ∞ := by rwa [← lintegral_congr_ae hf.ae_eq_mk]
  (ae_lt_top hf.measurable_mk h2f_meas).mp (hf.ae_eq_mk.mono fun x hx h => by rwa [hx])
#align measure_theory.ae_lt_top' MeasureTheory.ae_lt_top'

theorem set_lintegral_lt_top_of_bddAbove {s : Set α} (hs : μ s ≠ ∞) {f : α → ℝ≥0}
    (hf : Measurable f) (hbdd : BddAbove (f '' s)) : ∫⁻ x in s, f x ∂μ < ∞ := by
  obtain ⟨M, hM⟩ := hbdd
  rw [mem_upperBounds] at hM
  refine'
    lt_of_le_of_lt (set_lintegral_mono hf.coe_nnreal_ennreal (@measurable_const _ _ _ _ ↑M) _) _
  · simpa using hM
  · rw [lintegral_const]
    refine' ENNReal.mul_lt_top ENNReal.coe_lt_top.ne _
    simp [hs]
#align measure_theory.set_lintegral_lt_top_of_bdd_above MeasureTheory.set_lintegral_lt_top_of_bddAbove

theorem set_lintegral_lt_top_of_isCompact [TopologicalSpace α] [OpensMeasurableSpace α] {s : Set α}
    (hs : μ s ≠ ∞) (hsc : IsCompact s) {f : α → ℝ≥0} (hf : Continuous f) :
    ∫⁻ x in s, f x ∂μ < ∞ :=
  set_lintegral_lt_top_of_bddAbove hs hf.measurable (hsc.image hf).bddAbove
#align measure_theory.set_lintegral_lt_top_of_is_compact MeasureTheory.set_lintegral_lt_top_of_isCompact

theorem _root_.IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal {α : Type*}
    [MeasurableSpace α] (μ : Measure α) [μ_fin : IsFiniteMeasure μ] {f : α → ℝ≥0∞}
    (f_bdd : ∃ c : ℝ≥0, ∀ x, f x ≤ c) : ∫⁻ x, f x ∂μ < ∞ := by
  cases' f_bdd with c hc
  apply lt_of_le_of_lt (@lintegral_mono _ _ μ _ _ hc)
  rw [lintegral_const]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top.ne μ_fin.measure_univ_lt_top.ne
#align is_finite_measure.lintegral_lt_top_of_bounded_to_ennreal IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal

/-- If a monotone sequence of functions has an upper bound and the sequence of integrals of these
functions tends to the integral of the upper bound, then the sequence of functions converges
almost everywhere to the upper bound. Auxiliary version assuming moreover that the
functions in the sequence are ae measurable. -/
lemma tendsto_of_lintegral_tendsto_of_monotone_aux {α : Type*} {mα : MeasurableSpace α}
    {f : ℕ → α → ℝ≥0∞} {F : α → ℝ≥0∞} {μ : Measure α}
    (hf_meas : ∀ n, AEMeasurable (f n) μ) (hF_meas : AEMeasurable F μ)
    (hf_tendsto : Tendsto (fun i ↦ ∫⁻ a, f i a ∂μ) atTop (𝓝 (∫⁻ a, F a ∂μ)))
    (hf_mono : ∀ᵐ a ∂μ, Monotone (fun i ↦ f i a))
    (h_bound : ∀ᵐ a ∂μ, ∀ i, f i a ≤ F a) (h_int_finite : ∫⁻ a, F a ∂μ ≠ ∞) :
    ∀ᵐ a ∂μ, Tendsto (fun i ↦ f i a) atTop (𝓝 (F a)) := by
  have h_bound_finite : ∀ᵐ a ∂μ, F a ≠ ∞ := by
    filter_upwards [ae_lt_top' hF_meas h_int_finite] with a ha using ha.ne
  have h_exists : ∀ᵐ a ∂μ, ∃ l, Tendsto (fun i ↦ f i a) atTop (𝓝 l) := by
    filter_upwards [h_bound, h_bound_finite, hf_mono] with a h_le h_fin h_mono
    have h_tendsto : Tendsto (fun i ↦ f i a) atTop atTop ∨
        ∃ l, Tendsto (fun i ↦ f i a) atTop (𝓝 l) := tendsto_of_monotone h_mono
    cases' h_tendsto with h_absurd h_tendsto
    · rw [tendsto_atTop_atTop_iff_of_monotone h_mono] at h_absurd
      obtain ⟨i, hi⟩ := h_absurd (F a + 1)
      refine absurd (hi.trans (h_le _)) (not_le.mpr ?_)
      exact ENNReal.lt_add_right h_fin one_ne_zero
    · exact h_tendsto
  classical
  let F' : α → ℝ≥0∞ := fun a ↦ if h : ∃ l, Tendsto (fun i ↦ f i a) atTop (𝓝 l)
    then h.choose else ∞
  have hF'_tendsto : ∀ᵐ a ∂μ, Tendsto (fun i ↦ f i a) atTop (𝓝 (F' a)) := by
    filter_upwards [h_exists] with a ha
    simp_rw [F', dif_pos ha]
    exact ha.choose_spec
  suffices F' =ᵐ[μ] F by
    filter_upwards [this, hF'_tendsto] with a h_eq h_tendsto using h_eq ▸ h_tendsto
  have hF'_le : F' ≤ᵐ[μ] F := by
    filter_upwards [h_bound, hF'_tendsto] with a h_le h_tendsto
    exact le_of_tendsto' h_tendsto (fun m ↦ h_le _)
  suffices ∫⁻ a, F' a ∂μ = ∫⁻ a, F a ∂μ from
    ae_eq_of_ae_le_of_lintegral_le hF'_le (this ▸ h_int_finite) hF_meas this.symm.le
  refine tendsto_nhds_unique ?_ hf_tendsto
  exact lintegral_tendsto_of_tendsto_of_monotone hf_meas hf_mono hF'_tendsto

/-- If a monotone sequence of functions has an upper bound and the sequence of integrals of these
functions tends to the integral of the upper bound, then the sequence of functions converges
almost everywhere to the upper bound. -/
lemma tendsto_of_lintegral_tendsto_of_monotone {α : Type*} {mα : MeasurableSpace α}
    {f : ℕ → α → ℝ≥0∞} {F : α → ℝ≥0∞} {μ : Measure α}
    (hF_meas : AEMeasurable F μ)
    (hf_tendsto : Tendsto (fun i ↦ ∫⁻ a, f i a ∂μ) atTop (𝓝 (∫⁻ a, F a ∂μ)))
    (hf_mono : ∀ᵐ a ∂μ, Monotone (fun i ↦ f i a))
    (h_bound : ∀ᵐ a ∂μ, ∀ i, f i a ≤ F a) (h_int_finite : ∫⁻ a, F a ∂μ ≠ ∞) :
    ∀ᵐ a ∂μ, Tendsto (fun i ↦ f i a) atTop (𝓝 (F a)) := by
  have : ∀ n, ∃ g : α → ℝ≥0∞, Measurable g ∧ g ≤ f n ∧ ∫⁻ a, f n a ∂μ = ∫⁻ a, g a ∂μ :=
    fun n ↦ exists_measurable_le_lintegral_eq _ _
  choose g gmeas gf hg using this
  let g' : ℕ → α → ℝ≥0∞ := Nat.rec (g 0) (fun n I x ↦ max (g (n+1) x) (I x))
  have M n : Measurable (g' n) := by
    induction n with
    | zero => simp [g', gmeas 0]
    | succ n ih => exact Measurable.max (gmeas (n+1)) ih
  have I : ∀ n x, g n x ≤ g' n x := by
    intro n x
    cases n with | zero | succ => simp [g']
  have I' : ∀ᵐ x ∂μ, ∀ n, g' n x ≤ f n x := by
    filter_upwards [hf_mono] with x hx n
    induction n with
    | zero => simpa [g'] using gf 0 x
    | succ n ih => exact max_le (gf (n+1) x) (ih.trans (hx (Nat.le_succ n)))
  have Int_eq n : ∫⁻ x, g' n x ∂μ = ∫⁻ x, f n x ∂μ := by
    apply le_antisymm
    · apply lintegral_mono_ae
      filter_upwards [I'] with x hx using hx n
    · rw [hg n]
      exact lintegral_mono (I n)
  have : ∀ᵐ a ∂μ, Tendsto (fun i ↦ g' i a) atTop (𝓝 (F a)) := by
    apply tendsto_of_lintegral_tendsto_of_monotone_aux _ hF_meas _ _ _ h_int_finite
    · exact fun n ↦ (M n).aemeasurable
    · simp_rw [Int_eq]
      exact hf_tendsto
    · exact eventually_of_forall (fun x ↦ monotone_nat_of_le_succ (fun n ↦ le_max_right _ _))
    · filter_upwards [h_bound, I'] with x h'x hx n using (hx n).trans (h'x n)
  filter_upwards [this, I', h_bound] with x hx h'x h''x
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hx tendsto_const_nhds h'x h''x

/-- If an antitone sequence of functions has a lower bound and the sequence of integrals of these
functions tends to the integral of the lower bound, then the sequence of functions converges
almost everywhere to the lower bound. -/
lemma tendsto_of_lintegral_tendsto_of_antitone {α : Type*} {mα : MeasurableSpace α}
    {f : ℕ → α → ℝ≥0∞} {F : α → ℝ≥0∞} {μ : Measure α}
    (hf_meas : ∀ n, AEMeasurable (f n) μ)
    (hf_tendsto : Tendsto (fun i ↦ ∫⁻ a, f i a ∂μ) atTop (𝓝 (∫⁻ a, F a ∂μ)))
    (hf_mono : ∀ᵐ a ∂μ, Antitone (fun i ↦ f i a))
    (h_bound : ∀ᵐ a ∂μ, ∀ i, F a ≤ f i a) (h0 : ∫⁻ a, f 0 a ∂μ ≠ ∞) :
    ∀ᵐ a ∂μ, Tendsto (fun i ↦ f i a) atTop (𝓝 (F a)) := by
  have h_int_finite : ∫⁻ a, F a ∂μ ≠ ∞ := by
    refine ((lintegral_mono_ae ?_).trans_lt h0.lt_top).ne
    filter_upwards [h_bound] with a ha using ha 0
  have h_exists : ∀ᵐ a ∂μ, ∃ l, Tendsto (fun i ↦ f i a) atTop (𝓝 l) := by
    filter_upwards [hf_mono] with a h_mono
    rcases tendsto_of_antitone h_mono with h | h
    · refine ⟨0, h.mono_right ?_⟩
      rw [OrderBot.atBot_eq]
      exact pure_le_nhds _
    · exact h
  classical
  let F' : α → ℝ≥0∞ := fun a ↦ if h : ∃ l, Tendsto (fun i ↦ f i a) atTop (𝓝 l)
    then h.choose else ∞
  have hF'_tendsto : ∀ᵐ a ∂μ, Tendsto (fun i ↦ f i a) atTop (𝓝 (F' a)) := by
    filter_upwards [h_exists] with a ha
    simp_rw [F', dif_pos ha]
    exact ha.choose_spec
  suffices F' =ᵐ[μ] F by
    filter_upwards [this, hF'_tendsto] with a h_eq h_tendsto using h_eq ▸ h_tendsto
  have hF'_le : F ≤ᵐ[μ] F' := by
    filter_upwards [h_bound, hF'_tendsto] with a h_le h_tendsto
    exact ge_of_tendsto' h_tendsto (fun m ↦ h_le _)
  suffices ∫⁻ a, F' a ∂μ = ∫⁻ a, F a ∂μ by
    refine (ae_eq_of_ae_le_of_lintegral_le hF'_le h_int_finite ?_ this.le).symm
    exact ENNReal.aemeasurable_of_tendsto hf_meas hF'_tendsto
  refine tendsto_nhds_unique ?_ hf_tendsto
  exact lintegral_tendsto_of_tendsto_of_antitone hf_meas hf_mono h0 hF'_tendsto

end Lintegral

open MeasureTheory.SimpleFunc

variable {m m0 : MeasurableSpace α}

/-- In a sigma-finite measure space, there exists an integrable function which is
positive everywhere (and with an arbitrarily small integral). -/
theorem exists_pos_lintegral_lt_of_sigmaFinite (μ : Measure α) [SigmaFinite μ] {ε : ℝ≥0∞}
    (ε0 : ε ≠ 0) : ∃ g : α → ℝ≥0, (∀ x, 0 < g x) ∧ Measurable g ∧ ∫⁻ x, g x ∂μ < ε := by
  /- Let `s` be a covering of `α` by pairwise disjoint measurable sets of finite measure. Let
    `δ : ℕ → ℝ≥0` be a positive function such that `∑' i, μ (s i) * δ i < ε`. Then the function that
     is equal to `δ n` on `s n` is a positive function with integral less than `ε`. -/
  set s : ℕ → Set α := disjointed (spanningSets μ)
  have : ∀ n, μ (s n) < ∞ := fun n =>
    (measure_mono <| disjointed_subset _ _).trans_lt (measure_spanningSets_lt_top μ n)
  obtain ⟨δ, δpos, δsum⟩ : ∃ δ : ℕ → ℝ≥0, (∀ i, 0 < δ i) ∧ (∑' i, μ (s i) * δ i) < ε :=
    ENNReal.exists_pos_tsum_mul_lt_of_countable ε0 _ fun n => (this n).ne
  set N : α → ℕ := spanningSetsIndex μ
  have hN_meas : Measurable N := measurable_spanningSetsIndex μ
  have hNs : ∀ n, N ⁻¹' {n} = s n := preimage_spanningSetsIndex_singleton μ
  refine' ⟨δ ∘ N, fun x => δpos _, measurable_from_nat.comp hN_meas, _⟩
  erw [lintegral_comp measurable_from_nat.coe_nnreal_ennreal hN_meas]
  simpa [N, hNs, lintegral_countable', measurable_spanningSetsIndex, mul_comm] using δsum
#align measure_theory.exists_pos_lintegral_lt_of_sigma_finite MeasureTheory.exists_pos_lintegral_lt_of_sigmaFinite

theorem lintegral_trim {μ : Measure α} (hm : m ≤ m0) {f : α → ℝ≥0∞} (hf : Measurable[m] f) :
    ∫⁻ a, f a ∂μ.trim hm = ∫⁻ a, f a ∂μ := by
  refine'
    @Measurable.ennreal_induction α m (fun f => ∫⁻ a, f a ∂μ.trim hm = ∫⁻ a, f a ∂μ) _ _ _ f hf
  · intro c s hs
    rw [lintegral_indicator _ hs, lintegral_indicator _ (hm s hs), set_lintegral_const,
      set_lintegral_const]
    suffices h_trim_s : μ.trim hm s = μ s by rw [h_trim_s]
    exact trim_measurableSet_eq hm hs
  · intro f g _ hf _ hf_prop hg_prop
    have h_m := lintegral_add_left (μ := Measure.trim μ hm) hf g
    have h_m0 := lintegral_add_left (μ := μ) (Measurable.mono hf hm le_rfl) g
    rwa [hf_prop, hg_prop, ← h_m0] at h_m
  · intro f hf hf_mono hf_prop
    rw [lintegral_iSup hf hf_mono]
    rw [lintegral_iSup (fun n => Measurable.mono (hf n) hm le_rfl) hf_mono]
    congr
    exact funext fun n => hf_prop n
#align measure_theory.lintegral_trim MeasureTheory.lintegral_trim

theorem lintegral_trim_ae {μ : Measure α} (hm : m ≤ m0) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f (μ.trim hm)) : ∫⁻ a, f a ∂μ.trim hm = ∫⁻ a, f a ∂μ := by
  rw [lintegral_congr_ae (ae_eq_of_ae_eq_trim hf.ae_eq_mk), lintegral_congr_ae hf.ae_eq_mk,
    lintegral_trim hm hf.measurable_mk]
#align measure_theory.lintegral_trim_ae MeasureTheory.lintegral_trim_ae

section SigmaFinite

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]

theorem univ_le_of_forall_fin_meas_le {μ : Measure α} (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (C : ℝ≥0∞) {f : Set α → ℝ≥0∞} (hf : ∀ s, MeasurableSet[m] s → μ s ≠ ∞ → f s ≤ C)
    (h_F_lim :
      ∀ S : ℕ → Set α, (∀ n, MeasurableSet[m] (S n)) → Monotone S → f (⋃ n, S n) ≤ ⨆ n, f (S n)) :
    f univ ≤ C := by
  let S := @spanningSets _ m (μ.trim hm) _
  have hS_mono : Monotone S := @monotone_spanningSets _ m (μ.trim hm) _
  have hS_meas : ∀ n, MeasurableSet[m] (S n) := @measurable_spanningSets _ m (μ.trim hm) _
  rw [← @iUnion_spanningSets _ m (μ.trim hm)]
  refine' (h_F_lim S hS_meas hS_mono).trans _
  refine' iSup_le fun n => hf (S n) (hS_meas n) _
  exact ((le_trim hm).trans_lt (@measure_spanningSets_lt_top _ m (μ.trim hm) _ n)).ne
#align measure_theory.univ_le_of_forall_fin_meas_le MeasureTheory.univ_le_of_forall_fin_meas_le

/-- If the Lebesgue integral of a function is bounded by some constant on all sets with finite
measure in a sub-σ-algebra and the measure is σ-finite on that sub-σ-algebra, then the integral
over the whole space is bounded by that same constant. Version for a measurable function.
See `lintegral_le_of_forall_fin_meas_le'` for the more general `AEMeasurable` version. -/
theorem lintegral_le_of_forall_fin_meas_le_of_measurable {μ : Measure α} (hm : m ≤ m0)
    [SigmaFinite (μ.trim hm)] (C : ℝ≥0∞) {f : α → ℝ≥0∞} (hf_meas : Measurable f)
    (hf : ∀ s, MeasurableSet[m] s → μ s ≠ ∞ → ∫⁻ x in s, f x ∂μ ≤ C) : ∫⁻ x, f x ∂μ ≤ C := by
  have : ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ := by simp only [Measure.restrict_univ]
  rw [← this]
  refine' univ_le_of_forall_fin_meas_le hm C hf fun S hS_meas hS_mono => _
  rw [← lintegral_indicator]
  swap
  · exact hm (⋃ n, S n) (@MeasurableSet.iUnion _ _ m _ _ hS_meas)
  have h_integral_indicator : ⨆ n, ∫⁻ x in S n, f x ∂μ = ⨆ n, ∫⁻ x, (S n).indicator f x ∂μ := by
    congr
    ext1 n
    rw [lintegral_indicator _ (hm _ (hS_meas n))]
  rw [h_integral_indicator, ← lintegral_iSup]
  · refine' le_of_eq (lintegral_congr fun x => _)
    simp_rw [indicator_apply]
    by_cases hx_mem : x ∈ iUnion S
    · simp only [hx_mem, if_true]
      obtain ⟨n, hxn⟩ := mem_iUnion.mp hx_mem
      refine' le_antisymm (_root_.trans _ (le_iSup _ n)) (iSup_le fun i => _)
      · simp only [hxn, le_refl, if_true]
      · by_cases hxi : x ∈ S i <;> simp [hxi]
    · simp only [hx_mem, if_false]
      rw [mem_iUnion] at hx_mem
      push_neg at hx_mem
      refine' le_antisymm (zero_le _) (iSup_le fun n => _)
      simp only [hx_mem n, if_false, nonpos_iff_eq_zero]
  · exact fun n => hf_meas.indicator (hm _ (hS_meas n))
  · intro n₁ n₂ hn₁₂ a
    simp_rw [indicator_apply]
    split_ifs with h h_1
    · exact le_rfl
    · exact absurd (mem_of_mem_of_subset h (hS_mono hn₁₂)) h_1
    · exact zero_le _
    · exact le_rfl
#align measure_theory.lintegral_le_of_forall_fin_meas_le_of_measurable MeasureTheory.lintegral_le_of_forall_fin_meas_le_of_measurable

/-- If the Lebesgue integral of a function is bounded by some constant on all sets with finite
measure in a sub-σ-algebra and the measure is σ-finite on that sub-σ-algebra, then the integral
over the whole space is bounded by that same constant. -/
theorem lintegral_le_of_forall_fin_meas_le' {μ : Measure α} (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (C : ℝ≥0∞) {f : _ → ℝ≥0∞} (hf_meas : AEMeasurable f μ)
    (hf : ∀ s, MeasurableSet[m] s → μ s ≠ ∞ → ∫⁻ x in s, f x ∂μ ≤ C) : ∫⁻ x, f x ∂μ ≤ C := by
  let f' := hf_meas.mk f
  have hf' : ∀ s, MeasurableSet[m] s → μ s ≠ ∞ → ∫⁻ x in s, f' x ∂μ ≤ C := by
    refine' fun s hs hμs => (le_of_eq _).trans (hf s hs hμs)
    refine' lintegral_congr_ae (ae_restrict_of_ae (hf_meas.ae_eq_mk.mono fun x hx => _))
    dsimp only
    rw [hx]
  rw [lintegral_congr_ae hf_meas.ae_eq_mk]
  exact lintegral_le_of_forall_fin_meas_le_of_measurable hm C hf_meas.measurable_mk hf'
#align measure_theory.lintegral_le_of_forall_fin_meas_le' MeasureTheory.lintegral_le_of_forall_fin_meas_le'

/-- If the Lebesgue integral of a function is bounded by some constant on all sets with finite
measure and the measure is σ-finite, then the integral over the whole space is bounded by that same
constant. -/
theorem lintegral_le_of_forall_fin_meas_le [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    (C : ℝ≥0∞) {f : α → ℝ≥0∞} (hf_meas : AEMeasurable f μ)
    (hf : ∀ s, MeasurableSet s → μ s ≠ ∞ → ∫⁻ x in s, f x ∂μ ≤ C) : ∫⁻ x, f x ∂μ ≤ C :=
  @lintegral_le_of_forall_fin_meas_le' _ _ _ _ _ (by rwa [trim_eq_self]) C _ hf_meas hf
#align measure_theory.lintegral_le_of_forall_fin_meas_le MeasureTheory.lintegral_le_of_forall_fin_meas_le

theorem SimpleFunc.exists_lt_lintegral_simpleFunc_of_lt_lintegral {m : MeasurableSpace α}
    {μ : Measure α} [SigmaFinite μ] {f : α →ₛ ℝ≥0} {L : ℝ≥0∞} (hL : L < ∫⁻ x, f x ∂μ) :
    ∃ g : α →ₛ ℝ≥0, (∀ x, g x ≤ f x) ∧ ∫⁻ x, g x ∂μ < ∞ ∧ L < ∫⁻ x, g x ∂μ := by
  induction' f using MeasureTheory.SimpleFunc.induction with c s hs f₁ f₂ _ h₁ h₂ generalizing L
  · simp only [hs, const_zero, coe_piecewise, coe_const, SimpleFunc.coe_zero, univ_inter,
      piecewise_eq_indicator, lintegral_indicator, lintegral_const, Measure.restrict_apply',
      ENNReal.coe_indicator, Function.const_apply] at hL
    have c_ne_zero : c ≠ 0 := by
      intro hc
      simp only [hc, ENNReal.coe_zero, zero_mul, not_lt_zero] at hL
    have : L / c < μ s := by
      rwa [ENNReal.div_lt_iff, mul_comm]
      · simp only [c_ne_zero, Ne.def, ENNReal.coe_eq_zero, not_false_iff, true_or_iff]
      · simp only [Ne.def, coe_ne_top, not_false_iff, true_or_iff]
    obtain ⟨t, ht, ts, mlt, t_top⟩ :
      ∃ t : Set α, MeasurableSet t ∧ t ⊆ s ∧ L / ↑c < μ t ∧ μ t < ∞ :=
      Measure.exists_subset_measure_lt_top hs this
    refine' ⟨piecewise t ht (const α c) (const α 0), fun x => _, _, _⟩
    · refine indicator_le_indicator_of_subset ts (fun x => ?_) x
      exact zero_le _
    · simp only [ht, const_zero, coe_piecewise, coe_const, SimpleFunc.coe_zero, univ_inter,
        piecewise_eq_indicator, ENNReal.coe_indicator, Function.const_apply, lintegral_indicator,
        lintegral_const, Measure.restrict_apply', ENNReal.mul_lt_top ENNReal.coe_ne_top t_top.ne]
    · simp only [ht, const_zero, coe_piecewise, coe_const, SimpleFunc.coe_zero,
        piecewise_eq_indicator, ENNReal.coe_indicator, Function.const_apply, lintegral_indicator,
        lintegral_const, Measure.restrict_apply', univ_inter]
      rwa [mul_comm, ← ENNReal.div_lt_iff]
      · simp only [c_ne_zero, Ne.def, ENNReal.coe_eq_zero, not_false_iff, true_or_iff]
      · simp only [Ne.def, coe_ne_top, not_false_iff, true_or_iff]
  · replace hL : L < ∫⁻ x, f₁ x ∂μ + ∫⁻ x, f₂ x ∂μ := by
      rwa [← lintegral_add_left f₁.measurable.coe_nnreal_ennreal]
    by_cases hf₁ : ∫⁻ x, f₁ x ∂μ = 0
    · simp only [hf₁, zero_add] at hL
      rcases h₂ hL with ⟨g, g_le, g_top, gL⟩
      refine' ⟨g, fun x => (g_le x).trans _, g_top, gL⟩
      simp only [SimpleFunc.coe_add, Pi.add_apply, le_add_iff_nonneg_left, zero_le']
    by_cases hf₂ : ∫⁻ x, f₂ x ∂μ = 0
    · simp only [hf₂, add_zero] at hL
      rcases h₁ hL with ⟨g, g_le, g_top, gL⟩
      refine' ⟨g, fun x => (g_le x).trans _, g_top, gL⟩
      simp only [SimpleFunc.coe_add, Pi.add_apply, le_add_iff_nonneg_right, zero_le']
    obtain ⟨L₁, L₂, hL₁, hL₂, hL⟩ :
      ∃ L₁ L₂ : ℝ≥0∞, (L₁ < ∫⁻ x, f₁ x ∂μ) ∧ (L₂ < ∫⁻ x, f₂ x ∂μ) ∧ L < L₁ + L₂ :=
      ENNReal.exists_lt_add_of_lt_add hL hf₁ hf₂
    rcases h₁ hL₁ with ⟨g₁, g₁_le, g₁_top, hg₁⟩
    rcases h₂ hL₂ with ⟨g₂, g₂_le, g₂_top, hg₂⟩
    refine' ⟨g₁ + g₂, fun x => add_le_add (g₁_le x) (g₂_le x), _, _⟩
    · apply lt_of_le_of_lt _ (add_lt_top.2 ⟨g₁_top, g₂_top⟩)
      rw [← lintegral_add_left g₁.measurable.coe_nnreal_ennreal]
      exact le_rfl
    · apply hL.trans ((ENNReal.add_lt_add hg₁ hg₂).trans_le _)
      rw [← lintegral_add_left g₁.measurable.coe_nnreal_ennreal]
      simp only [coe_add, Pi.add_apply, ENNReal.coe_add, le_rfl]
#align measure_theory.simple_func.exists_lt_lintegral_simple_func_of_lt_lintegral MeasureTheory.SimpleFunc.exists_lt_lintegral_simpleFunc_of_lt_lintegral

theorem exists_lt_lintegral_simpleFunc_of_lt_lintegral {m : MeasurableSpace α} {μ : Measure α}
    [SigmaFinite μ] {f : α → ℝ≥0} {L : ℝ≥0∞} (hL : L < ∫⁻ x, f x ∂μ) :
    ∃ g : α →ₛ ℝ≥0, (∀ x, g x ≤ f x) ∧ ∫⁻ x, g x ∂μ < ∞ ∧ L < ∫⁻ x, g x ∂μ := by
  simp_rw [lintegral_eq_nnreal, lt_iSup_iff] at hL
  rcases hL with ⟨g₀, hg₀, g₀L⟩
  have h'L : L < ∫⁻ x, g₀ x ∂μ := by
    convert g₀L
    rw [← SimpleFunc.lintegral_eq_lintegral, coe_map]
    simp only [Function.comp_apply]
  rcases SimpleFunc.exists_lt_lintegral_simpleFunc_of_lt_lintegral h'L with ⟨g, hg, gL, gtop⟩
  exact ⟨g, fun x => (hg x).trans (coe_le_coe.1 (hg₀ x)), gL, gtop⟩
#align measure_theory.exists_lt_lintegral_simple_func_of_lt_lintegral MeasureTheory.exists_lt_lintegral_simpleFunc_of_lt_lintegral

end SigmaFinite

section TendstoIndicator

variable {α : Type*} [MeasurableSpace α] {A : Set α}
variable {ι : Type*} (L : Filter ι) [IsCountablyGenerated L] {As : ι → Set α}

/-- If the indicators of measurable sets `Aᵢ` tend pointwise almost everywhere to the indicator
of a measurable set `A` and we eventually have `Aᵢ ⊆ B` for some set `B` of finite measure, then
the measures of `Aᵢ` tend to the measure of `A`. -/
lemma tendsto_measure_of_ae_tendsto_indicator {μ : Measure α} (A_mble : MeasurableSet A)
    (As_mble : ∀ i, MeasurableSet (As i)) {B : Set α} (B_mble : MeasurableSet B)
    (B_finmeas : μ B ≠ ∞) (As_le_B : ∀ᶠ i in L, As i ⊆ B)
    (h_lim : ∀ᵐ x ∂μ, ∀ᶠ i in L, x ∈ As i ↔ x ∈ A) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) := by
  simp_rw [← MeasureTheory.lintegral_indicator_one A_mble,
           ← MeasureTheory.lintegral_indicator_one (As_mble _)]
  refine tendsto_lintegral_filter_of_dominated_convergence (B.indicator (1 : α → ℝ≥0∞))
          (eventually_of_forall ?_) ?_ ?_ ?_
  · exact fun i ↦ Measurable.indicator measurable_const (As_mble i)
  · filter_upwards [As_le_B] with i hi
    exact eventually_of_forall (fun x ↦ indicator_le_indicator_of_subset hi (by simp) x)
  · rwa [← lintegral_indicator_one B_mble] at B_finmeas
  · simpa only [show (OfNat.ofNat 1 : α → ℝ≥0∞) = (fun _ ↦ 1) by rfl,
                tendsto_indicator_const_apply_iff_eventually] using h_lim

/-- If `μ` is a finite measure and the indicators of measurable sets `Aᵢ` tend pointwise
almost everywhere to the indicator of a measurable set `A`, then the measures `μ Aᵢ` tend to
the measure `μ A`. -/
lemma tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure [IsCountablyGenerated L]
    {μ : Measure α} [IsFiniteMeasure μ] (A_mble : MeasurableSet A)
    (As_mble : ∀ i, MeasurableSet (As i)) (h_lim : ∀ᵐ x ∂μ, ∀ᶠ i in L, x ∈ As i ↔ x ∈ A) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) :=
  tendsto_measure_of_ae_tendsto_indicator L A_mble As_mble MeasurableSet.univ
    (measure_ne_top μ univ) (eventually_of_forall (fun i ↦ subset_univ (As i))) h_lim

end TendstoIndicator -- section

end MeasureTheory
