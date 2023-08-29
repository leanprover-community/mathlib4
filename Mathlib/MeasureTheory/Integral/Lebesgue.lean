/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

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

set_option autoImplicit true

noncomputable section

open Set hiding restrict restrict_apply

open Filter ENNReal

open Function (support)

open Classical Topology BigOperators NNReal ENNReal MeasureTheory

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
  -- ⊢ ⨆ (g : α →ₛ ℝ≥0∞) (_ : ↑g ≤ fun a => ↑f a), lintegral g μ = lintegral f μ
  exact le_antisymm (iSup₂_le fun g hg => lintegral_mono hg <| le_rfl)
    (le_iSup₂_of_le f le_rfl le_rfl)
#align measure_theory.simple_func.lintegral_eq_lintegral MeasureTheory.SimpleFunc.lintegral_eq_lintegral

@[mono]
theorem lintegral_mono' {m : MeasurableSpace α} ⦃μ ν : Measure α⦄ (hμν : μ ≤ ν) ⦃f g : α → ℝ≥0∞⦄
    (hfg : f ≤ g) : ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂ν := by
  rw [lintegral, lintegral]
  -- ⊢ ⨆ (g : α →ₛ ℝ≥0∞) (_ : ↑g ≤ fun a => f a), SimpleFunc.lintegral g μ ≤ ⨆ (g_1 …
  exact iSup_mono fun φ => iSup_mono' fun hφ => ⟨le_trans hφ hfg, lintegral_mono (le_refl φ) hμν⟩
  -- 🎉 no goals
#align measure_theory.lintegral_mono' MeasureTheory.lintegral_mono'

theorem lintegral_mono ⦃f g : α → ℝ≥0∞⦄ (hfg : f ≤ g) : ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂μ :=
  lintegral_mono' (le_refl μ) hfg
#align measure_theory.lintegral_mono MeasureTheory.lintegral_mono

theorem lintegral_mono_nnreal {f g : α → ℝ≥0} (h : f ≤ g) : ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂μ :=
  lintegral_mono fun a => ENNReal.coe_le_coe.2 (h a)
#align measure_theory.lintegral_mono_nnreal MeasureTheory.lintegral_mono_nnreal

theorem iSup_lintegral_measurable_le_eq_lintegral (f : α → ℝ≥0∞) :
    ⨆ (g : α → ℝ≥0∞) (_ : Measurable g) (_ : g ≤ f), ∫⁻ a, g a ∂μ = ∫⁻ a, f a ∂μ := by
  apply le_antisymm
  -- ⊢ ⨆ (g : α → ℝ≥0∞) (_ : Measurable g) (_ : g ≤ f), ∫⁻ (a : α), g a ∂μ ≤ ∫⁻ (a  …
  · exact iSup_le fun i => iSup_le fun _ => iSup_le fun h'i => lintegral_mono h'i
    -- 🎉 no goals
  · rw [lintegral]
    -- ⊢ ⨆ (g : α →ₛ ℝ≥0∞) (_ : ↑g ≤ fun a => f a), SimpleFunc.lintegral g μ ≤ ⨆ (g : …
    refine' iSup₂_le fun i hi => le_iSup₂_of_le i i.measurable <| le_iSup_of_le hi _
    -- ⊢ SimpleFunc.lintegral i μ ≤ ∫⁻ (a : α), ↑i a ∂μ
    exact le_of_eq (i.lintegral_eq_lintegral _).symm
    -- 🎉 no goals
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
  -- ⊢ ∫⁻ (x : α), c ∂μ = ∫⁻ (a : α), Function.const α c a ∂μ
  rfl
  -- 🎉 no goals
#align measure_theory.lintegral_const MeasureTheory.lintegral_const

theorem lintegral_zero : ∫⁻ _ : α, 0 ∂μ = 0 := by simp
                                                  -- 🎉 no goals
#align measure_theory.lintegral_zero MeasureTheory.lintegral_zero

theorem lintegral_zero_fun : lintegral μ (0 : α → ℝ≥0∞) = 0 :=
  lintegral_zero
#align measure_theory.lintegral_zero_fun MeasureTheory.lintegral_zero_fun

-- @[simp] -- Porting note: simp can prove this
theorem lintegral_one : ∫⁻ _, (1 : ℝ≥0∞) ∂μ = μ univ := by rw [lintegral_const, one_mul]
                                                           -- 🎉 no goals
#align measure_theory.lintegral_one MeasureTheory.lintegral_one

theorem set_lintegral_const (s : Set α) (c : ℝ≥0∞) : ∫⁻ _ in s, c ∂μ = c * μ s := by
  rw [lintegral_const, Measure.restrict_apply_univ]
  -- 🎉 no goals
#align measure_theory.set_lintegral_const MeasureTheory.set_lintegral_const

theorem set_lintegral_one (s) : ∫⁻ _ in s, 1 ∂μ = μ s := by rw [set_lintegral_const, one_mul]
                                                            -- 🎉 no goals
#align measure_theory.set_lintegral_one MeasureTheory.set_lintegral_one

theorem set_lintegral_const_lt_top [IsFiniteMeasure μ] (s : Set α) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    ∫⁻ _ in s, c ∂μ < ∞ := by
  rw [lintegral_const]
  -- ⊢ c * ↑↑(Measure.restrict μ s) univ < ⊤
  exact ENNReal.mul_lt_top hc (measure_ne_top (μ.restrict s) univ)
  -- 🎉 no goals
#align measure_theory.set_lintegral_const_lt_top MeasureTheory.set_lintegral_const_lt_top

theorem lintegral_const_lt_top [IsFiniteMeasure μ] {c : ℝ≥0∞} (hc : c ≠ ∞) : ∫⁻ _, c ∂μ < ∞ := by
  simpa only [Measure.restrict_univ] using set_lintegral_const_lt_top (univ : Set α) hc
  -- 🎉 no goals
#align measure_theory.lintegral_const_lt_top MeasureTheory.lintegral_const_lt_top

section

variable (μ)

/-- For any function `f : α → ℝ≥0∞`, there exists a measurable function `g ≤ f` with the same
integral. -/
theorem exists_measurable_le_lintegral_eq (f : α → ℝ≥0∞) :
    ∃ g : α → ℝ≥0∞, Measurable g ∧ g ≤ f ∧ ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ := by
  cases' eq_or_ne (∫⁻ a, f a ∂μ) 0 with h₀ h₀
  -- ⊢ ∃ g, Measurable g ∧ g ≤ f ∧ ∫⁻ (a : α), f a ∂μ = ∫⁻ (a : α), g a ∂μ
  · exact ⟨0, measurable_zero, zero_le f, h₀.trans lintegral_zero.symm⟩
    -- 🎉 no goals
  rcases exists_seq_strictMono_tendsto' h₀.bot_lt with ⟨L, _, hLf, hL_tendsto⟩
  -- ⊢ ∃ g, Measurable g ∧ g ≤ f ∧ ∫⁻ (a : α), f a ∂μ = ∫⁻ (a : α), g a ∂μ
  have : ∀ n, ∃ g : α → ℝ≥0∞, Measurable g ∧ g ≤ f ∧ L n < ∫⁻ a, g a ∂μ := by
    intro n
    simpa only [← iSup_lintegral_measurable_le_eq_lintegral f, lt_iSup_iff, exists_prop] using
      (hLf n).2
  choose g hgm hgf hLg using this
  -- ⊢ ∃ g, Measurable g ∧ g ≤ f ∧ ∫⁻ (a : α), f a ∂μ = ∫⁻ (a : α), g a ∂μ
  refine'
    ⟨fun x => ⨆ n, g n x, measurable_iSup hgm, fun x => iSup_le fun n => hgf n x, le_antisymm _ _⟩
  · refine' le_of_tendsto' hL_tendsto fun n => (hLg n).le.trans <| lintegral_mono fun x => _
    -- ⊢ g n x ≤ (fun x => ⨆ (n : ℕ), g n x) x
    exact le_iSup (fun n => g n x) n
    -- 🎉 no goals
  · exact lintegral_mono fun x => iSup_le fun n => hgf n x
    -- 🎉 no goals
#align measure_theory.exists_measurable_le_lintegral_eq MeasureTheory.exists_measurable_le_lintegral_eq

end

/-- `∫⁻ a in s, f a ∂μ` is defined as the supremum of integrals of simple functions
`φ : α →ₛ ℝ≥0∞` such that `φ ≤ f`. This lemma says that it suffices to take
functions `φ : α →ₛ ℝ≥0`. -/
theorem lintegral_eq_nnreal {m : MeasurableSpace α} (f : α → ℝ≥0∞) (μ : Measure α) :
    ∫⁻ a, f a ∂μ =
      ⨆ (φ : α →ₛ ℝ≥0) (_ : ∀ x, ↑(φ x) ≤ f x), (φ.map ((↑) : ℝ≥0 → ℝ≥0∞)).lintegral μ := by
  rw [lintegral]
  -- ⊢ ⨆ (g : α →ₛ ℝ≥0∞) (_ : ↑g ≤ fun a => f a), SimpleFunc.lintegral g μ = ⨆ (φ : …
  refine'
    le_antisymm (iSup₂_le fun φ hφ => _) (iSup_mono' fun φ => ⟨φ.map ((↑) : ℝ≥0 → ℝ≥0∞), le_rfl⟩)
  by_cases h : ∀ᵐ a ∂μ, φ a ≠ ∞
  -- ⊢ SimpleFunc.lintegral φ μ ≤ ⨆ (φ : α →ₛ ℝ≥0) (_ : ∀ (x : α), ↑(↑φ x) ≤ f x),  …
  · let ψ := φ.map ENNReal.toNNReal
    -- ⊢ SimpleFunc.lintegral φ μ ≤ ⨆ (φ : α →ₛ ℝ≥0) (_ : ∀ (x : α), ↑(↑φ x) ≤ f x),  …
    replace h : ψ.map ((↑) : ℝ≥0 → ℝ≥0∞) =ᵐ[μ] φ := h.mono fun a => ENNReal.coe_toNNReal
    -- ⊢ SimpleFunc.lintegral φ μ ≤ ⨆ (φ : α →ₛ ℝ≥0) (_ : ∀ (x : α), ↑(↑φ x) ≤ f x),  …
    have : ∀ x, ↑(ψ x) ≤ f x := fun x => le_trans ENNReal.coe_toNNReal_le_self (hφ x)
    -- ⊢ SimpleFunc.lintegral φ μ ≤ ⨆ (φ : α →ₛ ℝ≥0) (_ : ∀ (x : α), ↑(↑φ x) ≤ f x),  …
    exact
      le_iSup_of_le (φ.map ENNReal.toNNReal) (le_iSup_of_le this (ge_of_eq <| lintegral_congr h))
  · have h_meas : μ (φ ⁻¹' {∞}) ≠ 0 := mt measure_zero_iff_ae_nmem.1 h
    -- ⊢ SimpleFunc.lintegral φ μ ≤ ⨆ (φ : α →ₛ ℝ≥0) (_ : ∀ (x : α), ↑(↑φ x) ≤ f x),  …
    refine' le_trans le_top (ge_of_eq <| (iSup_eq_top _).2 fun b hb => _)
    -- ⊢ ∃ i, b < ⨆ (_ : ∀ (x : α), ↑(↑i x) ≤ f x), SimpleFunc.lintegral (SimpleFunc. …
    obtain ⟨n, hn⟩ : ∃ n : ℕ, b < n * μ (φ ⁻¹' {∞})
    -- ⊢ ∃ n, b < ↑n * ↑↑μ (↑φ ⁻¹' {⊤})
    exact exists_nat_mul_gt h_meas (ne_of_lt hb)
    -- ⊢ ∃ i, b < ⨆ (_ : ∀ (x : α), ↑(↑i x) ≤ f x), SimpleFunc.lintegral (SimpleFunc. …
    use (const α (n : ℝ≥0)).restrict (φ ⁻¹' {∞})
    -- ⊢ b < ⨆ (_ : ∀ (x : α), ↑(↑(restrict (const α ↑n) (↑φ ⁻¹' {⊤})) x) ≤ f x), Sim …
    simp only [lt_iSup_iff, exists_prop, coe_restrict, φ.measurableSet_preimage, coe_const,
      ENNReal.coe_indicator, map_coe_ennreal_restrict, SimpleFunc.map_const, ENNReal.coe_nat,
      restrict_const_lintegral]
    refine' ⟨indicator_le fun x hx => le_trans _ (hφ _), hn⟩
    -- ⊢ ↑(Function.const α (↑n) x) ≤ ↑φ x
    simp only [mem_preimage, mem_singleton_iff] at hx
    -- ⊢ ↑(Function.const α (↑n) x) ≤ ↑φ x
    simp only [hx, le_top]
    -- 🎉 no goals
#align measure_theory.lintegral_eq_nnreal MeasureTheory.lintegral_eq_nnreal

theorem exists_simpleFunc_forall_lintegral_sub_lt_of_pos {f : α → ℝ≥0∞} (h : ∫⁻ x, f x ∂μ ≠ ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ φ : α →ₛ ℝ≥0,
      (∀ x, ↑(φ x) ≤ f x) ∧
        ∀ ψ : α →ₛ ℝ≥0, (∀ x, ↑(ψ x) ≤ f x) → (map (↑) (ψ - φ)).lintegral μ < ε := by
  rw [lintegral_eq_nnreal] at h
  -- ⊢ ∃ φ, (∀ (x : α), ↑(↑φ x) ≤ f x) ∧ ∀ (ψ : α →ₛ ℝ≥0), (∀ (x : α), ↑(↑ψ x) ≤ f  …
  have := ENNReal.lt_add_right h hε
  -- ⊢ ∃ φ, (∀ (x : α), ↑(↑φ x) ≤ f x) ∧ ∀ (ψ : α →ₛ ℝ≥0), (∀ (x : α), ↑(↑ψ x) ≤ f  …
  erw [ENNReal.biSup_add] at this <;> [skip; exact ⟨0, fun x => zero_le _⟩]
  -- ⊢ ∃ φ, (∀ (x : α), ↑(↑φ x) ≤ f x) ∧ ∀ (ψ : α →ₛ ℝ≥0), (∀ (x : α), ↑(↑ψ x) ≤ f  …
  simp_rw [lt_iSup_iff, iSup_lt_iff, iSup_le_iff] at this
  -- ⊢ ∃ φ, (∀ (x : α), ↑(↑φ x) ≤ f x) ∧ ∀ (ψ : α →ₛ ℝ≥0), (∀ (x : α), ↑(↑ψ x) ≤ f  …
  rcases this with ⟨φ, hle : ∀ x, ↑(φ x) ≤ f x, b, hbφ, hb⟩
  -- ⊢ ∃ φ, (∀ (x : α), ↑(↑φ x) ≤ f x) ∧ ∀ (ψ : α →ₛ ℝ≥0), (∀ (x : α), ↑(↑ψ x) ≤ f  …
  refine' ⟨φ, hle, fun ψ hψ => _⟩
  -- ⊢ SimpleFunc.lintegral (SimpleFunc.map ENNReal.some (ψ - φ)) μ < ε
  have : (map (↑) φ).lintegral μ ≠ ∞ := ne_top_of_le_ne_top h (by exact le_iSup₂ (α := ℝ≥0∞) φ hle)
  -- ⊢ SimpleFunc.lintegral (SimpleFunc.map ENNReal.some (ψ - φ)) μ < ε
  rw [← ENNReal.add_lt_add_iff_left this, ← add_lintegral, ← SimpleFunc.map_add @ENNReal.coe_add]
  -- ⊢ SimpleFunc.lintegral (SimpleFunc.map ENNReal.some (φ + (ψ - φ))) μ < SimpleF …
  refine' (hb _ fun x => le_trans _ (max_le (hle x) (hψ x))).trans_lt hbφ
  -- ⊢ ↑(↑(φ + (ψ - φ)) x) ≤ max ↑(↑φ x) ↑(↑ψ x)
  norm_cast
  -- ⊢ ↑(φ + (ψ - φ)) x ≤ max (↑φ x) (↑ψ x)
  simp only [add_apply, sub_apply, add_tsub_eq_max]
  -- ⊢ max (↑φ x) (↑ψ x) ≤ max (↑φ x) (↑ψ x)
  rfl
  -- 🎉 no goals
#align measure_theory.exists_simple_func_forall_lintegral_sub_lt_of_pos MeasureTheory.exists_simpleFunc_forall_lintegral_sub_lt_of_pos

theorem iSup_lintegral_le {ι : Sort*} (f : ι → α → ℝ≥0∞) :
    ⨆ i, ∫⁻ a, f i a ∂μ ≤ ∫⁻ a, ⨆ i, f i a ∂μ := by
  simp only [← iSup_apply]
  -- ⊢ ⨆ (i : ι), ∫⁻ (a : α), f i a ∂μ ≤ ∫⁻ (a : α), iSup (fun i => f i) a ∂μ
  exact (monotone_lintegral μ).le_map_iSup
  -- 🎉 no goals
#align measure_theory.supr_lintegral_le MeasureTheory.iSup_lintegral_le

theorem iSup₂_lintegral_le {ι : Sort*} {ι' : ι → Sort*} (f : ∀ i, ι' i → α → ℝ≥0∞) :
    ⨆ (i) (j), ∫⁻ a, f i j a ∂μ ≤ ∫⁻ a, ⨆ (i) (j), f i j a ∂μ := by
  convert (monotone_lintegral μ).le_map_iSup₂ f with a
  -- ⊢ ⨆ (i : ι) (j : ι' i), f i j a = iSup (fun i => ⨆ (j : ι' i), f i j) a
  simp only [iSup_apply]
  -- 🎉 no goals
#align measure_theory.supr₂_lintegral_le MeasureTheory.iSup₂_lintegral_le

theorem le_iInf_lintegral {ι : Sort*} (f : ι → α → ℝ≥0∞) :
    ∫⁻ a, ⨅ i, f i a ∂μ ≤ ⨅ i, ∫⁻ a, f i a ∂μ := by
  simp only [← iInf_apply]
  -- ⊢ ∫⁻ (a : α), iInf (fun i => f i) a ∂μ ≤ ⨅ (i : ι), ∫⁻ (a : α), f i a ∂μ
  exact (monotone_lintegral μ).map_iInf_le
  -- 🎉 no goals
#align measure_theory.le_infi_lintegral MeasureTheory.le_iInf_lintegral

theorem le_iInf₂_lintegral {ι : Sort*} {ι' : ι → Sort*} (f : ∀ i, ι' i → α → ℝ≥0∞) :
    ∫⁻ a, ⨅ (i) (h : ι' i), f i h a ∂μ ≤ ⨅ (i) (h : ι' i), ∫⁻ a, f i h a ∂μ := by
  convert(monotone_lintegral μ).map_iInf₂_le f with a
  -- ⊢ ⨅ (i : ι) (h : ι' i), f i h a = iInf (fun i => ⨅ (j : ι' i), f i j) a
  simp only [iInf_apply]
  -- 🎉 no goals
#align measure_theory.le_infi₂_lintegral MeasureTheory.le_iInf₂_lintegral

theorem lintegral_mono_ae {f g : α → ℝ≥0∞} (h : ∀ᵐ a ∂μ, f a ≤ g a) :
    ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂μ := by
  rcases exists_measurable_superset_of_null h with ⟨t, hts, ht, ht0⟩
  -- ⊢ ∫⁻ (a : α), f a ∂μ ≤ ∫⁻ (a : α), g a ∂μ
  have : ∀ᵐ x ∂μ, x ∉ t := measure_zero_iff_ae_nmem.1 ht0
  -- ⊢ ∫⁻ (a : α), f a ∂μ ≤ ∫⁻ (a : α), g a ∂μ
  rw [lintegral, lintegral]
  -- ⊢ ⨆ (g : α →ₛ ℝ≥0∞) (_ : ↑g ≤ fun a => f a), SimpleFunc.lintegral g μ ≤ ⨆ (g_1 …
  refine' iSup_le fun s => iSup_le fun hfs => le_iSup_of_le (s.restrict tᶜ) <| le_iSup_of_le _ _
  -- ⊢ ↑(restrict s tᶜ) ≤ fun a => g a
  · intro a
    -- ⊢ ↑(restrict s tᶜ) a ≤ (fun a => g a) a
    by_cases h : a ∈ t <;> simp [h, restrict_apply s ht.compl, ht.compl]
    -- ⊢ ↑(restrict s tᶜ) a ≤ (fun a => g a) a
                           -- 🎉 no goals
                           -- ⊢ ↑s a ≤ g a
    exact le_trans (hfs a) (_root_.by_contradiction fun hnfg => h (hts hnfg))
    -- 🎉 no goals
  · refine' le_of_eq (SimpleFunc.lintegral_congr <| this.mono fun a hnt => _)
    -- ⊢ ↑s a = ↑(restrict s tᶜ) a
    by_cases hat : a ∈ t <;> simp [hat, restrict_apply s ht.compl]
    -- ⊢ ↑s a = ↑(restrict s tᶜ) a
                             -- ⊢ ↑s a = 0
                             -- 🎉 no goals
    exact (hnt hat).elim
    -- 🎉 no goals
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

theorem lintegral_congr_ae {f g : α → ℝ≥0∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ :=
  le_antisymm (lintegral_mono_ae <| h.le) (lintegral_mono_ae <| h.symm.le)
#align measure_theory.lintegral_congr_ae MeasureTheory.lintegral_congr_ae

theorem lintegral_congr {f g : α → ℝ≥0∞} (h : ∀ a, f a = g a) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ := by
  simp only [h]
  -- 🎉 no goals
#align measure_theory.lintegral_congr MeasureTheory.lintegral_congr

theorem set_lintegral_congr {f : α → ℝ≥0∞} {s t : Set α} (h : s =ᵐ[μ] t) :
    ∫⁻ x in s, f x ∂μ = ∫⁻ x in t, f x ∂μ := by rw [Measure.restrict_congr_set h]
                                                -- 🎉 no goals
#align measure_theory.set_lintegral_congr MeasureTheory.set_lintegral_congr

theorem set_lintegral_congr_fun {f g : α → ℝ≥0∞} {s : Set α} (hs : MeasurableSet s)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → f x = g x) : ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ := by
  rw [lintegral_congr_ae]
  -- ⊢ (fun x => f x) =ᵐ[Measure.restrict μ s] fun a => g a
  rw [EventuallyEq]
  -- ⊢ ∀ᵐ (x : α) ∂Measure.restrict μ s, f x = g x
  rwa [ae_restrict_iff' hs]
  -- 🎉 no goals
#align measure_theory.set_lintegral_congr_fun MeasureTheory.set_lintegral_congr_fun

theorem lintegral_ofReal_le_lintegral_nnnorm (f : α → ℝ) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ∫⁻ x, ‖f x‖₊ ∂μ := by
  simp_rw [← ofReal_norm_eq_coe_nnnorm]
  -- ⊢ ∫⁻ (x : α), ENNReal.ofReal (f x) ∂μ ≤ ∫⁻ (x : α), ENNReal.ofReal ‖f x‖ ∂μ
  refine' lintegral_mono fun x => ENNReal.ofReal_le_ofReal _
  -- ⊢ f x ≤ ‖f x‖
  rw [Real.norm_eq_abs]
  -- ⊢ f x ≤ |f x|
  exact le_abs_self (f x)
  -- 🎉 no goals
#align measure_theory.lintegral_of_real_le_lintegral_nnnorm MeasureTheory.lintegral_ofReal_le_lintegral_nnnorm

theorem lintegral_nnnorm_eq_of_ae_nonneg {f : α → ℝ} (h_nonneg : 0 ≤ᵐ[μ] f) :
    ∫⁻ x, ‖f x‖₊ ∂μ = ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  apply lintegral_congr_ae
  -- ⊢ (fun a => ↑‖f a‖₊) =ᵐ[μ] fun a => ENNReal.ofReal (f a)
  filter_upwards [h_nonneg]with x hx
  -- ⊢ ↑‖f x‖₊ = ENNReal.ofReal (f x)
  rw [Real.nnnorm_of_nonneg hx, ENNReal.ofReal_eq_coe_nnreal hx]
  -- 🎉 no goals
#align measure_theory.lintegral_nnnorm_eq_of_ae_nonneg MeasureTheory.lintegral_nnnorm_eq_of_ae_nonneg

theorem lintegral_nnnorm_eq_of_nonneg {f : α → ℝ} (h_nonneg : 0 ≤ f) :
    ∫⁻ x, ‖f x‖₊ ∂μ = ∫⁻ x, ENNReal.ofReal (f x) ∂μ :=
  lintegral_nnnorm_eq_of_ae_nonneg (Filter.eventually_of_forall h_nonneg)
#align measure_theory.lintegral_nnnorm_eq_of_nonneg MeasureTheory.lintegral_nnnorm_eq_of_nonneg

/-- Monotone convergence theorem -- sometimes called Beppo-Levi convergence.
See `lintegral_iSup_directed` for a more general form. -/
theorem lintegral_iSup {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, Measurable (f n)) (h_mono : Monotone f) :
    ∫⁻ a, ⨆ n, f n a ∂μ = ⨆ n, ∫⁻ a, f n a ∂μ := by
  set c : ℝ≥0 → ℝ≥0∞ := (↑)
  -- ⊢ ∫⁻ (a : α), ⨆ (n : ℕ), f n a ∂μ = ⨆ (n : ℕ), ∫⁻ (a : α), f n a ∂μ
  set F := fun a : α => ⨆ n, f n a
  -- ⊢ lintegral μ F = ⨆ (n : ℕ), ∫⁻ (a : α), f n a ∂μ
  have _ : Measurable F := measurable_iSup hf
  -- ⊢ lintegral μ F = ⨆ (n : ℕ), ∫⁻ (a : α), f n a ∂μ
  refine' le_antisymm _ (iSup_lintegral_le _)
  -- ⊢ lintegral μ F ≤ ⨆ (n : ℕ), ∫⁻ (a : α), f n a ∂μ
  rw [lintegral_eq_nnreal]
  -- ⊢ ⨆ (φ : α →ₛ ℝ≥0) (_ : ∀ (x : α), ↑(↑φ x) ≤ ⨆ (n : ℕ), f n x), SimpleFunc.lin …
  refine' iSup_le fun s => iSup_le fun hsf => _
  -- ⊢ SimpleFunc.lintegral (SimpleFunc.map ENNReal.some s) μ ≤ ⨆ (n : ℕ), ∫⁻ (a :  …
  refine' ENNReal.le_of_forall_lt_one_mul_le fun a ha => _
  -- ⊢ a * SimpleFunc.lintegral (SimpleFunc.map ENNReal.some s) μ ≤ ⨆ (n : ℕ), ∫⁻ ( …
  rcases ENNReal.lt_iff_exists_coe.1 ha with ⟨r, rfl, _⟩
  -- ⊢ ↑r * SimpleFunc.lintegral (SimpleFunc.map ENNReal.some s) μ ≤ ⨆ (n : ℕ), ∫⁻  …
  have ha : r < 1 := ENNReal.coe_lt_coe.1 ha
  -- ⊢ ↑r * SimpleFunc.lintegral (SimpleFunc.map ENNReal.some s) μ ≤ ⨆ (n : ℕ), ∫⁻  …
  let rs := s.map fun a => r * a
  -- ⊢ ↑r * SimpleFunc.lintegral (SimpleFunc.map ENNReal.some s) μ ≤ ⨆ (n : ℕ), ∫⁻  …
  have eq_rs : (const α r : α →ₛ ℝ≥0∞) * map c s = rs.map c := by
    ext1 a
    exact ENNReal.coe_mul.symm
  have eq : ∀ p, rs.map c ⁻¹' {p} = ⋃ n, rs.map c ⁻¹' {p} ∩ { a | p ≤ f n a } := by
    intro p
    rw [← inter_iUnion]; nth_rw 1 [← inter_univ (map c rs ⁻¹' {p})]
    refine' Set.ext fun x => and_congr_right fun hx => true_iff_iff.2 _
    by_cases p_eq : p = 0
    · simp [p_eq]
    simp [-ENNReal.coe_mul] at hx
    subst hx
    have : r * s x ≠ 0 := by rwa [Ne, ← ENNReal.coe_eq_zero]
    have : s x ≠ 0 := by
      refine' mt _ this
      intro h
      rw [h, mul_zero]
    have : (rs.map c) x < ⨆ n : ℕ, f n x := by
      refine' lt_of_lt_of_le (ENNReal.coe_lt_coe.2 _) (hsf x)
      suffices : r * s x < 1 * s x
      simpa
      exact mul_lt_mul_of_pos_right ha (pos_iff_ne_zero.2 this)
    rcases lt_iSup_iff.1 this with ⟨i, hi⟩
    exact mem_iUnion.2 ⟨i, le_of_lt hi⟩
  have mono : ∀ r : ℝ≥0∞, Monotone fun n => rs.map c ⁻¹' {r} ∩ { a | r ≤ f n a } := by
    intro r i j h
    refine' inter_subset_inter (Subset.refl _) _
    intro x (hx : r ≤ f i x)
    exact le_trans hx (h_mono h x)
  have h_meas : ∀ n, MeasurableSet { a : α | (⇑(map c rs)) a ≤ f n a } := fun n =>
    measurableSet_le (SimpleFunc.measurable _) (hf n)
  calc
    (r : ℝ≥0∞) * (s.map c).lintegral μ = ∑ r in (rs.map c).range, r * μ (rs.map c ⁻¹' {r}) := by
      rw [← const_mul_lintegral, eq_rs, SimpleFunc.lintegral]
    _ = ∑ r in (rs.map c).range, r * μ (⋃ n, rs.map c ⁻¹' {r} ∩ { a | r ≤ f n a }) := by
      simp only [(eq _).symm]
    _ = ∑ r in (rs.map c).range, ⨆ n, r * μ (rs.map c ⁻¹' {r} ∩ { a | r ≤ f n a }) :=
      (Finset.sum_congr rfl fun x _ => by
        rw [measure_iUnion_eq_iSup (directed_of_sup <| mono x), ENNReal.mul_iSup])
    _ = ⨆ n, ∑ r in (rs.map c).range, r * μ (rs.map c ⁻¹' {r} ∩ { a | r ≤ f n a }) := by
      rw [ENNReal.finset_sum_iSup_nat]
      intro p i j h
      exact mul_le_mul_left' (measure_mono <| mono p h) _
    _ ≤ ⨆ n : ℕ, ((rs.map c).restrict { a | (rs.map c) a ≤ f n a }).lintegral μ := by
      refine' iSup_mono fun n => _
      rw [restrict_lintegral _ (h_meas n)]
      · refine' le_of_eq (Finset.sum_congr rfl fun r _ => _)
        congr 2 with a
        refine' and_congr_right _
        simp (config := { contextual := true })
    _ ≤ ⨆ n, ∫⁻ a, f n a ∂μ := by
      refine' iSup_mono fun n => _
      rw [← SimpleFunc.lintegral_eq_lintegral]
      refine' lintegral_mono fun a => _
      simp only [map_apply] at h_meas
      simp only [coe_map, restrict_apply _ (h_meas _), (· ∘ ·)]
      exact indicator_apply_le id
#align measure_theory.lintegral_supr MeasureTheory.lintegral_iSup

/-- Monotone convergence theorem -- sometimes called Beppo-Levi convergence. Version with
ae_measurable functions. -/
theorem lintegral_iSup' {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, AEMeasurable (f n) μ)
    (h_mono : ∀ᵐ x ∂μ, Monotone fun n => f n x) : ∫⁻ a, ⨆ n, f n a ∂μ = ⨆ n, ∫⁻ a, f n a ∂μ := by
  simp_rw [← iSup_apply]
  -- ⊢ ∫⁻ (a : α), iSup (fun i => f i) a ∂μ = ⨆ (n : ℕ), ∫⁻ (a : α), f n a ∂μ
  let p : α → (ℕ → ℝ≥0∞) → Prop := fun _ f' => Monotone f'
  -- ⊢ ∫⁻ (a : α), iSup (fun i => f i) a ∂μ = ⨆ (n : ℕ), ∫⁻ (a : α), f n a ∂μ
  have hp : ∀ᵐ x ∂μ, p x fun i => f i x := h_mono
  -- ⊢ ∫⁻ (a : α), iSup (fun i => f i) a ∂μ = ⨆ (n : ℕ), ∫⁻ (a : α), f n a ∂μ
  have h_ae_seq_mono : Monotone (aeSeq hf p) := by
    intro n m hnm x
    by_cases hx : x ∈ aeSeqSet hf p
    · exact aeSeq.prop_of_mem_aeSeqSet hf hx hnm
    · simp only [aeSeq, hx, if_false]
      exact le_rfl
  rw [lintegral_congr_ae (aeSeq.iSup hf hp).symm]
  -- ⊢ ∫⁻ (a : α), iSup (fun n => aeSeq hf (fun x => p x) n) a ∂μ = ⨆ (n : ℕ), ∫⁻ ( …
  simp_rw [iSup_apply]
  -- ⊢ ∫⁻ (a : α), ⨆ (i : ℕ), aeSeq hf (fun x f' => Monotone f') i a ∂μ = ⨆ (n : ℕ) …
  rw [@lintegral_iSup _ _ μ _ (aeSeq.measurable hf p) h_ae_seq_mono]
  -- ⊢ ⨆ (n : ℕ), ∫⁻ (a : α), aeSeq hf p n a ∂μ = ⨆ (n : ℕ), ∫⁻ (a : α), f n a ∂μ
  congr
  -- ⊢ (fun n => ∫⁻ (a : α), aeSeq hf p n a ∂μ) = fun n => ∫⁻ (a : α), f n a ∂μ
  exact funext fun n => lintegral_congr_ae (aeSeq.aeSeq_n_eq_fun_n_ae hf hp n)
  -- 🎉 no goals
#align measure_theory.lintegral_supr' MeasureTheory.lintegral_iSup'

/-- Monotone convergence theorem expressed with limits -/
theorem lintegral_tendsto_of_tendsto_of_monotone {f : ℕ → α → ℝ≥0∞} {F : α → ℝ≥0∞}
    (hf : ∀ n, AEMeasurable (f n) μ) (h_mono : ∀ᵐ x ∂μ, Monotone fun n => f n x)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 <| F x)) :
    Tendsto (fun n => ∫⁻ x, f n x ∂μ) atTop (𝓝 <| ∫⁻ x, F x ∂μ) := by
  have : Monotone fun n => ∫⁻ x, f n x ∂μ := fun i j hij =>
    lintegral_mono_ae (h_mono.mono fun x hx => hx hij)
  suffices key : ∫⁻ x, F x ∂μ = ⨆ n, ∫⁻ x, f n x ∂μ
  -- ⊢ Tendsto (fun n => ∫⁻ (x : α), f n x ∂μ) atTop (𝓝 (∫⁻ (x : α), F x ∂μ))
  · rw [key]
    -- ⊢ Tendsto (fun n => ∫⁻ (x : α), f n x ∂μ) atTop (𝓝 (⨆ (n : ℕ), ∫⁻ (x : α), f n …
    exact tendsto_atTop_iSup this
    -- 🎉 no goals
  rw [← lintegral_iSup' hf h_mono]
  -- ⊢ ∫⁻ (x : α), F x ∂μ = ∫⁻ (a : α), ⨆ (n : ℕ), f n a ∂μ
  refine' lintegral_congr_ae _
  -- ⊢ (fun x => F x) =ᵐ[μ] fun a => ⨆ (n : ℕ), f n a
  filter_upwards [h_mono,
    h_tendsto] with _ hx_mono hx_tendsto using tendsto_nhds_unique hx_tendsto
      (tendsto_atTop_iSup hx_mono)
#align measure_theory.lintegral_tendsto_of_tendsto_of_monotone MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone

theorem lintegral_eq_iSup_eapprox_lintegral {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a, f a ∂μ = ⨆ n, (eapprox f n).lintegral μ :=
  calc
    ∫⁻ a, f a ∂μ = ∫⁻ a, ⨆ n, (eapprox f n : α → ℝ≥0∞) a ∂μ := by
      congr; ext a; rw [iSup_eapprox_apply f hf]
      -- ⊢ (fun a => f a) = fun a => ⨆ (n : ℕ), ↑(eapprox f n) a
             -- ⊢ f a = ⨆ (n : ℕ), ↑(eapprox f n) a
                    -- 🎉 no goals
    _ = ⨆ n, ∫⁻ a, (eapprox f n : α → ℝ≥0∞) a ∂μ := by
      rw [lintegral_iSup]
      -- ⊢ ∀ (n : ℕ), Measurable fun a => ↑(eapprox f n) a
      · measurability
        -- 🎉 no goals
      · intro i j h
        -- ⊢ (fun n a => ↑(eapprox f n) a) i ≤ (fun n a => ↑(eapprox f n) a) j
        exact monotone_eapprox f h
        -- 🎉 no goals
    _ = ⨆ n, (eapprox f n).lintegral μ := by
      congr; ext n; rw [(eapprox f n).lintegral_eq_lintegral]
      -- ⊢ (fun n => ∫⁻ (a : α), ↑(eapprox f n) a ∂μ) = fun n => SimpleFunc.lintegral ( …
             -- ⊢ ∫⁻ (a : α), ↑(eapprox f n) a ∂μ = SimpleFunc.lintegral (eapprox f n) μ
                    -- 🎉 no goals
#align measure_theory.lintegral_eq_supr_eapprox_lintegral MeasureTheory.lintegral_eq_iSup_eapprox_lintegral

/-- If `f` has finite integral, then `∫⁻ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. This lemma states states this fact in terms of `ε` and `δ`. -/
theorem exists_pos_set_lintegral_lt_of_measure_lt {f : α → ℝ≥0∞} (h : ∫⁻ x, f x ∂μ ≠ ∞) {ε : ℝ≥0∞}
    (hε : ε ≠ 0) : ∃ δ > 0, ∀ s, μ s < δ → ∫⁻ x in s, f x ∂μ < ε := by
  rcases exists_between hε.bot_lt with ⟨ε₂, hε₂0 : 0 < ε₂, hε₂ε⟩
  -- ⊢ ∃ δ, δ > 0 ∧ ∀ (s : Set α), ↑↑μ s < δ → ∫⁻ (x : α) in s, f x ∂μ < ε
  rcases exists_between hε₂0 with ⟨ε₁, hε₁0, hε₁₂⟩
  -- ⊢ ∃ δ, δ > 0 ∧ ∀ (s : Set α), ↑↑μ s < δ → ∫⁻ (x : α) in s, f x ∂μ < ε
  rcases exists_simpleFunc_forall_lintegral_sub_lt_of_pos h hε₁0.ne' with ⟨φ, _, hφ⟩
  -- ⊢ ∃ δ, δ > 0 ∧ ∀ (s : Set α), ↑↑μ s < δ → ∫⁻ (x : α) in s, f x ∂μ < ε
  rcases φ.exists_forall_le with ⟨C, hC⟩
  -- ⊢ ∃ δ, δ > 0 ∧ ∀ (s : Set α), ↑↑μ s < δ → ∫⁻ (x : α) in s, f x ∂μ < ε
  use (ε₂ - ε₁) / C, ENNReal.div_pos_iff.2 ⟨(tsub_pos_iff_lt.2 hε₁₂).ne', ENNReal.coe_ne_top⟩
  -- ⊢ ∀ (s : Set α), ↑↑μ s < (ε₂ - ε₁) / ↑C → ∫⁻ (x : α) in s, f x ∂μ < ε
  refine' fun s hs => lt_of_le_of_lt _ hε₂ε
  -- ⊢ ∫⁻ (x : α) in s, f x ∂μ ≤ ε₂
  simp only [lintegral_eq_nnreal, iSup_le_iff]
  -- ⊢ ∀ (i : α →ₛ ℝ≥0), (∀ (x : α), ↑(↑i x) ≤ f x) → SimpleFunc.lintegral (SimpleF …
  intro ψ hψ
  -- ⊢ SimpleFunc.lintegral (SimpleFunc.map ENNReal.some ψ) (Measure.restrict μ s)  …
  calc
    (map (↑) ψ).lintegral (μ.restrict s) ≤
        (map (↑) φ).lintegral (μ.restrict s) + (map (↑) (ψ - φ)).lintegral (μ.restrict s) := by
      rw [← SimpleFunc.add_lintegral, ← SimpleFunc.map_add @ENNReal.coe_add]
      refine' SimpleFunc.lintegral_mono (fun x => _) le_rfl
      simp only [add_tsub_eq_max, le_max_right, coe_map, Function.comp_apply, SimpleFunc.coe_add,
        SimpleFunc.coe_sub, Pi.add_apply, Pi.sub_apply, WithTop.coe_max (φ x) (ψ x), ENNReal.some]
    _ ≤ (map (↑) φ).lintegral (μ.restrict s) + ε₁ := by
      refine' add_le_add le_rfl (le_trans _ (hφ _ hψ).le)
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
  -- ⊢ ∀ᶠ (a : ι) in l, ∫⁻ (x : α) in s a, f x ∂μ < ε
  rcases exists_pos_set_lintegral_lt_of_measure_lt h ε0.ne' with ⟨δ, δ0, hδ⟩
  -- ⊢ ∀ᶠ (a : ι) in l, ∫⁻ (x : α) in s a, f x ∂μ < ε
  exact (hl δ δ0).mono fun i => hδ _
  -- 🎉 no goals
#align measure_theory.tendsto_set_lintegral_zero MeasureTheory.tendsto_set_lintegral_zero

/-- The sum of the lower Lebesgue integrals of two functions is less than or equal to the integral
of their sum. The other inequality needs one of these functions to be (a.e.-)measurable. -/
theorem le_lintegral_add (f g : α → ℝ≥0∞) :
    ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ ≤ ∫⁻ a, f a + g a ∂μ := by
  simp only [lintegral]
  -- ⊢ (⨆ (g : α →ₛ ℝ≥0∞) (_ : ↑g ≤ fun a => f a), SimpleFunc.lintegral g μ) + ⨆ (g …
  refine' ENNReal.biSup_add_biSup_le' (p := fun h : α →ₛ ℝ≥0∞ => h ≤ f)
    (q := fun h : α →ₛ ℝ≥0∞ => h ≤ g) ⟨0, zero_le f⟩ ⟨0, zero_le g⟩ fun f' hf' g' hg' => _
  exact le_iSup₂_of_le (f' + g') (add_le_add hf' hg') (add_lintegral _ _).ge
  -- 🎉 no goals
#align measure_theory.le_lintegral_add MeasureTheory.le_lintegral_add

-- Use stronger lemmas `lintegral_add_left`/`lintegral_add_right` instead
theorem lintegral_add_aux {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ :=
  calc
    ∫⁻ a, f a + g a ∂μ =
        ∫⁻ a, (⨆ n, (eapprox f n : α → ℝ≥0∞) a) + ⨆ n, (eapprox g n : α → ℝ≥0∞) a ∂μ :=
      by simp only [iSup_eapprox_apply, hf, hg]
         -- 🎉 no goals
    _ = ∫⁻ a, ⨆ n, (eapprox f n + eapprox g n : α → ℝ≥0∞) a ∂μ := by
      congr; funext a
      -- ⊢ (fun a => (⨆ (n : ℕ), ↑(eapprox f n) a) + ⨆ (n : ℕ), ↑(eapprox g n) a) = fun …
             -- ⊢ (⨆ (n : ℕ), ↑(eapprox f n) a) + ⨆ (n : ℕ), ↑(eapprox g n) a = ⨆ (n : ℕ), (↑( …
      rw [ENNReal.iSup_add_iSup_of_monotone]; · rfl
                                                -- 🎉 no goals
      · intro i j h
        -- ⊢ (fun n => ↑(eapprox f n) a) i ≤ (fun n => ↑(eapprox f n) a) j
        exact monotone_eapprox _ h a
        -- 🎉 no goals
      · intro i j h
        -- ⊢ (fun n => ↑(eapprox g n) a) i ≤ (fun n => ↑(eapprox g n) a) j
        exact monotone_eapprox _ h a
        -- 🎉 no goals
    _ = ⨆ n, (eapprox f n).lintegral μ + (eapprox g n).lintegral μ := by
      rw [lintegral_iSup]
      · congr
        -- ⊢ (fun n => ∫⁻ (a : α), (↑(eapprox f n) + ↑(eapprox g n)) a ∂μ) = fun n => Sim …
        funext n
        -- ⊢ ∫⁻ (a : α), (↑(eapprox f n) + ↑(eapprox g n)) a ∂μ = SimpleFunc.lintegral (e …
        rw [← SimpleFunc.add_lintegral, ← SimpleFunc.lintegral_eq_lintegral]
        -- ⊢ ∫⁻ (a : α), (↑(eapprox f n) + ↑(eapprox g n)) a ∂μ = ∫⁻ (a : α), ↑(eapprox f …
        rfl
        -- 🎉 no goals
      · measurability
        -- 🎉 no goals
      · intro i j h a
        -- ⊢ (fun n a => (↑(eapprox f n) + ↑(eapprox g n)) a) i a ≤ (fun n a => (↑(eappro …
        exact add_le_add (monotone_eapprox _ h _) (monotone_eapprox _ h _)
        -- 🎉 no goals
    _ = (⨆ n, (eapprox f n).lintegral μ) + ⨆ n, (eapprox g n).lintegral μ := by
      refine' (ENNReal.iSup_add_iSup_of_monotone _ _).symm <;>
      -- ⊢ Monotone fun n => SimpleFunc.lintegral (eapprox f n) μ
        · intro i j h
          -- ⊢ (fun n => SimpleFunc.lintegral (eapprox f n) μ) i ≤ (fun n => SimpleFunc.lin …
          -- ⊢ (fun n => SimpleFunc.lintegral (eapprox g n) μ) i ≤ (fun n => SimpleFunc.lin …
          -- 🎉 no goals
          exact SimpleFunc.lintegral_mono (monotone_eapprox _ h) (le_refl μ)
          -- 🎉 no goals
    _ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ := by
      rw [lintegral_eq_iSup_eapprox_lintegral hf, lintegral_eq_iSup_eapprox_lintegral hg]
      -- 🎉 no goals
#align measure_theory.lintegral_add_aux MeasureTheory.lintegral_add_aux

/-- If `f g : α → ℝ≥0∞` are two functions and one of them is (a.e.) measurable, then the Lebesgue
integral of `f + g` equals the sum of integrals. This lemma assumes that `f` is integrable, see also
`MeasureTheory.lintegral_add_right` and primed versions of these lemmas. -/
@[simp]
theorem lintegral_add_left {f : α → ℝ≥0∞} (hf : Measurable f) (g : α → ℝ≥0∞) :
    ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ := by
  refine' le_antisymm _ (le_lintegral_add _ _)
  -- ⊢ ∫⁻ (a : α), f a + g a ∂μ ≤ ∫⁻ (a : α), f a ∂μ + ∫⁻ (a : α), g a ∂μ
  rcases exists_measurable_le_lintegral_eq μ fun a => f a + g a with ⟨φ, hφm, hφ_le, hφ_eq⟩
  -- ⊢ ∫⁻ (a : α), f a + g a ∂μ ≤ ∫⁻ (a : α), f a ∂μ + ∫⁻ (a : α), g a ∂μ
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
  -- 🎉 no goals
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
     -- 🎉 no goals
#align measure_theory.lintegral_smul_measure MeasureTheory.lintegral_smul_measure

@[simp]
theorem lintegral_sum_measure {m : MeasurableSpace α} {ι} (f : α → ℝ≥0∞) (μ : ι → Measure α) :
    ∫⁻ a, f a ∂Measure.sum μ = ∑' i, ∫⁻ a, f a ∂μ i := by
  simp only [lintegral, iSup_subtype', SimpleFunc.lintegral_sum, ENNReal.tsum_eq_iSup_sum]
  -- ⊢ ⨆ (x : { i // ↑i ≤ fun a => f a }) (s : Finset ι), ∑ i in s, SimpleFunc.lint …
  rw [iSup_comm]
  -- ⊢ ⨆ (j : Finset ι) (i : { i // ↑i ≤ fun a => f a }), ∑ i_1 in j, SimpleFunc.li …
  congr; funext s
  -- ⊢ (fun j => ⨆ (i : { i // ↑i ≤ fun a => f a }), ∑ i_1 in j, SimpleFunc.lintegr …
         -- ⊢ ⨆ (i : { i // ↑i ≤ fun a => f a }), ∑ i_1 in s, SimpleFunc.lintegral (↑i) (μ …
  induction' s using Finset.induction_on with i s hi hs;
  -- ⊢ ⨆ (i : { i // ↑i ≤ fun a => f a }), ∑ i_1 in ∅, SimpleFunc.lintegral (↑i) (μ …
  · apply bot_unique
    -- ⊢ ⨆ (i : { i // ↑i ≤ fun a => f a }), ∑ i_1 in ∅, SimpleFunc.lintegral (↑i) (μ …
    simp
    -- 🎉 no goals
  simp only [Finset.sum_insert hi, ← hs]
  -- ⊢ ⨆ (i_1 : { i // ↑i ≤ fun a => f a }), SimpleFunc.lintegral (↑i_1) (μ i) + ∑  …
  refine' (ENNReal.iSup_add_iSup _).symm
  -- ⊢ ∀ (i_1 j : { i // ↑i ≤ fun a => f a }), ∃ k, SimpleFunc.lintegral (↑i_1) (μ  …
  intro φ ψ
  -- ⊢ ∃ k, SimpleFunc.lintegral (↑φ) (μ i) + ∑ i in s, SimpleFunc.lintegral (↑ψ) ( …
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
  -- 🎉 no goals
#align measure_theory.lintegral_add_measure MeasureTheory.lintegral_add_measure

@[simp]
theorem lintegral_finset_sum_measure {ι} {m : MeasurableSpace α} (s : Finset ι) (f : α → ℝ≥0∞)
    (μ : ι → Measure α) : ∫⁻ a, f a ∂(∑ i in s, μ i) = ∑ i in s, ∫⁻ a, f a ∂μ i := by
  rw [← Measure.sum_coe_finset, lintegral_sum_measure, ← Finset.tsum_subtype']
  -- ⊢ ∑' (i : { x // x ∈ s }), ∫⁻ (a : α), f a ∂μ ↑i = ∑' (x : ↑↑s), ∫⁻ (a : α), f …
  rfl
  -- 🎉 no goals
#align measure_theory.lintegral_finset_sum_measure MeasureTheory.lintegral_finset_sum_measure

@[simp]
theorem lintegral_zero_measure {m : MeasurableSpace α} (f : α → ℝ≥0∞) :
    (∫⁻ a, f a ∂(0 : Measure α)) = 0 :=
  bot_unique <| by simp [lintegral]
                   -- 🎉 no goals
#align measure_theory.lintegral_zero_measure MeasureTheory.lintegral_zero_measure

theorem set_lintegral_empty (f : α → ℝ≥0∞) : ∫⁻ x in ∅, f x ∂μ = 0 := by
  rw [Measure.restrict_empty, lintegral_zero_measure]
  -- 🎉 no goals
#align measure_theory.set_lintegral_empty MeasureTheory.set_lintegral_empty

theorem set_lintegral_univ (f : α → ℝ≥0∞) : ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ := by
  rw [Measure.restrict_univ]
  -- 🎉 no goals
#align measure_theory.set_lintegral_univ MeasureTheory.set_lintegral_univ

theorem set_lintegral_measure_zero (s : Set α) (f : α → ℝ≥0∞) (hs' : μ s = 0) :
    ∫⁻ x in s, f x ∂μ = 0 := by
  convert lintegral_zero_measure _
  -- ⊢ Measure.restrict μ s = 0
  exact Measure.restrict_eq_zero.2 hs'
  -- 🎉 no goals
#align measure_theory.set_lintegral_measure_zero MeasureTheory.set_lintegral_measure_zero

theorem lintegral_finset_sum' (s : Finset β) {f : β → α → ℝ≥0∞}
    (hf : ∀ b ∈ s, AEMeasurable (f b) μ) :
    ∫⁻ a, ∑ b in s, f b a ∂μ = ∑ b in s, ∫⁻ a, f b a ∂μ := by
  induction' s using Finset.induction_on with a s has ih
  -- ⊢ ∫⁻ (a : α), ∑ b in ∅, f b a ∂μ = ∑ b in ∅, ∫⁻ (a : α), f b a ∂μ
  · simp
    -- 🎉 no goals
  · simp only [Finset.sum_insert has]
    -- ⊢ ∫⁻ (a_1 : α), f a a_1 + ∑ b in s, f b a_1 ∂μ = ∫⁻ (a_1 : α), f a a_1 ∂μ + ∑  …
    rw [Finset.forall_mem_insert] at hf
    -- ⊢ ∫⁻ (a_1 : α), f a a_1 + ∑ b in s, f b a_1 ∂μ = ∫⁻ (a_1 : α), f a a_1 ∂μ + ∑  …
    rw [lintegral_add_left' hf.1, ih hf.2]
    -- 🎉 no goals
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
      -- ⊢ (fun a => r * f a) = fun a => ⨆ (n : ℕ), ↑(const α r * eapprox f n) a
      funext a
      -- ⊢ r * f a = ⨆ (n : ℕ), ↑(const α r * eapprox f n) a
      rw [← iSup_eapprox_apply f hf, ENNReal.mul_iSup]
      -- ⊢ ⨆ (i : ℕ), r * ↑(eapprox f i) a = ⨆ (n : ℕ), ↑(const α r * eapprox f n) a
      rfl
      -- 🎉 no goals
    _ = ⨆ n, r * (eapprox f n).lintegral μ := by
      rw [lintegral_iSup]
      · congr
        -- ⊢ (fun n => ∫⁻ (a : α), ↑(const α r * eapprox f n) a ∂μ) = fun n => r * Simple …
        funext n
        -- ⊢ ∫⁻ (a : α), ↑(const α r * eapprox f n) a ∂μ = r * SimpleFunc.lintegral (eapp …
        rw [← SimpleFunc.const_mul_lintegral, ← SimpleFunc.lintegral_eq_lintegral]
        -- 🎉 no goals
      · intro n
        -- ⊢ Measurable fun a => ↑(const α r * eapprox f n) a
        exact SimpleFunc.measurable _
        -- 🎉 no goals
      · intro i j h a
        -- ⊢ (fun n a => ↑(const α r * eapprox f n) a) i a ≤ (fun n a => ↑(const α r * ea …
        exact mul_le_mul_left' (monotone_eapprox _ h _) _
        -- 🎉 no goals
    _ = r * ∫⁻ a, f a ∂μ := by rw [← ENNReal.mul_iSup, lintegral_eq_iSup_eapprox_lintegral hf]
                               -- 🎉 no goals
#align measure_theory.lintegral_const_mul MeasureTheory.lintegral_const_mul

theorem lintegral_const_mul'' (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ := by
  have A : ∫⁻ a, f a ∂μ = ∫⁻ a, hf.mk f a ∂μ := lintegral_congr_ae hf.ae_eq_mk
  -- ⊢ ∫⁻ (a : α), r * f a ∂μ = r * ∫⁻ (a : α), f a ∂μ
  have B : ∫⁻ a, r * f a ∂μ = ∫⁻ a, r * hf.mk f a ∂μ :=
    lintegral_congr_ae (EventuallyEq.fun_comp hf.ae_eq_mk _)
  rw [A, B, lintegral_const_mul _ hf.measurable_mk]
  -- 🎉 no goals
#align measure_theory.lintegral_const_mul'' MeasureTheory.lintegral_const_mul''

theorem lintegral_const_mul_le (r : ℝ≥0∞) (f : α → ℝ≥0∞) :
    (r * ∫⁻ a, f a ∂μ) ≤ ∫⁻ a, r * f a ∂μ := by
  rw [lintegral, ENNReal.mul_iSup]
  -- ⊢ ⨆ (i : α →ₛ ℝ≥0∞), r * ⨆ (_ : ↑i ≤ fun a => f a), SimpleFunc.lintegral i μ ≤ …
  refine' iSup_le fun s => _
  -- ⊢ r * ⨆ (_ : ↑s ≤ fun a => f a), SimpleFunc.lintegral s μ ≤ ∫⁻ (a : α), r * f  …
  rw [ENNReal.mul_iSup]
  -- ⊢ ⨆ (_ : ↑s ≤ fun a => f a), r * SimpleFunc.lintegral s μ ≤ ∫⁻ (a : α), r * f  …
  simp only [iSup_le_iff]
  -- ⊢ (↑s ≤ fun a => f a) → r * SimpleFunc.lintegral s μ ≤ ∫⁻ (a : α), r * f a ∂μ
  intro hs
  -- ⊢ r * SimpleFunc.lintegral s μ ≤ ∫⁻ (a : α), r * f a ∂μ
  rw [← SimpleFunc.const_mul_lintegral, lintegral]
  -- ⊢ SimpleFunc.lintegral (const α r * s) μ ≤ ⨆ (g : α →ₛ ℝ≥0∞) (_ : ↑g ≤ fun a = …
  refine' le_iSup_of_le (const α r * s) (le_iSup_of_le (fun x => _) le_rfl)
  -- ⊢ ↑(const α r * s) x ≤ (fun a => r * f a) x
  exact mul_le_mul_left' (hs x) _
  -- 🎉 no goals
#align measure_theory.lintegral_const_mul_le MeasureTheory.lintegral_const_mul_le

theorem lintegral_const_mul' (r : ℝ≥0∞) (f : α → ℝ≥0∞) (hr : r ≠ ∞) :
    ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ := by
  by_cases h : r = 0
  -- ⊢ ∫⁻ (a : α), r * f a ∂μ = r * ∫⁻ (a : α), f a ∂μ
  · simp [h]
    -- 🎉 no goals
  apply le_antisymm _ (lintegral_const_mul_le r f)
  -- ⊢ ∫⁻ (a : α), r * f a ∂μ ≤ r * ∫⁻ (a : α), f a ∂μ
  have rinv : r * r⁻¹ = 1 := ENNReal.mul_inv_cancel h hr
  -- ⊢ ∫⁻ (a : α), r * f a ∂μ ≤ r * ∫⁻ (a : α), f a ∂μ
  have rinv' : r⁻¹ * r = 1 := by
    rw [mul_comm]
    exact rinv
  have := lintegral_const_mul_le (μ := μ) r⁻¹ fun x => r * f x
  -- ⊢ ∫⁻ (a : α), r * f a ∂μ ≤ r * ∫⁻ (a : α), f a ∂μ
  simp [(mul_assoc _ _ _).symm, rinv'] at this
  -- ⊢ ∫⁻ (a : α), r * f a ∂μ ≤ r * ∫⁻ (a : α), f a ∂μ
  simpa [(mul_assoc _ _ _).symm, rinv] using mul_le_mul_left' this r
  -- 🎉 no goals
#align measure_theory.lintegral_const_mul' MeasureTheory.lintegral_const_mul'

theorem lintegral_mul_const (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a, f a * r ∂μ = (∫⁻ a, f a ∂μ) * r := by simp_rw [mul_comm, lintegral_const_mul r hf]
                                                -- 🎉 no goals
#align measure_theory.lintegral_mul_const MeasureTheory.lintegral_mul_const

theorem lintegral_mul_const'' (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∫⁻ a, f a * r ∂μ = (∫⁻ a, f a ∂μ) * r := by simp_rw [mul_comm, lintegral_const_mul'' r hf]
                                                -- 🎉 no goals
#align measure_theory.lintegral_mul_const'' MeasureTheory.lintegral_mul_const''

theorem lintegral_mul_const_le (r : ℝ≥0∞) (f : α → ℝ≥0∞) : (∫⁻ a, f a ∂μ) * r ≤ ∫⁻ a, f a * r ∂μ :=
  by simp_rw [mul_comm, lintegral_const_mul_le r f]
     -- 🎉 no goals
#align measure_theory.lintegral_mul_const_le MeasureTheory.lintegral_mul_const_le

theorem lintegral_mul_const' (r : ℝ≥0∞) (f : α → ℝ≥0∞) (hr : r ≠ ∞) :
    ∫⁻ a, f a * r ∂μ = (∫⁻ a, f a ∂μ) * r := by simp_rw [mul_comm, lintegral_const_mul' r f hr]
                                                -- 🎉 no goals
#align measure_theory.lintegral_mul_const' MeasureTheory.lintegral_mul_const'

/- A double integral of a product where each factor contains only one variable
  is a product of integrals -/
theorem lintegral_lintegral_mul {β} [MeasurableSpace β] {ν : Measure β} {f : α → ℝ≥0∞}
    {g : β → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g ν) :
    ∫⁻ x, ∫⁻ y, f x * g y ∂ν ∂μ = (∫⁻ x, f x ∂μ) * ∫⁻ y, g y ∂ν := by
  simp [lintegral_const_mul'' _ hg, lintegral_mul_const'' _ hf]
  -- 🎉 no goals
#align measure_theory.lintegral_lintegral_mul MeasureTheory.lintegral_lintegral_mul

-- TODO: Need a better way of rewriting inside of an integral
theorem lintegral_rw₁ {f f' : α → β} (h : f =ᵐ[μ] f') (g : β → ℝ≥0∞) :
    ∫⁻ a, g (f a) ∂μ = ∫⁻ a, g (f' a) ∂μ :=
  lintegral_congr_ae <| h.mono fun a h => by dsimp only; rw [h]
                                             -- ⊢ g (f a) = g (f' a)
                                                         -- 🎉 no goals
#align measure_theory.lintegral_rw₁ MeasureTheory.lintegral_rw₁

-- TODO: Need a better way of rewriting inside of an integral
theorem lintegral_rw₂ {f₁ f₁' : α → β} {f₂ f₂' : α → γ} (h₁ : f₁ =ᵐ[μ] f₁') (h₂ : f₂ =ᵐ[μ] f₂')
    (g : β → γ → ℝ≥0∞) : ∫⁻ a, g (f₁ a) (f₂ a) ∂μ = ∫⁻ a, g (f₁' a) (f₂' a) ∂μ :=
  lintegral_congr_ae <| h₁.mp <| h₂.mono fun _ h₂ h₁ => by dsimp only; rw [h₁, h₂]
                                                           -- ⊢ g (f₁ x✝) (f₂ x✝) = g (f₁' x✝) (f₂' x✝)
                                                                       -- 🎉 no goals
#align measure_theory.lintegral_rw₂ MeasureTheory.lintegral_rw₂

@[simp]
theorem lintegral_indicator (f : α → ℝ≥0∞) {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f a ∂μ := by
  simp only [lintegral, ← restrict_lintegral_eq_lintegral_restrict _ hs, iSup_subtype']
  -- ⊢ ⨆ (x : { i // ↑i ≤ fun a => indicator s f a }), SimpleFunc.lintegral (↑x) μ  …
  apply le_antisymm <;> refine' iSup_mono' (Subtype.forall.2 fun φ hφ => _)
  -- ⊢ ⨆ (x : { i // ↑i ≤ fun a => indicator s f a }), SimpleFunc.lintegral (↑x) μ  …
                        -- ⊢ ∃ i', SimpleFunc.lintegral (↑{ val := φ, property := hφ }) μ ≤ SimpleFunc.li …
                        -- ⊢ ∃ i', SimpleFunc.lintegral (restrict (↑{ val := φ, property := hφ }) s) μ ≤  …
  · refine' ⟨⟨φ, le_trans hφ (indicator_le_self _ _)⟩, _⟩
    -- ⊢ SimpleFunc.lintegral (↑{ val := φ, property := hφ }) μ ≤ SimpleFunc.lintegra …
    refine' SimpleFunc.lintegral_mono (fun x => _) le_rfl
    -- ⊢ ↑↑{ val := φ, property := hφ } x ≤ ↑(restrict (↑{ val := φ, property := (_ : …
    by_cases hx : x ∈ s
    -- ⊢ ↑↑{ val := φ, property := hφ } x ≤ ↑(restrict (↑{ val := φ, property := (_ : …
    · simp [hx, hs, le_refl]
      -- 🎉 no goals
    · apply le_trans (hφ x)
      -- ⊢ (fun a => indicator s f a) x ≤ ↑(restrict (↑{ val := φ, property := (_ : ↑φ  …
      simp [hx, hs, le_refl]
      -- 🎉 no goals
  · refine' ⟨⟨φ.restrict s, fun x => _⟩, le_rfl⟩
    -- ⊢ ↑(restrict φ s) x ≤ (fun a => indicator s f a) x
    simp [hφ x, hs, indicator_le_indicator]
    -- 🎉 no goals
#align measure_theory.lintegral_indicator MeasureTheory.lintegral_indicator

theorem lintegral_indicator₀ (f : α → ℝ≥0∞) {s : Set α} (hs : NullMeasurableSet s μ) :
    ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f a ∂μ := by
  rw [← lintegral_congr_ae (indicator_ae_eq_of_ae_eq_set hs.toMeasurable_ae_eq),
    lintegral_indicator _ (measurableSet_toMeasurable _ _),
    Measure.restrict_congr_set hs.toMeasurable_ae_eq]
#align measure_theory.lintegral_indicator₀ MeasureTheory.lintegral_indicator₀

theorem lintegral_indicator_const₀ {s : Set α} (hs : NullMeasurableSet s μ) (c : ℝ≥0∞) :
    ∫⁻ a, s.indicator (fun _ => c) a ∂μ = c * μ s := by
  rw [lintegral_indicator₀ _ hs, set_lintegral_const]
  -- 🎉 no goals

theorem lintegral_indicator_const {s : Set α} (hs : MeasurableSet s) (c : ℝ≥0∞) :
    ∫⁻ a, s.indicator (fun _ => c) a ∂μ = c * μ s :=
  lintegral_indicator_const₀ hs.nullMeasurableSet c
#align measure_theory.lintegral_indicator_const MeasureTheory.lintegral_indicator_const

theorem set_lintegral_eq_const {f : α → ℝ≥0∞} (hf : Measurable f) (r : ℝ≥0∞) :
    ∫⁻ x in { x | f x = r }, f x ∂μ = r * μ { x | f x = r } := by
  have : ∀ᵐ x ∂μ, x ∈ { x | f x = r } → f x = r := ae_of_all μ fun _ hx => hx
  -- ⊢ ∫⁻ (x : α) in {x | f x = r}, f x ∂μ = r * ↑↑μ {x | f x = r}
  rw [set_lintegral_congr_fun _ this]
  -- ⊢ ∫⁻ (x : α) in {x | f x = r}, r ∂μ = r * ↑↑μ {x | f x = r}
  rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  -- ⊢ MeasurableSet {x | f x = r}
  exact hf (measurableSet_singleton r)
  -- 🎉 no goals
#align measure_theory.set_lintegral_eq_const MeasureTheory.set_lintegral_eq_const

@[simp]
theorem lintegral_indicator_one (hs : MeasurableSet s) : ∫⁻ a, s.indicator 1 a ∂μ = μ s :=
  (lintegral_indicator_const hs _).trans $ one_mul _
#align measure_theory.lintegral_indicator_one MeasureTheory.lintegral_indicator_one

/-- A version of **Markov's inequality** for two functions. It doesn't follow from the standard
Markov's inequality because we only assume measurability of `g`, not `f`. -/
theorem lintegral_add_mul_meas_add_le_le_lintegral {f g : α → ℝ≥0∞} (hle : f ≤ᵐ[μ] g)
    (hg : AEMeasurable g μ) (ε : ℝ≥0∞) :
    ∫⁻ a, f a ∂μ + ε * μ { x | f x + ε ≤ g x } ≤ ∫⁻ a, g a ∂μ := by
  rcases exists_measurable_le_lintegral_eq μ f with ⟨φ, hφm, hφ_le, hφ_eq⟩
  -- ⊢ ∫⁻ (a : α), f a ∂μ + ε * ↑↑μ {x | f x + ε ≤ g x} ≤ ∫⁻ (a : α), g a ∂μ
  calc
    ∫⁻ x, f x ∂μ + ε * μ { x | f x + ε ≤ g x } = ∫⁻ x, φ x ∂μ + ε * μ { x | f x + ε ≤ g x } :=
      by rw [hφ_eq]
    _ ≤ ∫⁻ x, φ x ∂μ + ε * μ { x | φ x + ε ≤ g x } := by
      gcongr
      exact measure_mono fun x => (add_le_add_right (hφ_le _) _).trans
    _ = ∫⁻ x, φ x + indicator { x | φ x + ε ≤ g x } (fun _ => ε) x ∂μ := by
      rw [lintegral_add_left hφm, lintegral_indicator₀, set_lintegral_const]
      exact measurableSet_le (hφm.nullMeasurable.measurable'.add_const _) hg.nullMeasurable
    _ ≤ ∫⁻ x, g x ∂μ := lintegral_mono_ae (hle.mono fun x hx₁ => ?_)
  simp only [indicator_apply]; split_ifs with hx₂
  -- ⊢ (φ x + if x ∈ {x | φ x + ε ≤ g x} then ε else 0) ≤ g x
                               -- ⊢ φ x + ε ≤ g x
  exacts [hx₂, (add_zero _).trans_le <| (hφ_le x).trans hx₁]
  -- 🎉 no goals
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

theorem lintegral_eq_top_of_measure_eq_top_ne_zero {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hμf : μ {x | f x = ∞} ≠ 0) : ∫⁻ x, f x ∂μ = ∞ :=
  eq_top_iff.mpr <|
    calc
      ∞ = ∞ * μ { x | ∞ ≤ f x } := by simp [mul_eq_top, hμf]
                                      -- 🎉 no goals
      _ ≤ ∫⁻ x, f x ∂μ := mul_meas_ge_le_lintegral₀ hf ∞
#align measure_theory.lintegral_eq_top_of_measure_eq_top_ne_zero MeasureTheory.lintegral_eq_top_of_measure_eq_top_ne_zero

theorem setLintegral_eq_top_of_measure_eq_top_ne_zero (hf : AEMeasurable f (μ.restrict s))
    (hμf : μ ({x ∈ s | f x = ∞}) ≠ 0) : ∫⁻ x in s, f x ∂μ = ∞ :=
  lintegral_eq_top_of_measure_eq_top_ne_zero hf $
    mt (eq_bot_mono $ by rw [←setOf_inter_eq_sep]; exact Measure.le_restrict_apply _ _) hμf
                         -- ⊢ ↑↑μ ({a | f a = ⊤} ∩ s) ≤ ↑↑(Measure.restrict μ s) {x | f x = ⊤}
                                                   -- 🎉 no goals
#align measure_theory.set_lintegral_eq_top_of_measure_eq_top_ne_zero MeasureTheory.setLintegral_eq_top_of_measure_eq_top_ne_zero

theorem measure_eq_top_of_lintegral_ne_top (hf : AEMeasurable f μ) (hμf : ∫⁻ x, f x ∂μ ≠ ∞) :
    μ {x | f x = ∞} = 0 :=
  of_not_not fun h => hμf <| lintegral_eq_top_of_measure_eq_top_ne_zero hf h
#align measure_theory.measure_eq_top_of_lintegral_ne_top MeasureTheory.measure_eq_top_of_lintegral_ne_top

theorem measure_eq_top_of_setLintegral_ne_top (hf : AEMeasurable f (μ.restrict s))
    (hμf : ∫⁻ x in s, f x ∂μ ≠ ∞) : μ ({x ∈ s | f x = ∞}) = 0 :=
  of_not_not fun h => hμf $ setLintegral_eq_top_of_measure_eq_top_ne_zero hf h
#align measure_theory.measure_eq_top_of_set_lintegral_ne_top MeasureTheory.measure_eq_top_of_setLintegral_ne_top

/-- **Markov's inequality** also known as **Chebyshev's first inequality**. -/
theorem meas_ge_le_lintegral_div {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) {ε : ℝ≥0∞} (hε : ε ≠ 0)
    (hε' : ε ≠ ∞) : μ { x | ε ≤ f x } ≤ (∫⁻ a, f a ∂μ) / ε :=
  (ENNReal.le_div_iff_mul_le (Or.inl hε) (Or.inl hε')).2 <| by
    rw [mul_comm]
    -- ⊢ ε * ↑↑μ {x | ε ≤ f x} ≤ ∫⁻ (a : α), f a ∂μ
    exact mul_meas_ge_le_lintegral₀ hf ε
    -- 🎉 no goals
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
  -- ⊢ g x ≤ f x
  suffices : Tendsto (fun n : ℕ => f x + (n : ℝ≥0∞)⁻¹) atTop (𝓝 (f x))
  -- ⊢ g x ≤ f x
  exact ge_of_tendsto' this fun i => (hlt i).le
  -- ⊢ Tendsto (fun n => f x + (↑n)⁻¹) atTop (𝓝 (f x))
  simpa only [inv_top, add_zero] using
    tendsto_const_nhds.add (ENNReal.tendsto_inv_iff.2 ENNReal.tendsto_nat_nhds_top)
#align measure_theory.ae_eq_of_ae_le_of_lintegral_le MeasureTheory.ae_eq_of_ae_le_of_lintegral_le

@[simp]
theorem lintegral_eq_zero_iff' {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0 :=
  have : ∫⁻ _ : α, 0 ∂μ ≠ ∞ := by simp [lintegral_zero, zero_ne_top]
                                  -- 🎉 no goals
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
  -- 🎉 no goals
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
                                                       -- 🎉 no goals
    _ = ⨆ n, ∫⁻ a, g n a ∂μ :=
      (lintegral_iSup (fun n => measurable_const.piecewise hs.2.1 (hf n))
        (monotone_nat_of_le_succ fun n a =>
          _root_.by_cases (fun h : a ∈ s => by simp [if_pos h]) fun h : a ∉ s => by
                                               -- 🎉 no goals
            simp only [if_neg h]; have := hs.1; rw [subset_def] at this; have := mt (this a) h
            -- ⊢ f n a ≤ f (n + 1) a
                                  -- ⊢ f n a ≤ f (n + 1) a
                                                -- ⊢ f n a ≤ f (n + 1) a
                                                                         -- ⊢ f n a ≤ f (n + 1) a
            simp only [Classical.not_not, mem_setOf_eq] at this; exact this n))
            -- ⊢ f n a ≤ f (n + 1) a
                                                                 -- 🎉 no goals
    _ = ⨆ n, ∫⁻ a, f n a ∂μ := by simp only [lintegral_congr_ae (g_eq_f.mono fun _a ha => ha _)]
                                  -- 🎉 no goals
#align measure_theory.lintegral_supr_ae MeasureTheory.lintegral_iSup_ae

theorem lintegral_sub' {f g : α → ℝ≥0∞} (hg : AEMeasurable g μ) (hg_fin : ∫⁻ a, g a ∂μ ≠ ∞)
    (h_le : g ≤ᵐ[μ] f) : ∫⁻ a, f a - g a ∂μ = ∫⁻ a, f a ∂μ - ∫⁻ a, g a ∂μ := by
  refine' ENNReal.eq_sub_of_add_eq hg_fin _
  -- ⊢ ∫⁻ (a : α), f a - g a ∂μ + ∫⁻ (a : α), g a ∂μ = ∫⁻ (a : α), f a ∂μ
  rw [← lintegral_add_right' _ hg]
  -- ⊢ ∫⁻ (a : α), f a - g a + g a ∂μ = ∫⁻ (a : α), f a ∂μ
  exact lintegral_congr_ae (h_le.mono fun x hx => tsub_add_cancel_of_le hx)
  -- 🎉 no goals
#align measure_theory.lintegral_sub' MeasureTheory.lintegral_sub'

theorem lintegral_sub {f g : α → ℝ≥0∞} (hg : Measurable g) (hg_fin : ∫⁻ a, g a ∂μ ≠ ∞)
    (h_le : g ≤ᵐ[μ] f) : ∫⁻ a, f a - g a ∂μ = ∫⁻ a, f a ∂μ - ∫⁻ a, g a ∂μ :=
  lintegral_sub' hg.aemeasurable hg_fin h_le
#align measure_theory.lintegral_sub MeasureTheory.lintegral_sub

theorem lintegral_sub_le' (f g : α → ℝ≥0∞) (hf : AEMeasurable f μ) :
    (∫⁻ x, g x ∂μ - ∫⁻ x, f x ∂μ) ≤ ∫⁻ x, g x - f x ∂μ := by
  rw [tsub_le_iff_right]
  -- ⊢ ∫⁻ (x : α), g x ∂μ ≤ ∫⁻ (x : α), g x - f x ∂μ + ∫⁻ (x : α), f x ∂μ
  by_cases hfi : ∫⁻ x, f x ∂μ = ∞
  -- ⊢ ∫⁻ (x : α), g x ∂μ ≤ ∫⁻ (x : α), g x - f x ∂μ + ∫⁻ (x : α), f x ∂μ
  · rw [hfi, add_top]
    -- ⊢ ∫⁻ (x : α), g x ∂μ ≤ ⊤
    exact le_top
    -- 🎉 no goals
  · rw [← lintegral_add_right' _ hf]
    -- ⊢ ∫⁻ (x : α), g x ∂μ ≤ ∫⁻ (a : α), g a - f a + f a ∂μ
    exact lintegral_mono fun x => le_tsub_add
    -- 🎉 no goals
#align measure_theory.lintegral_sub_le' MeasureTheory.lintegral_sub_le'

theorem lintegral_sub_le (f g : α → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, g x ∂μ - ∫⁻ x, f x ∂μ) ≤ ∫⁻ x, g x - f x ∂μ :=
  lintegral_sub_le' f g hf.aemeasurable
#align measure_theory.lintegral_sub_le MeasureTheory.lintegral_sub_le

theorem lintegral_strict_mono_of_ae_le_of_frequently_ae_lt {f g : α → ℝ≥0∞} (hg : AEMeasurable g μ)
    (hfi : ∫⁻ x, f x ∂μ ≠ ∞) (h_le : f ≤ᵐ[μ] g) (h : ∃ᵐ x ∂μ, f x ≠ g x) :
    ∫⁻ x, f x ∂μ < ∫⁻ x, g x ∂μ := by
  contrapose! h
  -- ⊢ ¬∃ᵐ (x : α) ∂μ, f x ≠ g x
  simp only [not_frequently, Ne.def, Classical.not_not]
  -- ⊢ ∀ᵐ (x : α) ∂μ, f x = g x
  exact ae_eq_of_ae_le_of_lintegral_le h_le hfi hg h
  -- 🎉 no goals
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
  -- ⊢ ∫⁻ (x : α), f x ∂μ < ∫⁻ (x : α), g x ∂μ
  refine' lintegral_strict_mono_of_ae_le_of_ae_lt_on hg hfi (ae_le_of_ae_lt h) hμ _
  -- ⊢ ∀ᵐ (x : α) ∂μ, x ∈ univ → f x < g x
  simpa using h
  -- 🎉 no goals
#align measure_theory.lintegral_strict_mono MeasureTheory.lintegral_strict_mono

theorem set_lintegral_strict_mono {f g : α → ℝ≥0∞} {s : Set α} (hsm : MeasurableSet s)
    (hs : μ s ≠ 0) (hg : Measurable g) (hfi : ∫⁻ x in s, f x ∂μ ≠ ∞)
    (h : ∀ᵐ x ∂μ, x ∈ s → f x < g x) : ∫⁻ x in s, f x ∂μ < ∫⁻ x in s, g x ∂μ :=
  lintegral_strict_mono (by simp [hs]) hg.aemeasurable hfi ((ae_restrict_iff' hsm).mpr h)
                            -- 🎉 no goals
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
              -- ⊢ f Nat.zero a ≤ f 0 a
              · { exact le_rfl }; · { exact le_trans (h n) ih }
                -- 🎉 no goals
                                    -- 🎉 no goals
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

/-- Known as Fatou's lemma, version with `AEMeasurable` functions -/
theorem lintegral_liminf_le' {f : ℕ → α → ℝ≥0∞} (h_meas : ∀ n, AEMeasurable (f n) μ) :
    ∫⁻ a, liminf (fun n => f n a) atTop ∂μ ≤ liminf (fun n => ∫⁻ a, f n a ∂μ) atTop :=
  calc
    ∫⁻ a, liminf (fun n => f n a) atTop ∂μ = ∫⁻ a, ⨆ n : ℕ, ⨅ i ≥ n, f i a ∂μ := by
      simp only [liminf_eq_iSup_iInf_of_nat]
      -- 🎉 no goals
    _ = ⨆ n : ℕ, ∫⁻ a, ⨅ i ≥ n, f i a ∂μ :=
      (lintegral_iSup' (fun n => aemeasurable_biInf _ (to_countable _) h_meas)
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
        -- ⊢ Measurable fun a => ⨆ (i : ℕ) (_ : i ≥ n), f i a
        exact measurable_biSup _ (to_countable _) hf_meas
        -- 🎉 no goals
      · intro n m hnm a
        -- ⊢ (fun n a => ⨆ (i : ℕ) (_ : i ≥ n), f i a) m a ≤ (fun n a => ⨆ (i : ℕ) (_ : i …
        exact iSup_le_iSup_of_subset fun i hi => le_trans hnm hi
        -- 🎉 no goals
      · refine' ne_top_of_le_ne_top h_fin (lintegral_mono_ae _)
        -- ⊢ ∀ᵐ (a : α) ∂μ, ⨆ (i : ℕ) (_ : i ≥ 0), f i a ≤ g a
        refine' (ae_all_iff.2 h_bound).mono fun n hn => _
        -- ⊢ ⨆ (i : ℕ) (_ : i ≥ 0), f i n ≤ g n
        exact iSup_le fun i => iSup_le fun _ => hn i
        -- 🎉 no goals
    _ = ∫⁻ a, limsup (fun n => f n a) atTop ∂μ := by simp only [limsup_eq_iInf_iSup_of_nat]
                                                     -- 🎉 no goals
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
  -- ⊢ Tendsto (fun n => ∫⁻ (a : α), AEMeasurable.mk (F n) (_ : AEMeasurable (F n)) …
  apply
    tendsto_lintegral_of_dominated_convergence bound (fun n => (hF_meas n).measurable_mk) _ h_fin
  · have : ∀ n, ∀ᵐ a ∂μ, (hF_meas n).mk (F n) a = F n a := fun n => (hF_meas n).ae_eq_mk.symm
    -- ⊢ ∀ᵐ (a : α) ∂μ, Tendsto (fun n => AEMeasurable.mk (F n) (_ : AEMeasurable (F  …
    have : ∀ᵐ a ∂μ, ∀ n, (hF_meas n).mk (F n) a = F n a := ae_all_iff.mpr this
    -- ⊢ ∀ᵐ (a : α) ∂μ, Tendsto (fun n => AEMeasurable.mk (F n) (_ : AEMeasurable (F  …
    filter_upwards [this, h_lim] with a H H'
    -- ⊢ Tendsto (fun n => AEMeasurable.mk (F n) (_ : AEMeasurable (F n)) a) atTop (𝓝 …
    simp_rw [H]
    -- ⊢ Tendsto (fun n => F n a) atTop (𝓝 (f a))
    exact H'
    -- 🎉 no goals
  · intro n
    -- ⊢ AEMeasurable.mk (F n) (_ : AEMeasurable (F n)) ≤ᵐ[μ] bound
    filter_upwards [h_bound n, (hF_meas n).ae_eq_mk] with a H H'
    -- ⊢ AEMeasurable.mk (F n) (_ : AEMeasurable (F n)) a ≤ bound a
    rwa [H'] at H
    -- 🎉 no goals
#align measure_theory.tendsto_lintegral_of_dominated_convergence' MeasureTheory.tendsto_lintegral_of_dominated_convergence'

/-- Dominated convergence theorem for filters with a countable basis -/
theorem tendsto_lintegral_filter_of_dominated_convergence {ι} {l : Filter ι}
    [l.IsCountablyGenerated] {F : ι → α → ℝ≥0∞} {f : α → ℝ≥0∞} (bound : α → ℝ≥0∞)
    (hF_meas : ∀ᶠ n in l, Measurable (F n)) (h_bound : ∀ᶠ n in l, ∀ᵐ a ∂μ, F n a ≤ bound a)
    (h_fin : ∫⁻ a, bound a ∂μ ≠ ∞) (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) l (𝓝 (f a))) :
    Tendsto (fun n => ∫⁻ a, F n a ∂μ) l (𝓝 <| ∫⁻ a, f a ∂μ) := by
  rw [tendsto_iff_seq_tendsto]
  -- ⊢ ∀ (x : ℕ → ι), Tendsto x atTop l → Tendsto ((fun n => ∫⁻ (a : α), F n a ∂μ)  …
  intro x xl
  -- ⊢ Tendsto ((fun n => ∫⁻ (a : α), F n a ∂μ) ∘ x) atTop (𝓝 (∫⁻ (a : α), f a ∂μ))
  have hxl := by
    rw [tendsto_atTop'] at xl
    exact xl
  have h := inter_mem hF_meas h_bound
  -- ⊢ Tendsto ((fun n => ∫⁻ (a : α), F n a ∂μ) ∘ x) atTop (𝓝 (∫⁻ (a : α), f a ∂μ))
  replace h := hxl _ h
  -- ⊢ Tendsto ((fun n => ∫⁻ (a : α), F n a ∂μ) ∘ x) atTop (𝓝 (∫⁻ (a : α), f a ∂μ))
  rcases h with ⟨k, h⟩
  -- ⊢ Tendsto ((fun n => ∫⁻ (a : α), F n a ∂μ) ∘ x) atTop (𝓝 (∫⁻ (a : α), f a ∂μ))
  rw [← tendsto_add_atTop_iff_nat k]
  -- ⊢ Tendsto (fun n => ((fun n => ∫⁻ (a : α), F n a ∂μ) ∘ x) (n + k)) atTop (𝓝 (∫ …
  refine' tendsto_lintegral_of_dominated_convergence _ _ _ _ _
  · exact bound
    -- 🎉 no goals
  · intro
    -- ⊢ Measurable fun a => F (x (n✝ + k)) a
    refine' (h _ _).1
    -- ⊢ n✝ + k ≥ k
    exact Nat.le_add_left _ _
    -- 🎉 no goals
  · intro
    -- ⊢ (fun a => F (x (n✝ + k)) a) ≤ᵐ[μ] bound
    refine' (h _ _).2
    -- ⊢ n✝ + k ≥ k
    exact Nat.le_add_left _ _
    -- 🎉 no goals
  · assumption
    -- 🎉 no goals
  · refine' h_lim.mono fun a h_lim => _
    -- ⊢ Tendsto (fun n => F (x (n + k)) a) atTop (𝓝 (f a))
    apply @Tendsto.comp _ _ _ (fun n => x (n + k)) fun n => F n a
    · assumption
      -- 🎉 no goals
    rw [tendsto_add_atTop_iff_nat]
    -- ⊢ Tendsto x atTop l
    assumption
    -- 🎉 no goals
#align measure_theory.tendsto_lintegral_filter_of_dominated_convergence MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence

section

open Encodable

/-- Monotone convergence for a supremum over a directed family and indexed by a countable type -/
theorem lintegral_iSup_directed_of_measurable [Countable β] {f : β → α → ℝ≥0∞}
    (hf : ∀ b, Measurable (f b)) (h_directed : Directed (· ≤ ·) f) :
    ∫⁻ a, ⨆ b, f b a ∂μ = ⨆ b, ∫⁻ a, f b a ∂μ := by
  cases nonempty_encodable β
  -- ⊢ ∫⁻ (a : α), ⨆ (b : β), f b a ∂μ = ⨆ (b : β), ∫⁻ (a : α), f b a ∂μ
  cases isEmpty_or_nonempty β
  -- ⊢ ∫⁻ (a : α), ⨆ (b : β), f b a ∂μ = ⨆ (b : β), ∫⁻ (a : α), f b a ∂μ
  · simp [iSup_of_empty]
    -- 🎉 no goals
  inhabit β
  -- ⊢ ∫⁻ (a : α), ⨆ (b : β), f b a ∂μ = ⨆ (b : β), ∫⁻ (a : α), f b a ∂μ
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
  -- ⊢ ∫⁻ (a : α), iSup (fun i => f i) a ∂μ = ⨆ (b : β), ∫⁻ (a : α), f b a ∂μ
  let p : α → (β → ENNReal) → Prop := fun x f' => Directed LE.le f'
  -- ⊢ ∫⁻ (a : α), iSup (fun i => f i) a ∂μ = ⨆ (b : β), ∫⁻ (a : α), f b a ∂μ
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
    -- ⊢ ∫⁻ (a : α), iSup (fun i => f i) a ∂μ = ∫⁻ (a : α), iSup (fun i => aeSeq hf ( …
    rw [lintegral_congr_ae (aeSeq.iSup hf hp).symm]
    -- 🎉 no goals
  · congr 1
    -- ⊢ (fun b => ∫⁻ (a : α), f b a ∂μ) = fun b => ∫⁻ (a : α), aeSeq hf p b a ∂μ
    ext1 b
    -- ⊢ ∫⁻ (a : α), f b a ∂μ = ∫⁻ (a : α), aeSeq hf p b a ∂μ
    rw [lintegral_congr_ae]
    -- ⊢ (fun a => f b a) =ᵐ[μ] fun a => aeSeq hf p b a
    apply EventuallyEq.symm
    -- ⊢ (fun a => aeSeq hf p b a) =ᵐ[μ] fun a => f b a
    refine' aeSeq.aeSeq_n_eq_fun_n_ae hf hp _
    -- 🎉 no goals
#align measure_theory.lintegral_supr_directed MeasureTheory.lintegral_iSup_directed

end

theorem lintegral_tsum [Countable β] {f : β → α → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) μ) :
    ∫⁻ a, ∑' i, f i a ∂μ = ∑' i, ∫⁻ a, f i a ∂μ := by
  simp only [ENNReal.tsum_eq_iSup_sum]
  -- ⊢ ∫⁻ (a : α), ⨆ (s : Finset β), ∑ i in s, f i a ∂μ = ⨆ (s : Finset β), ∑ i in  …
  rw [lintegral_iSup_directed]
  · simp [lintegral_finset_sum' _ fun i _ => hf i]
    -- 🎉 no goals
  · intro b
    -- ⊢ AEMeasurable fun a => ∑ i in b, f i a
    exact Finset.aemeasurable_sum _ fun i _ => hf i
    -- 🎉 no goals
  · intro s t
    -- ⊢ ∃ z, (fun x x_1 => x ≤ x_1) ((fun s a => ∑ i in s, f i a) s) ((fun s a => ∑  …
    use s ∪ t
    -- ⊢ (fun x x_1 => x ≤ x_1) ((fun s a => ∑ i in s, f i a) s) ((fun s a => ∑ i in  …
    constructor
    -- ⊢ (fun x x_1 => x ≤ x_1) ((fun s a => ∑ i in s, f i a) s) ((fun s a => ∑ i in  …
    · exact fun a => Finset.sum_le_sum_of_subset (Finset.subset_union_left _ _)
      -- 🎉 no goals
    · exact fun a => Finset.sum_le_sum_of_subset (Finset.subset_union_right _ _)
      -- 🎉 no goals
#align measure_theory.lintegral_tsum MeasureTheory.lintegral_tsum

open Measure

theorem lintegral_iUnion₀ [Countable β] {s : β → Set α} (hm : ∀ i, NullMeasurableSet (s i) μ)
    (hd : Pairwise (AEDisjoint μ on s)) (f : α → ℝ≥0∞) :
    ∫⁻ a in ⋃ i, s i, f a ∂μ = ∑' i, ∫⁻ a in s i, f a ∂μ := by
  simp only [Measure.restrict_iUnion_ae hd hm, lintegral_sum_measure]
  -- 🎉 no goals
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
  -- ⊢ ∫⁻ (a : α) in ⋃ (i : β) (_ : i ∈ t), s i, f a ∂μ = ∑' (i : ↑t), ∫⁻ (a : α) i …
  rw [biUnion_eq_iUnion, lintegral_iUnion₀ (SetCoe.forall'.1 hm) (hd.subtype _ _)]
  -- 🎉 no goals
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
  -- 🎉 no goals
#align measure_theory.lintegral_bUnion_finset₀ MeasureTheory.lintegral_biUnion_finset₀

theorem lintegral_biUnion_finset {s : Finset β} {t : β → Set α} (hd : Set.PairwiseDisjoint (↑s) t)
    (hm : ∀ b ∈ s, MeasurableSet (t b)) (f : α → ℝ≥0∞) :
    ∫⁻ a in ⋃ b ∈ s, t b, f a ∂μ = ∑ b in s, ∫⁻ a in t b, f a ∂μ :=
  lintegral_biUnion_finset₀ hd.aedisjoint (fun b hb => (hm b hb).nullMeasurableSet) f
#align measure_theory.lintegral_bUnion_finset MeasureTheory.lintegral_biUnion_finset

theorem lintegral_iUnion_le [Countable β] (s : β → Set α) (f : α → ℝ≥0∞) :
    ∫⁻ a in ⋃ i, s i, f a ∂μ ≤ ∑' i, ∫⁻ a in s i, f a ∂μ := by
  rw [← lintegral_sum_measure]
  -- ⊢ ∫⁻ (a : α) in ⋃ (i : β), s i, f a ∂μ ≤ ∫⁻ (a : α), f a ∂sum fun i => Measure …
  exact lintegral_mono' restrict_iUnion_le le_rfl
  -- 🎉 no goals
#align measure_theory.lintegral_Union_le MeasureTheory.lintegral_iUnion_le

theorem lintegral_union {f : α → ℝ≥0∞} {A B : Set α} (hB : MeasurableSet B) (hAB : Disjoint A B) :
    ∫⁻ a in A ∪ B, f a ∂μ = ∫⁻ a in A, f a ∂μ + ∫⁻ a in B, f a ∂μ := by
  rw [restrict_union hAB hB, lintegral_add_measure]
  -- 🎉 no goals
#align measure_theory.lintegral_union MeasureTheory.lintegral_union

theorem lintegral_union_le (f : α → ℝ≥0∞) (s t : Set α) :
    ∫⁻ a in s ∪ t, f a ∂μ ≤ ∫⁻ a in s, f a ∂μ + ∫⁻ a in t, f a ∂μ := by
  rw [← lintegral_add_measure]
  -- ⊢ ∫⁻ (a : α) in s ∪ t, f a ∂μ ≤ ∫⁻ (a : α), f a ∂(Measure.restrict μ s + Measu …
  exact lintegral_mono' (restrict_union_le _ _) le_rfl
  -- 🎉 no goals

theorem lintegral_inter_add_diff {B : Set α} (f : α → ℝ≥0∞) (A : Set α) (hB : MeasurableSet B) :
    ∫⁻ x in A ∩ B, f x ∂μ + ∫⁻ x in A \ B, f x ∂μ = ∫⁻ x in A, f x ∂μ := by
  rw [← lintegral_add_measure, restrict_inter_add_diff _ hB]
  -- 🎉 no goals
#align measure_theory.lintegral_inter_add_diff MeasureTheory.lintegral_inter_add_diff

theorem lintegral_add_compl (f : α → ℝ≥0∞) {A : Set α} (hA : MeasurableSet A) :
    ∫⁻ x in A, f x ∂μ + ∫⁻ x in Aᶜ, f x ∂μ = ∫⁻ x, f x ∂μ := by
  rw [← lintegral_add_measure, Measure.restrict_add_restrict_compl hA]
  -- 🎉 no goals
#align measure_theory.lintegral_add_compl MeasureTheory.lintegral_add_compl

theorem lintegral_max {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ x, max (f x) (g x) ∂μ =
      ∫⁻ x in { x | f x ≤ g x }, g x ∂μ + ∫⁻ x in { x | g x < f x }, f x ∂μ := by
  have hm : MeasurableSet { x | f x ≤ g x } := measurableSet_le hf hg
  -- ⊢ ∫⁻ (x : α), max (f x) (g x) ∂μ = ∫⁻ (x : α) in {x | f x ≤ g x}, g x ∂μ + ∫⁻  …
  rw [← lintegral_add_compl (fun x => max (f x) (g x)) hm]
  -- ⊢ ∫⁻ (x : α) in {x | f x ≤ g x}, max (f x) (g x) ∂μ + ∫⁻ (x : α) in {x | f x ≤ …
  simp only [← compl_setOf, ← not_le]
  -- ⊢ ∫⁻ (x : α) in {x | f x ≤ g x}, max (f x) (g x) ∂μ + ∫⁻ (x : α) in {x | f x ≤ …
  refine' congr_arg₂ (· + ·) (set_lintegral_congr_fun hm _) (set_lintegral_congr_fun hm.compl _)
  -- ⊢ ∀ᵐ (x : α) ∂μ, x ∈ {x | f x ≤ g x} → max (f x) (g x) = g x
  exacts [ae_of_all _ fun x => max_eq_right (a := f x) (b := g x),
    ae_of_all _ fun x (hx : ¬ f x ≤ g x) => max_eq_left (not_le.1 hx).le]
#align measure_theory.lintegral_max MeasureTheory.lintegral_max

theorem set_lintegral_max {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (s : Set α) :
    ∫⁻ x in s, max (f x) (g x) ∂μ =
      ∫⁻ x in s ∩ { x | f x ≤ g x }, g x ∂μ + ∫⁻ x in s ∩ { x | g x < f x }, f x ∂μ := by
  rw [lintegral_max hf hg, restrict_restrict, restrict_restrict, inter_comm s, inter_comm s]
  -- ⊢ MeasurableSet {x | g x < f x}
  exacts [measurableSet_lt hg hf, measurableSet_le hf hg]
  -- 🎉 no goals
#align measure_theory.set_lintegral_max MeasureTheory.set_lintegral_max

theorem lintegral_map {mβ : MeasurableSpace β} {f : β → ℝ≥0∞} {g : α → β} (hf : Measurable f)
    (hg : Measurable g) : ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a) ∂μ := by
  erw [lintegral_eq_iSup_eapprox_lintegral hf, lintegral_eq_iSup_eapprox_lintegral (hf.comp hg)]
  -- ⊢ ⨆ (n : ℕ), SimpleFunc.lintegral (eapprox f n) (Measure.map g μ) = ⨆ (n : ℕ), …
  congr with n : 1
  -- ⊢ SimpleFunc.lintegral (eapprox f n) (Measure.map g μ) = SimpleFunc.lintegral  …
  convert SimpleFunc.lintegral_map _ hg
  -- ⊢ eapprox (f ∘ g) n = comp (eapprox f n) g hg
  ext1 x; simp only [eapprox_comp hf hg, coe_comp]
  -- ⊢ ↑(eapprox (f ∘ g) n) x = ↑(comp (eapprox f n) g hg) x
          -- 🎉 no goals
#align measure_theory.lintegral_map MeasureTheory.lintegral_map

theorem lintegral_map' {mβ : MeasurableSpace β} {f : β → ℝ≥0∞} {g : α → β}
    (hf : AEMeasurable f (Measure.map g μ)) (hg : AEMeasurable g μ) :
    ∫⁻ a, f a ∂Measure.map g μ = ∫⁻ a, f (g a) ∂μ :=
  calc
    ∫⁻ a, f a ∂Measure.map g μ = ∫⁻ a, hf.mk f a ∂Measure.map g μ :=
      lintegral_congr_ae hf.ae_eq_mk
    _ = ∫⁻ a, hf.mk f a ∂Measure.map (hg.mk g) μ := by
      congr 1
      -- ⊢ Measure.map g μ = Measure.map (AEMeasurable.mk g hg) μ
      exact Measure.map_congr hg.ae_eq_mk
      -- 🎉 no goals
    _ = ∫⁻ a, hf.mk f (hg.mk g a) ∂μ := (lintegral_map hf.measurable_mk hg.measurable_mk)
    _ = ∫⁻ a, hf.mk f (g a) ∂μ := (lintegral_congr_ae <| hg.ae_eq_mk.symm.fun_comp _)
    _ = ∫⁻ a, f (g a) ∂μ := lintegral_congr_ae (ae_eq_comp hg hf.ae_eq_mk.symm)
#align measure_theory.lintegral_map' MeasureTheory.lintegral_map'

theorem lintegral_map_le {mβ : MeasurableSpace β} (f : β → ℝ≥0∞) {g : α → β} (hg : Measurable g) :
    (∫⁻ a, f a ∂Measure.map g μ) ≤ ∫⁻ a, f (g a) ∂μ := by
  rw [← iSup_lintegral_measurable_le_eq_lintegral, ← iSup_lintegral_measurable_le_eq_lintegral]
  -- ⊢ ⨆ (g_1 : β → ℝ≥0∞) (_ : Measurable g_1) (_ : g_1 ≤ fun a => f a), ∫⁻ (a : β) …
  refine' iSup₂_le fun i hi => iSup_le fun h'i => _
  -- ⊢ ∫⁻ (a : β), i a ∂Measure.map g μ ≤ ⨆ (g_1 : α → ℝ≥0∞) (_ : Measurable g_1) ( …
  refine' le_iSup₂_of_le (i ∘ g) (hi.comp hg) _
  -- ⊢ ∫⁻ (a : β), i a ∂Measure.map g μ ≤ ⨆ (_ : i ∘ g ≤ fun a => f (g a)), ∫⁻ (a : …
  exact le_iSup_of_le (fun x => h'i (g x)) (le_of_eq (lintegral_map hi hg))
  -- 🎉 no goals
#align measure_theory.lintegral_map_le MeasureTheory.lintegral_map_le

theorem lintegral_comp [MeasurableSpace β] {f : β → ℝ≥0∞} {g : α → β} (hf : Measurable f)
    (hg : Measurable g) : lintegral μ (f ∘ g) = ∫⁻ a, f a ∂map g μ :=
  (lintegral_map hf hg).symm
#align measure_theory.lintegral_comp MeasureTheory.lintegral_comp

theorem set_lintegral_map [MeasurableSpace β] {f : β → ℝ≥0∞} {g : α → β} {s : Set β}
    (hs : MeasurableSet s) (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ y in s, f y ∂map g μ = ∫⁻ x in g ⁻¹' s, f (g x) ∂μ := by
  rw [restrict_map hg hs, lintegral_map hf hg]
  -- 🎉 no goals
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
  -- ⊢ ⨆ (g_1 : β →ₛ ℝ≥0∞) (_ : ↑g_1 ≤ fun a => f a), SimpleFunc.lintegral g_1 (Mea …
  refine' le_antisymm (iSup₂_le fun f₀ hf₀ => _) (iSup₂_le fun f₀ hf₀ => _)
  -- ⊢ SimpleFunc.lintegral f₀ (Measure.map g μ) ≤ ⨆ (g_1 : α →ₛ ℝ≥0∞) (_ : ↑g_1 ≤  …
  · rw [SimpleFunc.lintegral_map _ hg.measurable]
    -- ⊢ SimpleFunc.lintegral (comp f₀ g (_ : Measurable g)) μ ≤ ⨆ (g_1 : α →ₛ ℝ≥0∞)  …
    have : (f₀.comp g hg.measurable : α → ℝ≥0∞) ≤ f ∘ g := fun x => hf₀ (g x)
    -- ⊢ SimpleFunc.lintegral (comp f₀ g (_ : Measurable g)) μ ≤ ⨆ (g_1 : α →ₛ ℝ≥0∞)  …
    exact le_iSup_of_le (comp f₀ g hg.measurable) (by exact le_iSup (α := ℝ≥0∞) _ this)
    -- 🎉 no goals
  · rw [← f₀.extend_comp_eq hg (const _ 0), ← SimpleFunc.lintegral_map, ←
      SimpleFunc.lintegral_eq_lintegral, ← lintegral]
    refine' lintegral_mono_ae (hg.ae_map_iff.2 <| eventually_of_forall fun x => _)
    -- ⊢ ↑(SimpleFunc.extend f₀ g hg (const β 0)) (g x) ≤ f (g x)
    exact (extend_apply _ _ _ _).trans_le (hf₀ _)
    -- 🎉 no goals
#align measurable_embedding.lintegral_map MeasurableEmbedding.lintegral_map

/-- The `lintegral` transforms appropriately under a measurable equivalence `g : α ≃ᵐ β`.
(Compare `lintegral_map`, which applies to a wider class of functions `g : α → β`, but requires
measurability of the function being integrated.) -/
theorem lintegral_map_equiv [MeasurableSpace β] (f : β → ℝ≥0∞) (g : α ≃ᵐ β) :
    ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a) ∂μ :=
  g.measurableEmbedding.lintegral_map f
#align measure_theory.lintegral_map_equiv MeasureTheory.lintegral_map_equiv

theorem MeasurePreserving.lintegral_comp {mb : MeasurableSpace β} {ν : Measure β} {g : α → β}
    (hg : MeasurePreserving g μ ν) {f : β → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a, f (g a) ∂μ = ∫⁻ b, f b ∂ν := by rw [← hg.map_eq, lintegral_map hf hg.measurable]
                                          -- 🎉 no goals
#align measure_theory.measure_preserving.lintegral_comp MeasureTheory.MeasurePreserving.lintegral_comp

theorem MeasurePreserving.lintegral_comp_emb {mb : MeasurableSpace β} {ν : Measure β} {g : α → β}
    (hg : MeasurePreserving g μ ν) (hge : MeasurableEmbedding g) (f : β → ℝ≥0∞) :
    ∫⁻ a, f (g a) ∂μ = ∫⁻ b, f b ∂ν := by rw [← hg.map_eq, hge.lintegral_map]
                                          -- 🎉 no goals
#align measure_theory.measure_preserving.lintegral_comp_emb MeasureTheory.MeasurePreserving.lintegral_comp_emb

theorem MeasurePreserving.set_lintegral_comp_preimage {mb : MeasurableSpace β} {ν : Measure β}
    {g : α → β} (hg : MeasurePreserving g μ ν) {s : Set β} (hs : MeasurableSet s) {f : β → ℝ≥0∞}
    (hf : Measurable f) : ∫⁻ a in g ⁻¹' s, f (g a) ∂μ = ∫⁻ b in s, f b ∂ν := by
  rw [← hg.map_eq, set_lintegral_map hs hf hg.measurable]
  -- 🎉 no goals
#align measure_theory.measure_preserving.set_lintegral_comp_preimage MeasureTheory.MeasurePreserving.set_lintegral_comp_preimage

theorem MeasurePreserving.set_lintegral_comp_preimage_emb {mb : MeasurableSpace β} {ν : Measure β}
    {g : α → β} (hg : MeasurePreserving g μ ν) (hge : MeasurableEmbedding g) (f : β → ℝ≥0∞)
    (s : Set β) : ∫⁻ a in g ⁻¹' s, f (g a) ∂μ = ∫⁻ b in s, f b ∂ν := by
  rw [← hg.map_eq, hge.restrict_map, hge.lintegral_map]
  -- 🎉 no goals
#align measure_theory.measure_preserving.set_lintegral_comp_preimage_emb MeasureTheory.MeasurePreserving.set_lintegral_comp_preimage_emb

theorem MeasurePreserving.set_lintegral_comp_emb {mb : MeasurableSpace β} {ν : Measure β}
    {g : α → β} (hg : MeasurePreserving g μ ν) (hge : MeasurableEmbedding g) (f : β → ℝ≥0∞)
    (s : Set α) : ∫⁻ a in s, f (g a) ∂μ = ∫⁻ b in g '' s, f b ∂ν := by
  rw [← hg.set_lintegral_comp_preimage_emb hge, preimage_image_eq _ hge.injective]
  -- 🎉 no goals
#align measure_theory.measure_preserving.set_lintegral_comp_emb MeasureTheory.MeasurePreserving.set_lintegral_comp_emb

section DiracAndCount

instance (priority := 10) _root_.MeasurableSpace.Top.measurableSingletonClass {α : Type*} :
    @MeasurableSingletonClass α (⊤ : MeasurableSpace α) :=
  @MeasurableSingletonClass.mk α (⊤ : MeasurableSpace α) <|
    fun _ => MeasurableSpace.measurableSet_top
#align measurable_space.top.measurable_singleton_class MeasurableSpace.Top.measurableSingletonClass

variable [MeasurableSpace α]

theorem lintegral_dirac' (a : α) {f : α → ℝ≥0∞} (hf : Measurable f) : ∫⁻ a, f a ∂dirac a = f a :=
  by simp [lintegral_congr_ae (ae_eq_dirac' hf)]
     -- 🎉 no goals
#align measure_theory.lintegral_dirac' MeasureTheory.lintegral_dirac'

theorem lintegral_dirac [MeasurableSingletonClass α] (a : α) (f : α → ℝ≥0∞) :
    ∫⁻ a, f a ∂dirac a = f a := by simp [lintegral_congr_ae (ae_eq_dirac f)]
                                   -- 🎉 no goals
#align measure_theory.lintegral_dirac MeasureTheory.lintegral_dirac

theorem set_lintegral_dirac' {a : α} {f : α → ℝ≥0∞} (hf : Measurable f) {s : Set α}
    (hs : MeasurableSet s) [Decidable (a ∈ s)] :
    ∫⁻ x in s, f x ∂Measure.dirac a = if a ∈ s then f a else 0 := by
  rw [restrict_dirac' hs]
  -- ⊢ (∫⁻ (x : α), f x ∂if a ∈ s then dirac a else 0) = if a ∈ s then f a else 0
  split_ifs
  -- ⊢ ∫⁻ (x : α), f x ∂dirac a = f a
  · exact lintegral_dirac' _ hf
    -- 🎉 no goals
  · exact lintegral_zero_measure _
    -- 🎉 no goals
#align measure_theory.set_lintegral_dirac' MeasureTheory.set_lintegral_dirac'

theorem set_lintegral_dirac {a : α} (f : α → ℝ≥0∞) (s : Set α) [MeasurableSingletonClass α]
    [Decidable (a ∈ s)] : ∫⁻ x in s, f x ∂Measure.dirac a = if a ∈ s then f a else 0 := by
  rw [restrict_dirac]
  -- ⊢ (∫⁻ (x : α), f x ∂if a ∈ s then dirac a else 0) = if a ∈ s then f a else 0
  split_ifs
  -- ⊢ ∫⁻ (x : α), f x ∂dirac a = f a
  · exact lintegral_dirac _ _
    -- 🎉 no goals
  · exact lintegral_zero_measure _
    -- 🎉 no goals
#align measure_theory.set_lintegral_dirac MeasureTheory.set_lintegral_dirac

theorem lintegral_count' {f : α → ℝ≥0∞} (hf : Measurable f) : ∫⁻ a, f a ∂count = ∑' a, f a := by
  rw [count, lintegral_sum_measure]
  -- ⊢ ∑' (i : α), ∫⁻ (a : α), f a ∂dirac i = ∑' (a : α), f a
  congr
  -- ⊢ (fun i => ∫⁻ (a : α), f a ∂dirac i) = fun a => f a
  exact funext fun a => lintegral_dirac' a hf
  -- 🎉 no goals
#align measure_theory.lintegral_count' MeasureTheory.lintegral_count'

theorem lintegral_count [MeasurableSingletonClass α] (f : α → ℝ≥0∞) :
    ∫⁻ a, f a ∂count = ∑' a, f a := by
  rw [count, lintegral_sum_measure]
  -- ⊢ ∑' (i : α), ∫⁻ (a : α), f a ∂dirac i = ∑' (a : α), f a
  congr
  -- ⊢ (fun i => ∫⁻ (a : α), f a ∂dirac i) = fun a => f a
  exact funext fun a => lintegral_dirac a f
  -- 🎉 no goals
#align measure_theory.lintegral_count MeasureTheory.lintegral_count

theorem _root_.ENNReal.tsum_const_eq [MeasurableSingletonClass α] (c : ℝ≥0∞) :
    ∑' _ : α, c = c * Measure.count (univ : Set α) := by rw [← lintegral_count, lintegral_const]
                                                         -- 🎉 no goals
#align ennreal.tsum_const_eq ENNReal.tsum_const_eq

/-- Markov's inequality for the counting measure with hypothesis using `tsum` in `ℝ≥0∞`. -/
theorem _root_.ENNReal.count_const_le_le_of_tsum_le [MeasurableSingletonClass α] {a : α → ℝ≥0∞}
    (a_mble : Measurable a) {c : ℝ≥0∞} (tsum_le_c : ∑' i, a i ≤ c) {ε : ℝ≥0∞} (ε_ne_zero : ε ≠ 0)
    (ε_ne_top : ε ≠ ∞) : Measure.count { i : α | ε ≤ a i } ≤ c / ε := by
  rw [← lintegral_count] at tsum_le_c
  -- ⊢ ↑↑count {i | ε ≤ a i} ≤ c / ε
  apply (MeasureTheory.meas_ge_le_lintegral_div a_mble.aemeasurable ε_ne_zero ε_ne_top).trans
  -- ⊢ (∫⁻ (a_1 : α), a a_1 ∂count) / ε ≤ c / ε
  exact ENNReal.div_le_div tsum_le_c rfl.le
  -- 🎉 no goals
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
      (by exact_mod_cast ε_ne_zero) (@ENNReal.coe_ne_top ε)
  convert ENNReal.coe_le_coe.mpr tsum_le_c
  -- ⊢ ∑' (i : α), (ENNReal.some ∘ a) i = ↑(∑' (i : α), a i)
  erw [ENNReal.tsum_coe_eq a_summable.hasSum]
  -- 🎉 no goals
#align nnreal.count_const_le_le_of_tsum_le NNReal.count_const_le_le_of_tsum_le

end DiracAndCount

section Countable

/-!
### Lebesgue integral over finite and countable types and sets
-/


theorem lintegral_countable' [Countable α] [MeasurableSingletonClass α] (f : α → ℝ≥0∞) :
    ∫⁻ a, f a ∂μ = ∑' a, f a * μ {a} := by
  conv_lhs => rw [← sum_smul_dirac μ, lintegral_sum_measure]
  -- ⊢ ∑' (i : α), ∫⁻ (a : α), f a ∂↑↑μ {i} • dirac i = ∑' (a : α), f a * ↑↑μ {a}
  congr 1 with a : 1
  -- ⊢ ∫⁻ (a : α), f a ∂↑↑μ {a} • dirac a = f a * ↑↑μ {a}
  rw [lintegral_smul_measure, lintegral_dirac, mul_comm]
  -- 🎉 no goals
#align measure_theory.lintegral_countable' MeasureTheory.lintegral_countable'

theorem lintegral_singleton' {f : α → ℝ≥0∞} (hf : Measurable f) (a : α) :
    ∫⁻ x in {a}, f x ∂μ = f a * μ {a} := by
  simp only [restrict_singleton, lintegral_smul_measure, lintegral_dirac' _ hf, mul_comm]
  -- 🎉 no goals
#align measure_theory.lintegral_singleton' MeasureTheory.lintegral_singleton'

theorem lintegral_singleton [MeasurableSingletonClass α] (f : α → ℝ≥0∞) (a : α) :
    ∫⁻ x in {a}, f x ∂μ = f a * μ {a} := by
  simp only [restrict_singleton, lintegral_smul_measure, lintegral_dirac, mul_comm]
  -- 🎉 no goals
#align measure_theory.lintegral_singleton MeasureTheory.lintegral_singleton

theorem lintegral_countable [MeasurableSingletonClass α] (f : α → ℝ≥0∞) {s : Set α}
    (hs : s.Countable) : ∫⁻ a in s, f a ∂μ = ∑' a : s, f a * μ {(a : α)} :=
  calc
    ∫⁻ a in s, f a ∂μ = ∫⁻ a in ⋃ x ∈ s, {x}, f a ∂μ := by rw [biUnion_of_singleton]
                                                           -- 🎉 no goals
    _ = ∑' a : s, ∫⁻ x in {(a : α)}, f x ∂μ :=
      (lintegral_biUnion hs (fun _ _ => measurableSet_singleton _) (pairwiseDisjoint_fiber id s) _)
    _ = ∑' a : s, f a * μ {(a : α)} := by simp only [lintegral_singleton]
                                          -- 🎉 no goals
#align measure_theory.lintegral_countable MeasureTheory.lintegral_countable

theorem lintegral_insert [MeasurableSingletonClass α] {a : α} {s : Set α} (h : a ∉ s)
    (f : α → ℝ≥0∞) : ∫⁻ x in insert a s, f x ∂μ = f a * μ {a} + ∫⁻ x in s, f x ∂μ := by
  rw [← union_singleton, lintegral_union (measurableSet_singleton a), lintegral_singleton,
    add_comm]
  rwa [disjoint_singleton_right]
  -- 🎉 no goals
#align measure_theory.lintegral_insert MeasureTheory.lintegral_insert

theorem lintegral_finset [MeasurableSingletonClass α] (s : Finset α) (f : α → ℝ≥0∞) :
    ∫⁻ x in s, f x ∂μ = ∑ x in s, f x * μ {x} := by
  simp only [lintegral_countable _ s.countable_toSet, ← Finset.tsum_subtype']
  -- 🎉 no goals
#align measure_theory.lintegral_finset MeasureTheory.lintegral_finset

theorem lintegral_fintype [MeasurableSingletonClass α] [Fintype α] (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = ∑ x, f x * μ {x} := by
  rw [← lintegral_finset, Finset.coe_univ, Measure.restrict_univ]
  -- 🎉 no goals
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
  -- ⊢ ↑↑μ {a | f a = ⊤} = 0
  by_contra h
  -- ⊢ False
  apply h2f.lt_top.not_le
  -- ⊢ ⊤ ≤ ∫⁻ (x : α), f x ∂μ
  have : (f ⁻¹' {∞}).indicator ⊤ ≤ f := by
    intro x
    by_cases hx : x ∈ f ⁻¹' {∞} <;> [simpa [indicator_of_mem hx]; simp [indicator_of_not_mem hx]]
  convert lintegral_mono this
  -- ⊢ ⊤ = ∫⁻ (a : α), indicator (f ⁻¹' {⊤}) ⊤ a ∂μ
  rw [lintegral_indicator _ (hf (measurableSet_singleton ∞))]
  -- ⊢ ⊤ = ∫⁻ (a : α) in f ⁻¹' {⊤}, ⊤ a ∂μ
  simp [ENNReal.top_mul', preimage, h]
  -- 🎉 no goals
#align measure_theory.ae_lt_top MeasureTheory.ae_lt_top

theorem ae_lt_top' {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (h2f : ∫⁻ x, f x ∂μ ≠ ∞) :
    ∀ᵐ x ∂μ, f x < ∞ :=
  haveI h2f_meas : ∫⁻ x, hf.mk f x ∂μ ≠ ∞ := by rwa [← lintegral_congr_ae hf.ae_eq_mk]
                                                -- 🎉 no goals
  (ae_lt_top hf.measurable_mk h2f_meas).mp (hf.ae_eq_mk.mono fun x hx h => by rwa [hx])
                                                                              -- 🎉 no goals
#align measure_theory.ae_lt_top' MeasureTheory.ae_lt_top'

theorem set_lintegral_lt_top_of_bddAbove {s : Set α} (hs : μ s ≠ ∞) {f : α → ℝ≥0}
    (hf : Measurable f) (hbdd : BddAbove (f '' s)) : ∫⁻ x in s, f x ∂μ < ∞ := by
  obtain ⟨M, hM⟩ := hbdd
  -- ⊢ ∫⁻ (x : α) in s, ↑(f x) ∂μ < ⊤
  rw [mem_upperBounds] at hM
  -- ⊢ ∫⁻ (x : α) in s, ↑(f x) ∂μ < ⊤
  refine'
    lt_of_le_of_lt (set_lintegral_mono hf.coe_nnreal_ennreal (@measurable_const _ _ _ _ ↑M) _) _
  · simpa using hM
    -- 🎉 no goals
  · rw [lintegral_const]
    -- ⊢ ↑M * ↑↑(Measure.restrict μ s) univ < ⊤
    refine' ENNReal.mul_lt_top ENNReal.coe_lt_top.ne _
    -- ⊢ ↑↑(Measure.restrict μ s) univ ≠ ⊤
    simp [hs]
    -- 🎉 no goals
#align measure_theory.set_lintegral_lt_top_of_bdd_above MeasureTheory.set_lintegral_lt_top_of_bddAbove

theorem set_lintegral_lt_top_of_isCompact [TopologicalSpace α] [OpensMeasurableSpace α] {s : Set α}
    (hs : μ s ≠ ∞) (hsc : IsCompact s) {f : α → ℝ≥0} (hf : Continuous f) :
    ∫⁻ x in s, f x ∂μ < ∞ :=
  set_lintegral_lt_top_of_bddAbove hs hf.measurable (hsc.image hf).bddAbove
#align measure_theory.set_lintegral_lt_top_of_is_compact MeasureTheory.set_lintegral_lt_top_of_isCompact

theorem _root_.IsFiniteMeasure.lintegral_lt_top_of_bounded_to_eNNReal {α : Type*}
    [MeasurableSpace α] (μ : Measure α) [μ_fin : IsFiniteMeasure μ] {f : α → ℝ≥0∞}
    (f_bdd : ∃ c : ℝ≥0, ∀ x, f x ≤ c) : ∫⁻ x, f x ∂μ < ∞ := by
  cases' f_bdd with c hc
  -- ⊢ ∫⁻ (x : α), f x ∂μ < ⊤
  apply lt_of_le_of_lt (@lintegral_mono _ _ μ _ _ hc)
  -- ⊢ ∫⁻ (a : α), ↑c ∂μ < ⊤
  rw [lintegral_const]
  -- ⊢ ↑c * ↑↑μ univ < ⊤
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top.ne μ_fin.measure_univ_lt_top.ne
  -- 🎉 no goals
#align is_finite_measure.lintegral_lt_top_of_bounded_to_ennreal IsFiniteMeasure.lintegral_lt_top_of_bounded_to_eNNReal

/-- Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the
measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`. -/
def Measure.withDensity {m : MeasurableSpace α} (μ : Measure α) (f : α → ℝ≥0∞) : Measure α :=
  Measure.ofMeasurable (fun s _ => ∫⁻ a in s, f a ∂μ) (by simp) fun s hs hd =>
                                                          -- 🎉 no goals
    lintegral_iUnion hs hd _
#align measure_theory.measure.with_density MeasureTheory.Measure.withDensity

@[simp]
theorem withDensity_apply (f : α → ℝ≥0∞) {s : Set α} (hs : MeasurableSet s) :
    μ.withDensity f s = ∫⁻ a in s, f a ∂μ :=
  Measure.ofMeasurable_apply s hs
#align measure_theory.with_density_apply MeasureTheory.withDensity_apply

theorem withDensity_congr_ae {f g : α → ℝ≥0∞} (h : f =ᵐ[μ] g) :
    μ.withDensity f = μ.withDensity g := by
  refine Measure.ext fun s hs => ?_
  -- ⊢ ↑↑(withDensity μ f) s = ↑↑(withDensity μ g) s
  rw [withDensity_apply _ hs, withDensity_apply _ hs]
  -- ⊢ ∫⁻ (a : α) in s, f a ∂μ = ∫⁻ (a : α) in s, g a ∂μ
  exact lintegral_congr_ae (ae_restrict_of_ae h)
  -- 🎉 no goals
#align measure_theory.with_density_congr_ae MeasureTheory.withDensity_congr_ae

theorem withDensity_add_left {f : α → ℝ≥0∞} (hf : Measurable f) (g : α → ℝ≥0∞) :
    μ.withDensity (f + g) = μ.withDensity f + μ.withDensity g := by
  refine' Measure.ext fun s hs => _
  -- ⊢ ↑↑(withDensity μ (f + g)) s = ↑↑(withDensity μ f + withDensity μ g) s
  rw [withDensity_apply _ hs, Measure.add_apply, withDensity_apply _ hs, withDensity_apply _ hs,
    ← lintegral_add_left hf]
  rfl
  -- 🎉 no goals
#align measure_theory.with_density_add_left MeasureTheory.withDensity_add_left

theorem withDensity_add_right (f : α → ℝ≥0∞) {g : α → ℝ≥0∞} (hg : Measurable g) :
    μ.withDensity (f + g) = μ.withDensity f + μ.withDensity g := by
  simpa only [add_comm] using withDensity_add_left hg f
  -- 🎉 no goals
#align measure_theory.with_density_add_right MeasureTheory.withDensity_add_right

theorem withDensity_add_measure {m : MeasurableSpace α} (μ ν : Measure α) (f : α → ℝ≥0∞) :
    (μ + ν).withDensity f = μ.withDensity f + ν.withDensity f := by
  ext1 s hs
  -- ⊢ ↑↑(withDensity (μ + ν) f) s = ↑↑(withDensity μ f + withDensity ν f) s
  simp only [withDensity_apply f hs, restrict_add, lintegral_add_measure, Measure.add_apply]
  -- 🎉 no goals
#align measure_theory.with_density_add_measure MeasureTheory.withDensity_add_measure

theorem withDensity_sum {ι : Type*} {m : MeasurableSpace α} (μ : ι → Measure α) (f : α → ℝ≥0∞) :
    (sum μ).withDensity f = sum fun n => (μ n).withDensity f := by
  ext1 s hs
  -- ⊢ ↑↑(withDensity (sum μ) f) s = ↑↑(sum fun n => withDensity (μ n) f) s
  simp_rw [sum_apply _ hs, withDensity_apply f hs, restrict_sum μ hs, lintegral_sum_measure]
  -- 🎉 no goals
#align measure_theory.with_density_sum MeasureTheory.withDensity_sum

theorem withDensity_smul (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : Measurable f) :
    μ.withDensity (r • f) = r • μ.withDensity f := by
  refine' Measure.ext fun s hs => _
  -- ⊢ ↑↑(withDensity μ (r • f)) s = ↑↑(r • withDensity μ f) s
  rw [withDensity_apply _ hs, Measure.coe_smul, Pi.smul_apply, withDensity_apply _ hs,
    smul_eq_mul, ← lintegral_const_mul r hf]
  rfl
  -- 🎉 no goals
#align measure_theory.with_density_smul MeasureTheory.withDensity_smul

theorem withDensity_smul' (r : ℝ≥0∞) (f : α → ℝ≥0∞) (hr : r ≠ ∞) :
    μ.withDensity (r • f) = r • μ.withDensity f := by
  refine' Measure.ext fun s hs => _
  -- ⊢ ↑↑(withDensity μ (r • f)) s = ↑↑(r • withDensity μ f) s
  rw [withDensity_apply _ hs, Measure.coe_smul, Pi.smul_apply, withDensity_apply _ hs,
    smul_eq_mul, ← lintegral_const_mul' r f hr]
  rfl
  -- 🎉 no goals
#align measure_theory.with_density_smul' MeasureTheory.withDensity_smul'

theorem isFiniteMeasure_withDensity {f : α → ℝ≥0∞} (hf : ∫⁻ a, f a ∂μ ≠ ∞) :
    IsFiniteMeasure (μ.withDensity f) :=
  { measure_univ_lt_top := by
      rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lt_top_iff_ne_top] }
      -- 🎉 no goals
#align measure_theory.is_finite_measure_with_density MeasureTheory.isFiniteMeasure_withDensity

theorem withDensity_absolutelyContinuous {m : MeasurableSpace α} (μ : Measure α) (f : α → ℝ≥0∞) :
    μ.withDensity f ≪ μ := by
  refine' AbsolutelyContinuous.mk fun s hs₁ hs₂ => _
  -- ⊢ ↑↑(withDensity μ f) s = 0
  rw [withDensity_apply _ hs₁]
  -- ⊢ ∫⁻ (a : α) in s, f a ∂μ = 0
  exact set_lintegral_measure_zero _ _ hs₂
  -- 🎉 no goals
#align measure_theory.with_density_absolutely_continuous MeasureTheory.withDensity_absolutelyContinuous

@[simp]
theorem withDensity_zero : μ.withDensity 0 = 0 := by
  ext1 s hs
  -- ⊢ ↑↑(withDensity μ 0) s = ↑↑0 s
  simp [withDensity_apply _ hs]
  -- 🎉 no goals
#align measure_theory.with_density_zero MeasureTheory.withDensity_zero

@[simp]
theorem withDensity_one : μ.withDensity 1 = μ := by
  ext1 s hs
  -- ⊢ ↑↑(withDensity μ 1) s = ↑↑μ s
  simp [withDensity_apply _ hs]
  -- 🎉 no goals
#align measure_theory.with_density_one MeasureTheory.withDensity_one

theorem withDensity_tsum {f : ℕ → α → ℝ≥0∞} (h : ∀ i, Measurable (f i)) :
    μ.withDensity (∑' n, f n) = sum fun n => μ.withDensity (f n) := by
  ext1 s hs
  -- ⊢ ↑↑(withDensity μ (∑' (n : ℕ), f n)) s = ↑↑(sum fun n => withDensity μ (f n)) s
  simp_rw [sum_apply _ hs, withDensity_apply _ hs]
  -- ⊢ ∫⁻ (a : α) in s, tsum (fun n => f n) a ∂μ = ∑' (i : ℕ), ∫⁻ (a : α) in s, f i …
  change ∫⁻ x in s, (∑' n, f n) x ∂μ = ∑' i : ℕ, ∫⁻ x, f i x ∂μ.restrict s
  -- ⊢ ∫⁻ (x : α) in s, tsum (fun n => f n) x ∂μ = ∑' (i : ℕ), ∫⁻ (x : α) in s, f i …
  rw [← lintegral_tsum fun i => (h i).aemeasurable]
  -- ⊢ ∫⁻ (x : α) in s, tsum (fun n => f n) x ∂μ = ∫⁻ (a : α) in s, ∑' (i : ℕ), f i …
  refine' lintegral_congr fun x => tsum_apply (Pi.summable.2 fun _ => ENNReal.summable)
  -- 🎉 no goals
#align measure_theory.with_density_tsum MeasureTheory.withDensity_tsum

theorem withDensity_indicator {s : Set α} (hs : MeasurableSet s) (f : α → ℝ≥0∞) :
    μ.withDensity (s.indicator f) = (μ.restrict s).withDensity f := by
  ext1 t ht
  -- ⊢ ↑↑(withDensity μ (indicator s f)) t = ↑↑(withDensity (Measure.restrict μ s)  …
  rw [withDensity_apply _ ht, lintegral_indicator _ hs, restrict_comm hs, ←
    withDensity_apply _ ht]
#align measure_theory.with_density_indicator MeasureTheory.withDensity_indicator

theorem withDensity_indicator_one {s : Set α} (hs : MeasurableSet s) :
    μ.withDensity (s.indicator 1) = μ.restrict s := by
  rw [withDensity_indicator hs, withDensity_one]
  -- 🎉 no goals
#align measure_theory.with_density_indicator_one MeasureTheory.withDensity_indicator_one

theorem withDensity_ofReal_mutuallySingular {f : α → ℝ} (hf : Measurable f) :
    (μ.withDensity fun x => ENNReal.ofReal <| f x) ⟂ₘ
      μ.withDensity fun x => ENNReal.ofReal <| -f x := by
  set S : Set α := { x | f x < 0 }
  -- ⊢ (withDensity μ fun x => ENNReal.ofReal (f x)) ⟂ₘ withDensity μ fun x => ENNR …
  have hS : MeasurableSet S := measurableSet_lt hf measurable_const
  -- ⊢ (withDensity μ fun x => ENNReal.ofReal (f x)) ⟂ₘ withDensity μ fun x => ENNR …
  refine' ⟨S, hS, _, _⟩
  -- ⊢ ↑↑(withDensity μ fun x => ENNReal.ofReal (f x)) S = 0
  · rw [withDensity_apply _ hS, lintegral_eq_zero_iff hf.ennreal_ofReal, EventuallyEq]
    -- ⊢ ∀ᵐ (x : α) ∂Measure.restrict μ S, ENNReal.ofReal (f x) = OfNat.ofNat 0 x
    exact (ae_restrict_mem hS).mono fun x hx => ENNReal.ofReal_eq_zero.2 (le_of_lt hx)
    -- 🎉 no goals
  · rw [withDensity_apply _ hS.compl, lintegral_eq_zero_iff hf.neg.ennreal_ofReal, EventuallyEq]
    -- ⊢ ∀ᵐ (x : α) ∂Measure.restrict μ Sᶜ, ENNReal.ofReal (-f x) = OfNat.ofNat 0 x
    exact
      (ae_restrict_mem hS.compl).mono fun x hx =>
        ENNReal.ofReal_eq_zero.2 (not_lt.1 <| mt neg_pos.1 hx)
#align measure_theory.with_density_of_real_mutually_singular MeasureTheory.withDensity_ofReal_mutuallySingular

theorem restrict_withDensity {s : Set α} (hs : MeasurableSet s) (f : α → ℝ≥0∞) :
    (μ.withDensity f).restrict s = (μ.restrict s).withDensity f := by
  ext1 t ht
  -- ⊢ ↑↑(Measure.restrict (withDensity μ f) s) t = ↑↑(withDensity (Measure.restric …
  rw [restrict_apply ht, withDensity_apply _ ht, withDensity_apply _ (ht.inter hs),
    restrict_restrict ht]
#align measure_theory.restrict_with_density MeasureTheory.restrict_withDensity

theorem withDensity_eq_zero {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (h : μ.withDensity f = 0) :
    f =ᵐ[μ] 0 := by
  rw [← lintegral_eq_zero_iff' hf, ← set_lintegral_univ, ← withDensity_apply _ MeasurableSet.univ,
    h, Measure.coe_zero, Pi.zero_apply]
#align measure_theory.with_density_eq_zero MeasureTheory.withDensity_eq_zero

theorem withDensity_apply_eq_zero {f : α → ℝ≥0∞} {s : Set α} (hf : Measurable f) :
    μ.withDensity f s = 0 ↔ μ ({ x | f x ≠ 0 } ∩ s) = 0 := by
  constructor
  -- ⊢ ↑↑(withDensity μ f) s = 0 → ↑↑μ ({x | f x ≠ 0} ∩ s) = 0
  · intro hs
    -- ⊢ ↑↑μ ({x | f x ≠ 0} ∩ s) = 0
    let t := toMeasurable (μ.withDensity f) s
    -- ⊢ ↑↑μ ({x | f x ≠ 0} ∩ s) = 0
    apply measure_mono_null (inter_subset_inter_right _ (subset_toMeasurable (μ.withDensity f) s))
    -- ⊢ ↑↑μ ({x | f x ≠ 0} ∩ toMeasurable (withDensity μ f) s) = 0
    have A : μ.withDensity f t = 0 := by rw [measure_toMeasurable, hs]
    -- ⊢ ↑↑μ ({x | f x ≠ 0} ∩ toMeasurable (withDensity μ f) s) = 0
    rw [withDensity_apply f (measurableSet_toMeasurable _ s), lintegral_eq_zero_iff hf,
      EventuallyEq, ae_restrict_iff, ae_iff] at A
    swap
    -- ⊢ MeasurableSet {x | f x = OfNat.ofNat 0 x}
    · exact hf (measurableSet_singleton 0)
      -- 🎉 no goals
    simp only [Pi.zero_apply, mem_setOf_eq, Filter.mem_mk] at A
    -- ⊢ ↑↑μ ({x | f x ≠ 0} ∩ toMeasurable (withDensity μ f) s) = 0
    convert A using 2
    -- ⊢ {x | f x ≠ 0} ∩ toMeasurable (withDensity μ f) s = {a | ¬(a ∈ toMeasurable ( …
    ext x
    -- ⊢ x ∈ {x | f x ≠ 0} ∩ toMeasurable (withDensity μ f) s ↔ x ∈ {a | ¬(a ∈ toMeas …
    simp only [and_comm, exists_prop, mem_inter_iff, iff_self_iff, mem_setOf_eq, mem_compl_iff,
      not_forall]
  · intro hs
    -- ⊢ ↑↑(withDensity μ f) s = 0
    let t := toMeasurable μ ({ x | f x ≠ 0 } ∩ s)
    -- ⊢ ↑↑(withDensity μ f) s = 0
    have A : s ⊆ t ∪ { x | f x = 0 } := by
      intro x hx
      rcases eq_or_ne (f x) 0 with (fx | fx)
      · simp only [fx, mem_union, mem_setOf_eq, eq_self_iff_true, or_true_iff]
      · left
        apply subset_toMeasurable _ _
        exact ⟨fx, hx⟩
    apply measure_mono_null A (measure_union_null _ _)
    -- ⊢ ↑↑(withDensity μ f) t = 0
    · apply withDensity_absolutelyContinuous
      -- ⊢ ↑↑μ t = 0
      rwa [measure_toMeasurable]
      -- 🎉 no goals
    · have M : MeasurableSet { x : α | f x = 0 } := hf (measurableSet_singleton _)
      -- ⊢ ↑↑(withDensity μ f) {x | f x = 0} = 0
      rw [withDensity_apply _ M, lintegral_eq_zero_iff hf]
      -- ⊢ f =ᶠ[ae (Measure.restrict μ {x | f x = 0})] 0
      filter_upwards [ae_restrict_mem M]
      -- ⊢ ∀ (a : α), f a = 0 → f a = OfNat.ofNat 0 a
      simp only [imp_self, Pi.zero_apply, imp_true_iff]
      -- 🎉 no goals
#align measure_theory.with_density_apply_eq_zero MeasureTheory.withDensity_apply_eq_zero

theorem ae_withDensity_iff {p : α → Prop} {f : α → ℝ≥0∞} (hf : Measurable f) :
    (∀ᵐ x ∂μ.withDensity f, p x) ↔ ∀ᵐ x ∂μ, f x ≠ 0 → p x := by
  rw [ae_iff, ae_iff, withDensity_apply_eq_zero hf, iff_iff_eq]
  -- ⊢ (↑↑μ ({x | f x ≠ 0} ∩ {a | ¬p a}) = 0) = (↑↑μ {a | ¬(f a ≠ 0 → p a)} = 0)
  congr
  -- ⊢ {x | f x ≠ 0} ∩ {a | ¬p a} = {a | ¬(f a ≠ 0 → p a)}
  ext x
  -- ⊢ x ∈ {x | f x ≠ 0} ∩ {a | ¬p a} ↔ x ∈ {a | ¬(f a ≠ 0 → p a)}
  simp only [exists_prop, mem_inter_iff, iff_self_iff, mem_setOf_eq, not_forall]
  -- 🎉 no goals
#align measure_theory.ae_with_density_iff MeasureTheory.ae_withDensity_iff

theorem ae_withDensity_iff_ae_restrict {p : α → Prop} {f : α → ℝ≥0∞} (hf : Measurable f) :
    (∀ᵐ x ∂μ.withDensity f, p x) ↔ ∀ᵐ x ∂μ.restrict { x | f x ≠ 0 }, p x := by
  rw [ae_withDensity_iff hf, ae_restrict_iff']
  -- ⊢ (∀ᵐ (x : α) ∂μ, f x ≠ 0 → p x) ↔ ∀ᵐ (x : α) ∂μ, x ∈ {x | f x ≠ 0} → p x
  · rfl
    -- 🎉 no goals
  · exact hf (measurableSet_singleton 0).compl
    -- 🎉 no goals
#align measure_theory.ae_with_density_iff_ae_restrict MeasureTheory.ae_withDensity_iff_ae_restrict

theorem aemeasurable_withDensity_ennreal_iff {f : α → ℝ≥0} (hf : Measurable f) {g : α → ℝ≥0∞} :
    AEMeasurable g (μ.withDensity fun x => (f x : ℝ≥0∞)) ↔
      AEMeasurable (fun x => (f x : ℝ≥0∞) * g x) μ := by
  constructor
  -- ⊢ AEMeasurable g → AEMeasurable fun x => ↑(f x) * g x
  · rintro ⟨g', g'meas, hg'⟩
    -- ⊢ AEMeasurable fun x => ↑(f x) * g x
    have A : MeasurableSet { x : α | f x ≠ 0 } := (hf (measurableSet_singleton 0)).compl
    -- ⊢ AEMeasurable fun x => ↑(f x) * g x
    refine' ⟨fun x => f x * g' x, hf.coe_nnreal_ennreal.smul g'meas, _⟩
    -- ⊢ (fun x => ↑(f x) * g x) =ᶠ[ae μ] fun x => ↑(f x) * g' x
    apply ae_of_ae_restrict_of_ae_restrict_compl { x | f x ≠ 0 }
    -- ⊢ ∀ᵐ (x : α) ∂Measure.restrict μ {x | f x ≠ 0}, (fun x => ↑(f x) * g x) x = (f …
    · rw [EventuallyEq, ae_withDensity_iff hf.coe_nnreal_ennreal] at hg'
      -- ⊢ ∀ᵐ (x : α) ∂Measure.restrict μ {x | f x ≠ 0}, (fun x => ↑(f x) * g x) x = (f …
      rw [ae_restrict_iff' A]
      -- ⊢ ∀ᵐ (x : α) ∂μ, x ∈ {x | f x ≠ 0} → (fun x => ↑(f x) * g x) x = (fun x => ↑(f …
      filter_upwards [hg']
      -- ⊢ ∀ (a : α), (↑(f a) ≠ 0 → g a = g' a) → f a ≠ 0 → ↑(f a) * g a = ↑(f a) * g' a
      intro a ha h'a
      -- ⊢ ↑(f a) * g a = ↑(f a) * g' a
      have : (f a : ℝ≥0∞) ≠ 0 := by simpa only [Ne.def, coe_eq_zero] using h'a
      -- ⊢ ↑(f a) * g a = ↑(f a) * g' a
      rw [ha this]
      -- 🎉 no goals
    · filter_upwards [ae_restrict_mem A.compl]
      -- ⊢ ∀ (a : α), a ∈ {x | f x ≠ 0}ᶜ → ↑(f a) * g a = ↑(f a) * g' a
      intro x hx
      -- ⊢ ↑(f x) * g x = ↑(f x) * g' x
      simp only [Classical.not_not, mem_setOf_eq, mem_compl_iff] at hx
      -- ⊢ ↑(f x) * g x = ↑(f x) * g' x
      simp [hx]
      -- 🎉 no goals
  · rintro ⟨g', g'meas, hg'⟩
    -- ⊢ AEMeasurable g
    refine' ⟨fun x => ((f x)⁻¹ : ℝ≥0∞) * g' x, hf.coe_nnreal_ennreal.inv.smul g'meas, _⟩
    -- ⊢ g =ᶠ[ae (withDensity μ fun x => ↑(f x))] fun x => (↑(f x))⁻¹ * g' x
    rw [EventuallyEq, ae_withDensity_iff hf.coe_nnreal_ennreal]
    -- ⊢ ∀ᵐ (x : α) ∂μ, ↑(f x) ≠ 0 → g x = (↑(f x))⁻¹ * g' x
    filter_upwards [hg']
    -- ⊢ ∀ (a : α), ↑(f a) * g a = g' a → ↑(f a) ≠ 0 → g a = (↑(f a))⁻¹ * g' a
    intro x hx h'x
    -- ⊢ g x = (↑(f x))⁻¹ * g' x
    rw [← hx, ← mul_assoc, ENNReal.inv_mul_cancel h'x ENNReal.coe_ne_top, one_mul]
    -- 🎉 no goals
#align measure_theory.ae_measurable_with_density_ennreal_iff MeasureTheory.aemeasurable_withDensity_ennreal_iff

end Lintegral

open MeasureTheory.SimpleFunc

variable {m m0 : MeasurableSpace α}

/-- This is Exercise 1.2.1 from [tao2010]. It allows you to express integration of a measurable
function with respect to `(μ.withDensity f)` as an integral with respect to `μ`, called the base
measure. `μ` is often the Lebesgue measure, and in this circumstance `f` is the probability density
function, and `(μ.withDensity f)` represents any continuous random variable as a
probability measure, such as the uniform distribution between 0 and 1, the Gaussian distribution,
the exponential distribution, the Beta distribution, or the Cauchy distribution (see Section 2.4
of [wasserman2004]). Thus, this method shows how to one can calculate expectations, variances,
and other moments as a function of the probability density function.
 -/
theorem lintegral_withDensity_eq_lintegral_mul (μ : Measure α) {f : α → ℝ≥0∞}
    (h_mf : Measurable f) :
    ∀ {g : α → ℝ≥0∞}, Measurable g → ∫⁻ a, g a ∂μ.withDensity f = ∫⁻ a, (f * g) a ∂μ := by
  apply Measurable.ennreal_induction
  · intro c s h_ms
    -- ⊢ ∫⁻ (a : α), indicator s (fun x => c) a ∂Measure.withDensity μ f = ∫⁻ (a : α) …
    simp [*, mul_comm _ c, ← indicator_mul_right]
    -- 🎉 no goals
  · intro g h _ h_mea_g _ h_ind_g h_ind_h
    -- ⊢ ∫⁻ (a : α), (g + h) a ∂Measure.withDensity μ f = ∫⁻ (a : α), (f * (g + h)) a …
    simp [mul_add, *, Measurable.mul]
    -- 🎉 no goals
  · intro g h_mea_g h_mono_g h_ind
    -- ⊢ ∫⁻ (a : α), (fun x => ⨆ (n : ℕ), g n x) a ∂Measure.withDensity μ f = ∫⁻ (a : …
    have : Monotone fun n a => f a * g n a := fun m n hmn x => mul_le_mul_left' (h_mono_g hmn x) _
    -- ⊢ ∫⁻ (a : α), (fun x => ⨆ (n : ℕ), g n x) a ∂Measure.withDensity μ f = ∫⁻ (a : …
    simp [lintegral_iSup, ENNReal.mul_iSup, h_mf.mul (h_mea_g _), *]
    -- 🎉 no goals
#align measure_theory.lintegral_with_density_eq_lintegral_mul MeasureTheory.lintegral_withDensity_eq_lintegral_mul

theorem set_lintegral_withDensity_eq_set_lintegral_mul (μ : Measure α) {f g : α → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ x in s, g x ∂μ.withDensity f = ∫⁻ x in s, (f * g) x ∂μ := by
  rw [restrict_withDensity hs, lintegral_withDensity_eq_lintegral_mul _ hf hg]
  -- 🎉 no goals
#align measure_theory.set_lintegral_with_density_eq_set_lintegral_mul MeasureTheory.set_lintegral_withDensity_eq_set_lintegral_mul

/-- The Lebesgue integral of `g` with respect to the measure `μ.withDensity f` coincides with
the integral of `f * g`. This version assumes that `g` is almost everywhere measurable. For a
version without conditions on `g` but requiring that `f` is almost everywhere finite, see
`lintegral_withDensity_eq_lintegral_mul_non_measurable` -/
theorem lintegral_withDensity_eq_lintegral_mul₀' {μ : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) {g : α → ℝ≥0∞} (hg : AEMeasurable g (μ.withDensity f)) :
    ∫⁻ a, g a ∂μ.withDensity f = ∫⁻ a, (f * g) a ∂μ := by
  let f' := hf.mk f
  -- ⊢ ∫⁻ (a : α), g a ∂Measure.withDensity μ f = ∫⁻ (a : α), (f * g) a ∂μ
  have : μ.withDensity f = μ.withDensity f' := withDensity_congr_ae hf.ae_eq_mk
  -- ⊢ ∫⁻ (a : α), g a ∂Measure.withDensity μ f = ∫⁻ (a : α), (f * g) a ∂μ
  rw [this] at hg ⊢
  -- ⊢ ∫⁻ (a : α), g a ∂Measure.withDensity μ f' = ∫⁻ (a : α), (f * g) a ∂μ
  let g' := hg.mk g
  -- ⊢ ∫⁻ (a : α), g a ∂Measure.withDensity μ f' = ∫⁻ (a : α), (f * g) a ∂μ
  calc
    ∫⁻ a, g a ∂μ.withDensity f' = ∫⁻ a, g' a ∂μ.withDensity f' := lintegral_congr_ae hg.ae_eq_mk
    _ = ∫⁻ a, (f' * g') a ∂μ :=
      (lintegral_withDensity_eq_lintegral_mul _ hf.measurable_mk hg.measurable_mk)
    _ = ∫⁻ a, (f' * g) a ∂μ := by
      apply lintegral_congr_ae
      apply ae_of_ae_restrict_of_ae_restrict_compl { x | f' x ≠ 0 }
      · have Z := hg.ae_eq_mk
        rw [EventuallyEq, ae_withDensity_iff_ae_restrict hf.measurable_mk] at Z
        filter_upwards [Z]
        intro x hx
        simp only [hx, Pi.mul_apply]
      · have M : MeasurableSet { x : α | f' x ≠ 0 }ᶜ :=
          (hf.measurable_mk (measurableSet_singleton 0).compl).compl
        filter_upwards [ae_restrict_mem M]
        intro x hx
        simp only [Classical.not_not, mem_setOf_eq, mem_compl_iff] at hx
        simp only [hx, zero_mul, Pi.mul_apply]
    _ = ∫⁻ a : α, (f * g) a ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hf.ae_eq_mk]
      intro x hx
      simp only [hx, Pi.mul_apply]
#align measure_theory.lintegral_with_density_eq_lintegral_mul₀' MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀'

theorem lintegral_withDensity_eq_lintegral_mul₀ {μ : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) {g : α → ℝ≥0∞} (hg : AEMeasurable g μ) :
    ∫⁻ a, g a ∂μ.withDensity f = ∫⁻ a, (f * g) a ∂μ :=
  lintegral_withDensity_eq_lintegral_mul₀' hf (hg.mono' (withDensity_absolutelyContinuous μ f))
#align measure_theory.lintegral_with_density_eq_lintegral_mul₀ MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀

theorem lintegral_withDensity_le_lintegral_mul (μ : Measure α) {f : α → ℝ≥0∞}
    (f_meas : Measurable f) (g : α → ℝ≥0∞) : (∫⁻ a, g a ∂μ.withDensity f) ≤ ∫⁻ a, (f * g) a ∂μ := by
  rw [← iSup_lintegral_measurable_le_eq_lintegral, ← iSup_lintegral_measurable_le_eq_lintegral]
  -- ⊢ ⨆ (g_1 : α → ℝ≥0∞) (_ : Measurable g_1) (_ : g_1 ≤ fun a => g a), ∫⁻ (a : α) …
  refine' iSup₂_le fun i i_meas => iSup_le fun hi => _
  -- ⊢ ∫⁻ (a : α), i a ∂Measure.withDensity μ f ≤ ⨆ (g_1 : α → ℝ≥0∞) (_ : Measurabl …
  have A : f * i ≤ f * g := fun x => mul_le_mul_left' (hi x) _
  -- ⊢ ∫⁻ (a : α), i a ∂Measure.withDensity μ f ≤ ⨆ (g_1 : α → ℝ≥0∞) (_ : Measurabl …
  refine' le_iSup₂_of_le (f * i) (f_meas.mul i_meas) _
  -- ⊢ ∫⁻ (a : α), i a ∂Measure.withDensity μ f ≤ ⨆ (_ : f * i ≤ fun a => (f * g) a …
  exact le_iSup_of_le A (le_of_eq (lintegral_withDensity_eq_lintegral_mul _ f_meas i_meas))
  -- 🎉 no goals
#align measure_theory.lintegral_with_density_le_lintegral_mul MeasureTheory.lintegral_withDensity_le_lintegral_mul

theorem lintegral_withDensity_eq_lintegral_mul_non_measurable (μ : Measure α) {f : α → ℝ≥0∞}
    (f_meas : Measurable f) (hf : ∀ᵐ x ∂μ, f x < ∞) (g : α → ℝ≥0∞) :
    ∫⁻ a, g a ∂μ.withDensity f = ∫⁻ a, (f * g) a ∂μ := by
  refine' le_antisymm (lintegral_withDensity_le_lintegral_mul μ f_meas g) _
  -- ⊢ ∫⁻ (a : α), (f * g) a ∂μ ≤ ∫⁻ (a : α), g a ∂Measure.withDensity μ f
  rw [← iSup_lintegral_measurable_le_eq_lintegral, ← iSup_lintegral_measurable_le_eq_lintegral]
  -- ⊢ ⨆ (g_1 : α → ℝ≥0∞) (_ : Measurable g_1) (_ : g_1 ≤ fun a => (f * g) a), ∫⁻ ( …
  refine' iSup₂_le fun i i_meas => iSup_le fun hi => _
  -- ⊢ ∫⁻ (a : α), i a ∂μ ≤ ⨆ (g_1 : α → ℝ≥0∞) (_ : Measurable g_1) (_ : g_1 ≤ fun  …
  have A : (fun x => (f x)⁻¹ * i x) ≤ g := by
    intro x
    dsimp
    rw [mul_comm, ← div_eq_mul_inv]
    exact div_le_of_le_mul' (hi x)
  refine' le_iSup_of_le (fun x => (f x)⁻¹ * i x) (le_iSup_of_le (f_meas.inv.mul i_meas) _)
  -- ⊢ ∫⁻ (a : α), i a ∂μ ≤ ⨆ (_ : (fun x => (f x)⁻¹ * i x) ≤ fun a => g a), ∫⁻ (a  …
  refine' le_iSup_of_le A _
  -- ⊢ ∫⁻ (a : α), i a ∂μ ≤ ∫⁻ (a : α), (fun x => (f x)⁻¹ * i x) a ∂Measure.withDen …
  rw [lintegral_withDensity_eq_lintegral_mul _ f_meas (f_meas.inv.mul i_meas)]
  -- ⊢ ∫⁻ (a : α), i a ∂μ ≤ ∫⁻ (a : α), (f * fun a => (f a)⁻¹ * i a) a ∂μ
  apply lintegral_mono_ae
  -- ⊢ ∀ᵐ (a : α) ∂μ, i a ≤ (f * fun a => (f a)⁻¹ * i a) a
  filter_upwards [hf]
  -- ⊢ ∀ (a : α), f a < ⊤ → i a ≤ (f * fun a => (f a)⁻¹ * i a) a
  intro x h'x
  -- ⊢ i x ≤ (f * fun a => (f a)⁻¹ * i a) x
  rcases eq_or_ne (f x) 0 with (hx | hx)
  -- ⊢ i x ≤ (f * fun a => (f a)⁻¹ * i a) x
  · have := hi x
    -- ⊢ i x ≤ (f * fun a => (f a)⁻¹ * i a) x
    simp only [hx, zero_mul, Pi.mul_apply, nonpos_iff_eq_zero] at this
    -- ⊢ i x ≤ (f * fun a => (f a)⁻¹ * i a) x
    simp [this]
    -- 🎉 no goals
  · apply le_of_eq _
    -- ⊢ i x = (f * fun a => (f a)⁻¹ * i a) x
    dsimp
    -- ⊢ i x = f x * ((f x)⁻¹ * i x)
    rw [← mul_assoc, ENNReal.mul_inv_cancel hx h'x.ne, one_mul]
    -- 🎉 no goals
#align measure_theory.lintegral_with_density_eq_lintegral_mul_non_measurable MeasureTheory.lintegral_withDensity_eq_lintegral_mul_non_measurable

theorem set_lintegral_withDensity_eq_set_lintegral_mul_non_measurable (μ : Measure α) {f : α → ℝ≥0∞}
    (f_meas : Measurable f) (g : α → ℝ≥0∞) {s : Set α} (hs : MeasurableSet s)
    (hf : ∀ᵐ x ∂μ.restrict s, f x < ∞) :
    ∫⁻ a in s, g a ∂μ.withDensity f = ∫⁻ a in s, (f * g) a ∂μ := by
  rw [restrict_withDensity hs, lintegral_withDensity_eq_lintegral_mul_non_measurable _ f_meas hf]
  -- 🎉 no goals
#align measure_theory.set_lintegral_with_density_eq_set_lintegral_mul_non_measurable MeasureTheory.set_lintegral_withDensity_eq_set_lintegral_mul_non_measurable

theorem lintegral_withDensity_eq_lintegral_mul_non_measurable₀ (μ : Measure α) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (h'f : ∀ᵐ x ∂μ, f x < ∞) (g : α → ℝ≥0∞) :
    ∫⁻ a, g a ∂μ.withDensity f = ∫⁻ a, (f * g) a ∂μ := by
  let f' := hf.mk f
  -- ⊢ ∫⁻ (a : α), g a ∂Measure.withDensity μ f = ∫⁻ (a : α), (f * g) a ∂μ
  calc
    ∫⁻ a, g a ∂μ.withDensity f = ∫⁻ a, g a ∂μ.withDensity f' := by
      rw [withDensity_congr_ae hf.ae_eq_mk]
    _ = ∫⁻ a, (f' * g) a ∂μ := by
      apply lintegral_withDensity_eq_lintegral_mul_non_measurable _ hf.measurable_mk
      filter_upwards [h'f, hf.ae_eq_mk]
      intro x hx h'x
      rwa [← h'x]
    _ = ∫⁻ a, (f * g) a ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hf.ae_eq_mk]
      intro x hx
      simp only [hx, Pi.mul_apply]
#align measure_theory.lintegral_with_density_eq_lintegral_mul_non_measurable₀ MeasureTheory.lintegral_withDensity_eq_lintegral_mul_non_measurable₀

theorem set_lintegral_withDensity_eq_set_lintegral_mul_non_measurable₀ (μ : Measure α)
    {f : α → ℝ≥0∞} {s : Set α} (hf : AEMeasurable f (μ.restrict s)) (g : α → ℝ≥0∞)
    (hs : MeasurableSet s) (h'f : ∀ᵐ x ∂μ.restrict s, f x < ∞) :
    ∫⁻ a in s, g a ∂μ.withDensity f = ∫⁻ a in s, (f * g) a ∂μ := by
  rw [restrict_withDensity hs, lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hf h'f]
  -- 🎉 no goals
#align measure_theory.set_lintegral_with_density_eq_set_lintegral_mul_non_measurable₀ MeasureTheory.set_lintegral_withDensity_eq_set_lintegral_mul_non_measurable₀

theorem withDensity_mul (μ : Measure α) {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    μ.withDensity (f * g) = (μ.withDensity f).withDensity g := by
  ext1 s hs
  -- ⊢ ↑↑(Measure.withDensity μ (f * g)) s = ↑↑(Measure.withDensity (Measure.withDe …
  simp [withDensity_apply _ hs, restrict_withDensity hs,
    lintegral_withDensity_eq_lintegral_mul _ hf hg]
#align measure_theory.with_density_mul MeasureTheory.withDensity_mul

/-- In a sigma-finite measure space, there exists an integrable function which is
positive everywhere (and with an arbitrarily small integral). -/
theorem exists_pos_lintegral_lt_of_sigmaFinite (μ : Measure α) [SigmaFinite μ] {ε : ℝ≥0∞}
    (ε0 : ε ≠ 0) : ∃ g : α → ℝ≥0, (∀ x, 0 < g x) ∧ Measurable g ∧ ∫⁻ x, g x ∂μ < ε := by
  /- Let `s` be a covering of `α` by pairwise disjoint measurable sets of finite measure. Let
    `δ : ℕ → ℝ≥0` be a positive function such that `∑' i, μ (s i) * δ i < ε`. Then the function that
     is equal to `δ n` on `s n` is a positive function with integral less than `ε`. -/
  set s : ℕ → Set α := disjointed (spanningSets μ)
  -- ⊢ ∃ g, (∀ (x : α), 0 < g x) ∧ Measurable g ∧ ∫⁻ (x : α), ↑(g x) ∂μ < ε
  have : ∀ n, μ (s n) < ∞ := fun n =>
    (measure_mono <| disjointed_subset _ _).trans_lt (measure_spanningSets_lt_top μ n)
  obtain ⟨δ, δpos, δsum⟩ : ∃ δ : ℕ → ℝ≥0, (∀ i, 0 < δ i) ∧ (∑' i, μ (s i) * δ i) < ε
  -- ⊢ ∃ δ, (∀ (i : ℕ), 0 < δ i) ∧ ∑' (i : ℕ), ↑↑μ (s i) * ↑(δ i) < ε
  exact ENNReal.exists_pos_tsum_mul_lt_of_countable ε0 _ fun n => (this n).ne
  -- ⊢ ∃ g, (∀ (x : α), 0 < g x) ∧ Measurable g ∧ ∫⁻ (x : α), ↑(g x) ∂μ < ε
  set N : α → ℕ := spanningSetsIndex μ
  -- ⊢ ∃ g, (∀ (x : α), 0 < g x) ∧ Measurable g ∧ ∫⁻ (x : α), ↑(g x) ∂μ < ε
  have hN_meas : Measurable N := measurable_spanningSetsIndex μ
  -- ⊢ ∃ g, (∀ (x : α), 0 < g x) ∧ Measurable g ∧ ∫⁻ (x : α), ↑(g x) ∂μ < ε
  have hNs : ∀ n, N ⁻¹' {n} = s n := preimage_spanningSetsIndex_singleton μ
  -- ⊢ ∃ g, (∀ (x : α), 0 < g x) ∧ Measurable g ∧ ∫⁻ (x : α), ↑(g x) ∂μ < ε
  refine' ⟨δ ∘ N, fun x => δpos _, measurable_from_nat.comp hN_meas, _⟩
  -- ⊢ ∫⁻ (x : α), ↑((δ ∘ N) x) ∂μ < ε
  erw [lintegral_comp measurable_from_nat.coe_nnreal_ennreal hN_meas]
  -- ⊢ ∫⁻ (a : ℕ), ↑(δ a) ∂Measure.map N μ < ε
  simpa [hNs, lintegral_countable', measurable_spanningSetsIndex, mul_comm] using δsum
  -- 🎉 no goals
#align measure_theory.exists_pos_lintegral_lt_of_sigma_finite MeasureTheory.exists_pos_lintegral_lt_of_sigmaFinite

theorem lintegral_trim {μ : Measure α} (hm : m ≤ m0) {f : α → ℝ≥0∞} (hf : Measurable[m] f) :
    ∫⁻ a, f a ∂μ.trim hm = ∫⁻ a, f a ∂μ := by
  refine'
    @Measurable.ennreal_induction α m (fun f => ∫⁻ a, f a ∂μ.trim hm = ∫⁻ a, f a ∂μ) _ _ _ f hf
  · intro c s hs
    -- ⊢ ∫⁻ (a : α), indicator s (fun x => c) a ∂Measure.trim μ hm = ∫⁻ (a : α), indi …
    rw [lintegral_indicator _ hs, lintegral_indicator _ (hm s hs), set_lintegral_const,
      set_lintegral_const]
    suffices h_trim_s : μ.trim hm s = μ s
    -- ⊢ c * ↑↑(Measure.trim μ hm) s = c * ↑↑μ s
    · rw [h_trim_s]
      -- 🎉 no goals
    exact trim_measurableSet_eq hm hs
    -- 🎉 no goals
  · intro f g _ hf _ hf_prop hg_prop
    -- ⊢ ∫⁻ (a : α), (f + g) a ∂Measure.trim μ hm = ∫⁻ (a : α), (f + g) a ∂μ
    have h_m := lintegral_add_left (μ := Measure.trim μ hm) hf g
    -- ⊢ ∫⁻ (a : α), (f + g) a ∂Measure.trim μ hm = ∫⁻ (a : α), (f + g) a ∂μ
    have h_m0 := lintegral_add_left (μ := μ) (Measurable.mono hf hm le_rfl) g
    -- ⊢ ∫⁻ (a : α), (f + g) a ∂Measure.trim μ hm = ∫⁻ (a : α), (f + g) a ∂μ
    rwa [hf_prop, hg_prop, ← h_m0] at h_m
    -- 🎉 no goals
  · intro f hf hf_mono hf_prop
    -- ⊢ ∫⁻ (a : α), (fun x => ⨆ (n : ℕ), f n x) a ∂Measure.trim μ hm = ∫⁻ (a : α), ( …
    rw [lintegral_iSup hf hf_mono]
    -- ⊢ ⨆ (n : ℕ), ∫⁻ (a : α), f n a ∂Measure.trim μ hm = ∫⁻ (a : α), (fun x => ⨆ (n …
    rw [lintegral_iSup (fun n => Measurable.mono (hf n) hm le_rfl) hf_mono]
    -- ⊢ ⨆ (n : ℕ), ∫⁻ (a : α), f n a ∂Measure.trim μ hm = ⨆ (n : ℕ), ∫⁻ (a : α), f n …
    congr
    -- ⊢ (fun n => ∫⁻ (a : α), f n a ∂Measure.trim μ hm) = fun n => ∫⁻ (a : α), f n a …
    exact funext fun n => hf_prop n
    -- 🎉 no goals
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
  -- ⊢ f univ ≤ C
  have hS_mono : Monotone S := @monotone_spanningSets _ m (μ.trim hm) _
  -- ⊢ f univ ≤ C
  have hS_meas : ∀ n, MeasurableSet[m] (S n) := @measurable_spanningSets _ m (μ.trim hm) _
  -- ⊢ f univ ≤ C
  rw [← @iUnion_spanningSets _ m (μ.trim hm)]
  -- ⊢ f (⋃ (i : ℕ), spanningSets (Measure.trim μ hm) i) ≤ C
  refine' (h_F_lim S hS_meas hS_mono).trans _
  -- ⊢ ⨆ (n : ℕ), f (S n) ≤ C
  refine' iSup_le fun n => hf (S n) (hS_meas n) _
  -- ⊢ ↑↑μ (S n) ≠ ⊤
  exact ((le_trim hm).trans_lt (@measure_spanningSets_lt_top _ m (μ.trim hm) _ n)).ne
  -- 🎉 no goals
#align measure_theory.univ_le_of_forall_fin_meas_le MeasureTheory.univ_le_of_forall_fin_meas_le

/-- If the Lebesgue integral of a function is bounded by some constant on all sets with finite
measure in a sub-σ-algebra and the measure is σ-finite on that sub-σ-algebra, then the integral
over the whole space is bounded by that same constant. Version for a measurable function.
See `lintegral_le_of_forall_fin_meas_le'` for the more general `AEMeasurable` version. -/
theorem lintegral_le_of_forall_fin_meas_le_of_measurable {μ : Measure α} (hm : m ≤ m0)
    [SigmaFinite (μ.trim hm)] (C : ℝ≥0∞) {f : α → ℝ≥0∞} (hf_meas : Measurable f)
    (hf : ∀ s, MeasurableSet[m] s → μ s ≠ ∞ → ∫⁻ x in s, f x ∂μ ≤ C) : ∫⁻ x, f x ∂μ ≤ C := by
  have : ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ := by simp only [Measure.restrict_univ]
  -- ⊢ ∫⁻ (x : α), f x ∂μ ≤ C
  rw [← this]
  -- ⊢ ∫⁻ (x : α) in univ, f x ∂μ ≤ C
  refine' univ_le_of_forall_fin_meas_le hm C hf fun S hS_meas hS_mono => _
  -- ⊢ ∫⁻ (x : α) in ⋃ (n : ℕ), S n, f x ∂μ ≤ ⨆ (n : ℕ), ∫⁻ (x : α) in S n, f x ∂μ
  rw [← lintegral_indicator]
  -- ⊢ ∫⁻ (a : α), indicator (⋃ (n : ℕ), S n) (fun x => f x) a ∂μ ≤ ⨆ (n : ℕ), ∫⁻ ( …
  swap
  -- ⊢ MeasurableSet (⋃ (n : ℕ), S n)
  · exact hm (⋃ n, S n) (@MeasurableSet.iUnion _ _ m _ _ hS_meas)
    -- 🎉 no goals
  have h_integral_indicator : ⨆ n, ∫⁻ x in S n, f x ∂μ = ⨆ n, ∫⁻ x, (S n).indicator f x ∂μ := by
    congr
    ext1 n
    rw [lintegral_indicator _ (hm _ (hS_meas n))]
  rw [h_integral_indicator, ← lintegral_iSup]
  · refine' le_of_eq (lintegral_congr fun x => _)
    -- ⊢ indicator (⋃ (n : ℕ), S n) (fun x => f x) x = ⨆ (n : ℕ), indicator (S n) f x
    simp_rw [indicator_apply]
    -- ⊢ (if x ∈ ⋃ (n : ℕ), S n then f x else 0) = ⨆ (n : ℕ), if x ∈ S n then f x els …
    by_cases hx_mem : x ∈ iUnion S
    -- ⊢ (if x ∈ ⋃ (n : ℕ), S n then f x else 0) = ⨆ (n : ℕ), if x ∈ S n then f x els …
    · simp only [hx_mem, if_true]
      -- ⊢ f x = ⨆ (n : ℕ), if x ∈ S n then f x else 0
      obtain ⟨n, hxn⟩ := mem_iUnion.mp hx_mem
      -- ⊢ f x = ⨆ (n : ℕ), if x ∈ S n then f x else 0
      refine' le_antisymm (_root_.trans _ (le_iSup _ n)) (iSup_le fun i => _)
      -- ⊢ f x ≤ if x ∈ S n then f x else 0
      · simp only [hxn, le_refl, if_true]
        -- 🎉 no goals
      · by_cases hxi : x ∈ S i <;> simp [hxi]
        -- ⊢ (if x ∈ S i then f x else 0) ≤ f x
                                   -- 🎉 no goals
                                   -- 🎉 no goals
    · simp only [hx_mem, if_false]
      -- ⊢ 0 = ⨆ (n : ℕ), if x ∈ S n then f x else 0
      rw [mem_iUnion] at hx_mem
      -- ⊢ 0 = ⨆ (n : ℕ), if x ∈ S n then f x else 0
      push_neg at hx_mem
      -- ⊢ 0 = ⨆ (n : ℕ), if x ∈ S n then f x else 0
      refine' le_antisymm (zero_le _) (iSup_le fun n => _)
      -- ⊢ (if x ∈ S n then f x else 0) ≤ 0
      simp only [hx_mem n, if_false, nonpos_iff_eq_zero]
      -- 🎉 no goals
  · exact fun n => hf_meas.indicator (hm _ (hS_meas n))
    -- 🎉 no goals
  · intro n₁ n₂ hn₁₂ a
    -- ⊢ (fun n x => indicator (S n) f x) n₁ a ≤ (fun n x => indicator (S n) f x) n₂ a
    simp_rw [indicator_apply]
    -- ⊢ (if a ∈ S n₁ then f a else 0) ≤ if a ∈ S n₂ then f a else 0
    split_ifs with h h_1
    · exact le_rfl
      -- 🎉 no goals
    · exact absurd (mem_of_mem_of_subset h (hS_mono hn₁₂)) h_1
      -- 🎉 no goals
    · exact zero_le _
      -- 🎉 no goals
    · exact le_rfl
      -- 🎉 no goals
#align measure_theory.lintegral_le_of_forall_fin_meas_le_of_measurable MeasureTheory.lintegral_le_of_forall_fin_meas_le_of_measurable

/-- If the Lebesgue integral of a function is bounded by some constant on all sets with finite
measure in a sub-σ-algebra and the measure is σ-finite on that sub-σ-algebra, then the integral
over the whole space is bounded by that same constant. -/
theorem lintegral_le_of_forall_fin_meas_le' {μ : Measure α} (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (C : ℝ≥0∞) {f : _ → ℝ≥0∞} (hf_meas : AEMeasurable f μ)
    (hf : ∀ s, MeasurableSet[m] s → μ s ≠ ∞ → ∫⁻ x in s, f x ∂μ ≤ C) : ∫⁻ x, f x ∂μ ≤ C := by
  let f' := hf_meas.mk f
  -- ⊢ ∫⁻ (x : α), f x ∂μ ≤ C
  have hf' : ∀ s, MeasurableSet[m] s → μ s ≠ ∞ → ∫⁻ x in s, f' x ∂μ ≤ C := by
    refine' fun s hs hμs => (le_of_eq _).trans (hf s hs hμs)
    refine' lintegral_congr_ae (ae_restrict_of_ae (hf_meas.ae_eq_mk.mono fun x hx => _))
    dsimp only
    rw [hx]
  rw [lintegral_congr_ae hf_meas.ae_eq_mk]
  -- ⊢ ∫⁻ (a : α), AEMeasurable.mk f hf_meas a ∂μ ≤ C
  exact lintegral_le_of_forall_fin_meas_le_of_measurable hm C hf_meas.measurable_mk hf'
  -- 🎉 no goals
#align measure_theory.lintegral_le_of_forall_fin_meas_le' MeasureTheory.lintegral_le_of_forall_fin_meas_le'

/-- If the Lebesgue integral of a function is bounded by some constant on all sets with finite
measure and the measure is σ-finite, then the integral over the whole space is bounded by that same
constant. -/
theorem lintegral_le_of_forall_fin_meas_le [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    (C : ℝ≥0∞) {f : α → ℝ≥0∞} (hf_meas : AEMeasurable f μ)
    (hf : ∀ s, MeasurableSet s → μ s ≠ ∞ → ∫⁻ x in s, f x ∂μ ≤ C) : ∫⁻ x, f x ∂μ ≤ C :=
  @lintegral_le_of_forall_fin_meas_le' _ _ _ _ _ (by rwa [trim_eq_self]) C _ hf_meas hf
                                                     -- 🎉 no goals
#align measure_theory.lintegral_le_of_forall_fin_meas_le MeasureTheory.lintegral_le_of_forall_fin_meas_le

theorem SimpleFunc.exists_lt_lintegral_simpleFunc_of_lt_lintegral {m : MeasurableSpace α}
    {μ : Measure α} [SigmaFinite μ] {f : α →ₛ ℝ≥0} {L : ℝ≥0∞} (hL : L < ∫⁻ x, f x ∂μ) :
    ∃ g : α →ₛ ℝ≥0, (∀ x, g x ≤ f x) ∧ ∫⁻ x, g x ∂μ < ∞ ∧ L < ∫⁻ x, g x ∂μ := by
  induction' f using MeasureTheory.SimpleFunc.induction with c s hs f₁ f₂ _ h₁ h₂ generalizing L
  -- ⊢ ∃ g, (∀ (x : α), ↑g x ≤ ↑(piecewise s hs (const α c) (const α 0)) x) ∧ ∫⁻ (x …
  · simp only [hs, const_zero, coe_piecewise, coe_const, SimpleFunc.coe_zero, univ_inter,
      piecewise_eq_indicator, lintegral_indicator, lintegral_const, Measure.restrict_apply',
      ENNReal.coe_indicator, Function.const_apply] at hL
    have c_ne_zero : c ≠ 0 := by
      intro hc
      simp only [hc, ENNReal.coe_zero, zero_mul, not_lt_zero] at hL
    have : L / c < μ s := by
      rwa [ENNReal.div_lt_iff, mul_comm]
      · simp only [c_ne_zero, Ne.def, coe_eq_zero, not_false_iff, true_or_iff]
      · simp only [Ne.def, coe_ne_top, not_false_iff, true_or_iff]
    obtain ⟨t, ht, ts, mlt, t_top⟩ :
      ∃ t : Set α, MeasurableSet t ∧ t ⊆ s ∧ L / ↑c < μ t ∧ μ t < ∞ :=
      Measure.exists_subset_measure_lt_top hs this
    refine' ⟨piecewise t ht (const α c) (const α 0), fun x => _, _, _⟩
    · refine indicator_le_indicator_of_subset ts (fun x => ?_) x
      -- ⊢ 0 ≤ ↑(const α c) x
      exact zero_le _
      -- 🎉 no goals
    · simp only [ht, const_zero, coe_piecewise, coe_const, SimpleFunc.coe_zero, univ_inter,
        piecewise_eq_indicator, ENNReal.coe_indicator, Function.const_apply, lintegral_indicator,
        lintegral_const, Measure.restrict_apply', ENNReal.mul_lt_top ENNReal.coe_ne_top t_top.ne]
    · simp only [ht, const_zero, coe_piecewise, coe_const, SimpleFunc.coe_zero,
        piecewise_eq_indicator, ENNReal.coe_indicator, Function.const_apply, lintegral_indicator,
        lintegral_const, Measure.restrict_apply', univ_inter]
      rwa [mul_comm, ← ENNReal.div_lt_iff]
      -- ⊢ ↑c ≠ 0 ∨ L ≠ 0
      · simp only [c_ne_zero, Ne.def, coe_eq_zero, not_false_iff, true_or_iff]
        -- 🎉 no goals
      · simp only [Ne.def, coe_ne_top, not_false_iff, true_or_iff]
        -- 🎉 no goals
  · replace hL : L < ∫⁻ x, f₁ x ∂μ + ∫⁻ x, f₂ x ∂μ
    -- ⊢ L < ∫⁻ (x : α), ↑(↑f₁ x) ∂μ + ∫⁻ (x : α), ↑(↑f₂ x) ∂μ
    · rwa [← lintegral_add_left f₁.measurable.coe_nnreal_ennreal]
      -- 🎉 no goals
    by_cases hf₁ : ∫⁻ x, f₁ x ∂μ = 0
    -- ⊢ ∃ g, (∀ (x : α), ↑g x ≤ ↑(f₁ + f₂) x) ∧ ∫⁻ (x : α), ↑(↑g x) ∂μ < ⊤ ∧ L < ∫⁻  …
    · simp only [hf₁, zero_add] at hL
      -- ⊢ ∃ g, (∀ (x : α), ↑g x ≤ ↑(f₁ + f₂) x) ∧ ∫⁻ (x : α), ↑(↑g x) ∂μ < ⊤ ∧ L < ∫⁻  …
      rcases h₂ hL with ⟨g, g_le, g_top, gL⟩
      -- ⊢ ∃ g, (∀ (x : α), ↑g x ≤ ↑(f₁ + f₂) x) ∧ ∫⁻ (x : α), ↑(↑g x) ∂μ < ⊤ ∧ L < ∫⁻  …
      refine' ⟨g, fun x => (g_le x).trans _, g_top, gL⟩
      -- ⊢ ↑f₂ x ≤ ↑(f₁ + f₂) x
      simp only [SimpleFunc.coe_add, Pi.add_apply, le_add_iff_nonneg_left, zero_le']
      -- 🎉 no goals
    by_cases hf₂ : ∫⁻ x, f₂ x ∂μ = 0
    -- ⊢ ∃ g, (∀ (x : α), ↑g x ≤ ↑(f₁ + f₂) x) ∧ ∫⁻ (x : α), ↑(↑g x) ∂μ < ⊤ ∧ L < ∫⁻  …
    · simp only [hf₂, add_zero] at hL
      -- ⊢ ∃ g, (∀ (x : α), ↑g x ≤ ↑(f₁ + f₂) x) ∧ ∫⁻ (x : α), ↑(↑g x) ∂μ < ⊤ ∧ L < ∫⁻  …
      rcases h₁ hL with ⟨g, g_le, g_top, gL⟩
      -- ⊢ ∃ g, (∀ (x : α), ↑g x ≤ ↑(f₁ + f₂) x) ∧ ∫⁻ (x : α), ↑(↑g x) ∂μ < ⊤ ∧ L < ∫⁻  …
      refine' ⟨g, fun x => (g_le x).trans _, g_top, gL⟩
      -- ⊢ ↑f₁ x ≤ ↑(f₁ + f₂) x
      simp only [SimpleFunc.coe_add, Pi.add_apply, le_add_iff_nonneg_right, zero_le']
      -- 🎉 no goals
    obtain ⟨L₁, L₂, hL₁, hL₂, hL⟩ :
      ∃ L₁ L₂ : ℝ≥0∞, (L₁ < ∫⁻ x, f₁ x ∂μ) ∧ (L₂ < ∫⁻ x, f₂ x ∂μ) ∧ L < L₁ + L₂ :=
      ENNReal.exists_lt_add_of_lt_add hL hf₁ hf₂
    rcases h₁ hL₁ with ⟨g₁, g₁_le, g₁_top, hg₁⟩
    -- ⊢ ∃ g, (∀ (x : α), ↑g x ≤ ↑(f₁ + f₂) x) ∧ ∫⁻ (x : α), ↑(↑g x) ∂μ < ⊤ ∧ L < ∫⁻  …
    rcases h₂ hL₂ with ⟨g₂, g₂_le, g₂_top, hg₂⟩
    -- ⊢ ∃ g, (∀ (x : α), ↑g x ≤ ↑(f₁ + f₂) x) ∧ ∫⁻ (x : α), ↑(↑g x) ∂μ < ⊤ ∧ L < ∫⁻  …
    refine' ⟨g₁ + g₂, fun x => add_le_add (g₁_le x) (g₂_le x), _, _⟩
    -- ⊢ ∫⁻ (x : α), ↑(↑(g₁ + g₂) x) ∂μ < ⊤
    · apply lt_of_le_of_lt _ (add_lt_top.2 ⟨g₁_top, g₂_top⟩)
      -- ⊢ ∫⁻ (x : α), ↑(↑(g₁ + g₂) x) ∂μ ≤ ∫⁻ (x : α), ↑(↑g₁ x) ∂μ + ∫⁻ (x : α), ↑(↑g₂ …
      rw [← lintegral_add_left g₁.measurable.coe_nnreal_ennreal]
      -- ⊢ ∫⁻ (x : α), ↑(↑(g₁ + g₂) x) ∂μ ≤ ∫⁻ (a : α), ↑(↑g₁ a) + ↑(↑g₂ a) ∂μ
      exact le_rfl
      -- 🎉 no goals
    · apply hL.trans ((ENNReal.add_lt_add hg₁ hg₂).trans_le _)
      -- ⊢ ∫⁻ (x : α), ↑(↑g₁ x) ∂μ + ∫⁻ (x : α), ↑(↑g₂ x) ∂μ ≤ ∫⁻ (x : α), ↑(↑(g₁ + g₂) …
      rw [← lintegral_add_left g₁.measurable.coe_nnreal_ennreal]
      -- ⊢ ∫⁻ (a : α), ↑(↑g₁ a) + ↑(↑g₂ a) ∂μ ≤ ∫⁻ (x : α), ↑(↑(g₁ + g₂) x) ∂μ
      exact le_rfl
      -- 🎉 no goals
#align measure_theory.simple_func.exists_lt_lintegral_simple_func_of_lt_lintegral MeasureTheory.SimpleFunc.exists_lt_lintegral_simpleFunc_of_lt_lintegral

theorem exists_lt_lintegral_simpleFunc_of_lt_lintegral {m : MeasurableSpace α} {μ : Measure α}
    [SigmaFinite μ] {f : α → ℝ≥0} {L : ℝ≥0∞} (hL : L < ∫⁻ x, f x ∂μ) :
    ∃ g : α →ₛ ℝ≥0, (∀ x, g x ≤ f x) ∧ ∫⁻ x, g x ∂μ < ∞ ∧ L < ∫⁻ x, g x ∂μ := by
  simp_rw [lintegral_eq_nnreal, lt_iSup_iff] at hL
  -- ⊢ ∃ g, (∀ (x : α), ↑g x ≤ f x) ∧ ∫⁻ (x : α), ↑(↑g x) ∂μ < ⊤ ∧ L < ∫⁻ (x : α),  …
  rcases hL with ⟨g₀, hg₀, g₀L⟩
  -- ⊢ ∃ g, (∀ (x : α), ↑g x ≤ f x) ∧ ∫⁻ (x : α), ↑(↑g x) ∂μ < ⊤ ∧ L < ∫⁻ (x : α),  …
  have h'L : L < ∫⁻ x, g₀ x ∂μ := by
    convert g₀L
    rw [← SimpleFunc.lintegral_eq_lintegral]
    rfl
  rcases SimpleFunc.exists_lt_lintegral_simpleFunc_of_lt_lintegral h'L with ⟨g, hg, gL, gtop⟩
  -- ⊢ ∃ g, (∀ (x : α), ↑g x ≤ f x) ∧ ∫⁻ (x : α), ↑(↑g x) ∂μ < ⊤ ∧ L < ∫⁻ (x : α),  …
  exact ⟨g, fun x => (hg x).trans (coe_le_coe.1 (hg₀ x)), gL, gtop⟩
  -- 🎉 no goals
#align measure_theory.exists_lt_lintegral_simple_func_of_lt_lintegral MeasureTheory.exists_lt_lintegral_simpleFunc_of_lt_lintegral

/-- A sigma-finite measure is absolutely continuous with respect to some finite measure. -/
theorem exists_absolutelyContinuous_isFiniteMeasure {m : MeasurableSpace α} (μ : Measure α)
    [SigmaFinite μ] : ∃ ν : Measure α, IsFiniteMeasure ν ∧ μ ≪ ν := by
  obtain ⟨g, gpos, gmeas, hg⟩ :
    ∃ g : α → ℝ≥0, (∀ x : α, 0 < g x) ∧ Measurable g ∧ ∫⁻ x : α, ↑(g x) ∂μ < 1 :=
    exists_pos_lintegral_lt_of_sigmaFinite μ one_ne_zero
  refine' ⟨μ.withDensity fun x => g x, isFiniteMeasure_withDensity hg.ne_top, _⟩
  -- ⊢ μ ≪ Measure.withDensity μ fun x => ↑(g x)
  have : μ = (μ.withDensity fun x => g x).withDensity fun x => (g x)⁻¹ := by
    have A : ((fun x : α => (g x : ℝ≥0∞)) * fun x : α => (g x : ℝ≥0∞)⁻¹) = 1 := by
      ext1 x
      exact ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.2 (gpos x).ne') ENNReal.coe_ne_top
    rw [← withDensity_mul _ gmeas.coe_nnreal_ennreal gmeas.coe_nnreal_ennreal.inv, A,
      withDensity_one]
  nth_rw 1 [this]
  -- ⊢ (Measure.withDensity (Measure.withDensity μ fun x => ↑(g x)) fun x => (↑(g x …
  exact withDensity_absolutelyContinuous _ _
  -- 🎉 no goals
#align measure_theory.exists_absolutely_continuous_is_finite_measure MeasureTheory.exists_absolutelyContinuous_isFiniteMeasure

end SigmaFinite

section TendstoIndicator

variable {α : Type _} [MeasurableSpace α] {A : Set α}
variable {ι : Type _} (L : Filter ι) [IsCountablyGenerated L] {As : ι → Set α}

/-- If the indicators of measurable sets `Aᵢ` tend pointwise almost everywhere to the indicator
of a measurable set `A` and we eventually have `Aᵢ ⊆ B` for some set `B` of finite measure, then
the measures of `Aᵢ` tend to the measure of `A`. -/
lemma tendsto_measure_of_ae_tendsto_indicator {μ : Measure α} (A_mble : MeasurableSet A)
    (As_mble : ∀ i, MeasurableSet (As i)) {B : Set α} (B_mble : MeasurableSet B)
    (B_finmeas : μ B ≠ ∞) (As_le_B : ∀ᶠ i in L, As i ⊆ B)
    (h_lim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ (As i).indicator (1 : α → ℝ≥0∞) x)
      L (𝓝 (A.indicator 1 x))) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) := by
  simp_rw [← MeasureTheory.lintegral_indicator_one A_mble,
           ← MeasureTheory.lintegral_indicator_one (As_mble _)]
  refine tendsto_lintegral_filter_of_dominated_convergence (B.indicator (1 : α → ℝ≥0∞))
          (eventually_of_forall ?_) ?_ ?_ h_lim
  · exact fun i ↦ Measurable.indicator measurable_const (As_mble i)
    -- 🎉 no goals
  · filter_upwards [As_le_B] with i hi
    -- ⊢ ∀ᵐ (a : α) ∂μ, indicator (As i) 1 a ≤ indicator B 1 a
    exact eventually_of_forall (fun x ↦ indicator_le_indicator_of_subset hi (by simp) x)
    -- 🎉 no goals
  · rwa [← lintegral_indicator_one B_mble] at B_finmeas
    -- 🎉 no goals

/-- If `μ` is a finite measure and the indicators of measurable sets `Aᵢ` tend pointwise
almost everywhere to the indicator of a measurable set `A`, then the measures `μ Aᵢ` tend to
the measure `μ A`. -/
lemma tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure [IsCountablyGenerated L]
    {μ : Measure α} [IsFiniteMeasure μ] (A_mble : MeasurableSet A)
    (As_mble : ∀ i, MeasurableSet (As i))
    (h_lim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ (As i).indicator (1 : α → ℝ≥0∞) x)
      L (𝓝 (A.indicator 1 x))) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) :=
  tendsto_measure_of_ae_tendsto_indicator L A_mble As_mble MeasurableSet.univ
    (measure_ne_top μ univ) (eventually_of_forall (fun i ↦ subset_univ (As i))) h_lim

/-- If the indicators of measurable sets `Aᵢ` tend pointwise to the indicator of a set `A`
and we eventually have `Aᵢ ⊆ B` for some set `B` of finite measure, then the measures of `Aᵢ`
tend to the measure of `A`. -/
lemma tendsto_measure_of_tendsto_indicator [NeBot L] {μ : Measure α}
    (As_mble : ∀ i, MeasurableSet (As i)) {B : Set α} (B_mble : MeasurableSet B)
    (B_finmeas : μ B ≠ ∞) (As_le_B : ∀ᶠ i in L, As i ⊆ B)
    (h_lim : Tendsto (fun i ↦ (As i).indicator (1 : α → ℝ≥0∞)) L (𝓝 (A.indicator 1))) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) := by
  apply tendsto_measure_of_ae_tendsto_indicator L ?_ As_mble B_mble B_finmeas As_le_B
  -- ⊢ ∀ᵐ (x : α) ∂μ, Tendsto (fun i => indicator (As i) 1 x) L (𝓝 (indicator A 1 x))
  · exact eventually_of_forall (by simpa only [tendsto_pi_nhds] using h_lim)
    -- 🎉 no goals
  · exact measurableSet_of_tendsto_indicator L As_mble h_lim
    -- 🎉 no goals

/-- If `μ` is a finite measure and the indicators of measurable sets `Aᵢ` tend pointwise to
the indicator of a set `A`, then the measures `μ Aᵢ` tend to the measure `μ A`. -/
lemma tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure [NeBot L]
    (μ : Measure α) [IsFiniteMeasure μ] (As_mble : ∀ i, MeasurableSet (As i))
    (h_lim : Tendsto (fun i ↦ (As i).indicator (1 : α → ℝ≥0∞)) L (𝓝 (A.indicator 1))) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) := by
  apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure L ?_ As_mble
  -- ⊢ ∀ᵐ (x : α) ∂μ, Tendsto (fun i => indicator (As i) 1 x) L (𝓝 (indicator A 1 x))
  · exact eventually_of_forall (by simpa only [tendsto_pi_nhds] using h_lim)
    -- 🎉 no goals
  · exact measurableSet_of_tendsto_indicator L As_mble h_lim
    -- 🎉 no goals

end TendstoIndicator -- section

end MeasureTheory
