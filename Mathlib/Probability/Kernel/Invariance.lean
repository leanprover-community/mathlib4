/-
Copyright (c) 2023 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Matteo Cipollina
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Invariance of measures along a kernel

We say that a measure `μ` is invariant with respect to a kernel `κ` if its push-forward along the
kernel `μ.bind κ` is the same measure.

## Main definitions

* `ProbabilityTheory.Kernel.Invariant`: invariance of a given measure with respect to a kernel.

-/

@[expose] public section


open MeasureTheory

open scoped MeasureTheory ENNReal ProbabilityTheory

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α}

namespace Kernel

/-! ### Invariant measures of kernels -/

/-- A measure `μ` is invariant with respect to the kernel `κ` if the push-forward measure of `μ`
along `κ` equals `μ`. -/
def Invariant (κ : Kernel α α) (μ : Measure α) : Prop :=
  μ.bind κ = μ

variable {κ η : Kernel α α} {μ : Measure α}

theorem Invariant.def (hκ : Invariant κ μ) : μ.bind κ = μ :=
  hκ

nonrec theorem Invariant.comp_const (hκ : Invariant κ μ) : κ ∘ₖ const α μ = const α μ := by
  rw [comp_const κ μ, hκ.def]

theorem Invariant.comp (hκ : Invariant κ μ) (hη : Invariant η μ) :
    Invariant (κ ∘ₖ η) μ := by
  rw [Invariant, ← Measure.comp_assoc, hη, hκ]

theorem Invariant.pow (h : Invariant κ μ) (n : ℕ) : Invariant (κ ^ n) μ := by
  induction n with
  | zero => simp [Invariant]
  | succ n ih => rw [pow_succ, mul_eq_comp]; exact ih.comp h

theorem Invariant.smul (h : Invariant κ μ) (c : ℝ≥0∞) : Invariant κ (c • μ) := by
  rw [Invariant, Measure.comp_smul, h.def]

/-- If `μ` is invariant for `κ` and a property holds `μ`-almost everywhere, then for `μ`-almost
every `a` it holds `(κ ^ n) a`-almost everywhere for all `n`. -/
theorem Invariant.ae_ae_pow (h : Invariant κ μ) {p : α → Prop} (hp : ∀ᵐ a ∂μ, p a) :
    ∀ᵐ a ∂μ, ∀ n, ∀ᵐ b ∂(κ ^ n) a, p b := by
  rw [ae_all_iff]
  intro n
  rw [← (h.pow n).def] at hp
  exact Measure.ae_ae_of_ae_comp hp

section Absorbing

variable {π : Measure α} {G : Set α}

/-- If a measurable set `G` is absorbing almost everywhere with respect to an invariant measure
`π`, then for `π`-almost every point of `G`, no power of `κ` charges `Gᶜ`. -/
theorem Invariant.ae_pow_apply_compl_eq_zero (hπ : Invariant κ π) (hG : MeasurableSet G)
    (h : ∀ᵐ x ∂π, x ∈ G → κ x Gᶜ = 0) :
    ∀ᵐ x ∂π, x ∈ G → ∀ n, (κ ^ n) x Gᶜ = 0 := by
  suffices ∀ n, ∀ᵐ x ∂π, x ∈ G → (κ ^ n) x Gᶜ = 0 by
    filter_upwards [ae_all_iff.mpr this] with x hx hxG n using hx n hxG
  intro n
  induction n with
  | zero => simp [Kernel.id_apply, Measure.dirac_apply' _ hG.compl]
  | succ n ih =>
    have h1 : ∀ᵐ x ∂π, ∀ᵐ y ∂κ x, y ∈ G → (κ ^ n) y Gᶜ = 0 := by
      rw [← hπ.def] at ih
      exact Measure.ae_ae_of_ae_comp ih
    filter_upwards [h, h1] with x hx hx1 hxG
    suffices (fun a ↦ (κ ^ n) a Gᶜ) =ᵐ[κ x] 0 by
      rwa [pow_add_one, comp_apply, Measure.bind_apply hG.compl (κ ^ n).aemeasurable,
        lintegral_eq_zero_iff ((κ ^ n).measurable_coe hG.compl)]
    have hxG' : ∀ᵐ y ∂κ x, y ∈ G := by
      simpa using measure_eq_zero_iff_ae_notMem.mp (hx hxG)
    filter_upwards [hx1, hxG'] with y hy hyG using hy hyG

/-- If a measurable set `G` of finite measure is absorbing almost everywhere with respect to an
invariant measure of a Markov kernel, then so is its complement. -/
theorem Invariant.ae_apply_eq_zero_of_compl [IsMarkovKernel κ] (hπ : Invariant κ π)
    (hG : MeasurableSet G) (hπG : π G ≠ ∞) (h : ∀ᵐ x ∂π, x ∈ G → κ x Gᶜ = 0) :
    ∀ᵐ x ∂π, x ∈ Gᶜ → κ x G = 0 := by
  have h1 : ∫⁻ x, κ x G ∂π = π G := by
    rw [← Measure.bind_apply hG κ.aemeasurable, hπ.def]
  have h2 : ∫⁻ x in G, κ x G ∂π = π G := by
    rw [← setLIntegral_one]
    refine setLIntegral_congr_fun_ae hG ?_
    filter_upwards [h] with x hx hxG using (prob_compl_eq_zero_iff hG).mp (hx hxG)
  have h3 : ∫⁻ x in Gᶜ, κ x G ∂π = 0 := by
    have h_add := lintegral_add_compl (μ := π) (fun x ↦ κ x G) hG
    rw [h1, h2] at h_add
    exact (ENNReal.add_right_inj hπG).mp (by rw [h_add, add_zero])
  rwa [setLIntegral_eq_zero_iff hG.compl (κ.measurable_coe hG)] at h3

end Absorbing

/-! ### Reversibility of kernels -/

/-- Reversibility (detailed balance) of a Markov kernel `κ` w.r.t. a measure `π`:
for all measurable sets `A B`, the mass flowing from `A` to `B` equals that from `B` to `A`. -/
def IsReversible (κ : Kernel α α) (π : Measure α) : Prop :=
  ∀ ⦃A B⦄, MeasurableSet A → MeasurableSet B →
    ∫⁻ x in A, κ x B ∂π = ∫⁻ x in B, κ x A ∂π

/-- A reversible Markov kernel leaves the measure `π` invariant. -/
theorem IsReversible.invariant
    {κ : Kernel α α} [IsMarkovKernel κ] {π : Measure α}
    (h_rev : IsReversible κ π) : Invariant κ π := by
  ext s hs
  calc
    (κ ∘ₘ π) s = ∫⁻ x, κ x s ∂π := by rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
             _ = ∫⁻ x in s, κ x Set.univ ∂π := by simpa [restrict_univ] using (h_rev hs .univ).symm
             _ = π s := by simp

end Kernel

end ProbabilityTheory
