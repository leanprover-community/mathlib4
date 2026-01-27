/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def

import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Gaussian processes

This file contains basic properties of Gaussian processes. In particular,
in `IsGaussianProcess.of_isGaussianProcess`, we show that if a stochastic
process `Y : S → Ω → F` is such that for each `s : S`, `Y s` can be written as a linear map
applied to finitely many values of a certain Gaussian process,
then `Y` is itself a Gaussian process.

## Main statement

* `IsGaussianProcess.of_isGaussianProcess`: If a stochastic process `Y : S → Ω → F` is such that
  for each `s : S`, `Y s` can be written as a linear map applied to finitely many values
  of a certain Gaussian process, then `Y` is itself a Gaussian process.

## Tags

Gaussian process
-/

public section

open MeasureTheory Finset

namespace ProbabilityTheory.IsGaussianProcess

variable {S T Ω E F : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : T → Ω → E}

section Basic

/-! ### Basic facts -/

variable [MeasurableSpace E] [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]

lemma isProbabilityMeasure (hX : IsGaussianProcess X P) :
    IsProbabilityMeasure P :=
  hX.hasGaussianLaw Classical.ofNonempty |>.isProbabilityMeasure

lemma aemeasurable (hX : IsGaussianProcess X P) (t : T) : AEMeasurable (X t) P :=
  AEMeasurable.of_map_ne_zero
    (hX.hasGaussianLaw {t}).isGaussian_map.toIsProbabilityMeasure.ne_zero |>.eval ⟨t, by simp⟩

/-- A modification of a Gaussian process is a Gaussian process. -/
lemma congr (hX : IsGaussianProcess X P) (hXY : ∀ t, X t =ᵐ[P] Y t) :
    IsGaussianProcess Y P where
  hasGaussianLaw I := by
    constructor
    rw [map_restrict_eq_of_forall_ae_eq fun t ↦ (hXY t).symm]
    exact (hX.hasGaussianLaw I).isGaussian_map

end Basic

variable [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

section Maps

/-! ### Gaussian Marginals -/

variable [NormedSpace ℝ E]

lemma hasGaussianLaw_eval (hX : IsGaussianProcess X P) (t : T) : HasGaussianLaw (X t) P := by
  -- removing `by exact` fails
  exact (hX.hasGaussianLaw {t}).map (.proj ⟨t, by simp⟩)

variable [SecondCountableTopology E]

lemma hasGaussianLaw_prodMk (hX : IsGaussianProcess X P) {s t : T} :
    HasGaussianLaw (fun ω ↦ (X s ω, X t ω)) P := by
  classical
  exact (hX.hasGaussianLaw {s, t}).prodMk ⟨s, by simp⟩ ⟨t, by simp⟩

lemma hasGaussianLaw_add (hX : IsGaussianProcess X P) {s t : T} :
    HasGaussianLaw (X s + X t) P := hX.hasGaussianLaw_prodMk.add

lemma hasGaussianLaw_fun_add (hX : IsGaussianProcess X P) {s t : T} :
    HasGaussianLaw (fun ω ↦ X s ω + X t ω) P := hX.hasGaussianLaw_add

lemma hasGaussianLaw_sub (hX : IsGaussianProcess X P) {s t : T} :
    HasGaussianLaw (X s - X t) P := hX.hasGaussianLaw_prodMk.sub

lemma hasGaussianLaw_fun_sub (hX : IsGaussianProcess X P) {s t : T} :
    HasGaussianLaw (fun ω ↦ X s ω - X t ω) P := hX.hasGaussianLaw_sub

lemma hasGaussianLaw_sum (hX : IsGaussianProcess X P) {I : Finset T} :
    HasGaussianLaw (∑ i ∈ I, X i) P := by
  convert (hX.hasGaussianLaw I).sum
  simp [I.sum_attach X]

lemma hasGaussianLaw_fun_sum (hX : IsGaussianProcess X P) {I : Finset T} :
    HasGaussianLaw (fun ω ↦ ∑ i ∈ I, X i ω) P := by
  convert hX.hasGaussianLaw_sum (I := I)
  simp

/-- The increments of a Gaussian process are Gaussian. -/
lemma hasGaussianLaw_increments (hX : IsGaussianProcess X P) {n : ℕ} {t : Fin (n + 1) → T} :
    HasGaussianLaw (fun ω (i : Fin n) ↦ X (t i.succ) ω - X (t i.castSucc) ω) P := by
  classical
  let L : ((univ.image t) → E) →L[ℝ] Fin n → E :=
    { toFun x i := x ⟨t i.succ, by simp⟩ - x ⟨t i.castSucc, by simp⟩
      map_add' x y := by ext; simp; abel
      map_smul' m x := by ext; simp; module
      cont := by fun_prop }
  exact (hX.hasGaussianLaw _).map L

end Maps

section Transformations

/-! ### Operations that preserve Gaussianity -/

variable [NormedSpace ℝ E] [SecondCountableTopology E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
  [BorelSpace F] [SecondCountableTopology F] {Y : S → Ω → F}

/-- If a stochastic process `Y` is such that for each `s`, `Y s` can be written as a linear
combination of finitely many values of a Gaussian process, then `Y` is a Gaussian process. -/
lemma of_isGaussianProcess (hX : IsGaussianProcess X P)
    (h : ∀ s, ∃ I : Finset T, ∃ L : (I → E) →L[ℝ] F, ∀ ω, Y s ω = L (I.restrict (X · ω))) :
    IsGaussianProcess Y P where
  hasGaussianLaw I := by
    choose J L hL using h
    classical
    let K : (I.biUnion J → E) →L[ℝ] I → F :=
      { toFun x s := L s (fun t ↦ x ⟨t.1, mem_biUnion.2 ⟨s.1, s.2, t.2⟩⟩)
        map_add' x y := by ext; simp [← Pi.add_def]
        map_smul' c x := by ext; simp [← Pi.smul_def]
        cont := by fun_prop }
    have : (fun ω ↦ I.restrict (Y · ω)) = K ∘ (fun ω ↦ (I.biUnion J).restrict (X · ω)) := by
      ext; simp [K, hL, Finset.restrict_def]
    rw [this]
    exact (hX.hasGaussianLaw _).map _

lemma comp_right (h : IsGaussianProcess X P) (f : S → T) : IsGaussianProcess (X ∘ f) P :=
  h.of_isGaussianProcess fun s ↦ ⟨{f s},
    { toFun x := x ⟨f s, by simp⟩
      map_add' := by simp
      map_smul' := by simp },
    by simp⟩

lemma comp_left (L : T → E →L[ℝ] F) (h : IsGaussianProcess X P) :
    IsGaussianProcess (fun t ω ↦ L t (X t ω)) P :=
  h.of_isGaussianProcess fun t ↦ ⟨{t},
    { toFun x := L t (x ⟨t, by simp⟩),
      map_add' := by simp
      map_smul' := by simp },
    by simp⟩

lemma smul (c : T → ℝ) (hX : IsGaussianProcess X P) :
    IsGaussianProcess (fun t ω ↦ c t • (X t ω)) P :=
  hX.comp_left (fun t ↦ .lsmul ℝ ℝ (c t))

lemma shift [Add T] (h : IsGaussianProcess X P) (t₀ : T) :
    IsGaussianProcess (fun t ω ↦ X (t₀ + t) ω - X t₀ ω) P := by
  classical
  exact h.of_isGaussianProcess fun t ↦ ⟨{t₀, t₀ + t},
    { toFun x := x ⟨t₀ + t, by simp⟩ - x ⟨t₀, by simp⟩
      map_add' x y := by simp; abel
      map_smul' c x := by simp; module },
    by simp⟩

lemma restrict (h : IsGaussianProcess X P) (s : Set T) :
    IsGaussianProcess (fun t : s ↦ X t) P :=
  h.comp_right Subtype.val

end Transformations

end ProbabilityTheory.IsGaussianProcess
