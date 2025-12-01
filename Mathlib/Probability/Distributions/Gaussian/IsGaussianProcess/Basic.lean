/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def

import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Independence.Process
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Gaussian processes

-/

public section

open MeasureTheory InnerProductSpace Finset

open scoped ENNReal NNReal RealInnerProductSpace

namespace ProbabilityTheory.IsGaussianProcess

variable {S T Ω E F : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : T → Ω → E}

section Basic

variable [MeasurableSpace E] [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]

lemma isProbabilityMeasure (hX : IsGaussianProcess X P) :
    IsProbabilityMeasure P :=
  hX.hasGaussianLaw Classical.ofNonempty |>.isProbabilityMeasure

lemma aemeasurable (hX : IsGaussianProcess X P) (t : T) : AEMeasurable (X t) P :=
  AEMeasurable.of_map_ne_zero
    (hX.hasGaussianLaw {t}).isGaussian_map.toIsProbabilityMeasure.ne_zero |>.eval ⟨t, by simp⟩

/-- A modification of a Gaussian process is a Gaussian Process -/
lemma congr (hX : IsGaussianProcess X P) (hXY : ∀ t, X t =ᵐ[P] Y t) :
    IsGaussianProcess Y P where
  hasGaussianLaw I := by
    constructor
    rw [map_restrict_eq_of_forall_ae_eq fun t ↦ (hXY t).symm]
    exact (hX.hasGaussianLaw I).isGaussian_map

end Basic

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

section Maps

lemma hasGaussianLaw_eval (hX : IsGaussianProcess X P) (t : T) : HasGaussianLaw (X t) P := by
  have : X t = (ContinuousLinearMap.proj (R := ℝ) ⟨t, by simp⟩) ∘
    (fun ω ↦ ({t} : Finset T).restrict (X · ω)) := by ext; simp
  rw [this]
  exact (hX.hasGaussianLaw {t}).map (.proj ⟨t, by simp⟩)

variable [SecondCountableTopology E]

lemma hasGaussianLaw_prodMk (hX : IsGaussianProcess X P)
    {s t : T} : HasGaussianLaw (fun ω ↦ (X s ω, X t ω)) P := by
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

section Independence

variable [SecondCountableTopology E] [CompleteSpace E] {X : S → Ω → E}

lemma indepFun {X : S → Ω → E} {Y : T → Ω → E} (hXY : IsGaussianProcess (Sum.elim X Y) P)
    (hX : ∀ s, Measurable (X s)) (hY : ∀ t, Measurable (Y t))
    (h : ∀ s t (L₁ L₂ : StrongDual ℝ E), cov[L₁ ∘ X s, L₂ ∘ Y t; P] = 0) :
    IndepFun (fun ω s ↦ X s ω) (fun ω t ↦ Y t ω) P := by
  have := hXY.isProbabilityMeasure
  refine IndepFun.process_indepFun_process hX hY fun I J ↦
    HasGaussianLaw.indepFun_of_covariance_strongDual ?_ fun L₁ L₂ ↦ ?_
  · let L : (I.disjSum J → E) →L[ℝ] (I → E) × (J → E) :=
      { toFun x := (fun s ↦ x ⟨Sum.inl s, inl_mem_disjSum.2 s.2⟩,
          fun t ↦ x ⟨Sum.inr t, inr_mem_disjSum.2 t.2⟩)
        map_add' x y := by ext <;> simp
        map_smul' c x := by ext <;> simp }
    exact (hXY.hasGaussianLaw _).map L
  classical
  have h1 : L₁ ∘ (fun ω i ↦ X i ω) = ∑ i : I, (L₁ ∘L .single ℝ _ i) ∘ X i := by
    ext; simp [-ContinuousLinearMap.coe_comp', ← L₁.sum_comp_single]
  have h2 : L₂ ∘ (fun ω j ↦ Y j ω) = ∑ j : J, (L₂ ∘L .single ℝ _ j) ∘ Y j := by
    ext; simp [-ContinuousLinearMap.coe_comp', ← L₂.sum_comp_single]
  rw [h1, h2, covariance_sum_sum]
  · exact sum_eq_zero fun i _ ↦ sum_eq_zero fun j _ ↦ h ..
  · exact fun s ↦ ((hXY.hasGaussianLaw_eval (.inl s)).map _).memLp_two
  · exact fun t ↦ ((hXY.hasGaussianLaw_eval (.inr t)).map _).memLp_two

lemma iIndepFun {S : T → Type*} {X : (t : T) → (s : S t) → Ω → E}
    (hX : IsGaussianProcess (fun (p : (t : T) × S t) ω ↦ X p.1 p.2 ω) P)
    (mX : ∀ t s, Measurable (X t s))
    (h : ∀ t₁ t₂, t₁ ≠ t₂ → ∀ (s₁ : S t₁) (s₂ : S t₂) (L₁ L₂ : StrongDual ℝ E),
      cov[L₁ ∘ X t₁ s₁, L₂ ∘ X t₂ s₂; P] = 0) :
    iIndepFun (fun t ω s ↦ X t s ω) P := by
  have := hX.isProbabilityMeasure
  refine iIndepFun.iIndepFun_process mX fun I J ↦
    HasGaussianLaw.iIndepFun_of_covariance_strongDual ?_ fun i j hij L₁ L₂ ↦ ?_
  · classical
    let L : (I.sigma (fun i ↦ if hi : i ∈ I then J ⟨i, hi⟩ else ∅) → E) →L[ℝ] (i : I) → J i → E :=
      { toFun x i j := x ⟨⟨i, j⟩, by simp⟩
        map_add' x y := by ext; simp
        map_smul' c x := by ext; simp
        cont := by fun_prop }
    exact (hX.hasGaussianLaw _).map L
  classical
  have h1 : L₁ ∘ (fun ω k ↦ X i k ω) = ∑ k : J i, (L₁ ∘L .single ℝ _ k) ∘ X i k := by
    ext; simp [-ContinuousLinearMap.coe_comp', ← L₁.sum_comp_single]
  have h2 : L₂ ∘ (fun ω k ↦ X j k ω) = ∑ k : J j, (L₂ ∘L .single ℝ _ k) ∘ X j k := by
    ext; simp [-ContinuousLinearMap.coe_comp', ← L₂.sum_comp_single]
  rw [h1, h2, covariance_sum_sum]
  · exact sum_eq_zero fun _ _ ↦ sum_eq_zero fun _ _ ↦ h i j (by simpa) ..
  · exact fun k ↦ ((hX.hasGaussianLaw_eval ⟨i, k⟩).map _).memLp_two
  · exact fun k ↦ ((hX.hasGaussianLaw_eval ⟨j, k⟩).map _).memLp_two

lemma indepFun'
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E]
    {X : S → Ω → E} {Y : T → Ω → E}
    (h : IsGaussianProcess (Sum.elim X Y) P) (hX : ∀ s, Measurable (X s))
    (hY : ∀ t, Measurable (Y t))
    (h' : ∀ s t x y, cov[fun ω ↦ ⟪x, X s ω⟫, fun ω ↦ ⟪y, Y t ω⟫; P] = 0) :
    IndepFun (fun ω s ↦ X s ω) (fun ω t ↦ Y t ω) P :=
  h.indepFun hX hY fun s t L₁ L₂ ↦ by
    simpa using h' s t ((toDual ℝ E).symm L₁) ((toDual ℝ E).symm L₂)

lemma iIndepFun'
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E] {S : T → Type*}
    {X : (t : T) → (s : S t) → Ω → E}
    (h : IsGaussianProcess (fun (p : (t : T) × S t) ω ↦ X p.1 p.2 ω) P)
    (hX : ∀ t s, Measurable (X t s))
    (h' : ∀ t₁ t₂, t₁ ≠ t₂ → ∀ (s₁ : S t₁) (s₂ : S t₂) (x y : E),
      cov[fun ω ↦ ⟪x, X t₁ s₁ ω⟫, fun ω ↦ ⟪y, X t₂ s₂ ω⟫; P] = 0) :
    ProbabilityTheory.iIndepFun (fun t ω s ↦ X t s ω) P :=
  h.iIndepFun hX fun t₁ t₂ ht s₁ s₂ L₁ L₂ ↦ by
    simpa using h' t₁ t₂ ht s₁ s₂ ((toDual ℝ E).symm L₁) ((toDual ℝ E).symm L₂)

lemma indepFun'' {X : S → Ω → ℝ} {Y : T → Ω → ℝ}
    (h : IsGaussianProcess (Sum.elim X Y) P) (hX : ∀ s, Measurable (X s))
    (hY : ∀ t, Measurable (Y t)) (h' : ∀ s t, cov[X s, Y t; P] = 0) :
    IndepFun (fun ω s ↦ X s ω) (fun ω t ↦ Y t ω) P :=
  h.indepFun' hX hY fun _ _ _ _ ↦ by
    simp [mul_comm, covariance_const_mul_left, covariance_const_mul_right, h']

lemma iIndepFun'' {S : T → Type*}
    {X : (t : T) → (s : S t) → Ω → ℝ}
    (h : IsGaussianProcess (fun (p : (t : T) × S t) ω ↦ X p.1 p.2 ω) P)
    (hX : ∀ t s, Measurable (X t s))
    (h' : ∀ t₁ t₂, t₁ ≠ t₂ → ∀ (s₁ : S t₁) (s₂ : S t₂), cov[X t₁ s₁, X t₂ s₂; P] = 0) :
    ProbabilityTheory.iIndepFun (fun t ω s ↦ X t s ω) P :=
  h.iIndepFun' hX fun _ _ h'' _ _ _ _ ↦ by
    simp [mul_comm, covariance_const_mul_left, covariance_const_mul_right, h' _ _ h'']

end Independence

variable [SecondCountableTopology E]

/-- If a stochastic process `Y` is such that for `s`, `Y s` can be written as a linear
combination of finitely many values of a Gaussian process, then `Y` is a Gaussian process. -/
lemma of_isGaussianProcess (hX : IsGaussianProcess X P)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
    [BorelSpace F] [SecondCountableTopology F] {Y : S → Ω → F}
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
      ext; simp [K, hL]; rfl
    rw [this]
    exact (hX.hasGaussianLaw _).map _

lemma comp_right (h : IsGaussianProcess X P)
    (f : S → T) : IsGaussianProcess (X ∘ f) P :=
  h.of_isGaussianProcess fun s ↦ ⟨{f s},
    { toFun x := x ⟨f s, by simp⟩
      map_add' := by simp
      map_smul' := by simp },
    by simp⟩

lemma comp_left {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] (L : T → E →L[ℝ] F) (h : IsGaussianProcess X P) :
    IsGaussianProcess (fun t ω ↦ L t (X t ω)) P :=
  h.of_isGaussianProcess fun t ↦ ⟨{t},
    { toFun x := L t (x ⟨t, by simp⟩),
      map_add' := by simp
      map_smul' := by simp },
    by simp⟩

lemma smul (c : T → ℝ)
    (hX : IsGaussianProcess X P) :
    IsGaussianProcess (fun t ω ↦ c t • (X t ω)) P :=
  letI L t : E →L[ℝ] E :=
    { toFun x := c t • x
      map_add' := by simp
      map_smul' := by simp [smul_smul, mul_comm]
      cont := by fun_prop }
  hX.comp_left L

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
  h.of_isGaussianProcess fun t ↦ ⟨{t.1},
    { toFun x := x ⟨t.1, by simp⟩
      map_add' := by simp
      map_smul' := by simp },
    by simp⟩

end ProbabilityTheory.IsGaussianProcess
