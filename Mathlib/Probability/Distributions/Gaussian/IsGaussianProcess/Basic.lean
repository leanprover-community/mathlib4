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

open MeasureTheory InnerProductSpace

open scoped ENNReal NNReal RealInnerProductSpace

namespace ProbabilityTheory

variable {S T Ω E F : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : T → Ω → E}

section Basic

variable [MeasurableSpace E] [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]

lemma IsGaussianProcess.isProbabilityMeasure (hX : IsGaussianProcess X P) :
    IsProbabilityMeasure P :=
  hX.hasGaussianLaw Classical.ofNonempty |>.isProbabilityMeasure

lemma IsGaussianProcess.aemeasurable (hX : IsGaussianProcess X P) (t : T) :
    AEMeasurable (X t) P := by
  by_contra h
  have := (hX.hasGaussianLaw {t}).isGaussian_map
  rw [Measure.map_of_not_aemeasurable] at this
  · exact this.toIsProbabilityMeasure.ne_zero _ rfl
  · rw [aemeasurable_pi_iff]
    push_neg
    exact ⟨⟨t, by simp⟩, h⟩

lemma IsGaussianProcess.modification (hX : IsGaussianProcess X P) (hXY : ∀ t, X t =ᵐ[P] Y t) :
    IsGaussianProcess Y P where
  hasGaussianLaw I := by
    constructor
    rw [map_restrict_eq_of_forall_ae_eq fun t ↦ (hXY t).symm]
    exact (hX.hasGaussianLaw I).isGaussian_map

end Basic

lemma borelSpace_of_isOpen {X : Type*} [TopologicalSpace X] [m : MeasurableSpace X]
    (h : ∀ s : Set X, IsOpen s → MeasurableSet s) : borel X ≤ m :=
  MeasurableSpace.generateFrom_le h

lemma nonempty_of_nontrivial_pi {ι : Type*} (α : ι → Type*) [h : Nontrivial (Π i, α i)] :
    Nonempty ι := by
  contrapose! h
  infer_instance

instance {ι : Type*} (E : ι → Type*) [∀ i, TopologicalSpace (E i)] [∀ i, MeasurableSpace (E i)]
    [∀ i, BorelSpace (E i)] [Subsingleton ι] :
    BorelSpace (Π i, E i) := by
  nontriviality (Π i, E i)
  have := nonempty_of_nontrivial_pi E
  have := Classical.choice (nonempty_unique ι)
  refine ⟨le_antisymm pi_le_borel_pi (borelSpace_of_isOpen fun s hs ↦ ?_)⟩
  simp only [Pi.topologicalSpace, ciInf_unique, isOpen_induced_eq, Set.mem_image,
    Set.mem_setOf_eq] at hs
  rw [MeasurableSpace.pi, ciSup_unique, MeasurableSpace.measurableSet_comap]
  exact ⟨(fun (b : Π i, E i) ↦ b default) ⁻¹' s, hs.measurableSet, rfl⟩

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

instance {ι : Type*} (E : ι → Type*) [∀ i, TopologicalSpace (E i)] [∀ i, MeasurableSpace (E i)]
    [∀ i, BorelSpace (E i)] [Subsingleton ι] :
    BorelSpace (Π i, E i) := by
  refine ⟨le_antisymm pi_le_borel_pi ?_⟩
  obtain h | h := isEmpty_or_nonempty ι
  · exact fun s _ ↦ Subsingleton.set_cases .empty .univ s
  have := Classical.choice (nonempty_unique ι)
  rw [borel, MeasurableSpace.pi, ciSup_unique]
  refine MeasurableSpace.generateFrom_le fun s hs ↦ MeasurableSpace.measurableSet_comap.2 ?_
  simp only [Pi.topologicalSpace, ciInf_unique, isOpen_induced_eq, Set.mem_image,
    Set.mem_setOf_eq] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  exact ⟨t, ht.measurableSet, rfl⟩

lemma IsGaussianProcess.hasGaussianLaw_eval (hX : IsGaussianProcess X P) (t : T) :
    HasGaussianLaw (X t) P := by
  have : X t = (ContinuousLinearMap.proj (R := ℝ) ⟨t, by simp⟩) ∘
    (fun ω ↦ ({t} : Finset T).restrict (X · ω)) := by ext; simp
  rw [this]
  exact (hX.hasGaussianLaw _).map _

variable [SecondCountableTopology E]

lemma IsGaussianProcess.hasGaussianLaw_sub (hX : IsGaussianProcess X P)
    {s t : T} : HasGaussianLaw (X s - X t) P := by
  classical
  have : X s - X t =
      (ContinuousLinearMap.proj (R := ℝ) (ι := ({s, t} : Finset T))
        (φ := fun _ ↦ E) ⟨s, by simp⟩ -
      ContinuousLinearMap.proj (R := ℝ) (ι := ({s, t} : Finset T))
        (φ := fun _ ↦ E) ⟨t, by simp⟩) ∘
    (fun ω ↦ Finset.restrict {s, t} (X · ω)) := by ext; simp
  rw [this]
  exact (hX.hasGaussianLaw _).map _

lemma IsGaussianProcess.hasGaussianLaw_fun_sub
    (hX : IsGaussianProcess X P) {s t : T} : HasGaussianLaw (fun ω ↦ X s ω - X t ω) P :=
  hX.hasGaussianLaw_sub

lemma IsGaussianProcess.hasGaussianLaw_increments
    (hX : IsGaussianProcess X P) {n : ℕ} {t : Fin (n + 1) → T} :
    HasGaussianLaw (fun ω (i : Fin n) ↦ X (t i.succ) ω - X (t i.castSucc) ω) P := by
  classical
  let L : ((Finset.univ.image t) → E) →L[ℝ] Fin n → E :=
    { toFun x i := x ⟨t i.succ, by simp⟩ - x ⟨t i.castSucc, by simp⟩
      map_add' x y := by ext; simp; abel
      map_smul' m x := by ext; simp; module
      cont := by fun_prop }
  have : (fun ω i ↦ X (t i.succ) ω - X (t i.castSucc) ω) =
      L ∘ fun ω ↦ (Finset.univ.image t).restrict (X · ω) := by ext; simp [L]
  rw [this]
  exact (hX.hasGaussianLaw _).map _

lemma IsGaussianProcess.indepFun [CompleteSpace E] {X : S → Ω → E} {Y : T → Ω → E}
    (h : IsGaussianProcess (Sum.elim X Y) P) (hX : ∀ s, Measurable (X s))
    (hY : ∀ t, Measurable (Y t))
    (h' : ∀ s t (L₁ L₂ : StrongDual ℝ E), cov[L₁ ∘ X s, L₂ ∘ Y t; P] = 0) :
    IndepFun (fun ω s ↦ X s ω) (fun ω t ↦ Y t ω) P := by
  have := h.isProbabilityMeasure
  refine IndepFun.process_indepFun_process hX hY fun I J ↦
    HasGaussianLaw.indepFun_of_covariance_strongDual ?_ fun L₁ L₂ ↦ ?_
  · let L : (I.disjSum J → E) →L[ℝ] (I → E) × (J → E) :=
      { toFun x := (fun s ↦ x ⟨Sum.inl s, Finset.inl_mem_disjSum.2 s.2⟩,
          fun t ↦ x ⟨Sum.inr t, Finset.inr_mem_disjSum.2 t.2⟩)
        map_add' x y := by ext <;> simp
        map_smul' c x := by ext <;> simp }
    have : (fun ω ↦ (fun i : I ↦ X i ω, fun j : J ↦ Y j ω)) =
        L ∘ (fun ω ↦ (I.disjSum J).restrict (Sum.elim X Y · ω)) := by
      ext <;> simp [L]
    rw [this]
    exact (h.hasGaussianLaw _).map _
  classical
  have h1 : L₁ ∘ (fun ω i ↦ X i ω) = ∑ i : I, (L₁ ∘L .single ℝ _ i) ∘ X i := by
    ext ω
    simp only [Function.comp_apply, ← L₁.sum_comp_single, Finset.univ_eq_attach, Finset.sum_apply]
  have h2 : L₂ ∘ (fun ω j ↦ Y j ω) = ∑ j : J, (L₂ ∘L .single ℝ _ j) ∘ Y j := by
    ext ω
    simp only [Function.comp_apply, ← L₂.sum_comp_single, Finset.univ_eq_attach, Finset.sum_apply]
  rw [h1, h2, covariance_sum_sum]
  · exact Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦ h' ..
  · exact fun s ↦ ((h.hasGaussianLaw_eval (.inl s)).map _).memLp_two
  · exact fun t ↦ ((h.hasGaussianLaw_eval (.inr t)).map _).memLp_two

lemma IsGaussianProcess.iIndepFun [CompleteSpace E] {S : T → Type*}
    {X : (t : T) → (s : S t) → Ω → E}
    (h : IsGaussianProcess (fun (p : (t : T) × S t) ω ↦ X p.1 p.2 ω) P)
    (hX : ∀ t s, Measurable (X t s))
    (h' : ∀ t₁ t₂, t₁ ≠ t₂ → ∀ (s₁ : S t₁) (s₂ : S t₂) (L₁ L₂ : StrongDual ℝ E),
      cov[L₁ ∘ X t₁ s₁, L₂ ∘ X t₂ s₂; P] = 0) :
    iIndepFun (fun t ω s ↦ X t s ω) P := by
  have := h.isProbabilityMeasure
  refine iIndepFun.iIndepFun_process hX fun I J ↦
    HasGaussianLaw.iIndepFun_of_covariance_strongDual ?_ fun i j hij L₁ L₂ ↦ ?_
  · classical
    let L : (I.sigma (fun i ↦ if hi : i ∈ I then J ⟨i, hi⟩ else ∅) → E) →L[ℝ] (i : I) → J i → E :=
      { toFun x i j := x ⟨⟨i, j⟩, by simp⟩
        map_add' x y := by ext; simp
        map_smul' c x := by ext; simp
        cont := by fun_prop }
    have : (fun ω (i : I) (j : J i) ↦ X i j ω) =
        L ∘ (fun ω ↦ (I.sigma (fun i ↦ if hi : i ∈ I then J ⟨i, hi⟩ else ∅)).restrict
          (fun p ↦ X p.1 p.2 ω)) := by
      ext; simp [L]
    rw [this]
    exact (h.hasGaussianLaw _).map _
  classical
  have h1 : L₁ ∘ (fun ω k ↦ X i k ω) = ∑ k : J i, (L₁ ∘L .single ℝ _ k) ∘ X i k := by
    ext ω
    simp only [Function.comp_apply, ← L₁.sum_comp_single, Finset.univ_eq_attach, Finset.sum_apply]
  have h2 : L₂ ∘ (fun ω k ↦ X j k ω) = ∑ k : J j, (L₂ ∘L .single ℝ _ k) ∘ X j k := by
    ext ω
    simp only [Function.comp_apply, ← L₂.sum_comp_single, Finset.univ_eq_attach, Finset.sum_apply]
  rw [h1, h2, covariance_sum_sum]
  · exact Finset.sum_eq_zero fun _ _ ↦ Finset.sum_eq_zero fun _ _ ↦ h' i j (by simpa) ..
  · exact fun k ↦ ((h.hasGaussianLaw_eval ⟨i, k⟩).map _).memLp_two
  · exact fun k ↦ ((h.hasGaussianLaw_eval ⟨j, k⟩).map _).memLp_two

lemma IsGaussianProcess.indepFun'
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E]
    {X : S → Ω → E} {Y : T → Ω → E}
    (h : IsGaussianProcess (Sum.elim X Y) P) (hX : ∀ s, Measurable (X s))
    (hY : ∀ t, Measurable (Y t))
    (h' : ∀ s t x y, cov[fun ω ↦ ⟪x, X s ω⟫, fun ω ↦ ⟪y, Y t ω⟫; P] = 0) :
    IndepFun (fun ω s ↦ X s ω) (fun ω t ↦ Y t ω) P :=
  h.indepFun hX hY fun s t L₁ L₂ ↦ by
    simpa using h' s t ((toDual ℝ E).symm L₁) ((toDual ℝ E).symm L₂)

lemma IsGaussianProcess.iIndepFun'
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

lemma IsGaussianProcess.indepFun'' {X : S → Ω → ℝ} {Y : T → Ω → ℝ}
    (h : IsGaussianProcess (Sum.elim X Y) P) (hX : ∀ s, Measurable (X s))
    (hY : ∀ t, Measurable (Y t)) (h' : ∀ s t, cov[X s, Y t; P] = 0) :
    IndepFun (fun ω s ↦ X s ω) (fun ω t ↦ Y t ω) P :=
  h.indepFun' hX hY fun _ _ _ _ ↦ by
    simp [mul_comm, covariance_const_mul_left, covariance_const_mul_right, h']

lemma IsGaussianProcess.iIndepFun'' {S : T → Type*}
    {X : (t : T) → (s : S t) → Ω → ℝ}
    (h : IsGaussianProcess (fun (p : (t : T) × S t) ω ↦ X p.1 p.2 ω) P)
    (hX : ∀ t s, Measurable (X t s))
    (h' : ∀ t₁ t₂, t₁ ≠ t₂ → ∀ (s₁ : S t₁) (s₂ : S t₂), cov[X t₁ s₁, X t₂ s₂; P] = 0) :
    ProbabilityTheory.iIndepFun (fun t ω s ↦ X t s ω) P :=
  h.iIndepFun' hX fun _ _ h'' _ _ _ _ ↦ by
    simp [mul_comm, covariance_const_mul_left, covariance_const_mul_right, h' _ _ h'']

/-- If a stochastic process `Y` is such that for `s`, `Y s` can be written as a linear
combination of finitely many values of a Gaussian process, then `Y` is a Gaussian process. -/
lemma IsGaussianProcess.of_isGaussianProcess (hX : IsGaussianProcess X P)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
    [BorelSpace F] [SecondCountableTopology F] {Y : S → Ω → F}
    (h : ∀ s, ∃ I : Finset T, ∃ L : (I → E) →L[ℝ] F, ∀ ω, Y s ω = L (I.restrict (X · ω))) :
    IsGaussianProcess Y P where
  hasGaussianLaw I := by
    choose J L hL using h
    classical
    let K : (I.biUnion J → E) →L[ℝ] I → F :=
      { toFun x s := L s (fun t ↦ x ⟨t.1, Finset.mem_biUnion.2 ⟨s.1, s.2, t.2⟩⟩)
        map_add' x y := by ext; simp [← Pi.add_def]
        map_smul' c x := by ext; simp [← Pi.smul_def]
        cont := by fun_prop }
    have : (fun ω ↦ I.restrict (Y · ω)) = K ∘ (fun ω ↦ (I.biUnion J).restrict (X · ω)) := by
      ext; simp [K, hL]; rfl
    rw [this]
    exact (hX.hasGaussianLaw _).map _

lemma IsGaussianProcess.comp_right (h : IsGaussianProcess X P)
    (f : S → T) : IsGaussianProcess (X ∘ f) P :=
  h.of_isGaussianProcess fun s ↦ ⟨{f s},
    { toFun x := x ⟨f s, by simp⟩
      map_add' := by simp
      map_smul' := by simp },
    by simp⟩

lemma IsGaussianProcess.comp_left {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] (L : T → E →L[ℝ] F) (h : IsGaussianProcess X P) :
    IsGaussianProcess (fun t ω ↦ L t (X t ω)) P :=
  h.of_isGaussianProcess fun t ↦ ⟨{t},
    { toFun x := L t (x ⟨t, by simp⟩),
      map_add' := by simp
      map_smul' := by simp },
    by simp⟩

lemma IsGaussianProcess.smul (c : T → ℝ)
    (hX : IsGaussianProcess X P) :
    IsGaussianProcess (fun t ω ↦ c t • (X t ω)) P :=
  letI L t : E →L[ℝ] E :=
    { toFun x := c t • x
      map_add' := by simp
      map_smul' := by simp [smul_smul, mul_comm]
      cont := by fun_prop }
  hX.comp_left L

lemma IsGaussianProcess.shift [Add T] (h : IsGaussianProcess X P) (t₀ : T) :
    IsGaussianProcess (fun t ω ↦ X (t₀ + t) ω - X t₀ ω) P := by
  classical
  exact h.of_isGaussianProcess fun t ↦ ⟨{t₀, t₀ + t},
    { toFun x := x ⟨t₀ + t, by simp⟩ - x ⟨t₀, by simp⟩
      map_add' x y := by simp; abel
      map_smul' c x := by simp; module },
    by simp⟩

lemma IsGaussianProcess.restrict (h : IsGaussianProcess X P) (s : Set T) :
    IsGaussianProcess (fun t : s ↦ X t) P :=
  h.of_isGaussianProcess fun t ↦ ⟨{t.1},
    { toFun x := x ⟨t.1, by simp⟩
      map_add' := by simp
      map_smul' := by simp },
    by simp⟩

end ProbabilityTheory
