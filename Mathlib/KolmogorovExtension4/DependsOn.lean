import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.Data.Finset.Update

open MeasureTheory ENNReal Finset symmDiff

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
variable {μ : (i : ι) → Measure (X i)}
variable {f : (∀ i, X i) → ℝ≥0∞} {s : Finset ι}

def DependsOn (f : (∀ i, X i) → ℝ≥0∞) (s : Finset ι) : Prop :=
  ∀ x y, (∀ i ∈ s, x i = y i) → f x = f y

theorem const_dependsOn (c : ℝ≥0∞) : DependsOn (fun _ : ∀ i, X i ↦ c) ∅ := by
  simp [DependsOn]

variable (hf : DependsOn f s)

theorem lmarginal_dependsOn (t : Finset ι) (hf : DependsOn f s) :
    DependsOn (∫⋯∫⁻_t, f ∂μ) (s \ t) := by
  intro x y hxy
  have : ∀ z, f (Function.updateFinset x t z) = f (Function.updateFinset y t z) := by
    intro z
    apply hf
    intro i hi
    rw [Function.updateFinset_def, Function.updateFinset_def]
    by_cases h : i ∈ t
    · simp [h]
    · simp only [h, ↓reduceDite]
      exact hxy i (mem_sdiff.2 ⟨hi, h⟩)
  exact lintegral_congr this

variable [∀ i, IsProbabilityMeasure (μ i)]

theorem lmarginal_eq {t : Finset ι} (hst : Disjoint s t) :
    ∫⋯∫⁻_t, f ∂μ = f := by
  ext x
  have : ∀ y, f (Function.updateFinset x t y) = f x := by
    intro y
    apply hf
    intro i hi
    rw [Function.updateFinset_def]
    by_cases h : i ∈ t
    · exfalso
      apply not_mem_empty i
      rw [disjoint_iff_inter_eq_empty] at hst
      rw [← hst]
      simp [hi, h]
    · simp [h]
  rw [lmarginal, lintegral_congr this, lintegral_const]
  simp

theorem lmarginal_const (c : ℝ≥0∞) : ∀ x : ∀ i, X i, (∫⋯∫⁻_s, (fun _ ↦ c) ∂μ) x = c := by
  intro x
  rw [lmarginal_eq (const_dependsOn c) (Finset.disjoint_empty_left _)]

variable (mf : Measurable f)

theorem lmarginal_eq' (t u : Finset ι) (htu : t ⊆ u) (hsu : Disjoint s (u \ t)) :
    ∫⋯∫⁻_u, f ∂μ = ∫⋯∫⁻_t, f ∂μ := by
  rw [← union_sdiff_of_subset htu, lmarginal_union]
  congrm ∫⋯∫⁻_t, ?_ ∂μ
  apply lmarginal_eq hf hsu
  exact mf
  exact disjoint_sdiff_self_right

theorem lmarginal_eq'' (t u : Finset ι) (hstu : Disjoint s (t ∆ u)) :
    ∫⋯∫⁻_t, f ∂μ = ∫⋯∫⁻_u, f ∂μ := by
  rw [symmDiff_def, disjoint_sup_right] at hstu
  rcases hstu with ⟨h1, h2⟩
  have : ∫⋯∫⁻_u ∪ t, f ∂μ = ∫⋯∫⁻_u, f ∂μ := by
    rw [← union_sdiff_self_eq_union, lmarginal_union]
    congrm ∫⋯∫⁻_u, ?_ ∂μ
    apply lmarginal_eq hf h1
    exact mf
    exact disjoint_sdiff_self_right
  rw [← this, union_comm, ← union_sdiff_self_eq_union, lmarginal_union]
  congrm ∫⋯∫⁻_t, ?_ ∂μ
  rw [lmarginal_eq hf h2]
  exact mf
  exact disjoint_sdiff_self_right
