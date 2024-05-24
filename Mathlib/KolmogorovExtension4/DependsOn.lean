import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.Data.Finset.Update

open MeasureTheory ENNReal Set Finset symmDiff

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)] {α : Type*}
variable {f : (∀ i, X i) → α}

def DependsOn (f : (∀ i, X i) → α) (s : Set ι) : Prop :=
  ∀ x y, (∀ i ∈ s, x i = y i) → f x = f y

theorem dependsOn_const (a : α) : DependsOn (fun _ : ∀ i, X i ↦ a) ∅ := by simp [DependsOn]

theorem dependsOn_empty (hf : DependsOn f ∅) (x y : (i : ι) → X i) : f x = f y := hf x y (by simp)

theorem dependsOn_updateFinset {s : Set ι} (hf : DependsOn f s) (t : Finset ι) (y : (i : t) → X i) :
    DependsOn (fun x ↦ f (Function.updateFinset x t y)) (s \ t) := by
  intro x₁ x₂ h
  refine hf _ _ (fun i hi ↦ ?_)
  simp only [Function.updateFinset]
  split_ifs with h'
  · rfl
  · exact h i <| (mem_diff _).2 ⟨hi, h'⟩

theorem dependsOn_update {s : Finset ι} (hf : DependsOn f s) (i : ι) (y : X i) :
    DependsOn (fun x ↦ f (Function.update x i y)) (s.erase i) := by
  simp_rw [Function.update_eq_updateFinset, erase_eq, coe_sdiff]
  exact dependsOn_updateFinset hf _ _

variable {μ : (i : ι) → Measure (X i)} {f : ((i : ι) → X i) → ℝ≥0∞} {s : Set ι}

theorem dependsOn_lmarginal (hf : DependsOn f s) (t : Finset ι) :
    DependsOn (∫⋯∫⁻_t, f ∂μ) (s \ t) := by
  intro x y hxy
  have aux z : f (Function.updateFinset x t z) = f (Function.updateFinset y t z) := by
    refine hf _ _ (fun i hi ↦ ?_)
    simp only [Function.updateFinset]
    split_ifs with h
    · rfl
    · exact hxy i ((mem_diff _).2 ⟨hi, h⟩)
  exact lintegral_congr aux

variable [∀ i, IsProbabilityMeasure (μ i)]

theorem lmarginal_eq_of_disjoint (hf : DependsOn f s) {t : Finset ι} (hst : Disjoint s t) :
    ∫⋯∫⁻_t, f ∂μ = f := by
  ext x
  have aux y : f (Function.updateFinset x t y) = f x := by
    refine hf _ _ (fun i hi ↦ ?_)
    simp only [Function.updateFinset]
    split_ifs with h
    · exact (Set.not_disjoint_iff.2 ⟨i, hi, h⟩ hst).elim
    · rfl
  simp [lmarginal, lintegral_congr aux]

theorem lmarginal_const {s : Finset ι} (c : ℝ≥0∞) (x : ∀ i, X i) :
    (∫⋯∫⁻_s, (fun _ ↦ c) ∂μ) x = c := by
  rw [lmarginal_eq_of_disjoint (dependsOn_const c) (empty_disjoint _)]

theorem lmarginal_eq_of_disjoint_diff (mf : Measurable f) (hf : DependsOn f s) {t u : Finset ι}
(htu : t ⊆ u) (hsut : Disjoint s (u \ t)) :
    ∫⋯∫⁻_u, f ∂μ = ∫⋯∫⁻_t, f ∂μ := by
  rw [← coe_sdiff] at hsut
  rw [← union_sdiff_of_subset htu, lmarginal_union _ _ mf disjoint_sdiff_self_right]
  congrm ∫⋯∫⁻_t, ?_ ∂μ
  exact lmarginal_eq_of_disjoint hf hsut

theorem lmarginal_eq_of_disjoint_symmDiff (mf : Measurable f) (hf : DependsOn f s)
    {t u : Finset ι} (hstu : Disjoint s (t ∆ u)) :
    ∫⋯∫⁻_t, f ∂μ = ∫⋯∫⁻_u, f ∂μ := by
  rw [symmDiff_def, disjoint_sup_right] at hstu
  rcases hstu with ⟨h1, h2⟩
  rw [← coe_sdiff] at h1 h2
  have : ∫⋯∫⁻_u ∪ t, f ∂μ = ∫⋯∫⁻_u, f ∂μ := by
    rw [← union_sdiff_self_eq_union, lmarginal_union _ _ mf disjoint_sdiff_self_right]
    congrm ∫⋯∫⁻_u, ?_ ∂μ
    exact lmarginal_eq_of_disjoint hf h1
  rw [← this, Finset.union_comm, ← union_sdiff_self_eq_union,
    lmarginal_union _ _ mf disjoint_sdiff_self_right]
  congrm ∫⋯∫⁻_t, ?_ ∂μ
  exact (lmarginal_eq_of_disjoint hf h2).symm
