import Mathlib.Analysis.NormedSpace.FiniteDimension
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.ENNReal.Real
import Init.Data.Fin.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.SetTheory.Cardinal.Basic





#check MeasureTheory.MeasurePreserving
#check Measurable
open MeasureTheory ENNReal Set Function BigOperators Finset
#check tsum

structure partition {α : Type*} (m : MeasurableSpace α) (μ : Measure α) [IsProbabilityMeasure μ] :=
  f : ℕ → Set α         -- A function from natural numbers to sets of terms in α
  measurable : ∀ n, MeasurableSet (f n)  -- Each set is measurable
  (disjoint : ∀ i j, i ≠ j → μ (f i ∩ f j) = 0)  -- The sets are pairwise disjoint
  (cover : μ (⋃ n, f n)ᶜ  = 0)  -- The union of all sets covers the entire space

noncomputable section
def met_entropy {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) : ℝ :=
  -∑' (n : ℕ),
    (μ (p.f n)).toReal* Real.log ((μ (p.f n)).toReal)


-- defining conditional entropy

def conmet_entropy {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (g : partition m μ): ℝ :=
  ∑' (n : ℕ),
    let mb := (μ (g.f n)).toReal
    if mb = 0 then 0 else ∑' (n' : ℕ), (μ ((g.f n)∩(p.f n'))).toReal * Real.log ((μ ((g.f n)∩(p.f n'))).toReal/mb)


#check preimage_compl
#check add_left_cancel

lemma measure_compl_eq_of_measure_eq {α : Type*} [m : MeasurableSpace α] {μ : Measure α}[IsProbabilityMeasure μ] {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) (h : μ A = μ B) :
  μ (Aᶜ) = μ (Bᶜ) := by
  have hA₁ : μ (A ∪ Aᶜ) = μ (Set.univ) := by
    rw [Set.union_compl_self A]
  have hB₁ : μ (B ∪ Bᶜ) = μ (Set.univ) := by
    rw [Set.union_compl_self B]
  have hA₂ : μ (A ∪ Aᶜ) = μ A + μ Aᶜ := by
    exact measure_union₀_aux (MeasurableSet.nullMeasurableSet hA) (NullMeasurableSet.compl_iff.mpr (MeasurableSet.nullMeasurableSet hA)) aedisjoint_compl_right
  have hB₂ : μ (B ∪ Bᶜ) = μ B + μ Bᶜ := by
    exact measure_union₀_aux (MeasurableSet.nullMeasurableSet hB) (NullMeasurableSet.compl_iff.mpr (MeasurableSet.nullMeasurableSet hB)) aedisjoint_compl_right
  have: μ A < 1:= by
    sorry
  have: μ B < 1:= by
    sorry
  have: μ Aᶜ < 1 := by sorry
  have: μ Bᶜ  < 1 := by sorry
  rw[← hA₁,hA₂,hB₂,h] at hB₁--; apply add_left_cancel at hB₁;
  sorry

def pre_partition {α : Type*} [m : MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ] (p : partition m μ)
(T: α → α) (h₁: MeasureTheory.MeasurePreserving T μ μ ): partition m μ
  where
f := λ n ↦  T ⁻¹' (p.f n)
measurable:= by
  intro N
  exact MeasurableSet.preimage (p.measurable N) h
disjoint:= by
  intro i j hij
  have:= p.disjoint i j hij
  dsimp; show μ (T⁻¹' (p.f i ∩ p.f j))=0
  have : μ (T⁻¹' (p.f i ∩ p.f j)) = μ (p.f i ∩ p.f j) := by
    exact MeasurePreserving.measure_preimage h₁ (MeasurableSet.inter (p.measurable i) (p.measurable j))
  rw[this];assumption
cover:= by
  have := p.cover
  rw[← preimage_iUnion]
  have: μ (T ⁻¹' ⋃ i, p.f i) = μ (⋃ i, p.f i) := by
    exact MeasurePreserving.measure_preimage h₁ (MeasurableSet.iUnion (p.measurable))
  have: μ (T ⁻¹' ⋃ i, p.f i)ᶜ = μ (⋃ i, p.f i)ᶜ := by
    refine measure_compl_eq_of_measure_eq ?hA ?hB this
    · refine MeasurableSpace.map_def.mp ?hA.a
      · refine MeasurableSet.iUnion ?hA.a.h
        · sorry
    · exact (MeasurableSet.iUnion (p.measurable))
  rwa [this]



theorem invariance {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ](T: α → α)
 (self : MeasureTheory.MeasurePreserving T μ μ) (p : partition m μ) (g : partition m μ) :
 cond_info p g ∘ T = cond_info (pre_partition p T self) (pre_partition g T self) := by
  sorry
lemma  molly {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ](T: α → α)
 (self : MeasureTheory.MeasurePreserving T μ μ) (p : partition m μ)(x: α)[dec : Decidable (x ∈ (⋃ n, p.f n))][dec : Decidable (x ∈ (⋃ n, p.f n))]:
 ∫ x, info p ∘ T x ∂μ = ∫ x, info p x ∂μ

theorem invariance₁ {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ](T: α → α)
 (self : MeasureTheory.MeasurePreserving T μ μ) (p : partition m μ) (g : partition m μ):
conmet_entropy p g = conmet_entropy (pre_partition p T self) (pre_partition g T self) := by
  sorry

noncomputable def iter_pre_partition {α : Type*}  {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (T : α → α) (self : MeasureTheory.MeasurePreserving T μ μ) : ℕ → partition m μ
| 0  => p
| (n + 1) => pre_partition (iter_pre_partition p T self n) T self


def partition.tentropy {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ](T: α → α)
 (self : MeasureTheory.MeasurePreserving T μ μ) (p : partition m μ) : ℝ :=
⨅ (n : ℕ), (1 / (n + 1 : ℝ)) * met_entropy (iter_pre_partition p T self n)

def tentropy {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ](T: α → α)
 (self : MeasureTheory.MeasurePreserving T μ μ) (p : partition m μ): ℝ :=
⨆ (p:partition m μ ), p.tentropy T self
