import Mathlib.Topology.Instances.Real
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
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.SetTheory.Cardinal.Basic



open MeasureTheory ENNReal Set Function BigOperators Finset

#check Set.Countable_bUnion
#check Set.countable_iff_exists_injective
#check Real.log

structure partition {α : Type*} (m : MeasurableSpace α) (μ : Measure α) [IsProbabilityMeasure μ] :=
  P : Set (Set α)        -- A function from natural numbers to sets of terms in α
  measurable : ∀ a ∈ P, MeasurableSet a  -- Each set is measurable
  disjoint : ∀ a b : P, a≠b → μ (a ∩ b)=0  -- The sets are pairwise disjoint
  cover : μ (⋃₀ P)ᶜ  = 0  -- The union of all sets covers the entire space
  countable : P.Countable

def refine_partition {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p1 p2 : partition m μ) : partition m μ
    where
  P := {x | ∃ a b, a ∈ p1.P ∧ b ∈ p2.P ∧ x = a ∩ b}
  measurable := by
    intro k hk; dsimp at hk; rcases hk with ⟨a,b,h₁,h₂,h₃⟩;rw[h₃]
    exact MeasurableSet.inter (p1.measurable a h₁) (p2.measurable b h₂)
  disjoint := by
    intro a b hab; dsimp at a b; have := a; have:= hab;
    rcases a with ⟨c,d,e,hd,he,hc⟩
    rcases b with ⟨f,g,h,hg,hh,hf⟩
    have : d ≠ g ∨ e ≠ h := by
      by_contra h'; push_neg at h'
      rw [h'.1,h'.2,← hf] at hc; dsimp at hab
      exact hab hc
  cover := by
    have h: ⋃₀ p1.P ∩ ⋃₀ p2.P  ⊆ ⋃₀ {x | ∃ a b, a ∈ p1.P ∧ b ∈ p2.P ∧ x = a ∩ b} := by
      intro x ⟨hx₁,hx₂⟩;rw [mem_sUnion] at *
      rcases hx₁ with ⟨a,ha₁,ha₂⟩; rcases hx₂ with ⟨b,hb₁,hb₂⟩
      use a∩b;simp; refine ⟨?_, ha₂ ,hb₂⟩
      exact ⟨a,ha₁,b,hb₁,rfl⟩
    have h₁: μ  (⋃₀ p1.P ∩ ⋃₀ p2.P)ᶜ = 0 := by
      rw [Set.compl_inter]
      have h₁ := measure_union_le (μ := μ) ((⋃₀ p1.P)ᶜ) ((⋃₀ p2.P)ᶜ)
      have h₂ :  μ (⋃₀ p1.P)ᶜ + μ (⋃₀ p2.P)ᶜ = 0 := by
        simp only [p1.cover,p2.cover]; rw [add_zero]
    exact measure_mono_null (compl_subset_compl_of_subset h) h₁
  countable := by
    have h₁ := Set.countable_iff_exists_injective.mp p1.countable
    have h₂ := Set.countable_iff_exists_injective.mp p2.countable
    rcases h₁ with ⟨f,hf⟩;rcases h₂ with ⟨g,hg⟩
    refine Set.countable_iff_exists_injective.mpr ?_
    · use (λ x : {x // ∃ a b, a ∈ p1.P ∧ b ∈ p2.P ∧ x = a ∩ b} ↦
       (Nat.pairEquiv.toFun (1,2)))

  noncmputable def met_entropy {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) : ℝ  :=
  -∑' (a:p.P),
  μ a * ENNReal.log (μ a)
