import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.NormedSpace.FiniteDimension
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNReal
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



structure partition {α : Type*} (m : MeasurableSpace α) (μ : Measure α) [IsProbabilityMeasure μ] :=
  P : Set (Set α)        -- A set of sets of terms in α
  measurable : ∀ a ∈ P, MeasurableSet a  -- Each set is measurable
  disjoint : P.Pairwise (AEDisjoint μ)  -- The sets are pairwise disjoint
  cover : μ (⋃₀ P)ᶜ  = 0  -- The union of all sets covers the entire space
  countable : P.Countable -- at most countable or finite

def injective_function {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p1 p2 : partition m μ)(f:p1.P → ℕ)(g:p2.P → ℕ) : {x | ∃ a b, a ∈ p1.P ∧ b ∈ p2.P ∧ x = a ∩ b} → ℕ :=
  λ x ↦ (Nat.pairEquiv.toFun (f a,g b))


def refine_partition {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p1 p2 : partition m μ) : partition m μ
    where
  P := {a ∩ b|(a ∈ p1.P) (b ∈ p2.P)}
  measurable := by
    intro k hk; dsimp at hk; rcases hk with ⟨a, ha, b, hb, rfl⟩
    exact MeasurableSet.inter (p1.measurable a ha) (p2.measurable b hb)
  disjoint := by
    intro x hx y hy hxy
    simp at *
    rcases hx with ⟨a,⟨ha,h⟩⟩
    rcases h with ⟨b,⟨hb,hx⟩⟩
    rcases hy with ⟨c,⟨hc,h⟩⟩
    rcases h with ⟨d,⟨hd,hy⟩⟩
    have h₁: a ≠ c ∨ b ≠ d:= by
      by_contra hcontra
      push_neg at hcontra
      rw[hcontra.1,hcontra.2,hy] at hx; exact hxy (id (Eq.symm hx))
    cases' h₁ with h₁ h₁
    · rw[← hx,← hy]; show μ ((a∩b) ∩ (c ∩ d))=0
      rw[← inter_assoc (a ∩ b),inter_assoc a,inter_comm b,← inter_assoc a,inter_assoc (a ∩ c)]
      refine measure_inter_null_of_null_left (b ∩ d) ?_
      · exact p1.disjoint ha hc h₁
    · rw[← hx,← hy]; show μ ((a∩b) ∩ (c ∩ d))=0
      rw[inter_comm a,inter_comm c,← inter_assoc (b ∩ a),inter_assoc b,inter_comm a,← inter_assoc b,inter_assoc (b ∩ d)]
      refine measure_inter_null_of_null_left (a ∩ c) ?_
      · exact p2.disjoint hb hd h₁
  cover := by
    have h: ⋃₀ p1.P ∩ ⋃₀ p2.P  ⊆ ⋃₀ {x | ∃ a b, a ∈ p1.P ∧ b ∈ p2.P ∧ x = a ∩ b} := by
      intro x ⟨hx₁,hx₂⟩;rw [mem_sUnion] at *
      rcases hx₁ with ⟨a,ha₁,ha₂⟩; rcases hx₂ with ⟨b,hb₁,hb₂⟩
      use a∩b;simp; refine ⟨?_, ha₂ ,hb₂⟩
      exact ⟨a,ha₁,b,hb₁,rfl⟩
    have h₁: μ  (⋃₀ p1.P ∩ ⋃₀ p2.P)ᶜ = 0 := by
      rw [Set.compl_inter]
      exact measure_union_null p1.cover p2.cover
    exact measure_mono_null (compl_subset_compl_of_subset h) h₁
  countable := by
    convert (p1.countable.prod p2.countable).image (fun x => x.1 ∩ x.2) using 1
    ext x
    simp
    tauto



lemma partcover {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ](p: partition m μ ):
μ (⋃₀ p.P) = 1 := by
  exact (prob_compl_eq_zero_iff (MeasurableSet.sUnion p.countable p.measurable)).mp p.cover

noncomputable section

def met_entropy {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
(p : partition m μ) : EReal  :=
∑' (a:p.P),
-(μ a * ENNReal.log (μ a))

lemma met_entropy_nng {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
(p : partition m μ): 0 ≤ met_entropy p := by
unfold met_entropy
refine tsum_nonneg ?h
· intro a
  have h₁: (0:EReal) ≤  (μ ↑a) := by
    exact EReal.coe_ennreal_nonneg (μ ↑a)
  have h₂: μ a ≤ 1 := by
    exact prob_le_one
  have: (μ a).log ≤ 0 := by
    exact (log_le_one_iff (μ ↑a)).mpr h₂
  refine EReal.le_neg_of_le_neg ?h.h
  · simp;exact mul_nonpos_of_nonneg_of_nonpos h₁ this

def cond_entropy {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
(p s: partition m μ) : EReal :=
∑' (a:p.P),
∑' (b:s.P),
(μ (a∩b)) * ENNReal.log (μ (a ∩ b))/(μ b)

end section

lemma addone {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
 (p : partition m μ) : μ (⋃₀ p.P) = ∑' (a:p.P), μ a := by
  exact measure_sUnion₀ p.countable p.disjoint (fun s a => MeasurableSet.nullMeasurableSet (p.measurable s a))

lemma partition_finite_or_infinite {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
  [IsProbabilityMeasure μ] (p : partition m μ) : p.P.Finite ∨ p.P.Infinite := by
  exact Set.finite_or_infinite p.P


lemma max_ent {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ](p : partition m μ)(hp: p.P.Finite)[Fintype p.P]
(n : ℕ) (hn:Finset.card ((p.P).toFinset)=n)(h : ¬∀ a:p.P, μ a = 1 / ↑n) : Real.log ↑n > -∑ i : Fin n, (μ (fp.f i)).toReal * Real.log (μ (fp.f i)).toReal:= by
