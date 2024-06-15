
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
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring

open MeasureTheory
open ENNReal
open Set
open Function
open scoped BigOperators

--defining partition given measure

structure partition {α : Type*} (m : MeasurableSpace α) (μ : Measure α) [IsProbabilityMeasure μ] :=
  f : ℕ → Set α         -- A function from natural numbers to sets of terms in α
  measurable : ∀ n, MeasurableSet (f n)  -- Each set is measurable
  (disjoint : ∀ i j, i ≠ j → μ (f i ∩ f j) = 0)  -- The sets are pairwise disjoint
  (cover : (⋃ n, f n) = Set.univ)  -- The union of all sets covers the entire space

--defining finite partitions given measure

structure finpart {α : Type*} (m : MeasurableSpace α) (μ : Measure α) [IsProbabilityMeasure μ] (n: ℕ):=
  (f : Fin n → Set α)          -- A function from finite sets of size n to sets of terms in α
  (measurable : ∀ i : Fin n, MeasurableSet (f i))  -- Each set is measurable
  (disjoint : ∀ i j, i ≠ j → μ (f i ∩ f j) = 0)  -- The sets are pairwise disjoint
  (cover : (⋃ i, f i) = Set.univ)  -- The union of all sets covers the entire space




--defining a function which given a finite partition give back
--the countable partition whit tail of empty sets
--

def finpart_to_partition {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (n : ℕ) (fp : finpart m μ n) : partition m μ
    where
  f := λ k ↦ if h : k < n then fp.f ⟨k, h⟩ else ∅
  measurable:= by
    intro k; by_cases h : k<n
    · simp only [dif_pos h]
      exact fp.measurable ⟨k, h⟩
    · simp only [dif_neg h]
      exact MeasurableSet.empty
  disjoint:=  by
    intro i j hij
    by_cases hi : i < n
    · by_cases hj: j < n
      · simp only [dif_pos hi, dif_pos hj]
        exact fp.disjoint ⟨i, hi⟩ ⟨j, hj⟩ (λ h ↦ hij (Fin.val_eq_of_eq h))
      · simp only [dif_pos hi, dif_neg hj, Set.inter_empty, measure_empty]
    · simp only [dif_neg hi, Set.empty_inter, measure_empty]
  cover:= by
    ext x
    constructor
    · tauto
    · intro h;dsimp; rw[← fp.cover] at h; rcases mem_iUnion.mp h with ⟨a, ha⟩
      rw[mem_iUnion]
      use a; simp only [dif_pos a.is_lt]; exact ha

#check finpart_to_partition
--A pairing function to map pairs of natural numbers to a single natural number

def pairing_function (k : ℕ × ℕ) : ℕ := (k.1 + k.2) * (k.1 + k.2 + 1) / 2 + k.2

#check pairing_function

-- An inverse of the pairing function to retrieve pairs from a single natural number
def inverse_pairing_function (k : ℕ) : ℕ × ℕ :=
  let w := Nat.floor (Nat.sqrt (8 * k + 1) - 1) / 2
  let t := w * (w + 1) / 2
  (w - (k - t), k - t)



theorem stupid: LeftInverse (inverse_pairing_function) pairing_function:= by
  intro x;unfold pairing_function;unfold inverse_pairing_function;dsimp
  sorry

theorem stupid': RightInverse (inverse_pairing_function) pairing_function := by
  sorry

--defining functin that takes two partitions and gives the refinement partition


def refine_partition {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p1 p2 : partition m μ) : partition m μ :=
{ f := λ k ↦ let (i, j) := inverse_pairing_function k
  p1.f i ∩ p2.f j
  --f := λ k ↦ p1.f (inverse_pairing_function k).1  ∩ p2.f (inverse_pairing_function k).1
  measurable := by
    intro k
    let i := (inverse_pairing_function k).1
    let j := (inverse_pairing_function k).2
    dsimp only
    exact MeasurableSet.inter (p1.measurable i) (p2.measurable j)
  disjoint := by
    intro i j hij
    dsimp
    let (i1, j1) := inverse_pairing_function i
    let (i2, j2) := inverse_pairing_function j
    by_cases h : i1 = i2 ∧ j1 = j2
    · exfalso; have h':(i1,j1)=(i2,j2):= by
        rw[h.1,h.2]
      have : inverse_pairing_function i = inverse_pairing_function j := by
        sorry
      have h :pairing_function (inverse_pairing_function i)= pairing_function (inverse_pairing_function j):= by
        rw[this]
      have h1 : pairing_function (inverse_pairing_function i)=i:= by exact stupid' _
      have h2 : pairing_function (inverse_pairing_function j)=j:= by exact stupid' _
      rw[h1,h2] at h
      exact hij h
    · simp only [Set.inter_comm, Set.inter_assoc]
      rcases not_and_or.mp h with a | b
      · apply measure_mono_null _ (p1.disjoint i1 i2 a)
        intro x hx; exact ⟨hx.1,((hx.2).2).1⟩
      · apply measure_mono_null _ (p2.disjoint j1 j2 b)
        intro x hx; exact ⟨(hx.2).1,((hx.2).2).2⟩
  cover := by
    ext x
    constructor
    · intro _
      exact Set.mem_univ x
    · intro h; dsimp; have h': x ∈ univ := by tauto
      rw [← p1.cover]at h; rw[← p2.cover] at h'
      rcases mem_iUnion.mp h with ⟨i, hi⟩
      rcases mem_iUnion.mp h' with ⟨j, hj⟩
      rw[mem_iUnion]
      use (pairing_function (i, j))
      constructor
      rw[stupid];exact hi
      rw[stupid]; exact hj
}

noncomputable section



--defining entropy and conditional entropy

 def met_entropy {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) : ℝ :=
  -∑' (n : ℕ),
    (μ (p.f n)).toReal* Real.log ((μ (p.f n)).toReal)

-- entropy of a finite partition

 def met_entropy' {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (n : ℕ) (fp : finpart m μ n): ℝ :=
-∑ i in Finset.univ,
   (μ (fp.f i)).toReal* Real.log ((μ (fp.f i)).toReal)




def conmet_entropy {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (g : partition m μ): ℝ :=
  ∑' (n : ℕ),
    let mb := (μ (g.f n)).toReal
    if mb = 0 then 0 else ∑' (n' : ℕ), (μ ((g.f n)∩(p.f n'))).toReal * Real.log ((μ ((g.f n)∩(p.f n'))).toReal/mb)


end section


--In this section we prove the max_entropy theorem relying on
-- the exiting definitions of convexity and the Jensen inequality in mathlib
--theorem ConvexOn.map_integral_le
--theorem StrictConvexOn.ae_eq_const_or_map_average_lt



--maximal entropy theorem



theorem max_entropy {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
(n : ℕ) (fp : finpart m μ n) :(met_entropy' n fp  ≤ Real.log n) ∧ (met_entropy' n fp = Real.log (n) ↔
∀ i : Fin n, (μ (fp.f i)).toReal=1/n) :=
by
  constructor
  · by_cases h : ∀ i : Fin n, μ (fp.f i)=1/n
    · simp [met_entropy',h]
      rw[← mul_assoc]
      sorry
    · push_neg at h
      sorry
  · constructor
    · sorry
    · sorry



-- in this next section we indtroduce information function
-- and prove proposition 1.7

--function extracting the set in the partition containing desired point
noncomputable section

--information funciton
def info {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (x : α) :ℝ := by
    have h: x ∈ univ := by tauto
    rw[← p.cover] at h; rw[mem_iUnion] at h
    choose a b using h
    exact (-Real.log (μ (p.f (a))).toReal)


def cond_info {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (s : partition m μ) (x : α) :ℝ := by
  have h: x ∈ univ := by tauto
  have h': x ∈ univ := by tauto
  rw[← p.cover] at h; rw[mem_iUnion] at h
  rw[← s.cover] at h'; rw[mem_iUnion] at h'
  choose a b using h
  choose c d using h'
  exact (-Real.log (μ ((p.f (a)) ∩ s.f (c))).toReal/(μ (s.f (c))).toReal)

-- should introduce a conditional in case the measure in denominator is zero

end section

theorem ent_inf {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ): met_entropy p = ∫ x, info p x ∂μ := by
  sorry

theorem info_add {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (s : partition m μ) (t : partition m μ) :
  cond_info (refine_partition p s) (t) = (cond_info s t) + cond_info (p) (refine_partition s t) := by
    sorry
theorem ent_add {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (s : partition m μ) (t : partition m μ) :
  conmet_entropy (refine_partition p s) (t) = (conmet_entropy s t) + conmet_entropy (p) (refine_partition s t) := by
    sorry

theorem  inf_mono {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (s : partition m μ) (t : partition m μ) :
  cond_info s t ≤ cond_info (refine_partition p s) (t):= by
    sorry
theorem  ent_mono {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (s : partition m μ) (t : partition m μ) :
  conmet_entropy s t ≤ conmet_entropy (refine_partition p s) (t):= by
    sorry

theorem ent_monod {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (s : partition m μ) (t : partition m μ) :
  conmet_entropy (p) (refine_partition s t) ≤ conmet_entropy p t := by
    sorry
theorem ent_subadd {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (s : partition m μ) (t : partition m μ) :
  conmet_entropy (refine_partition p s) (t) ≤ conmet_entropy p t +  conmet_entropy s t := by
    sorry












variable {α : Type*} [LinearOrderedField α] [OrderedAddCommGroup α] [Module α α] [OrderedSMul α α]

#check Fin.elim0



def convex_on' (s : Set ℝ ) (f : ℝ → ℝ) : Prop :=
∀ (n : ℕ) (x : Fin n → ℝ ) (t : Fin n → ℝ),
  (∀ i , x i ∈ s) →
  (∀ i, 0 ≤ t i) →
  (∑ i, t i = 1) →
  f (∑ i, t i * x i) ≤ ∑ i, t i * f (x i)





variable {a b : ℝ} {f : ℝ → ℝ}






theorem convex_combination_inequality
  {f : ℝ → ℝ} {a b : ℝ} (hf : ConvexOn ℝ  (Icc a b) f)
  {n : ℕ} {x : Fin n → ℝ} {t : Fin n → ℝ}
  (hx : ∀ i, x i ∈ Icc a b) (ht : ∀ i, t i ∈ Icc 0 1)
  (ht_sum : ∑ i, t i = 1) :
  f (∑ i, t i * x i) ≤ ∑ i, t i * f (x i) := by
  -- We'll proceed by induction on `n`.
    induction' n with n ih
  -- Base case: n = 0
    · exfalso; have h': ∑ i : Fin 0, t i = (0 : ℝ) := by
        simp only [Fin.sum_univ_zero, Finset.sum_empty, MulZeroClass.mul_zero]
      rw[ht_sum] at h'; have: (1 : ℝ) ≠ 0 := by norm_num
      exact this h'
    · sorry
end


-- need to understand what proofs of convergence are needed

--𝑓(𝑚,𝑛)=2𝑚(2𝑛+1)−1 possible function for the


--definitin of convex and jensen inequality is already on Lean

--theorem ConvexOn.map_integral_le
--theorem StrictConvexOn.ae_eq_const_or_map_average_lt

--the jensens inequality is in lean both in its strict and non strict
--form
-- left to prove that two specific functions are strictly convex before proving maximal entropy
