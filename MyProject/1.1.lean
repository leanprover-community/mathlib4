
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
import Mathlib.MeasureTheory.Measure.NullMeasurable




open MeasureTheory
open ENNReal
open Set
open Function
open scoped BigOperators
open Finset

--defining partition given measure, disjointness defined measure-theoretically
-- cover for now is defined in the set-theoretic sense

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
  (cover : (⋃ i ∈ Finset.univ, f i) = Set.univ)  -- The union of all sets covers the entire space

structure finpart' {α : Type*} (m : MeasurableSpace α) (μ : Measure α) [IsProbabilityMeasure μ] (n: ℕ):=
  (f : Fin n → Set α)          -- A function from finite sets of size n to sets of terms in α
  (measurable : ∀ i : Fin n, MeasurableSet (f i))  -- Each set is measurable
  (disjoint : ∀ i j, i ≠ j → μ (f i ∩ f j) = 0)  -- The sets are pairwise disjoint
  (cover : (⋃ i , f i) = Set.univ)  -- The union of all sets covers the entire space




--defining a function which given a finite partition gives back
--the countable partition whith a tail of empty sets


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
      rcases mem_iUnion.mp ha with ⟨b, hb⟩
      use a; simp only [dif_pos a.is_lt]; exact hb




--defining function that takes two partitions and gives the refinement partition

def refine_partition {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p1 p2 : partition m μ) : partition m μ :=
{ f := λ k ↦ let (i, j) := Nat.pairEquiv.invFun k
  p1.f i ∩ p2.f j
  measurable := by
    intro k
    let i := (Nat.pairEquiv.invFun k).1
    let j := (Nat.pairEquiv.invFun k).2
    dsimp only
    exact MeasurableSet.inter (p1.measurable i) (p2.measurable j)
  disjoint := by
    intro i j hij;dsimp
    let i1 := (Nat.pairEquiv.invFun i).1
    let j1 := (Nat.pairEquiv.invFun i).2
    let i2 := (Nat.pairEquiv.invFun j).1
    let j2 := (Nat.pairEquiv.invFun j).2
    by_cases h : i1 = i2 ∧ j1 = j2
    · exfalso; have h':(i1,j1)=(i2,j2):= by
        rw[h.1,h.2]
      have : Nat.pairEquiv.invFun i = Nat.pairEquiv.invFun j := by
        exact h'
      have h : Nat.pairEquiv.toFun (Nat.pairEquiv.invFun i)= Nat.pairEquiv.toFun (Nat.pairEquiv.invFun j):= by
        rw[this]
      have h1 : Nat.pairEquiv.toFun (Nat.pairEquiv.invFun i) = i := by exact Nat.pairEquiv.right_inv _
      have h2 : Nat.pairEquiv.toFun (Nat.pairEquiv.invFun j) = j := by exact  Nat.pairEquiv.right_inv _
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
    · intro h;dsimp; have h':= h
      rw [← p1.cover]at h; rw[← p2.cover] at h'
      rcases mem_iUnion.mp h with ⟨i, hi⟩
      rcases mem_iUnion.mp h' with ⟨j, hj⟩
      rw[mem_iUnion]
      use (Nat.pairEquiv.toFun (i, j))
      simp [Nat.pairEquiv.left_inv]
      exact ⟨hi, hj⟩
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

-- defining conditional entropy

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



noncomputable section

def φ (x : ℝ) : ℝ :=
x * Real.log x

end section






#check MeasureTheory.measure_iUnion₀
#check MeasureTheory.measure_biUnion_finset₀
#check MeasureTheory.measure_biUnion_finset


--useful lemmas

theorem addone {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
 (p : partition m μ) : (μ (⋃ i, p.f i)) = ∑' i , μ (p.f i) := by
  apply MeasureTheory.measure_iUnion₀
  · intro x y
    exact p.disjoint x y
  · intro i-- (h : MeasurableSet s) :
    exact  MeasurableSet.nullMeasurableSet (p.measurable i)
--Toreal? or no.

theorem addone' {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
(n : ℕ) (fp : finpart m μ n) : (μ (⋃ i ∈ Finset.univ, fp.f i)) = ∑ i ∈ Finset.univ, μ (fp.f i) := by
  apply MeasureTheory.measure_biUnion_finset₀
  · intro x _ s _ hxs
    exact fp.disjoint x s hxs
  · intro b _
    exact MeasurableSet.nullMeasurableSet (fp.measurable b)


theorem equiv {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
 (n : ℕ) (fp : finpart m μ n): (μ (⋃ i ∈ Finset.univ, fp.f i)).toReal =∑ i ∈ Finset.univ,(μ (fp.f i)).toReal := by
  have h: (∑ i ∈ Finset.univ,(μ (fp.f i))).toReal=∑ i ∈ Finset.univ,(μ (fp.f i)).toReal := by
    refine toReal_sum ?hf
    intro a _
    exact (measure_lt_top μ (fp.f a)).ne
  rw [← addone' n fp]  at h
  exact h










#check @_root_.mul_lt_mul_left
#check mul_lt_mul_left

--maximal entropy theorem

theorem max_entropy {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
(n : ℕ) (fp : finpart m μ n) :(met_entropy' n fp  ≤ Real.log n) ∧ (met_entropy' n fp = Real.log (n) ↔
∀ i : Fin n, (μ (fp.f i)).toReal=1/n) :=
by
  constructor
  · by_cases h : ∀ i : Fin n, μ (fp.f i)=1/n
    · simp [met_entropy',h]
      rw[← mul_assoc]
      obtain (rfl | hn) := eq_zero_or_pos n
      · simp
      · simp [toReal_inv, mul_inv_cancel <| show (n : ℝ) ≠ 0 by norm_cast; linarith]
    · push_neg at h
      rcases h with ⟨a,b⟩
      simp [met_entropy']
      obtain (rfl | hn) := eq_zero_or_pos n
      · simp
      · have : n ≠ 0 := by linarith[hn]
        have h: -1/(n:ℝ) *Real.log (n:ℝ) = 1/(n:ℝ) * Real.log (1/(n:ℝ)) := by
          field_simp
          simp [Real.log_inv, mul_inv_cancel <| show (n : ℝ) ≠ 0 by norm_cast]
        have h1: 1/(n:ℝ) * Real.log (1/(n:ℝ))= φ (1/(n:ℝ)) := by
          tauto
        have h2: (∑ i in Finset.univ, (μ (fp.f i)).toReal)=1 := by
          rw[← equiv]; rw [fp.cover]; simp
        have h3: 1/(n:ℝ) = 1/(n:ℝ)*(∑ i in Finset.univ, (μ (fp.f i)).toReal) := by
          rw[h2,mul_one]
        have h4: φ (1/(n:ℝ))= φ (1/(n:ℝ)*(∑ i in Finset.univ, (μ (fp.f i)).toReal)) := by
          nth_rewrite 1[h3]
          rfl
        have h5: φ ((∑ i in Finset.univ, 1/(n:ℝ)*(μ (fp.f i)).toReal)) = φ ((1/(n:ℝ)) * (∑ i in Finset.univ, (μ (fp.f i)).toReal)) := by
          rw[mul_sum]
        have h6: sconvex_on' (Ici (0:ℝ)) φ := by
          sorry
        let t : Fin n → ℝ := λ i ↦ 1 / n
        have h7: φ ((∑ i in Finset.univ, (t i)*(μ (fp.f i)).toReal)) = φ ((∑ i in Finset.univ, 1/(n:ℝ)*(μ (fp.f i)).toReal)) := by
          exact rfl
        have h8: φ ((∑ i in Finset.univ, (t i)*(μ (fp.f i)).toReal)) <  ∑ i in Finset.univ, (t i) * φ ((μ (fp.f i)).toReal) := by
          apply (h6 n)
          · intro s; simp [zero_le (μ (fp.f s))]
          · intro s; change 0 ≤ 1 / (n : ℝ);simp
          · change ∑ i : Fin n, 1 / (n : ℝ) = 1
            simp[mul_inv_cancel,this]
        have h9:  ∑ i in Finset.univ, (t i) * φ ((μ (fp.f i)).toReal) = ∑ i in Finset.univ, 1/(n:ℝ) * φ ((μ (fp.f i)).toReal):= by
          exact rfl
        rw[h7,h9,h5,h2,mul_one,← mul_sum] at h8;unfold φ at h8
        have : 0 < 1 / (n : ℝ) := by
          sorry
        apply (mul_lt_mul_left.mp (1 / (n : ℝ)) ((1 / ↑n).log_) ( ∑ i : Fin n, (μ (fp.f i)).toReal * (μ (fp.f i)).toReal.log) this).mp at h8










            --simp [mul_inv_cancel <| show (n : ℝ) ≠ 0 by linarith [hn]]




-- in this next section we indtroduce information function
-- and prove proposition 1.7


noncomputable section

--information funciton

def info {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (x : α) :ℝ := by
    have h: x ∈ univ := by tauto
    rw[← p.cover] at h; rw[mem_iUnion] at h
    choose a b using h
    exact (-Real.log (μ (p.f (a))).toReal)

-- conditional information function

def cond_info {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (s : partition m μ) (x : α) :ℝ := by
  have h: x ∈ Set.univ := by tauto
  have h':= h
  rw[← p.cover] at h; rw[mem_iUnion] at h;rw[← s.cover] at h'; rw[mem_iUnion] at h'
  choose a _ using h
  choose c _ using h'
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

end


-- need to understand what proofs of convergence are needed

--𝑓(𝑚,𝑛)=2𝑚(2𝑛+1)−1 possible function for the


--definitin of convex and jensen inequality is already on Lean

--theorem ConvexOn.map_integral_le
--theorem StrictConvexOn.ae_eq_const_or_map_average_lt

--the jensens inequality is in lean both in its strict and non strict
--form
-- left to prove that two specific functions are strictly convex before proving maximal entropy
