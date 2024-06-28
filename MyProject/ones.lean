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
import Mathlib.Analysis.Subadditive



--fkt lemma is fully contained in lean
--and is described by the followinf theorems
#eval ENNReal.log 0 

#check Subadditive --definition
#check Subadditive.lim
#check Subadditive.tendsto_lim

--this version is catching up to the progress in one
-- but with measure theoretic defintion of cover
-- which calls for different definition of info

open MeasureTheory ENNReal Set Function BigOperators Finset

structure partition {α : Type*} (m : MeasurableSpace α) (μ : Measure α) [IsProbabilityMeasure μ] :=
  f : ℕ → Set α         -- A function from natural numbers to sets of terms in α
  measurable : ∀ n, MeasurableSet (f n)  -- Each set is measurable
  (disjoint : ∀ i j, i ≠ j → μ (f i ∩ f j) = 0)  -- The sets are pairwise disjoint
  (cover : μ (⋃ n, f n)ᶜ  = 0)  -- The union of all sets covers the entire space

structure finpart {α : Type*} (m : MeasurableSpace α) (μ : Measure α) [IsProbabilityMeasure μ] (n: ℕ):=
  (f : Fin n → Set α)          -- A function from finite sets of size n to sets of terms in α
  (measurable : ∀ i : Fin n, MeasurableSet (f i))  -- Each set is measurable
  (disjoint : ∀ i j, i ≠ j → μ (f i ∩ f j) = 0)  -- The sets are pairwise disjoint
  (cover : μ (⋃ i ∈ Finset.univ, f i)ᶜ  = 0)  -- The union of all sets covers the entire space  

lemma partcover {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ](p: partition m μ ):
μ (⋃ n, p.f n) = 1 := by
  exact (prob_compl_eq_zero_iff (MeasurableSet.iUnion fun b ↦ p.measurable b)).mp (p.cover)

lemma finpartcover  {α : Type*}  {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ](n:ℕ)(fp: finpart m μ n):
μ (⋃ i ∈ Finset.univ, fp.f i) = 1 := by
  exact (prob_compl_eq_zero_iff (measurableSet_biUnion Finset.univ (fun b a ↦ fp.measurable b))).mp fp.cover


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
    have h: ⋃ i ∈ Finset.univ, fp.f i ⊆ ⋃ n_1, (fun k ↦ if h : k < n then fp.f ⟨k, h⟩ else ∅) n_1 := by
      rintro x ⟨a,h',ha⟩; simp at h'
      rcases h' with ⟨s,hs⟩
      rw[mem_iUnion]; use s
      refine (mem_dite_empty_right (↑s < n) (fun h ↦ fp.f ⟨↑s, h⟩) x).mpr ?h.a
      · have h: s<n:= by
          exact s.isLt
        use h
        rw [← hs] at ha; exact ha
    exact measure_mono_null (compl_subset_compl_of_subset h) (fp.cover)    
        

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
    dsimp
    have h: (⋃ n, p1.f n) ∩ (⋃ n, p2.f n) ⊆ ⋃ n:ℕ , (p1.f n.unpair.1 ∩ p2.f n.unpair.2) := by
      intro x hx; cases' hx with h₁ h₂; rw[mem_iUnion] at *
      rcases h₁ with ⟨a,ha⟩; rcases h₂ with ⟨b,hb⟩
      use Nat.pairEquiv.toFun (a,b);
      simp [Nat.pairEquiv.left_inv (a,b)]
      exact ⟨ha,hb⟩
    have h₁: μ ((⋃ n, p1.f n) ∩ (⋃ n, p2.f n))ᶜ = 0 := by
      rw[Set.compl_inter]
      have h₁ := measure_union_le (μ := μ) ((⋃ n, p1.f n)ᶜ) ((⋃ n, p2.f n)ᶜ)
      have h₂ :  μ (⋃ n, p1.f n)ᶜ + μ (⋃ n, p2.f n)ᶜ = 0 := by
        simp only [p1.cover,p2.cover]; rw [add_zero]
    exact measure_mono_null (compl_subset_compl_of_subset h) h₁
}

noncomputable section

#check ENNReal.log
#check Real.log

--defining entropy and conditional entropy
-- need to choose whether to write entropy as a function to extended reals or
-- or send it to zero if the sum diverges
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


--useful lemmas for max_entropy

lemma addone {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
 (p : partition m μ) : (μ (⋃ i, p.f i)) = ∑' i , μ (p.f i) := by
  apply MeasureTheory.measure_iUnion₀
  · exact p.disjoint
  · intro i-- (h : MeasurableSet s) :
    exact  MeasurableSet.nullMeasurableSet (p.measurable i)
--Toreal? or no.

lemma addone' {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
(n : ℕ) (fp : finpart m μ n) : (μ (⋃ i ∈ Finset.univ, fp.f i)) = ∑ i ∈ Finset.univ, μ (fp.f i) := by
  apply MeasureTheory.measure_biUnion_finset₀
  · intro x _ s _ hxs
    exact fp.disjoint x s hxs
  · intro b _
    exact MeasurableSet.nullMeasurableSet (fp.measurable b)


lemma equiv {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
 (n : ℕ) (fp : finpart m μ n): (μ (⋃ i ∈ Finset.univ, fp.f i)).toReal =∑ i ∈ Finset.univ,(μ (fp.f i)).toReal := by
  have h: (∑ i ∈ Finset.univ,(μ (fp.f i))).toReal=∑ i ∈ Finset.univ,(μ (fp.f i)).toReal := by
    refine toReal_sum ?hf
    intro a _
    exact (measure_lt_top μ (fp.f a)).ne
  rw [← addone' n fp]  at h
  exact h

--one small issue



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
          rw[← equiv]; rw[finpartcover];simp
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
        sorry  
        apply (mul_lt_mul_left.mp (1 / (n : ℝ)) ((1 / ↑n).log_) ( ∑ i : Fin n, (μ (fp.f i)).toReal * (μ (fp.f i)).toReal.log) this).mp at h8



