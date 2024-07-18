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
import Mathlib.Analysis.SpecialFunctions.Log.ENNReal
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog



--fkt lemma is fully contained in lean
--and is described by the followinf theorems


#check Subadditive --definition
#check Subadditive.lim
#check Subadditive.tendsto_lim

--this version is catching up to the progress in one
-- but with measure theoretic defintion of cover
-- which calls for different definition of info.
-- all that is left is one small detail in max_ent and max_entropy
-- and dealing with case o funciton not being integrable, probably can prove it is integrable.

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
      rw[Set.compl_inter]; exact measure_union_null p1.cover p2.cover
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

#check StrictConvexOn.map_sum_lt
#check Finset.sum_congr
#check ENNReal.coe_div

--one piece missing, clean up

lemma max_ent {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
(n : ℕ) (fp : finpart m μ n)(h : ¬∀ (i : Fin n), μ (fp.f i) = 1 / ↑n) : Real.log ↑n > -∑ i : Fin n, (μ (fp.f i)).toReal * Real.log (μ (fp.f i)).toReal:= by
      push_neg at h
      rcases h with ⟨a,ha⟩
      simp [met_entropy']
      obtain (rfl | hn) := eq_zero_or_pos n
      · simp
        have h:= fp.cover
        have h₁: ⋃ i ∈ Finset.univ, fp.f i = ∅ := by
          exact iUnion_of_empty fun i => ⋃ (_ : i ∈ Finset.univ), fp.f i
        rw[h₁] at h
        have : μ ∅ᶜ=1 := by
          refine (prob_compl_eq_one_iff MeasurableSet.empty).mpr (OuterMeasureClass.measure_empty μ)
        rw [this] at h
        exact (one_ne_zero) h
      · have h0: n ≠ 0 := by linarith[hn]
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
        have h6: StrictConvexOn ℝ (Ici (0:ℝ)) φ := by
          exact Real.strictConvexOn_mul_log
        let t : Fin n → ℝ := λ i ↦ 1 / n
        have h7: φ ((∑ i in Finset.univ, (t i)*(μ (fp.f i)).toReal)) = φ ((∑ i in Finset.univ, 1/(n:ℝ)*(μ (fp.f i)).toReal)) := by
          exact rfl
        have h₀: ∀ i ∈ Finset.univ, 0 < t i := by
          intro j hj
          refine one_div_pos.mpr ?_
          exact Nat.cast_pos'.mpr hn
        have h₁: ∑ i, t i = 1 := by
          have: ∑ i, t i = ((∑ i in (Finset.univ : Finset (Fin n)),  1 / n) : ℝ ) := by
            apply Finset.sum_congr
            · rfl
            · intro x hx
              exact rfl
          rw[this,Finset.sum_const,Finset.card_univ]
          simp
          refine mul_inv_cancel ?_
          · exact Nat.cast_ne_zero.mpr h0
        have hmem: ∀ i ∈ Finset.univ, (μ (fp.f i)).toReal ∈ (Ici (0:ℝ)) := by
          intro i hi
          show (μ (fp.f i)).toReal ≥ 0
          exact toReal_nonneg
        have hp : ∃ j ∈ Finset.univ, ∃ k ∈ Finset.univ,(μ (fp.f j)).toReal ≠ (μ (fp.f k)).toReal:= by
          use a
          constructor
          · exact Finset.mem_univ a
          · by_contra h
            push_neg at h
            have:= equiv n fp
            have h1: ∑ i : Fin n, (μ (fp.f i)).toReal = ∑ i : Fin n, (μ (fp.f a)).toReal := by
              exact Eq.symm (sum_congr rfl h)
            rw[h1] at this
            have h2: ∑ i : Fin n, (μ (fp.f a)).toReal = n*(μ (fp.f a)).toReal:= by
              rw[Finset.sum_const,Finset.card_univ]; simp
            rw[h2] at this
            rw[finpartcover] at this
            simp at this
            have : (μ (fp.f a)) = 1 / n:= by
              refine (ENNReal.eq_div_iff ?ha ?ha').mpr ?_
              · exact Nat.cast_ne_zero.mpr h0
              · exact ENNReal.natCast_ne_top n
              · symm
                refine (toReal_eq_toReal_iff' ?hx ?hy).mp ?_
                · exact one_ne_top
                · refine mul_ne_top ?hy.a ?hy.b
                  · exact ENNReal.natCast_ne_top n
                  · exact measure_ne_top μ (fp.f a)
                · simp;assumption
            rw[this] at ha; exact ha rfl
        have := StrictConvexOn.map_sum_lt h6 h₀ h₁ hmem hp
        have h7: φ ((∑ i in Finset.univ, (t i)*(μ (fp.f i)).toReal)) = φ ((∑ i in Finset.univ, 1/(n:ℝ)*(μ (fp.f i)).toReal)) := by
          exact rfl
        have h8: φ ((∑ i in Finset.univ, (t i)*(μ (fp.f i)).toReal)) <  ∑ i in Finset.univ, (t i) * φ ((μ (fp.f i)).toReal) := by
          exact this
        have h9:  ∑ i in Finset.univ, (t i) * φ ((μ (fp.f i)).toReal) = ∑ i in Finset.univ, 1/(n:ℝ) * φ ((μ (fp.f i)).toReal):= by
          exact rfl
        rw[h7,h9,h5,h2,mul_one,← mul_sum] at h8;unfold φ at h8
        have : 0 < 1 / (n : ℝ) := by
          refine one_div_pos.mpr ?_
          exact Nat.cast_pos'.mpr hn
        apply (mul_lt_mul_left this).mp at h8
        simp
        have ht: (1 / ↑n:ℝ ) = (↑n)⁻¹ := by
          rw [inv_eq_one_div]
        have hs := Real.log_inv ↑n
        rw[← ht] at hs; rw[hs] at h8
        exact neg_lt_of_neg_lt h8


--one piece missing

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
    · have:= max_ent n fp h
      exact le_of_lt this
  · constructor
    · intro h; by_contra h₁
      have :  ¬∀ (i : Fin n), μ (fp.f i) = 1 / ↑n := by
        push_neg at *; rcases h₁ with ⟨a,ha⟩
        use a
        intro h'; rw[h'] at ha
        have: 0 ≤ ((1/n):ℝ) := by
          refine one_div_nonneg.mpr ?_
          · exact Nat.cast_nonneg' n
        have : ((1 / n):ENNReal).toReal = ((1 / n):ℝ) := by
          exact ENNReal.coe_toReal (1/n)

          have h₁: ((1/n):ENNReal) ≠ ⊤ := by
            sorry
          apply?
        exact ha this
      have:= max_ent n fp this
      simp[met_entropy'] at h
      rw[h] at this
      exact (lt_self_iff_false (Real.log ↑n)).mp this
    · intro h
      simp [met_entropy',h]
      rw[← mul_assoc]
      obtain (rfl | hn) := eq_zero_or_pos n
      · simp
      · simp [toReal_inv, mul_inv_cancel <| show (n : ℝ) ≠ 0 by norm_cast; linarith]




open scoped Classical

noncomputable section

def partition.partOf {α : Type*} {m : MeasurableSpace α} {μ : Measure α}  [IsProbabilityMeasure μ]
  (p : partition m μ ) (x : α)  : ℕ :=
  ite (x ∈ (⋃ n, p.f n)) (Classical.epsilon (λ n ↦ x ∈  p.f n)) 0

lemma partition.partOf_spec {α : Type*} {m : MeasurableSpace α} {μ : Measure α}[IsProbabilityMeasure μ]
    (p : partition m μ) (x : α) (hx : x ∈ ⋃ n, p.f n):
    x ∈ p.f (p.partOf x) := by
    unfold partition.partOf
    rw [if_pos hx]
    rw[mem_iUnion] at hx
    exact Classical.epsilon_spec hx

#eval ⊥ * (0:EReal)

lemma partition.partOf_spec' {α : Type*} {m : MeasurableSpace α} {μ : Measure α}[IsProbabilityMeasure μ]
    (p : partition m μ) (x : α): p.partOf x ≠ 0 → x ∈ p.f (p.partOf x):= by
    intro h
    refine partOf_spec p x ?hx
    by_contra h₁
    simp[partition.partOf, if_neg h₁] at h
    cases' h with h₂ h₃
    rcases h₂ with ⟨a,ha⟩
    have: x ∈ ⋃ n, p.f n := by
      rw[mem_iUnion]
      use a
    exact h₁ this


def info {α : Type*} {m : MeasurableSpace α} {μ : Measure α}  [IsProbabilityMeasure μ]
  (p : partition m μ ) (x : α): ℝ :=
  (-Real.log (μ (p.f (p.partOf x))).toReal)

-- in practice these functions don't matter whether they are undefined on a set of measure zero
-- so does it even matter if the definition would allow division by zero.

def cond_info {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (s : partition m μ) (x : α) :ℝ :=
  (-Real.log ((μ ((p.f (p.partOf x)) ∩ s.f (s.partOf x))).toReal/(μ (s.f (s.partOf x))).toReal))

end section


--this partition is a place holder for the Universal set
-- created to use connection between information and conditional information

def univ_partition {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]: partition m μ :=
{ f := λ k ↦ if k=0 then Set.univ else ∅
  measurable := by
    intro k
    by_cases h : k = 0
    · dsimp; rw[if_pos h]; exact MeasurableSet.univ
    · dsimp;rw[if_neg h];exact MeasurableSet.empty
  disjoint := by
    intro i j hij
    by_cases h: i=0
    · dsimp;rw[if_pos h]; rw[h] at hij; symm at hij;rw[if_neg hij]
      refine measure_inter_null_of_null_right Set.univ ?_;exact OuterMeasureClass.measure_empty μ
    · dsimp;rw[if_neg h]; have: μ ∅ =0:= by exact OuterMeasureClass.measure_empty μ
      exact measure_inter_null_of_null_left (if j = 0 then Set.univ else ∅) this
  cover := by
    have: (⋃ n, (fun k => if k = 0 then Set.univ else ∅) n) = Set.univ (α:=α) := by
      ext x
      constructor
      · exact fun a => trivial
      · intro h; rw[mem_iUnion]; use 0;exact h
    rw[this]
    have: (Set.univ (α:=α))ᶜ = ∅ := by
      exact Set.compl_univ
    rw[this]
    exact OuterMeasureClass.measure_empty μ
}

lemma univ_partition_partOf {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ](x:α):
  (univ_partition (μ:=μ)).partOf x = 0 := by
  by_contra h
  let a:ℕ := (univ_partition (μ:=μ)).partOf x
  have h₁: a=(univ_partition (μ:=μ)).partOf x := by
    rfl
  push_neg at h
  have h₂:= (univ_partition (μ:=μ)).partOf_spec' x h
  rw[← h₁] at h;rw[← h₁] at h₂;unfold univ_partition at h₂
  simp at h₂
  exact h h₂


lemma info_eq_condinfo_univ  {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ] (p: partition m μ):
info p = cond_info p univ_partition := by
  have: ∀ x, info p x = cond_info p univ_partition x := by
    intro x;unfold info
    unfold cond_info
    rw[univ_partition_partOf];
    unfold univ_partition;simp
  exact (eqOn_univ (info p) (cond_info p univ_partition)).mp fun ⦃x⦄ a => this x

lemma abc (a:ℝ)(b:ℝ)(h:a ≤ b)(h₁:0 ≤ a)(h₂:0 ≤ b):0 ≤ a/b := by
  exact div_nonneg h₁ h₂

lemma cond_info_nng {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ] (p: partition m μ)(s: partition m μ)(x:α):
0 ≤ cond_info p s x := by
  unfold cond_info
  have h: (μ (p.f (p.partOf x) ∩ s.f (s.partOf x))) ≤ (μ (s.f (s.partOf x))) := by
    refine measure_mono ?h
    · exact Set.inter_subset_right
  have h₁: (μ (p.f (p.partOf x) ∩ s.f (s.partOf x))).toReal ≤ (μ (s.f (s.partOf x))).toReal := by
    refine (toReal_le_toReal ?ha ?hb).mpr h
    ·exact measure_ne_top μ (p.f (p.partOf x) ∩ s.f (s.partOf x))
    · exact measure_ne_top μ (s.f (s.partOf x))
  have h₂: ((μ (p.f (p.partOf x) ∩ s.f (s.partOf x))).toReal / (μ (s.f (s.partOf x))).toReal) ≤ 1 := by
    refine  div_le_one_of_le h₁ ?_
    · exact toReal_nonneg
  have h₃ : 0 ≤ ((μ (p.f (p.partOf x) ∩ s.f (s.partOf x))).toReal / (μ (s.f (s.partOf x))).toReal) := by
    exact div_nonneg (toReal_nonneg) (toReal_nonneg)
  simp
  exact Real.log_nonpos h₃ h₂

lemma info_nng {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ] (p: partition m μ)(x:α):
0 ≤ info p x := by
  rw[info_eq_condinfo_univ]
  exact cond_info_nng p univ_partition x


--complement singleton, e1 and e2 are lemmas building the statement of
-- the partition.partOf_eq_ae
lemma countable_complement_singleton  (n : ℕ ) :

--these two are equivalent
  Set.Countable {i | i ≠ n} := by
  apply Set.countable_iff_exists_injective.mpr
  use (λ x => x)
  · intro x y hxy
    dsimp at hxy; ext; exact hxy

lemma countable_complement_singleton'  (n : ℕ ) :
  Set.Countable fun i => i = n → False := by
  apply Set.countable_iff_exists_injective.mpr
  use (λ x => x)
  · intro x y hxy
    dsimp at hxy; ext; exact hxy


lemma e1 {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    (p : partition m μ) (n : ℕ): (p.f n)\((p.partOf) ⁻¹' {n}) ⊆  ⋃ (i : ℕ) (h: i ≠ n), (p.f n ∩ p.f i) := by
  intro x hx
  have h: p.partOf x ≠ n := by
    have h' := hx.2
    by_contra h_eq
    exact h' h_eq
  let n' := p.partOf x
  rw [Set.mem_iUnion]
  use n'
  rw [Set.mem_iUnion]
  have h_ne: n' ≠ n := by
    intro h_eq
    rw [← h_eq] at h
    contradiction
  use h_ne
  exact ⟨hx.1, p.partOf_spec x (mem_iUnion_of_mem n hx.1)⟩


lemma e2 {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    (p : partition m μ) (n : ℕ): μ (⋃ (i : ℕ) (h: i ≠ n), (p.f n ∩ p.f i)) = 0 := by
  refine (measure_biUnion_null_iff ?hI).mpr ?_
  · exact (countable_complement_singleton n)
  · intro s h
    exact ((p.disjoint n s) (fun a => h (id (Eq.symm a))))

lemma e3 {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    (p : partition m μ) (n : ℕ) : p.partOf ⁻¹' {n} \ p.f n ⊆ (⋃ n, p.f n)ᶜ := by
    intro x hx; show x ∉ (⋃ n, p.f n)
    intro h; have h1:= p.partOf_spec x h
    have: p.partOf x= n:= hx.1; rw[this] at h1
    exact hx.2 h1


lemma partition.partOf_eq_ae {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    (p : partition m μ) (n : ℕ) :
    (p.partOf) ⁻¹' {n} =ᵐ[μ] p.f n := by
    have h: μ (p.f n \ p.partOf ⁻¹' {n})=0 := by
      exact measure_mono_null (e1 _ _) (e2 _ _)
    have h₁: μ ( p.partOf ⁻¹' {n} \ p.f n) = 0 := measure_mono_null (e3 p n) (p.cover)
    have : μ ((p.partOf ⁻¹' {n} \ p.f n) ∪ (p.f n \ p.partOf ⁻¹' {n})) = 0 := by
      exact measure_union_null h₁ h
    exact measure_symmDiff_eq_zero_iff.mp this

--eqset₀,eqset₀,eqset₁,eqset₂,eqset₃ and pre_info_ae_eq are building blocks of info_ae_eq
--turns out they obsolete for info_ae_eq but I use these often in other places.

def eqset₀ {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    (p : partition m μ) : ℕ → Set α :=
  λ n ↦ p.f n \ (⋃ (i : ℕ) (h: i ≠ n), (p.f i))

def eqset  {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    (p : partition m μ): Set α :=
  ⋃ (i : ℕ), eqset₀ p i

lemma eqset₁  {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    (p : partition m μ): ⋂ i, (eqset₀ p i)ᶜ ⊆ (⋃ (n : ℕ), ⋃ (i : ℕ)(h: i ≠ n), (p.f n ∩ p.f i)) ∪ (⋃ n, p.f n)ᶜ := by
    intro x hx
    by_cases h: x ∈ (⋃ n, p.f n)
    · let s: ℕ := Exists.choose (mem_iUnion.mp h)
      rw[Set.mem_iInter] at hx
      have h₁:= hx s
      unfold eqset₀ at h₁; rw[Set.diff_eq,Set.compl_inter,compl_compl] at h₁
      have h₂: x ∈ p.f s := Exists.choose_spec (mem_iUnion.mp h)
      cases' h₁ with h₃ h₃
      · exfalso; exact h₃ h₂
      · left;rw[mem_iUnion] at *; rcases h₃ with ⟨a,A,c,d⟩;use s
        simp at c
        rw[mem_iUnion]; use a
        refine mem_iUnion.mpr ?h.a
        have h10 : a ≠ s := by
          by_contra h
          tauto
        rw[← c.2 ] at d
        use h10
        exact ⟨h₂,d⟩
    right
    assumption




lemma eqset₂  {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    (p : partition m μ) : μ (⋃ (n : ℕ),( ⋃ (i : ℕ)(h: i ≠ n), (p.f n ∩ p.f i))) = 0 := by
    apply measure_iUnion_null_iff.mpr;intro i;exact (e2 p i)


lemma eqset₃ {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    (p : partition m μ): μ (eqset p)ᶜ  = 0 := by
    unfold eqset; simp
    exact measure_mono_null (eqset₁ p) (measure_union_null (eqset₂ p) (p.cover))

lemma eqset₀_measurable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
 (p : partition m μ) (i : ℕ): MeasurableSet (eqset₀ p i):= by
  unfold eqset₀
  refine MeasurableSet.diff ?h₁ ?h₂
  · exact p.measurable i
  · refine MeasurableSet.biUnion ?h₂.hs ?h₂.h
    · exact countable_complement_singleton i
    · intro c _
      exact p.measurable c


lemma eqset_measurable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
 (p : partition m μ): MeasurableSet (eqset p) := by
  unfold eqset;unfold eqset₀
  refine MeasurableSet.iUnion ?h
  intro b
  refine MeasurableSet.diff ?h.h₁ ?h.h₂
  exact p.measurable b
  refine MeasurableSet.biUnion ?h.h₂.hs ?h.h₂.h
  · exact countable_complement_singleton b
  · intro c _
    exact p.measurable c

lemma eqset₀_partOf {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
 (p : partition m μ) (x: α)(n:ℕ ): x ∈ eqset₀ p n → p.partOf x = n :=  by
  intro h
  unfold eqset₀ at h
  by_contra h₁
  push_neg at h₁
  let j:= p.partOf x
  have : j= p.partOf x := by
    exact rfl
  rw[← this] at h₁
  have: x ∈  ⋃ i, ⋃ (_ : i ≠ n), p.f i := by
    rw[mem_iUnion]
    use j
    rw[mem_iUnion]; use h₁
    refine partition.partOf_spec p x ?h.hx
    · rw[mem_iUnion];use n; exact h.1
  exact h.2 this

  lemma eqset₀_measure  {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
 (p : partition m μ)(n:ℕ ) : μ (p.f n \ eqset₀ p n) = 0 := by
    have: (p.f n \ eqset₀ p n) ⊆ (⋃ (n : ℕ), ⋃ (i : ℕ)(h: i ≠ n), (p.f n ∩ p.f i)) := by
      intro x ⟨hx₁,hx₂⟩
      unfold eqset₀ at hx₂
      simp at hx₂
      have hx₃:= hx₂ hx₁
      rcases hx₃ with ⟨j,⟨hj₁,hj₂⟩⟩
      rw[mem_iUnion]
      use j;rw[mem_iUnion]
      push_neg at hj₁; symm at hj₁;use n;rw[mem_iUnion]; use hj₁
      exact Set.mem_inter hj₂ hx₁
    exact measure_mono_null this (eqset₂ p)



lemma info_eq {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    (p : partition m μ) :
    info (μ := μ) p = fun x ↦ ∑' n, (p.partOf ⁻¹' {n}).indicator (fun _ ↦ (-Real.log (μ (p.f n)).toReal)) x := by
    ext x;  let N := p.partOf x
    have h₁: ∑' (n : ℕ), (p.partOf ⁻¹' {n}).indicator (fun _ => -(μ (p.f n)).toReal.log) x = (p.partOf ⁻¹' {N}).indicator (fun _ => -(μ (p.f N)).toReal.log) x := by
      apply tsum_eq_single
      intro b hbn
      exact indicator_of_not_mem (id (Ne.symm hbn)) fun _ => -(μ (p.f b)).toReal.log
    rw[h₁]
    exact Eq.symm (indicator_of_mem rfl fun _ => -(μ (p.f N)).toReal.log)

lemma info_measurable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    (p : partition m μ): MeasureTheory.StronglyMeasurable (info p)  := by
    rw[info_eq]
    refine Continuous.comp_stronglyMeasurable ?hg ?hf
    ·





#check setIntegral_const


lemma should_this_be_in_the_library
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {ι : Type*} [Countable ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {As : ι → Set X} (As_mble : ∀ i, NullMeasurableSet (As i) μ)
    (As_disj : Pairwise (AEDisjoint μ on As))
    {f : X → E} (f_intble : IntegrableOn f (⋃ i, As i) μ)
    {cs : ι → E} (f_ae_loc_cst : ∀ i, f =ᵐ[μ.restrict (As i)] fun _ ↦ cs i) :
    ∫ x in (⋃ i, As i), f x ∂μ = ∑' i, (μ (As i)).toReal • cs i := by
  rw [integral_iUnion_ae (μ := μ) (s := As) As_mble As_disj f_intble]
  congr; funext i
  simpa [setIntegral_const (cs i)] using
    setIntegral_congr_ae₀ (g := fun _ ↦ cs i) (s := As i) (μ := μ) (As_mble i)
      (ae_imp_of_ae_restrict (f_ae_loc_cst i))


#check lintegral_mono
#check MeasureTheory.integral_iUnion_ae
#check MeasureTheory.setIntegral_congr_ae -- equivalence between integral of function ae equal
#check MeasureTheory.setIntegral_const --integral of a constant
#check measure_union

--lemma necessary for ent_inf

--one piece mssing from lent_inf

lemma lentinf {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    (p : partition m μ) (n: ℕ ) : μ (eqset₀ p n) = 0 → μ (p.f n)=0 := by
    intro h
    have h' : eqset₀ p n ⊆  p.f n := by
      simp[eqset₀]; exact diff_subset
    have h'':= eqset₀_measure p n
    have h''': p.f n = eqset₀ p n ∪ p.f n \ eqset₀ p n := by
      exact Eq.symm (union_diff_cancel' (fun ⦃a⦄ a => a) h')
    have h_eq : μ (p.f n) = μ (eqset₀ p n) + μ (p.f n \ eqset₀ p n) := by
      nth_rewrite 1[h''']
      rw[add_comm,Set.union_comm]
      exact (measure_union disjoint_sdiff_left) (eqset₀_measurable p n)
    simp [h,h''] at h_eq; exact h_eq

--Several things have changed, can try again bochner or lebesgue

#check Measure.restrict_apply_eq_zero'
theorem setIntegral_eq_zero_of_measure_eq_zero {α : Type*} {m : MeasurableSpace α} {μ : Measure α}{t: Set α}{f:α →ℝ}(ht : μ t = 0) :
    ∫ x in t, f x ∂μ = 0 := by
  simp [Measure.restrict_eq_zero.mpr ht]


#check Measure.restrict_apply_eq_zero'
#check integrable_congr

theorem ent_inf {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ](p : partition m μ) :
    met_entropy p = ∫ x, info p x ∂μ := by
  by_cases junk : ¬ Integrable (info (μ := μ) p) μ
  · simp [integral_undef junk]
    sorry -- You should prove that your `tsum` defining `info` has the same junk value as `integral`
  rw[info_eq]
  simp only [not_not, (info_eq p)] at junk
  unfold met_entropy
  have h := p.cover
  have : ∫ (a : α), ∑' (n : ℕ), (p.partOf ⁻¹' {n}).indicator (fun x => -(μ (p.f n)).toReal.log) a ∂μ =
    ∫ (a : α) in ⋃ n, p.f n, ∑' (n : ℕ), (p.partOf ⁻¹' {n}).indicator (fun x => -(μ (p.f n)).toReal.log) a ∂μ := by
    have:  ∫ (a : α), ∑' (n : ℕ), (p.partOf ⁻¹' {n}).indicator (fun x => -(μ (p.f n)).toReal.log) a ∂μ =
    (∫ (a : α) in ⋃ n, p.f n, ∑' (n : ℕ), (p.partOf ⁻¹' {n}).indicator (fun x => -(μ (p.f n)).toReal.log) a ∂μ)+(∫ (a : α) in (⋃ n, p.f n)ᶜ, ∑' (n : ℕ), (p.partOf ⁻¹' {n}).indicator (fun x => -(μ (p.f n)).toReal.log) a ∂μ) := by
      refine Eq.symm (integral_add_compl ?hs junk)
      · refine MeasurableSet.iUnion ?hs.h
        · exact fun b => p.measurable b
    rw[this]
    have: ∫ (a : α) in (⋃ n, p.f n)ᶜ, ∑' (n : ℕ), (p.partOf ⁻¹' {n}).indicator (fun x => -(μ (p.f n)).toReal.log) a ∂μ=0:= by
      exact setIntegral_eq_zero_of_measure_eq_zero h
    rw[this,add_zero]
  rw[this]
  let c: ℕ → ℝ := λ n ↦ -(μ (p.f n)).toReal.log
  have h₂: ∫ (a : α) in ⋃ n, p.f n, ∑' (n : ℕ), (p.partOf ⁻¹' {n}).indicator (fun x => -(μ (p.f n)).toReal.log) a ∂μ =
  ∑' (i : ℕ), (μ (p.f i)).toReal • c i := by
    refine' (should_this_be_in_the_library _ _ _ _ _)
    · exact fun i => MeasurableSet.nullMeasurableSet (p.measurable i)
    · exact p.disjoint
    · rw [← MeasureTheory.integrableOn_univ] at junk
      have: (⋃ i, p.f i) ⊆ Set.univ:= by
        exact fun ⦃a⦄ a => trivial
      refine MeasureTheory.IntegrableOn.mono_set junk this
    · intro i
      show (μ.restrict (p.f i)) {x | ∑' (n : ℕ), (p.partOf ⁻¹' {n}).indicator (fun x => -Real.log (μ (p.f n)).toReal) x = c i}ᶜ = 0
      have  hs :eqset₀ p i⊆ {x | ∑' (n : ℕ), (p.partOf ⁻¹' {n}).indicator (fun x => -Real.log (μ (p.f n)).toReal) x = c i} := by
        intro j hj
        show ∑' (n : ℕ), (p.partOf ⁻¹' {n}).indicator (fun x => -Real.log (μ (p.f n)).toReal) j = c i
        have: ∀ n:ℕ, n ≠ i → (p.partOf ⁻¹' {n}).indicator (fun x => -Real.log (μ (p.f n)).toReal) j = 0 := by
          intro n hn
          have : j ∉ (p.partOf ⁻¹' {n}) := by
            by_contra h
            have h: p.partOf j = n := by
              exact h
            unfold eqset₀ at hj
            cases' hj with hj₁ hj₂
            rw[mem_iUnion] at hj₂; push_neg at hj₂
            have:= hj₂ n
            rw[mem_iUnion] at this; push_neg at this
            have h10: j ∉ p.f n := this hn
            have : j ∈ ⋃ n, p.f n := by
              exact mem_iUnion_of_mem i hj₁
            have := p.partOf_spec j this
            rw[h] at this
            exact h10 this
          exact indicator_of_not_mem this fun x => -Real.log (μ (p.f n)).toReal
        have:=  tsum_eq_single i this
        rw[this]
        simp only [c]
        exact indicator_of_mem (eqset₀_partOf p j i hj) fun x => -Real.log (μ (p.f i)).toReal
      have h':= compl_subset_compl_of_subset hs
      have : (μ.restrict (p.f i)) (eqset₀ p i)ᶜ = 0 := by
        refine (Measure.restrict_apply_eq_zero' (p.measurable i)).mpr ?_
        · rw [Set.inter_comm]
          exact (eqset₀_measure p i)
      exact measure_mono_null h' this
  rw[h₂]; rw[← tsum_neg]; apply tsum_congr
  intro r; simp [c]






theorem condent_inf {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ](p : partition m μ)(s : partition m μ) :
    conmet_entropy p s = ∫ x, cond_info p s x ∂μ := by
    sorry

lemma info_add₀  {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (s : partition m μ) (x : α): x ∈ eqset p ∩ eqset s → x ∈ (refine_partition p s).f ((refine_partition p s).partOf x) := by
    intro ⟨hx₁,hx₂⟩;simp [eqset] at *
    rcases hx₁ with ⟨a,ha⟩;rcases hx₂ with ⟨b,hb⟩
    refine partition.partOf_spec (refine_partition p s) x ?hx
    rw[mem_iUnion]; use Nat.pairEquiv.toFun (a,b)
    have: (refine_partition p s).f (Nat.pairEquiv.toFun (a, b)) = p.f (Nat.pairEquiv.invFun (Nat.pairEquiv.toFun (a, b))).1 ∩ s.f (Nat.pairEquiv.invFun (Nat.pairEquiv.toFun (a, b))).2 := by
      exact rfl
    rw[this]
    simp
    exact ⟨mem_of_mem_diff ha,mem_of_mem_diff hb⟩



lemma info_add₁  {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (s : partition m μ) : eqset p ∩ eqset s ⊆ {x | (refine_partition p s).f ((refine_partition p s).partOf x) = p.f (p.partOf x) ∩ s.f (s.partOf x)} := by
  intro x' hx
  have h₀ := info_add₀ p s x' hx
  simp[eqset] at *; rcases hx.1 with ⟨a,ha⟩;rcases hx.2 with ⟨b,hb⟩
  have hx₁:=ha;have hx₂:=hb
  apply eqset₀_partOf at ha; apply  eqset₀_partOf at hb
  have : (refine_partition p s).f ((refine_partition p s).partOf x') = p.f (Nat.pairEquiv.invFun  ((refine_partition p s).partOf x')).1  ∩ s.f  (Nat.pairEquiv.invFun  ((refine_partition p s).partOf x')).2 := by
    exact rfl
  rw[this];
  rw[ha,hb]
  have h₁:  (Nat.pairEquiv.invFun ((refine_partition p s).partOf x')).1 = a:= by
    by_contra h
    unfold eqset₀ at hx₁
    let c:ℕ := (Nat.pairEquiv.invFun ((refine_partition p s).partOf x')).1
    have h₁ : c = (Nat.pairEquiv.invFun ((refine_partition p s).partOf x')).1 := by
      rfl
    push_neg at h;rw[← h₁] at h
    have h₂: x' ∈  ⋃ i, ⋃ (_ : i ≠ a), p.f i := by
      rw[mem_iUnion]; use c;rw[mem_iUnion]; use h; exact Set.mem_of_mem_inter_left h₀
    exact hx₁.2 h₂
  have h₂:  (Nat.pairEquiv.invFun ((refine_partition p s).partOf x')).2 = b:= by
    by_contra h
    unfold eqset₀ at hx₂
    let d:ℕ := (Nat.pairEquiv.invFun ((refine_partition p s).partOf x')).2
    have h₁ : d = (Nat.pairEquiv.invFun ((refine_partition p s).partOf x')).2 := by
      rfl
    push_neg at h;rw[← h₁] at h
    have h₂: x' ∈  ⋃ i, ⋃ (_ : i ≠ b), s.f i := by
      rw[mem_iUnion]; use d;rw[mem_iUnion]; use h; exact Set.mem_of_mem_inter_right h₀
    exact hx₂.2 h₂
  rw[h₁,h₂]

lemma info_add₂  {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (s : partition m μ) : (λ x ↦ ((refine_partition p s).f ((refine_partition p s).partOf x))) =ᵐ[μ] λ x ↦ ((p.f (p.partOf x)) ∩ (s.f (s.partOf x))) := by
  have h:= info_add₁ p s
  have h₁:= compl_subset_compl_of_subset h
  have h₂ : μ (eqset p ∩ eqset s)ᶜ=0 := by
    rw[Set.compl_inter]
    exact measure_union_null (eqset₃ p) (eqset₃ s)
  exact measure_mono_null h₁ h₂

lemma mul_div_real (a:ℝ) (b:ℝ)(h:b≠0) : a = b * a/b := by
  exact Eq.symm (mul_div_cancel_left₀ a h)


def condeqset {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) : Set α:= (⋃ n, p.f n) \ (⋃ n, if (μ (p.f n)).toReal = 0 then p.f n else ∅)

lemma condeqset_measurable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ): MeasurableSet (condeqset p) := by
  unfold condeqset
  refine MeasurableSet.diff ?h₁ ?h₂
  · exact MeasurableSet.iUnion fun b => p.measurable b
  · refine MeasurableSet.iUnion ?h₂.h
    · intro B
      by_cases h:(μ (p.f B)).toReal = 0
      · rw[if_pos h];exact p.measurable B
      · rw[if_neg h]; exact MeasurableSet.empty

  lemma condeqset_measure_zero {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ): μ (condeqset p)ᶜ=0 := by
  unfold condeqset
  show μ ((⋃ n, p.f n) ∩ (⋃ n, if (μ (p.f n)).toReal = 0 then p.f n else ∅)ᶜ)ᶜ = 0
  rw[Set.compl_inter]
  refine measure_union_null p.cover ?ht
  · simp;intro i
    by_cases h:(μ (p.f i)).toReal = 0
    · rw[if_pos h]
      refine Eq.symm ((fun {x y} hx hy => (toReal_eq_toReal_iff' hx hy).mp) ?_ ?_ (id (Eq.symm h)))
      ·exact Ne.symm top_ne_zero
      ·exact measure_ne_top μ (p.f i)
    · rw[if_neg h]; exact OuterMeasureClass.measure_empty μ

  lemma condeqset_members {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ)(x:α): x ∈ (condeqset p) → (μ (p.f (p.partOf x))).toReal ≠ 0 := by
  intro h
  by_contra h₁
  unfold condeqset at h
  have h₂: x ∈ ⋃ n, if (μ (p.f n)).toReal = 0 then p.f n else ∅:= by
    rw[mem_iUnion]
    use p.partOf x
    rw[if_pos h₁];exact partition.partOf_spec p x h.1
  exact h.2 h₂

lemma info_add₃ {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (s : partition m μ): (eqset p) ∩ (eqset s) ∩ (condeqset s ∩ condeqset (refine_partition p s)) ⊆ {x | info (refine_partition p s) x = (info s x)  + (cond_info p s x)} := by
  intro x ⟨hx₁,⟨hx₂,hx₃⟩⟩
  show info (refine_partition p s) x = (info s x)  + (cond_info p s x)
  have  h:= info_add₁ p s hx₁
  simp at h
  have h₁:=condeqset_members s x hx₂
  have h₂:= condeqset_members (refine_partition p s) x hx₃
  rw[h] at h₂
  have h₃:(μ (p.f (p.partOf x) ∩ s.f (s.partOf x))).toReal= (μ (s.f (s.partOf x))).toReal * (μ (p.f (p.partOf x) ∩ s.f (s.partOf x))).toReal /(μ (s.f (s.partOf x))).toReal := by
    exact Eq.symm (mul_div_cancel_left₀ ((μ (p.f (p.partOf x) ∩ s.f (s.partOf x))).toReal) h₁)
  have h₄: (μ (p.f (p.partOf x) ∩ s.f (s.partOf x))).toReal /(μ (s.f (s.partOf x))).toReal ≠ 0 := by
    exact div_ne_zero h₂ h₁
  unfold info; unfold cond_info;rw[h];nth_rewrite 1[h₃]
  rw[neg_eq_neg_one_mul]
  have h₅:= Real.log_mul h₁ h₄
  have : ((μ (s.f (s.partOf x))).toReal *
      ((μ (p.f (p.partOf x) ∩ s.f (s.partOf x))).toReal / (μ (s.f (s.partOf x))).toReal)) = ((μ (s.f (s.partOf x))).toReal * (μ (p.f (p.partOf x) ∩ s.f (s.partOf x))).toReal /
        (μ (s.f (s.partOf x))).toReal) := by
      exact
        Eq.symm
          (mul_div_assoc (μ (s.f (s.partOf x))).toReal
            (μ (p.f (p.partOf x) ∩ s.f (s.partOf x))).toReal (μ (s.f (s.partOf x))).toReal)
  rw[this] at h₅; linarith [h₅]


lemma info_add_conduniv {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (s : partition m μ) : info (refine_partition p s)=ᵐ[μ] info s + cond_info p s:= by
  have h:= info_add₃ p s
  show μ  {x | info (refine_partition p s) x = info s x + cond_info p s x}ᶜ = 0
  have h₁:= compl_subset_compl_of_subset h
  refine measure_mono_null h₁ ?_
  · rw[Set.compl_inter]
    refine measure_union_null ?hs ?ht
    · rw[Set.compl_inter]
      exact measure_union_null (eqset₃ p) (eqset₃ s)
    · rw[Set.compl_inter]
      exact measure_union_null (condeqset_measure_zero s) (condeqset_measure_zero (refine_partition p s))



lemma info_add₄ {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (s : partition m μ) (t : partition m μ): eqset (refine_partition p s) ∩ eqset t ⊆
  {x | (refine_partition (refine_partition p s) t).f ((refine_partition (refine_partition p s) t).partOf x)=(refine_partition p s).f ((refine_partition p s).partOf x) ∩ t.f (t.partOf x)} := by
  exact info_add₁ (refine_partition p s) t

lemma info_add₅ {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (s : partition m μ) (t : partition m μ): eqset (refine_partition p s) ∩ eqset t ∩ (eqset p ∩ eqset s) ⊆
 {x | (refine_partition (refine_partition p s) t).f ((refine_partition (refine_partition p s) t).partOf x)= p.f (p.partOf x) ∩ s.f (s.partOf x) ∩ t.f (t.partOf x)} := by
 intro x ⟨hx₁,hx₂⟩
 have h₁:= info_add₁ (refine_partition p s) t hx₁
 have h₂:= info_add₁ p s hx₂
 simp at h₁ h₂; simp
 rw[h₁,h₂]


lemma info_add₆ {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (s : partition m μ) (t : partition m μ): eqset p ∩ eqset (refine_partition s t) ∩ (eqset s ∩ eqset t) ⊆
 {x | (refine_partition p (refine_partition s t) ).f ((refine_partition p (refine_partition s t)).partOf x)= p.f (p.partOf x) ∩ s.f (s.partOf x) ∩ t.f (t.partOf x)} := by
 intro x ⟨hx₁,hx₂⟩
 have h₁:= info_add₁ p (refine_partition s t) hx₁
 have h₂:= info_add₁ s t hx₂
 simp at h₁ h₂; simp
 rw[h₁,h₂]


lemma preinfo_add {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (s : partition m μ) (t : partition m μ) : eqset p ∩ eqset s ∩ eqset t ∩ eqset (refine_partition p s) ∩ eqset (refine_partition s t) ∩ condeqset (refine_partition (refine_partition p s) t) ∩  condeqset (refine_partition p (refine_partition s t) ) ∩ condeqset t ∩ condeqset (refine_partition s t)⊆
  {x | cond_info (refine_partition p s) (t) x = (cond_info s t) x + cond_info (p) (refine_partition s t) x} := by
  intro x ⟨⟨⟨⟨⟨⟨⟨⟨hx₁,hx₂⟩,hx₃⟩,hx₄⟩,hx₅⟩,hx₆⟩,hx₇⟩,hx₈⟩,hx₉⟩; simp
  unfold cond_info
  rw[(info_add₁ p s ⟨hx₁,hx₂⟩),info_add₁ s t ⟨hx₂,hx₃⟩]
  have h₁:= condeqset_members t x hx₈
  have h₂:=  condeqset_members (refine_partition s t) x hx₉
  have h₃:=  condeqset_members (refine_partition (refine_partition p s) t) x hx₆
  have h₄:= condeqset_members (refine_partition p (refine_partition s t)) x hx₇
  rw[info_add₁ s t ⟨hx₂,hx₃⟩] at h₂
  rw[info_add₄ p s t ⟨hx₄,hx₃⟩,(info_add₁ p s ⟨hx₁,hx₂⟩)] at h₃
  rw[info_add₆ p s t ⟨⟨hx₁,hx₅⟩,⟨hx₂,hx₃⟩⟩] at h₄
  rw [neg_eq_neg_one_mul (Real.log ((μ (s.f (s.partOf x) ∩ t.f (t.partOf x))).toReal / (μ (t.f (t.partOf x))).toReal)), neg_eq_neg_one_mul (Real.log
        ((μ (p.f (p.partOf x) ∩ (s.f (s.partOf x) ∩ t.f (t.partOf x)))).toReal /
          (μ (s.f (s.partOf x) ∩ t.f (t.partOf x))).toReal))]
  have h₅: ((μ (s.f (s.partOf x) ∩ t.f (t.partOf x))).toReal / (μ (t.f (t.partOf x))).toReal) ≠ 0:= by
    exact div_ne_zero h₂ h₁
  have h₆:(μ (p.f (p.partOf x) ∩ (s.f (s.partOf x) ∩ t.f (t.partOf x)))).toReal /
          (μ (s.f (s.partOf x) ∩ t.f (t.partOf x))).toReal ≠ 0 := by
    rw[Set.inter_assoc] at h₃
    simp [div_ne_zero h₃ h₂]
  rw[← LeftDistribClass.left_distrib,← Real.log_mul h₅ h₆,Set.inter_assoc,neg_eq_neg_one_mul]
  have: ((μ (s.f (s.partOf x) ∩ t.f (t.partOf x))).toReal / (μ (t.f (t.partOf x))).toReal *
        ((μ (p.f (p.partOf x) ∩ (s.f (s.partOf x) ∩ t.f (t.partOf x)))).toReal /
          (μ (s.f (s.partOf x) ∩ t.f (t.partOf x))).toReal))=((μ (p.f (p.partOf x) ∩ (s.f (s.partOf x) ∩ t.f (t.partOf x)))).toReal / (μ (t.f (t.partOf x))).toReal) := by
        rw[mul_comm,div_eq_mul_one_div,div_eq_mul_one_div (((μ (s.f (s.partOf x) ∩ t.f (t.partOf x))).toReal)) _]
        rw[mul_assoc,← mul_assoc (1 / (μ (s.f (s.partOf x) ∩ t.f (t.partOf x))).toReal)]
  rw[this]

lemma measure_zero_info {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (s : partition m μ) (t : partition m μ): μ
    (eqset p ∩ eqset s ∩ eqset t ∩ eqset (refine_partition p s) ∩ eqset (refine_partition s t) ∩
              condeqset (refine_partition (refine_partition p s) t) ∩
            condeqset (refine_partition p (refine_partition s t)) ∩
          condeqset t ∩
        condeqset (refine_partition s t))ᶜ = 0 := by
   rw[Set.compl_inter]
   refine measure_union_null ?_ ?_
   · rw[Set.compl_inter]
     refine measure_union_null ?_ ?_
     · rw[Set.compl_inter]
       refine measure_union_null ?_ ?_
       · rw[Set.compl_inter]
         refine measure_union_null ?_ ?_
         · rw[Set.compl_inter]
           refine measure_union_null ?_ ?_
           · rw[Set.compl_inter]
             refine measure_union_null ?_ ?_
             · rw[Set.compl_inter]
               refine measure_union_null ?_ ?_
               · rw[Set.compl_inter]
                 refine measure_union_null ?_ ?_
                 · exact eqset₃ p
                 · exact eqset₃ s
               · exact eqset₃ t
             · exact eqset₃ (refine_partition p s)
           · exact eqset₃ (refine_partition s t)
         · exact condeqset_measure_zero (refine_partition (refine_partition p s) t)
       · exact condeqset_measure_zero (refine_partition p (refine_partition s t))
     · exact condeqset_measure_zero t
   · exact condeqset_measure_zero (refine_partition s t)


theorem info_add {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (s : partition m μ) (t : partition m μ) :
  cond_info (refine_partition p s) (t) =ᵐ[μ] (cond_info s t) + cond_info (p) (refine_partition s t) := by
  show μ {x | cond_info (refine_partition p s) (t) x = (cond_info s t) x + cond_info (p) (refine_partition s t) x}ᶜ=0
  have h:=  preinfo_add p s t
  have h₁:=  compl_subset_compl_of_subset h
  exact measure_mono_null h₁ (measure_zero_info p s t)


theorem entro_add {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (s : partition m μ) (t : partition m μ) : conmet_entropy (refine_partition p s) (t) = (conmet_entropy s t) + conmet_entropy (p) (refine_partition s t):= by
  rw[(condent_inf (refine_partition p s) (t)),(condent_inf s t), (condent_inf (p) (refine_partition s t))]
  have h:= info_add p s t
  rw [integral_congr_ae (info_add p s t)]
  apply?



theorem info_monoton_increasing_meas_part  {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (s : partition m μ) (t : partition m μ) : cond_info s t ≤ᵐ[μ] cond_info (refine_partition p s) t := by
  show μ {x | cond_info s t x ≤ cond_info (refine_partition p s) t x}ᶜ=0
  have h: eqset p ∩ eqset s ∩ eqset t ∩ eqset (refine_partition p s) ∩ eqset (refine_partition s t) ∩
              condeqset (refine_partition (refine_partition p s) t) ∩
            condeqset (refine_partition p (refine_partition s t)) ∩
          condeqset t ∩
        condeqset (refine_partition s t) ⊆  {x | cond_info s t x ≤ cond_info (refine_partition p s) t x}:= by
        intro x hx
        have h₁:= preinfo_add p s t hx
        have h₂:= cond_info_nng (p) (refine_partition s t) x
        simp; simp at h₁
        linarith
  have h₁:=  compl_subset_compl_of_subset h
  exact measure_mono_null h₁ (measure_zero_info p s t)

theorem entro_monoton_increasing_meas_part  {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (s : partition m μ) (t : partition m μ) : conmet_entropy s t ≤ conmet_entropy (refine_partition p s) t:= by
  rw[condent_inf]
  have h :=info_monoton_increasing_meas_part p s t
  apply?
