
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


--defining partition given measure, disjointness defined measure-theoretically
-- cover for now is defined in the set-theoretic sense,
-- could change but many lemmas would be harder
--this change could be written as measure of union is 1, measure of complement is zero
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

-- different definitions of finite partitions, little detail changed for convenience

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
  cover:= by -- simple the union is same set so same measure
    ext x
    constructor
    · tauto
    · intro h;dsimp; rw[← fp.cover] at h; rcases mem_iUnion.mp h with ⟨a, ha⟩
      rw[mem_iUnion]
      rcases mem_iUnion.mp ha with ⟨b, hb⟩
      use a; simp only [dif_pos a.is_lt]; exact hb




--defining function that takes two partitions and gives the refinement partition
-- what are points that would be included all points that are covered by both
-- need to show that the set of point that lie at most in one of them has measure zero
-- first the set of points not covered by first one, then set of points not covered by the second one
--that's it.

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

#check ENNReal.log
#check Real.log

--defining entropy and conditional entropy
-- need to choose whether to write entropy as a function to extended reals or
-- or send it to zero if the sum diverges

--def met_entropy {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  --(p : partition m μ) : ℝ≥0∞ :=
 -- ∑' (n : ℕ),
 --   (μ (p.f n))



 def met_entropy {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) : ℝ  :=
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










#check @_root_.mul_lt_mul_left
#check mul_lt_mul_left

--maximal entropy theorem, small details to fill

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
        --have h6: sconvex_on' (Ici (0:ℝ)) φ := by
          --sorry
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


-- new definitons
--outputs a partition containg our point
noncomputable def partition.partOf {α : Type*} {m : MeasurableSpace α} {μ : Measure α}[IsProbabilityMeasure μ]
    (p : partition m μ) (x : α) : ℕ :=
  Exists.choose
    (show ∃ n, x ∈ p.f n from (mem_iUnion (x := x) (s := p.f)).mp <| p.cover.symm ▸ mem_univ x)

lemma partition.partOf_spec {α : Type*} {m : MeasurableSpace α} {μ : Measure α}[IsProbabilityMeasure μ]
    (p : partition m μ) (x : α) :
    x ∈ p.f (p.partOf x) :=
  Exists.choose_spec
    (show ∃ n, x ∈ p.f n from (mem_iUnion (x := x) (s := p.f)).mp <| p.cover.symm ▸ mem_univ x)

def info {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    (p : partition m μ) (x : α) : ℝ :=
  (-Real.log (μ (p.f (p.partOf x))).toReal)

def cond_info {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (s : partition m μ) (x : α) :ℝ :=
  (-Real.log (μ ((p.f (p.partOf x)) ∩ s.f (s.partOf x))).toReal/(μ (s.f (s.partOf x))).toReal)




--alternative/old defintions of information function

def info' {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (x : α) :ℝ := by
    have h: x ∈ Set.univ := by tauto
    rw[← p.cover] at h; rw[mem_iUnion] at h
    choose a _ using h
    exact (-Real.log (μ (p.f (a))).toReal)

-- define information as function type

def infof {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) : α → ℝ :=
λ x ↦ info p x

-- old conditional information function

def cond_info' {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (s : partition m μ) (x : α) :ℝ := by
  have h: x ∈ Set.univ := by tauto
  have h':= h
  rw[← p.cover] at h; rw[mem_iUnion] at h;rw[← s.cover] at h'; rw[mem_iUnion] at h'
  choose a _ using h
  choose c _ using h'
  exact (-Real.log (μ ((p.f (a)) ∩ s.f (c))).toReal/(μ (s.f (c))).toReal)

-- should introduce a conditional in case the measure in denominator is zero

end section

#check partition.partOf
#check measure_mono

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
  exact ⟨hx.1, partition.partOf_spec p x⟩


lemma e2 {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    (p : partition m μ) (n : ℕ): μ (⋃ (i : ℕ) (h: i ≠ n), (p.f n ∩ p.f i)) = 0 := by
  refine (measure_biUnion_null_iff ?hI).mpr ?_
  · exact (countable_complement_singleton n)
  · intro s h
    exact ((p.disjoint n s) (fun a => h (id (Eq.symm a))))



lemma partition.partOf_eq_ae {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    (p : partition m μ) (n : ℕ) :
    (p.partOf) ⁻¹' {n} =ᵐ[μ] p.f n := by
    have h: p.partOf ⁻¹' {n} ⊆ p.f n := by
      intro x hx
      have h := partition.partOf_spec p x
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
      rw[hx] at h; assumption
    have h':= e1 p n
    have h'':= e2 p n
    refine measure_symmDiff_eq_zero_iff.mp ?_
    simp [symmDiff]
    constructor
    · rw [Set.diff_eq_empty.mpr]
      · exact OuterMeasureClass.measure_empty μ
      · assumption
    · exact measure_mono_null h' h''

--eqset₀,eqset₀,eqset₁,eqset₂,eqset₃ and pre_info_ae_eq are building blocks of info_ae_eq

def eqset₀ {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    (p : partition m μ) : ℕ → Set α :=
  λ n ↦ p.f n \ (⋃ (i : ℕ) (h: i ≠ n), (p.f i))

def eqset  {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    (p : partition m μ): Set α :=
  ⋃ (i : ℕ), eqset₀ p i

lemma eqset₁  {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    (p : partition m μ): ⋂ i, (eqset₀ p i)ᶜ ⊆ ⋃ (n : ℕ), ⋃ (i : ℕ)(h: i ≠ n), (p.f n ∩ p.f i) := by
    intro x hx
    let s: ℕ := Exists.choose (mem_iUnion.mp (p.cover.symm ▸ mem_univ x))
    rw[Set.mem_iInter] at hx
    have h:= hx s
    unfold eqset₀ at h; rw[Set.diff_eq,Set.compl_inter,compl_compl] at h
    have h': x ∈ p.f s := Exists.choose_spec (mem_iUnion.mp (p.cover.symm ▸ mem_univ x))
    cases' h with h'' h''
    · exfalso; exact h'' h'
    · rw[mem_iUnion] at *; rcases h'' with ⟨a,A,c,d⟩; use s
      simp at c
      rw[mem_iUnion]; use a
      refine mem_iUnion.mpr ?h.a
      have h10 : a ≠ s := by
        by_contra h
        tauto
      rw[← c.2 ] at d
      use h10
      exact ⟨h',d⟩


lemma eqset₂  {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    (p : partition m μ) : μ (⋃ (n : ℕ),( ⋃ (i : ℕ)(h: i ≠ n), (p.f n ∩ p.f i))) = 0 := by
    apply measure_iUnion_null_iff.mpr
    intro i
    exact (e2 p i)


lemma eqset₃ {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    (p : partition m μ): μ (eqset p)ᶜ  = 0 := by
    unfold eqset; simp
    exact measure_mono_null (eqset₁ p) (eqset₂ p)



lemma pre_info_ae_eq {α : Type*} {m : MeasurableSpace α} (μ : Measure α) [IsProbabilityMeasure μ]
    (p : partition m μ) : eqset p ⊆  {x | info p x = ∑' n, (p.partOf ⁻¹' {n}).indicator (λ _ ↦ -Real.log (μ (p.f n)).toReal) x} := by
    intro x' hx'
    show info p x' = ∑' (n : ℕ), (p.partOf ⁻¹' {n}).indicator (fun x => -(μ (p.f n)).toReal.log) x'
    let N := p.partOf x'
    have h:= p.partOf_spec x'
    have h₁: ∑' (n : ℕ), (p.partOf ⁻¹' {n}).indicator (fun x => -(μ (p.f n)).toReal.log) x' = (p.partOf ⁻¹' {N}).indicator (fun x => -(μ (p.f N)).toReal.log) x' := by
      apply tsum_eq_single
      intro b hbn

      exact indicator_of_not_mem (id (Ne.symm hbn)) fun x => -(μ (p.f b)).toReal.log
    rw[h₁]
    exact Eq.symm (indicator_of_mem rfl fun x => -(μ (p.f N)).toReal.log)


lemma info_ae_eq {α : Type*} {m : MeasurableSpace α} (μ : Measure α) [IsProbabilityMeasure μ]
    (p : partition m μ) :
    info (μ := μ) p =ᵐ[μ] fun x ↦ ∑' n, (p.partOf ⁻¹' {n}).indicator (fun _ ↦ (-Real.log (μ (p.f n)).toReal)) x := by
    let s := {x | info p x = ∑' n, (p.partOf ⁻¹' {n}).indicator (λ _ ↦ -Real.log (μ (p.f n)).toReal) x}
    have h:= (pre_info_ae_eq μ p)
    have h': {x | info p x = ∑' (n : ℕ), (p.partOf ⁻¹' {n}).indicator (fun x => -(μ (p.f n)).toReal.log) x}ᶜ⊆ (eqset p)ᶜ := by
      exact compl_subset_compl_of_subset h
    exact measure_mono_null h' (eqset₃ p)

#check setIntegral_const
#check lintegral_iUnion_ae

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

lemma lentinf {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    (p : partition m μ) (n: ℕ ) : μ (eqset₀ p n) = 0 → μ (p.f n)=0 := by
    intro h
    have h' : eqset₀ p n ⊆  p.f n := by
      simp[eqset₀]; exact diff_subset
    have h'': μ (p.f n \ eqset₀ p n) = 0 := by
      sorry
    have h''': p.f n = eqset₀ p n ∪ p.f n \ eqset₀ p n := by
      exact Eq.symm (union_diff_cancel' (fun ⦃a⦄ a => a) h')
    have h_eq : μ (p.f n) = μ (eqset₀ p n) + μ (p.f n \ eqset₀ p n) := by
      nth_rewrite 1[h''']
      refine (measure_union ?_) ?_
      . exact disjoint_sdiff_right
    simp [h,h''] at h_eq; exact h_eq




-- should I have used the lebesgue integral instead?

theorem ent_inf {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    (p : partition m μ) {c: ℕ → ℝ}:
    met_entropy p = ∫ x, info p x ∂μ := by
  by_cases junk : ¬ Integrable (info (μ := μ) p) μ
  · simp [integral_undef junk]
    sorry -- You should prove that your `tsum` defining `info` has the same junk value as `integral`
  simp only [not_not, integrable_congr (info_ae_eq μ p)] at junk
  rw [integral_congr_ae (info_ae_eq μ p)]
  unfold met_entropy
  have h := p.cover
  have : ∫ (a : α), ∑' (n : ℕ), (p.partOf ⁻¹' {n}).indicator (fun x => -(μ (p.f n)).toReal.log) a ∂μ =
    ∫ (a : α) in ⋃ n, p.f n, ∑' (n : ℕ), (p.partOf ⁻¹' {n}).indicator (fun x => -(μ (p.f n)).toReal.log) a ∂μ := by
    rw[h]
    exact Eq.symm integral_univ
  rw[this]
  let c: ℕ → ℝ := λ n ↦ if μ (eqset₀ p n) = 0 then 0 else -(μ (p.f n)).toReal.log --not info function,can simplify
  have h₁:= info_ae_eq μ p
  have h₂: ∫ (a : α) in ⋃ n, p.f n, ∑' (n : ℕ), (p.partOf ⁻¹' {n}).indicator (fun x => -(μ (p.f n)).toReal.log) a ∂μ =
  ∑' (i : ℕ), (μ (p.f i)).toReal • c i := by
    refine' (should_this_be_in_the_library _ _ _ _ _)
    · exact fun i => MeasurableSet.nullMeasurableSet (p.measurable i)
    · exact p.disjoint
    · simp only [p.cover, integrableOn_univ,junk]
    · intro s
      show (μ.restrict (p.f s)) {a : p.f s|  ∑' (n : ℕ), (p.partOf ⁻¹' {n}).indicator (fun x => -Real.log (μ (p.f n)).toReal) a =  c s }ᶜ=0
      --show μ {a | a ∈ p.f s ∧ ∑' (n : ℕ), (p.partOf ⁻¹' {n}).indicator (fun x => -Real.log (μ (p.f n)).toReal) a = c s }ᶜ  = 0
      dsimp
      apply?
      show (μ.restrict (p.f s)) {a : p.f s|  ∑' (n : ℕ), (p.partOf ⁻¹' {n}).indicator (fun x => -Real.log (μ (p.f n)).toReal) a =  c s }ᶜ=0
  rw[h₂]; rw[← tsum_neg]; apply tsum_congr
  intro r; simp [c]
  by_cases h₀ : μ (eqset₀ p r) = 0
  · simp only [if_pos h₀]
    rw[lentinf p r h₀]
    have h: ENNReal.toReal 0 = 0 := by
      exact rfl
    rw[h,zero_mul]
    exact neg_zero
  · simp only [if_neg h₀]


lemma preinfo_add {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (s : partition m μ) : info (refine_partition p s)=ᵐ[μ] info s + cond_info p s:= by


theorem info_add {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (s : partition m μ) (t : partition m μ) :
  cond_info (refine_partition p s) (t) = (cond_info s t) + cond_info (p) (refine_partition s t) := by
  ext x; unfold cond_info; unfold refine_partition;dsimp




theorem ent_add {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (s : partition m μ) (t : partition m μ) :
  conmet_entropy (refine_partition p s) (t) = (conmet_entropy s t) + conmet_entropy (p) (refine_partition s t) := by
  intro x

theorem  inf_mono {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (s : partition m μ) (t : partition m μ) :
  cond_info s t ≤ cond_info (refine_partition p s) (t):= by
  intro x; unfold cond_info;dsimp; rw[refine_partition]; dsimp
  let i_s:= Classical.choose (Set.mem_iUnion.mp (s.cover ▸ Set.mem_univ x))
  have hi_s : x ∈ s.f i_s := Classical.choose_spec (Set.mem_iUnion.mp (s.cover ▸ Set.mem_univ x))
  let j_t := Classical.choose (Set.mem_iUnion.mp (t.cover ▸ Set.mem_univ x))
  have hj_t : x ∈ t.f j_t := Classical.choose_spec (Set.mem_iUnion.mp (t.cover ▸ Set.mem_univ x))
  let i_rs := Classical.choose (Set.mem_iUnion.mp ((refine_partition p s).cover ▸ Set.mem_univ x))
  have hi_rs : x ∈ (refine_partition p s).f i_rs := Classical.choose_spec (Set.mem_iUnion.mp ((refine_partition p s).cover ▸ Set.mem_univ x))
  rw[]






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
