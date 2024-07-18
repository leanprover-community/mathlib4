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

lemma partcover {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ](p: partition m μ ):
μ (⋃ n, p.f n) = 1 := by
  exact (prob_compl_eq_zero_iff (MeasurableSet.iUnion fun b ↦ p.measurable b)).mp (p.cover)


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


noncomputable section

def met_entropy {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) : EReal :=
  -∑' (n : ℕ),
    (μ (p.f n))* ENNReal.log ((μ (p.f n)))

lemma entropy_nng {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ): 0 ≤ met_entropy p := by
  unfold met_entropy
  refine EReal.neg_le_neg_iff.mp ?_
  · simp
    refine tsum_nonpos ?h
    · intro A
      refine mul_nonpos_of_nonneg_of_nonpos ?_ ?_
      · exact EReal.coe_ennreal_nonneg (μ (p.f A))
      · exact (log_le_one_iff (μ (p.f A))).mpr prob_le_one

def conmet_entropy {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (g : partition m μ): EReal:=
  -∑' (n : ℕ),
  ∑' (n' : ℕ), (μ ((g.f n)∩(p.f n'))) * ENNReal.log ((μ ((g.f n)∩(p.f n')))/(μ (g.f n)))

lemma conmet_entropy_nng {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ)(g : partition m μ): 0 ≤ conmet_entropy p g:= by
  unfold conmet_entropy;
  refine EReal.le_neg_of_le_neg ?_;simp
  · refine tsum_nonpos ?_
    · intro I
      refine tsum_nonpos ?_
      · intro j
        refine mul_nonpos_of_nonneg_of_nonpos ?ha ?hb
        · exact EReal.coe_ennreal_nonneg (μ (g.f I ∩ p.f j))
        · refine (log_le_one_iff (μ (g.f I ∩ p.f j) / μ (g.f I))).mpr ?hb.a
          · refine (ENNReal.div_le_iff_le_mul (Or.inr (one_ne_top)) (Or.inr (one_ne_zero))).mpr ?_
            · simp; exact OuterMeasureClass.measure_mono μ Set.inter_subset_left

open scoped Classical

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



def info {α : Type*} {m : MeasurableSpace α} {μ : Measure α}  [IsProbabilityMeasure μ]
  (p : partition m μ ) (x : α): EReal :=
  (-ENNReal.log (μ (p.f (p.partOf x))))



-- in practice these functions don't matter whether they are undefined on a set of measure zero
-- so does it even matter if the definition would allow division by zero.

def cond_info {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (s : partition m μ) (x : α) :EReal :=
  (-ENNReal.log ((μ ((p.f (p.partOf x)) ∩ s.f (s.partOf x)))/(μ (s.f (s.partOf x)))))

end section


lemma entropy_eq_condentropy_univ {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ] (p: partition m μ):
met_entropy p = conmet_entropy p univ_partition := by
unfold conmet_entropy

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
  have h₂: ((μ (p.f (p.partOf x) ∩ s.f (s.partOf x))) / (μ (s.f (s.partOf x)))) ≤ 1 := by
    refine (ENNReal.div_le_iff_le_mul ?hb0 ?hbt).mpr ?_
    · right;exact one_ne_top
    · right;exact one_ne_zero
    · rw[one_mul]; assumption
  refine EReal.le_neg_of_le_neg ?h
  simpa


lemma info_nng {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ] (p: partition m μ)(x:α):
0 ≤ info p x := by
  rw[info_eq_condinfo_univ]
  exact cond_info_nng p univ_partition x

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
    info (μ := μ) p = fun x ↦ ∑' n, (p.partOf ⁻¹' {n}).indicator (fun _ ↦ (-ENNReal.log (μ (p.f n)))) x := by
    ext x;  let N := p.partOf x
    have h₁: ∑' (n : ℕ), (p.partOf ⁻¹' {n}).indicator (fun _ => -(μ (p.f n)).log) x = (p.partOf ⁻¹' {N}).indicator (fun _ => -(μ (p.f N)).log) x := by
      apply tsum_eq_single
      intro b hbn
      exact indicator_of_not_mem (id (Ne.symm hbn)) fun _ => -(μ (p.f b)).log
    rw[h₁]
    exact Eq.symm (indicator_of_mem rfl fun _ => -(μ (p.f N)).log)

lemma info_measurable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    (p : partition m μ): MeasureTheory.StronglyMeasurable (info p)  := by
    rw[info_eq]
    refine Continuous.comp_stronglyMeasurable ?hg ?hf
    · sorry




theorem ent_inf {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ](p : partition m μ) :
    met_entropy p = ∫⁻  x, (info p x):ENNReal ∂μ

    theorem ent_inf {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ](p : partition m μ) :
   met_entropy p = ∫⁻ x, ENNReal.ofReal (info p x).toReal ∂μ := by
   apply?
