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

def info {α : Type*} {m : MeasurableSpace α} {μ : Measure α}  [IsProbabilityMeasure μ]
  (p : partition m μ ) (x : α): ℝ :=
  (-Real.log (μ (p.f (p.partOf x))).toReal)

-- in practice these functions don't matter whether they are undefined on a set of measure zero
-- so does it even matter if the definition would allow division by zero.

def cond_info {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (s : partition m μ) (x : α) :ℝ :=
  (-Real.log (μ ((p.f (p.partOf x)) ∩ s.f (s.partOf x))).toReal/(μ (s.f (s.partOf x))).toReal)


#check preimage_compl
#check add_left_cancel
--weird,is this true
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
  rw[← hA₁,hA₂,hB₂,h] at hB₁--; apply add_left_cancel at hB₁;
  have h₁:= measure_ne_top μ B
  exact (ENNReal.add_right_inj h₁).mp (id (Eq.symm hB₁))

def partition.pre {α : Type*} [m : MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ] (p : partition m μ)
(T: α → α) (h₁ : MeasureTheory.MeasurePreserving T μ μ ): partition m μ
  where
f := λ n ↦  T ⁻¹' (p.f n)
measurable:= by
  intro N
  apply MeasurableSet.preimage (p.measurable N)
  exact h₁.measurable -- works here for some reason
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
    · apply MeasurableSet.preimage (m:= m) (mβ:=m)
      · exact MeasurableSet.iUnion p.measurable
      · exact h₁.measurable
    · exact (MeasurableSet.iUnion (p.measurable))
  rwa [this]


lemma countable_complement_singleton  (n : ℕ ) :

--these two are equivalent
  Set.Countable {i | i ≠ n} := by
  apply Set.countable_iff_exists_injective.mpr
  use (λ x => x)
  · intro x y hxy
    dsimp at hxy; ext; exact hxy

lemma e2 {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    (p : partition m μ) (n : ℕ): μ (⋃ (i : ℕ) (h: i ≠ n), (p.f n ∩ p.f i)) = 0 := by
  refine (measure_biUnion_null_iff ?hI).mpr ?_
  · exact (countable_complement_singleton n)
  · intro s h
    exact ((p.disjoint n s) (fun a => h (id (Eq.symm a))))

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
    apply measure_iUnion_null_iff.mpr
    intro i
    exact (e2 p i)


lemma eqset₃ {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    (p : partition m μ): μ (eqset p)ᶜ  = 0 := by
    unfold eqset; simp
    exact measure_mono_null (eqset₁ p) (measure_union_null (eqset₂ p) (p.cover))


lemma eqsetpartition {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ] (p : partition m μ) (x:α)(n:ℕ):
x ∈ eqset₀ p n → p.partOf x = n := by
  intro hx; unfold eqset₀ at hx; cases' hx with hx₁ hx₂
  by_contra h'
  let a:= p.partOf x
  have: a ≠ n:= by
    exact h'
  have :x ∈  ⋃ i, ⋃ (_ : i ≠ n), p.f i := by
    rw[mem_iUnion]; use a; refine mem_iUnion.mpr ?h.a
    use this
    refine partition.partOf_spec p x ?h.hx
    rw[mem_iUnion]; use n
  exact hx₂ this

lemma invariance₀ {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ](T: α → α)
 {self : MeasureTheory.MeasurePreserving T μ μ} (p : partition m μ):  T⁻¹'eqset p ∩ eqset (p.pre T self) ⊆  {x | p.partOf (T x) = (p.pre T self).partOf x} := by
 intro x' ⟨_,hx₂⟩
 show (p.partOf (T x')) =  (p.pre T self ).partOf x'
 let s : ℕ  := (p.pre T self).partOf x'
 unfold eqset at hx₂;rw [mem_iUnion] at hx₂
 rcases hx₂ with ⟨a,ha⟩
 have := (eqsetpartition (p.pre T self) x' a) ha
 rw[this]
 unfold eqset₀ at ha
 cases' ha with ha₁ hA₂
 apply eqsetpartition
 unfold eqset₀
 constructor
 · exact ha₁
 · intro h; rw [mem_iUnion] at h;rcases h with ⟨b,hb⟩
   rcases hb with ⟨C,hc₁,hc₂⟩
   have :  x' ∈ ⋃ i, ⋃ (_ : i ≠ a), (p.pre T self).f i := by
    rw[mem_iUnion]; use b; simp; simp at hc₁
    constructor
    · exact hc₁.1
    · show x' ∈ T⁻¹' p.f b
      rw[hc₁.2]
      exact hc₂
   exact hA₂ this


#check MeasurableSet.compl_iff
#check MeasureTheory.MeasurePreserving
#check preimage_compl
#check Measure.map_eq



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

--I showed that the function given x gives index of set in partition p containing Tx is same as the index of the
--set in the partition p.pre containing x. What I need to prove is to show that these two sets are identical?(maybe up to measure zero)
--if these two fucntion are almost everywhere equal then given x in  T⁻¹'eqset p ∩ eqset (p.pre T self) then must it be the case that
-- if I intersect the set with can isee that not only x coincide but also match the sets.


lemma pre_invariance {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ](T: α → α)
 (self : MeasureTheory.MeasurePreserving T μ μ) (p : partition m μ) : (λ x ↦ (p.partOf (T x))) =ᵐ[μ] λ x ↦ (p.pre T self ).partOf x := by
  have := invariance₀ (self:=self) p
  have h': {x | p.partOf (T x) = (p.pre T self).partOf x}ᶜ ⊆ ( T⁻¹'eqset p ∩ eqset (p.pre T self))ᶜ := by
    exact compl_subset_compl_of_subset this
  refine measure_mono_null h' ?_
  · have h₁ : μ (T⁻¹'eqset p)ᶜ=0 := by
      rw[← Set.preimage_compl]
      have: μ (T⁻¹'(eqset p)ᶜ)= μ (eqset p)ᶜ  := by
        exact MeasurePreserving.measure_preimage self (MeasurableSet.compl_iff.mpr (eqset_measurable p))
      rw[this];exact eqset₃ p
    have h₂ := eqset₃ (p.pre T self)
    rw[Set.compl_inter]
    exact measure_union_null h₁ h₂

--one small detail left, for info, entropy can be complete once the integral is figured out

theorem invariance {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ](T: α → α)
 (self : MeasureTheory.MeasurePreserving T μ μ) (p : partition m μ) (g : partition m μ) :
 (cond_info p g) ∘ T =ᵐ[μ] (cond_info (p.pre T self) (g.pre T self)) := by
  unfold cond_info;
  have : (fun x => -Real.log (μ (p.f (p.partOf x) ∩ g.f (g.partOf x))).toReal / (μ (g.f (g.partOf x))).toReal) ∘ T = fun x => -Real.log (μ (p.f (p.partOf (T x)) ∩ g.f (g.partOf (T x)))).toReal / (μ (g.f (g.partOf (T x)))).toReal := by
    ext X
    rw [Function.comp_apply]
  rw [this]
  show μ {x | -Real.log (μ (p.f (p.partOf (T x)) ∩ g.f (g.partOf (T x)))).toReal / (μ (g.f (g.partOf (T x)))).toReal = -Real.log (μ ((p.pre T self).f ((p.pre T self).partOf x) ∩ (g.pre T self).f ((g.pre T self).partOf x))).toReal /
    (μ ((g.pre T self).f ((g.pre T self).partOf x))).toReal}ᶜ = 0
  have h₁:  (T ⁻¹' eqset p ∩ eqset (p.pre T self)) ∩  (T ⁻¹' eqset g ∩ eqset (g.pre T self)) ⊆ {x | -Real.log (μ (p.f (p.partOf (T x)) ∩ g.f (g.partOf (T x)))).toReal / (μ (g.f (g.partOf (T x)))).toReal = -Real.log (μ ((p.pre T self).f ((p.pre T self).partOf x) ∩ (g.pre T self).f ((g.pre T self).partOf x))).toReal /
    (μ ((g.pre T self).f ((g.pre T self).partOf x))).toReal} := by
    intro x ⟨hx₁,hx₂⟩
    show -Real.log (μ (p.f (p.partOf (T x)) ∩ g.f (g.partOf (T x)))).toReal / (μ (g.f (g.partOf (T x)))).toReal =
      -Real.log (μ ((p.pre T self).f ((p.pre T self).partOf x) ∩ (g.pre T self).f ((g.pre T self).partOf x))).toReal /
        (μ ((g.pre T self).f ((g.pre T self).partOf x))).toReal
    have h1: p.partOf (T x) = (p.pre T self).partOf x := by
      exact (invariance₀ p (self:= self)) hx₁
    have h2: g.partOf (T x) = (g.pre T self).partOf x := by
      exact (invariance₀ g (self:= self)) hx₂
    rw[h1,h2]
    have h3: μ (g.f ((g.pre T self).partOf x)) = μ ((g.pre T self).f ((g.pre T self).partOf x)) := by
      have : (g.pre T self).f ((g.pre T self).partOf x)=T⁻¹' (g.f ((g.pre T self).partOf x)) := by
        exact rfl
      rw[this]
      symm
      exact MeasurePreserving.measure_preimage self (g.measurable ((g.pre T self).partOf x))
    rw[h3]
    have h4: (p.pre T self).f ((p.pre T self).partOf x) = T⁻¹' p.f ((p.pre T self).partOf x) := by
      exact rfl
    have h5: (g.pre T self).f ((g.pre T self).partOf x) = T⁻¹' g.f ((g.pre T self).partOf x) := by
      exact rfl
    rw[h4,h5]
    rw[← Set.preimage_inter]
    have h6: μ (p.f ((p.pre T self).partOf x) ∩ g.f ((g.pre T self).partOf x))=μ (T ⁻¹' (p.f ((p.pre T self).partOf x) ∩ g.f ((g.pre T self).partOf x))) := by
      refine Eq.symm (MeasurePreserving.measure_preimage self ?hs)
      · refine MeasurableSet.inter ?hs.h₁ ?hs.h₂
        · exact p.measurable ((p.pre T self).partOf x)
        · exact g.measurable ((g.pre T self).partOf x)
    rw[h6]
  have h₂: {x | -Real.log (μ (p.f (p.partOf (T x)) ∩ g.f (g.partOf (T x)))).toReal / (μ (g.f (g.partOf (T x)))).toReal = -Real.log (μ ((p.pre T self).f ((p.pre T self).partOf x) ∩ (g.pre T self).f ((g.pre T self).partOf x))).toReal /
    (μ ((g.pre T self).f ((g.pre T self).partOf x))).toReal}ᶜ⊆ ((T ⁻¹' eqset p ∩ eqset (p.pre T self)) ∩  (T ⁻¹' eqset g ∩ eqset (g.pre T self)))ᶜ := by
      exact compl_subset_compl_of_subset h₁
  refine measure_mono_null h₂ ?_
  simp [Set.compl_inter]
  constructor
  · constructor
    · rw[← Set.preimage_compl]
      have h₁':= eqset₃ p
      have: μ (T⁻¹'(eqset p)ᶜ)= μ (eqset p)ᶜ  := by
        exact MeasurePreserving.measure_preimage self (MeasurableSet.compl_iff.mpr (eqset_measurable p))
      rw[this];exact h₁'
    · exact eqset₃ (p.pre T self)
  · constructor
    · rw[← Set.preimage_compl]
      have h₁':= eqset₃ g
      have: μ (T⁻¹'(eqset g)ᶜ)= μ (eqset g)ᶜ  := by
        exact MeasurePreserving.measure_preimage self (MeasurableSet.compl_iff.mpr (eqset_measurable g))
      rw[this];exact h₁'
    · exact eqset₃ (g.pre T self)








lemma  molly {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ](T: α → α)
 (self : MeasureTheory.MeasurePreserving T μ μ) (p : partition m μ):
 ∫ x, info p (T x) ∂μ = ∫ x, info p x ∂μ := by
 sorry


theorem invariance₁ {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ](T: α → α)
 (self : MeasureTheory.MeasurePreserving T μ μ) (p : partition m μ) (g : partition m μ):
conmet_entropy p g = conmet_entropy (p.pre T self) (g.pre T self) := by
  sorry

noncomputable def iter_pre_partition {α : Type*}  {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (p : partition m μ) (T : α → α) (self : MeasureTheory.MeasurePreserving T μ μ) : ℕ → partition m μ
| 0  => p
| (n + 1) => (iter_pre_partition p T self n).pre  T self


def partition.tentropy {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ](T: α → α)
 (self : MeasureTheory.MeasurePreserving T μ μ) (p : partition m μ) : ℝ :=
⨅ (n : ℕ), (1 / (n + 1 : ℝ)) * met_entropy (iter_pre_partition p T self n)

def tentropy {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ](T: α → α)
 (self : MeasureTheory.MeasurePreserving T μ μ) (p : partition m μ): ℝ :=
⨆ (p:partition m μ ), p.tentropy T self
