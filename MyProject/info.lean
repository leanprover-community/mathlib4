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
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Init.Classical


open MeasureTheory ENNReal Set Function BigOperators Finset

--storing different possible defintions of info

structure partition {α : Type*} (m : MeasurableSpace α) (μ : Measure α) [IsProbabilityMeasure μ] :=
  f : ℕ → Set α         -- A function from natural numbers to sets of terms in α
  measurable : ∀ n, MeasurableSet (f n)  -- Each set is measurable
  (disjoint : ∀ i j, i ≠ j → μ (f i ∩ f j) = 0)  -- The sets are pairwise disjoint
  (cover : μ (⋃ n, f n)ᶜ  = 0)  -- The union of all sets covers the entire space



noncomputable def partition.partOf {α : Type*} {m : MeasurableSpace α} {μ : Measure α}  [IsProbabilityMeasure μ]
  (p : partition m μ ) (x : α) (hx : x ∈ ⋃ n, p.f n) : ℕ :=
Exists.choose (show ∃ n, x ∈ p.f n from (mem_iUnion (x := x) (s := p.f)).mp hx)

lemma  partition.partOf_spec {α : Type*} {m : MeasurableSpace α} {μ : Measure α}[IsProbabilityMeasure μ]
    (p : partition m μ) (x : α) (hx : x ∈ ⋃ n, p.f n):
    x ∈ p.f (p.partOf x hx) :=
  Exists.choose_spec (show ∃ n, x ∈ p.f n from (mem_iUnion (x := x) (s := p.f)).mp hx)

noncomputable def info {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    (p : partition m μ) (x : α) (hx : x ∈ ⋃ n, p.f n) : ℝ :=
  (-Real.log (μ (p.f (p.partOf x hx))).toReal)




--non measure cover/exact cover--
structure partition' {α : Type*} (m : MeasurableSpace α) (μ : Measure α) [IsProbabilityMeasure μ] :=
  f : ℕ → Set α         -- A function from natural numbers to sets of terms in α
  measurable : ∀ n, MeasurableSet (f n)  -- Each set is measurable
  (disjoint : ∀ i j, i ≠ j → μ (f i ∩ f j) = 0)  -- The sets are pairwise disjoint
  (cover : (⋃ n, f n) = Set.univ)  -- The union of all sets covers the entire space

noncomputable def partition'.partOf {α : Type*} {m : MeasurableSpace α} {μ : Measure α}[IsProbabilityMeasure μ]
    (p : partition' m μ) (x : α) : ℕ :=
  Exists.choose
    (show ∃ n, x ∈ p.f n from (mem_iUnion (x := x) (s := p.f)).mp <| p.cover.symm ▸ mem_univ x)

lemma partition'.partOf_spec {α : Type*} {m : MeasurableSpace α} {μ : Measure α}[IsProbabilityMeasure μ]
    (p : partition' m μ) (x : α) :
    x ∈ p.f (p.partOf x) :=
  Exists.choose_spec
    (show ∃ n, x ∈ p.f n from (mem_iUnion (x := x) (s := p.f)).mp <| p.cover.symm ▸ mem_univ x)

noncomputable def info' {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    (p : partition' m μ) (x : α) : ℝ :=
  (-Real.log (μ (p.f (p.partOf x))).toReal)
--



noncomputable def partition.partOf'' {α : Type*} {m : MeasurableSpace α} {μ : Measure α}[IsProbabilityMeasure μ]
    (p : partition m μ) (x : α) [dec : Decidable (x ∈ (⋃ n, p.f n))]: ℕ :=
  if h : x ∈ (⋃ n, p.f n) then
    Exists.choose (show ∃ n, x ∈ p.f n from (Set.mem_iUnion.mp h)) else 0


lemma partition.partOf_spec {α : Type*} {m : MeasurableSpace α} {μ : Measure α}[IsProbabilityMeasure μ]
    (p : partition m μ) (x : α) :
    x ∈ p.f (p.partOf x) :=
  Exists.choose_spec
    (show ∃ n, x ∈ p.f n from (mem_iUnion (x := x) (s := p.f)).mp <| p.cover.symm ▸ mem_univ x)

-- this decidable thing seems to not work properly/maybe better to define
-- on a different modain

noncomputable def info'' {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
    (p : partition m μ)(x : α) [dec : Decidable (x ∈ (⋃ n, p.f n))]: ℝ :=
  (-Real.log (μ (p.f (p.partOf'' x))).toReal)


structure partition'' {α : Type*} (m : MeasurableSpace α) (μ : Measure α) [IsProbabilityMeasure μ] :=
  P : Set (Set α)        -- A function from natural numbers to sets of terms in α
  measurable : ∀ a ∈ P, MeasurableSet a  -- Each set is measurable
  disjoint : ∀ a b : P, a≠b → μ (a ∩ b)=0  -- The sets are pairwise disjoint
  cover : μ (⋃₀ P)ᶜ  = 0  -- The union of all sets covers the entire space
  countable : P.Countable -- at most countable or finite


lemma pre_info_ae_eq {α : Type*} {m : MeasurableSpace α} (μ : Measure α) [IsProbabilityMeasure μ]
    (p : partition m μ) : eqset p ⊆  {x | info p x = ∑' n, (p.partOf ⁻¹' {n}).indicator (λ _ ↦ -Real.log (μ (p.f n)).toReal) x} := by
    intro x' _
    show info p x' = ∑' (n : ℕ), (p.partOf ⁻¹' {n}).indicator (fun _ => -(μ (p.f n)).toReal.log) x'
    let N := p.partOf x'
    have h₁: ∑' (n : ℕ), (p.partOf ⁻¹' {n}).indicator (fun _ => -(μ (p.f n)).toReal.log) x' = (p.partOf ⁻¹' {N}).indicator (fun _ => -(μ (p.f N)).toReal.log) x' := by
      apply tsum_eq_single
      intro b hbn
      exact indicator_of_not_mem (id (Ne.symm hbn)) fun _ => -(μ (p.f b)).toReal.log
    rw[h₁]
    exact Eq.symm (indicator_of_mem rfl fun _ => -(μ (p.f N)).toReal.log)


lemma info_ae_eq {α : Type*} {m : MeasurableSpace α} (μ : Measure α) [IsProbabilityMeasure μ]
    (p : partition m μ) :
    info (μ := μ) p =ᵐ[μ] fun x ↦ ∑' n, (p.partOf ⁻¹' {n}).indicator (fun _ ↦ (-Real.log (μ (p.f n)).toReal)) x := by
    have h:= (pre_info_ae_eq μ p)
    have h': {x | info p x = ∑' (n : ℕ), (p.partOf ⁻¹' {n}).indicator (fun x => -(μ (p.f n)).toReal.log) x}ᶜ⊆ (eqset p)ᶜ := by
      exact compl_subset_compl_of_subset h
    exact measure_mono_null h' (eqset₃ p)
