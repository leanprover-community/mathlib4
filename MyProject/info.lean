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
