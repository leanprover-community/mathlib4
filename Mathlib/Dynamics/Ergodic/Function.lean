import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Topology.CountableInterFilter
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open Function Set Filter MeasureTheory Topology TopologicalSpace

variable {α X : Type _} [MeasurableSpace α] [TopologicalSpace X]

/-- If `f : α → α` is a (quasi)ergodic map and `g : α → X` is a null-measurable function from `α` to
a nonempty topological space with second countable topology that is a.e.-invariant under `f`, then
`g` is a.e. constant. -/
theorem QuasiErgodic.ae_eq_const_of_ae_eq_comp_of_ae_range₀ [T0Space X] [Nonempty X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {μ : MeasureTheory.Measure α} {s : Set X}
    [SecondCountableTopology s] (h : QuasiErgodic f μ) (hs : ∀ᵐ x ∂μ, g x ∈ s)
    (hgm : NullMeasurable g μ) (hg_eq : g ∘ f =ᵐ[μ] g) : ∃ c, g =ᵐ[μ] const α c := by
  refine exists_eventuallyEq_const_of_eventually_mem_of_forall_open hs fun U hU ↦ ?_
  refine h.ae_mem_or_ae_nmem₀ (s := g ⁻¹' U) (hgm hU.measurableSet) ?_
  refine (hg_eq.mono fun x hx ↦ ?_).set_eq
  rw [← preimage_comp, mem_preimage, mem_preimage, hx]

section SecondCountableTopology

variable [SecondCountableTopology X] [T0Space X] [Nonempty X] [MeasurableSpace X]
  [OpensMeasurableSpace X] {μ : MeasureTheory.Measure α} {f : α → α} {g : α → X}

/-- If `f : α → α` is a (pre)ergodic map and `g : α → X` is a measurable function from `α` to a
nonempty topological space with second countable topology that is invariant under `f`, then `g` is
a.e. constant. -/
theorem PreErgodic.ae_eq_const_of_ae_eq_comp (h : PreErgodic f μ) (hgm : Measurable g)
    (hg_eq : g ∘ f = g) : ∃ c, g =ᵐ[μ] const α c := by
  refine exists_eventuallyEq_const_of_forall_open fun U hU ↦ ?_
  refine h.ae_mem_or_ae_nmem (s := g ⁻¹' U) (hgm hU.measurableSet) ?_
  rw [← preimage_comp, hg_eq]

/-- If `f : α → α` is a (quasi)ergodic map and `g : α → X` is a null-measurable function from `α` to
a nonempty topological space with second countable topology that is a.e.-invariant under `f`, then
`g` is a.e. constant. -/
theorem QuasiErgodic.ae_eq_const_of_ae_eq_comp₀ (h : QuasiErgodic f μ) (hgm : NullMeasurable g μ)
    (hg_eq : g ∘ f =ᵐ[μ] g) : ∃ c, g =ᵐ[μ] const α c :=
  h.ae_eq_const_of_ae_eq_comp_of_ae_range₀ (s := univ) univ_mem hgm hg_eq

end SecondCountableTopology

namespace QuasiErgodic

variable [MetrizableSpace X] [Nonempty X] {μ : MeasureTheory.Measure α} {f : α → α}

/-- If `f : α → α` is a (quasi)ergodic map and `g : α → X` is an a.e. strongly measurable function
from `α` to a nonempty topological space that is a.e.-invariant under `f`, then `g` is
a.e. constant. -/
theorem ae_eq_const_of_ae_eq_comp_ae {g : α → X} (h : QuasiErgodic f μ)
    (hgm : AEStronglyMeasurable g μ) (hg_eq : g ∘ f =ᵐ[μ] g) :
    ∃ c, g =ᵐ[μ] const α c := by
  borelize X
  rcases hgm.isSeparable_ae_range with ⟨t, ht, hgt⟩
  -- TODO: add `AEStronglyMeasurable.secondCountableTopology_ae_range`
  have : SecondCountableTopology t
  · letI := metrizableSpaceMetric X
    have := ht.separableSpace
    exact UniformSpace.secondCountable_of_separable t
  exact h.ae_eq_const_of_ae_eq_comp_of_ae_range₀ hgt hgm.aemeasurable.nullMeasurable hg_eq

theorem eq_const_of_compQuasiMeasurePreserving_eq (h : QuasiErgodic f μ) {g : α →ₘ[μ] X}
    (hg_eq : g.compQuasiMeasurePreserving f h.1 = g) : ∃ c, g = .const α c :=
 _

end QuasiErgodic
