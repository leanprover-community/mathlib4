import Mathlib.Tactic.TFAE
import Mathlib.Topology.Defs.Sequences
import Mathlib.Topology.ContinuousOn

open Set Filter
open scoped Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {S : Set (Set X)}
  {f : X → Y} {t : Set X} {x : X}

namespace TopologicalSpace.RestrGenFamily

protected theorem isOpen_iff (hS : RestrGenFamily S) :
    IsOpen t ↔ ∀ s ∈ S, IsOpen ((↑) ⁻¹' t : Set s) :=
  ⟨fun ht _ _ ↦ ht.preimage continuous_subtype_val, hS.1 t⟩

protected theorem isClosed_iff (hS : RestrGenFamily S) :
    IsClosed t ↔ ∀ s ∈ S, IsClosed ((↑) ⁻¹' t : Set s) := by
  simp only [← isOpen_compl_iff, hS.isOpen_iff, preimage_compl]

protected theorem continuous_iff (hS : RestrGenFamily S) :
    Continuous f ↔ ∀ s ∈ S, ContinuousOn f s :=
  ⟨fun h _ _ ↦ h.continuousOn, fun h ↦ continuous_def.2 fun _u hu ↦ hS.isOpen_iff.2 fun s hs ↦
    hu.preimage <| (h s hs).restrict⟩

theorem of_continuous_prop (h : ∀ f : X → Prop, (∀ s ∈ S, ContinuousOn f s) → Continuous f) :
    RestrGenFamily S where
  isOpen_of_forall_induced u hu := by
    simp only [continuousOn_iff_continuous_restrict, continuous_Prop] at *
    exact h _ hu

theorem isClosed_intro (h : ∀ t : Set X, (∀ s ∈ S, IsClosed ((↑) ⁻¹' t : Set s)) → IsClosed t) :
    RestrGenFamily S :=
  ⟨fun _t ht ↦ isClosed_compl_iff.1 <| h _ fun s hs ↦ (ht s hs).isClosed_compl⟩

protected theorem enlarge {T} (hS : RestrGenFamily S) (hT : ∀ s ∈ S, ∃ t ∈ T, s ⊆ t) :
    RestrGenFamily T :=
  of_continuous_prop fun _f hf ↦ hS.continuous_iff.2 fun s hs ↦
    let ⟨t, htT, hst⟩ := hT s hs; (hf t htT).mono hst

protected theorem mono {T} (hS : RestrGenFamily S) (hT : S ⊆ T) : RestrGenFamily T :=
  hS.enlarge fun s hs ↦ ⟨s, hT hs, Subset.rfl⟩

theorem of_seq' [SequentialSpace X] :
    RestrGenFamily {s | ∃ (u : ℕ → X) (x : X), Tendsto u atTop (𝓝 x) ∧ insert x (range u) = s} :=
  isClosed_intro fun t ht ↦ _

theorem of_seq [SequentialSpace X]
    (hS : ∀ (u : ℕ → X) x, Tendsto u atTop (𝓝 x) → ∃ s ∈ S, (∀ n, u n ∈ s) ∧ x ∈ s) :
    RestrGenFamily S
