import Mathlib.Dynamics.Ergodic.Conservative

open Function Set MeasureTheory Measure

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α} {s t : Set α}

structure IsDissipativeSet (f : α → α) (μ : Measure α) (s : Set α) : Prop where
  aedisjoint_iterate ⦃n : ℕ⦄ : 0 < n → AEDisjoint μ (f^[n] ⁻¹' s) s

namespace IsDissipativeSet

theorem of_null (h : μ s = 0) : IsDissipativeSet f μ s :=
  ⟨fun _ _ ↦ measure_mono_null inter_subset_right h⟩

@[simp]
protected theorem empty : IsDissipativeSet f μ ∅ := of_null measure_empty

theorem rightInverse {g : α → α} (h : IsDissipativeSet f μ s) (hgf : RightInverse g f)
    (hg : QuasiMeasurePreserving g μ μ) :
    IsDissipativeSet g μ s where
  aedisjoint_iterate n hn := by
    refine measure_mono_null ?_ ((hg.iterate n).preimage_null <| h.aedisjoint_iterate hn)
    refine fun x ⟨hgx, hx⟩ ↦ ⟨?_, hgx⟩
    rwa [mem_preimage, hgf.iterate n]

/-- If `s` is a dissipative set of a quasi measure preserving map `f`,
then all of its preimages -/
theorem aedisjoint_iterate_iterate (h : IsDissipativeSet f μ s)
    (hf : QuasiMeasurePreserving f μ μ) :
    Pairwise (AEDisjoint μ on (f^[·] ⁻¹' s)) := by
  rw [AEDisjoint.symmetric.pairwise_on]
  intro m n hlt
  rw [← Nat.sub_add_cancel hlt.le, iterate_add, preimage_comp]
  refine ((h.aedisjoint_iterate ?_).preimage (hf.iterate _)).symm
  rwa [Nat.sub_pos_iff_lt]
  
end IsDissipativeSet

end MeasureTheory

