import Mathlib.Topology.Basic

open Set

namespace TopologicalSpace

variable {X Y : Type*}

/-- Given `f : X → Y` and a topology on `Y`,
  the induced topology on `X` is the collection of sets
  that are preimages of some open set in `Y`.
  This is the coarsest topology that makes `f` continuous. -/
def induced (f : X → Y) (t : TopologicalSpace Y) : TopologicalSpace X where
  IsOpen s := ∃ t, IsOpen t ∧ f ⁻¹' t = s
  isOpen_univ := ⟨univ, isOpen_univ, preimage_univ⟩
  isOpen_inter := by
    rintro s₁ s₂ ⟨s'₁, hs₁, rfl⟩ ⟨s'₂, hs₂, rfl⟩
    exact ⟨s'₁ ∩ s'₂, hs₁.inter hs₂, preimage_inter⟩
  isOpen_sUnion S h := by
    choose! g hgo hfg using h
    refine ⟨⋃₀ (g '' S), isOpen_sUnion <| ball_image_iff.2 hgo, ?_⟩
    rw [preimage_sUnion, biUnion_image, sUnion_eq_biUnion]
    exact iUnion₂_congr hfg
#align topological_space.induced TopologicalSpace.induced

/-- Given `f : X → Y` and a topology on `X`,
  the coinduced topology on `Y` is defined such that
  `s : Set Y` is open if the preimage of `s` is open.
  This is the finest topology that makes `f` continuous. -/
def coinduced (f : X → Y) (t : TopologicalSpace X) : TopologicalSpace Y where
  IsOpen s := IsOpen (f ⁻¹' s)
  isOpen_univ := t.isOpen_univ
  isOpen_inter s₁ s₂ h₁ h₂ := h₁.inter h₂
  isOpen_sUnion s h := by simpa only [preimage_sUnion] using isOpen_biUnion h
#align topological_space.coinduced TopologicalSpace.coinduced

end TopologicalSpace
