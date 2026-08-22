module

public import Mathlib
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.CanonicalCocone
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.UniversalProperty
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.CleanMapFromAdapted
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.PartwiseCoveredHomotopy
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.CompListChain
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.ComposeMorphisms
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.SingleCovered
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.HomotopyInvarianceBase

@[expose] public section

open TopologicalSpace CategoryTheory Limits

open scoped unitInterval

noncomputable section

universe u

variable (X : Type u) [TopologicalSpace X]
variable (𝒰 : Set (Opens X))
variable (hcover : ∀ x : X, ∃ U : Opens X, U ∈ 𝒰 ∧ x ∈ U)
variable (hfinite_intersections :
  ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)

variable (s : Cocone
    (((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
      Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor))

include hcover hfinite_intersections

/-- Rectangle identity: given four paths forming the boundary of a rectangle,
    all contained in U ∈ 𝒰, then the composition "bottom ; right" equals
    the composition "left ; top" as single_covered_maps.

    Proof: bottom.trans right is homotopic to left.trans top within U,
    so their single_covered_maps are equal. Then apply single_covered_split_eq to both sides. -/
lemma rectangle_identity_clean {a b c d : X} (U : Opens X) (hU : U ∈ 𝒰)
    (γ_bottom : Path a b) (h_bottom : Set.range γ_bottom ⊆ (U : Set X))
    (γ_right : Path b d) (h_right : Set.range γ_right ⊆ (U : Set X))
    (γ_left : Path a c) (h_left : Set.range γ_left ⊆ (U : Set X))
    (γ_top : Path c d) (h_top : Set.range γ_top ⊆ (U : Set X))
    (H_rect : Path.Homotopy (γ_bottom.trans γ_right) (γ_left.trans γ_top))
    (hH_rect : ∀ (p : I × I), H_rect p ∈ U) :
    single_covered_map X 𝒰 hcover hfinite_intersections s γ_bottom U hU h_bottom ≫
    single_covered_map X 𝒰 hcover hfinite_intersections s γ_right U hU h_right =
    single_covered_map X 𝒰 hcover hfinite_intersections s γ_left U hU h_left ≫
    single_covered_map X 𝒰 hcover hfinite_intersections s γ_top U hU h_top := by
  have h1 : single_covered_map X 𝒰 hcover hfinite_intersections s (γ_bottom.trans γ_right) U hU
      (range_trans_subset γ_bottom γ_right h_bottom h_right) =
      single_covered_map X 𝒰 hcover hfinite_intersections s (γ_left.trans γ_top) U hU
      (range_trans_subset γ_left γ_top h_left h_top) :=
    single_covered_map_homotopic X 𝒰 hcover hfinite_intersections s
      (γ_bottom.trans γ_right) (γ_left.trans γ_top) U hU
      (range_trans_subset γ_bottom γ_right h_bottom h_right)
      (range_trans_subset γ_left γ_top h_left h_top)
      H_rect hH_rect
  have h2 : single_covered_map X 𝒰 hcover hfinite_intersections s γ_bottom U hU h_bottom ≫
      single_covered_map X 𝒰 hcover hfinite_intersections s γ_right U hU h_right =
      single_covered_map X 𝒰 hcover hfinite_intersections s (γ_bottom.trans γ_right) U hU
        (range_trans_subset γ_bottom γ_right h_bottom h_right) :=
    single_covered_split_eq X 𝒰 hcover hfinite_intersections s U hU γ_bottom h_bottom γ_right h_right
  have h3 : single_covered_map X 𝒰 hcover hfinite_intersections s γ_left U hU h_left ≫
      single_covered_map X 𝒰 hcover hfinite_intersections s γ_top U hU h_top =
      single_covered_map X 𝒰 hcover hfinite_intersections s (γ_left.trans γ_top) U hU
        (range_trans_subset γ_left γ_top h_left h_top) :=
    single_covered_split_eq X 𝒰 hcover hfinite_intersections s U hU γ_left h_left γ_top h_top
  rw [h2, h3, h1]

end

end
