module

public import Mathlib
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.CanonicalCocone
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.CleanDescent
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.ColimitProof

@[expose] public section

open TopologicalSpace CategoryTheory Limits

noncomputable section

universe u

variable (X : Type u) [TopologicalSpace X]
variable (𝒰 : Set (Opens X))
variable (hcover : ∀ x : X, ∃ U : Opens X, U ∈ 𝒰 ∧ x ∈ U)
variable (hpath_connected : ∀ U : Opens X, U ∈ 𝒰 → IsPathConnected (U : Set X))
variable (hfinite_intersections :
  ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰)

variable (s : Cocone
    (((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
      Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor))

include hcover hfinite_intersections

/-- Full uniqueness: any two functors making the cocone triangles commute must be equal.
    We have uniqueness on objects proved; uniqueness on morphisms follows from the
    fact that every morphism in π₁(X) can be decomposed into paths covered by open sets,
    and the action on those paths is determined by the cocone components. -/
lemma uniqueness_full
    (F G : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X) ⥤ s.pt)
    (hF : ∀ (U : Opens X) (hU : U ∈ 𝒰),
      (FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)) ≫ F =
      s.ι.app ⟨U, hU⟩)
    (hG : ∀ (U : Opens X) (hU : U ∈ 𝒰),
      (FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)) ≫ G =
      s.ι.app ⟨U, hU⟩) :
    F = G := by
  let h_colim := my_canonicalCocone_isColimit X 𝒰 hcover hfinite_intersections
  have hF' : ∀ (j : { U : Opens X // U ∈ 𝒰 }),
      (canonicalCocone X 𝒰).ι.app j ≫ F = s.ι.app j := by
    intro j
    exact hF j.val j.property
  have hG' : ∀ (j : { U : Opens X // U ∈ 𝒰 }),
      (canonicalCocone X 𝒰).ι.app j ≫ G = s.ι.app j := by
    intro j
    exact hG j.val j.property
  have h1 : F = h_colim.desc s := h_colim.uniq s F hF'
  have h2 : G = h_colim.desc s := h_colim.uniq s G hG'
  rw [h1, h2]

/-- The main theorem: there exists a colimit cocone whose apex is isomorphic to π₁(X).
    This follows directly from my_canonicalCocone_isColimit (the clean proof). -/
theorem van_kampen_groupoid_main
    (hcover : ∀ x : X, ∃ U : Opens X, U ∈ 𝒰 ∧ x ∈ U)
    (hfinite_intersections :
      ∀ s : Finset (Opens X), s.Nonempty → (∀ U ∈ s, U ∈ 𝒰) → s.inf (fun U : Opens X => U) ∈ 𝒰) :
    ∃ c : Cocone
      (((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
        Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor),
      Nonempty (IsColimit c) ∧
      Nonempty (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X) ≅ c.pt) := by
  let c := canonicalCocone X 𝒰
  use c
  constructor
  · -- Proof that c is a colimit (using the clean proof from CleanDescent.lean)
    exact ⟨my_canonicalCocone_isColimit X 𝒰 hcover hfinite_intersections⟩
  · -- Proof that π₁(X) ≅ c.pt
    have h_eq : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X) = c.pt := by
      rfl
    exact ⟨eqToIso h_eq⟩

end

end
