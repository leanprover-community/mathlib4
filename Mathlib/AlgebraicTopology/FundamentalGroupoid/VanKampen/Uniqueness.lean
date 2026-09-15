module

public import Mathlib
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.CanonicalCocone
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.UniversalProperty

@[expose] public section

open TopologicalSpace CategoryTheory Limits

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

include hcover

/-- Any two functors F G : π₁(X) → s.pt that make the cocone triangles commute
    must be equal on objects. -/
theorem uniqueness_on_objects
    (F G : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X) ⥤ s.pt)
    (hF : ∀ (U : Opens X) (hU : U ∈ 𝒰),
      (FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)) ≫ F =
      s.ι.app ⟨U, hU⟩)
    (hG : ∀ (U : Opens X) (hU : U ∈ 𝒰),
      (FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)) ≫ G =
      s.ι.app ⟨U, hU⟩) :
    ∀ (x : FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X)),
      F.obj x = G.obj x := by
  intro x
  let x_pt : X := x.as
  have h_exists : ∃ (U : Opens X), U ∈ 𝒰 ∧ x_pt ∈ U := hcover x_pt

  rcases h_exists with ⟨U, hU, hxU⟩
  let x_U : FundamentalGroupoid.fundamentalGroupoidFunctor.obj ((Opens.toTopCat (TopCat.of X)).obj U) :=
    FundamentalGroupoid.mk ⟨x_pt, hxU⟩
  have hF_obj : F.obj ((FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)).obj x_U) =
      (s.ι.app ⟨U, hU⟩).obj x_U := by
    have h_eq : ((FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)) ≫ F).obj x_U =
        (s.ι.app ⟨U, hU⟩).obj x_U := by
      rw [hF U hU]
      <;> rfl
    exact h_eq
  have hG_obj : G.obj ((FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)).obj x_U) =
      (s.ι.app ⟨U, hU⟩).obj x_U := by
    have h_eq : ((FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)) ≫ G).obj x_U =
        (s.ι.app ⟨U, hU⟩).obj x_U := by
      rw [hG U hU]
      <;> rfl
    exact h_eq
  have h_π_obj : (FundamentalGroupoid.fundamentalGroupoidFunctor.map (Opens.inclusion' U)).obj x_U = x := by
    simp [x_U]
    <;> rfl
  rw [h_π_obj] at hF_obj
  rw [h_π_obj] at hG_obj
  exact hF_obj.trans hG_obj.symm

end

end
