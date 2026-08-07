module

public import Mathlib

@[expose] public section

open TopologicalSpace CategoryTheory Limits

noncomputable section

universe u

variable (X : Type u) [TopologicalSpace X]
variable (𝒰 : Set (Opens X))

/-- The canonical cocone with apex `π₁(X)` for the diagram of fundamental groupoids
    of open sets in the cover. -/
def canonicalCocone : Cocone
    (((Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor) ⋙
      Opens.toTopCat (TopCat.of X) ⋙ FundamentalGroupoid.fundamentalGroupoidFunctor) := by
  let π₁ := FundamentalGroupoid.fundamentalGroupoidFunctor
  let X_top := TopCat.of X
  let F := (Subtype.mono_coe (fun U : Opens X => U ∈ 𝒰)).functor
  let G := Opens.toTopCat X_top
  let D := F ⋙ G ⋙ π₁
  refine' {
    pt := π₁.obj X_top,
    ι := {
      app := fun U => π₁.map (Opens.inclusion' (show Opens X_top from U.val)),
      naturality := fun {U V} (f : U ⟶ V) => by
        let i : U.val ⟶ V.val := F.map f
        have h_comm : G.map i ≫ Opens.inclusion' (show Opens X_top from V.val) =
            Opens.inclusion' (show Opens X_top from U.val) := by
          apply TopCat.hom_ext
          ext x
          simp [Opens.coe_inclusion']
          <;> rfl
        have h_main : π₁.map (G.map i) ≫ π₁.map (Opens.inclusion' (show Opens X_top from V.val)) =
            π₁.map (Opens.inclusion' (show Opens X_top from U.val)) := by
          rw [←π₁.map_comp, h_comm]
        have h_goal : π₁.map (G.map i) ≫ π₁.map (Opens.inclusion' (show Opens X_top from V.val)) =
            π₁.map (Opens.inclusion' (show Opens X_top from U.val)) ≫ 𝟙 (π₁.obj X_top) := by
          rw [h_main, Category.comp_id]
        exact h_goal
    }
  }

/-- The apex of the canonical cocone is exactly `π₁(X)`. -/
theorem canonicalCocone_pt :
    (canonicalCocone X 𝒰).pt = FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X) := by
  rfl

end

end
