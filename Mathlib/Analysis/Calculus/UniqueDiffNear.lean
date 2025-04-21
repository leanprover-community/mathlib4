import Mathlib.Analysis.Calculus.TangentCone

open Filter Function Set 
open scoped Topology

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] {s t : Set E} {x y : E}

variable (𝕜) in
@[mk_iff uniqueDiffNear_iff_eventually_insert]
structure UniqueDiffNear (s : Set E) (x : E) : Prop where of_eventually_insert ::
  eventually_insert : ∀ᶠ y in 𝓝[insert x s] x, UniqueDiffWithinAt 𝕜 s y

theorem UniqueDiffNear.iff_uniqueDiffWithinAt_and_eventually :
    UniqueDiffNear 𝕜 s x ↔
      UniqueDiffWithinAt 𝕜 s x ∧ ∀ᶠ y in 𝓝[s] x, UniqueDiffWithinAt 𝕜 s y := by
  simp [uniqueDiffNear_iff_eventually_insert]

theorem UniqueDiffNear.uniqueDiffWithinAt (h : UniqueDiffNear 𝕜 s x) :
    UniqueDiffWithinAt 𝕜 s x :=
  (iff_uniqueDiffWithinAt_and_eventually.mp h).1

theorem UniqueDiffNear.eventually (h : UniqueDiffNear 𝕜 s x) :
    ∀ᶠ y in 𝓝[s] x, UniqueDiffWithinAt 𝕜 s y :=
  (iff_uniqueDiffWithinAt_and_eventually.mp h).2

theorem UniqueDiffNear.of_uniqueDiffWithinAt_of_eventually (h₁ : UniqueDiffWithinAt 𝕜 s x)
    (h₂ : ∀ᶠ y in 𝓝[s] x, UniqueDiffWithinAt 𝕜 s y) : UniqueDiffNear 𝕜 s x :=
    iff_uniqueDiffWithinAt_and_eventually.mpr ⟨h₁, h₂⟩
