import Mathlib.AlgebraicGeometry.AlgebraicCycle.Sheaf
import Mathlib.AlgebraicGeometry.AlgebraicCycle.SkyscraperEulerChar

namespace Function.locallyFinsupp

variable {X R : Type*} [Ring R] [TopologicalSpace X] (s : Set X)
open Classical in
def inductionOn [CompactSpace X]
    {D : locallyFinsupp X R} (hD : D.support ⊆ s)
    {motive : (D : locallyFinsupp X R) → Sort*}
    (zero : motive 0)
    (add : ∀ (D : locallyFinsupp X R), D.support ⊆ s → motive D →
      ∀ {p : X} (hp : p ∈ s), motive (D + Function.locallyFinsuppWithin.single p 1))
    (minus : ∀ (D : locallyFinsupp X R), D.support ⊆ s → motive D →
      ∀ {p : X} (hp : p ∈ s), motive (D - Function.locallyFinsuppWithin.single p 1)) :
    motive D := by
  sorry

end Function.locallyFinsupp

namespace AlgebraicCycle

open AlgebraicGeometry Order CategoryTheory Limits

universe u

variable {X : Scheme.{u}} (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))]
    (D : AlgebraicCycle X ℤ)

noncomputable def degree : ℤ := ∑ᶠ (x : X), (D x) * (Module.finrank k (X.residueField x))

variable [IsIntegral X] [IsNoetherian X] [IsRegularInCodimensionOne X]
  (hD : D.support ⊆ {x | coheight x = 1})

/-
These assumptions are a very funny way of spelling that our scheme is proper over k. We can (and
probably should) weaken these assumptions to just be that O_X has these cohomological vanishing
properties.
-/
variable {N : ℕ}
    (hf₁ : ∀ (D : AlgebraicCycle X ℤ) (_ : D.support ⊆ {x | coheight x = 1}),
        ∀ n, Module.Finite k (lesH (CommRingCat.of k) D.sheaf n))
    (hb₁ : ∀ (D : AlgebraicCycle X ℤ) (_ : D.support ⊆ {x | coheight x = 1}),
        ∀ n, N < n → IsZero (lesH (CommRingCat.of k) D.sheaf n))

/-
This is a funny way of spelling that X is a curve (i.e. it's a scheme where all codimension one
points are closed)
-/
variable (hX : ∀ x : X, coheight x = 1 → ∀ p, x ≤ p → x = p)

theorem riemann_roch (hD : D.support ⊆ {x | coheight x = 1}) : D.sheaf.eulerChar k =
    D.degree k + (0 : AlgebraicCycle X ℤ).sheaf.eulerChar k := by
  induction D using Function.locallyFinsupp.inductionOn {x | coheight x = 1}
  · infer_instance
  · infer_instance
  · /-
    This needs reworking to be a useful induction principal
    -/
    sorry
  · simp [degree]
  · sorry
  · sorry

end AlgebraicCycle
