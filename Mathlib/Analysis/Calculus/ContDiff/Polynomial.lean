import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Higher smoothness of polynomials

We prove that polynomials are `C^∞`.
-/

public section

namespace Polynomial

/-- Polynomials are smooth -/
lemma contDiff_aeval {R 𝕜 : Type*} [CommSemiring R] [NontriviallyNormedField 𝕜] [Algebra R 𝕜]
    (f : Polynomial R) (n : WithTop ℕ∞) : ContDiff 𝕜 n (fun x : 𝕜 ↦ f.aeval x) := by
  induction f using Polynomial.induction_on' with
  | add f g fc gc => simpa using fc.add gc
  | monomial n a => simpa using contDiff_const.mul (contDiff_id.pow _)

end Polynomial
