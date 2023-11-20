import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Complex.Basic

-- From https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Power.20series.20.2F.20bound.20for.20complex.20logarithm/near/403007421
example {f g : ℝ → ℂ} {x : ℝ} {a b : ℂ} (hf : HasDerivAt f a x) (hg : HasDerivAt g b x) :
    HasDerivAt (f + g) (a + b) x := by
  exact? says exact HasDerivAt.add hf hg
