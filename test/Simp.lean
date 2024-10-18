import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Defs

/-!
Tests for the behavior of `simp`.
--/

/- Taken from [Zulip](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/
  topic/simp.20.5BX.5D.20fails.2C.20rw.20.5BX.5D.20works) -/
-- Example 1: succeeds
example {α R : Type*} [CommRing R] (f : α → R) (r : R) (a : α) :
    (r • f) a = r • (f a) := by
  simp only [Pi.smul_apply] -- succeeds

-- Example 2: used to fail, now succeeds!
example {α R : Type*} [CommRing R] (f : α → R) (r : R) (a : α) :
    (r • f) a = r • (f a) := by
  let _ : SMul R R := SMulZeroClass.toSMul
  simp only [Pi.smul_apply]
