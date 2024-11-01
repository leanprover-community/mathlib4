import Mathlib.Algebra.ContinuedFractions.ConvergentsEquiv
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat

namespace Rat

open GenContFract FiniteContFract

def toFiniteContFract (x : ℚ) : FiniteContFract :=
  let c := ContFract.of x
  ⟨c.h, c.s.toList ((ContFract.terminates_coe_iff (α := ℚ)).1 (by
    rw [coe_of, terminates_iff_rat]
    exact ⟨x, rfl⟩))⟩

@[simp]
theorem coeContFract_toFiniteContFract (x : ℚ) :
    (toFiniteContFract x : ContFract) = ContFract.of x := by
  simp [toFiniteContFract, FiniteContFract.toContFract]

@[simp]
theorem coeGenContFract_toFiniteContFract (x : ℚ) :
    (toFiniteContFract x : GenContFract ℚ) = GenContFract.of x := by
  simp [ContFract.toRegContFract, ContFract.toSimpContFract]

@[simp]
theorem eval_toFiniteContFract (x : ℚ) : x.toFiniteContFract.eval = x := by
  rw [eval_eq_convs'_coe_length, ← RegContFract.convs_eq_convs',
    coeGenContFract_toFiniteContFract, ← of_correctness_of_terminatedAt]
  simpa using (ContFract.terminatedAt_coe_iff (α := ℚ)).2
    (terminatedAt_toContFract (toFiniteContFract x))

end Rat
