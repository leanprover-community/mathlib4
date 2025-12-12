module

import Mathlib
import Mathlib.Lean.LinterCopies

/-
`eraseProofs`:

control took 1.12s
bench took 97.4s
-/

/-
dolorous telescope:

control took 1.07s
bench took 20.3s
-/

/-
`eraseProofs` + early exit:

control took 1.1s
bench took 6.82s
-/

/-
dolorous telescope + early exit:

control took 1.07s
bench took 3.99s
-/
