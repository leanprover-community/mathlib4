/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finsupp.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Data.Finset.Sym

/-!
# Finsupp and Sym2
-/


section

variable {ι R}

/-- All the products of pairs of elements in `f`. -/
noncomputable def Finsupp.sym2Mul [CommMonoidWithZero R] (f : ι →₀ R) : Sym2 ι →₀ R :=
  .onFinset
    f.support.sym2
    (Sym2.lift ⟨fun i j => f i * f j, fun _ _ => mul_comm _ _⟩)
    (Sym2.ind <| by aesop)

end
