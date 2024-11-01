/-
Copyright (c) 2024 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/

import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
Documentation
-/

namespace exteriorPower

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {I : Type*} [LinearOrder I] [Fintype I]
variable {n : ℕ}

/-- If `b` is a basis of `M` (indexed by a linearly ordered type), the basis of the `n`th
exterior power of `M` formed by the `n`-fold exterior products of elements of `b`. -/
noncomputable def _root_.Basis.exteriorPower {I : Type*} [LinearOrder I] (b : Basis I R M) :
    Basis {s : Finset I // Finset.card s = n} R (⋀[R]^n M) := sorry --From SM.ExteriorPower

def ιMulti : M [⋀^Fin n]→ₗ[R] (⋀[R]^n M) :=
  (ExteriorAlgebra.ιMulti R n).codRestrict (⋀[R]^n M) fun _ =>
    ExteriorAlgebra.ιMulti_range R n <| Set.mem_range_self _

noncomputable def ιMulti_family {I : Type*} [LinearOrder I] (v : I → M) :
    {s : Finset I // Finset.card s = n} → ⋀[R]^n M :=
  fun ⟨s, hs⟩ => ιMulti (fun i => v (Finset.orderIsoOfFin s hs i))

end exteriorPower
