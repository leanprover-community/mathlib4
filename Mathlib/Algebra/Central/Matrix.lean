/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Yunzhou Xie
-/
import Mathlib.Algebra.Central.Defs
import Mathlib.Data.Matrix.Basis

/-!
# The matrix algebra is a central algebra
-/

namespace Matrix
variable {n R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Fintype n] [DecidableEq n]

theorem subalgebraCenter_eq_scalarAlgHom_map :
    Subalgebra.center R (Matrix n n A) = (Subalgebra.center R A).map (scalarAlgHom n R) :=
  SetLike.coe_injective center_eq_scalar_image

end Matrix

namespace Algebra.IsCentral
variable (K D : Type*) [CommSemiring K] [Semiring D] [Algebra K D] [IsCentral K D]

open Matrix in
instance matrix (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Algebra.IsCentral K (Matrix ι ι D) where
  out := subalgebraCenter_eq_scalarAlgHom_map.trans_le <|
    Subalgebra.map_mono out |>.trans_eq <| map_bot _

end Algebra.IsCentral
