/-
Copyright (c) 2023 Wen Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wen Yang
-/
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Projective Special Linear Group
-/

namespace Matrix

universe u v

open Matrix LinearMap

open scoped MatrixGroups

variable (n : Type u) [DecidableEq n] [Fintype n] (R : Type v) [CommRing R]

/- A projective special linear group is the quotient of a special linear group by its center.-/
def ProjectiveSpecialLinearGroup :=
    SpecialLinearGroup n R ⧸ Subgroup.center (SpecialLinearGroup n R)

scoped[MatrixGroups] notation "PSL(" n ", " R ")" => Matrix.ProjectiveSpecialLinearGroup (Fin n) R

namespace ProjectiveSpecialLinearGroup

instance : Group (ProjectiveSpecialLinearGroup n R) :=
    QuotientGroup.Quotient.group <| Subgroup.center (SpecialLinearGroup n R)

instance : Inhabited (ProjectiveSpecialLinearGroup n R) := ⟨1⟩

end ProjectiveSpecialLinearGroup
