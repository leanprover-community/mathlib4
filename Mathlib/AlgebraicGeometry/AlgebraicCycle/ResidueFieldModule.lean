/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
import Mathlib.AlgebraicGeometry.AlgebraicCycle.CohmologyModule
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# The residue field of a point as a module over the base field

For a scheme `X` over a field `k`, the residue field `κ(p)` at a point is a `k`-module via
the structure map `k → Γ(X, ⊤) → κ(p)`. This tiny file exists so that the degree of a divisor
(`Mathlib.AlgebraicGeometry.AlgebraicCycle.Degree`) and the skyscraper Euler characteristic
computations can share one instance.
-/

universe u

namespace AlgebraicGeometry.AlgebraicCycle

open AlgebraicGeometry

variable {X : Scheme.{u}} (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))] (p : X)

/-- The residue field at `p` is a `k`-module via the structure map `k → Γ(X, ⊤) → κ(p)`. -/
noncomputable instance : Module k ↑(X.residueField p) :=
  Module.compHom (↑(X.residueField p))
    ((X.Γevaluation p).hom.comp (globalSec (X := X) (R := CommRingCat.of k)))

/-- The `k`-action on the residue field is multiplication by the evaluation of the global
section at `p`. -/
lemma residueField_smul_def (r : k) (y : ↑(X.residueField p)) :
    r • y = (X.Γevaluation p).hom (globalSec (X := X) (R := CommRingCat.of k) r) * y := rfl

end AlgebraicGeometry.AlgebraicCycle
