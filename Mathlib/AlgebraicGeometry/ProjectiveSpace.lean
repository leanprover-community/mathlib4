/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Projective space

## Main definitions

- `AlgebraicGeometry.ProjectiveSpace`: `ℙ(n; S)` is the projective `n`-space over `S`.
-/

/-
TODO:
- `AlgebraicGeometry.ProjectiveSpace.SpecIso`: `ℙ(n; Spec R) ≅ Proj R[n]`
- `AlgebraicGeometry.ProjectiveSpace.openCover`: the canonical cover of `ℙ(n; S)` by `n` affine
  charts. The `i`ᵗʰ chart is `𝔸({k // k ≠ i}; S) ⟶ ℙ(n; S)`, and represents the open set where
  the function `Xᵢ` does not vanish.
- Functoriality.
-/

universe v w u

open CategoryTheory Limits MvPolynomial HomogeneousLocalization

noncomputable section

namespace AlgebraicGeometry

variable (n : Type u) (S : Scheme.{u})

attribute [local instance] gradedAlgebra

/-- `ℙ(n; S)` is the projective `n`-space over `S`.
Note that `n` is an arbitrary index type (e.g. `Fin m`). -/
def ProjectiveSpace (n : Type u) (S : Scheme.{u}) : Scheme.{max u v} :=
  pullback (terminal.from S) (terminal.from (Proj (homogeneousSubmodule n (ULift.{max u v} ℤ))))

@[inherit_doc] scoped notation "ℙ("n"; "S")" => ProjectiveSpace n S

namespace ProjectiveSpace

@[simps -isSimp]
instance over : ℙ(n; S).CanonicallyOver S where
  hom := pullback.fst _ _

/-- The map from the projective `n`-space over `S` to the integral model `Proj ℤ[n]`. -/
def toProjMvPoly : ℙ(n; S) ⟶ Proj (homogeneousSubmodule n (ULift.{max u v} ℤ)) := pullback.snd ..

end ProjectiveSpace

end AlgebraicGeometry
