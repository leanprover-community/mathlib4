/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Projective space

## Main definitions

- `AlgebraicGeometry.ProjectiveSpace`: `ℙ(n; S)` is the projective `n`-space over a scheme `S`.

## TODO

- `AlgebraicGeometry.ProjectiveSpace.SpecIso`: `ℙ(n; Spec R) ≅ Proj R[n]`.
- `AlgebraicGeometry.ProjectiveSpace.openCover`: the canonical cover of `ℙ(n; S)` by `n` affine
  charts. The `i`ᵗʰ chart is `𝔸({k // k ≠ i}; S) ⟶ ℙ(n; S)`, and represents the open set where
  the function `Xᵢ` does not vanish.
- Functoriality of `ProjectiveSpace` on the `S` component.
- Show that a map `Spec A ⟶ ℙ(n; S)` corresponds to a map `p : Spec A ⟶ S` and a unique
  `A`-submodule `N` of `n →₀ A` such that `(n →₀ A) ⧸ N` is locally free of rank 1.
-/

universe u

open CategoryTheory Limits MvPolynomial HomogeneousLocalization

noncomputable section

namespace AlgebraicGeometry

variable (n : Type u) (S : Scheme.{u})

attribute [local instance] gradedAlgebra

/-- The structure of a graded algebra on `ℤ[n]`, i.e. on `MvPolynomial n (ULift.{u} ℤ)`. -/
local notation3 "ℤ[" n "].{" u "}" => homogeneousSubmodule n (ULift.{u} ℤ)

/-- `ℙ(n; S)` is the projective `n`-space over a scheme `S`.
Note that `n` is an arbitrary index type (e.g. `ULift (Fin m)`). -/
def ProjectiveSpace (n : Type u) (S : Scheme.{u}) : Scheme.{u} :=
  pullback (terminal.from S) (terminal.from (Proj ℤ[n].{u}))

@[inherit_doc] scoped notation "ℙ("n"; "S")" => ProjectiveSpace n S

namespace ProjectiveSpace

@[simps -isSimp]
instance over : ℙ(n; S).CanonicallyOver S where
  hom := pullback.fst _ _

/-- The map from the projective `n`-space over `S` to the integral model `Proj ℤ[n]`. -/
def toProjMvPoly : ℙ(n; S) ⟶ Proj ℤ[n].{u} := pullback.snd _ _

end ProjectiveSpace

end AlgebraicGeometry
