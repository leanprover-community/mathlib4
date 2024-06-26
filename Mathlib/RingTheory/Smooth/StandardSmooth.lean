/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Presentation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.FinitePresentation

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

namespace Algebra

/--
A `SubmersivePresentation` of an `R`-algebra `S` is a `Presentation`
with finitely-many relations equipped with an injective `map : relations → vars`.
-/
structure SubmersivePresentation extends Algebra.Presentation R S where
  /- A map from the relations type to the variables type. -/
  map : relations → vars
  map_inj : Function.Injective map
  relations_finite : Finite relations

namespace SubmersivePresentation

attribute [instance] relations_finite

variable {R S}
variable (P : SubmersivePresentation R S)

/--
A `SubmersivePresentation` induces a `P.Ring`-linear map on
`P.relations → P.Ring`.

More precisely, the `j`-th standard basis
vector, corresponding to the `j`-th relation of `P` is mapped
to the vector of partial derivatives of `P.relation j` with respect
to the coordinates `P.map i` for all `i : P.relations`.

The determinant of this map is used to define when a `SubmersivePresentation`
is standard smooth. See `SubmersivePresentation.det`.
-/
noncomputable def linearMap : (P.relations → P.Ring) →ₗ[P.Ring] (P.relations → P.Ring) :=
  Basis.constr
    (Pi.basisFun P.Ring P.relations)
    P.Ring
    (fun j i : P.relations ↦ MvPolynomial.pderiv (P.map i) (P.relation j))

/-- The determinant of a `P : SubmersivePresentation` is the determinant
of `P.linearMap` viewed as element of `S`. -/
noncomputable def det : S :=
  algebraMap P.Ring S <| LinearMap.det P.linearMap

/-
Note: the definition of `IsStandardSmooth` does not necessarily need
`presentation_finite`.

Should we generalize this and call it `IsWeaklyStandardSmooth`
and have `IsStandardSmooth` additionally?
-/

/-- A `SubmersivePresentation` is standard smooth if its determinant is a unit
and the presentation is finite. -/
class IsStandardSmooth (P : SubmersivePresentation R S) : Prop where
  det_isUnit : IsUnit P.det
  presentation_finite : P.IsFinite

end SubmersivePresentation

/--
An `R`-algebra `S` is called standard smooth, if there
exists a standard smooth submersive presentation.
-/
class IsStandardSmooth : Prop where
  out : ∃ (P : SubmersivePresentation R S), P.IsStandardSmooth
