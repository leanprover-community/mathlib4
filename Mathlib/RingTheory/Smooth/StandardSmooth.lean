/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jung Tao Cheng, Christian Merten, Andrew Yang
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.Presentation

/-!
# Standard smooth algebras

In this file we define standard smooth presentations for algebras. This notion
is introduced for `SubmersivePresentations`, which is a `Presentation`
that has less relations than generators. More precisely there exists
an injective map from `P.relations` to `P.vars`.

Finally, we introduce the notion of standard smooth algebras, which are algebras that
admit a standard smooth presentation.

## Main definitions

All of these are in the `Algebra` namespace. Let `S` be an `R`-algebra.

- `SubmersivePresentation`: A `Presentation` of `S` as `R`-algebra, equipped with an injective map
  from `P.relations` to `P.vars`. This map is used to define the differential of a submersive
  presentation.

Let now `P` be a submersive presentation of `S` over `R`.

- `SubmersivePresentation.differential`: A linear endomorphism of `P.rels → P.ring` sending
  the `j`-th standard basis vector, corresponding to the `j`-th relation, to the vector
  of partial derivatives of `P.relation j` with respect to the coordinates `P.map i` for
  `i : P.rels`.
- `SubmersivePresentation.jacobian`: The determinant of `P.differential`.
- `SubmersivePresentation.jacobiMatrix`: If `P.rels` has a `Fintype` instance, we may form
  the matrix corresponding to `P.differential`. Its determinant is `P.jacobian`.
- `SubmersivePresentation.IsStandardSmooth`: `P` is standard smooth, if it's jacobian
  is a unit in `S` and it is finite.

Furthermore, we define:

- `IsStandardSmooth`: `S` is `R`-standard smooth if `S` has a standard smooth submersive
  `R`-presentation.
- `IsOfRelativeDimension n`: A standard smooth `R`-algebra `S` is of relative dimension `n`
  if `S` has a standard smooth submersive `R`-presentation of dimension `n`. Equivalently,
  that every standard smooth has dimension `n` (TODO, see below).

Finally, in the `RingHom` namespace we define

- `IsStandardSmooth`: A ring hom `R →+* S` is standard smooth if `S` is standard smooth as
  `R`-algebra.

## TODO

- Show that the canonical presentation for localization away from an element is standard smooth
  of relative dimension 0.
- Show that the base change of a standard smooth presentation is standard smooth of equal relative
  dimension.
- Show that the composition of standard smooth presentations of relative dimensions `n` and `m` is
  standard smooth of relative dimension `n + m`.
- Show that the Kaehler differentials of a standard smooth `R`-algebra `S` of relative dimension `n`
  are `S`-free of rank `n`. In particular this shows that the relative dimension is independent
  of the choice of the standard smooth presentation.

## Implementation details

We don't bundle `IsStandardSmooth` and `IsOfRelativeDimension n` in one typeclass, because then
`IsStandardSmooth` can't be inferred from `StandardSmoothOfRelativeDimension n` as Lean can't know
which `n` to choose. Mathematically this is still correct, since the dimension
does not depend on the choice of the standard smooth presentation.

Standard smooth algebras and ring homs feature 4 universe levels: The universe levels of the rings
involved and the universe levels of the types of the variables and relations.

## Notes

This contribution was created as part of the AIM workshop "Formalizing algebraic geometry"
in June 2024.

-/

universe t t' w w' u v

variable (R : Type u) [CommRing R]
variable (S : Type v) [CommRing S] [Algebra R S]

open TensorProduct

namespace Algebra

/--
A `SubmersivePresentation` of an `R`-algebra `S` is a `Presentation`
with finitely-many relations equipped with an injective `map : relations → vars`.

This map determines how the differential of `P` is constructed. See
`SubmersivePresentation.differential` for details.
-/
@[nolint checkUnivs]
structure SubmersivePresentation extends Algebra.Presentation.{t, w} R S where
  /-- A map from the relations type to the variables type. Used to compute the differential. -/
  map : rels → vars
  map_inj : Function.Injective map
  relations_finite : Finite rels

namespace SubmersivePresentation

attribute [instance] relations_finite

variable {R S}
variable (P : SubmersivePresentation R S)

lemma card_relations_le_card_vars_of_isFinite [P.IsFinite] :
    Nat.card P.rels ≤ Nat.card P.vars :=
  Nat.card_le_card_of_injective P.map P.map_inj

/-- The standard basis of `P.rels → P.ring`. -/
noncomputable abbrev basis : Basis P.rels P.Ring (P.rels → P.Ring) :=
  Pi.basisFun P.Ring P.rels

/--
The differential of a `P : SubmersivePresentation` is a `P.Ring`-linear map on
`P.rels → P.Ring`:

The `j`-th standard basis vector, corresponding to the `j`-th relation of `P` is mapped
to the vector of partial derivatives of `P.relation j` with respect
to the coordinates `P.map i` for all `i : P.rels`.

The determinant of this map is the jacobian of `P` used to define when a `SubmersivePresentation`
is standard smooth. See `SubmersivePresentation.jacobian`.
-/
noncomputable def differential : (P.rels → P.Ring) →ₗ[P.Ring] (P.rels → P.Ring) :=
  Basis.constr P.basis P.Ring
    (fun j i : P.rels ↦ MvPolynomial.pderiv (P.map i) (P.relation j))

/-- The jacobian of a `P : SubmersivePresentation` is the determinant
of `P.linearMap` viewed as element of `S`. -/
noncomputable def jacobian : S :=
  algebraMap P.Ring S <| LinearMap.det P.differential

section Matrix

variable [Fintype P.rels] [DecidableEq P.rels]

/--
If `P.rels` has a `Fintype` and `DecidableEq` instance, the differential of `P`
can be expressed in matrix form.
-/
noncomputable def jacobiMatrix : Matrix P.rels P.rels P.Ring :=
  LinearMap.toMatrix P.basis P.basis P.differential

lemma jacobian_eq_jacobiMatrix_det : P.jacobian = algebraMap P.Ring S P.jacobiMatrix.det := by
   simp [jacobiMatrix, jacobian]

lemma jacobiMatrix_apply (i j : P.rels) :
    P.jacobiMatrix i j = MvPolynomial.pderiv (P.map i) (P.relation j) := by
  simp [jacobiMatrix, LinearMap.toMatrix, differential]

end Matrix

/--
A `SubmersivePresentation` is standard smooth if its jacobian is a unit in `S`
and the presentation is finite.
-/
class IsStandardSmooth : Prop where
  jacobian_isUnit : IsUnit P.jacobian
  isFinite : P.IsFinite := by infer_instance

attribute [instance] IsStandardSmooth.isFinite

end SubmersivePresentation

/--
An `R`-algebra `S` is called standard smooth, if there
exists a standard smooth submersive presentation.
-/
class IsStandardSmooth : Prop where
  out : ∃ (P : SubmersivePresentation.{t, w} R S), P.IsStandardSmooth

/--
A standard smooth `R`-algebra `S` is of relative dimension `n`, if there
exists a standard smooth submersive presentation of dimension `n`.

Note: The relative dimension of a standard smooth `R`-algebra `S` is independent of
the choice of the presentation as it is equal to the `S`-rank of `Ω[S/R]` (TODO).
-/
class IsOfRelativeDimension (n : ℕ) [IsStandardSmooth R S] : Prop where
  out : ∃ (P : SubmersivePresentation.{t, w} R S), P.IsStandardSmooth ∧ P.dimension = n

end Algebra

namespace RingHom

variable {R S}

/-- A ring hom `R →+* S` is standard smooth if `S` is standard smooth as `S`-algebra. -/
def IsStandardSmooth (f : R →+* S) : Prop :=
  @Algebra.IsStandardSmooth.{t, w} _ _ _ _ f.toAlgebra

/-- A standard smooth ring hom `R →+* S` is standard smooth of relative dimension `n`
if `S` has relative dimension `n` as `R`-algebra. -/
def IsOfRelativeDimension (n : ℕ) (f : R →+* S) (hf : f.IsStandardSmooth) : Prop :=
  @Algebra.IsOfRelativeDimension.{t, w} _ _ _ _ f.toAlgebra n hf

end RingHom
