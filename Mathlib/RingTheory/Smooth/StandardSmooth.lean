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

In this file we define standard smooth algebras. For this we introduce
the notion of a `PreSubmersivePresentation`. This is a presentation `P` that has
fewer relations than generators. More precisely there exists an injective map from `P.rels`
to `P.vars`. To such a presentation we may associate a jacobian. `P` is then a submersive
presentation, if its jacobian is invertible.

Finally, a standard smooth algebra is an algebra that admits a submersive presentation.

While every standard smooth algebra is smooth, the converse does not hold. But if `S` is `R`-smooth,
then `S` is `R`-standard smooth locally on `S`, i.e. there exists a set `{ t }` of `S` that
generates the unit ideal, such that `Sₜ` is `R`-standard smooth for every `t` (TODO, see below).

## Main definitions

All of these are in the `Algebra` namespace. Let `S` be an `R`-algebra.

- `PreSubmersivePresentation`: A `Presentation` of `S` as `R`-algebra, equipped with an injective
  map `P.map` from `P.rels` to `P.vars`. This map is used to define the differential of a
  presubmersive presentation.

For a presubmersive presentation `P` of `S` over `R` we make the following definitions:

- `PreSubmersivePresentation.differential`: A linear endomorphism of `P.rels → P.Ring` sending
  the `j`-th standard basis vector, corresponding to the `j`-th relation, to the vector
  of partial derivatives of `P.relation j` with respect to the coordinates `P.map i` for
  `i : P.rels`.
- `PreSubmersivePresentation.jacobian`: The determinant of `P.differential`.
- `PreSubmersivePresentation.jacobiMatrix`: If `P.rels` has a `Fintype` instance, we may form
  the matrix corresponding to `P.differential`. Its determinant is `P.jacobian`.
- `SubmersivePresentation`: A submersive presentation is a finite, presubmersive presentation `P`
  with in `S` invertible jacobian.

Furthermore, for algebras we define:

- `Algebra.IsStandardSmooth`: `S` is `R`-standard smooth if `S` admits a submersive
  `R`-presentation.
- `Algebra.IsStandardSmooth.relativeDimension`: If `S` is `R`-standard smooth this is the dimension
  of an arbitrary submersive `R`-presentation of `S`. This is independent of the choice
  of the presentation (TODO, see below).
- `Algebra.IsStandardSmoothOfRelativeDimension n`: `S` is `R`-standard smooth of relative dimension
  `n` if it admits a submersive `R`-presentation of dimension `n`.

Finally, for ring homomorphisms we define:

- `RingHom.IsStandardSmooth`: A ring homomorphism `R →+* S` is standard smooth if `S` is standard
  smooth as `R`-algebra.
- `RingHom.IsStandardSmoothOfRelativeDimension n`: A ring homomorphism `R →+* S` is standard
  smooth of relative dimension `n` if `S` is standard smooth of relative dimension `n` as
  `R`-algebra.

## TODO

- Show that the canonical presentation for localization away from an element is standard smooth
  of relative dimension 0.
- Show that the base change of a submersive presentation is submersive of equal relative
  dimension.
- Show that the composition of submersive presentations of relative dimensions `n` and `m` is
  submersive of relative dimension `n + m`.
- Show that the module of Kaehler differentials of a standard smooth `R`-algebra `S` of relative
  dimension `n` is `S`-free of rank `n`. In particular this shows that the relative dimension
  is independent of the choice of the standard smooth presentation.
- Show that standard smooth algebras are smooth. This relies on the computation of the module of
  Kaehler differentials.
- Show that locally on the target, smooth algebras are standard smooth.

## Implementation details

Standard smooth algebras and ring homomorphisms feature 4 universe levels: The universe levels of
the rings involved and the universe levels of the types of the variables and relations.

## Notes

This contribution was created as part of the AIM workshop "Formalizing algebraic geometry"
in June 2024.

-/

universe t t' w w' u v

open TensorProduct

variable (n : ℕ)

namespace Algebra

variable (R : Type u) [CommRing R]
variable (S : Type v) [CommRing S] [Algebra R S]

/--
A `PreSubmersivePresentation` of an `R`-algebra `S` is a `Presentation`
with finitely-many relations equipped with an injective `map : relations → vars`.

This map determines how the differential of `P` is constructed. See
`PreSubmersivePresentation.differential` for details.
-/
@[nolint checkUnivs]
structure PreSubmersivePresentation extends Algebra.Presentation.{t, w} R S where
  /-- A map from the relations type to the variables type. Used to compute the differential. -/
  map : rels → vars
  map_inj : Function.Injective map
  relations_finite : Finite rels

namespace PreSubmersivePresentation

attribute [instance] relations_finite

variable {R S}
variable (P : PreSubmersivePresentation R S)

lemma card_relations_le_card_vars_of_isFinite [P.IsFinite] :
    Nat.card P.rels ≤ Nat.card P.vars :=
  Nat.card_le_card_of_injective P.map P.map_inj

/-- The standard basis of `P.rels → P.ring`. -/
noncomputable abbrev basis : Basis P.rels P.Ring (P.rels → P.Ring) :=
  Pi.basisFun P.Ring P.rels

/--
The differential of a `P : PreSubmersivePresentation` is a `P.Ring`-linear map on
`P.rels → P.Ring`:

The `j`-th standard basis vector, corresponding to the `j`-th relation of `P`, is mapped
to the vector of partial derivatives of `P.relation j` with respect
to the coordinates `P.map i` for all `i : P.rels`.

The determinant of this map is the jacobian of `P` used to define when a `PreSubmersivePresentation`
is submersive. See `PreSubmersivePresentation.jacobian`.
-/
noncomputable def differential : (P.rels → P.Ring) →ₗ[P.Ring] (P.rels → P.Ring) :=
  Basis.constr P.basis P.Ring
    (fun j i : P.rels ↦ MvPolynomial.pderiv (P.map i) (P.relation j))

/-- The jacobian of a `P : PreSubmersivePresentation` is the determinant
of `P.differential` viewed as element of `S`. -/
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

end PreSubmersivePresentation

/--
A `PreSubmersivePresentation` is submersive if its jacobian is a unit in `S`
and the presentation is finite.
-/
@[nolint checkUnivs]
structure SubmersivePresentation extends PreSubmersivePresentation.{t, w} R S where
  jacobian_isUnit : IsUnit toPreSubmersivePresentation.jacobian
  isFinite : toPreSubmersivePresentation.IsFinite := by infer_instance

attribute [instance] SubmersivePresentation.isFinite

/--
An `R`-algebra `S` is called standard smooth, if there
exists a submersive presentation.
-/
class IsStandardSmooth : Prop where
  out : Nonempty (SubmersivePresentation.{t, w} R S)

/--
The relative dimension of a standard smooth `R`-algebra `S` is
the dimension of an arbitrarily chosen submersive `R`-presentation of `S`.

Note: If `S` is non-trivial, this number is independent of the choice of the presentation as it is
equal to the `S`-rank of `Ω[S/R]` (TODO).
-/
noncomputable def IsStandardSmooth.relativeDimension [IsStandardSmooth R S] : ℕ :=
  ‹IsStandardSmooth R S›.out.some.dimension

/--
An `R`-algebra `S` is called standard smooth of relative dimension `n`, if there exists
a submersive presentation of dimension `n`.
-/
class IsStandardSmoothOfRelativeDimension : Prop where
  out : ∃ P : SubmersivePresentation.{t, w} R S, P.dimension = n

variable {R} {S}

lemma IsStandardSmoothOfRelativeDimension.isStandardSmooth
    [IsStandardSmoothOfRelativeDimension.{t, w} n R S] :
    IsStandardSmooth.{t, w} R S :=
  ⟨‹IsStandardSmoothOfRelativeDimension n R S›.out.nonempty⟩

end Algebra

namespace RingHom

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S]

/-- A ring homomorphism `R →+* S` is standard smooth if `S` is standard smooth as `R`-algebra. -/
def IsStandardSmooth (f : R →+* S) : Prop :=
  @Algebra.IsStandardSmooth.{t, w} _ _ _ _ f.toAlgebra

/-- A ring homomorphism `R →+* S` is standard smooth of relative dimension `n` if
`S` is standard smooth of relative dimension `n` as `R`-algebra. -/
def IsStandardSmoothOfRelativeDimension (f : R →+* S) : Prop :=
  @Algebra.IsStandardSmoothOfRelativeDimension.{t, w} n _ _ _ _ f.toAlgebra

lemma IsStandardSmoothOfRelativeDimension.isStandardSmooth (f : R →+* S)
    (hf : IsStandardSmoothOfRelativeDimension.{t, w} n f) :
    IsStandardSmooth.{t, w} f :=
  letI : Algebra R S := f.toAlgebra
  letI : Algebra.IsStandardSmoothOfRelativeDimension.{t, w} n R S := hf
  Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n

end RingHom
