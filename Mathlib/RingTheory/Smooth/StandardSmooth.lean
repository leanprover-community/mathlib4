/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Presentation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.FinitePresentation

/-!
# Standard smooth algebras

In this file we define standard smooth presentations for algebras. This notion
is introduced for `SubmersivePresentations`, which is a `Presentation`
that has less relations than generators. More precisely there exists
an injective map from `P.relations` to `P.vars`.

-/

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

/--
A `SubmersivePresentation` is standard smooth of relative dimension `n` if it is
standard smooth and the presentation is of dimension `n`.
-/
class IsStandardSmoothOfRelativeDimension (P : SubmersivePresentation R S) (n : ℕ) : Prop where
  isStandardSmooth : P.IsStandardSmooth
  of_relative_dimension : P.dimension = n

end SubmersivePresentation

/--
An `R`-algebra `S` is called standard smooth, if there
exists a standard smooth submersive presentation.
-/
class IsStandardSmooth : Prop where
  out : ∃ (P : SubmersivePresentation R S), P.IsStandardSmooth

/--
An `R`-algebra `S` is called standard smooth of relative dimension `n`, if there
exists a standard smooth submersive presentation.
-/
class IsStandardSmoothOfRelativeDimension (n : ℕ) : Prop where
  out : ∃ (P : SubmersivePresentation R S), P.IsStandardSmoothOfRelativeDimension n

end Algebra

open TensorProduct Algebra

noncomputable
def foo2 {R S T} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (P : SubmersivePresentation R S) : SubmersivePresentation T (T ⊗[R] S) where
  __ := P.foo2
  map := P.map
  map_inj := P.map_inj
  relations_finite := P.relations_finite

theorem GOAL {R S T} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (P : SubmersivePresentation R S) (hP : P.IsStandardSmooth) : (foo2 P (T := T)).IsStandardSmooth := by
  classical
  constructor
  let P' := foo2 P (T := T)
  cases nonempty_fintype P.relations
  obtain ⟨a⟩ := nonempty_fintype P'.relations
  have : LinearMap.toMatrix (Pi.basisFun _ _) (Pi.basisFun _ _) P'.linearMap =
    (MvPolynomial.map (algebraMap R T)).mapMatrix
      (LinearMap.toMatrix (Pi.basisFun _ _) (Pi.basisFun _ _) P.linearMap) := by
    ext i j : 1
    simp [LinearMap.toMatrix, SubmersivePresentation.linearMap, P', foo2, Presentation.foo2]
    induction' P.relation j using MvPolynomial.induction_on
    · simp
      erw [MvPolynomial.map_C]
      simp
    · simp[*]
    · simp[*, Pi.single_apply]
      split <;> rfl
  apply_fun Matrix.det at this
  erw [← RingHom.map_det] at this
  simp only [LinearMap.det_toMatrix] at this
  erw [SubmersivePresentation.det, this]
  have := hP.1.map (Algebra.TensorProduct.includeRight (R := R) (A := T))
  convert this
  erw [LinearMap.det_toMatrix]
  simp
  erw [MvPolynomial.aeval_map_algebraMap]
  show _ = Algebra.TensorProduct.includeRight (MvPolynomial.aeval _ _)
  erw [MvPolynomial.map_aeval]
  erw [(Algebra.TensorProduct.includeRight).comp_algebraMap]
  rfl
  exact ⟨hP.2.1, hP.2.2⟩
