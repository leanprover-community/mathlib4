/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.LinearAlgebra.RootSystem.Defs

/-!
# Weyl-invariant forms on root pairings

This file contains basic results on Weyl-invariant inner products for root systems and root data.
We introduce a Prop-valued mixin for classes that admit Weyl-invariant forms such that all roots
have nonzero norm.  We show that finite root data over ordered rings always admit positive-definite
invariant forms.

## Main definitions:

 * `Symmetrizable`: A prop-valued mixin class for root pairings that admit Weyl-invariant forms such
  that all rootshave nonzero norm.
 * `Polarization`: A distinguished map from the weight space to the coweight space.
 * `

## References:

 * SGAIII Exp. XXI
 * Bourbaki, Lie groups and Lie algebras

## Main results:

 * Faithfulness of Weyl group action, and finiteness of Weyl group, for finite root systems.

## Todo

 *

-/

open Set Function
open Module hiding reflection
open Submodule (span)
open AddSubgroup (zmultiples)

noncomputable section

namespace RootPairing

variable {ι R M N : Type*}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A Prop-valued class for symmetrizability of a root pairing. -/
class IsSymmetrizable (P : RootPairing ι R M N) : Prop where
  exists_inv_form : ∃ B : M →ₗ[R] M →ₗ[R] R,
    (∀ i : ι, B (P.root i) (P.root i) ≠ 0) ∧
    (∀ x y : M, B x y = B y x) ∧
    (∀ (i : ι) (x y : M), B (P.reflection i x) (P.reflection i y) = B x y)

/-! Do I want a compatibility with the root pairing in some way, e.g., reflection in x takes y to
`y - 2(x,y)/(x,x) x`?  Does this follow automatically from invariance?

what can we do with a symmetrizable root pairing?  Better to talk about a pair given by a root
pairing and a symmetric invariant form. Existence is useful for elimination in classification.

theorem : if there is a nonpositive norm nonzero vector in the span of roots, then the root
pairing is infinite.
Maybe better to say, given a finite root pairing, there are no nonpositive norm zero vectors in
the span of roots.
Then, we can say, a Dynkin diagram is not finite type if there is a nonzero combination of simple
roots that has norm zero.
-/

/-- An invariant linear map from weight space to coweight space. -/
def Polarization (P : RootPairing ι R M N) [Finite ι] : M →ₗ[R] N where
  toFun m :=
    haveI := Fintype.ofFinite ι
    ∑ (i : ι), P.toLin m (P.coroot i) • (P.coroot i)
  map_add' x y := by
    simp only [map_add, LinearMap.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_assoc]

theorem Polarization_self (P : RootPairing ι R M N) [Finite ι] (j : ι) :
    haveI := Fintype.ofFinite ι
    P.toLin (P.root j) (P.Polarization (P.root j)) = ∑ (i : ι), (P.pairing j i) * (P.pairing j i) := by
  simp [Polarization]

-- reflections taken to coreflections.  polarization_self = sum of squares

/-- An invariant inner product on the weight space. -/
def PolInner (P : RootPairing ι R M N) [Finite ι] : M →ₗ[R] M →ₗ[R] R where
  toFun x := P.toLin x ∘ₗ P.Polarization
  map_add' x y := by simp only [map_add, LinearMap.add_comp]
  map_smul' r x := by simp only [LinearMapClass.map_smul, RingHom.id_apply, LinearMap.smul_comp]

/-!
theorem positive_norm [OrderedCommRing R] (P : RootPairing ι R M N) [Finite ι] (i : ι) :
    PolInner P (P.root i) (P.root i) ≥ 0 := by
  sorry

symmetric, positive definite on R-span of roots, Weyl-invariant.  If `P` is crystallographic,
then this takes integer values. `(α,α)α^* = 2P.Polarization α` -/

-- faithful Weyl action, finiteness of Weyl
