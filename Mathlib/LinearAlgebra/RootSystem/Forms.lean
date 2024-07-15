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

variable {ι R M N : Type*}

namespace RootPairing

section

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A Prop-valued class for a bilinear form to be compatible with a root system. -/
class IsRootInvariant (P : RootPairing ι R M N) (B : M →ₗ[R] M →ₗ[R] R) : Prop where
  root_ne : ∀ i : ι, B (P.root i) (P.root i) ≠ 0
  symm : ∀ x y : M, B x y = B y x
  refl_inv : ∀ (i : ι) (x y : M), B (P.reflection i x) (P.reflection i y) = B x y

/-- A Prop-valued class for symmetrizability of a root pairing. -/
class IsSymmetrizable (P : RootPairing ι R M N) : Prop where
  exists_inv_form : ∃ B : M →ₗ[R] M →ₗ[R] R, IsRootInvariant P B

/-! Show: reflection in x takes y to `y - 2(x,y)/(x,x) x`.
If y is fixed by reflection in x = P.root i, then B (-x) y = B x y = 0.
If y is inverted by reflection in x, then B (-x) (-y) = B x y.

What can we do with a symmetrizable root pairing?  We'd have to choose a form each time we did
something.  Better to talk about a pair given by a root
pairing and a symmetric invariant form. Existence is useful for elimination in classification.

theorem : if there is a nonzero vector with nonpositive norm in the span of roots, then the root
pairing is infinite.
Maybe better to say, given a finite root pairing, all nonzero combinations of simple roots have
strictly positive norm.
Then, we can say, a Dynkin diagram is not finite type if there is a nonzero combination of simple
roots that has nonpositive norm.
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

theorem Polarization_self (P : RootPairing ι R M N) [Finite ι] (x : M) :
    haveI := Fintype.ofFinite ι
    P.toLin x (P.Polarization x) =
      ∑ (i : ι), P.toLin x (P.coroot i) * P.toLin x (P.coroot i) := by
  simp [Polarization]

theorem Polarization_root_self (P : RootPairing ι R M N) [Finite ι] (j : ι) :
    haveI := Fintype.ofFinite ι
    P.toLin (P.root j) (P.Polarization (P.root j)) =
      ∑ (i : ι), (P.pairing j i) * (P.pairing j i) := by
  simp [Polarization]

-- reflections taken to coreflections.  polarization_self = sum of squares

/-- An invariant inner product on the weight space. -/
def PolInner (P : RootPairing ι R M N) [Finite ι] : M →ₗ[R] M →ₗ[R] R where
  toFun x := P.toLin x ∘ₗ P.Polarization
  map_add' x y := by simp only [map_add, LinearMap.add_comp]
  map_smul' r x := by simp only [LinearMapClass.map_smul, RingHom.id_apply, LinearMap.smul_comp]

/-!
theorem positive_norm [OrderedCommRing R] (P : RootPairing ι R M N) [Finite ι] (i : ι) :
    PolInner P (P.root i) (P.root i) > 0 := by
  sorry

symmetric, positive definite on R-span of roots, Weyl-invariant.  If `P` is crystallographic,
then this takes integer values. `(α,α)α^* = 2P.Polarization α` -/

-- faithful Weyl action, finiteness of Weyl
end


section ordered

variable [LinearOrderedCommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
(P : RootPairing ι R M N)

theorem PolInner_self_non_neg [Finite ι] (x : M) : 0 ≤ P.PolInner x x := by
  simp only [PolInner, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, comp_apply,
    Polarization_self]
  exact Finset.sum_nonneg fun i _ =>
    (sq (P.toLin x (P.coroot i))) ▸ sq_nonneg (P.toLin x (P.coroot i))

theorem PolInner_root_self_pos [Finite ι] (j : ι) :
    0 < P.PolInner (P.root j) (P.root j) := by
  simp only [PolInner, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, comp_apply,
    Polarization_root_self]
  refine Finset.sum_pos' ?_ ?_
  · exact fun i _ => (sq (P.pairing j i)) ▸ sq_nonneg (P.pairing j i)
  use j
  refine ⟨letI := Fintype.ofFinite ι; Finset.mem_univ j, ?_⟩
  rw [pairing, root_coroot_two]
  norm_num

end ordered


end RootPairing
