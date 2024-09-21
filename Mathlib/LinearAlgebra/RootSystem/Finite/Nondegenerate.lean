/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.LinearAlgebra.RootSystem.Finite.Polarization
import Mathlib.LinearAlgebra.RootSystem.RootPositive
import Mathlib.Algebra.Ring.SumsOfSquares
import Mathlib.Algebra.Module.LocalizedModule
import Mathlib.RingTheory.Localization.FractionRing


/-!
# Nondegeneracy of the polarization on a finite root pairing

We show that if if the base ring of a root pairing is linearly ordered, the canonical bilinear form
is root-positive, positive-semidefinite on the weight space, and positive-definite on the span of
roots.

From these facts, it is easy to show that Coxeter weights in a finite root pairing are bounded
above by 4.  Thus, the pairings of roots and coroots in a root pairing are restricted to the
interval `[-4, 4]`.  Furthermore, a linearly independent pair of roots cannot have Coxeter weight 4.
For the case of crystallographic root pairings, we are thus reduced to a finite set of possible
options for each pair.

Another application is to the faithfulness of the Weyl group action on roots, and finiteness of the
Weyl group.

## Main results:

 * `polInner_rootPositive` : The inner product is root-positive.

## References:

 * SGAIII Exp. XXI
 * Bourbaki, Lie groups and Lie algebras

## Main results:

 * `polInner_rootPositive`: `PolInner` is strictly positive on roots.
 * `polInner_posDef` : `PolInner` is strictly positive on non-zero linear combinations of roots.
  That is, it is positive-definite when restricted to the linear span of roots.  This gives
  us a convenient way to eliminate certain Dynkin diagrams from the classification, since it
  suffices to produce a nonzero linear combination of simple roots with non-positive norm.

## Todo

 * Weyl-invariance
 * Faithfulness of Weyl group action, and finiteness of Weyl group, for finite root systems.
 * Relation to Coxeter weight.  In particular, positivity constraints for finite root pairings mean
  we restrict to weights between 0 and 4.

-/

noncomputable section

open Set Function
open Module hiding reflection
open Submodule (span)
open AddSubgroup (zmultiples)

namespace RootPairing


variable {ι R M N : Type*}


section LinearOrderedCommRing

variable [Fintype ι] [LinearOrderedCommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
[Module R N] (P : RootPairing ι R M N)

/-! Plan: base change of id "is" id
base change of flip "is" flip
flat base change takes bijective maps to bijective maps

-/



-- SGA3 first extends polarization to the span of roots over the field of fractions ℚ, and shows the
-- polarization is surjective there (because the image contains positive multiples of all coroots).
-- Then, using `flip`, they get equal dimension, hence injection over `ℤ`.
-- Then, P.toPerfectPairing is nondegenerate on the span of roots, since (c,r) = 0 for all c implies
-- p(r) = 0.
-- Finally, PolInner is also nondegenerate on the span of roots, since
-- it is a composition with a spanning injection.

-- I need base change to be an injection on weight spaces, and this uses reflexivity and flatness.

/-! This strategy seems doomed.
theorem polarization_injective : InjOn P.Polarization (span R (range P.root)) := by
  intro x hx y hy hxy
  rw [SetLike.mem_coe, mem_span_range_iff_exists_fun] at hx
  obtain ⟨cx, hcx⟩ := hx
  rw [SetLike.mem_coe, mem_span_range_iff_exists_fun] at hy
  obtain ⟨cy, hcy⟩ := hy
  have hp : 4 • P.flip.Polarization (P.Polarization x) =
      4 • P.flip.Polarization (P.Polarization y) :=
    congrArg (HSMul.hSMul 4) (congrArg (⇑P.flip.Polarization) hxy)
  rw [← hcx, ← hcy, map_sum, map_sum, map_sum, map_sum] at hp
  sorry
-/

--use IsSumSq.nonneg ?
theorem polInner_self_non_neg (x : M) : 0 ≤ P.PolInner x x := by
  simp only [PolInner, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, comp_apply,
    polarization_self, toLin_toPerfectPairing]
  exact Finset.sum_nonneg fun i _ =>
    (sq (P.toPerfectPairing x (P.coroot i))) ▸ sq_nonneg (P.toPerfectPairing x (P.coroot i))

theorem polInner_self_zero_iff (x : M) :
    P.PolInner x x = 0 ↔ ∀ i, P.toPerfectPairing x (P.coroot i) = 0 := by
  simp only [PolInner_apply, PerfectPairing.toLin_apply, LinearMap.coe_comp, comp_apply,
    Polarization_apply, map_sum, map_smul, smul_eq_mul]
  convert sum_of_squares_eq_zero_iff Finset.univ fun i => (P.toPerfectPairing x) (P.coroot i)
  constructor
  · intro x _
    exact x
  · rename_i i
    intro x
    refine x ?_
    exact Finset.mem_univ i

-- Use four_smul_flip_polarization_polarization to get injectivity of Polarization.

--lemma coxeter_weight_leq_4 :

lemma polInner_root_self_pos (j : ι) :
    0 < P.PolInner (P.root j) (P.root j) := by
  simp only [PolInner, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, comp_apply,
    polarization_root_self, toLin_toPerfectPairing]
  refine Finset.sum_pos' (fun i _ => (sq (P.pairing j i)) ▸ sq_nonneg (P.pairing j i)) ?_
  use j
  refine ⟨Finset.mem_univ j, ?_⟩
  simp only [pairing_same, Nat.ofNat_pos, mul_pos_iff_of_pos_left]

lemma polInner_rootPositive : IsRootPositive P P.PolInner where
  zero_lt_apply_root i := P.polInner_root_self_pos i
  symm := P.polInner_symmetric
  apply_reflection_eq := P.polInner_reflection_reflection_apply

/-!
lemma positive_definite_polInner {x : M} (hx : x ∈ span R (range P.root)) (h : P.PolInner x x = 0) :
    x = 0 := by
  rw [mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, hc⟩ := hx
  rw [← hc] at h
  simp at h

  sorry

For any bilinear form over a commutative ring,
`|(x,y) • x - (x,x) • y|^2 = |x|^2(|x|^2 * |y|^2 - (x,y)^2)` (easy cancellation)
LinearOrderedCommRing version of Cauchy-Schwarz: right side of above is non-neg, and only zero when
`(x,y) • x - (x,x) • y = 0`, i.e., linearly dependent.

This constrains coxeterWeight to at most 4, and proportionality when 4.
-/

-- faithful Weyl action on roots: for all x, w(x)-x lies in R-span of roots.
--If all roots are fixed by w, then (w(x)-x, r) = (x, w^-1r -r)=0. w(x) - w by nondeg on R-span.
-- finiteness of Weyl follows from finiteness of permutations of roots.

--positivity constraints for finite root pairings mean we restrict to weights between 0 and 4.

/-!
theorem : if there is a nonzero vector with nonpositive norm in the span of roots, then the root
pairing is infinite.
Maybe better to say, given a finite root pairing, all nonzero combinations of simple roots have
strictly positive norm.
Then, we can say, a Dynkin diagram is not finite type if there is a nonzero combination of simple
roots that has nonpositive norm.
-/
end LinearOrderedCommRing

end RootPairing

end
