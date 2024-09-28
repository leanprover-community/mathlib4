/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.LinearAlgebra.RootSystem.Finite.Polarization


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

/-! From SGA3 lemma 1.2.1 (10), we have a linear map `Polarization: M → N`.

Polarization maps the span of roots to the span of coroots. - done.

This restricted map has torsion cokernel.

I would like to say that the span of roots has `Module.rank` at least the span of coroots, since
this map is almost surjective.

From Mathlib.LinearAlgebra.Dimension.Localization:
theorem rank_quotient_add_rank_of_isDomain [IsDomain R] (M' : Submodule R M) :
    Module.rank R (M ⧸ M') + Module.rank R M' = Module.rank R M := by sorry

Use M = span of coroots, M' = image of Polarization.
Then, it suffices to show the quotient, i.e., the cokernel has rank zero.

This should follow from the fact that there are no linearly independent sets of size one,
since they are all killed by a certain positive element, i.e., a nonzero divisor.

Thus, we have image of polarization has same rank as span of coroots.

Note LinearMap.rank is just Module.rank of LinearMap.range.

Also need: rank of source is at least rank of image: rank_le_domain
(LinearAlgebra.Dimension.LinearMap)

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

-- this is a copy just for imports
lemma prod_canonicalBilinear_root_self_pos' :
    0 < ∏ i, P.CanonicalBilinear (P.root i) (P.root i) :=
  Finset.prod_pos fun i _ => canonicalBilinear_root_self_pos P i


-- Use four_smul_flip_polarization_polarization to get injectivity of Polarization.


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
