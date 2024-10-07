/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear


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

 * `RootForm_posDef` : `RootForm` is strictly positive on non-zero linear combinations of roots.
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

variable [Fintype ι] [LinearOrderedCommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
[Module R N] (P : RootPairing ι R M N)

lemma rank_polarization_eq_rank_span_coroot :
    LinearMap.rank P.Polarization = Module.rank R (span R (range P.coroot)) := by
  refine eq_of_le_of_le (Submodule.rank_mono P.range_polarization_le_span_coroot) ?_
  letI : IsReflexive R N := PerfectPairing.reflexive_right P.toPerfectPairing
  refine rank_le_of_smul_regular (span R (range P.coroot)) (LinearMap.range P.Polarization)
    (injective_smul_pos_of_reflexive P.prod_rootForm_root_self_pos) ?_
  intro x hx
  obtain ⟨c, hc⟩ := (mem_span_range_iff_exists_fun R).mp hx
  rw [← hc, Finset.smul_sum]
  simp_rw [smul_smul, mul_comm, ← smul_smul]
  exact Submodule.sum_smul_mem (LinearMap.range P.Polarization) c
    (fun c _ ↦ prod_rootForm_smul_coroot_in_range P c)

lemma rank_coPolarization_eq_rank_span_root :
    LinearMap.rank P.CoPolarization = Module.rank R (span R (range P.root)) :=
  P.flip.rank_polarization_eq_rank_span_coroot

lemma rank_polarization_domRestrict_eq_rank_span_coroot :
    LinearMap.rank (P.Polarization.domRestrict (span R (range P.root))) =
      Module.rank R (span R (range P.coroot)) := by
  refine eq_of_le_of_le (Submodule.rank_mono P.range_polarization_domRestrict_le_span_coroot) ?_
  letI : IsReflexive R N := PerfectPairing.reflexive_right P.toPerfectPairing
  refine rank_le_of_smul_regular (span R (range P.coroot))
    (LinearMap.range (P.Polarization.domRestrict (span R (range P.root))))
    (injective_smul_pos_of_reflexive P.prod_rootForm_root_self_pos) ?_
  intro x hx
  obtain ⟨c, hc⟩ := (mem_span_range_iff_exists_fun R).mp hx
  rw [← hc, Finset.smul_sum]
  simp_rw [smul_smul, mul_comm, ← smul_smul]
  exact Submodule.sum_smul_mem
    (LinearMap.range (P.Polarization.domRestrict (span R (range P.root)))) c
    (fun c _ ↦ prod_rootForm_smul_coroot_in_range_domRestrict P c)

lemma rank_Polarization_domRestrict :
    LinearMap.rank (P.Polarization.domRestrict (span R (range P.root))) =
      LinearMap.rank P.Polarization :=
  P.rank_polarization_domRestrict_eq_rank_span_coroot.trans
    P.rank_polarization_eq_rank_span_coroot.symm

/-!
lemma polarization_kernel_rank_zero : Module.rank R (LinearMap.ker (LinearMap.domRestrict
    P.Polarization (span R (range P.root)))) = 0 := by
  have rn := rank_quotient_add_rank_of_isDomain (LinearMap.ker (LinearMap.domRestrict
    P.Polarization (span R (range P.root))))
  rw [← rank_coPolarization_eq_rank_span_root] at rn
  let e := (P.Polarization.domRestrict (span R (range ⇑P.root))).quotKerEquivRange
  have h := LinearEquiv.lift_rank_eq e
  rw [h] at rn -- universe problems
  sorry

have:
range Polarization ⊆ span R range P.coroot
Polarization rank = rank span R range P.coroot
range CoPolarization ⊆ span R range P.root
coPolarization rank = rank span R range P.root

need :

       same for CoPolarization
Then, using rank range ≤ rank domain (`LinearMap.rank_le_domain`), we get:
rank (span R (range P.coroot)) ≤ rank (span R (range P.root)) and
rank (span R (range P.root)) ≤ rank (span R (range P.coroot)) hence equality.

To show kernel of P.Polarization.domRestrict (span R (range P.root)) has rank zero,
use LinearMap.quotKerEquivRange to identify image with quotient.
When they have the same rank, then the kernel has rank zero.
To show the kernel vanishes, take `x` in kernel, use rank_eq_zero_iff to get suitable nonzero `r`.
Then, x = 0 by injective_smul_pos_of_reflexive.

use finite_rank_of_reflexive

-/
--lemma polarization_restriction_injective : restriction of P.Polarization to range P.root is inj.

-- injectivity from lemma: reflexive modules over a domain have no torsion
--torsion_free_of_reflexive or injective_smul_pos_of_reflexive

lemma rank_eq_zero_iff : Module.rank R M = 0 ↔ ∀ x : M, ∃ a : R, a ≠ 0 ∧ a • x = 0 :=
  _root_.rank_eq_zero_iff

theorem rank_quotient_add_rank_of_isDomain [IsDomain R] (M' : Submodule R M) :
    Module.rank R (M ⧸ M') + Module.rank R M' = Module.rank R M :=
  HasRankNullity.rank_quotient_add_rank M'

--lemma coxeter_weight_leq_4 (i j : ι) : coxeterWeight i j ≤ 4 := by sorry



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

end RootPairing

end
