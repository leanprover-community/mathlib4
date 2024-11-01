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

We show that if if the base ring of a finite root pairing is linearly ordered, then the canonical
bilinear form is root-positive, positive-semidefinite on the weight space, and positive-definite on
the span of roots.

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

variable {ι R M N S : Type*}

variable [Fintype ι] [LinearOrderedCommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
[Module R N] (P : RootPairing ι R M N)

lemma span_root_finite : Module.Finite R (span R (range P.root)) :=
  Finite.span_of_finite R <| finite_range P.root

lemma span_coroot_finite : Module.Finite R (span R (range P.coroot)) :=
  Finite.span_of_finite R <| finite_range P.coroot

lemma span_root_finite_rank : Module.rank R ↥(span R (range ⇑P.root)) < Cardinal.aleph0 := by
  haveI := span_root_finite P
  exact rank_lt_aleph0 R ↥(span R (range ⇑P.root))

lemma finrank_eq_rank_span_root :
    Module.finrank R (span R (range P.root)) = Module.rank R (span R (range P.root)) := by
  haveI := span_root_finite P
  exact finrank_eq_rank R ↥(span R (range P.root))

lemma finrank_eq_rank_span_coroot :
    Module.finrank R (span R (range P.coroot)) = Module.rank R (span R (range P.coroot)) := by
  haveI := span_coroot_finite P
  exact finrank_eq_rank R ↥(span R (range P.coroot))

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

lemma rank_coPolarization_eq_rank_span_root :
    LinearMap.rank P.CoPolarization = Module.rank R (span R (range P.root)) :=
  P.flip.rank_polarization_eq_rank_span_coroot

lemma rank_coPolarization_domRestrict_eq_rank_span_root :
    LinearMap.rank (P.CoPolarization.domRestrict (span R (range P.coroot))) =
      Module.rank R (span R (range P.root)) :=
  P.flip.rank_polarization_domRestrict_eq_rank_span_coroot

lemma finrank_polarization_domRestrict :
    finrank R (LinearMap.range (P.Polarization.domRestrict (span R (range P.root)))) =
      finrank R (span R (range P.coroot)) := by
  refine finrank_eq_of_rank_eq ?h
  rw [finrank_eq_rank_span_coroot]
  exact rank_polarization_domRestrict_eq_rank_span_coroot P

lemma rank_coPolarization_domRestrict :
    LinearMap.rank (P.CoPolarization.domRestrict (span R (range P.coroot))) =
      LinearMap.rank P.CoPolarization :=
  P.flip.rank_Polarization_domRestrict

lemma finrank_span_root_le :
    Module.finrank R (span R (range P.coroot)) ≤ Module.finrank R (span R (range P.root)) := by
  have h := lift_rank_map_le P.Polarization (span R (range P.root))
  refine finrank_le_finrank_of_rank_le_rank (le_of_eq_of_le ?_ h) (span_root_finite_rank P)
  rw [← rank_polarization_domRestrict_eq_rank_span_coroot, ← LinearMap.range_domRestrict]

lemma finrank_span_root_eq :
    Module.finrank R (span R (range P.coroot)) = Module.finrank R (span R (range P.root)) :=
  Nat.le_antisymm (finrank_span_root_le P) (by simpa using finrank_span_root_le P.flip)

/-!
To show the kernel vanishes, take `x` in kernel, use rank_eq_zero_iff to get suitable nonzero `r`.
Then, x = 0 by injective_smul_pos_of_reflexive.
-/
lemma polarization_kernel_finrank_zero : Module.finrank R (LinearMap.ker (LinearMap.domRestrict
    P.Polarization (span R (range P.root)))) = 0 := by
  haveI := span_root_finite P
  have h := Submodule.finrank_quotient_add_finrank
    (LinearMap.ker (LinearMap.domRestrict P.Polarization (span R (range P.root))))
  rw [LinearEquiv.finrank_eq (P.Polarization.domRestrict (span R
    (range P.root))).quotKerEquivRange, ← finrank_span_root_eq, finrank_polarization_domRestrict,
    Nat.add_eq_left] at h
  exact h

lemma polarization_domRestrict_kernel_rank_zero : Module.rank R (LinearMap.ker
    (LinearMap.domRestrict P.Polarization (span R (range P.root)))) = 0 := by
  have h := Submodule.rank_quotient_add_rank
    (LinearMap.ker (LinearMap.domRestrict P.Polarization (span R (range P.root))))
  have h3 := congrArg Cardinal.lift.{u_4, u_3} h
  rw [Cardinal.lift_add, LinearEquiv.lift_rank_eq ((P.Polarization.domRestrict (span R
    (range P.root))).quotKerEquivRange), show (Module.rank R (LinearMap.range
    (P.Polarization.domRestrict (span R (range P.root))))) = LinearMap.rank
    (P.Polarization.domRestrict (span R (range P.root))) by rfl,
    rank_polarization_domRestrict_eq_rank_span_coroot, ← finrank_eq_rank_span_coroot,
    ← finrank_eq_rank_span_root, finrank_span_root_eq] at h3
  refine Cardinal.lift_injective.{u_4, u_3} ?_
  have h6 : Cardinal.lift.{u_4,u_3} (finrank R ↥(span R (range ⇑P.root))) < Cardinal.aleph0 :=
    Cardinal.lift_lt_aleph0.mpr (Cardinal.nat_lt_aleph0 (finrank R ↥(span R (range ⇑P.root))))
  exact Cardinal.eq_of_add_eq_add_left (by simpa using h3) h6

lemma polarization_domRestrict_injective :
    Injective (LinearMap.domRestrict P.Polarization (span R (range P.root))) := by
  have htor := rank_eq_zero_iff.mp (polarization_domRestrict_kernel_rank_zero P)
  refine LinearMap.ker_eq_bot.mp ?_
  ext x
  rw [Submodule.mem_bot]
  refine ⟨fun hx => ?_, fun hx => hx ▸ Submodule.zero_mem _⟩
  let y : (LinearMap.ker (P.Polarization.domRestrict (span R (range ⇑P.root)))) := ⟨x, hx⟩
  have : (y : M) = 0 := by
    haveI : IsReflexive R M := PerfectPairing.reflexive_left P.toPerfectPairing
    obtain ⟨a, ⟨h1, h2⟩⟩ := htor y
    obtain ⟨z, hz⟩ := x
    exact torsion_free_of_reflexive (by simp_all [y]) h1
  exact Submodule.coe_eq_zero.mp this



--lemma coxeter_weight_leq_4 (i j : ι) : coxeterWeight i j ≤ 4 := by sorry

-- Then, P.toPerfectPairing is nondegenerate on the span of roots, since (c,r) = 0 for all c implies
-- p(r) = 0.
-- Finally, PolInner is also nondegenerate on the span of roots, since
-- it is a composition with a spanning injection.

-- I need base change to be an injection on weight spaces, and this uses reflexivity and flatness.


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
