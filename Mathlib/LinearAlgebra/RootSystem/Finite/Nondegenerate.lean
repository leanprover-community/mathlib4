/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear
import Mathlib.LinearAlgebra.RootSystem.RootPositive


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

lemma rootForm_rootPositive : IsRootPositive P P.RootForm where
  zero_lt_apply_root i := P.rootForm_root_self_pos i
  symm := P.rootForm_symmetric
  apply_reflection_eq := P.rootForm_reflection_reflection_apply

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

lemma rank_polarization_domRestrict_eq_rank_span_coroot :
    LinearMap.rank (P.Polarization.domRestrict (span R (range P.root))) =
      Module.rank R (span R (range P.coroot)) := by
  refine eq_of_le_of_le (Submodule.rank_mono P.range_polarization_domRestrict_le_span_coroot) ?_
  letI : IsReflexive R N := PerfectPairing.reflexive_right P.toPerfectPairing
  refine rank_le_of_smul_regular (span R (range P.coroot))
    (LinearMap.range (P.Polarization.domRestrict (span R (range P.root))))
    (smul_right_injective N (Ne.symm (ne_of_lt P.prod_rootForm_root_self_pos)))
    (mem_center_iff.mp (by simp)) fun _ hx => ?_
  obtain ⟨c, hc⟩ := (mem_span_range_iff_exists_fun R).mp hx
  rw [← hc, Finset.smul_sum]
  simp_rw [smul_smul, mul_comm, ← smul_smul]
  exact Submodule.sum_smul_mem
    (LinearMap.range (P.Polarization.domRestrict (span R (range P.root)))) c
    (fun c _ ↦ prod_rootForm_smul_coroot_in_range_domRestrict P c)

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

lemma finrank_span_root_le :
    Module.finrank R (span R (range P.coroot)) ≤ Module.finrank R (span R (range P.root)) := by
  have h := lift_rank_map_le P.Polarization (span R (range P.root))
  refine finrank_le_finrank_of_rank_le_rank (le_of_eq_of_le ?_ h) (span_root_finite_rank P)
  rw [← rank_polarization_domRestrict_eq_rank_span_coroot, ← LinearMap.range_domRestrict]

lemma finrank_span_root_eq :
    Module.finrank R (span R (range P.coroot)) = Module.finrank R (span R (range P.root)) :=
  Nat.le_antisymm (finrank_span_root_le P) (by simpa using finrank_span_root_le P.flip)

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
  let n := finrank R (span R (range P.root))
  have hm : Module.rank R (span R (range P.root)) = n := by rw [finrank_eq_rank_span_root]
  have hn : Module.rank R (LinearMap.range
      (LinearMap.domRestrict P.Polarization (span R (range P.root)))) = n := by
    rw [show (Module.rank R (LinearMap.range (P.Polarization.domRestrict
      (span R (range P.root))))) = LinearMap.rank (P.Polarization.domRestrict (span R
      (range P.root))) by rfl, rank_polarization_domRestrict_eq_rank_span_coroot,
      ← finrank_eq_rank_span_coroot, finrank_span_root_eq]
  simp [LinearMap.rank_ker_of_nat (LinearMap.domRestrict P.Polarization
    (span R (range P.root))) hm hn]

-- I would like to use `Module.bot_of_rank_zero` here, but `y` lies in a submodule of a submodule.
lemma polarization_domRestrict_injective :
    Injective (LinearMap.domRestrict P.Polarization (span R (range P.root))) := by
  refine LinearMap.ker_eq_bot.mp ?_
  ext x
  rw [Submodule.mem_bot]
  refine ⟨fun hx => ?_, fun hx => hx ▸ Submodule.zero_mem _⟩
  let y : (LinearMap.ker (P.Polarization.domRestrict (span R (range ⇑P.root)))) := ⟨x, hx⟩
  have : y = 0 := by
    haveI : IsReflexive R M := PerfectPairing.reflexive_left P.toPerfectPairing
    obtain ⟨a, ⟨h1, h2⟩⟩ := rank_eq_zero_iff.mp (polarization_domRestrict_kernel_rank_zero P) y
    exact (smul_eq_zero_iff_right h1).mp h2
  exact (AddSubmonoid.mk_eq_zero _).mp this

lemma mem_span_root_zero_of_coroot {x : span R (range P.root)} (hx : ∀ i, P.coroot' i x = 0) :
    x = 0 := by
  apply polarization_domRestrict_injective
  rw [LinearMap.map_zero, LinearMap.domRestrict_apply, Polarization_apply]
  exact Fintype.sum_eq_zero (fun i ↦ (P.coroot' i) x.1 • P.coroot i) fun i => (by simp [hx i])

lemma mem_span_root_eq_zero_of_rootForm {x : M} (hx : x ∈ span R (range P.root))
    (h : P.RootForm x x = 0) : x = 0 := by
  rw [rootForm_self_zero_iff] at h
  let y : span R (range P.root) := ⟨x, hx⟩
  have : y = 0 := mem_span_root_zero_of_coroot P h
  exact (AddSubmonoid.mk_eq_zero (span R (range P.root)).toAddSubmonoid).mp this

-- combine above with `rootForm_self_non_neg` to get positive-definiteness; use #18559

-- rewrite with #18559
lemma rootForm_nondegenerate_on_span {x : span R (range P.root)}
    (hx : ∀ y : span R (range P.root), RootForm P x y = 0) : x = 0 :=
  SetLike.coe_eq_coe.mp (mem_span_root_eq_zero_of_rootForm P (Submodule.coe_mem x) (hx x))

end RootPairing
