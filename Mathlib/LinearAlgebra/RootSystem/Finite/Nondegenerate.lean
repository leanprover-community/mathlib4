/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear
import Mathlib.LinearAlgebra.RootSystem.RootPositive

/-!
# Nondegeneracy of the polarization on a finite root pairing

We show that if the base ring of a finite root pairing is linearly ordered, then the canonical
bilinear form is root-positive and positive-definite on the span of roots.
From these facts, it is easy to show that Coxeter weights in a finite root pairing are bounded
above by 4.  Thus, the pairings of roots and coroots in a root pairing are restricted to the
interval `[-4, 4]`.  Furthermore, a linearly independent pair of roots cannot have Coxeter weight 4.
For the case of crystallographic root pairings, we are thus reduced to a finite set of possible
options for each pair.
Another application is to the faithfulness of the Weyl group action on roots, and finiteness of the
Weyl group.

## Main results:
 * `RootPairing.rootForm_rootPositive`: `RootForm` is root-positive.
 * `RootPairing.polarization_domRestrict_injective`: The polarization restricted to the span of
   roots is injective.
 * `RootPairing.rootForm_pos_of_nonzero`: `RootForm` is strictly positive on non-zero linear
  combinations of roots. This gives us a convenient way to eliminate certain Dynkin diagrams from
  the classification, since it suffices to produce a nonzero linear combination of simple roots with
  non-positive norm.

## References:
 * [N. Bourbaki, *Lie groups and {L}ie algebras. {C}hapters 4--6*][bourbaki1968]
 * [M. Demazure, *SGA III, Expos\'{e} XXI, Don\'{e}es Radicielles*][demazure1970]

## Todo
 * Weyl-invariance of `RootForm` and `CorootForm`
 * Faithfulness of Weyl group perm action, and finiteness of Weyl group, over ordered rings.
 * Relation to Coxeter weight.  In particular, positivity constraints for finite root pairings mean
  we restrict to weights between 0 and 4.
-/

noncomputable section

open Set Function
open Module hiding reflection
open Submodule (span)

namespace RootPairing

variable {ι R M N : Type*}

variable [Fintype ι] [LinearOrderedCommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
[Module R N] (P : RootPairing ι R M N)

lemma rootForm_rootPositive : IsRootPositive P P.RootForm where
  zero_lt_apply_root i := P.rootForm_root_self_pos i
  symm := P.rootForm_symmetric
  apply_reflection_eq := P.rootForm_reflection_reflection_apply

instance : Module.Finite R P.rootSpan := Finite.span_of_finite R <| finite_range P.root

instance : Module.Finite R P.corootSpan := Finite.span_of_finite R <| finite_range P.coroot

@[simp]
lemma finrank_rootSpan_map_polarization_eq_finrank_corootSpan :
    finrank R (P.rootSpan.map P.Polarization) = finrank R P.corootSpan := by
  rw [← LinearMap.range_domRestrict]
  apply (Submodule.finrank_mono P.range_polarization_domRestrict_le_span_coroot).antisymm
  have : IsReflexive R N := PerfectPairing.reflexive_right P.toPerfectPairing
  refine LinearMap.finrank_le_of_isSMulRegular P.corootSpan
    (LinearMap.range (P.Polarization.domRestrict P.rootSpan))
    (smul_right_injective N (Ne.symm (ne_of_lt P.prod_rootForm_root_self_pos)))
    fun _ hx => ?_
  obtain ⟨c, hc⟩ := (mem_span_range_iff_exists_fun R).mp hx
  rw [← hc, Finset.smul_sum]
  simp_rw [smul_smul, mul_comm, ← smul_smul]
  exact Submodule.sum_smul_mem (LinearMap.range (P.Polarization.domRestrict P.rootSpan)) c
    (fun c _ ↦ prod_rootForm_smul_coroot_mem_range_domRestrict P c)

/-- An auxiliary lemma en route to `RootPairing.finrank_corootSpan_eq`. -/
private lemma finrank_corootSpan_le :
    finrank R P.corootSpan ≤ finrank R P.rootSpan := by
  rw [← finrank_rootSpan_map_polarization_eq_finrank_corootSpan]
  exact Submodule.finrank_map_le P.Polarization P.rootSpan

lemma finrank_corootSpan_eq :
    finrank R P.corootSpan = finrank R P.rootSpan :=
  le_antisymm P.finrank_corootSpan_le P.flip.finrank_corootSpan_le

lemma disjoint_rootSpan_ker_polarization :
    Disjoint P.rootSpan (LinearMap.ker P.Polarization) := by
  have : IsReflexive R M := PerfectPairing.reflexive_left P.toPerfectPairing
  refine Submodule.disjoint_ker_of_finrank_eq (L := P.rootSpan) P.Polarization ?_
  rw [finrank_rootSpan_map_polarization_eq_finrank_corootSpan, finrank_corootSpan_eq]

lemma mem_ker_polarization_of_rootForm_self_eq_zero {x : M} (hx : P.RootForm x x = 0) :
    x ∈ LinearMap.ker P.Polarization := by
  rw [LinearMap.mem_ker, Polarization_apply]
  rw [rootForm_self_zero_iff] at hx
  exact Fintype.sum_eq_zero _ fun i ↦ by simp [hx i]

lemma eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero {x : M}
    (hx : x ∈ P.rootSpan) (hx' : P.RootForm x x = 0) :
    x = 0 := by
  rw [← Submodule.mem_bot (R := R), ← P.disjoint_rootSpan_ker_polarization.eq_bot]
  exact ⟨hx, P.mem_ker_polarization_of_rootForm_self_eq_zero hx'⟩

lemma _root_.RootSystem.rootForm_anisotropic (P : RootSystem ι R M N) :
    P.RootForm.toQuadraticMap.Anisotropic :=
  fun x ↦ P.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero <| by
    simpa only [rootSpan, P.span_eq_top] using Submodule.mem_top

lemma rootForm_pos_of_nonzero {x : M} (hx : x ∈ P.rootSpan) (h : x ≠ 0) :
    0 < P.RootForm x x := by
  apply (P.rootForm_self_non_neg x).lt_of_ne
  contrapose! h
  exact eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero P hx h.symm

lemma rootForm_restrict_nondegenerate :
    (P.RootForm.restrict P.rootSpan).Nondegenerate :=
  LinearMap.IsRefl.nondegenerate_of_separatingLeft (LinearMap.IsSymm.isRefl fun x y => by
    simp [rootForm_apply_apply, mul_comm]) fun x h => SetLike.coe_eq_coe.mp
    (P.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero (Submodule.coe_mem x) (h x))

end RootPairing
