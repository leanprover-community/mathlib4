/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear

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
 * `RootPairing.IsAnisotropic`: We say a finite root pairing is anisotropic if there are no roots /
   coroots which have length zero wrt the root / coroot forms.
 * `RootPairing.rootForm_pos_of_nonzero`: `RootForm` is strictly positive on non-zero linear
  combinations of roots. This gives us a convenient way to eliminate certain Dynkin diagrams from
  the classification, since it suffices to produce a nonzero linear combination of simple roots with
  non-positive norm.
 * `RootPairing.rootForm_restrict_nondegenerate_of_ordered`: The root form is non-degenerate if
   the coefficients are ordered.
 * `RootPairing.rootForm_restrict_nondegenerate_of_isAnisotropic`: the root form is
   non-degenerate if the coefficients are a field and the pairing is crystallographic.

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

variable {ι R M N : Type*} [Fintype ι] [AddCommGroup M] [AddCommGroup N]

section CommRing

variable [CommRing R] [Module R M] [Module R N] (P : RootPairing ι R M N)

/-- We say a finite root pairing is anisotropic if there are no roots / coroots which have length
zero wrt the root / coroot forms.

Examples include crystallographic pairings in characteristic zero
`RootPairing.instIsAnisotropicOfIsCrystallographic` and pairings over ordered scalars.
`RootPairing.instIsAnisotropicOfLinearOrderedCommRing`. -/
class IsAnisotropic : Prop where
  rootForm_root_ne_zero (i : ι) : P.RootForm (P.root i) (P.root i) ≠ 0
  corootForm_coroot_ne_zero (i : ι) : P.CorootForm (P.coroot i) (P.coroot i) ≠ 0

instance [P.IsAnisotropic] : P.flip.IsAnisotropic where
  rootForm_root_ne_zero := IsAnisotropic.corootForm_coroot_ne_zero
  corootForm_coroot_ne_zero := IsAnisotropic.rootForm_root_ne_zero

/-- An auxiliary lemma en route to `RootPairing.instIsAnisotropicOfIsCrystallographic`. -/
private lemma rootForm_root_ne_zero_aux [CharZero R] [P.IsCrystallographic] (i : ι) :
    P.RootForm (P.root i) (P.root i) ≠ 0 := by
  choose z hz using P.exists_int i
  simp only [rootForm_apply_apply, PerfectPairing.flip_apply_apply, root_coroot_eq_pairing, ← hz]
  suffices 0 < ∑ i, z i * z i by norm_cast; exact this.ne'
  refine Finset.sum_pos' (fun i _ ↦ mul_self_nonneg (z i)) ⟨i, Finset.mem_univ i, ?_⟩
  have hzi : z i = 2 := by
    specialize hz i
    rw [pairing_same] at hz
    norm_cast at hz
  simp [hzi]

instance instIsAnisotropicOfIsCrystallographic [CharZero R] [P.IsCrystallographic] :
    IsAnisotropic P where
  rootForm_root_ne_zero := P.rootForm_root_ne_zero_aux
  corootForm_coroot_ne_zero := P.flip.rootForm_root_ne_zero_aux

end CommRing

section IsDomain

variable [CommRing R] [IsDomain R] [Module R M] [Module R N] (P : RootPairing ι R M N)
  [P.IsAnisotropic]

@[simp]
lemma finrank_rootSpan_map_polarization_eq_finrank_corootSpan :
    finrank R (P.rootSpan.map P.Polarization) = finrank R P.corootSpan := by
  rw [← LinearMap.range_domRestrict]
  apply (Submodule.finrank_mono P.range_polarization_domRestrict_le_span_coroot).antisymm
  have : IsReflexive R N := PerfectPairing.reflexive_right P.toPerfectPairing
  have h_ne : ∏ i, P.RootForm (P.root i) (P.root i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ ↦ IsAnisotropic.rootForm_root_ne_zero i
  refine LinearMap.finrank_le_of_isSMulRegular P.corootSpan
    (LinearMap.range (P.Polarization.domRestrict P.rootSpan))
    (smul_right_injective N h_ne)
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

lemma disjoint_rootSpan_ker_rootForm :
    Disjoint P.rootSpan (LinearMap.ker P.RootForm) := by
  have : IsReflexive R M := PerfectPairing.reflexive_left P.toPerfectPairing
  rw [← P.ker_polarization_eq_ker_rootForm]
  refine Submodule.disjoint_ker_of_finrank_le (L := P.rootSpan) P.Polarization ?_
  rw [P.finrank_rootSpan_map_polarization_eq_finrank_corootSpan, P.finrank_corootSpan_eq]

lemma disjoint_corootSpan_ker_corootForm :
    Disjoint P.corootSpan (LinearMap.ker P.CorootForm) :=
  P.flip.disjoint_rootSpan_ker_rootForm

end IsDomain

section Field

variable [Field R] [Module R M] [Module R N] (P : RootPairing ι R M N) [P.IsAnisotropic]

lemma isCompl_rootSpan_ker_rootForm :
    IsCompl P.rootSpan (LinearMap.ker P.RootForm) := by
  have _iM : IsReflexive R M := PerfectPairing.reflexive_left P.toPerfectPairing
  have _iN : IsReflexive R N := PerfectPairing.reflexive_right P.toPerfectPairing
  refine (Submodule.isCompl_iff_disjoint _ _ ?_).mpr P.disjoint_rootSpan_ker_rootForm
  have aux : finrank R M = finrank R P.rootSpan + finrank R P.corootSpan.dualAnnihilator := by
    rw [P.toPerfectPairing.finrank_eq, ← P.finrank_corootSpan_eq,
      Subspace.finrank_add_finrank_dualAnnihilator_eq P.corootSpan]
  rw [aux, add_le_add_iff_left]
  convert Submodule.finrank_mono P.corootSpan_dualAnnihilator_le_ker_rootForm
  exact (LinearEquiv.finrank_map_eq _ _).symm

lemma isCompl_corootSpan_ker_corootForm :
    IsCompl P.corootSpan (LinearMap.ker P.CorootForm) :=
  P.flip.isCompl_rootSpan_ker_rootForm

/-- See also `RootPairing.rootForm_restrict_nondegenerate_of_ordered`.

Note that this applies to crystallographic root systems in characteristic zero via
`RootPairing.instIsAnisotropicOfIsCrystallographic`. -/
lemma rootForm_restrict_nondegenerate_of_isAnisotropic :
    LinearMap.Nondegenerate (P.RootForm.restrict P.rootSpan) :=
  P.rootForm_symmetric.nondegenerate_restrict_of_isCompl_ker P.isCompl_rootSpan_ker_rootForm

@[simp]
lemma orthogonal_rootSpan_eq :
    P.RootForm.orthogonal P.rootSpan = LinearMap.ker P.RootForm := by
  rw [← LinearMap.BilinForm.orthogonal_top_eq_ker P.rootForm_symmetric.isRefl]
  refine le_antisymm ?_ (by intro; aesop)
  rintro x hx y -
  simp only [LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.BilinForm.IsOrtho] at hx ⊢
  obtain ⟨u, hu, v, hv, rfl⟩ : ∃ᵉ (u ∈ P.rootSpan) (v ∈ LinearMap.ker P.RootForm), u + v = y := by
    rw [← Submodule.mem_sup, P.isCompl_rootSpan_ker_rootForm.sup_eq_top]; exact Submodule.mem_top
  simp only [LinearMap.mem_ker] at hv
  simp [hx _ hu, hv]

@[simp]
lemma orthogonal_corootSpan_eq :
    P.CorootForm.orthogonal P.corootSpan = LinearMap.ker P.CorootForm :=
  P.flip.orthogonal_rootSpan_eq

end Field

section LinearOrderedCommRing

variable [LinearOrderedCommRing R] [Module R M] [Module R N] (P : RootPairing ι R M N)

instance instIsAnisotropicOfLinearOrderedCommRing : IsAnisotropic P where
  rootForm_root_ne_zero i := (P.rootForm_root_self_pos i).ne'
  corootForm_coroot_ne_zero i := (P.flip.rootForm_root_self_pos i).ne'

/-- See also `RootPairing.rootForm_restrict_nondegenerate_of_isAnisotropic`. -/
lemma rootForm_restrict_nondegenerate_of_ordered :
    LinearMap.Nondegenerate (P.RootForm.restrict P.rootSpan) :=
  (P.RootForm.nondegenerate_restrict_iff_disjoint_ker (rootForm_self_non_neg P)
    P.rootForm_symmetric).mpr P.disjoint_rootSpan_ker_rootForm

lemma eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero {x : M}
    (hx : x ∈ P.rootSpan) (hx' : P.RootForm x x = 0) :
    x = 0 := by
  have : x ∈ P.rootSpan ⊓ LinearMap.ker P.RootForm := ⟨hx, P.rootForm_self_eq_zero_iff.mp hx'⟩
  simpa [P.disjoint_rootSpan_ker_rootForm.eq_bot] using this

lemma rootForm_pos_of_ne_zero {x : M} (hx : x ∈ P.rootSpan) (h : x ≠ 0) :
    0 < P.RootForm x x := by
  apply (P.rootForm_self_non_neg x).lt_of_ne
  contrapose! h
  exact P.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero hx h.symm

lemma _root_.RootSystem.rootForm_anisotropic (P : RootSystem ι R M N) :
    P.RootForm.toQuadraticMap.Anisotropic :=
  fun x ↦ P.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero <| by
    simpa only [rootSpan, P.span_eq_top] using Submodule.mem_top

end LinearOrderedCommRing

end RootPairing
