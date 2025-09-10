/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.RootSystem.BaseChange
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
  coroots which have length zero w.r.t. the root / coroot forms.
* `RootPairing.rootForm_pos_of_nonzero`: `RootForm` is strictly positive on non-zero linear
  combinations of roots. This gives us a convenient way to eliminate certain Dynkin diagrams from
  the classification, since it suffices to produce a nonzero linear combination of simple roots with
  non-positive norm.
* `RootPairing.rootForm_restrict_nondegenerate_of_ordered`: The root form is non-degenerate if
  the coefficients are ordered.
* `RootPairing.rootForm_restrict_nondegenerate_of_isAnisotropic`: the root form is
  non-degenerate if the coefficients are a field and the pairing is crystallographic.

## References:
* [N. Bourbaki, *Lie groups and Lie algebras. Chapters 4--6*][bourbaki1968]
* [M. Demazure, *SGA III, Exposé XXI, Données Radicielles*][demazure1970]

## Todo
* Weyl-invariance of `RootForm` and `CorootForm`
* Faithfulness of Weyl group perm action, and finiteness of Weyl group, over ordered rings.
* Relation to Coxeter weight.
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
zero w.r.t. the root / coroot forms.

Examples include crystallographic pairings in characteristic zero
`RootPairing.instIsAnisotropicOfIsCrystallographic` and pairings over ordered scalars.
`RootPairing.instIsAnisotropicOfLinearOrderedCommRing`. -/
class IsAnisotropic : Prop where
  rootForm_root_ne_zero (i : ι) : P.RootForm (P.root i) (P.root i) ≠ 0
  corootForm_coroot_ne_zero (i : ι) : P.CorootForm (P.coroot i) (P.coroot i) ≠ 0

instance [P.IsAnisotropic] : P.flip.IsAnisotropic where
  rootForm_root_ne_zero := IsAnisotropic.corootForm_coroot_ne_zero
  corootForm_coroot_ne_zero := IsAnisotropic.rootForm_root_ne_zero (P := P)

lemma isAnisotropic_of_isValuedIn (S : Type*)
    [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
    [Algebra S R] [FaithfulSMul S R] [P.IsValuedIn S] :
    IsAnisotropic P where
  rootForm_root_ne_zero i := (P.posRootForm S).form_apply_root_ne_zero i
  corootForm_coroot_ne_zero i := (P.flip.posRootForm S).form_apply_root_ne_zero i

instance instIsAnisotropicOfIsCrystallographic [CharZero R] [P.IsCrystallographic] :
    IsAnisotropic P :=
  P.isAnisotropic_of_isValuedIn ℤ

/-- The root form of an anisotropic pairing as an invariant form. -/
@[simps] def toInvariantForm [P.IsAnisotropic] : P.InvariantForm where
  form := P.RootForm
  symm := P.rootForm_symmetric
  ne_zero := IsAnisotropic.rootForm_root_ne_zero
  isOrthogonal_reflection := P.rootForm_reflection_reflection_apply

section DomainAlg

variable (S : Type*) [CommRing S] [IsDomain R] [IsDomain S] [Algebra S R] [FaithfulSMul S R]
  [P.IsValuedIn S] [Module S M] [IsScalarTower S R M] [Module S N] [IsScalarTower S R N]

lemma finrank_range_polarization_eq_finrank_span_coroot [P.IsAnisotropic] :
    finrank S (LinearMap.range (P.PolarizationIn S)) = finrank S (P.corootSpan S) := by
  apply (Submodule.finrank_mono (P.range_polarizationIn_le_span_coroot S)).antisymm
  have : IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  have : NoZeroSMulDivisors S N := NoZeroSMulDivisors.trans_faithfulSMul S R N
  have h_ne : ∏ i, (P.RootFormIn S (P.rootSpanMem S i) (P.rootSpanMem S i)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i _ h ↦ ?_
    have := (FaithfulSMul.algebraMap_eq_zero_iff S R).mpr h
    rw [algebraMap_rootFormIn] at this
    apply IsAnisotropic.rootForm_root_ne_zero i this
  refine LinearMap.finrank_le_of_isSMulRegular (P.corootSpan S)
    (LinearMap.range (M₂ := N) (P.PolarizationIn S))
    (smul_right_injective N h_ne) ?_
  intro _ hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).mp hx
  rw [← hc, Finset.smul_sum]
  simp_rw [smul_smul, mul_comm, ← smul_smul]
  exact Submodule.sum_smul_mem (LinearMap.range (P.PolarizationIn S)) c
    fun j _ ↦ prod_rootFormIn_smul_coroot_mem_range_PolarizationIn P S j

/-- An auxiliary lemma en route to `RootPairing.finrank_corootSpan_eq`. -/
private lemma finrank_corootSpan_le [P.IsAnisotropic] :
    finrank S (P.corootSpan S) ≤ finrank S (P.rootSpan S) := by
  rw [← finrank_range_polarization_eq_finrank_span_coroot]
  exact LinearMap.finrank_range_le (P.PolarizationIn S)

lemma finrank_corootSpan_eq [P.IsAnisotropic] :
    finrank S (P.corootSpan S) = finrank S (P.rootSpan S) :=
  le_antisymm (P.finrank_corootSpan_le S) (P.flip.finrank_corootSpan_le S)

lemma polarizationIn_Injective [P.IsAnisotropic] :
    Function.Injective (P.PolarizationIn S) := by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : NoZeroSMulDivisors S M := NoZeroSMulDivisors.trans_faithfulSMul S R M
  rw [← LinearMap.ker_eq_bot, ← top_disjoint]
  refine Submodule.disjoint_ker_of_finrank_le (L := ⊤) (P.PolarizationIn S) ?_
  rw [finrank_top, ← finrank_corootSpan_eq, ← finrank_range_polarization_eq_finrank_span_coroot]
  exact Submodule.finrank_mono <| le_of_eq <| LinearMap.range_eq_map (P.PolarizationIn S)

lemma exists_coroot_ne [P.IsAnisotropic]
    {x : P.rootSpan S} (hx : x ≠ 0) :
    ∃ i, P.coroot'In S i x ≠ 0 := by
  have hI := P.polarizationIn_Injective S
  have h := (map_ne_zero_iff (P.PolarizationIn S) hI).mpr hx
  rw [PolarizationIn_apply] at h
  contrapose! h
  exact Fintype.sum_eq_zero (fun a ↦ (P.coroot'In S a) x • P.coroot a) fun i ↦ by simp [h i]

end DomainAlg

section LinearOrderedCommRingAlg

variable (S : Type*) [CommRing S] [LinearOrder S] [IsStrictOrderedRing S] [IsDomain R] [Algebra S R]
  [FaithfulSMul S R] [P.IsValuedIn S] [Module S M] [IsScalarTower S R M] [Module S N]
  [IsScalarTower S R N]

theorem posRootForm_posForm_pos_of_ne_zero {x : P.rootSpan S} (hx : x ≠ 0) :
    0 < (P.posRootForm S).posForm x x := by
  rw [posRootForm_posForm_apply_apply]
  have := P.isAnisotropic_of_isValuedIn S
  have : ∃ i ∈ Finset.univ, 0 < (P.coroot'In S i) x * (P.coroot'In S i) x := by
    obtain ⟨i, hi⟩ := P.exists_coroot_ne S hx
    use i
    exact ⟨Finset.mem_univ i, mul_self_pos.mpr hi⟩
  exact Finset.sum_pos' (fun i a ↦ mul_self_nonneg ((P.coroot'In S i) x)) this

lemma posRootForm_posForm_anisotropic :
    (P.posRootForm S).posForm.toQuadraticMap.Anisotropic :=
  fun _ hx ↦ Classical.byContradiction fun h ↦
    (ne_of_lt (posRootForm_posForm_pos_of_ne_zero P S h)).symm hx

lemma posRootForm_posForm_nondegenerate :
    (P.posRootForm S).posForm.Nondegenerate := by
  refine LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.mpr <| LinearMap.ker_eq_bot'.mpr ?_
  intro x hx
  contrapose! hx
  rw [DFunLike.ne_iff]
  use x
  exact (posRootForm_posForm_pos_of_ne_zero P S hx).ne'

end LinearOrderedCommRingAlg

end CommRing

section IsDomain

variable [CommRing R] [IsDomain R] [Module R M] [Module R N] (P : RootPairing ι R M N)
  [P.IsAnisotropic]

@[simp]
lemma finrank_rootSpan_map_polarization_eq_finrank_corootSpan :
    finrank R ((P.rootSpan R).map P.Polarization) = finrank R (P.corootSpan R) := by
  rw [← P.finrank_range_polarization_eq_finrank_span_coroot R, range_polarizationIn]

/-- An auxiliary lemma en route to `RootPairing.finrank_corootSpan_eq'`. -/
private lemma finrank_corootSpan_le' :
    finrank R (P.corootSpan R) ≤ finrank R (P.rootSpan R) := by
  rw [← finrank_rootSpan_map_polarization_eq_finrank_corootSpan]
  exact Submodule.finrank_map_le P.Polarization (P.rootSpan R)

/-- Equality of `finrank`s when the base is a domain. -/
lemma finrank_corootSpan_eq' :
    finrank R (P.corootSpan R) = finrank R (P.rootSpan R) :=
  le_antisymm P.finrank_corootSpan_le' P.flip.finrank_corootSpan_le'

lemma disjoint_rootSpan_ker_rootForm :
    Disjoint (P.rootSpan R) (LinearMap.ker P.RootForm) := by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  rw [← P.ker_polarization_eq_ker_rootForm]
  refine Submodule.disjoint_ker_of_finrank_le (L := P.rootSpan R) P.Polarization ?_
  rw [P.finrank_rootSpan_map_polarization_eq_finrank_corootSpan, P.finrank_corootSpan_eq']

lemma disjoint_corootSpan_ker_corootForm :
    Disjoint (P.corootSpan R) (LinearMap.ker P.CorootForm) :=
  P.flip.disjoint_rootSpan_ker_rootForm

lemma _root_.RootSystem.rootForm_nondegenerate (P : RootSystem ι R M N) [P.IsAnisotropic] :
    P.RootForm.Nondegenerate :=
  LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.mpr <| by
    simpa using P.disjoint_rootSpan_ker_rootForm

end IsDomain

section Field

variable [Field R] [Module R M] [Module R N] (P : RootPairing ι R M N) [P.IsAnisotropic]

lemma isCompl_rootSpan_ker_rootForm :
    IsCompl (P.rootSpan R) (LinearMap.ker P.RootForm) := by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  refine (Submodule.isCompl_iff_disjoint _ _ ?_).mpr P.disjoint_rootSpan_ker_rootForm
  have aux : finrank R M =
      finrank R (P.rootSpan R) + finrank R (P.corootSpan R).dualAnnihilator := by
    rw [P.toPerfPair.finrank_eq, ← P.finrank_corootSpan_eq',
      Subspace.finrank_add_finrank_dualAnnihilator_eq (P.corootSpan R), Subspace.dual_finrank_eq]
  rw [aux, add_le_add_iff_left]
  convert Submodule.finrank_mono P.corootSpan_dualAnnihilator_le_ker_rootForm
  exact (LinearEquiv.finrank_map_eq _ _).symm

lemma isCompl_corootSpan_ker_corootForm :
    IsCompl (P.corootSpan R) (LinearMap.ker P.CorootForm) :=
  P.flip.isCompl_rootSpan_ker_rootForm

lemma ker_rootForm_eq_dualAnnihilator :
    LinearMap.ker P.RootForm = (P.corootSpan R).dualAnnihilator.map P.toPerfPair.symm := by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  suffices finrank R (LinearMap.ker P.RootForm) = finrank R (P.corootSpan R).dualAnnihilator by
    refine (Submodule.eq_of_le_of_finrank_eq P.corootSpan_dualAnnihilator_le_ker_rootForm ?_).symm
    rw [this]
    apply LinearEquiv.finrank_map_eq
  have aux0 := Subspace.finrank_add_finrank_dualAnnihilator_eq (P.corootSpan R)
  have aux1 := Submodule.finrank_add_eq_of_isCompl P.isCompl_rootSpan_ker_rootForm
  rw [← P.finrank_corootSpan_eq', P.toPerfPair.finrank_eq, Subspace.dual_finrank_eq] at aux1
  omega

lemma ker_corootForm_eq_dualAnnihilator :
    LinearMap.ker P.CorootForm = (P.rootSpan R).dualAnnihilator.map P.flip.toPerfPair.symm :=
  P.flip.ker_rootForm_eq_dualAnnihilator

instance : P.IsBalanced where
    isPerfectCompl :=
  { isCompl_left := by
      simpa only [ker_rootForm_eq_dualAnnihilator] using P.isCompl_rootSpan_ker_rootForm
    isCompl_right := by
      simpa only [ker_corootForm_eq_dualAnnihilator] using P.isCompl_corootSpan_ker_corootForm }

/-- See also `RootPairing.rootForm_restrict_nondegenerate_of_ordered`.

Note that this applies to crystallographic root systems in characteristic zero via
`RootPairing.instIsAnisotropicOfIsCrystallographic`. -/
lemma rootForm_restrict_nondegenerate_of_isAnisotropic :
    LinearMap.Nondegenerate (P.RootForm.restrict (P.rootSpan R)) :=
  P.rootForm_symmetric.nondegenerate_restrict_of_isCompl_ker P.isCompl_rootSpan_ker_rootForm

@[simp]
lemma orthogonal_rootSpan_eq :
    P.RootForm.orthogonal (P.rootSpan R) = LinearMap.ker P.RootForm := by
  rw [← LinearMap.BilinForm.orthogonal_top_eq_ker P.rootForm_symmetric.isRefl]
  refine le_antisymm ?_ (by intro; simp_all)
  rintro x hx y -
  simp only [LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.BilinForm.IsOrtho] at hx ⊢
  obtain ⟨u, hu, v, hv, rfl⟩ : ∃ᵉ (u ∈ P.rootSpan R) (v ∈ LinearMap.ker P.RootForm), u + v = y := by
    rw [← Submodule.mem_sup, P.isCompl_rootSpan_ker_rootForm.sup_eq_top]; exact Submodule.mem_top
  simp only [LinearMap.mem_ker] at hv
  simp [hx _ hu, hv]

@[simp]
lemma orthogonal_corootSpan_eq :
    P.CorootForm.orthogonal (P.corootSpan R) = LinearMap.ker P.CorootForm :=
  P.flip.orthogonal_rootSpan_eq

lemma rootSpan_eq_top_iff :
    P.rootSpan R = ⊤ ↔ P.corootSpan R = ⊤ := by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;> apply Submodule.eq_top_of_finrank_eq
  · rw [P.finrank_corootSpan_eq', h, finrank_top, P.toPerfPair.finrank_eq, Subspace.dual_finrank_eq]
  · rw [← P.finrank_corootSpan_eq', h, finrank_top, P.toPerfPair.finrank_eq,
      Subspace.dual_finrank_eq]

end Field

section LinearOrderedCommRing

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [Module R M] [Module R N] (P : RootPairing ι R M N)

instance instIsAnisotropicOfLinearOrderedCommRing : IsAnisotropic P :=
  P.isAnisotropic_of_isValuedIn R

lemma zero_le_rootForm (x : M) :
    0 ≤ P.RootForm x x :=
  (P.rootForm_self_sum_of_squares x).nonneg

/-- See also `RootPairing.rootForm_restrict_nondegenerate_of_isAnisotropic`. -/
lemma rootForm_restrict_nondegenerate_of_ordered :
    LinearMap.Nondegenerate (P.RootForm.restrict (P.rootSpan R)) :=
  (P.RootForm.nondegenerate_restrict_iff_disjoint_ker P.zero_le_rootForm
    P.rootForm_symmetric).mpr P.disjoint_rootSpan_ker_rootForm

lemma rootForm_self_eq_zero_iff {x : M} :
    P.RootForm x x = 0 ↔ x ∈ LinearMap.ker P.RootForm :=
  P.RootForm.apply_apply_same_eq_zero_iff P.zero_le_rootForm P.rootForm_symmetric

lemma eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero {x : M}
    (hx : x ∈ P.rootSpan R) (hx' : P.RootForm x x = 0) :
    x = 0 := by
  have : x ∈ P.rootSpan R ⊓ LinearMap.ker P.RootForm := ⟨hx, P.rootForm_self_eq_zero_iff.mp hx'⟩
  simpa [P.disjoint_rootSpan_ker_rootForm.eq_bot] using this

lemma rootForm_pos_of_ne_zero {x : M} (hx : x ∈ P.rootSpan R) (h : x ≠ 0) :
    0 < P.RootForm x x := by
  apply (P.zero_le_rootForm x).lt_of_ne
  contrapose! h
  exact P.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero hx h.symm

lemma _root_.RootSystem.rootForm_anisotropic (P : RootSystem ι R M N) :
    P.RootForm.toQuadraticMap.Anisotropic :=
  fun x ↦ P.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero <| by
    simpa only [rootSpan, P.span_root_eq_top] using Submodule.mem_top

end LinearOrderedCommRing

end RootPairing
