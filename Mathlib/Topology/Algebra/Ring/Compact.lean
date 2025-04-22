/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Ring.Ideal

/-!

# Compact Hausdorff Rings

## Main results
- `IsArtinianRing.finite_of_compactSpace_of_t2Space`:
  Compact hausdorff artinian rings are finite (and thus discrete).
- `Ideal.isOpen_of_isMaximal`:
  Maximal ideals are open in compact hausdorff noetherian rings.
- `IsLocalRing.isOpen_iff_finite_quotient`:
  An ideal in a compact hausdorff noetherian local ring is open iff it has finite index.
- `IsDedekindDomain.isOpen_iff`:
  An ideal in a compact hausdorff dedekind domain (that is not a field) is open iff it is non-zero.

## Future projects
Show that compact hausdoff rings are totally disconnected and linearly topologized.
See https://ncatlab.org/nlab/show/compact+Hausdorff+rings+are+profinite

-/

attribute [local instance] Ideal.Quotient.field Fintype.ofFinite finite_of_compact_of_discrete

variable {R : Type*} [CommRing R] [TopologicalSpace R]
variable [IsTopologicalRing R] [CompactSpace R] [T2Space R]

namespace IsArtinianRing

/-- Compact hausdorff artinian (commutative) rings are finite. -/
instance (priority := low) finite_of_compactSpace_of_t2Space [IsArtinianRing R] :
    Finite R := by
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  have H : (∏ p : PrimeSpectrum R, p.asIdeal) ^ n = ⊥ := by
    rw [← le_bot_iff, ← Ideal.zero_eq_bot, ← hn]
    gcongr
    rw [Ideal.jacobson_bot, Ring.jacobson_eq_sInf_isMaximal, le_sInf_iff]
    exact fun I hI ↦ Ideal.prod_le_inf.trans
      (Finset.inf_le (b := PrimeSpectrum.mk I hI.isPrime) (by simp))
  have := Ideal.finite_quotient_prod (R := R) PrimeSpectrum.asIdeal Finset.univ
    (fun _ _ ↦ IsNoetherian.noetherian _) (fun _ _ ↦ inferInstance)
  have := Ideal.finite_quotient_pow (IsNoetherian.noetherian (∏ p : PrimeSpectrum R, p.asIdeal)) n
  rw [H] at this
  exact .of_equiv _ (RingEquiv.quotientBot R).toEquiv

end IsArtinianRing

section IsNoetherianRing

variable [IsNoetherianRing R]

lemma Ideal.isOpen_of_isMaximal (I : Ideal R) [I.IsMaximal] : IsOpen (X := R) I :=
  have : I.toAddSubgroup.FiniteIndex :=
    @AddSubgroup.finiteIndex_of_finite_quotient _ _ _
      (inferInstanceAs (Finite (R ⧸ I)))
  I.toAddSubgroup.isOpen_of_isClosed_of_finiteIndex (inferInstanceAs (IsClosed (X := R) I))

lemma Ideal.isOpen_pow_of_isMaximal (I : Ideal R) [I.IsMaximal] (n : ℕ) :
    IsOpen (X := R) ↑(I ^ n) :=
  have : (I ^ n).toAddSubgroup.FiniteIndex :=
    @AddSubgroup.finiteIndex_of_finite_quotient _ _ _
      (Ideal.finite_quotient_pow (IsNoetherian.noetherian _) _)
  (I ^ n).toAddSubgroup.isOpen_of_isClosed_of_finiteIndex
    (Ideal.isCompact_of_fg (IsNoetherian.noetherian _)).isClosed

-- Note: this is only by infer_instance because of the opened local instances.
instance (priority := low) (I : Ideal R) [I.IsMaximal] : Finite (R ⧸ I) := inferInstance

end IsNoetherianRing

namespace IsLocalRing

variable [IsLocalRing R] [IsNoetherianRing R]

variable (R) in
lemma isOpen_maximalIdeal_pow (n : ℕ) :
    IsOpen (X := R) ↑(maximalIdeal R ^ n) :=
  Ideal.isOpen_pow_of_isMaximal _ _

variable (R) in
lemma isOpen_maximalIdeal : IsOpen (X := R) ↑(maximalIdeal R) :=
  Ideal.isOpen_of_isMaximal _

instance finite_residueField_of_compactSpace : Finite (ResidueField R) :=
  inferInstanceAs (Finite (R ⧸ _))

lemma isOpen_iff_finite_quotient {I : Ideal R} :
    IsOpen (X := R) I ↔ Finite (R ⧸ I) := by
  refine ⟨AddSubgroup.quotient_finite_of_isOpen I.toAddSubgroup, fun H ↦ ?_⟩
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_of_finite_quotient I
  exact AddSubgroup.isOpen_mono (H₁ := (maximalIdeal R ^ n).toAddSubgroup)
    (H₂ := I.toAddSubgroup) hn (isOpen_maximalIdeal_pow R n)

end IsLocalRing

section IsDedekindDomain

lemma IsDedekindDomain.isOpen_of_ne_bot
    [IsDedekindDomain R] {I : Ideal R} (hI : I ≠ ⊥) :
    IsOpen (X := R) I := by
  rw [← Ideal.finprod_heightOneSpectrum_factorization hI,
    finprod_eq_finset_prod_of_mulSupport_subset _
      (s := (Ideal.finite_mulSupport hI).toFinset) (by simp)]
  refine @AddSubgroup.isOpen_of_isClosed_of_finiteIndex _ _ _ _ (Submodule.toAddSubgroup _)
    ?_ (IsNoetherianRing.isClosed_ideal _)
  refine @AddSubgroup.finiteIndex_of_finite_quotient _ _ _ ?_
  refine Ideal.finite_quotient_prod _ _ (fun _ _ ↦ IsNoetherian.noetherian _) fun _ _ ↦ ?_
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) _

lemma IsDedekindDomain.isOpen_iff
    [IsDedekindDomain R] (hR : ¬ IsField R) {I : Ideal R} :
    IsOpen (X := R) I ↔ I ≠ ⊥ := by
  refine ⟨?_, IsDedekindDomain.isOpen_of_ne_bot⟩
  rintro H rfl
  have := discreteTopology_iff_isOpen_singleton_zero.mpr H
  exact hR (Finite.isField_of_domain R)

lemma IsDiscreteValuationRing.isOpen_iff
    [IsDomain R] [IsDiscreteValuationRing R] {I : Ideal R} :
    IsOpen (X := R) I ↔ I ≠ ⊥ :=
  IsDedekindDomain.isOpen_iff (not_isField R)

end IsDedekindDomain
