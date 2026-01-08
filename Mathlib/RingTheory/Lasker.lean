/-
Copyright (c) 2024 Thomas Browning, Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Yakov Pechersky
-/
module

public import Mathlib.Order.Irreducible
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.IsPrimary
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Lasker ring

## Main declarations

- `IsLasker`: A ring `R` satisfies `IsLasker R` when any `I : Ideal R` can be decomposed into
  finitely many primary ideals.
- `IsLasker.minimal`: Any `I : Ideal R` in a ring `R` satisfying `IsLasker R` can be
  decomposed into primary ideals, such that the decomposition is minimal:
  each primary ideal is necessary, and each primary ideal has an independent radical.
- `Ideal.isLasker`: Every Noetherian commutative ring is a Lasker ring.

## Implementation details

There is a generalization for submodules that needs to be implemented.
Also, one needs to prove that the radicals of minimal decompositions are independent of the
  precise decomposition.

-/

@[expose] public section

section IsLasker

variable (R : Type*) [CommSemiring R]

/-- A ring `R` satisfies `IsLasker R` when any `I : Ideal R` can be decomposed into
finitely many primary ideals. -/
def IsLasker : Prop :=
  ∀ I : Ideal R, ∃ s : Finset (Ideal R), s.inf id = I ∧ ∀ ⦃J⦄, J ∈ s → J.IsPrimary

variable {R}

namespace Ideal

lemma decomposition_erase_inf [DecidableEq (Ideal R)] {I : Ideal R}
    {s : Finset (Ideal R)} (hs : s.inf id = I) :
    ∃ t : Finset (Ideal R), t ⊆ s ∧ t.inf id = I ∧ (∀ ⦃J⦄, J ∈ t → ¬ (t.erase J).inf id ≤ J) := by
  induction s using Finset.eraseInduction with
  | H s IH =>
    by_cases! H : ∀ J ∈ s, ¬ (s.erase J).inf id ≤ J
    · exact ⟨s, Finset.Subset.rfl, hs, H⟩
    obtain ⟨J, hJ, hJ'⟩ := H
    refine (IH _ hJ ?_).imp
      fun t ↦ And.imp_left (fun ht ↦ ht.trans (Finset.erase_subset _ _))
    rw [← Finset.insert_erase hJ] at hs
    simp [← hs, hJ']

open scoped Function -- required for scoped `on` notation

lemma isPrimary_decomposition_pairwise_ne_radical {I : Ideal R}
    {s : Finset (Ideal R)} (hs : s.inf id = I) (hs' : ∀ ⦃J⦄, J ∈ s → J.IsPrimary) :
    ∃ t : Finset (Ideal R), t.inf id = I ∧ (∀ ⦃J⦄, J ∈ t → J.IsPrimary) ∧
      (t : Set (Ideal R)).Pairwise ((· ≠ ·) on radical) := by
  classical
  refine ⟨(s.image (fun J ↦ {I ∈ s | I.radical = J.radical})).image fun t ↦ t.inf id,
    ?_, ?_, ?_⟩
  · ext
    grind [Finset.inf_image, Submodule.mem_finsetInf]
  · simp only [Finset.mem_image, exists_exists_and_eq_and, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
    intro J hJ
    refine isPrimary_finset_inf (i := J) ?_ ?_ (by simp)
    · simp [hJ]
    · simp only [Finset.mem_filter, id_eq, and_imp]
      intro y hy
      simp [hs' hy]
  · intro I hI J hJ hIJ
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, exists_exists_and_eq_and] at hI hJ
    obtain ⟨I', hI', hI⟩ := hI
    obtain ⟨J', hJ', hJ⟩ := hJ
    simp only [Function.onFun, ne_eq]
    contrapose! hIJ
    suffices I'.radical = J'.radical by
      rw [← hI, ← hJ, this]
    · rw [← hI, radical_finset_inf (i := I') (by simp [hI']) (by simp), id_eq] at hIJ
      rw [hIJ, ← hJ, radical_finset_inf (i := J') (by simp [hJ']) (by simp), id_eq]

lemma exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition [DecidableEq (Ideal R)]
    {I : Ideal R} {s : Finset (Ideal R)} (hs : s.inf id = I) (hs' : ∀ ⦃J⦄, J ∈ s → J.IsPrimary) :
    ∃ t : Finset (Ideal R), t.inf id = I ∧ (∀ ⦃J⦄, J ∈ t → J.IsPrimary) ∧
      ((t : Set (Ideal R)).Pairwise ((· ≠ ·) on radical)) ∧
      (∀ ⦃J⦄, J ∈ t → ¬ (t.erase J).inf id ≤ J) := by
  obtain ⟨t, ht, ht', ht''⟩ := isPrimary_decomposition_pairwise_ne_radical hs hs'
  obtain ⟨u, hut, hu, hu'⟩ := decomposition_erase_inf ht
  exact ⟨u, hu, fun _ hi ↦ ht' (hut hi), ht''.mono hut, hu'⟩

structure IsMinimalPrimaryDecomposition [DecidableEq (Ideal R)]
    (I : Ideal R) (t : Finset (Ideal R)) where
  inf_eq : t.inf id = I
  primary : ∀ ⦃J⦄, J ∈ t → J.IsPrimary
  distinct : (t : Set (Ideal R)).Pairwise ((· ≠ ·) on radical)
  minimal : ∀ ⦃J⦄, J ∈ t → ¬ (t.erase J).inf id ≤ J

lemma IsLasker.exists_isMinimalPrimaryDecomposition [DecidableEq (Ideal R)]
    (h : IsLasker R) (I : Ideal R) :
    ∃ t : Finset (Ideal R), I.IsMinimalPrimaryDecomposition t := by
  obtain ⟨s, hs1, hs2⟩ := h I
  obtain ⟨t, h1, h2, h3, h4⟩ :=
    exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition hs1 hs2
  exact ⟨t, h1, h2, h3, h4⟩

theorem IsPrime.eq_of_inf_eq
    {ι : Type*} {s : Finset ι} {f : ι → Ideal R} {P : Ideal R} (hp : IsPrime P)
    (hs : s.inf f = P) : ∃ i ∈ s, f i = P := by
  subst hs
  exact (hp.inf_le'.mp le_rfl).imp (fun a ⟨h1, h2⟩ ↦ ⟨h1, le_antisymm h2 (Finset.inf_le h1)⟩)

open LinearMap in
-- The quotient `R ⧸ I` requires `CommRing R`.
lemma IsMinimalPrimaryDecomposition.image_radical_eq_associated_primes {R : Type*} [CommRing R]
    [DecidableEq (Ideal R)] {I : Ideal R}
    {t : Finset (Ideal R)} (ht : I.IsMinimalPrimaryDecomposition t) :
    -- without Noetherian, should be radicals of annihilators, not associated primes
    t.image radical = associatedPrimes R (R ⧸ I) := by
  let ann (I : Ideal R) (x : R) := (toSpanSingleton R (R ⧸ I) ((Quotient.mk I) x)).ker
  have hann (I : Ideal R) (x : R) (y : R) : y ∈ ann I x ↔ x * y ∈ I := by
    simp [ann, Algebra.smul_def, ← map_mul, Quotient.eq_zero_iff_mem, mul_comm]
  have key1 (x : R) : ann I x = t.inf fun q ↦ ann q x := by
    simp [← ht.inf_eq, Ideal.ext_iff, hann]
  have key2 (x : R) : radical (ann I x) = t.inf fun q ↦ radical (ann q x) := by
    simp [key1, ← radicalInfTopHom_apply, Function.comp_def]
  ext p
  constructor <;> intro hp
  · rw [Finset.mem_coe, Finset.mem_image] at hp
    obtain ⟨q, hqt, rfl⟩ := hp
    obtain ⟨x, hxt, hxq⟩ := SetLike.not_le_iff_exists.mp (ht.minimal hqt)
    refine ⟨isPrime_radical (ht.primary hqt), x, ?_⟩
    change q.radical = ann I x
    rw [key1, ← Finset.insert_erase hqt, Finset.inf_insert]
    have key : ∀ q' ∈ t.erase q, ann q' x = ⊤ := by
      intro q' hq'
      rw [Submodule.eq_top_iff']
      intro y
      rw [hann]
      rw [Submodule.mem_finsetInf] at hxt
      exact mul_mem_right y q' (hxt q' hq')
    rw [Finset.inf_congr rfl key, Finset.inf_top, inf_top_eq]
    have key := Finset.insert_erase hqt
    ext y
    simp only [hann]
    have key := ht.primary hqt
    rw [isPrimary_iff] at key
    constructor
    · intro h
      sorry
    · intro h
      simpa [hxq] using key.2 h
  · obtain ⟨hx, x, rfl⟩ := hp
    have := IsPrime.eq_of_inf_eq (s := t) (f := radical) hx ?_
    · obtain ⟨i, hi1, hi2⟩ := this
      rw [Finset.mem_coe, Finset.mem_image]
      exact ⟨i, hi1, hi2⟩
    · refine Quotient.inductionOn' x fun x ↦ ?_
      specialize key1 x
      refine Eq.trans ?_ key1.symm
      sorry

-- This cannot be deduced from the previous lemma due to the `CommRing` assumption.
lemma IsMinimalPrimaryDecomposition.minimalPrimes_subset_image_radical [DecidableEq (Ideal R)]
    {I : Ideal R} {t : Finset (Ideal R)} (ht : I.IsMinimalPrimaryDecomposition t) :
    I.minimalPrimes ⊆ radical '' t := by
  intro p hp
  have htp : t.inf radical ≤ p := by
    rw [← hp.1.1.radical]
    transitivity I.radical
    · rw [← ht.inf_eq, ← radicalInfTopHom_apply, map_finset_inf]
      rfl
    · apply radical_mono
      exact hp.1.2
  obtain ⟨q, hqt, hqp⟩ := (IsPrime.inf_le' hp.1.1).mp htp
  refine ⟨q, hqt, le_antisymm hqp (hp.2 ⟨isPrime_radical (ht.primary hqt), ?_⟩ hqp)⟩
  rw [← ht.inf_eq]
  exact (Finset.inf_le hqt).trans le_radical

instance {I : Ideal R} (p : I.minimalPrimes) : IsPrime p.1 := p.2.1.1

/-- The `p`-primary component of `I` is the preimage of the image of `I` in `Rₚ`. -/
def component (I p : Ideal R) [p.IsPrime] : Ideal R :=
  (I.map (algebraMap R (Localization.AtPrime p))).comap (algebraMap R (Localization.AtPrime p))

lemma _root_.Set.compl_disjoint {α : Type*} (S : Set α) : Disjoint (Sᶜ) S := by
  grind

lemma component_self (p : Ideal R) [hp : p.IsPrime] : p.component p = p :=
  IsLocalization.comap_map_of_isPrime_disjoint p.primeCompl (Localization.AtPrime p)
    p hp (Set.compl_disjoint (p : Set R))

def le_component (I p : Ideal R) [p.IsPrime] : I ≤ I.component p :=
  le_comap_map

def component_mono {I J : Ideal R} (h : I ≤ J) (p : Ideal R) [p.IsPrime] :
    I.component p ≤ J.component p :=
  comap_mono (map_mono h)

lemma component_def (I p : Ideal R) [hp : p.IsPrime]
    (A : Type*) [CommSemiring A] [Algebra R A] [IsLocalization.AtPrime A p] :
    I.component p = (I.map (algebraMap R A)).comap (algebraMap R A) := by
  let φ := IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) A
  rw [← φ.toAlgHom.comp_algebraMap, ← map_map, ← comap_comap, comap_map_of_bijective, component]
  exact φ.bijective

lemma IsPrimary.comap {R S : Type*} [CommSemiring R] [CommSemiring S] {I : Ideal S} (hI : I.IsPrimary)
    (φ : R →+* S) : (I.comap φ).IsPrimary := by
  rw [isPrimary_iff] at hI ⊢
  refine ⟨comap_ne_top φ hI.1, fun h ↦ ?_⟩
  rw [mem_comap, map_mul] at h
  rw [← comap_radical φ I]
  exact hI.2 h

lemma IsLocalization.foo_of_mem_minimalPrimes
    {R : Type*} [CommSemiring R] (I : Ideal R)
    (p : Ideal R) [hp : p.IsPrime] (hp' : p ∈ I.minimalPrimes)
    (S : Type*) [CommSemiring S] [Algebra R S] [IsLocalization.AtPrime S p] :
    (I.map (algebraMap R S)).minimalPrimes = {p.map (algebraMap R S)} := by
  rw [IsLocalization.minimalPrimes_map p.primeCompl S I, Set.eq_singleton_iff_unique_mem]
  constructor
  · rwa [Set.mem_preimage, IsLocalization.comap_map_of_isPrime_disjoint p.primeCompl S p hp]
    exact Set.compl_disjoint (p : Set R)
  · rintro q hq
    rw [Set.mem_preimage] at hq
    by_contra! hqp
    replace hqp : q.comap (algebraMap R S) ≠ p := by
      contrapose! hqp
      rw [← hqp, IsLocalization.map_comap p.primeCompl]
    replace hqp : ¬ q.comap (algebraMap R S) ≤ p := by
      contrapose! hqp
      exact le_antisymm hqp (hp'.2 hq.1 hqp)
    replace hqp : ¬ Disjoint (p.primeCompl : Set R) (q.comap (algebraMap R S) : Set R) := by
      contrapose! hqp
      rw [← Set.subset_compl_iff_disjoint_right] at hqp
      refine Set.compl_subset_compl.mp hqp
    rw [← IsLocalization.map_algebraMap_ne_top_iff_disjoint p.primeCompl S] at hqp
    simp only [ne_eq, not_not] at hqp
    rw [IsLocalization.map_comap p.primeCompl S] at hqp
    rw [hqp, comap_top] at hq
    have key := hq.1.1
    exact key.ne_top rfl

lemma isPrimary_component (I : Ideal R) (p : Ideal R) [hp : p.IsPrime] (hpI : p ∈ I.minimalPrimes) :
    (I.component p).IsPrimary := by
  classical
  have tada (x : R) : x ∈ I.component p ↔ ∃ y ∉ p, y * x ∈ I :=
    IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl (Localization.AtPrime p) I x
  apply IsPrimary.comap
  apply isPrimary_of_isMaximal_radical
  have h1 := IsLocalization.minimalPrimes_map p.primeCompl (Localization.AtPrime p) I
  rw [← Ideal.sInf_minimalPrimes]
  rw [IsLocalization.foo_of_mem_minimalPrimes I p hpI (Localization.AtPrime p),
    sInf_singleton]
  exact IsLocalization.AtPrime.isMaximal_map p (Localization.AtPrime p)

lemma radical_component (I : Ideal R) (p : Ideal R) [hp : p.IsPrime] (hpI : p ∈ I.minimalPrimes) :
    (I.component p).radical = p := by
  suffices (I.component p).radical ≤ p from
    le_antisymm this (hpI.2 ⟨isPrime_radical (I.isPrimary_component p hpI),
      (I.le_component p).trans le_radical⟩ this)
  conv_rhs => rw [← IsPrime.radical hp, ← component_self p]
  exact radical_mono (component_mono hpI.1.2 p)

-- Preimage of `I Rₚ` under the localization map `R → Rₚ`.
lemma IsMinimalPrimaryDecomposition.foo [DecidableEq (Ideal R)]
    {I : Ideal R} {t : Finset (Ideal R)} (ht : I.IsMinimalPrimaryDecomposition t)
    (p : Ideal R) [p.IsPrime] (hp : p ∈ I.minimalPrimes) :
    I.component p ∈ t := by
  -- we know that the component is a primary ideal with radical p
  -- and we know that some primary ideal with radical p appears
  -- but need to prove that the component is the one that appears
  sorry

end Ideal

end IsLasker

namespace Ideal

section Noetherian

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

lemma _root_.InfIrred.isPrimary {I : Ideal R} (h : InfIrred I) : I.IsPrimary := by
  rw [Ideal.isPrimary_iff]
  refine ⟨h.ne_top, fun {a b} hab ↦ ?_⟩
  let f : ℕ → Ideal R := fun n ↦ (I.colon (span {b ^ n}))
  have hf : Monotone f := by
    intro n m hnm
    simp_rw [f]
    exact (Submodule.colon_mono le_rfl (Ideal.span_singleton_le_span_singleton.mpr
      (pow_dvd_pow b hnm)))
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr ‹_› ⟨f, hf⟩
  rcases h with ⟨-, h⟩
  specialize @h (I.colon (span {b ^ n})) (I + (span {b ^ n})) ?_
  · refine le_antisymm (fun r ↦ ?_) (le_inf (fun _ ↦ ?_) ?_)
    · simp only [Submodule.add_eq_sup, sup_comm I, mem_inf, mem_colon_singleton,
        mem_span_singleton_sup, and_imp, forall_exists_index]
      rintro hrb t s hs rfl
      refine add_mem ?_ hs
      have := hn (n + n) (by simp)
      simp only [OrderHom.coe_mk, f] at this
      rw [add_mul, mul_assoc, ← pow_add] at hrb
      rwa [← mem_colon_singleton, this, mem_colon_singleton,
           ← Ideal.add_mem_iff_left _ (Ideal.mul_mem_right _ _ hs)]
    · simpa only [mem_colon_singleton] using mul_mem_right _ _
    · simp
  rcases h with (h | h)
  · replace h : I = I.colon (span {b}) := by
      rcases eq_or_ne n 0 with rfl | hn'
      · simpa [f] using hn 1 zero_le_one
      refine le_antisymm ?_ (h.le.trans' (Submodule.colon_mono le_rfl ?_))
      · intro
        simpa only [mem_colon_singleton] using mul_mem_right _ _
      · exact span_singleton_le_span_singleton.mpr (dvd_pow_self b hn')
    rw [← mem_colon_singleton, ← h] at hab
    exact Or.inl hab
  · rw [← h]
    refine Or.inr ⟨n, ?_⟩
    simpa using mem_sup_right (mem_span_singleton_self _)

variable (R) in
/-- The Lasker--Noether theorem: every ideal in a Noetherian ring admits a decomposition into
  primary ideals. -/
lemma isLasker : IsLasker R := fun I ↦
  (exists_infIrred_decomposition I).imp fun _ h ↦ h.imp_right fun h' _ ht ↦ (h' ht).isPrimary

end Noetherian

end Ideal
