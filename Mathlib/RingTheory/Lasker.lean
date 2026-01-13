/-
Copyright (c) 2024 Thomas Browning, Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Yakov Pechersky
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Order.Irreducible
public import Mathlib.RingTheory.Ideal.Annihilator
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

-/

@[expose] public section

section for_mathlib

open Ideal

theorem _root_.IsLocalization.map_inf {R : Type*} [CommSemiring R] (M : Submonoid R)
    (S : Type*) [CommSemiring S] [Algebra R S] [IsLocalization M S] (I J : Ideal R) :
    (I ⊓ J).map (algebraMap R S) = I.map (algebraMap R S) ⊓ J.map (algebraMap R S) := by
  refine le_antisymm (map_inf_le (algebraMap R S)) fun x hx ↦ ?_
  simp only [mem_inf, IsLocalization.mem_map_algebraMap_iff M, Prod.exists] at hx ⊢
  obtain ⟨⟨⟨i, hi⟩, mi, hi'⟩, ⟨j, hj⟩, mj, hj'⟩ := hx
  simp only [← IsLocalization.eq_mk'_iff_mul_eq] at hi' hj'
  obtain ⟨m, hm⟩ := IsLocalization.eq.mp (hi'.symm.trans hj')
  rw [← mul_assoc, ← mul_assoc, mul_comm, ← mul_comm (j : R)] at hm
  refine ⟨⟨i * (m * mj : M), I.mul_mem_right _ hi, hm ▸ J.mul_mem_right _ hj⟩, mi * (m * mj), ?_⟩
  rwa [← IsLocalization.eq_mk'_iff_mul_eq, Subtype.coe_mk, IsLocalization.mk'_cancel]

/-- `IsLocalization.map_inf` as an `FrameHom`. -/
def IsLocalization.mapFrameHom
    {R : Type*} [CommSemiring R] (M : Submonoid R)
    (S : Type*) [CommSemiring S] [Algebra R S] [IsLocalization M S] :
    FrameHom (Ideal R) (Ideal S) where
  toFun := Ideal.map (algebraMap R S)
  map_inf' := IsLocalization.map_inf M S
  map_top' := Ideal.map_top (algebraMap R S)
  map_sSup' _ := (Ideal.gc_map_comap (algebraMap R S)).l_sSup.trans sSup_image.symm

@[simp]
lemma IsLocalization.mapFrameHom_apply {R : Type*} [CommSemiring R] (M : Submonoid R)
    (S : Type*) [CommSemiring S] [Algebra R S] [IsLocalization M S] (I : Ideal R) :
    IsLocalization.mapFrameHom M S I = I.map (algebraMap R S) :=
  rfl

theorem _root_.Submodule.comap_finset_inf {R M M' : Type*} [Semiring R] [AddCommMonoid M]
    [AddCommMonoid M'] [Module R M] [Module R M'] (f : M →ₗ[R] M')
    {ι : Type*} (s : Finset ι) (g : ι → Submodule R M') : (s.inf g).comap f =
      s.inf (Submodule.comap f ∘ g) := by
  simp [Finset.inf_eq_iInf]

theorem _root_.Ideal.comap_finset_inf {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    {ι : Type*} (s : Finset ι) (g : ι → Ideal S) : (s.inf g).comap f = s.inf (comap f ∘ g) := by
  exact Finset.comp_inf_eq_inf_comp (comap f) (fun x ↦ congrFun rfl) rfl

@[simp]
theorem _root_.Ideal.coe_primeCompl {R : Type*} [Semiring R] (I : Ideal R) [IsPrime I] :
    (I.primeCompl : Set R) = (I : Set R)ᶜ := rfl

end for_mathlib

section IsLasker

variable (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- A ring `R` satisfies `IsLasker R` when any `I : Ideal R` can be decomposed into
finitely many primary ideals. -/
def IsLasker : Prop :=
  ∀ I : Submodule R M, ∃ s : Finset (Submodule R M), s.inf id = I ∧ ∀ ⦃J⦄, J ∈ s → J.IsPrimary

variable {R M}

namespace Submodule

lemma decomposition_erase_inf [DecidableEq (Submodule R M)] {I : Submodule R M}
    {s : Finset (Submodule R M)} (hs : s.inf id = I) :
    ∃ t : Finset (Submodule R M), t ⊆ s ∧ t.inf id = I ∧
      ∀ ⦃J⦄, J ∈ t → ¬ (t.erase J).inf id ≤ J := by
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

lemma isPrimary_decomposition_pairwise_ne_radical {I : Submodule R M}
    {s : Finset (Submodule R M)} (hs : s.inf id = I) (hs' : ∀ ⦃J⦄, J ∈ s → J.IsPrimary) :
    ∃ t : Finset (Submodule R M), t.inf id = I ∧ (∀ ⦃J⦄, J ∈ t → J.IsPrimary) ∧
      (t : Set (Submodule R M)).Pairwise ((· ≠ ·) on fun J ↦ (J.colon ⊤).radical) := by
  classical
  refine ⟨(s.image (fun J ↦ {I ∈ s | (I.colon ⊤).radical = (J.colon ⊤).radical})).image
    fun t ↦ t.inf id, ?_, ?_, ?_⟩
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
    suffices (I'.colon ⊤).radical = (J'.colon ⊤).radical by
      rw [← hI, ← hJ, this]
    · rw [← hI, colon_finset_inf,
        Ideal.radical_finset_inf (i := I') (by simp [hI']) (by simp), id_eq] at hIJ
      rw [hIJ, ← hJ, colon_finset_inf,
        Ideal.radical_finset_inf (i := J') (by simp [hJ']) (by simp), id_eq]

lemma exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition
    [DecidableEq (Submodule R M)] {I : Submodule R M} {s : Finset (Submodule R M)}
    (hs : s.inf id = I) (hs' : ∀ ⦃J⦄, J ∈ s → J.IsPrimary) :
    ∃ t : Finset (Submodule R M), t.inf id = I ∧ (∀ ⦃J⦄, J ∈ t → J.IsPrimary) ∧
      ((t : Set (Submodule R M)).Pairwise ((· ≠ ·) on fun J ↦ (J.colon ⊤).radical)) ∧
      (∀ ⦃J⦄, J ∈ t → ¬ (t.erase J).inf id ≤ J) := by
  obtain ⟨t, ht, ht', ht''⟩ := isPrimary_decomposition_pairwise_ne_radical hs hs'
  obtain ⟨u, hut, hu, hu'⟩ := decomposition_erase_inf ht
  exact ⟨u, hu, fun _ hi ↦ ht' (hut hi), ht''.mono hut, hu'⟩

structure IsMinimalPrimaryDecomposition [DecidableEq (Submodule R M)]
    (I : Submodule R M) (t : Finset (Submodule R M)) where
  inf_eq : t.inf id = I
  primary : ∀ ⦃J⦄, J ∈ t → J.IsPrimary
  distinct : (t : Set (Submodule R M)).Pairwise ((· ≠ ·) on fun J ↦ (J.colon ⊤).radical)
  minimal : ∀ ⦃J⦄, J ∈ t → ¬ (t.erase J).inf id ≤ J

protected lemma IsMinimalPrimaryDecomposition.le_radical [DecidableEq (Ideal R)]
    {I : Ideal R} {t : Finset (Ideal R)}
    (ht : I.IsMinimalPrimaryDecomposition t) {q : Ideal R} (hq : q ∈ t) : I ≤ q.radical := by
  rw [← ht.inf_eq]
  exact (Finset.inf_le hq).trans Ideal.le_radical

lemma IsLasker.exists_isMinimalPrimaryDecomposition [DecidableEq (Submodule R M)]
    (h : IsLasker R M) (I : Submodule R M) :
    ∃ t : Finset (Submodule R M), I.IsMinimalPrimaryDecomposition t := by
  obtain ⟨s, hs1, hs2⟩ := h I
  obtain ⟨t, h1, h2, h3, h4⟩ :=
    exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition hs1 hs2
  exact ⟨t, h1, h2, h3, h4⟩

theorem _root_.Ideal.eq_inf_of_isPrime_inf
    {ι : Type*} {s : Finset ι} {f : ι → Ideal R} (hp : Ideal.IsPrime (s.inf f)) :
    ∃ i ∈ s, f i = s.inf f :=
  (hp.inf_le'.mp le_rfl).imp (fun _ ⟨h1, h2⟩ ↦ ⟨h1, le_antisymm h2 (Finset.inf_le h1)⟩)

-- todo: see if `IsPrimary.mem_or_mem` can help golf
theorem _root_.Submodule.IsPrimary.foobar {R M : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] {I : Submodule R M} (hI : I.IsPrimary) : (I.colon ⊤).radical.IsPrime := by
  rw [Ideal.isPrime_iff]
  refine hI.imp ?_ ?_
  · contrapose!
    rw [Ideal.radical_eq_top, Ideal.eq_top_iff_one]
    simp [mem_colon]
    simp [eq_top_iff']
  · simp only [← mem_colon_def, ← Ideal.mem_radical_iff]
    rintro h x y ⟨n, hn⟩
    rw [or_iff_not_imp_left]
    intro hx
    have h1 := @h (x ^ n)
    replace hx : x ^ n ∉ (I.colon ⊤).radical := by
      contrapose! hx
      exact Ideal.mem_radical_of_pow_mem hx
    simp [hx] at h1
    simp [mem_colon, mul_pow, mul_smul] at hn
    use n
    simp only [mem_colon, mem_top]
    grind

open Ideal LinearMap in
/-- The first uniqueness theorem for primary decomposition, Theorem 4.5 in Atiyah-Macdonald. -/
lemma IsMinimalPrimaryDecomposition.image_radical_eq_associated_primes
    {R M : Type*} [CommSemiring R] [AddCommGroup M] [Module R M] [DecidableEq (Submodule R M)]
    {I : Submodule R M} {t : Finset (Submodule R M)} (ht : I.IsMinimalPrimaryDecomposition t)
    {p : Ideal R} :
    p ∈ (fun J : (Submodule R M) ↦ (J.colon ⊤).radical) '' t ↔
      p.IsPrime ∧ ∃ x : M, p = (I.ann x).radical := by
  classical
  have key1 (x : M) : I.ann x = t.inf fun q ↦ q.ann x := by
    simp [← ht.inf_eq, Ideal.ext_iff, Submodule.mem_ann_iff]
  have key2 (x : M) : radical (I.ann x) = t.inf fun q ↦ radical (q.ann x) := by
    simp [key1, ← radicalInfTopHom_apply, Function.comp_def]
  have key3 (x : M) : ∀ q ∈ t, (q.ann x).radical = if x ∈ q then ⊤ else (q.colon ⊤).radical := by
    intro q hq
    split_ifs with hx
    · rwa [radical_eq_top, Submodule.ann_eq_top]
    · exact (ht.primary hq).radical_ann_of_notMem hx
  constructor <;> intro hp
  · obtain ⟨q, hqt, rfl⟩ := hp
    obtain ⟨x, hxt, hxq⟩ := SetLike.not_le_iff_exists.mp (ht.minimal hqt)
    use (ht.primary hqt).foobar
    use x
    symm
    rw [key1, ← Finset.insert_erase hqt, Finset.inf_insert]
    have key : ∀ q' ∈ t.erase q, q'.ann x = ⊤ := by
      intro q' hq'
      rw [Submodule.ann_eq_top]
      rw [Submodule.mem_finsetInf] at hxt
      exact hxt q' hq'
    rw [Finset.inf_congr rfl key, Finset.inf_top, inf_top_eq]
    symm
    rw [key3 x q hqt, if_neg hxq]
  · obtain ⟨hp, x, rfl⟩ := hp
    have key : (I.ann x).radical = (t.filter (x ∉ ·)).inf (fun q ↦ (q.colon ⊤).radical) := by
      rw [key2, Finset.inf_congr rfl (key3 x), Finset.inf_ite, Finset.inf_top, top_inf_eq]
    rw [key] at hp ⊢
    obtain ⟨q, hq1, hq2⟩ := eq_inf_of_isPrime_inf hp
    exact ⟨q, Finset.mem_of_mem_filter q hq1, hq2⟩

end Submodule

lemma Ideal.IsMinimalPrimaryDecomposition.minimalPrimes_subset_image_radical
    [DecidableEq (Ideal R)]
    {I : Ideal R} {t : Finset (Ideal R)} (ht : I.IsMinimalPrimaryDecomposition t) :
    I.minimalPrimes ⊆ radical '' t := by
  intro p hp
  have htp : t.inf radical ≤ p := by
    rw [← hp.1.1.radical]
    refine le_trans ?_ (radical_mono hp.1.2)
    rw [← ht.inf_eq, ← radicalInfTopHom_apply, map_finset_inf]
    rfl
  obtain ⟨q, hqt, hqp⟩ := (IsPrime.inf_le' hp.1.1).mp htp
  exact ⟨q, hqt, le_antisymm hqp (hp.2 ⟨isPrime_radical (ht.primary hqt), ht.le_radical hqt⟩ hqp)⟩

namespace Submodule

/-- The second uniqueness theorem for primary decomposition, Theorem 4.10 in Atiyah-Macdonald. -/
theorem IsMinimalPrimaryDecomposition.foobar {R M : Type*} [CommRing R] [AddCommMonoid M]
    [Module R M]
    [DecidableEq (Submodule R M)] {I : Submodule R M} {t : Finset (Submodule R M)}
    (ht : I.IsMinimalPrimaryDecomposition t)
    (s : Finset (Submodule R M)) (hs : s ⊆ t)
    (downward_closed : ∀ q ∈ t, ∀ r ∈ s, (q.colon ⊤).radical ≤ (r.colon ⊤).radical → q ∈ s) :
    (localized₀ (⨅ q ∈ s,
      have : (q.colon ⊤).radical.IsPrime := (ht.primary (by aesop)).foobar;
      (q.colon ⊤).radical.primeCompl) (LocalizedModule.mkLinearMap (⨅ q ∈ s,
      have : (q.colon ⊤).radical.IsPrime := (ht.primary (by aesop)).foobar;
      (q.colon ⊤).radical.primeCompl) M) I).comap (LocalizedModule.mkLinearMap (⨅ q ∈ s,
      have : (q.colon ⊤).radical.IsPrime := (ht.primary (by aesop)).foobar;
      (q.colon ⊤).radical.primeCompl) M) = ⨅ q ∈ s, q := by
  let S := ⨅ q ∈ s,
    have : (q.colon ⊤).radical.IsPrime := (ht.primary (by aesop)).foobar;
    (q.colon ⊤).radical.primeCompl
  let f := LocalizedModule.mkLinearMap S M
  have h : IsLocalizedModule S f := inferInstance
  change (Submodule.localized₀ S f I).comap f = ⨅ q ∈ s, q
  rw [← ht.inf_eq, ← IsLocalizedModule.localized₀_frameHom_apply, map_finset_inf,
    Submodule.comap_finset_inf]
  simp only [Function.comp_def, id_eq, IsLocalizedModule.localized₀_frameHom_apply]
  rw [← Finset.sdiff_union_of_subset hs, Finset.inf_union]
  have key0 : ∀ q ∈ s, (S : Set R) ⊆ (q.colon ⊤).radicalᶜ := by
    intro q hq
    simp only [S, Submonoid.coe_iInf]
    exact Set.iInter₂_subset q hq
  have key1 : ∀ q ∈ s, (localized₀ S f q).comap f = q := by
    intro q hq
    refine le_antisymm ?_ ?_
    · intro x hx
      simp only [mem_comap, mem_localized₀] at hx
      obtain ⟨b, hb, a, ha⟩ := hx
      rw [IsLocalizedModule.mk'_eq_iff, ← LinearMap.map_smul_of_tower] at ha
      obtain ⟨c, hc⟩ := h.eq_iff_exists.mp ha
      have key : (c * a) • x ∈ q := by rw [mul_smul, ← hc]; exact q.smul_mem c hb
      apply ((ht.primary (hs hq)).mem_or_mem key).resolve_right
      exact key0 q hq (c * a).2
    · rw [← map_le_iff_le_comap]
      let _ : Module (Localization S) (LocalizedModule S M) := h.module S f
      apply map_le_localized₀
  have key2 : ∀ q ∈ t \ s, (localized₀ S f q).comap f = ⊤ := by
    intro q hq
    rw [eq_top_iff']
    intro x
    contrapose! hq
    rw [Finset.mem_sdiff, not_and_not_right]
    intro hqt
    suffices ((q.colon ⊤) : Set R) ⊆ ⋃ r ∈ s, (r.colon ⊤).radical by
      obtain ⟨r, hrs, h⟩ := (Ideal.subset_union_prime
        ⊥ ⊥ fun q hq _ _ ↦ (ht.primary (hs hq)).foobar).mp this
      exact downward_closed q hqt r hrs (Ideal.radical_le_radical_iff.mpr h)
    contrapose! hq
    rw [Set.not_subset_iff_exists_mem_notMem] at hq
    obtain ⟨y, hy1, hy2⟩ := hq
    replace hy2 : y ∈ S := by simpa [S] using hy2
    rw [mem_comap, mem_localized₀]
    refine ⟨y • x, ?_, ⟨y, hy2⟩, ?_⟩
    · apply hy1
      apply Set.smul_mem_smul_set
      exact mem_top
    · rw [IsLocalizedModule.mk'_eq_iff, ← LinearMap.map_smul_of_tower, Submonoid.mk_smul]
  rw [Finset.inf_congr rfl key2, Finset.inf_congr rfl key1]
  simp [Finset.inf_eq_iInf]

end Submodule

end IsLasker

namespace Ideal

section Noetherian

variable {R M : Type*} [CommRing R] [IsNoetherianRing R] [AddCommMonoid M] [Module R M]

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
lemma isLasker : IsLasker R R := fun I ↦
  (exists_infIrred_decomposition I).imp fun _ h ↦ h.imp_right fun h' _ ht ↦ (h' ht).isPrimary

end Noetherian

end Ideal
