/-
Copyright (c) 2024 Thomas Browning, Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Yakov Pechersky
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
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

-/

@[expose] public section

-- all PRed
section for_mathlib

open Ideal

theorem Submodule.comap_finset_inf {R M M' : Type*} [Semiring R] [AddCommMonoid M]
    [AddCommMonoid M'] [Module R M] [Module R M'] (f : M →ₗ[R] M')
    {ι : Type*} (s : Finset ι) (g : ι → Submodule R M') : (s.inf g).comap f =
      s.inf (Submodule.comap f ∘ g) := by
  simp [Finset.inf_eq_iInf]

theorem Ideal.comap_finset_inf {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    {ι : Type*} (s : Finset ι) (g : ι → Ideal S) : (s.inf g).comap f = s.inf (comap f ∘ g) := by
  exact Finset.comp_inf_eq_inf_comp (comap f) (fun x ↦ congrFun rfl) rfl

@[simp]
theorem Submodule.coe_eq_univ {R M : Type*}
    [CommSemiring R] [AddCommMonoid M] [Module R M] {I : Submodule R M} :
    (I : Set M) = Set.univ ↔ I = ⊤ := by
  rw [iff_comm, ← SetLike.coe_set_eq, top_coe]

theorem Submodule.IsPrimary.isPrime_radical_colon {R M : Type*}
    [CommSemiring R] [AddCommMonoid M] [Module R M] {I : Submodule R M} (hI : I.IsPrimary) :
    (I.colon Set.univ).radical.IsPrime := by
  refine isPrime_iff.mpr <| hI.imp (by simp) fun h x y ⟨n, hn⟩ ↦ ?_
  simp_rw [← mem_colon_iff_le, ← mem_radical_iff] at h
  refine or_iff_not_imp_left.mpr fun hx ↦ ⟨n, ?_⟩
  simp only [mul_pow, mem_colon, Set.mem_univ, true_imp_iff, mul_smul] at hn ⊢
  exact fun p ↦ (h (hn p)).resolve_right (mt mem_radical_of_pow_mem hx)

theorem _root_.Submodule.IsPrimary.radical_ann_of_notMem {R M : Type*}
    [CommSemiring R] [AddCommMonoid M] [Module R M] {I : Submodule R M} {m : M}
    (hI : I.IsPrimary) (hm : m ∉ I) :
    (I.colon {m}).radical = (I.colon Set.univ).radical :=
  le_antisymm (radical_le_radical_iff.mpr fun _ hy ↦
    (hI.2 (Submodule.mem_colon_singleton.mp hy)).resolve_left hm)
    (radical_mono (Submodule.colon_mono le_rfl (Set.subset_univ {m})))

end for_mathlib

section IsLasker

variable (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- A ring `R` satisfies `IsLasker R` when any `I : Ideal R` can be decomposed into
finitely many primary ideals. -/
def IsLasker : Prop :=
  ∀ I : Submodule R M, ∃ s : Finset (Submodule R M), s.inf id = I ∧ ∀ ⦃J⦄, J ∈ s → J.IsPrimary

variable {R M}

namespace Submodule

open Ideal

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
      (t : Set (Submodule R M)).Pairwise ((· ≠ ·) on fun J ↦ (J.colon Set.univ).radical) := by
  classical
  refine ⟨(s.image (fun J ↦ {I ∈ s | (I.colon Set.univ).radical =
      (J.colon Set.univ).radical})).image
    fun t ↦ t.inf id, ?_, ?_, ?_⟩
  · ext
    grind [Finset.inf_image, Submodule.mem_finsetInf]
  · simp only [Finset.mem_image, exists_exists_and_eq_and, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
    intro J hJ
    refine isPrimary_finsetInf (i := J) ?_ ?_ (by simp)
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
    suffices (I'.colon Set.univ).radical = (J'.colon Set.univ).radical by
      rw [← hI, ← hJ, this]
    · rw [← hI, colon_finsetInf,
        radical_finset_inf (i := I') (by simp [hI']) (by simp), id_eq] at hIJ
      rw [hIJ, ← hJ, colon_finsetInf,
        radical_finset_inf (i := J') (by simp [hJ']) (by simp), id_eq]

lemma exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition
    [DecidableEq (Submodule R M)] {I : Submodule R M} {s : Finset (Submodule R M)}
    (hs : s.inf id = I) (hs' : ∀ ⦃J⦄, J ∈ s → J.IsPrimary) :
    ∃ t : Finset (Submodule R M), t.inf id = I ∧ (∀ ⦃J⦄, J ∈ t → J.IsPrimary) ∧
      ((t : Set (Submodule R M)).Pairwise ((· ≠ ·) on fun J ↦ (J.colon Set.univ).radical)) ∧
      (∀ ⦃J⦄, J ∈ t → ¬ (t.erase J).inf id ≤ J) := by
  obtain ⟨t, ht, ht', ht''⟩ := isPrimary_decomposition_pairwise_ne_radical hs hs'
  obtain ⟨u, hut, hu, hu'⟩ := decomposition_erase_inf ht
  exact ⟨u, hu, fun _ hi ↦ ht' (hut hi), ht''.mono hut, hu'⟩

structure IsMinimalPrimaryDecomposition [DecidableEq (Submodule R M)]
    (I : Submodule R M) (t : Finset (Submodule R M)) where
  inf_eq : t.inf id = I
  primary : ∀ ⦃J⦄, J ∈ t → J.IsPrimary
  distinct : (t : Set (Submodule R M)).Pairwise ((· ≠ ·) on fun J ↦ (J.colon Set.univ).radical)
  minimal : ∀ ⦃J⦄, J ∈ t → ¬ (t.erase J).inf id ≤ J

protected lemma IsMinimalPrimaryDecomposition.le_radical [DecidableEq (Ideal R)]
    {I : Ideal R} {t : Finset (Ideal R)}
    (ht : I.IsMinimalPrimaryDecomposition t) {q : Ideal R} (hq : q ∈ t) : I ≤ q.radical := by
  rw [← ht.inf_eq]
  exact (Finset.inf_le hq).trans le_radical

lemma IsLasker.exists_isMinimalPrimaryDecomposition [DecidableEq (Submodule R M)]
    (h : IsLasker R M) (I : Submodule R M) :
    ∃ t : Finset (Submodule R M), I.IsMinimalPrimaryDecomposition t := by
  obtain ⟨s, hs1, hs2⟩ := h I
  obtain ⟨t, h1, h2, h3, h4⟩ :=
    exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition hs1 hs2
  exact ⟨t, h1, h2, h3, h4⟩

open Ideal LinearMap in
/-- The first uniqueness theorem for primary decomposition, Theorem 4.5 in Atiyah-Macdonald. -/
lemma IsMinimalPrimaryDecomposition.image_radical_eq_associated_primes
    {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [DecidableEq (Submodule R M)]
    {I : Submodule R M} {t : Finset (Submodule R M)} (ht : I.IsMinimalPrimaryDecomposition t) :
    (fun J : (Submodule R M) ↦ (J.colon Set.univ).radical) '' t = I.associatedPrimes := by
  classical
  have h {x} q (hq : q ∈ t) :
      (q.colon {x}).radical = if x ∈ q then ⊤ else (q.colon Set.univ).radical := by
    split_ifs with hx
    · rwa [radical_eq_top, colon_eq_top_iff_subset, Set.singleton_subset_iff]
    · exact (ht.primary hq).radical_ann_of_notMem hx
  replace h x :
      radical (I.colon {x}) = (t.filter (x ∉ ·)).inf (fun q ↦ (q.colon Set.univ).radical) := by
    rw [← ht.inf_eq, colon_finsetInf, ← radicalInfTopHom_apply]
    simp [Function.comp_def, Finset.inf_congr rfl h, Finset.inf_ite]
  ext p
  constructor
  · rintro ⟨q, hqt, rfl⟩
    obtain ⟨x, hxt, hxq⟩ := SetLike.not_le_iff_exists.mp (ht.minimal hqt)
    refine ⟨(ht.primary hqt).isPrime_radical_colon, x, ?_⟩
    rw [h, ← Finset.insert_erase (Finset.mem_filter.mpr ⟨hqt, hxq⟩), Finset.inf_insert,
      eq_comm, inf_eq_left, Finset.le_inf_iff]
    simp only [mem_finsetInf, Finset.mem_erase] at hxt
    grind
  · rintro ⟨hp, x, rfl⟩
    rw [h] at hp ⊢
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

open LocalizedModule IsLocalizedModule

/-- The second uniqueness theorem for primary decomposition, Theorem 4.10 in Atiyah-Macdonald. -/
theorem IsMinimalPrimaryDecomposition.foobar'
    {R M : Type*} [CommRing R] [AddCommMonoid M] [Module R M] [DecidableEq (Submodule R M)]
    [DecidableEq (Ideal R)]
    {I : Submodule R M} {t : Finset (Submodule R M)} (ht : I.IsMinimalPrimaryDecomposition t)
    (s₀ : Finset I.associatedPrimes) (hs₀ : IsLowerSet (s₀ : Set I.associatedPrimes))
    (s : Finset (Submodule R M)) (hs : s ⊆ t)
    (hs' : (s.image fun q ↦ (q.colon Set.univ).radical) = s₀.image (↑)) :
    ⨅ q ∈ s, q = (I.localized₀ (⨅ q ∈ s₀, q.1.primeCompl) (mkLinearMap
      (⨅ q ∈ s₀, q.1.primeCompl) M)).comap (mkLinearMap (⨅ q ∈ s₀, q.1.primeCompl) M) := by
  have ax (q : Submodule R M) (hqt : q ∈ t) (hqI : (q.colon Set.univ).radical ∈ I.associatedPrimes)
      (hqs : ⟨(q.colon Set.univ).radical, hqI⟩ ∈ s₀) : q ∈ s := by
    have key := Finset.mem_image_of_mem Subtype.val hqs
    rw [← hs', Finset.mem_image] at key
    obtain ⟨q', hq', hq''⟩ := key
    suffices q' = q by rwa [← this]
    contrapose! hq''
    exact ht.distinct (hs hq') hqt hq''
  set S := ⨅ q ∈ s₀, q.1.primeCompl
  set f := mkLinearMap S M
  have h : IsLocalizedModule S f := inferInstance
  change ⨅ q ∈ s, q = (Submodule.localized₀ S f I).comap f
  rw [← ht.inf_eq, ← localized₀FrameHom_apply, map_finset_inf, Submodule.comap_finset_inf]
  simp only [Function.comp_def, id_eq, localized₀FrameHom_apply]
  rw [← Finset.sdiff_union_of_subset hs, Finset.inf_union]
  have key0 : ∀ q ∈ s, (S : Set R) ⊆ (q.colon Set.univ).radicalᶜ := by
    intro q hq
    simp only [S, Submonoid.coe_iInf]
    replace hq : (q.colon Set.univ).radical ∈ s.image fun q ↦ (q.colon Set.univ).radical := by
      exact Finset.mem_image_of_mem _ hq
    rw [hs', Finset.mem_image] at hq
    obtain ⟨r, hrs, hrq⟩ := hq
    rw [← hrq]
    exact Set.iInter₂_subset r hrs
  have key1 : ∀ q ∈ s, (localized₀ S f q).comap f = q := by
    intro q hq
    refine le_antisymm ?_ ?_
    · intro x hx
      simp only [mem_comap, mem_localized₀] at hx
      obtain ⟨b, hb, a, ha⟩ := hx
      rw [h.mk'_eq_iff, ← LinearMap.map_smul_of_tower] at ha
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
    suffices ((q.colon Set.univ) : Set R) ⊆ ⋃ r ∈ s, (r.colon Set.univ).radical by
      obtain ⟨r, hrs, h⟩ := (Ideal.subset_union_prime
        ⊥ ⊥ fun q hq _ _ ↦ (ht.primary (hs hq)).isPrime_radical_colon).mp this
      replace hrs : (r.colon Set.univ).radical ∈ s.image fun q ↦ (q.colon Set.univ).radical := by
        exact Finset.mem_image_of_mem _ hrs
      rw [hs', Finset.mem_image] at hrs
      obtain ⟨p, hps, hpr⟩ := hrs
      rw [← Ideal.radical_le_radical_iff, ← hpr] at h
      have hqI : (q.colon Set.univ).radical ∈ I.associatedPrimes := by
        rw [← ht.image_radical_eq_associated_primes]
        exact ⟨q, hqt, rfl⟩
      exact ax q hqt hqI (hs₀ h hps)
    contrapose! hq
    rw [Set.not_subset_iff_exists_mem_notMem] at hq
    obtain ⟨y, hy1, hy2⟩ := hq
    replace hy2 : y ∈ S := by
      simp only [Submonoid.mem_iInf, Ideal.mem_primeCompl_iff, Subtype.forall, S]
      intro r hrI hrs
      rw [← ht.image_radical_eq_associated_primes] at hrI
      obtain ⟨r, hrt, rfl⟩ := hrI
      contrapose! hy2
      exact Set.mem_biUnion (ax r hrt hrI hrs) hy2
    rw [mem_comap, mem_localized₀]
    refine ⟨y • x, ?_, ⟨y, hy2⟩, ?_⟩
    · apply hy1
      apply Set.smul_mem_smul_set
      trivial
    · rw [h.mk'_eq_iff, ← LinearMap.map_smul_of_tower, Submonoid.mk_smul]
  rw [Finset.inf_congr rfl key2, Finset.inf_congr rfl key1]
  simp [Finset.inf_eq_iInf]

end Submodule

end IsLasker

namespace Submodule

section Noetherian

open Pointwise

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [IsNoetherian R M]

lemma _root_.InfIrred.isPrimary {I : Submodule R M} (h : InfIrred I) : I.IsPrimary := by
  rw [Submodule.IsPrimary]
  refine ⟨h.ne_top, fun {a b} hab ↦ ?_⟩
  let f : ℕ → Submodule R M := fun n ↦
  { carrier := {x | a ^ n • x ∈ I}
    add_mem' hx hy := by simp [I.add_mem hx hy]
    zero_mem' := by simp
    smul_mem' x y h := by simp [smul_comm _ x, I.smul_mem x h] }
  have hf : Monotone f := by
    intro n m hnm x hx
    simpa [hnm, smul_smul, ← pow_add] using I.smul_mem (a ^ (m - n)) hx
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr ‹_› ⟨f, hf⟩
  rcases h with ⟨-, h⟩
  specialize @h (f n) (I + a ^ n • ⊤) ?_
  · refine le_antisymm (fun r ⟨h1, h2⟩ ↦ ?_) (le_inf (fun x ↦ I.smul_mem (a ^ n)) (by simp))
    simp only [add_eq_sup, SetLike.mem_coe, mem_sup, mem_smul_pointwise_iff_exists] at h2
    obtain ⟨x, hx, -, ⟨y, -, rfl⟩, rfl⟩ := h2
    have h : (a ^ n • y ∈ I) = (a ^ (n + n) • y ∈ I) := congr_arg (y ∈ ·) (hn (n + n) le_add_self)
    rw [pow_add, mul_smul] at h
    rwa [I.add_mem_iff_right hx, h, ← I.add_mem_iff_right (I.smul_mem (a ^ n) hx), ← smul_add]
  rw [add_eq_sup, sup_eq_left] at h
  refine h.imp (fun h ↦ ?_) (fun h ↦ ⟨n, h⟩)
  replace hn : f n = f (n + 1) := hn (n + 1) n.le_succ
  rw [← h, hn]
  rw [← h] at hab
  simpa [f, pow_succ, mul_smul] using hab

variable (R M) in
/-- The Lasker--Noether theorem: every ideal in a Noetherian ring admits a decomposition into
  primary ideals. -/
lemma isLasker : IsLasker R M := fun I ↦
  (exists_infIrred_decomposition I).imp fun _ h ↦ h.imp_right fun h' _ ht ↦ (h' ht).isPrimary

end Noetherian

end Submodule
