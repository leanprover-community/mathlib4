/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Filippo A. E. Nuccio, Andrew Yang
-/
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Spectrum.Prime.Defs

/-!
# Prime spectrum of a commutative (semi)ring

For the Zariski topology, see `Mathlib/RingTheory/Spectrum/Prime/Topology.lean`.

(It is also naturally endowed with a sheaf of rings,
which is constructed in `AlgebraicGeometry.StructureSheaf`.)

## Main definitions

* `zeroLocus s`: The zero locus of a subset `s` of `R`
  is the subset of `PrimeSpectrum R` consisting of all prime ideals that contain `s`.
* `vanishingIdeal t`: The vanishing ideal of a subset `t` of `PrimeSpectrum R`
  is the intersection of points in `t` (viewed as prime ideals).

## Conventions

We denote subsets of (semi)rings with `s`, `s'`, etc...
whereas we denote subsets of prime spectra with `t`, `t'`, etc...

## Inspiration/contributors

The contents of this file draw inspiration from <https://github.com/ramonfmir/lean-scheme>
which has contributions from Ramon Fernandez Mir, Kevin Buzzard, Kenny Lau,
and Chris Hughes (on an earlier repository).

## References
* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1967]
-/

-- A dividing line between this file and `Mathlib/RingTheory/Spectrum/Prime/Topology.lean` is
-- that we should not depend on the Zariski topology here
assert_not_exists TopologicalSpace

noncomputable section

open scoped Pointwise

universe u v

variable (R : Type u) (S : Type v)

namespace PrimeSpectrum

section CommSemiRing

variable [CommSemiring R] [CommSemiring S]
variable {R S}

lemma nonempty_iff_nontrivial : Nonempty (PrimeSpectrum R) ↔ Nontrivial R := by
  refine ⟨fun ⟨p⟩ ↦ ⟨0, 1, fun h ↦ p.2.ne_top ?_⟩, fun h ↦ ?_⟩
  · simp [Ideal.eq_top_iff_one p.asIdeal, ← h]
  · obtain ⟨I, hI⟩ := Ideal.exists_maximal R
    exact ⟨⟨I, hI.isPrime⟩⟩

lemma isEmpty_iff_subsingleton : IsEmpty (PrimeSpectrum R) ↔ Subsingleton R := by
  rw [← not_iff_not, not_isEmpty_iff, not_subsingleton_iff_nontrivial, nonempty_iff_nontrivial]

instance [Nontrivial R] : Nonempty <| PrimeSpectrum R :=
  nonempty_iff_nontrivial.mpr inferInstance

/-- The prime spectrum of the zero ring is empty. -/
instance [Subsingleton R] : IsEmpty (PrimeSpectrum R) :=
  isEmpty_iff_subsingleton.mpr inferInstance

lemma nontrivial (p : PrimeSpectrum R) : Nontrivial R :=
  nonempty_iff_nontrivial.mp ⟨p⟩

variable (R S)

theorem range_asIdeal : Set.range PrimeSpectrum.asIdeal = {J : Ideal R | J.IsPrime} :=
  Set.ext fun J ↦
    ⟨fun hJ ↦ let ⟨j, hj⟩ := Set.mem_range.mp hJ; Set.mem_setOf.mpr <| hj ▸ j.isPrime,
      fun hJ ↦ Set.mem_range.mpr ⟨⟨J, Set.mem_setOf.mp hJ⟩, rfl⟩⟩

/-- The map from the direct sum of prime spectra to the prime spectrum of a direct product. -/
@[simp]
def primeSpectrumProdOfSum : PrimeSpectrum R ⊕ PrimeSpectrum S → PrimeSpectrum (R × S)
  | Sum.inl ⟨I, _⟩ => ⟨Ideal.prod I ⊤, Ideal.isPrime_ideal_prod_top⟩
  | Sum.inr ⟨J, _⟩ => ⟨Ideal.prod ⊤ J, Ideal.isPrime_ideal_prod_top'⟩

/-- The prime spectrum of `R × S` is in bijection with the disjoint unions of the prime spectrum of
`R` and the prime spectrum of `S`. -/
noncomputable def primeSpectrumProd :
    PrimeSpectrum (R × S) ≃ PrimeSpectrum R ⊕ PrimeSpectrum S :=
  Equiv.symm <|
    Equiv.ofBijective (primeSpectrumProdOfSum R S) (by
        constructor
        · rintro (⟨I, hI⟩ | ⟨J, hJ⟩) (⟨I', hI'⟩ | ⟨J', hJ'⟩) h <;>
          simp only [mk.injEq, Ideal.prod_inj, primeSpectrumProdOfSum] at h
          · simp only [h]
          · exact False.elim (hI.ne_top h.left)
          · exact False.elim (hJ.ne_top h.right)
          · simp only [h]
        · rintro ⟨I, hI⟩
          rcases (Ideal.ideal_prod_prime I).mp hI with (⟨p, ⟨hp, rfl⟩⟩ | ⟨p, ⟨hp, rfl⟩⟩)
          · exact ⟨Sum.inl ⟨p, hp⟩, rfl⟩
          · exact ⟨Sum.inr ⟨p, hp⟩, rfl⟩)

variable {R S}

@[simp]
theorem primeSpectrumProd_symm_inl_asIdeal (x : PrimeSpectrum R) :
    ((primeSpectrumProd R S).symm <| Sum.inl x).asIdeal = Ideal.prod x.asIdeal ⊤ := by
  cases x
  rfl

@[simp]
theorem primeSpectrumProd_symm_inr_asIdeal (x : PrimeSpectrum S) :
    ((primeSpectrumProd R S).symm <| Sum.inr x).asIdeal = Ideal.prod ⊤ x.asIdeal := by
  cases x
  rfl

/-- The zero locus of a set `s` of elements of a commutative (semi)ring `R` is the set of all
prime ideals of the ring that contain the set `s`.

An element `f` of `R` can be thought of as a dependent function on the prime spectrum of `R`.
At a point `x` (a prime ideal) the function (i.e., element) `f` takes values in the quotient ring
`R` modulo the prime ideal `x`. In this manner, `zeroLocus s` is exactly the subset of
`PrimeSpectrum R` where all "functions" in `s` vanish simultaneously.
-/
def zeroLocus (s : Set R) : Set (PrimeSpectrum R) :=
  { x | s ⊆ x.asIdeal }

@[simp]
theorem mem_zeroLocus (x : PrimeSpectrum R) (s : Set R) : x ∈ zeroLocus s ↔ s ⊆ x.asIdeal :=
  Iff.rfl

@[simp]
theorem zeroLocus_span (s : Set R) : zeroLocus (Ideal.span s : Set R) = zeroLocus s := by
  ext x
  exact (Submodule.gi R R).gc s x.asIdeal

/-- The vanishing ideal of a set `t` of points of the prime spectrum of a commutative ring `R` is
the intersection of all the prime ideals in the set `t`.

An element `f` of `R` can be thought of as a dependent function on the prime spectrum of `R`.
At a point `x` (a prime ideal) the function (i.e., element) `f` takes values in the quotient ring
`R` modulo the prime ideal `x`. In this manner, `vanishingIdeal t` is exactly the ideal of `R`
consisting of all "functions" that vanish on all of `t`.
-/
def vanishingIdeal (t : Set (PrimeSpectrum R)) : Ideal R :=
  ⨅ x ∈ t, x.asIdeal

theorem coe_vanishingIdeal (t : Set (PrimeSpectrum R)) :
    (vanishingIdeal t : Set R) = { f : R | ∀ x ∈ t, f ∈ x.asIdeal } := by
  ext f
  rw [vanishingIdeal, SetLike.mem_coe, Submodule.mem_iInf]
  apply forall_congr'; intro x
  rw [Submodule.mem_iInf]

theorem mem_vanishingIdeal (t : Set (PrimeSpectrum R)) (f : R) :
    f ∈ vanishingIdeal t ↔ ∀ x ∈ t, f ∈ x.asIdeal := by
  rw [← SetLike.mem_coe, coe_vanishingIdeal, Set.mem_setOf_eq]

@[simp]
theorem vanishingIdeal_singleton (x : PrimeSpectrum R) :
    vanishingIdeal ({x} : Set (PrimeSpectrum R)) = x.asIdeal := by simp [vanishingIdeal]

theorem subset_zeroLocus_iff_le_vanishingIdeal (t : Set (PrimeSpectrum R)) (I : Ideal R) :
    t ⊆ zeroLocus I ↔ I ≤ vanishingIdeal t :=
  ⟨fun h _ k => (mem_vanishingIdeal _ _).mpr fun _ j => (mem_zeroLocus _ _).mpr (h j) k, fun h =>
    fun x j => (mem_zeroLocus _ _).mpr (le_trans h fun _ h => ((mem_vanishingIdeal _ _).mp h) x j)⟩

section Gc

variable (R)

/-- `zeroLocus` and `vanishingIdeal` form a Galois connection. -/
theorem gc :
    @GaloisConnection (Ideal R) (Set (PrimeSpectrum R))ᵒᵈ _ _ (fun I => zeroLocus I) fun t =>
      vanishingIdeal t :=
  fun I t => subset_zeroLocus_iff_le_vanishingIdeal t I

/-- `zeroLocus` and `vanishingIdeal` form a Galois connection. -/
theorem gc_set :
    @GaloisConnection (Set R) (Set (PrimeSpectrum R))ᵒᵈ _ _ (fun s => zeroLocus s) fun t =>
      vanishingIdeal t := by
  have ideal_gc : GaloisConnection Ideal.span _ := (Submodule.gi R R).gc
  simpa [zeroLocus_span, Function.comp_def] using ideal_gc.compose (gc R)

theorem subset_zeroLocus_iff_subset_vanishingIdeal (t : Set (PrimeSpectrum R)) (s : Set R) :
    t ⊆ zeroLocus s ↔ s ⊆ vanishingIdeal t :=
  (gc_set R) s t

end Gc

theorem subset_vanishingIdeal_zeroLocus (s : Set R) : s ⊆ vanishingIdeal (zeroLocus s) :=
  (gc_set R).le_u_l s

theorem le_vanishingIdeal_zeroLocus (I : Ideal R) : I ≤ vanishingIdeal (zeroLocus I) :=
  (gc R).le_u_l I

@[simp]
theorem vanishingIdeal_zeroLocus_eq_radical (I : Ideal R) :
    vanishingIdeal (zeroLocus (I : Set R)) = I.radical :=
  Ideal.ext fun f => by
    rw [mem_vanishingIdeal, Ideal.radical_eq_sInf, Submodule.mem_sInf]
    exact ⟨fun h x hx => h ⟨x, hx.2⟩ hx.1, fun h x hx => h x.1 ⟨hx, x.2⟩⟩

theorem nilradical_eq_iInf : nilradical R = iInf asIdeal := by
  apply range_asIdeal R ▸ nilradical_eq_sInf R

@[simp] theorem vanishingIdeal_univ : vanishingIdeal Set.univ = nilradical R := by
  rw [vanishingIdeal, iInf_univ, nilradical_eq_iInf]

@[simp]
theorem zeroLocus_radical (I : Ideal R) : zeroLocus (I.radical : Set R) = zeroLocus I :=
  vanishingIdeal_zeroLocus_eq_radical I ▸ (gc R).l_u_l_eq_l I

theorem subset_zeroLocus_vanishingIdeal (t : Set (PrimeSpectrum R)) :
    t ⊆ zeroLocus (vanishingIdeal t) :=
  (gc R).l_u_le t

theorem zeroLocus_anti_mono {s t : Set R} (h : s ⊆ t) : zeroLocus t ⊆ zeroLocus s :=
  (gc_set R).monotone_l h

theorem zeroLocus_anti_mono_ideal {s t : Ideal R} (h : s ≤ t) :
    zeroLocus (t : Set R) ⊆ zeroLocus (s : Set R) :=
  (gc R).monotone_l h

theorem vanishingIdeal_anti_mono {s t : Set (PrimeSpectrum R)} (h : s ⊆ t) :
    vanishingIdeal t ≤ vanishingIdeal s :=
  (gc R).monotone_u h

theorem zeroLocus_subset_zeroLocus_iff (I J : Ideal R) :
    zeroLocus (I : Set R) ⊆ zeroLocus (J : Set R) ↔ J ≤ I.radical := by
  rw [subset_zeroLocus_iff_le_vanishingIdeal, vanishingIdeal_zeroLocus_eq_radical]

theorem zeroLocus_subset_zeroLocus_singleton_iff (f g : R) :
    zeroLocus ({f} : Set R) ⊆ zeroLocus {g} ↔ g ∈ (Ideal.span ({f} : Set R)).radical := by
  rw [← zeroLocus_span {f}, ← zeroLocus_span {g}, zeroLocus_subset_zeroLocus_iff, Ideal.span_le,
    Set.singleton_subset_iff, SetLike.mem_coe]

theorem zeroLocus_bot : zeroLocus ((⊥ : Ideal R) : Set R) = Set.univ :=
  (gc R).l_bot

@[simp]
lemma zeroLocus_nilradical : zeroLocus (nilradical R : Set R) = Set.univ := by
  rw [nilradical, zeroLocus_radical, Ideal.zero_eq_bot, zeroLocus_bot]

@[simp]
theorem zeroLocus_singleton_zero : zeroLocus ({0} : Set R) = Set.univ :=
  zeroLocus_bot

@[simp]
theorem zeroLocus_empty : zeroLocus (∅ : Set R) = Set.univ :=
  (gc_set R).l_bot

@[simp]
theorem vanishingIdeal_empty : vanishingIdeal (∅ : Set (PrimeSpectrum R)) = ⊤ := by
  simpa using (gc R).u_top

theorem zeroLocus_empty_of_one_mem {s : Set R} (h : (1 : R) ∈ s) : zeroLocus s = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  rw [mem_zeroLocus] at hx
  have x_prime : x.asIdeal.IsPrime := by infer_instance
  have eq_top : x.asIdeal = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    exact hx h
  apply x_prime.ne_top eq_top

@[simp]
theorem zeroLocus_singleton_one : zeroLocus ({1} : Set R) = ∅ :=
  zeroLocus_empty_of_one_mem (Set.mem_singleton (1 : R))

theorem zeroLocus_empty_iff_eq_top {I : Ideal R} : zeroLocus (I : Set R) = ∅ ↔ I = ⊤ := by
  constructor
  · contrapose!
    intro h
    rcases Ideal.exists_le_maximal I h with ⟨M, hM, hIM⟩
    exact ⟨⟨M, hM.isPrime⟩, hIM⟩
  · rintro rfl
    apply zeroLocus_empty_of_one_mem
    trivial

@[simp]
theorem zeroLocus_univ : zeroLocus (Set.univ : Set R) = ∅ :=
  zeroLocus_empty_of_one_mem (Set.mem_univ 1)

theorem vanishingIdeal_eq_top_iff {s : Set (PrimeSpectrum R)} : vanishingIdeal s = ⊤ ↔ s = ∅ := by
  rw [← top_le_iff, ← subset_zeroLocus_iff_le_vanishingIdeal, Submodule.top_coe, zeroLocus_univ,
    Set.subset_empty_iff]

theorem zeroLocus_eq_univ_iff (s : Set R) :
    zeroLocus s = Set.univ ↔ s ⊆ nilradical R := by
  rw [← Set.univ_subset_iff, subset_zeroLocus_iff_subset_vanishingIdeal, vanishingIdeal_univ]

@[deprecated (since := "2025-04-05")] alias zeroLocus_eq_top_iff := zeroLocus_eq_univ_iff

theorem zeroLocus_sup (I J : Ideal R) :
    zeroLocus ((I ⊔ J : Ideal R) : Set R) = zeroLocus I ∩ zeroLocus J :=
  (gc R).l_sup

theorem zeroLocus_union (s s' : Set R) : zeroLocus (s ∪ s') = zeroLocus s ∩ zeroLocus s' :=
  (gc_set R).l_sup

theorem vanishingIdeal_union (t t' : Set (PrimeSpectrum R)) :
    vanishingIdeal (t ∪ t') = vanishingIdeal t ⊓ vanishingIdeal t' :=
  (gc R).u_inf

theorem zeroLocus_iSup {ι : Sort*} (I : ι → Ideal R) :
    zeroLocus ((⨆ i, I i : Ideal R) : Set R) = ⋂ i, zeroLocus (I i) :=
  (gc R).l_iSup

theorem zeroLocus_iUnion {ι : Sort*} (s : ι → Set R) :
    zeroLocus (⋃ i, s i) = ⋂ i, zeroLocus (s i) :=
  (gc_set R).l_iSup

theorem zeroLocus_iUnion₂ {ι : Sort*} {κ : (i : ι) → Sort*} (s : ∀ i, κ i → Set R) :
    zeroLocus (⋃ (i) (j), s i j) = ⋂ (i) (j), zeroLocus (s i j) :=
  (gc_set R).l_iSup₂

theorem zeroLocus_bUnion (s : Set (Set R)) :
    zeroLocus (⋃ s' ∈ s, s' : Set R) = ⋂ s' ∈ s, zeroLocus s' := by simp only [zeroLocus_iUnion]

theorem vanishingIdeal_iUnion {ι : Sort*} (t : ι → Set (PrimeSpectrum R)) :
    vanishingIdeal (⋃ i, t i) = ⨅ i, vanishingIdeal (t i) :=
  (gc R).u_iInf

theorem zeroLocus_inf (I J : Ideal R) :
    zeroLocus ((I ⊓ J : Ideal R) : Set R) = zeroLocus I ∪ zeroLocus J :=
  Set.ext fun x => x.2.inf_le

theorem union_zeroLocus (s s' : Set R) :
    zeroLocus s ∪ zeroLocus s' = zeroLocus (Ideal.span s ⊓ Ideal.span s' : Ideal R) := by
  rw [zeroLocus_inf]
  simp

theorem zeroLocus_mul (I J : Ideal R) :
    zeroLocus ((I * J : Ideal R) : Set R) = zeroLocus I ∪ zeroLocus J :=
  Set.ext fun x => x.2.mul_le

theorem zeroLocus_singleton_mul (f g : R) :
    zeroLocus ({f * g} : Set R) = zeroLocus {f} ∪ zeroLocus {g} :=
  Set.ext fun x => by simpa using x.2.mul_mem_iff_mem_or_mem

@[simp]
theorem zeroLocus_pow (I : Ideal R) {n : ℕ} (hn : n ≠ 0) :
    zeroLocus ((I ^ n : Ideal R) : Set R) = zeroLocus I :=
  zeroLocus_radical (I ^ n) ▸ (I.radical_pow hn).symm ▸ zeroLocus_radical I

@[simp]
theorem zeroLocus_singleton_pow (f : R) (n : ℕ) (hn : 0 < n) :
    zeroLocus ({f ^ n} : Set R) = zeroLocus {f} :=
  Set.ext fun x => by simpa using x.2.pow_mem_iff_mem n hn

theorem sup_vanishingIdeal_le (t t' : Set (PrimeSpectrum R)) :
    vanishingIdeal t ⊔ vanishingIdeal t' ≤ vanishingIdeal (t ∩ t') := by
  intro r
  rw [Submodule.mem_sup, mem_vanishingIdeal]
  rintro ⟨f, hf, g, hg, rfl⟩ x ⟨hxt, hxt'⟩
  rw [mem_vanishingIdeal] at hf hg
  apply Submodule.add_mem <;> solve_by_elim

theorem mem_compl_zeroLocus_iff_notMem {f : R} {I : PrimeSpectrum R} :
    I ∈ (zeroLocus {f} : Set (PrimeSpectrum R))ᶜ ↔ f ∉ I.asIdeal := by
  rw [Set.mem_compl_iff, mem_zeroLocus, Set.singleton_subset_iff]; rfl

@[deprecated (since := "2025-05-23")]
alias mem_compl_zeroLocus_iff_not_mem := mem_compl_zeroLocus_iff_notMem

@[simp]
lemma zeroLocus_insert_zero (s : Set R) : zeroLocus (insert 0 s) = zeroLocus s := by
  rw [← Set.union_singleton, zeroLocus_union, zeroLocus_singleton_zero, Set.inter_univ]

@[simp]
lemma zeroLocus_diff_singleton_zero (s : Set R) : zeroLocus (s \ {0}) = zeroLocus s := by
  rw [← zeroLocus_insert_zero, ← zeroLocus_insert_zero (s := s)]; simp

lemma zeroLocus_smul_of_isUnit {r : R} (hr : IsUnit r) (s : Set R) :
    zeroLocus (r • s) = zeroLocus s := by
  ext; simp [Set.subset_def, ← Set.image_smul, Ideal.unit_mul_mem_iff_mem _ hr]

section Order

instance [IsDomain R] : OrderBot (PrimeSpectrum R) where
  bot := ⟨⊥, Ideal.bot_prime⟩
  bot_le I := @bot_le _ _ _ I.asIdeal

instance {R : Type*} [Field R] : Unique (PrimeSpectrum R) where
  default := ⊥
  uniq x := PrimeSpectrum.ext ((IsSimpleOrder.eq_bot_or_eq_top _).resolve_right x.2.ne_top)

/-- Also see `PrimeSpectrum.isClosed_singleton_iff_isMaximal` -/
lemma isMax_iff {x : PrimeSpectrum R} :
    IsMax x ↔ x.asIdeal.IsMaximal := by
  refine ⟨fun hx ↦ ⟨⟨x.2.ne_top, fun I hI ↦ ?_⟩⟩, fun hx y e ↦ (hx.eq_of_le y.2.ne_top e).ge⟩
  by_contra e
  obtain ⟨m, hm, hm'⟩ := Ideal.exists_le_maximal I e
  exact hx.not_lt (show x < ⟨m, hm.isPrime⟩ from hI.trans_le hm')

lemma zeroLocus_eq_singleton (m : Ideal R) [m.IsMaximal] :
    zeroLocus m = {⟨m, inferInstance⟩} := by
  ext I
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [mem_zeroLocus, SetLike.coe_subset_coe] at h
    simpa using PrimeSpectrum.ext_iff.mpr (Ideal.IsMaximal.eq_of_le ‹_› I.2.ne_top h).symm
  · simp [Set.mem_singleton_iff.mp h]

lemma isMin_iff {x : PrimeSpectrum R} :
    IsMin x ↔ x.asIdeal ∈ minimalPrimes R := by
  change IsMin _ ↔ Minimal (fun q : Ideal R ↦ q.IsPrime ∧ ⊥ ≤ q) _
  simp only [IsMin, Minimal, x.2, bot_le, and_self, and_true, true_and]
  exact ⟨fun H y hy e ↦ @H ⟨y, hy⟩ e, fun H y e ↦ H y.2 e⟩

end Order

section Noetherian

open Submodule

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]

/-- In a Noetherian ring, every ideal contains a product of prime ideals
([samuel1967, § 3.3, Lemma 3]). -/
theorem exists_primeSpectrum_prod_le (I : Ideal R) :
    ∃ Z : Multiset (PrimeSpectrum R), Multiset.prod (Z.map asIdeal) ≤ I := by
  induction I using IsNoetherian.induction with | hgt M hgt =>
  change Ideal R at M
  by_cases h_prM : M.IsPrime
  · use {⟨M, h_prM⟩}
    rw [Multiset.map_singleton, Multiset.prod_singleton]
  by_cases htop : M = ⊤
  · rw [htop]
    exact ⟨0, le_top⟩
  have lt_add : ∀ z ∉ M, M < M + span R {z} := by
    intro z hz
    refine lt_of_le_of_ne le_sup_left fun m_eq => hz ?_
    rw [m_eq]
    exact Ideal.mem_sup_right (mem_span_singleton_self z)
  obtain ⟨x, hx, y, hy, hxy⟩ := (Ideal.not_isPrime_iff.mp h_prM).resolve_left htop
  obtain ⟨Wx, h_Wx⟩ := hgt (M + span R {x}) (lt_add _ hx)
  obtain ⟨Wy, h_Wy⟩ := hgt (M + span R {y}) (lt_add _ hy)
  use Wx + Wy
  rw [Multiset.map_add, Multiset.prod_add]
  apply le_trans (mul_le_mul' h_Wx h_Wy)
  rw [add_mul]
  apply sup_le (show M * (M + span R {y}) ≤ M from Ideal.mul_le_right)
  rw [mul_add]
  apply sup_le (show span R {x} * M ≤ M from Ideal.mul_le_left)
  rwa [span_mul_span, Set.singleton_mul_singleton, span_singleton_le_iff_mem]

/-- In a Noetherian integral domain which is not a field, every non-zero ideal contains a non-zero
  product of prime ideals; in a field, the whole ring is a non-zero ideal containing only 0 as
  product or prime ideals ([samuel1967, § 3.3, Lemma 3]) -/
theorem exists_primeSpectrum_prod_le_and_ne_bot_of_domain (h_fA : ¬IsField A) {I : Ideal A}
    (h_nzI : I ≠ ⊥) :
    ∃ Z : Multiset (PrimeSpectrum A),
      Multiset.prod (Z.map asIdeal) ≤ I ∧ Multiset.prod (Z.map asIdeal) ≠ ⊥ := by
  induction I using IsNoetherian.induction with | hgt M hgt =>
  change Ideal A at M
  have hA_nont : Nontrivial A := IsDomain.toNontrivial
  by_cases h_topM : M = ⊤
  · rcases h_topM with rfl
    obtain ⟨p_id, h_nzp, h_pp⟩ : ∃ p : Ideal A, p ≠ ⊥ ∧ p.IsPrime := by
      apply Ring.not_isField_iff_exists_prime.mp h_fA
    use ({⟨p_id, h_pp⟩} : Multiset (PrimeSpectrum A)), le_top
    rwa [Multiset.map_singleton, Multiset.prod_singleton]
  by_cases h_prM : M.IsPrime
  · use ({⟨M, h_prM⟩} : Multiset (PrimeSpectrum A))
    rw [Multiset.map_singleton, Multiset.prod_singleton]
    exact ⟨le_rfl, h_nzI⟩
  obtain ⟨x, hx, y, hy, h_xy⟩ := (Ideal.not_isPrime_iff.mp h_prM).resolve_left h_topM
  have lt_add : ∀ z ∉ M, M < M + span A {z} := by
    intro z hz
    refine lt_of_le_of_ne le_sup_left fun m_eq => hz ?_
    rw [m_eq]
    exact mem_sup_right (mem_span_singleton_self z)
  obtain ⟨Wx, h_Wx_le, h_Wx_ne⟩ := hgt (M + span A {x}) (lt_add _ hx) (ne_bot_of_gt (lt_add _ hx))
  obtain ⟨Wy, h_Wy_le, h_Wx_ne⟩ := hgt (M + span A {y}) (lt_add _ hy) (ne_bot_of_gt (lt_add _ hy))
  use Wx + Wy
  rw [Multiset.map_add, Multiset.prod_add]
  refine ⟨le_trans (mul_le_mul' h_Wx_le h_Wy_le) ?_, mt Ideal.mul_eq_bot.mp ?_⟩
  · rw [add_mul]
    apply sup_le (show M * (M + span A {y}) ≤ M from Ideal.mul_le_right)
    rw [mul_add]
    apply sup_le (show span A {x} * M ≤ M from Ideal.mul_le_left)
    rwa [span_mul_span, Set.singleton_mul_singleton, span_singleton_le_iff_mem]
  · rintro (hx | hy) <;> contradiction

end Noetherian

end CommSemiRing

end PrimeSpectrum
