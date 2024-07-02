/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.LinearAlgebra.Finsupp
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Prod
import Mathlib.RingTheory.Ideal.MinimalPrime
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.Sober

#align_import algebraic_geometry.prime_spectrum.basic from "leanprover-community/mathlib"@"a7c017d750512a352b623b1824d75da5998457d0"

/-!
# Prime spectrum of a commutative (semi)ring

The prime spectrum of a commutative (semi)ring is the type of all prime ideals.
It is naturally endowed with a topology: the Zariski topology.

(It is also naturally endowed with a sheaf of rings,
which is constructed in `AlgebraicGeometry.StructureSheaf`.)

## Main definitions

* `PrimeSpectrum R`: The prime spectrum of a commutative (semi)ring `R`,
  i.e., the set of all prime ideals of `R`.
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
-/


noncomputable section

open scoped Classical

universe u v

variable (R : Type u) (S : Type v)

/-- The prime spectrum of a commutative (semi)ring `R` is the type of all prime ideals of `R`.

It is naturally endowed with a topology (the Zariski topology),
and a sheaf of commutative rings (see `AlgebraicGeometry.StructureSheaf`).
It is a fundamental building block in algebraic geometry. -/
@[ext]
structure PrimeSpectrum [CommSemiring R] where
  asIdeal : Ideal R
  isPrime : asIdeal.IsPrime
#align prime_spectrum PrimeSpectrum

@[deprecated (since := "2024-06-22")] alias PrimeSpectrum.IsPrime := PrimeSpectrum.isPrime

attribute [instance] PrimeSpectrum.isPrime

namespace PrimeSpectrum

section CommSemiRing

variable [CommSemiring R] [CommSemiring S]
variable {R S}

instance [Nontrivial R] : Nonempty <| PrimeSpectrum R :=
  let ⟨I, hI⟩ := Ideal.exists_maximal R
  ⟨⟨I, hI.isPrime⟩⟩

/-- The prime spectrum of the zero ring is empty. -/
instance [Subsingleton R] : IsEmpty (PrimeSpectrum R) :=
  ⟨fun x ↦ x.isPrime.ne_top <| SetLike.ext' <| Subsingleton.eq_univ_of_nonempty x.asIdeal.nonempty⟩
#noalign prime_spectrum.punit

variable (R S)

/-- The map from the direct sum of prime spectra to the prime spectrum of a direct product. -/
@[simp]
def primeSpectrumProdOfSum : Sum (PrimeSpectrum R) (PrimeSpectrum S) → PrimeSpectrum (R × S)
  | Sum.inl ⟨I, _⟩ => ⟨Ideal.prod I ⊤, Ideal.isPrime_ideal_prod_top⟩
  | Sum.inr ⟨J, _⟩ => ⟨Ideal.prod ⊤ J, Ideal.isPrime_ideal_prod_top'⟩
#align prime_spectrum.prime_spectrum_prod_of_sum PrimeSpectrum.primeSpectrumProdOfSum

/-- The prime spectrum of `R × S` is in bijection with the disjoint unions of the prime spectrum of
`R` and the prime spectrum of `S`. -/
noncomputable def primeSpectrumProd :
    PrimeSpectrum (R × S) ≃ Sum (PrimeSpectrum R) (PrimeSpectrum S) :=
  Equiv.symm <|
    Equiv.ofBijective (primeSpectrumProdOfSum R S) (by
        constructor
        · rintro (⟨I, hI⟩ | ⟨J, hJ⟩) (⟨I', hI'⟩ | ⟨J', hJ'⟩) h <;>
          simp only [mk.injEq, Ideal.prod.ext_iff, primeSpectrumProdOfSum] at h
          · simp only [h]
          · exact False.elim (hI.ne_top h.left)
          · exact False.elim (hJ.ne_top h.right)
          · simp only [h]
        · rintro ⟨I, hI⟩
          rcases (Ideal.ideal_prod_prime I).mp hI with (⟨p, ⟨hp, rfl⟩⟩ | ⟨p, ⟨hp, rfl⟩⟩)
          · exact ⟨Sum.inl ⟨p, hp⟩, rfl⟩
          · exact ⟨Sum.inr ⟨p, hp⟩, rfl⟩)
#align prime_spectrum.prime_spectrum_prod PrimeSpectrum.primeSpectrumProd

variable {R S}

@[simp]
theorem primeSpectrumProd_symm_inl_asIdeal (x : PrimeSpectrum R) :
    ((primeSpectrumProd R S).symm <| Sum.inl x).asIdeal = Ideal.prod x.asIdeal ⊤ := by
  cases x
  rfl
#align prime_spectrum.prime_spectrum_prod_symm_inl_as_ideal PrimeSpectrum.primeSpectrumProd_symm_inl_asIdeal

@[simp]
theorem primeSpectrumProd_symm_inr_asIdeal (x : PrimeSpectrum S) :
    ((primeSpectrumProd R S).symm <| Sum.inr x).asIdeal = Ideal.prod ⊤ x.asIdeal := by
  cases x
  rfl
#align prime_spectrum.prime_spectrum_prod_symm_inr_as_ideal PrimeSpectrum.primeSpectrumProd_symm_inr_asIdeal

/-- The zero locus of a set `s` of elements of a commutative (semi)ring `R` is the set of all
prime ideals of the ring that contain the set `s`.

An element `f` of `R` can be thought of as a dependent function on the prime spectrum of `R`.
At a point `x` (a prime ideal) the function (i.e., element) `f` takes values in the quotient ring
`R` modulo the prime ideal `x`. In this manner, `zeroLocus s` is exactly the subset of
`PrimeSpectrum R` where all "functions" in `s` vanish simultaneously.
-/
def zeroLocus (s : Set R) : Set (PrimeSpectrum R) :=
  { x | s ⊆ x.asIdeal }
#align prime_spectrum.zero_locus PrimeSpectrum.zeroLocus

@[simp]
theorem mem_zeroLocus (x : PrimeSpectrum R) (s : Set R) : x ∈ zeroLocus s ↔ s ⊆ x.asIdeal :=
  Iff.rfl
#align prime_spectrum.mem_zero_locus PrimeSpectrum.mem_zeroLocus

@[simp]
theorem zeroLocus_span (s : Set R) : zeroLocus (Ideal.span s : Set R) = zeroLocus s := by
  ext x
  exact (Submodule.gi R R).gc s x.asIdeal
#align prime_spectrum.zero_locus_span PrimeSpectrum.zeroLocus_span

/-- The vanishing ideal of a set `t` of points of the prime spectrum of a commutative ring `R` is
the intersection of all the prime ideals in the set `t`.

An element `f` of `R` can be thought of as a dependent function on the prime spectrum of `R`.
At a point `x` (a prime ideal) the function (i.e., element) `f` takes values in the quotient ring
`R` modulo the prime ideal `x`. In this manner, `vanishingIdeal t` is exactly the ideal of `R`
consisting of all "functions" that vanish on all of `t`.
-/
def vanishingIdeal (t : Set (PrimeSpectrum R)) : Ideal R :=
  ⨅ x ∈ t, x.asIdeal
#align prime_spectrum.vanishing_ideal PrimeSpectrum.vanishingIdeal

theorem coe_vanishingIdeal (t : Set (PrimeSpectrum R)) :
    (vanishingIdeal t : Set R) = { f : R | ∀ x ∈ t, f ∈ x.asIdeal } := by
  ext f
  rw [vanishingIdeal, SetLike.mem_coe, Submodule.mem_iInf]
  apply forall_congr'; intro x
  rw [Submodule.mem_iInf]
#align prime_spectrum.coe_vanishing_ideal PrimeSpectrum.coe_vanishingIdeal

theorem mem_vanishingIdeal (t : Set (PrimeSpectrum R)) (f : R) :
    f ∈ vanishingIdeal t ↔ ∀ x ∈ t, f ∈ x.asIdeal := by
  rw [← SetLike.mem_coe, coe_vanishingIdeal, Set.mem_setOf_eq]
#align prime_spectrum.mem_vanishing_ideal PrimeSpectrum.mem_vanishingIdeal

@[simp]
theorem vanishingIdeal_singleton (x : PrimeSpectrum R) :
    vanishingIdeal ({x} : Set (PrimeSpectrum R)) = x.asIdeal := by simp [vanishingIdeal]
#align prime_spectrum.vanishing_ideal_singleton PrimeSpectrum.vanishingIdeal_singleton

theorem subset_zeroLocus_iff_le_vanishingIdeal (t : Set (PrimeSpectrum R)) (I : Ideal R) :
    t ⊆ zeroLocus I ↔ I ≤ vanishingIdeal t :=
  ⟨fun h _ k => (mem_vanishingIdeal _ _).mpr fun _ j => (mem_zeroLocus _ _).mpr (h j) k, fun h =>
    fun x j => (mem_zeroLocus _ _).mpr (le_trans h fun _ h => ((mem_vanishingIdeal _ _).mp h) x j)⟩
#align prime_spectrum.subset_zero_locus_iff_le_vanishing_ideal PrimeSpectrum.subset_zeroLocus_iff_le_vanishingIdeal

section Gc

variable (R)

/-- `zeroLocus` and `vanishingIdeal` form a galois connection. -/
theorem gc :
    @GaloisConnection (Ideal R) (Set (PrimeSpectrum R))ᵒᵈ _ _ (fun I => zeroLocus I) fun t =>
      vanishingIdeal t :=
  fun I t => subset_zeroLocus_iff_le_vanishingIdeal t I
#align prime_spectrum.gc PrimeSpectrum.gc

/-- `zeroLocus` and `vanishingIdeal` form a galois connection. -/
theorem gc_set :
    @GaloisConnection (Set R) (Set (PrimeSpectrum R))ᵒᵈ _ _ (fun s => zeroLocus s) fun t =>
      vanishingIdeal t := by
  have ideal_gc : GaloisConnection Ideal.span _ := (Submodule.gi R R).gc
  simpa [zeroLocus_span, Function.comp] using ideal_gc.compose (gc R)
#align prime_spectrum.gc_set PrimeSpectrum.gc_set

theorem subset_zeroLocus_iff_subset_vanishingIdeal (t : Set (PrimeSpectrum R)) (s : Set R) :
    t ⊆ zeroLocus s ↔ s ⊆ vanishingIdeal t :=
  (gc_set R) s t
#align prime_spectrum.subset_zero_locus_iff_subset_vanishing_ideal PrimeSpectrum.subset_zeroLocus_iff_subset_vanishingIdeal

end Gc

theorem subset_vanishingIdeal_zeroLocus (s : Set R) : s ⊆ vanishingIdeal (zeroLocus s) :=
  (gc_set R).le_u_l s
#align prime_spectrum.subset_vanishing_ideal_zero_locus PrimeSpectrum.subset_vanishingIdeal_zeroLocus

theorem le_vanishingIdeal_zeroLocus (I : Ideal R) : I ≤ vanishingIdeal (zeroLocus I) :=
  (gc R).le_u_l I
#align prime_spectrum.le_vanishing_ideal_zero_locus PrimeSpectrum.le_vanishingIdeal_zeroLocus

@[simp]
theorem vanishingIdeal_zeroLocus_eq_radical (I : Ideal R) :
    vanishingIdeal (zeroLocus (I : Set R)) = I.radical :=
  Ideal.ext fun f => by
    rw [mem_vanishingIdeal, Ideal.radical_eq_sInf, Submodule.mem_sInf]
    exact ⟨fun h x hx => h ⟨x, hx.2⟩ hx.1, fun h x hx => h x.1 ⟨hx, x.2⟩⟩
#align prime_spectrum.vanishing_ideal_zero_locus_eq_radical PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical

@[simp]
theorem zeroLocus_radical (I : Ideal R) : zeroLocus (I.radical : Set R) = zeroLocus I :=
  vanishingIdeal_zeroLocus_eq_radical I ▸ (gc R).l_u_l_eq_l I
#align prime_spectrum.zero_locus_radical PrimeSpectrum.zeroLocus_radical

theorem subset_zeroLocus_vanishingIdeal (t : Set (PrimeSpectrum R)) :
    t ⊆ zeroLocus (vanishingIdeal t) :=
  (gc R).l_u_le t
#align prime_spectrum.subset_zero_locus_vanishing_ideal PrimeSpectrum.subset_zeroLocus_vanishingIdeal

theorem zeroLocus_anti_mono {s t : Set R} (h : s ⊆ t) : zeroLocus t ⊆ zeroLocus s :=
  (gc_set R).monotone_l h
#align prime_spectrum.zero_locus_anti_mono PrimeSpectrum.zeroLocus_anti_mono

theorem zeroLocus_anti_mono_ideal {s t : Ideal R} (h : s ≤ t) :
    zeroLocus (t : Set R) ⊆ zeroLocus (s : Set R) :=
  (gc R).monotone_l h
#align prime_spectrum.zero_locus_anti_mono_ideal PrimeSpectrum.zeroLocus_anti_mono_ideal

theorem vanishingIdeal_anti_mono {s t : Set (PrimeSpectrum R)} (h : s ⊆ t) :
    vanishingIdeal t ≤ vanishingIdeal s :=
  (gc R).monotone_u h
#align prime_spectrum.vanishing_ideal_anti_mono PrimeSpectrum.vanishingIdeal_anti_mono

theorem zeroLocus_subset_zeroLocus_iff (I J : Ideal R) :
    zeroLocus (I : Set R) ⊆ zeroLocus (J : Set R) ↔ J ≤ I.radical := by
  rw [subset_zeroLocus_iff_le_vanishingIdeal, vanishingIdeal_zeroLocus_eq_radical]
#align prime_spectrum.zero_locus_subset_zero_locus_iff PrimeSpectrum.zeroLocus_subset_zeroLocus_iff

theorem zeroLocus_subset_zeroLocus_singleton_iff (f g : R) :
    zeroLocus ({f} : Set R) ⊆ zeroLocus {g} ↔ g ∈ (Ideal.span ({f} : Set R)).radical := by
  rw [← zeroLocus_span {f}, ← zeroLocus_span {g}, zeroLocus_subset_zeroLocus_iff, Ideal.span_le,
    Set.singleton_subset_iff, SetLike.mem_coe]
#align prime_spectrum.zero_locus_subset_zero_locus_singleton_iff PrimeSpectrum.zeroLocus_subset_zeroLocus_singleton_iff

theorem zeroLocus_bot : zeroLocus ((⊥ : Ideal R) : Set R) = Set.univ :=
  (gc R).l_bot
#align prime_spectrum.zero_locus_bot PrimeSpectrum.zeroLocus_bot

@[simp]
theorem zeroLocus_singleton_zero : zeroLocus ({0} : Set R) = Set.univ :=
  zeroLocus_bot
#align prime_spectrum.zero_locus_singleton_zero PrimeSpectrum.zeroLocus_singleton_zero

@[simp]
theorem zeroLocus_empty : zeroLocus (∅ : Set R) = Set.univ :=
  (gc_set R).l_bot
#align prime_spectrum.zero_locus_empty PrimeSpectrum.zeroLocus_empty

@[simp]
theorem vanishingIdeal_empty : vanishingIdeal (∅ : Set (PrimeSpectrum R)) = ⊤ := by
  simpa using (gc R).u_top
#align prime_spectrum.vanishing_ideal_univ PrimeSpectrum.vanishingIdeal_empty

theorem zeroLocus_empty_of_one_mem {s : Set R} (h : (1 : R) ∈ s) : zeroLocus s = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem]
  intro x hx
  rw [mem_zeroLocus] at hx
  have x_prime : x.asIdeal.IsPrime := by infer_instance
  have eq_top : x.asIdeal = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    exact hx h
  apply x_prime.ne_top eq_top
#align prime_spectrum.zero_locus_empty_of_one_mem PrimeSpectrum.zeroLocus_empty_of_one_mem

@[simp]
theorem zeroLocus_singleton_one : zeroLocus ({1} : Set R) = ∅ :=
  zeroLocus_empty_of_one_mem (Set.mem_singleton (1 : R))
#align prime_spectrum.zero_locus_singleton_one PrimeSpectrum.zeroLocus_singleton_one

theorem zeroLocus_empty_iff_eq_top {I : Ideal R} : zeroLocus (I : Set R) = ∅ ↔ I = ⊤ := by
  constructor
  · contrapose!
    intro h
    rcases Ideal.exists_le_maximal I h with ⟨M, hM, hIM⟩
    exact ⟨⟨M, hM.isPrime⟩, hIM⟩
  · rintro rfl
    apply zeroLocus_empty_of_one_mem
    trivial
#align prime_spectrum.zero_locus_empty_iff_eq_top PrimeSpectrum.zeroLocus_empty_iff_eq_top

@[simp]
theorem zeroLocus_univ : zeroLocus (Set.univ : Set R) = ∅ :=
  zeroLocus_empty_of_one_mem (Set.mem_univ 1)
#align prime_spectrum.zero_locus_univ PrimeSpectrum.zeroLocus_univ

theorem vanishingIdeal_eq_top_iff {s : Set (PrimeSpectrum R)} : vanishingIdeal s = ⊤ ↔ s = ∅ := by
  rw [← top_le_iff, ← subset_zeroLocus_iff_le_vanishingIdeal, Submodule.top_coe, zeroLocus_univ,
    Set.subset_empty_iff]
#align prime_spectrum.vanishing_ideal_eq_top_iff PrimeSpectrum.vanishingIdeal_eq_top_iff

theorem zeroLocus_sup (I J : Ideal R) :
    zeroLocus ((I ⊔ J : Ideal R) : Set R) = zeroLocus I ∩ zeroLocus J :=
  (gc R).l_sup
#align prime_spectrum.zero_locus_sup PrimeSpectrum.zeroLocus_sup

theorem zeroLocus_union (s s' : Set R) : zeroLocus (s ∪ s') = zeroLocus s ∩ zeroLocus s' :=
  (gc_set R).l_sup
#align prime_spectrum.zero_locus_union PrimeSpectrum.zeroLocus_union

theorem vanishingIdeal_union (t t' : Set (PrimeSpectrum R)) :
    vanishingIdeal (t ∪ t') = vanishingIdeal t ⊓ vanishingIdeal t' :=
  (gc R).u_inf
#align prime_spectrum.vanishing_ideal_union PrimeSpectrum.vanishingIdeal_union

theorem zeroLocus_iSup {ι : Sort*} (I : ι → Ideal R) :
    zeroLocus ((⨆ i, I i : Ideal R) : Set R) = ⋂ i, zeroLocus (I i) :=
  (gc R).l_iSup
#align prime_spectrum.zero_locus_supr PrimeSpectrum.zeroLocus_iSup

theorem zeroLocus_iUnion {ι : Sort*} (s : ι → Set R) :
    zeroLocus (⋃ i, s i) = ⋂ i, zeroLocus (s i) :=
  (gc_set R).l_iSup
#align prime_spectrum.zero_locus_Union PrimeSpectrum.zeroLocus_iUnion

theorem zeroLocus_bUnion (s : Set (Set R)) :
    zeroLocus (⋃ s' ∈ s, s' : Set R) = ⋂ s' ∈ s, zeroLocus s' := by simp only [zeroLocus_iUnion]
#align prime_spectrum.zero_locus_bUnion PrimeSpectrum.zeroLocus_bUnion

theorem vanishingIdeal_iUnion {ι : Sort*} (t : ι → Set (PrimeSpectrum R)) :
    vanishingIdeal (⋃ i, t i) = ⨅ i, vanishingIdeal (t i) :=
  (gc R).u_iInf
#align prime_spectrum.vanishing_ideal_Union PrimeSpectrum.vanishingIdeal_iUnion

theorem zeroLocus_inf (I J : Ideal R) :
    zeroLocus ((I ⊓ J : Ideal R) : Set R) = zeroLocus I ∪ zeroLocus J :=
  Set.ext fun x => x.2.inf_le
#align prime_spectrum.zero_locus_inf PrimeSpectrum.zeroLocus_inf

theorem union_zeroLocus (s s' : Set R) :
    zeroLocus s ∪ zeroLocus s' = zeroLocus (Ideal.span s ⊓ Ideal.span s' : Ideal R) := by
  rw [zeroLocus_inf]
  simp
#align prime_spectrum.union_zero_locus PrimeSpectrum.union_zeroLocus

theorem zeroLocus_mul (I J : Ideal R) :
    zeroLocus ((I * J : Ideal R) : Set R) = zeroLocus I ∪ zeroLocus J :=
  Set.ext fun x => x.2.mul_le
#align prime_spectrum.zero_locus_mul PrimeSpectrum.zeroLocus_mul

theorem zeroLocus_singleton_mul (f g : R) :
    zeroLocus ({f * g} : Set R) = zeroLocus {f} ∪ zeroLocus {g} :=
  Set.ext fun x => by simpa using x.2.mul_mem_iff_mem_or_mem
#align prime_spectrum.zero_locus_singleton_mul PrimeSpectrum.zeroLocus_singleton_mul

@[simp]
theorem zeroLocus_pow (I : Ideal R) {n : ℕ} (hn : n ≠ 0) :
    zeroLocus ((I ^ n : Ideal R) : Set R) = zeroLocus I :=
  zeroLocus_radical (I ^ n) ▸ (I.radical_pow hn).symm ▸ zeroLocus_radical I
#align prime_spectrum.zero_locus_pow PrimeSpectrum.zeroLocus_pow

@[simp]
theorem zeroLocus_singleton_pow (f : R) (n : ℕ) (hn : 0 < n) :
    zeroLocus ({f ^ n} : Set R) = zeroLocus {f} :=
  Set.ext fun x => by simpa using x.2.pow_mem_iff_mem n hn
#align prime_spectrum.zero_locus_singleton_pow PrimeSpectrum.zeroLocus_singleton_pow

theorem sup_vanishingIdeal_le (t t' : Set (PrimeSpectrum R)) :
    vanishingIdeal t ⊔ vanishingIdeal t' ≤ vanishingIdeal (t ∩ t') := by
  intro r
  rw [Submodule.mem_sup, mem_vanishingIdeal]
  rintro ⟨f, hf, g, hg, rfl⟩ x ⟨hxt, hxt'⟩
  rw [mem_vanishingIdeal] at hf hg
  apply Submodule.add_mem <;> solve_by_elim
#align prime_spectrum.sup_vanishing_ideal_le PrimeSpectrum.sup_vanishingIdeal_le

theorem mem_compl_zeroLocus_iff_not_mem {f : R} {I : PrimeSpectrum R} :
    I ∈ (zeroLocus {f} : Set (PrimeSpectrum R))ᶜ ↔ f ∉ I.asIdeal := by
  rw [Set.mem_compl_iff, mem_zeroLocus, Set.singleton_subset_iff]; rfl
#align prime_spectrum.mem_compl_zero_locus_iff_not_mem PrimeSpectrum.mem_compl_zeroLocus_iff_not_mem

/-- The Zariski topology on the prime spectrum of a commutative (semi)ring is defined
via the closed sets of the topology: they are exactly those sets that are the zero locus
of a subset of the ring. -/
instance zariskiTopology : TopologicalSpace (PrimeSpectrum R) :=
  TopologicalSpace.ofClosed (Set.range PrimeSpectrum.zeroLocus) ⟨Set.univ, by simp⟩
    (by
      intro Zs h
      rw [Set.sInter_eq_iInter]
      choose f hf using fun i : Zs => h i.prop
      simp only [← hf]
      exact ⟨_, zeroLocus_iUnion _⟩)
    (by
      rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
      exact ⟨_, (union_zeroLocus s t).symm⟩)
#align prime_spectrum.zariski_topology PrimeSpectrum.zariskiTopology

theorem isOpen_iff (U : Set (PrimeSpectrum R)) : IsOpen U ↔ ∃ s, Uᶜ = zeroLocus s := by
  simp only [@eq_comm _ Uᶜ]; rfl
#align prime_spectrum.is_open_iff PrimeSpectrum.isOpen_iff

theorem isClosed_iff_zeroLocus (Z : Set (PrimeSpectrum R)) : IsClosed Z ↔ ∃ s, Z = zeroLocus s := by
  rw [← isOpen_compl_iff, isOpen_iff, compl_compl]
#align prime_spectrum.is_closed_iff_zero_locus PrimeSpectrum.isClosed_iff_zeroLocus

theorem isClosed_iff_zeroLocus_ideal (Z : Set (PrimeSpectrum R)) :
    IsClosed Z ↔ ∃ I : Ideal R, Z = zeroLocus I :=
  (isClosed_iff_zeroLocus _).trans
    ⟨fun ⟨s, hs⟩ => ⟨_, (zeroLocus_span s).substr hs⟩, fun ⟨I, hI⟩ => ⟨I, hI⟩⟩
#align prime_spectrum.is_closed_iff_zero_locus_ideal PrimeSpectrum.isClosed_iff_zeroLocus_ideal

theorem isClosed_iff_zeroLocus_radical_ideal (Z : Set (PrimeSpectrum R)) :
    IsClosed Z ↔ ∃ I : Ideal R, I.IsRadical ∧ Z = zeroLocus I :=
  (isClosed_iff_zeroLocus_ideal _).trans
    ⟨fun ⟨I, hI⟩ => ⟨_, I.radical_isRadical, (zeroLocus_radical I).substr hI⟩, fun ⟨I, _, hI⟩ =>
      ⟨I, hI⟩⟩
#align prime_spectrum.is_closed_iff_zero_locus_radical_ideal PrimeSpectrum.isClosed_iff_zeroLocus_radical_ideal

theorem isClosed_zeroLocus (s : Set R) : IsClosed (zeroLocus s) := by
  rw [isClosed_iff_zeroLocus]
  exact ⟨s, rfl⟩
#align prime_spectrum.is_closed_zero_locus PrimeSpectrum.isClosed_zeroLocus

theorem zeroLocus_vanishingIdeal_eq_closure (t : Set (PrimeSpectrum R)) :
    zeroLocus (vanishingIdeal t : Set R) = closure t := by
  rcases isClosed_iff_zeroLocus (closure t) |>.mp isClosed_closure with ⟨I, hI⟩
  rw [subset_antisymm_iff, (isClosed_zeroLocus _).closure_subset_iff, hI,
      subset_zeroLocus_iff_subset_vanishingIdeal, (gc R).u_l_u_eq_u,
      ← subset_zeroLocus_iff_subset_vanishingIdeal, ← hI]
  exact ⟨subset_closure, subset_zeroLocus_vanishingIdeal t⟩
#align prime_spectrum.zero_locus_vanishing_ideal_eq_closure PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure

theorem vanishingIdeal_closure (t : Set (PrimeSpectrum R)) :
    vanishingIdeal (closure t) = vanishingIdeal t :=
  zeroLocus_vanishingIdeal_eq_closure t ▸ (gc R).u_l_u_eq_u t
#align prime_spectrum.vanishing_ideal_closure PrimeSpectrum.vanishingIdeal_closure

theorem closure_singleton (x) : closure ({x} : Set (PrimeSpectrum R)) = zeroLocus x.asIdeal := by
  rw [← zeroLocus_vanishingIdeal_eq_closure, vanishingIdeal_singleton]
#align prime_spectrum.closure_singleton PrimeSpectrum.closure_singleton

theorem isClosed_singleton_iff_isMaximal (x : PrimeSpectrum R) :
    IsClosed ({x} : Set (PrimeSpectrum R)) ↔ x.asIdeal.IsMaximal := by
  rw [← closure_subset_iff_isClosed, ← zeroLocus_vanishingIdeal_eq_closure,
      vanishingIdeal_singleton]
  constructor <;> intro H
  · rcases x.asIdeal.exists_le_maximal x.2.1 with ⟨m, hm, hxm⟩
    exact (congr_arg asIdeal (@H ⟨m, hm.isPrime⟩ hxm)) ▸ hm
  · exact fun p hp ↦ PrimeSpectrum.ext _ _ (H.eq_of_le p.2.1 hp).symm
#align prime_spectrum.is_closed_singleton_iff_is_maximal PrimeSpectrum.isClosed_singleton_iff_isMaximal

theorem isRadical_vanishingIdeal (s : Set (PrimeSpectrum R)) : (vanishingIdeal s).IsRadical := by
  rw [← vanishingIdeal_closure, ← zeroLocus_vanishingIdeal_eq_closure,
    vanishingIdeal_zeroLocus_eq_radical]
  apply Ideal.radical_isRadical
#align prime_spectrum.is_radical_vanishing_ideal PrimeSpectrum.isRadical_vanishingIdeal

theorem vanishingIdeal_anti_mono_iff {s t : Set (PrimeSpectrum R)} (ht : IsClosed t) :
    s ⊆ t ↔ vanishingIdeal t ≤ vanishingIdeal s :=
  ⟨vanishingIdeal_anti_mono, fun h => by
    rw [← ht.closure_subset_iff, ← ht.closure_eq]
    convert ← zeroLocus_anti_mono_ideal h <;> apply zeroLocus_vanishingIdeal_eq_closure⟩
#align prime_spectrum.vanishing_ideal_anti_mono_iff PrimeSpectrum.vanishingIdeal_anti_mono_iff

theorem vanishingIdeal_strict_anti_mono_iff {s t : Set (PrimeSpectrum R)} (hs : IsClosed s)
    (ht : IsClosed t) : s ⊂ t ↔ vanishingIdeal t < vanishingIdeal s := by
  rw [Set.ssubset_def, vanishingIdeal_anti_mono_iff hs, vanishingIdeal_anti_mono_iff ht,
    lt_iff_le_not_le]
#align prime_spectrum.vanishing_ideal_strict_anti_mono_iff PrimeSpectrum.vanishingIdeal_strict_anti_mono_iff

/-- The antitone order embedding of closed subsets of `Spec R` into ideals of `R`. -/
def closedsEmbedding (R : Type*) [CommSemiring R] :
    (TopologicalSpace.Closeds <| PrimeSpectrum R)ᵒᵈ ↪o Ideal R :=
  OrderEmbedding.ofMapLEIff (fun s => vanishingIdeal ↑(OrderDual.ofDual s)) fun s _ =>
    (vanishingIdeal_anti_mono_iff s.2).symm
#align prime_spectrum.closeds_embedding PrimeSpectrum.closedsEmbedding

theorem t1Space_iff_isField [IsDomain R] : T1Space (PrimeSpectrum R) ↔ IsField R := by
  refine ⟨?_, fun h => ?_⟩
  · intro h
    have hbot : Ideal.IsPrime (⊥ : Ideal R) := Ideal.bot_prime
    exact
      Classical.not_not.1
        (mt
          (Ring.ne_bot_of_isMaximal_of_not_isField <|
            (isClosed_singleton_iff_isMaximal _).1 (T1Space.t1 ⟨⊥, hbot⟩))
          (by aesop))
  · refine ⟨fun x => (isClosed_singleton_iff_isMaximal x).2 ?_⟩
    by_cases hx : x.asIdeal = ⊥
    · letI := h.toSemifield
      exact hx.symm ▸ Ideal.bot_isMaximal
    · exact absurd h (Ring.not_isField_iff_exists_prime.2 ⟨x.asIdeal, ⟨hx, x.2⟩⟩)
#align prime_spectrum.t1_space_iff_is_field PrimeSpectrum.t1Space_iff_isField

local notation "Z(" a ")" => zeroLocus (a : Set R)

theorem isIrreducible_zeroLocus_iff_of_radical (I : Ideal R) (hI : I.IsRadical) :
    IsIrreducible (zeroLocus (I : Set R)) ↔ I.IsPrime := by
  rw [Ideal.isPrime_iff, IsIrreducible]
  apply and_congr
  · rw [Set.nonempty_iff_ne_empty, Ne, zeroLocus_empty_iff_eq_top]
  · trans ∀ x y : Ideal R, Z(I) ⊆ Z(x) ∪ Z(y) → Z(I) ⊆ Z(x) ∨ Z(I) ⊆ Z(y)
    · simp_rw [isPreirreducible_iff_closed_union_closed, isClosed_iff_zeroLocus_ideal]
      constructor
      · rintro h x y
        exact h _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
      · rintro h _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact h x y
    · simp_rw [← zeroLocus_inf, subset_zeroLocus_iff_le_vanishingIdeal,
        vanishingIdeal_zeroLocus_eq_radical, hI.radical]
      constructor
      · simp_rw [← SetLike.mem_coe, ← Set.singleton_subset_iff, ← Ideal.span_le, ←
          Ideal.span_singleton_mul_span_singleton]
        refine fun h x y h' => h _ _ ?_
        rw [← hI.radical_le_iff] at h' ⊢
        simpa only [Ideal.radical_inf, Ideal.radical_mul] using h'
      · simp_rw [or_iff_not_imp_left, SetLike.not_le_iff_exists]
        rintro h s t h' ⟨x, hx, hx'⟩ y hy
        exact h (h' ⟨Ideal.mul_mem_right _ _ hx, Ideal.mul_mem_left _ _ hy⟩) hx'
#align prime_spectrum.is_irreducible_zero_locus_iff_of_radical PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical

theorem isIrreducible_zeroLocus_iff (I : Ideal R) :
    IsIrreducible (zeroLocus (I : Set R)) ↔ I.radical.IsPrime :=
  zeroLocus_radical I ▸ isIrreducible_zeroLocus_iff_of_radical _ I.radical_isRadical
#align prime_spectrum.is_irreducible_zero_locus_iff PrimeSpectrum.isIrreducible_zeroLocus_iff

theorem isIrreducible_iff_vanishingIdeal_isPrime {s : Set (PrimeSpectrum R)} :
    IsIrreducible s ↔ (vanishingIdeal s).IsPrime := by
  rw [← isIrreducible_iff_closure, ← zeroLocus_vanishingIdeal_eq_closure,
    isIrreducible_zeroLocus_iff_of_radical _ (isRadical_vanishingIdeal s)]
#align prime_spectrum.is_irreducible_iff_vanishing_ideal_is_prime PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime

lemma vanishingIdeal_isIrreducible :
    vanishingIdeal (R := R) '' {s | IsIrreducible s} = {P | P.IsPrime} :=
  Set.ext fun I ↦ ⟨fun ⟨_, hs, e⟩ ↦ e ▸ isIrreducible_iff_vanishingIdeal_isPrime.mp hs,
    fun h ↦ ⟨zeroLocus I, (isIrreducible_zeroLocus_iff_of_radical _ h.isRadical).mpr h,
      (vanishingIdeal_zeroLocus_eq_radical I).trans h.radical⟩⟩

lemma vanishingIdeal_isClosed_isIrreducible :
    vanishingIdeal (R := R) '' {s | IsClosed s ∧ IsIrreducible s} = {P | P.IsPrime} := by
  refine (subset_antisymm ?_ ?_).trans vanishingIdeal_isIrreducible
  · exact Set.image_subset _ fun _ ↦ And.right
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨closure s, ⟨isClosed_closure, hs.closure⟩, vanishingIdeal_closure s⟩

instance irreducibleSpace [IsDomain R] : IrreducibleSpace (PrimeSpectrum R) := by
  rw [irreducibleSpace_def, Set.top_eq_univ, ← zeroLocus_bot, isIrreducible_zeroLocus_iff]
  simpa using Ideal.bot_prime

instance quasiSober : QuasiSober (PrimeSpectrum R) :=
  ⟨fun {S} h₁ h₂ =>
    ⟨⟨_, isIrreducible_iff_vanishingIdeal_isPrime.1 h₁⟩, by
      rw [IsGenericPoint, closure_singleton, zeroLocus_vanishingIdeal_eq_closure, h₂.closure_eq]⟩⟩

/-- The prime spectrum of a commutative (semi)ring is a compact topological space. -/
instance compactSpace : CompactSpace (PrimeSpectrum R) := by
  refine compactSpace_of_finite_subfamily_closed fun S S_closed S_empty ↦ ?_
  choose I hI using fun i ↦ (isClosed_iff_zeroLocus_ideal (S i)).mp (S_closed i)
  simp_rw [hI, ← zeroLocus_iSup, zeroLocus_empty_iff_eq_top, ← top_le_iff] at S_empty ⊢
  exact Ideal.isCompactElement_top.exists_finset_of_le_iSup _ _ S_empty

section Comap

variable {S' : Type*} [CommSemiring S']

theorem preimage_comap_zeroLocus_aux (f : R →+* S) (s : Set R) :
    (fun y => ⟨Ideal.comap f y.asIdeal, inferInstance⟩ : PrimeSpectrum S → PrimeSpectrum R) ⁻¹'
        zeroLocus s =
      zeroLocus (f '' s) := by
  ext x
  simp only [mem_zeroLocus, Set.image_subset_iff, Set.mem_preimage, mem_zeroLocus, Ideal.coe_comap]
#align prime_spectrum.preimage_comap_zero_locus_aux PrimeSpectrum.preimage_comap_zeroLocus_aux

/-- The function between prime spectra of commutative (semi)rings induced by a ring homomorphism.
This function is continuous. -/
def comap (f : R →+* S) : C(PrimeSpectrum S, PrimeSpectrum R) where
  toFun y := ⟨Ideal.comap f y.asIdeal, inferInstance⟩
  continuous_toFun := by
    simp only [continuous_iff_isClosed, isClosed_iff_zeroLocus]
    rintro _ ⟨s, rfl⟩
    exact ⟨_, preimage_comap_zeroLocus_aux f s⟩
#align prime_spectrum.comap PrimeSpectrum.comap

variable (f : R →+* S)

@[simp]
theorem comap_asIdeal (y : PrimeSpectrum S) : (comap f y).asIdeal = Ideal.comap f y.asIdeal :=
  rfl
#align prime_spectrum.comap_as_ideal PrimeSpectrum.comap_asIdeal

@[simp]
theorem comap_id : comap (RingHom.id R) = ContinuousMap.id _ := by
  ext
  rfl
#align prime_spectrum.comap_id PrimeSpectrum.comap_id

@[simp]
theorem comap_comp (f : R →+* S) (g : S →+* S') : comap (g.comp f) = (comap f).comp (comap g) :=
  rfl
#align prime_spectrum.comap_comp PrimeSpectrum.comap_comp

theorem comap_comp_apply (f : R →+* S) (g : S →+* S') (x : PrimeSpectrum S') :
    PrimeSpectrum.comap (g.comp f) x = (PrimeSpectrum.comap f) (PrimeSpectrum.comap g x) :=
  rfl
#align prime_spectrum.comap_comp_apply PrimeSpectrum.comap_comp_apply

@[simp]
theorem preimage_comap_zeroLocus (s : Set R) : comap f ⁻¹' zeroLocus s = zeroLocus (f '' s) :=
  preimage_comap_zeroLocus_aux f s
#align prime_spectrum.preimage_comap_zero_locus PrimeSpectrum.preimage_comap_zeroLocus

theorem comap_injective_of_surjective (f : R →+* S) (hf : Function.Surjective f) :
    Function.Injective (comap f) := fun x y h =>
  PrimeSpectrum.ext _ _
    (Ideal.comap_injective_of_surjective f hf
      (congr_arg PrimeSpectrum.asIdeal h : (comap f x).asIdeal = (comap f y).asIdeal))
#align prime_spectrum.comap_injective_of_surjective PrimeSpectrum.comap_injective_of_surjective

variable (S)

theorem localization_comap_inducing [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    Inducing (comap (algebraMap R S)) := by
  refine ⟨TopologicalSpace.ext_isClosed fun Z ↦ ?_⟩
  simp_rw [isClosed_induced_iff, isClosed_iff_zeroLocus, @eq_comm _ _ (zeroLocus _),
    exists_exists_eq_and, preimage_comap_zeroLocus]
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨(Ideal.span s).comap (algebraMap R S), ?_⟩
    rw [← zeroLocus_span, ← zeroLocus_span s, ← Ideal.map, IsLocalization.map_comap M S]
  · rintro ⟨s, rfl⟩
    exact ⟨_, rfl⟩
#align prime_spectrum.localization_comap_inducing PrimeSpectrum.localization_comap_inducing

theorem localization_comap_injective [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    Function.Injective (comap (algebraMap R S)) := by
  intro p q h
  replace h := congr_arg (fun x : PrimeSpectrum R => Ideal.map (algebraMap R S) x.asIdeal) h
  dsimp only [comap, ContinuousMap.coe_mk] at h
  rw [IsLocalization.map_comap M S, IsLocalization.map_comap M S] at h
  ext1
  exact h
#align prime_spectrum.localization_comap_injective PrimeSpectrum.localization_comap_injective

theorem localization_comap_embedding [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    Embedding (comap (algebraMap R S)) :=
  ⟨localization_comap_inducing S M, localization_comap_injective S M⟩
#align prime_spectrum.localization_comap_embedding PrimeSpectrum.localization_comap_embedding

theorem localization_comap_range [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    Set.range (comap (algebraMap R S)) = { p | Disjoint (M : Set R) p.asIdeal } := by
  ext x
  constructor
  · simp_rw [disjoint_iff_inf_le]
    rintro ⟨p, rfl⟩ x ⟨hx₁, hx₂⟩
    exact (p.2.1 : ¬_) (p.asIdeal.eq_top_of_isUnit_mem hx₂ (IsLocalization.map_units S ⟨x, hx₁⟩))
  · intro h
    use ⟨x.asIdeal.map (algebraMap R S), IsLocalization.isPrime_of_isPrime_disjoint M S _ x.2 h⟩
    ext1
    exact IsLocalization.comap_map_of_isPrime_disjoint M S _ x.2 h
#align prime_spectrum.localization_comap_range PrimeSpectrum.localization_comap_range

open Function RingHom

theorem comap_inducing_of_surjective (hf : Surjective f) : Inducing (comap f) where
  induced := by
    set_option tactic.skipAssignedInstances false in
    simp_rw [TopologicalSpace.ext_iff, ← isClosed_compl_iff,
      ← @isClosed_compl_iff (PrimeSpectrum S)
        ((TopologicalSpace.induced (comap f) zariskiTopology)), isClosed_induced_iff,
      isClosed_iff_zeroLocus]
    refine fun s =>
      ⟨fun ⟨F, hF⟩ =>
        ⟨zeroLocus (f ⁻¹' F), ⟨f ⁻¹' F, rfl⟩, by
          rw [preimage_comap_zeroLocus, Function.Surjective.image_preimage hf, hF]⟩,
        ?_⟩
    rintro ⟨-, ⟨F, rfl⟩, hF⟩
    exact ⟨f '' F, hF.symm.trans (preimage_comap_zeroLocus f F)⟩
#align prime_spectrum.comap_inducing_of_surjective PrimeSpectrum.comap_inducing_of_surjective


end Comap
end CommSemiRing

section SpecOfSurjective

/-! The comap of a surjective ring homomorphism is a closed embedding between the prime spectra. -/


open Function RingHom

variable [CommRing R] [CommRing S]
variable (f : R →+* S)
variable {R}

theorem comap_singleton_isClosed_of_surjective (f : R →+* S) (hf : Function.Surjective f)
    (x : PrimeSpectrum S) (hx : IsClosed ({x} : Set (PrimeSpectrum S))) :
    IsClosed ({comap f x} : Set (PrimeSpectrum R)) :=
  haveI : x.asIdeal.IsMaximal := (isClosed_singleton_iff_isMaximal x).1 hx
  (isClosed_singleton_iff_isMaximal _).2 (Ideal.comap_isMaximal_of_surjective f hf)
#align prime_spectrum.comap_singleton_is_closed_of_surjective PrimeSpectrum.comap_singleton_isClosed_of_surjective

theorem comap_singleton_isClosed_of_isIntegral (f : R →+* S) (hf : f.IsIntegral)
    (x : PrimeSpectrum S) (hx : IsClosed ({x} : Set (PrimeSpectrum S))) :
    IsClosed ({comap f x} : Set (PrimeSpectrum R)) :=
  have := (isClosed_singleton_iff_isMaximal x).1 hx
  (isClosed_singleton_iff_isMaximal _).2
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hf x.asIdeal)
#align prime_spectrum.comap_singleton_is_closed_of_is_integral PrimeSpectrum.comap_singleton_isClosed_of_isIntegral

theorem image_comap_zeroLocus_eq_zeroLocus_comap (hf : Surjective f) (I : Ideal S) :
    comap f '' zeroLocus I = zeroLocus (I.comap f) := by
  simp only [Set.ext_iff, Set.mem_image, mem_zeroLocus, SetLike.coe_subset_coe]
  refine fun p => ⟨?_, fun h_I_p => ?_⟩
  · rintro ⟨p, hp, rfl⟩ a ha
    exact hp ha
  · have hp : ker f ≤ p.asIdeal := (Ideal.comap_mono bot_le).trans h_I_p
    refine ⟨⟨p.asIdeal.map f, Ideal.map_isPrime_of_surjective hf hp⟩, fun x hx => ?_, ?_⟩
    · obtain ⟨x', rfl⟩ := hf x
      exact Ideal.mem_map_of_mem f (h_I_p hx)
    · ext x
      rw [comap_asIdeal, Ideal.mem_comap, Ideal.mem_map_iff_of_surjective f hf]
      refine ⟨?_, fun hx => ⟨x, hx, rfl⟩⟩
      rintro ⟨x', hx', heq⟩
      rw [← sub_sub_cancel x' x]
      refine p.asIdeal.sub_mem hx' (hp ?_)
      rwa [mem_ker, map_sub, sub_eq_zero]
#align prime_spectrum.image_comap_zero_locus_eq_zero_locus_comap PrimeSpectrum.image_comap_zeroLocus_eq_zeroLocus_comap

theorem range_comap_of_surjective (hf : Surjective f) :
    Set.range (comap f) = zeroLocus (ker f) := by
  rw [← Set.image_univ]
  convert image_comap_zeroLocus_eq_zeroLocus_comap _ _ hf _
  rw [zeroLocus_bot]
#align prime_spectrum.range_comap_of_surjective PrimeSpectrum.range_comap_of_surjective

theorem isClosed_range_comap_of_surjective (hf : Surjective f) :
    IsClosed (Set.range (comap f)) := by
  rw [range_comap_of_surjective _ f hf]
  exact isClosed_zeroLocus _
#align prime_spectrum.is_closed_range_comap_of_surjective PrimeSpectrum.isClosed_range_comap_of_surjective

theorem closedEmbedding_comap_of_surjective (hf : Surjective f) : ClosedEmbedding (comap f) :=
  { induced := (comap_inducing_of_surjective S f hf).induced
    inj := comap_injective_of_surjective f hf
    isClosed_range := isClosed_range_comap_of_surjective S f hf }
#align prime_spectrum.closed_embedding_comap_of_surjective PrimeSpectrum.closedEmbedding_comap_of_surjective

end SpecOfSurjective

section CommSemiRing

variable [CommSemiring R] [CommSemiring S]
variable {R S}

section BasicOpen

/-- `basicOpen r` is the open subset containing all prime ideals not containing `r`. -/
def basicOpen (r : R) : TopologicalSpace.Opens (PrimeSpectrum R) where
  carrier := { x | r ∉ x.asIdeal }
  is_open' := ⟨{r}, Set.ext fun _ => Set.singleton_subset_iff.trans <| Classical.not_not.symm⟩
#align prime_spectrum.basic_open PrimeSpectrum.basicOpen

@[simp]
theorem mem_basicOpen (f : R) (x : PrimeSpectrum R) : x ∈ basicOpen f ↔ f ∉ x.asIdeal :=
  Iff.rfl
#align prime_spectrum.mem_basic_open PrimeSpectrum.mem_basicOpen

theorem isOpen_basicOpen {a : R} : IsOpen (basicOpen a : Set (PrimeSpectrum R)) :=
  (basicOpen a).isOpen
#align prime_spectrum.is_open_basic_open PrimeSpectrum.isOpen_basicOpen

@[simp]
theorem basicOpen_eq_zeroLocus_compl (r : R) :
    (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ :=
  Set.ext fun x => by simp only [SetLike.mem_coe, mem_basicOpen, Set.mem_compl_iff, mem_zeroLocus,
    Set.singleton_subset_iff]
#align prime_spectrum.basic_open_eq_zero_locus_compl PrimeSpectrum.basicOpen_eq_zeroLocus_compl

@[simp]
theorem basicOpen_one : basicOpen (1 : R) = ⊤ :=
  TopologicalSpace.Opens.ext <| by simp
#align prime_spectrum.basic_open_one PrimeSpectrum.basicOpen_one

@[simp]
theorem basicOpen_zero : basicOpen (0 : R) = ⊥ :=
  TopologicalSpace.Opens.ext <| by simp
#align prime_spectrum.basic_open_zero PrimeSpectrum.basicOpen_zero

theorem basicOpen_le_basicOpen_iff (f g : R) :
    basicOpen f ≤ basicOpen g ↔ f ∈ (Ideal.span ({g} : Set R)).radical := by
  rw [← SetLike.coe_subset_coe, basicOpen_eq_zeroLocus_compl, basicOpen_eq_zeroLocus_compl,
    Set.compl_subset_compl, zeroLocus_subset_zeroLocus_singleton_iff]
#align prime_spectrum.basic_open_le_basic_open_iff PrimeSpectrum.basicOpen_le_basicOpen_iff

theorem basicOpen_mul (f g : R) : basicOpen (f * g) = basicOpen f ⊓ basicOpen g :=
  TopologicalSpace.Opens.ext <| by simp [zeroLocus_singleton_mul]
#align prime_spectrum.basic_open_mul PrimeSpectrum.basicOpen_mul

theorem basicOpen_mul_le_left (f g : R) : basicOpen (f * g) ≤ basicOpen f := by
  rw [basicOpen_mul f g]
  exact inf_le_left
#align prime_spectrum.basic_open_mul_le_left PrimeSpectrum.basicOpen_mul_le_left

theorem basicOpen_mul_le_right (f g : R) : basicOpen (f * g) ≤ basicOpen g := by
  rw [basicOpen_mul f g]
  exact inf_le_right
#align prime_spectrum.basic_open_mul_le_right PrimeSpectrum.basicOpen_mul_le_right

@[simp]
theorem basicOpen_pow (f : R) (n : ℕ) (hn : 0 < n) : basicOpen (f ^ n) = basicOpen f :=
  TopologicalSpace.Opens.ext <| by simpa using zeroLocus_singleton_pow f n hn
#align prime_spectrum.basic_open_pow PrimeSpectrum.basicOpen_pow

theorem isTopologicalBasis_basic_opens :
    TopologicalSpace.IsTopologicalBasis
      (Set.range fun r : R => (basicOpen r : Set (PrimeSpectrum R))) := by
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨r, rfl⟩
    exact isOpen_basicOpen
  · rintro p U hp ⟨s, hs⟩
    rw [← compl_compl U, Set.mem_compl_iff, ← hs, mem_zeroLocus, Set.not_subset] at hp
    obtain ⟨f, hfs, hfp⟩ := hp
    refine ⟨basicOpen f, ⟨f, rfl⟩, hfp, ?_⟩
    rw [← Set.compl_subset_compl, ← hs, basicOpen_eq_zeroLocus_compl, compl_compl]
    exact zeroLocus_anti_mono (Set.singleton_subset_iff.mpr hfs)
#align prime_spectrum.is_topological_basis_basic_opens PrimeSpectrum.isTopologicalBasis_basic_opens

theorem isBasis_basic_opens : TopologicalSpace.Opens.IsBasis (Set.range (@basicOpen R _)) := by
  unfold TopologicalSpace.Opens.IsBasis
  convert isTopologicalBasis_basic_opens (R := R)
  rw [← Set.range_comp]
  rfl
#align prime_spectrum.is_basis_basic_opens PrimeSpectrum.isBasis_basic_opens

@[simp]
theorem basicOpen_eq_bot_iff (f : R) : basicOpen f = ⊥ ↔ IsNilpotent f := by
  rw [← TopologicalSpace.Opens.coe_inj, basicOpen_eq_zeroLocus_compl]
  simp only [Set.eq_univ_iff_forall, Set.singleton_subset_iff, TopologicalSpace.Opens.coe_bot,
    nilpotent_iff_mem_prime, Set.compl_empty_iff, mem_zeroLocus, SetLike.mem_coe]
  exact ⟨fun h I hI => h ⟨I, hI⟩, fun h ⟨I, hI⟩ => h I hI⟩
#align prime_spectrum.basic_open_eq_bot_iff PrimeSpectrum.basicOpen_eq_bot_iff

theorem localization_away_comap_range (S : Type v) [CommSemiring S] [Algebra R S] (r : R)
    [IsLocalization.Away r S] : Set.range (comap (algebraMap R S)) = basicOpen r := by
  rw [localization_comap_range S (Submonoid.powers r)]
  ext x
  simp only [mem_zeroLocus, basicOpen_eq_zeroLocus_compl, SetLike.mem_coe, Set.mem_setOf_eq,
    Set.singleton_subset_iff, Set.mem_compl_iff, disjoint_iff_inf_le]
  constructor
  · intro h₁ h₂
    exact h₁ ⟨Submonoid.mem_powers r, h₂⟩
  · rintro h₁ _ ⟨⟨n, rfl⟩, h₃⟩
    exact h₁ (x.2.mem_of_pow_mem _ h₃)
#align prime_spectrum.localization_away_comap_range PrimeSpectrum.localization_away_comap_range

theorem localization_away_openEmbedding (S : Type v) [CommSemiring S] [Algebra R S] (r : R)
    [IsLocalization.Away r S] : OpenEmbedding (comap (algebraMap R S)) :=
  { toEmbedding := localization_comap_embedding S (Submonoid.powers r)
    isOpen_range := by
      rw [localization_away_comap_range S r]
      exact isOpen_basicOpen }
#align prime_spectrum.localization_away_open_embedding PrimeSpectrum.localization_away_openEmbedding

theorem isCompact_basicOpen (f : R) : IsCompact (basicOpen f : Set (PrimeSpectrum R)) := by
  rw [← localization_away_comap_range (Localization (Submonoid.powers f))]
  exact isCompact_range (map_continuous _)
#align prime_spectrum.is_compact_basic_open PrimeSpectrum.isCompact_basicOpen

lemma comap_basicOpen (f : R →+* S) (x : R) :
    TopologicalSpace.Opens.comap (comap f) (basicOpen x) = basicOpen (f x) :=
  rfl

end BasicOpen

section Order

/-!
## The specialization order

We endow `PrimeSpectrum R` with a partial order, where `x ≤ y` if and only if `y ∈ closure {x}`.
-/


instance : PartialOrder (PrimeSpectrum R) :=
  PartialOrder.lift asIdeal (PrimeSpectrum.ext)

@[simp]
theorem asIdeal_le_asIdeal (x y : PrimeSpectrum R) : x.asIdeal ≤ y.asIdeal ↔ x ≤ y :=
  Iff.rfl
#align prime_spectrum.as_ideal_le_as_ideal PrimeSpectrum.asIdeal_le_asIdeal

@[simp]
theorem asIdeal_lt_asIdeal (x y : PrimeSpectrum R) : x.asIdeal < y.asIdeal ↔ x < y :=
  Iff.rfl
#align prime_spectrum.as_ideal_lt_as_ideal PrimeSpectrum.asIdeal_lt_asIdeal

theorem le_iff_mem_closure (x y : PrimeSpectrum R) :
    x ≤ y ↔ y ∈ closure ({x} : Set (PrimeSpectrum R)) := by
  rw [← asIdeal_le_asIdeal, ← zeroLocus_vanishingIdeal_eq_closure, mem_zeroLocus,
    vanishingIdeal_singleton, SetLike.coe_subset_coe]
#align prime_spectrum.le_iff_mem_closure PrimeSpectrum.le_iff_mem_closure

theorem le_iff_specializes (x y : PrimeSpectrum R) : x ≤ y ↔ x ⤳ y :=
  (le_iff_mem_closure x y).trans specializes_iff_mem_closure.symm
#align prime_spectrum.le_iff_specializes PrimeSpectrum.le_iff_specializes

/-- `nhds` as an order embedding. -/
@[simps!]
def nhdsOrderEmbedding : PrimeSpectrum R ↪o Filter (PrimeSpectrum R) :=
  OrderEmbedding.ofMapLEIff nhds fun a b => (le_iff_specializes a b).symm
#align prime_spectrum.nhds_order_embedding PrimeSpectrum.nhdsOrderEmbedding

instance : T0Space (PrimeSpectrum R) :=
  ⟨nhdsOrderEmbedding.inj'⟩

instance [IsDomain R] : OrderBot (PrimeSpectrum R) where
  bot := ⟨⊥, Ideal.bot_prime⟩
  bot_le I := @bot_le _ _ _ I.asIdeal

instance {R : Type*} [Field R] : Unique (PrimeSpectrum R) where
  default := ⊥
  uniq x := PrimeSpectrum.ext _ _ ((IsSimpleOrder.eq_bot_or_eq_top _).resolve_right x.2.ne_top)

end Order

/-- If `x` specializes to `y`, then there is a natural map from the localization of `y` to the
localization of `x`. -/
def localizationMapOfSpecializes {x y : PrimeSpectrum R} (h : x ⤳ y) :
    Localization.AtPrime y.asIdeal →+* Localization.AtPrime x.asIdeal :=
  @IsLocalization.lift _ _ _ _ _ _ _ _ Localization.isLocalization
    (algebraMap R (Localization.AtPrime x.asIdeal))
    (by
      rintro ⟨a, ha⟩
      rw [← PrimeSpectrum.le_iff_specializes, ← asIdeal_le_asIdeal, ← SetLike.coe_subset_coe, ←
        Set.compl_subset_compl] at h
      exact (IsLocalization.map_units (Localization.AtPrime x.asIdeal)
        ⟨a, show a ∈ x.asIdeal.primeCompl from h ha⟩ : _))
#align prime_spectrum.localization_map_of_specializes PrimeSpectrum.localizationMapOfSpecializes

variable (R) in
/--
Zero loci of prime ideals are closed irreducible sets in the Zariski topology and any closed
irreducible set is a zero locus of some prime ideal.
-/
protected def pointsEquivIrreducibleCloseds :
    PrimeSpectrum R ≃o {s : Set (PrimeSpectrum R) | IsIrreducible s ∧ IsClosed s}ᵒᵈ where
  __ := irreducibleSetEquivPoints.toEquiv.symm.trans OrderDual.toDual
  map_rel_iff' {p q} :=
    (RelIso.symm irreducibleSetEquivPoints).map_rel_iff.trans (le_iff_specializes p q).symm

section LocalizationAtMinimal

variable {I : Ideal R} [hI : I.IsPrime]

/--
Localizations at minimal primes have single-point prime spectra.
-/
def primeSpectrum_unique_of_localization_at_minimal (h : I ∈ minimalPrimes R) :
    Unique (PrimeSpectrum (Localization.AtPrime I)) where
  default :=
    ⟨LocalRing.maximalIdeal (Localization I.primeCompl),
    (LocalRing.maximalIdeal.isMaximal _).isPrime⟩
  uniq x := PrimeSpectrum.ext _ _ (Localization.AtPrime.prime_unique_of_minimal h x.asIdeal)

end LocalizationAtMinimal

end CommSemiRing

end PrimeSpectrum

section CommSemiring
variable [CommSemiring R]

open PrimeSpectrum in
/--
[Stacks: Lemma 00ES (3)](https://stacks.math.columbia.edu/tag/00ES)
Zero loci of minimal prime ideals of `R` are irreducible components in `Spec R` and any
irreducible component is a zero locus of some minimal prime ideal.
-/
protected def minimalPrimes.equivIrreducibleComponents :
    minimalPrimes R ≃o (irreducibleComponents <| PrimeSpectrum R)ᵒᵈ :=
  let e : {p : Ideal R | p.IsPrime ∧ ⊥ ≤ p} ≃o PrimeSpectrum R :=
    ⟨⟨fun x ↦ ⟨x.1, x.2.1⟩, fun x ↦ ⟨x.1, x.2, bot_le⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩, Iff.rfl⟩
  (e.trans <| PrimeSpectrum.pointsEquivIrreducibleCloseds R).minimalsIsoMaximals.trans
    (OrderIso.setCongr _ _ <| by simp_rw [irreducibleComponents_eq_maximals_closed, and_comm]).dual

namespace PrimeSpectrum

lemma vanishingIdeal_irreducibleComponents :
    vanishingIdeal '' (irreducibleComponents <| PrimeSpectrum R) =
    minimalPrimes R := by
  rw [irreducibleComponents_eq_maximals_closed, minimalPrimes_eq_minimals, ← minimals_swap,
    ← PrimeSpectrum.vanishingIdeal_isClosed_isIrreducible, image_minimals_of_rel_iff_rel]
  exact fun s t hs _ ↦ vanishingIdeal_anti_mono_iff hs.1

lemma zeroLocus_minimalPrimes :
    zeroLocus ∘ (↑) '' minimalPrimes R =
    irreducibleComponents (PrimeSpectrum R) := by
  rw [← vanishingIdeal_irreducibleComponents, ← Set.image_comp, Set.EqOn.image_eq_self]
  intros s hs
  simpa [zeroLocus_vanishingIdeal_eq_closure, closure_eq_iff_isClosed]
    using isClosed_of_mem_irreducibleComponents s hs

variable {R}

lemma vanishingIdeal_mem_minimalPrimes {s : Set (PrimeSpectrum R)} :
    vanishingIdeal s ∈ minimalPrimes R ↔ closure s ∈ irreducibleComponents (PrimeSpectrum R) := by
  constructor
  · rw [← zeroLocus_minimalPrimes, ← zeroLocus_vanishingIdeal_eq_closure]
    exact Set.mem_image_of_mem _
  · rw [← vanishingIdeal_irreducibleComponents, ← vanishingIdeal_closure]
    exact Set.mem_image_of_mem _

lemma zeroLocus_ideal_mem_irreducibleComponents {I : Ideal R} :
    zeroLocus I ∈ irreducibleComponents (PrimeSpectrum R) ↔ I.radical ∈ minimalPrimes R := by
  rw [← vanishingIdeal_zeroLocus_eq_radical]
  conv_lhs => rw [← (isClosed_zeroLocus _).closure_eq]
  exact vanishingIdeal_mem_minimalPrimes.symm

end PrimeSpectrum

end CommSemiring

namespace LocalRing

variable [CommSemiring R] [LocalRing R]

/-- The closed point in the prime spectrum of a local ring. -/
def closedPoint : PrimeSpectrum R :=
  ⟨maximalIdeal R, (maximalIdeal.isMaximal R).isPrime⟩
#align local_ring.closed_point LocalRing.closedPoint

variable {R}

theorem isLocalRingHom_iff_comap_closedPoint {S : Type v} [CommSemiring S] [LocalRing S]
    (f : R →+* S) : IsLocalRingHom f ↔ PrimeSpectrum.comap f (closedPoint S) = closedPoint R := by
  -- Porting note: inline `this` does **not** work
  have := (local_hom_TFAE f).out 0 4
  rw [this, PrimeSpectrum.ext_iff]
  rfl
#align local_ring.is_local_ring_hom_iff_comap_closed_point LocalRing.isLocalRingHom_iff_comap_closedPoint

@[simp]
theorem comap_closedPoint {S : Type v} [CommSemiring S] [LocalRing S] (f : R →+* S)
    [IsLocalRingHom f] : PrimeSpectrum.comap f (closedPoint S) = closedPoint R :=
  (isLocalRingHom_iff_comap_closedPoint f).mp inferInstance
#align local_ring.comap_closed_point LocalRing.comap_closedPoint

theorem specializes_closedPoint (x : PrimeSpectrum R) : x ⤳ closedPoint R :=
  (PrimeSpectrum.le_iff_specializes _ _).mp (LocalRing.le_maximalIdeal x.2.1)
#align local_ring.specializes_closed_point LocalRing.specializes_closedPoint

theorem closedPoint_mem_iff (U : TopologicalSpace.Opens <| PrimeSpectrum R) :
    closedPoint R ∈ U ↔ U = ⊤ := by
  constructor
  · rw [eq_top_iff]
    exact fun h x _ => (specializes_closedPoint x).mem_open U.2 h
  · rintro rfl
    trivial
#align local_ring.closed_point_mem_iff LocalRing.closedPoint_mem_iff

@[simp]
theorem PrimeSpectrum.comap_residue (T : Type u) [CommRing T] [LocalRing T]
    (x : PrimeSpectrum (ResidueField T)) : PrimeSpectrum.comap (residue T) x = closedPoint T := by
  rw [Subsingleton.elim x ⊥]
  ext1
  exact Ideal.mk_ker
#align local_ring.prime_spectrum.comap_residue LocalRing.PrimeSpectrum.comap_residue

end LocalRing
