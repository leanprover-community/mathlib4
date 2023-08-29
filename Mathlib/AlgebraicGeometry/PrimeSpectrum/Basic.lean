/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.LinearAlgebra.Finsupp
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Prod
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Nilpotent
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.Sober

#align_import algebraic_geometry.prime_spectrum.basic from "leanprover-community/mathlib"@"a7c017d750512a352b623b1824d75da5998457d0"

/-!
# Prime spectrum of a commutative ring

The prime spectrum of a commutative ring is the type of all prime ideals.
It is naturally endowed with a topology: the Zariski topology.

(It is also naturally endowed with a sheaf of rings,
which is constructed in `AlgebraicGeometry.StructureSheaf`.)

## Main definitions

* `PrimeSpectrum R`: The prime spectrum of a commutative ring `R`,
  i.e., the set of all prime ideals of `R`.
* `zeroLocus s`: The zero locus of a subset `s` of `R`
  is the subset of `PrimeSpectrum R` consisting of all prime ideals that contain `s`.
* `vanishingIdeal t`: The vanishing ideal of a subset `t` of `PrimeSpectrum R`
  is the intersection of points in `t` (viewed as prime ideals).

## Conventions

We denote subsets of rings with `s`, `s'`, etc...
whereas we denote subsets of prime spectra with `t`, `t'`, etc...

## Inspiration/contributors

The contents of this file draw inspiration from <https://github.com/ramonfmir/lean-scheme>
which has contributions from Ramon Fernandez Mir, Kevin Buzzard, Kenny Lau,
and Chris Hughes (on an earlier repository).
-/


noncomputable section

open Classical

universe u v

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S]

/-- The prime spectrum of a commutative ring `R` is the type of all prime ideals of `R`.

It is naturally endowed with a topology (the Zariski topology),
and a sheaf of commutative rings (see `AlgebraicGeometry.StructureSheaf`).
It is a fundamental building block in algebraic geometry. -/
@[ext]
structure PrimeSpectrum where
  asIdeal : Ideal R
  IsPrime : asIdeal.IsPrime
#align prime_spectrum PrimeSpectrum

attribute [instance] PrimeSpectrum.IsPrime

namespace PrimeSpectrum

variable {R S}

instance [Nontrivial R] : Nonempty <| PrimeSpectrum R :=
  let ⟨I, hI⟩ := Ideal.exists_maximal R
  ⟨⟨I, hI.isPrime⟩⟩

/-- The prime spectrum of the zero ring is empty. -/
theorem punit (x : PrimeSpectrum PUnit) : False :=
  x.1.ne_top_iff_one.1 x.2.1 <| Eq.substr (Subsingleton.elim 1 (0 : PUnit)) x.1.zero_mem
#align prime_spectrum.punit PrimeSpectrum.punit

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
        -- ⊢ Function.Injective (primeSpectrumProdOfSum R S)
        · rintro (⟨I, hI⟩ | ⟨J, hJ⟩) (⟨I', hI'⟩ | ⟨J', hJ'⟩) h <;>
          simp only [mk.injEq, Ideal.prod.ext_iff, primeSpectrumProdOfSum] at h
          -- ⊢ Sum.inl { asIdeal := I, IsPrime := hI } = Sum.inl { asIdeal := I', IsPrime : …
          -- ⊢ Sum.inl { asIdeal := I, IsPrime := hI } = Sum.inr { asIdeal := J', IsPrime : …
          -- ⊢ Sum.inr { asIdeal := J, IsPrime := hJ } = Sum.inl { asIdeal := I', IsPrime : …
          -- ⊢ Sum.inr { asIdeal := J, IsPrime := hJ } = Sum.inr { asIdeal := J', IsPrime : …
          · simp only [h]
            -- 🎉 no goals
          · exact False.elim (hI.ne_top h.left)
            -- 🎉 no goals
          · exact False.elim (hJ.ne_top h.right)
            -- 🎉 no goals
          · simp only [h]
            -- 🎉 no goals
        · rintro ⟨I, hI⟩
          -- ⊢ ∃ a, primeSpectrumProdOfSum R S a = { asIdeal := I, IsPrime := hI }
          rcases(Ideal.ideal_prod_prime I).mp hI with (⟨p, ⟨hp, rfl⟩⟩ | ⟨p, ⟨hp, rfl⟩⟩)
          -- ⊢ ∃ a, primeSpectrumProdOfSum R S a = { asIdeal := Ideal.prod p ⊤, IsPrime :=  …
          · exact ⟨Sum.inl ⟨p, hp⟩, rfl⟩
            -- 🎉 no goals
          · exact ⟨Sum.inr ⟨p, hp⟩, rfl⟩)
            -- 🎉 no goals
#align prime_spectrum.prime_spectrum_prod PrimeSpectrum.primeSpectrumProd

variable {R S}

@[simp]
theorem primeSpectrumProd_symm_inl_asIdeal (x : PrimeSpectrum R) :
    ((primeSpectrumProd R S).symm <| Sum.inl x).asIdeal = Ideal.prod x.asIdeal ⊤ := by
  cases x
  -- ⊢ (↑(primeSpectrumProd R S).symm (Sum.inl { asIdeal := asIdeal✝, IsPrime := Is …
  rfl
  -- 🎉 no goals
#align prime_spectrum.prime_spectrum_prod_symm_inl_as_ideal PrimeSpectrum.primeSpectrumProd_symm_inl_asIdeal

@[simp]
theorem primeSpectrumProd_symm_inr_asIdeal (x : PrimeSpectrum S) :
    ((primeSpectrumProd R S).symm <| Sum.inr x).asIdeal = Ideal.prod ⊤ x.asIdeal := by
  cases x
  -- ⊢ (↑(primeSpectrumProd R S).symm (Sum.inr { asIdeal := asIdeal✝, IsPrime := Is …
  rfl
  -- 🎉 no goals
#align prime_spectrum.prime_spectrum_prod_symm_inr_as_ideal PrimeSpectrum.primeSpectrumProd_symm_inr_asIdeal

/-- The zero locus of a set `s` of elements of a commutative ring `R` is the set of all prime ideals
of the ring that contain the set `s`.

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
  -- ⊢ x ∈ zeroLocus ↑(Ideal.span s) ↔ x ∈ zeroLocus s
  exact (Submodule.gi R R).gc s x.asIdeal
  -- 🎉 no goals
#align prime_spectrum.zero_locus_span PrimeSpectrum.zeroLocus_span

/-- The vanishing ideal of a set `t` of points of the prime spectrum of a commutative ring `R` is
the intersection of all the prime ideals in the set `t`.

An element `f` of `R` can be thought of as a dependent function on the prime spectrum of `R`.
At a point `x` (a prime ideal) the function (i.e., element) `f` takes values in the quotient ring
`R` modulo the prime ideal `x`. In this manner, `vanishingIdeal t` is exactly the ideal of `R`
consisting of all "functions" that vanish on all of `t`.
-/
def vanishingIdeal (t : Set (PrimeSpectrum R)) : Ideal R :=
  ⨅ (x : PrimeSpectrum R) (_ : x ∈ t), x.asIdeal
#align prime_spectrum.vanishing_ideal PrimeSpectrum.vanishingIdeal

theorem coe_vanishingIdeal (t : Set (PrimeSpectrum R)) :
    (vanishingIdeal t : Set R) = { f : R | ∀ x : PrimeSpectrum R, x ∈ t → f ∈ x.asIdeal } := by
  ext f
  -- ⊢ f ∈ ↑(vanishingIdeal t) ↔ f ∈ {f | ∀ (x : PrimeSpectrum R), x ∈ t → f ∈ x.as …
  rw [vanishingIdeal, SetLike.mem_coe, Submodule.mem_iInf]
  -- ⊢ (∀ (i : PrimeSpectrum R), f ∈ ⨅ (_ : i ∈ t), i.asIdeal) ↔ f ∈ {f | ∀ (x : Pr …
  apply forall_congr'; intro x
  -- ⊢ ∀ (a : PrimeSpectrum R), f ∈ ⨅ (_ : a ∈ t), a.asIdeal ↔ a ∈ t → f ∈ a.asIdeal
                       -- ⊢ f ∈ ⨅ (_ : x ∈ t), x.asIdeal ↔ x ∈ t → f ∈ x.asIdeal
  rw [Submodule.mem_iInf]
  -- 🎉 no goals
#align prime_spectrum.coe_vanishing_ideal PrimeSpectrum.coe_vanishingIdeal

theorem mem_vanishingIdeal (t : Set (PrimeSpectrum R)) (f : R) :
    f ∈ vanishingIdeal t ↔ ∀ x : PrimeSpectrum R, x ∈ t → f ∈ x.asIdeal := by
  rw [← SetLike.mem_coe, coe_vanishingIdeal, Set.mem_setOf_eq]
  -- 🎉 no goals
#align prime_spectrum.mem_vanishing_ideal PrimeSpectrum.mem_vanishingIdeal

@[simp]
theorem vanishingIdeal_singleton (x : PrimeSpectrum R) :
    vanishingIdeal ({x} : Set (PrimeSpectrum R)) = x.asIdeal := by simp [vanishingIdeal]
                                                                   -- 🎉 no goals
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
  -- ⊢ GaloisConnection (fun s => zeroLocus s) fun t => ↑(vanishingIdeal t)
  simpa [zeroLocus_span, Function.comp] using ideal_gc.compose (gc R)
  -- 🎉 no goals
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
    -- ⊢ (∀ (x : PrimeSpectrum R), x ∈ zeroLocus ↑I → f ∈ x.asIdeal) ↔ ∀ (p : Submodu …
    exact ⟨fun h x hx => h ⟨x, hx.2⟩ hx.1, fun h x hx => h x.1 ⟨hx, x.2⟩⟩
    -- 🎉 no goals
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
    zeroLocus (I : Set R) ⊆ zeroLocus (J : Set R) ↔ J ≤ I.radical :=
  ⟨fun h =>
    Ideal.radical_le_radical_iff.mp
      (vanishingIdeal_zeroLocus_eq_radical I ▸
        vanishingIdeal_zeroLocus_eq_radical J ▸ vanishingIdeal_anti_mono h),
    fun h => zeroLocus_radical I ▸ zeroLocus_anti_mono_ideal h⟩
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
theorem vanishingIdeal_univ : vanishingIdeal (∅ : Set (PrimeSpectrum R)) = ⊤ := by
  simpa using (gc R).u_top
  -- 🎉 no goals
#align prime_spectrum.vanishing_ideal_univ PrimeSpectrum.vanishingIdeal_univ

theorem zeroLocus_empty_of_one_mem {s : Set R} (h : (1 : R) ∈ s) : zeroLocus s = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem]
  -- ⊢ ∀ (x : PrimeSpectrum R), ¬x ∈ zeroLocus s
  intro x hx
  -- ⊢ False
  rw [mem_zeroLocus] at hx
  -- ⊢ False
  have x_prime : x.asIdeal.IsPrime := by infer_instance
  -- ⊢ False
  have eq_top : x.asIdeal = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    exact hx h
  apply x_prime.ne_top eq_top
  -- 🎉 no goals
#align prime_spectrum.zero_locus_empty_of_one_mem PrimeSpectrum.zeroLocus_empty_of_one_mem

@[simp]
theorem zeroLocus_singleton_one : zeroLocus ({1} : Set R) = ∅ :=
  zeroLocus_empty_of_one_mem (Set.mem_singleton (1 : R))
#align prime_spectrum.zero_locus_singleton_one PrimeSpectrum.zeroLocus_singleton_one

theorem zeroLocus_empty_iff_eq_top {I : Ideal R} : zeroLocus (I : Set R) = ∅ ↔ I = ⊤ := by
  constructor
  -- ⊢ zeroLocus ↑I = ∅ → I = ⊤
  · contrapose!
    -- ⊢ I ≠ ⊤ → zeroLocus ↑I ≠ ∅
    intro h
    -- ⊢ zeroLocus ↑I ≠ ∅
    rcases Ideal.exists_le_maximal I h with ⟨M, hM, hIM⟩
    -- ⊢ zeroLocus ↑I ≠ ∅
    exact Set.Nonempty.ne_empty ⟨⟨M, hM.isPrime⟩, hIM⟩
    -- 🎉 no goals
  · rintro rfl
    -- ⊢ zeroLocus ↑⊤ = ∅
    apply zeroLocus_empty_of_one_mem
    -- ⊢ 1 ∈ ↑⊤
    trivial
    -- 🎉 no goals
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
                                                                    -- 🎉 no goals
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
  -- ⊢ zeroLocus s ∪ zeroLocus s' = zeroLocus ↑(Ideal.span s) ∪ zeroLocus ↑(Ideal.s …
  simp
  -- 🎉 no goals
#align prime_spectrum.union_zero_locus PrimeSpectrum.union_zeroLocus

theorem zeroLocus_mul (I J : Ideal R) :
    zeroLocus ((I * J : Ideal R) : Set R) = zeroLocus I ∪ zeroLocus J :=
  Set.ext fun x => x.2.mul_le
#align prime_spectrum.zero_locus_mul PrimeSpectrum.zeroLocus_mul

theorem zeroLocus_singleton_mul (f g : R) :
    zeroLocus ({f * g} : Set R) = zeroLocus {f} ∪ zeroLocus {g} :=
  Set.ext fun x => by simpa using x.2.mul_mem_iff_mem_or_mem
                      -- 🎉 no goals
#align prime_spectrum.zero_locus_singleton_mul PrimeSpectrum.zeroLocus_singleton_mul

@[simp]
theorem zeroLocus_pow (I : Ideal R) {n : ℕ} (hn : 0 < n) :
    zeroLocus ((I ^ n : Ideal R) : Set R) = zeroLocus I :=
  zeroLocus_radical (I ^ n) ▸ (I.radical_pow n hn).symm ▸ zeroLocus_radical I
#align prime_spectrum.zero_locus_pow PrimeSpectrum.zeroLocus_pow

@[simp]
theorem zeroLocus_singleton_pow (f : R) (n : ℕ) (hn : 0 < n) :
    zeroLocus ({f ^ n} : Set R) = zeroLocus {f} :=
  Set.ext fun x => by simpa using x.2.pow_mem_iff_mem n hn
                      -- 🎉 no goals
#align prime_spectrum.zero_locus_singleton_pow PrimeSpectrum.zeroLocus_singleton_pow

theorem sup_vanishingIdeal_le (t t' : Set (PrimeSpectrum R)) :
    vanishingIdeal t ⊔ vanishingIdeal t' ≤ vanishingIdeal (t ∩ t') := by
  intro r
  -- ⊢ r ∈ vanishingIdeal t ⊔ vanishingIdeal t' → r ∈ vanishingIdeal (t ∩ t')
  rw [Submodule.mem_sup, mem_vanishingIdeal]
  -- ⊢ (∃ y, y ∈ vanishingIdeal t ∧ ∃ z, z ∈ vanishingIdeal t' ∧ y + z = r) → ∀ (x  …
  rintro ⟨f, hf, g, hg, rfl⟩ x ⟨hxt, hxt'⟩
  -- ⊢ f + g ∈ x.asIdeal
  rw [mem_vanishingIdeal] at hf hg
  -- ⊢ f + g ∈ x.asIdeal
  apply Submodule.add_mem <;> solve_by_elim
  -- ⊢ f ∈ x.asIdeal
                              -- 🎉 no goals
                              -- 🎉 no goals
#align prime_spectrum.sup_vanishing_ideal_le PrimeSpectrum.sup_vanishingIdeal_le

theorem mem_compl_zeroLocus_iff_not_mem {f : R} {I : PrimeSpectrum R} :
    I ∈ (zeroLocus {f} : Set (PrimeSpectrum R))ᶜ ↔ f ∉ I.asIdeal := by
  rw [Set.mem_compl_iff, mem_zeroLocus, Set.singleton_subset_iff]; rfl
  -- ⊢ ¬f ∈ ↑I.asIdeal ↔ ¬f ∈ I.asIdeal
                                                                   -- 🎉 no goals
#align prime_spectrum.mem_compl_zero_locus_iff_not_mem PrimeSpectrum.mem_compl_zeroLocus_iff_not_mem

/-- The Zariski topology on the prime spectrum of a commutative ring is defined via the closed sets
of the topology: they are exactly those sets that are the zero locus of a subset of the ring. -/
instance zariskiTopology : TopologicalSpace (PrimeSpectrum R) :=
  TopologicalSpace.ofClosed (Set.range PrimeSpectrum.zeroLocus) ⟨Set.univ, by simp⟩
                                                                              -- 🎉 no goals
    (by
      intro Zs h
      -- ⊢ ⋂₀ Zs ∈ Set.range zeroLocus
      rw [Set.sInter_eq_iInter]
      -- ⊢ ⋂ (i : ↑Zs), ↑i ∈ Set.range zeroLocus
      choose f hf using fun i : Zs => h i.prop
      -- ⊢ ⋂ (i : ↑Zs), ↑i ∈ Set.range zeroLocus
      simp only [← hf]
      -- ⊢ ⋂ (i : ↑Zs), zeroLocus (f i) ∈ Set.range zeroLocus
      exact ⟨_, zeroLocus_iUnion _⟩)
      -- 🎉 no goals
    (by
      rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
      -- ⊢ zeroLocus s ∪ zeroLocus t ∈ Set.range zeroLocus
      exact ⟨_, (union_zeroLocus s t).symm⟩)
      -- 🎉 no goals
#align prime_spectrum.zariski_topology PrimeSpectrum.zariskiTopology

theorem isOpen_iff (U : Set (PrimeSpectrum R)) : IsOpen U ↔ ∃ s, Uᶜ = zeroLocus s := by
  simp only [@eq_comm _ Uᶜ]; rfl
  -- ⊢ IsOpen U ↔ ∃ s, zeroLocus s = Uᶜ
                             -- 🎉 no goals
#align prime_spectrum.is_open_iff PrimeSpectrum.isOpen_iff

theorem isClosed_iff_zeroLocus (Z : Set (PrimeSpectrum R)) : IsClosed Z ↔ ∃ s, Z = zeroLocus s := by
  rw [← isOpen_compl_iff, isOpen_iff, compl_compl]
  -- 🎉 no goals
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
  -- ⊢ ∃ s_1, zeroLocus s = zeroLocus s_1
  exact ⟨s, rfl⟩
  -- 🎉 no goals
#align prime_spectrum.is_closed_zero_locus PrimeSpectrum.isClosed_zeroLocus

theorem isClosed_singleton_iff_isMaximal (x : PrimeSpectrum R) :
    IsClosed ({x} : Set (PrimeSpectrum R)) ↔ x.asIdeal.IsMaximal := by
  refine' (isClosed_iff_zeroLocus _).trans ⟨fun h => _, fun h => _⟩
  -- ⊢ Ideal.IsMaximal x.asIdeal
  · obtain ⟨s, hs⟩ := h
    -- ⊢ Ideal.IsMaximal x.asIdeal
    rw [eq_comm, Set.eq_singleton_iff_unique_mem] at hs
    -- ⊢ Ideal.IsMaximal x.asIdeal
    refine'
      ⟨⟨x.2.1, fun I hI =>
          Classical.not_not.1
            (mt (Ideal.exists_le_maximal I) <| not_exists.2 fun J => not_and.2 fun hJ hIJ => _)⟩⟩
    exact
      ne_of_lt (lt_of_lt_of_le hI hIJ)
        (symm <|
          congr_arg PrimeSpectrum.asIdeal
            (hs.2 ⟨J, hJ.isPrime⟩ fun r hr => hIJ (le_of_lt hI <| hs.1 hr)))
  · refine' ⟨x.asIdeal.1, _⟩
    -- ⊢ {x} = zeroLocus ↑x.asIdeal.toAddSubmonoid
    rw [eq_comm, Set.eq_singleton_iff_unique_mem]
    -- ⊢ x ∈ zeroLocus ↑x.asIdeal.toAddSubmonoid ∧ ∀ (x_1 : PrimeSpectrum R), x_1 ∈ z …
    refine' ⟨fun _ h => h, fun y hy => PrimeSpectrum.ext _ _ (h.eq_of_le y.2.ne_top hy).symm⟩
    -- 🎉 no goals
#align prime_spectrum.is_closed_singleton_iff_is_maximal PrimeSpectrum.isClosed_singleton_iff_isMaximal

theorem zeroLocus_vanishingIdeal_eq_closure (t : Set (PrimeSpectrum R)) :
    zeroLocus (vanishingIdeal t : Set R) = closure t := by
  apply Set.Subset.antisymm
  -- ⊢ zeroLocus ↑(vanishingIdeal t) ⊆ closure t
  · rintro x hx t' ⟨ht', ht⟩
    -- ⊢ x ∈ t'
    obtain ⟨fs, rfl⟩ : ∃ s, t' = zeroLocus s := by rwa [isClosed_iff_zeroLocus] at ht'
    -- ⊢ x ∈ zeroLocus fs
    rw [subset_zeroLocus_iff_subset_vanishingIdeal] at ht
    -- ⊢ x ∈ zeroLocus fs
    exact Set.Subset.trans ht hx
    -- 🎉 no goals
  · rw [(isClosed_zeroLocus _).closure_subset_iff]
    -- ⊢ t ⊆ zeroLocus ↑(vanishingIdeal t)
    exact subset_zeroLocus_vanishingIdeal t
    -- 🎉 no goals
#align prime_spectrum.zero_locus_vanishing_ideal_eq_closure PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure

theorem vanishingIdeal_closure (t : Set (PrimeSpectrum R)) :
    vanishingIdeal (closure t) = vanishingIdeal t :=
  zeroLocus_vanishingIdeal_eq_closure t ▸ (gc R).u_l_u_eq_u t
#align prime_spectrum.vanishing_ideal_closure PrimeSpectrum.vanishingIdeal_closure

theorem closure_singleton (x) : closure ({x} : Set (PrimeSpectrum R)) = zeroLocus x.asIdeal := by
  rw [← zeroLocus_vanishingIdeal_eq_closure, vanishingIdeal_singleton]
  -- 🎉 no goals
#align prime_spectrum.closure_singleton PrimeSpectrum.closure_singleton

theorem isRadical_vanishingIdeal (s : Set (PrimeSpectrum R)) : (vanishingIdeal s).IsRadical := by
  rw [← vanishingIdeal_closure, ← zeroLocus_vanishingIdeal_eq_closure,
    vanishingIdeal_zeroLocus_eq_radical]
  apply Ideal.radical_isRadical
  -- 🎉 no goals
#align prime_spectrum.is_radical_vanishing_ideal PrimeSpectrum.isRadical_vanishingIdeal

theorem vanishingIdeal_anti_mono_iff {s t : Set (PrimeSpectrum R)} (ht : IsClosed t) :
    s ⊆ t ↔ vanishingIdeal t ≤ vanishingIdeal s :=
  ⟨vanishingIdeal_anti_mono, fun h => by
    rw [← ht.closure_subset_iff, ← ht.closure_eq]
    -- ⊢ closure s ⊆ closure t
    convert ← zeroLocus_anti_mono_ideal h <;> apply zeroLocus_vanishingIdeal_eq_closure⟩
    -- ⊢ zeroLocus ↑(vanishingIdeal s) = closure s
                                              -- 🎉 no goals
                                              -- 🎉 no goals
#align prime_spectrum.vanishing_ideal_anti_mono_iff PrimeSpectrum.vanishingIdeal_anti_mono_iff

theorem vanishingIdeal_strict_anti_mono_iff {s t : Set (PrimeSpectrum R)} (hs : IsClosed s)
    (ht : IsClosed t) : s ⊂ t ↔ vanishingIdeal t < vanishingIdeal s := by
  rw [Set.ssubset_def, vanishingIdeal_anti_mono_iff hs, vanishingIdeal_anti_mono_iff ht,
    lt_iff_le_not_le]
#align prime_spectrum.vanishing_ideal_strict_anti_mono_iff PrimeSpectrum.vanishingIdeal_strict_anti_mono_iff

/-- The antitone order embedding of closed subsets of `Spec R` into ideals of `R`. -/
def closedsEmbedding (R : Type*) [CommRing R] :
    (TopologicalSpace.Closeds <| PrimeSpectrum R)ᵒᵈ ↪o Ideal R :=
  OrderEmbedding.ofMapLEIff (fun s => vanishingIdeal <| OrderDual.ofDual s) fun s _ =>
    (vanishingIdeal_anti_mono_iff s.2).symm
#align prime_spectrum.closeds_embedding PrimeSpectrum.closedsEmbedding

theorem t1Space_iff_isField [IsDomain R] : T1Space (PrimeSpectrum R) ↔ IsField R := by
  refine' ⟨_, fun h => _⟩
  -- ⊢ T1Space (PrimeSpectrum R) → IsField R
  · intro h
    -- ⊢ IsField R
    have hbot : Ideal.IsPrime (⊥ : Ideal R) := Ideal.bot_prime
    -- ⊢ IsField R
    exact
      Classical.not_not.1
        (mt
          (Ring.ne_bot_of_isMaximal_of_not_isField <|
            (isClosed_singleton_iff_isMaximal _).1 (T1Space.t1 ⟨⊥, hbot⟩))
          (by aesop))
  · refine' ⟨fun x => (isClosed_singleton_iff_isMaximal x).2 _⟩
    -- ⊢ Ideal.IsMaximal x.asIdeal
    by_cases hx : x.asIdeal = ⊥
    -- ⊢ Ideal.IsMaximal x.asIdeal
    · letI := h.toField
      -- ⊢ Ideal.IsMaximal x.asIdeal
      exact hx.symm ▸ Ideal.bot_isMaximal
      -- 🎉 no goals
    · exact absurd h (Ring.not_isField_iff_exists_prime.2 ⟨x.asIdeal, ⟨hx, x.2⟩⟩)
      -- 🎉 no goals
#align prime_spectrum.t1_space_iff_is_field PrimeSpectrum.t1Space_iff_isField

local notation "Z(" a ")" => zeroLocus (a : Set R)

theorem isIrreducible_zeroLocus_iff_of_radical (I : Ideal R) (hI : I.IsRadical) :
    IsIrreducible (zeroLocus (I : Set R)) ↔ I.IsPrime := by
  rw [Ideal.isPrime_iff, IsIrreducible]
  -- ⊢ Set.Nonempty (zeroLocus ↑I) ∧ IsPreirreducible (zeroLocus ↑I) ↔ I ≠ ⊤ ∧ ∀ {x …
  apply and_congr
  -- ⊢ Set.Nonempty (zeroLocus ↑I) ↔ I ≠ ⊤
  · rw [Set.nonempty_iff_ne_empty, Ne.def, zeroLocus_empty_iff_eq_top]
    -- 🎉 no goals
  · trans ∀ x y : Ideal R, Z(I) ⊆ Z(x) ∪ Z(y) → Z(I) ⊆ Z(x) ∨ Z(I) ⊆ Z(y)
    -- ⊢ IsPreirreducible (zeroLocus ↑I) ↔ ∀ (x y : Ideal R), zeroLocus ↑I ⊆ zeroLocu …
    · simp_rw [isPreirreducible_iff_closed_union_closed, isClosed_iff_zeroLocus_ideal]
      -- ⊢ (∀ (z₁ z₂ : Set (PrimeSpectrum R)), (∃ I, z₁ = zeroLocus ↑I) → (∃ I, z₂ = ze …
      constructor
      -- ⊢ (∀ (z₁ z₂ : Set (PrimeSpectrum R)), (∃ I, z₁ = zeroLocus ↑I) → (∃ I, z₂ = ze …
      · rintro h x y
        -- ⊢ zeroLocus ↑I ⊆ zeroLocus ↑x ∪ zeroLocus ↑y → zeroLocus ↑I ⊆ zeroLocus ↑x ∨ z …
        exact h _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        -- 🎉 no goals
      · rintro h _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        -- ⊢ zeroLocus ↑I ⊆ zeroLocus ↑x ∪ zeroLocus ↑y → zeroLocus ↑I ⊆ zeroLocus ↑x ∨ z …
        exact h x y
        -- 🎉 no goals
    · simp_rw [← zeroLocus_inf, subset_zeroLocus_iff_le_vanishingIdeal,
        vanishingIdeal_zeroLocus_eq_radical, hI.radical]
      constructor
      -- ⊢ (∀ (x y : Ideal R), x ⊓ y ≤ I → x ≤ I ∨ y ≤ I) → ∀ {x y : R}, x * y ∈ I → x  …
      · simp_rw [← SetLike.mem_coe, ← Set.singleton_subset_iff, ← Ideal.span_le, ←
          Ideal.span_singleton_mul_span_singleton]
        refine' fun h x y h' => h _ _ _
        -- ⊢ Ideal.span {x} ⊓ Ideal.span {y} ≤ I
        rw [← hI.radical_le_iff] at h' ⊢
        -- ⊢ Ideal.radical (Ideal.span {x} ⊓ Ideal.span {y}) ≤ I
        simpa only [Ideal.radical_inf, Ideal.radical_mul] using h'
        -- 🎉 no goals
      · simp_rw [or_iff_not_imp_left, SetLike.not_le_iff_exists]
        -- ⊢ (∀ {x y : R}, x * y ∈ I → ¬x ∈ I → y ∈ I) → ∀ (x y : Ideal R), x ⊓ y ≤ I → ( …
        rintro h s t h' ⟨x, hx, hx'⟩ y hy
        -- ⊢ y ∈ I
        exact h (h' ⟨Ideal.mul_mem_right _ _ hx, Ideal.mul_mem_left _ _ hy⟩) hx'
        -- 🎉 no goals
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

instance irreducibleSpace [IsDomain R] : IrreducibleSpace (PrimeSpectrum R) := by
  rw [irreducibleSpace_def, Set.top_eq_univ, ← zeroLocus_bot, isIrreducible_zeroLocus_iff]
  -- ⊢ Ideal.IsPrime (Ideal.radical ⊥)
  simpa using Ideal.bot_prime
  -- 🎉 no goals

instance quasiSober : QuasiSober (PrimeSpectrum R) :=
  ⟨fun {S} h₁ h₂ =>
    ⟨⟨_, isIrreducible_iff_vanishingIdeal_isPrime.1 h₁⟩, by
      rw [IsGenericPoint, closure_singleton, zeroLocus_vanishingIdeal_eq_closure, h₂.closure_eq]⟩⟩
      -- 🎉 no goals

section Comap

variable {S' : Type*} [CommRing S']

theorem preimage_comap_zeroLocus_aux (f : R →+* S) (s : Set R) :
    (fun y => ⟨Ideal.comap f y.asIdeal, inferInstance⟩ : PrimeSpectrum S → PrimeSpectrum R) ⁻¹'
        zeroLocus s =
      zeroLocus (f '' s) := by
  ext x
  -- ⊢ x ∈ (fun y => { asIdeal := Ideal.comap f y.asIdeal, IsPrime := (_ : Ideal.Is …
  simp only [mem_zeroLocus, Set.image_subset_iff, Set.mem_preimage, mem_zeroLocus, Ideal.coe_comap]
  -- 🎉 no goals
#align prime_spectrum.preimage_comap_zero_locus_aux PrimeSpectrum.preimage_comap_zeroLocus_aux

/-- The function between prime spectra of commutative rings induced by a ring homomorphism.
This function is continuous. -/
def comap (f : R →+* S) : C(PrimeSpectrum S, PrimeSpectrum R) where
  toFun y := ⟨Ideal.comap f y.asIdeal, inferInstance⟩
  continuous_toFun := by
    simp only [continuous_iff_isClosed, isClosed_iff_zeroLocus]
    -- ⊢ ∀ (s : Set (PrimeSpectrum R)), (∃ s_1, s = zeroLocus s_1) → ∃ s_1, (fun y => …
    rintro _ ⟨s, rfl⟩
    -- ⊢ ∃ s_1, (fun y => { asIdeal := Ideal.comap f y.asIdeal, IsPrime := (_ : Ideal …
    exact ⟨_, preimage_comap_zeroLocus_aux f s⟩
    -- 🎉 no goals
#align prime_spectrum.comap PrimeSpectrum.comap

variable (f : R →+* S)

@[simp]
theorem comap_asIdeal (y : PrimeSpectrum S) : (comap f y).asIdeal = Ideal.comap f y.asIdeal :=
  rfl
#align prime_spectrum.comap_as_ideal PrimeSpectrum.comap_asIdeal

@[simp]
theorem comap_id : comap (RingHom.id R) = ContinuousMap.id _ := by
  ext
  -- ⊢ x✝ ∈ (↑(comap (RingHom.id R)) a✝).asIdeal ↔ x✝ ∈ (↑(ContinuousMap.id (PrimeS …
  rfl
  -- 🎉 no goals
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

theorem comap_singleton_isClosed_of_surjective (f : R →+* S) (hf : Function.Surjective f)
    (x : PrimeSpectrum S) (hx : IsClosed ({x} : Set (PrimeSpectrum S))) :
    IsClosed ({comap f x} : Set (PrimeSpectrum R)) :=
  haveI : x.asIdeal.IsMaximal := (isClosed_singleton_iff_isMaximal x).1 hx
  (isClosed_singleton_iff_isMaximal _).2 (Ideal.comap_isMaximal_of_surjective f hf)
#align prime_spectrum.comap_singleton_is_closed_of_surjective PrimeSpectrum.comap_singleton_isClosed_of_surjective

theorem comap_singleton_isClosed_of_isIntegral (f : R →+* S) (hf : f.IsIntegral)
    (x : PrimeSpectrum S) (hx : IsClosed ({x} : Set (PrimeSpectrum S))) :
    IsClosed ({comap f x} : Set (PrimeSpectrum R)) :=
  (isClosed_singleton_iff_isMaximal _).2
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hf x.asIdeal <|
      (isClosed_singleton_iff_isMaximal x).1 hx)
#align prime_spectrum.comap_singleton_is_closed_of_is_integral PrimeSpectrum.comap_singleton_isClosed_of_isIntegral

variable (S)

theorem localization_comap_inducing [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    Inducing (comap (algebraMap R S)) := by
  constructor
  -- ⊢ zariskiTopology = TopologicalSpace.induced (↑(comap (algebraMap R S))) zaris …
  rw [TopologicalSpace.ext_iff]
  -- ⊢ ∀ (s : Set (PrimeSpectrum S)), IsOpen s ↔ IsOpen s
  intro U
  -- ⊢ IsOpen U ↔ IsOpen U
  rw [← isClosed_compl_iff, ← @isClosed_compl_iff (α := PrimeSpectrum S) (s := U)]
  -- ⊢ IsClosed Uᶜ ↔ IsClosed Uᶜ
  generalize Uᶜ = Z
  -- ⊢ IsClosed Z ↔ IsClosed Z
  simp_rw [isClosed_induced_iff, isClosed_iff_zeroLocus]
  -- ⊢ (∃ s, Z = zeroLocus s) ↔ ∃ t, (∃ s, t = zeroLocus s) ∧ ↑(comap (algebraMap R …
  constructor
  -- ⊢ (∃ s, Z = zeroLocus s) → ∃ t, (∃ s, t = zeroLocus s) ∧ ↑(comap (algebraMap R …
  · rintro ⟨s, rfl⟩
    -- ⊢ ∃ t, (∃ s, t = zeroLocus s) ∧ ↑(comap (algebraMap R S)) ⁻¹' t = zeroLocus s
    refine ⟨_, ⟨algebraMap R S ⁻¹' Ideal.span s, rfl⟩, ?_⟩
    -- ⊢ ↑(comap (algebraMap R S)) ⁻¹' zeroLocus (↑(algebraMap R S) ⁻¹' ↑(Ideal.span  …
    rw [preimage_comap_zeroLocus, ← zeroLocus_span, ← zeroLocus_span s]
    -- ⊢ zeroLocus ↑(Ideal.span (↑(algebraMap R S) '' (↑(algebraMap R S) ⁻¹' ↑(Ideal. …
    congr 2
    -- ⊢ zeroLocus ↑(Ideal.span (↑(algebraMap R S) '' (↑(algebraMap R S) ⁻¹' ↑(Ideal. …
    exact congr_arg (zeroLocus ·) <| Submodule.carrier_inj.mpr
      (IsLocalization.map_comap M S (Ideal.span s))
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    -- ⊢ ∃ s, ↑(comap (algebraMap R S)) ⁻¹' zeroLocus t = zeroLocus s
    rw [preimage_comap_zeroLocus]
    -- ⊢ ∃ s, zeroLocus (↑(algebraMap R S) '' t) = zeroLocus s
    exact ⟨_, rfl⟩
    -- 🎉 no goals
#align prime_spectrum.localization_comap_inducing PrimeSpectrum.localization_comap_inducing

theorem localization_comap_injective [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    Function.Injective (comap (algebraMap R S)) := by
  intro p q h
  -- ⊢ p = q
  replace h := congr_arg (fun x : PrimeSpectrum R => Ideal.map (algebraMap R S) x.asIdeal) h
  -- ⊢ p = q
  dsimp only [comap, ContinuousMap.coe_mk] at h
  -- ⊢ p = q
  rw [IsLocalization.map_comap M S, IsLocalization.map_comap M S] at h
  -- ⊢ p = q
  ext1
  -- ⊢ p.asIdeal = q.asIdeal
  exact h
  -- 🎉 no goals
#align prime_spectrum.localization_comap_injective PrimeSpectrum.localization_comap_injective

theorem localization_comap_embedding [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    Embedding (comap (algebraMap R S)) :=
  ⟨localization_comap_inducing S M, localization_comap_injective S M⟩
#align prime_spectrum.localization_comap_embedding PrimeSpectrum.localization_comap_embedding

theorem localization_comap_range [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    Set.range (comap (algebraMap R S)) = { p | Disjoint (M : Set R) p.asIdeal } := by
  ext x
  -- ⊢ x ∈ Set.range ↑(comap (algebraMap R S)) ↔ x ∈ {p | Disjoint ↑M ↑p.asIdeal}
  constructor
  -- ⊢ x ∈ Set.range ↑(comap (algebraMap R S)) → x ∈ {p | Disjoint ↑M ↑p.asIdeal}
  · simp_rw [disjoint_iff_inf_le]
    -- ⊢ x ∈ Set.range ↑(comap (algebraMap R S)) → x ∈ {p | ↑M ⊓ ↑p.asIdeal ≤ ⊥}
    rintro ⟨p, rfl⟩ x ⟨hx₁, hx₂⟩
    -- ⊢ x ∈ ⊥
    exact (p.2.1 : ¬_) (p.asIdeal.eq_top_of_isUnit_mem hx₂ (IsLocalization.map_units S ⟨x, hx₁⟩))
    -- 🎉 no goals
  · intro h
    -- ⊢ x ∈ Set.range ↑(comap (algebraMap R S))
    use ⟨x.asIdeal.map (algebraMap R S), IsLocalization.isPrime_of_isPrime_disjoint M S _ x.2 h⟩
    -- ⊢ ↑(comap (algebraMap R S)) { asIdeal := Ideal.map (algebraMap R S) x.asIdeal, …
    ext1
    -- ⊢ (↑(comap (algebraMap R S)) { asIdeal := Ideal.map (algebraMap R S) x.asIdeal …
    exact IsLocalization.comap_map_of_isPrime_disjoint M S _ x.2 h
    -- 🎉 no goals
#align prime_spectrum.localization_comap_range PrimeSpectrum.localization_comap_range

section SpecOfSurjective

/-! The comap of a surjective ring homomorphism is a closed embedding between the prime spectra. -/


open Function RingHom

theorem comap_inducing_of_surjective (hf : Surjective f) : Inducing (comap f) where
  induced := by
    simp_rw [TopologicalSpace.ext_iff, ← isClosed_compl_iff,
      ← @isClosed_compl_iff (PrimeSpectrum S)
        ((TopologicalSpace.induced (comap f) zariskiTopology)), isClosed_induced_iff,
      isClosed_iff_zeroLocus]
    refine' fun s =>
      ⟨fun ⟨F, hF⟩ =>
        ⟨zeroLocus (f ⁻¹' F), ⟨f ⁻¹' F, rfl⟩, by
          rw [preimage_comap_zeroLocus, Function.Surjective.image_preimage hf, hF]⟩,
        _⟩
    rintro ⟨-, ⟨F, rfl⟩, hF⟩
    -- ⊢ ∃ s_1, sᶜ = zeroLocus s_1
    exact ⟨f '' F, hF.symm.trans (preimage_comap_zeroLocus f F)⟩
    -- 🎉 no goals
#align prime_spectrum.comap_inducing_of_surjective PrimeSpectrum.comap_inducing_of_surjective

theorem image_comap_zeroLocus_eq_zeroLocus_comap (hf : Surjective f) (I : Ideal S) :
    comap f '' zeroLocus I = zeroLocus (I.comap f) := by
  simp only [Set.ext_iff, Set.mem_image, mem_zeroLocus, SetLike.coe_subset_coe]
  -- ⊢ ∀ (x : PrimeSpectrum R), (∃ x_1, I ≤ x_1.asIdeal ∧ ↑(comap f) x_1 = x) ↔ Ide …
  refine' fun p => ⟨_, fun h_I_p => _⟩
  -- ⊢ (∃ x, I ≤ x.asIdeal ∧ ↑(comap f) x = p) → Ideal.comap f I ≤ p.asIdeal
  · rintro ⟨p, hp, rfl⟩ a ha
    -- ⊢ a ∈ (↑(comap f) p).asIdeal
    exact hp ha
    -- 🎉 no goals
  · have hp : ker f ≤ p.asIdeal := (Ideal.comap_mono bot_le).trans h_I_p
    -- ⊢ ∃ x, I ≤ x.asIdeal ∧ ↑(comap f) x = p
    refine' ⟨⟨p.asIdeal.map f, Ideal.map_isPrime_of_surjective hf hp⟩, fun x hx => _, _⟩
    -- ⊢ x ∈ { asIdeal := Ideal.map f p.asIdeal, IsPrime := (_ : Ideal.IsPrime (Ideal …
    · obtain ⟨x', rfl⟩ := hf x
      -- ⊢ ↑f x' ∈ { asIdeal := Ideal.map f p.asIdeal, IsPrime := (_ : Ideal.IsPrime (I …
      exact Ideal.mem_map_of_mem f (h_I_p hx)
      -- 🎉 no goals
    · ext x
      -- ⊢ x ∈ (↑(comap f) { asIdeal := Ideal.map f p.asIdeal, IsPrime := (_ : Ideal.Is …
      rw [comap_asIdeal, Ideal.mem_comap, Ideal.mem_map_iff_of_surjective f hf]
      -- ⊢ (∃ x_1, x_1 ∈ p.asIdeal ∧ ↑f x_1 = ↑f x) ↔ x ∈ p.asIdeal
      refine' ⟨_, fun hx => ⟨x, hx, rfl⟩⟩
      -- ⊢ (∃ x_1, x_1 ∈ p.asIdeal ∧ ↑f x_1 = ↑f x) → x ∈ p.asIdeal
      rintro ⟨x', hx', heq⟩
      -- ⊢ x ∈ p.asIdeal
      rw [← sub_sub_cancel x' x]
      -- ⊢ x' - (x' - x) ∈ p.asIdeal
      refine' p.asIdeal.sub_mem hx' (hp _)
      -- ⊢ x' - x ∈ ker f
      rwa [mem_ker, map_sub, sub_eq_zero]
      -- 🎉 no goals
#align prime_spectrum.image_comap_zero_locus_eq_zero_locus_comap PrimeSpectrum.image_comap_zeroLocus_eq_zeroLocus_comap

theorem range_comap_of_surjective (hf : Surjective f) :
    Set.range (comap f) = zeroLocus (ker f) := by
  rw [← Set.image_univ]
  -- ⊢ ↑(comap f) '' Set.univ = zeroLocus ↑(ker f)
  convert image_comap_zeroLocus_eq_zeroLocus_comap _ _ hf _
  -- ⊢ Set.univ = zeroLocus ↑⊥
  rw [zeroLocus_bot]
  -- 🎉 no goals
#align prime_spectrum.range_comap_of_surjective PrimeSpectrum.range_comap_of_surjective

theorem isClosed_range_comap_of_surjective (hf : Surjective f) :
    IsClosed (Set.range (comap f)) := by
  rw [range_comap_of_surjective _ f hf]
  -- ⊢ IsClosed (zeroLocus ↑(ker f))
  exact isClosed_zeroLocus _
  -- 🎉 no goals
#align prime_spectrum.is_closed_range_comap_of_surjective PrimeSpectrum.isClosed_range_comap_of_surjective

theorem closedEmbedding_comap_of_surjective (hf : Surjective f) : ClosedEmbedding (comap f) :=
  { induced := (comap_inducing_of_surjective S f hf).induced
    inj := comap_injective_of_surjective f hf
    closed_range := isClosed_range_comap_of_surjective S f hf }
#align prime_spectrum.closed_embedding_comap_of_surjective PrimeSpectrum.closedEmbedding_comap_of_surjective

end SpecOfSurjective

end Comap

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
                                   -- 🎉 no goals
#align prime_spectrum.basic_open_one PrimeSpectrum.basicOpen_one

@[simp]
theorem basicOpen_zero : basicOpen (0 : R) = ⊥ :=
  TopologicalSpace.Opens.ext <| by simp
                                   -- 🎉 no goals
#align prime_spectrum.basic_open_zero PrimeSpectrum.basicOpen_zero

theorem basicOpen_le_basicOpen_iff (f g : R) :
    basicOpen f ≤ basicOpen g ↔ f ∈ (Ideal.span ({g} : Set R)).radical := by
  rw [← SetLike.coe_subset_coe, basicOpen_eq_zeroLocus_compl, basicOpen_eq_zeroLocus_compl,
    Set.compl_subset_compl, zeroLocus_subset_zeroLocus_singleton_iff]
#align prime_spectrum.basic_open_le_basic_open_iff PrimeSpectrum.basicOpen_le_basicOpen_iff

theorem basicOpen_mul (f g : R) : basicOpen (f * g) = basicOpen f ⊓ basicOpen g :=
  TopologicalSpace.Opens.ext <| by simp [zeroLocus_singleton_mul]
                                   -- 🎉 no goals
#align prime_spectrum.basic_open_mul PrimeSpectrum.basicOpen_mul

theorem basicOpen_mul_le_left (f g : R) : basicOpen (f * g) ≤ basicOpen f := by
  rw [basicOpen_mul f g]
  -- ⊢ basicOpen f ⊓ basicOpen g ≤ basicOpen f
  exact inf_le_left
  -- 🎉 no goals
#align prime_spectrum.basic_open_mul_le_left PrimeSpectrum.basicOpen_mul_le_left

theorem basicOpen_mul_le_right (f g : R) : basicOpen (f * g) ≤ basicOpen g := by
  rw [basicOpen_mul f g]
  -- ⊢ basicOpen f ⊓ basicOpen g ≤ basicOpen g
  exact inf_le_right
  -- 🎉 no goals
#align prime_spectrum.basic_open_mul_le_right PrimeSpectrum.basicOpen_mul_le_right

@[simp]
theorem basicOpen_pow (f : R) (n : ℕ) (hn : 0 < n) : basicOpen (f ^ n) = basicOpen f :=
  TopologicalSpace.Opens.ext <| by simpa using zeroLocus_singleton_pow f n hn
                                   -- 🎉 no goals
#align prime_spectrum.basic_open_pow PrimeSpectrum.basicOpen_pow

theorem isTopologicalBasis_basic_opens :
    TopologicalSpace.IsTopologicalBasis
      (Set.range fun r : R => (basicOpen r : Set (PrimeSpectrum R))) := by
  apply TopologicalSpace.isTopologicalBasis_of_open_of_nhds
  -- ⊢ ∀ (u : Set (PrimeSpectrum R)), (u ∈ Set.range fun r => ↑(basicOpen r)) → IsO …
  · rintro _ ⟨r, rfl⟩
    -- ⊢ IsOpen ((fun r => ↑(basicOpen r)) r)
    exact isOpen_basicOpen
    -- 🎉 no goals
  · rintro p U hp ⟨s, hs⟩
    -- ⊢ ∃ v, (v ∈ Set.range fun r => ↑(basicOpen r)) ∧ p ∈ v ∧ v ⊆ U
    rw [← compl_compl U, Set.mem_compl_iff, ← hs, mem_zeroLocus, Set.not_subset] at hp
    -- ⊢ ∃ v, (v ∈ Set.range fun r => ↑(basicOpen r)) ∧ p ∈ v ∧ v ⊆ U
    obtain ⟨f, hfs, hfp⟩ := hp
    -- ⊢ ∃ v, (v ∈ Set.range fun r => ↑(basicOpen r)) ∧ p ∈ v ∧ v ⊆ U
    refine' ⟨basicOpen f, ⟨f, rfl⟩, hfp, _⟩
    -- ⊢ ↑(basicOpen f) ⊆ U
    rw [← Set.compl_subset_compl, ← hs, basicOpen_eq_zeroLocus_compl, compl_compl]
    -- ⊢ zeroLocus s ⊆ zeroLocus {f}
    exact zeroLocus_anti_mono (Set.singleton_subset_iff.mpr hfs)
    -- 🎉 no goals
#align prime_spectrum.is_topological_basis_basic_opens PrimeSpectrum.isTopologicalBasis_basic_opens

theorem isBasis_basic_opens : TopologicalSpace.Opens.IsBasis (Set.range (@basicOpen R _)) := by
  unfold TopologicalSpace.Opens.IsBasis
  -- ⊢ TopologicalSpace.IsTopologicalBasis (SetLike.coe '' Set.range basicOpen)
  convert isTopologicalBasis_basic_opens (R := R)
  -- ⊢ SetLike.coe '' Set.range basicOpen = Set.range fun r => ↑(basicOpen r)
  rw [← Set.range_comp]
  -- ⊢ Set.range (SetLike.coe ∘ basicOpen) = Set.range fun r => ↑(basicOpen r)
  rfl
  -- 🎉 no goals
#align prime_spectrum.is_basis_basic_opens PrimeSpectrum.isBasis_basic_opens

theorem isCompact_basicOpen (f : R) : IsCompact (basicOpen f : Set (PrimeSpectrum R)) :=
  isCompact_of_finite_subfamily_closed fun {ι} Z hZc hZ => by
    let I : ι → Ideal R := fun i => vanishingIdeal (Z i)
    -- ⊢ ∃ t, ↑(basicOpen f) ∩ ⋂ (i : ι) (_ : i ∈ t), Z i = ∅
    have hI : ∀ i, Z i = zeroLocus (I i) := fun i => by
      simpa only [zeroLocus_vanishingIdeal_eq_closure] using (hZc i).closure_eq.symm
    rw [basicOpen_eq_zeroLocus_compl f, Set.inter_comm, ← Set.diff_eq, Set.diff_eq_empty,
      funext hI, ← zeroLocus_iSup] at hZ
    obtain ⟨n, hn⟩ : f ∈ (⨆ i : ι, I i).radical := by
      rw [← vanishingIdeal_zeroLocus_eq_radical]
      apply vanishingIdeal_anti_mono hZ
      exact subset_vanishingIdeal_zeroLocus {f} (Set.mem_singleton f)
    rcases Submodule.exists_finset_of_mem_iSup I hn with ⟨s, hs⟩
    -- ⊢ ∃ t, ↑(basicOpen f) ∩ ⋂ (i : ι) (_ : i ∈ t), Z i = ∅
    use s
    -- ⊢ ↑(basicOpen f) ∩ ⋂ (i : ι) (_ : i ∈ s), Z i = ∅
    -- Using simp_rw here, because `hI` and `zeroLocus_iSup` need to be applied underneath binders
    simp_rw [basicOpen_eq_zeroLocus_compl f, Set.inter_comm (zeroLocus {f})ᶜ, ← Set.diff_eq,
      Set.diff_eq_empty]
    rw [show (Set.iInter fun i => Set.iInter fun (_ : i ∈ s) => Z i) =
      Set.iInter fun i => Set.iInter fun (_ : i ∈ s) => zeroLocus (I i) from congr_arg _
        (funext fun i => congr_arg _ (funext fun _ => hI i))]
    simp_rw [← zeroLocus_iSup]
    -- ⊢ zeroLocus ↑(⨆ (i : ι) (_ : i ∈ s), vanishingIdeal (Z i)) ⊆ zeroLocus {f}
    rw [← zeroLocus_radical]
    -- ⊢ zeroLocus ↑(Ideal.radical (⨆ (i : ι) (_ : i ∈ s), vanishingIdeal (Z i))) ⊆ z …
    -- this one can't be in `simp_rw` because it would loop
    apply zeroLocus_anti_mono
    -- ⊢ {f} ⊆ ↑(Ideal.radical (⨆ (i : ι) (_ : i ∈ s), vanishingIdeal (Z i)))
    rw [Set.singleton_subset_iff]
    -- ⊢ f ∈ ↑(Ideal.radical (⨆ (i : ι) (_ : i ∈ s), vanishingIdeal (Z i)))
    exact ⟨n, hs⟩
    -- 🎉 no goals
#align prime_spectrum.is_compact_basic_open PrimeSpectrum.isCompact_basicOpen

@[simp]
theorem basicOpen_eq_bot_iff (f : R) : basicOpen f = ⊥ ↔ IsNilpotent f := by
  rw [← TopologicalSpace.Opens.coe_inj, basicOpen_eq_zeroLocus_compl]
  -- ⊢ (zeroLocus {f})ᶜ = ↑⊥ ↔ IsNilpotent f
  simp only [Set.eq_univ_iff_forall, Set.singleton_subset_iff, TopologicalSpace.Opens.coe_bot,
    nilpotent_iff_mem_prime, Set.compl_empty_iff, mem_zeroLocus, SetLike.mem_coe]
  exact ⟨fun h I hI => h ⟨I, hI⟩, fun h ⟨I, hI⟩ => h I hI⟩
  -- 🎉 no goals
#align prime_spectrum.basic_open_eq_bot_iff PrimeSpectrum.basicOpen_eq_bot_iff

theorem localization_away_comap_range (S : Type v) [CommRing S] [Algebra R S] (r : R)
    [IsLocalization.Away r S] : Set.range (comap (algebraMap R S)) = basicOpen r := by
  rw [localization_comap_range S (Submonoid.powers r)]
  -- ⊢ {p | Disjoint ↑(Submonoid.powers r) ↑p.asIdeal} = ↑(basicOpen r)
  ext x
  -- ⊢ x ∈ {p | Disjoint ↑(Submonoid.powers r) ↑p.asIdeal} ↔ x ∈ ↑(basicOpen r)
  simp only [mem_zeroLocus, basicOpen_eq_zeroLocus_compl, SetLike.mem_coe, Set.mem_setOf_eq,
    Set.singleton_subset_iff, Set.mem_compl_iff, disjoint_iff_inf_le]
  constructor
  -- ⊢ ↑(Submonoid.powers r) ⊓ ↑x.asIdeal ≤ ⊥ → ¬r ∈ x.asIdeal
  · intro h₁ h₂
    -- ⊢ False
    exact h₁ ⟨Submonoid.mem_powers r, h₂⟩
    -- 🎉 no goals
  · rintro h₁ _ ⟨⟨n, rfl⟩, h₃⟩
    -- ⊢ (fun x x_1 => x ^ x_1) r n ∈ ⊥
    exact h₁ (x.2.mem_of_pow_mem _ h₃)
    -- 🎉 no goals
#align prime_spectrum.localization_away_comap_range PrimeSpectrum.localization_away_comap_range

theorem localization_away_openEmbedding (S : Type v) [CommRing S] [Algebra R S] (r : R)
    [IsLocalization.Away r S] : OpenEmbedding (comap (algebraMap R S)) :=
  { toEmbedding := localization_comap_embedding S (Submonoid.powers r)
    open_range := by
      rw [localization_away_comap_range S r]
      -- ⊢ IsOpen ↑(basicOpen r)
      exact isOpen_basicOpen }
      -- 🎉 no goals
#align prime_spectrum.localization_away_open_embedding PrimeSpectrum.localization_away_openEmbedding

end BasicOpen

/-- The prime spectrum of a commutative ring is a compact topological space. -/
instance compactSpace : CompactSpace (PrimeSpectrum R) :=
  { isCompact_univ := by
      convert isCompact_basicOpen (1 : R)
      -- ⊢ Set.univ = ↑(basicOpen 1)
      rw [basicOpen_one, TopologicalSpace.Opens.coe_top] }
      -- 🎉 no goals

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
      -- ⊢ IsUnit (↑(algebraMap R (Localization.AtPrime x.asIdeal)) ↑{ val := a, proper …
      rw [← PrimeSpectrum.le_iff_specializes, ← asIdeal_le_asIdeal, ← SetLike.coe_subset_coe, ←
        Set.compl_subset_compl] at h
      exact (IsLocalization.map_units (Localization.AtPrime x.asIdeal)
        ⟨a, show a ∈ x.asIdeal.primeCompl from h ha⟩ : _))
#align prime_spectrum.localization_map_of_specializes PrimeSpectrum.localizationMapOfSpecializes

end PrimeSpectrum

namespace LocalRing

variable [LocalRing R]

/-- The closed point in the prime spectrum of a local ring. -/
def closedPoint : PrimeSpectrum R :=
  ⟨maximalIdeal R, (maximalIdeal.isMaximal R).isPrime⟩
#align local_ring.closed_point LocalRing.closedPoint

variable {R}

theorem isLocalRingHom_iff_comap_closedPoint {S : Type v} [CommRing S] [LocalRing S] (f : R →+* S) :
    IsLocalRingHom f ↔ PrimeSpectrum.comap f (closedPoint S) = closedPoint R := by
  -- Porting note : inline `this` does **not** work
  have := (local_hom_TFAE f).out 0 4
  -- ⊢ IsLocalRingHom f ↔ ↑(PrimeSpectrum.comap f) (closedPoint S) = closedPoint R
  rw [this, PrimeSpectrum.ext_iff]
  -- ⊢ Ideal.comap f (maximalIdeal S) = maximalIdeal R ↔ (↑(PrimeSpectrum.comap f)  …
  rfl
  -- 🎉 no goals
#align local_ring.is_local_ring_hom_iff_comap_closed_point LocalRing.isLocalRingHom_iff_comap_closedPoint

@[simp]
theorem comap_closedPoint {S : Type v} [CommRing S] [LocalRing S] (f : R →+* S) [IsLocalRingHom f] :
    PrimeSpectrum.comap f (closedPoint S) = closedPoint R :=
  (isLocalRingHom_iff_comap_closedPoint f).mp inferInstance
#align local_ring.comap_closed_point LocalRing.comap_closedPoint

theorem specializes_closedPoint (x : PrimeSpectrum R) : x ⤳ closedPoint R :=
  (PrimeSpectrum.le_iff_specializes _ _).mp (LocalRing.le_maximalIdeal x.2.1)
#align local_ring.specializes_closed_point LocalRing.specializes_closedPoint

theorem closedPoint_mem_iff (U : TopologicalSpace.Opens <| PrimeSpectrum R) :
    closedPoint R ∈ U ↔ U = ⊤ := by
  constructor
  -- ⊢ closedPoint R ∈ U → U = ⊤
  · rw [eq_top_iff]
    -- ⊢ closedPoint R ∈ U → ⊤ ≤ U
    exact fun h x _ => (specializes_closedPoint x).mem_open U.2 h
    -- 🎉 no goals
  · rintro rfl
    -- ⊢ closedPoint R ∈ ⊤
    trivial
    -- 🎉 no goals
#align local_ring.closed_point_mem_iff LocalRing.closedPoint_mem_iff

@[simp]
theorem PrimeSpectrum.comap_residue (x : PrimeSpectrum (ResidueField R)) :
    PrimeSpectrum.comap (residue R) x = closedPoint R := by
  rw [Subsingleton.elim x ⊥]
  -- ⊢ ↑(PrimeSpectrum.comap (residue R)) ⊥ = closedPoint R
  ext1
  -- ⊢ (↑(PrimeSpectrum.comap (residue R)) ⊥).asIdeal = (closedPoint R).asIdeal
  exact Ideal.mk_ker
  -- 🎉 no goals
#align local_ring.prime_spectrum.comap_residue LocalRing.PrimeSpectrum.comap_residue

end LocalRing
