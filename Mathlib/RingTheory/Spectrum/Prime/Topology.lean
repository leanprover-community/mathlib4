/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Order.Ring.Idempotent
import Mathlib.Order.Heyting.Hom
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.Tactic.StacksAttribute
import Mathlib.Topology.Constructible
import Mathlib.Topology.KrullDimension
import Mathlib.Topology.Spectral.Basic

/-!
# The Zariski topology on the prime spectrum of a commutative (semi)ring

## Conventions

We denote subsets of (semi)rings with `s`, `s'`, etc...
whereas we denote subsets of prime spectra with `t`, `t'`, etc...

## Inspiration/contributors

The contents of this file draw inspiration from <https://github.com/ramonfmir/lean-scheme>
which has contributions from Ramon Fernandez Mir, Kevin Buzzard, Kenny Lau,
and Chris Hughes (on an earlier repository).

## Main definitions

* `PrimeSpectrum.zariskiTopology`: the Zariski topology on the prime spectrum, whose closed sets
  are zero loci (`zeroLocus`).

* `PrimeSpectrum.basicOpen`: the complement of the zero locus of a single element.
  The `basicOpen`s form a topological basis of the Zariski topology:
  `PrimeSpectrum.isTopologicalBasis_basic_opens`.

* `PrimeSpectrum.comap`: the continuous map between prime spectra induced by a ring homomorphism.

* `IsLocalRing.closedPoint`: the maximal ideal of a local ring is the unique closed point in its
  prime spectrum.

## Main results

* `PrimeSpectrum.instSpectralSpace`: every prime spectrum is a spectral space, i.e. it is
  quasi-compact, sober (in particular T0), quasi-separated, and its compact open subsets form
  a topological basis.

* `PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero`: the prime spectrum of a
  commutative semiring is discrete iff it is finite and the semiring has zero Krull dimension
  or is trivial.

* `PrimeSpectrum.localization_comap_range`, `PrimeSpectrum.localization_comap_isEmbedding`:
  localization at a submonoid of a commutative semiring induces an embedding between the prime
  spectra, with range consisting of prime ideals disjoint from the submonoid.

* `PrimeSpectrum.localization_away_comap_range`: for localization away from an element, the
  range of the embedding is the `basicOpen` associated to the element.

* `PrimeSpectrum.comap_isEmbedding_of_surjective`: a surjective ring homomorphism between
  commutative semirings induces an embedding between the prime spectra.

* `PrimeSpectrum.isClosedEmbedding_comap_of_surjective`: a surjective ring homomorphism between
  commutative rings induces a closed embedding between the prime spectra.

* `PrimeSpectrum.primeSpectrumProdHomeo`: the prime spectrum of a product semiring is homeomorphic
  to the disjoint union of the prime spectra.

* `PrimeSpectrum.stableUnderSpecialization_range_iff`: the range of `PrimeSpectrum.comap _` is
  closed iff it is stable under specialization.

* `PrimeSpectrum.denseRange_comap_iff_minimalPrimes`,
  `PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical`: the range of `comap f` is dense
  iff it contains all minimal primes, iff the kernel of `f` is contained in the nilradical.

* `PrimeSpectrum.isClosedMap_comap_of_isIntegral`: `comap f` is a closed map if `f` is integral.

* `PrimeSpectrum.isIntegral_of_isClosedMap_comap_mapRingHom`: `f : R →+* S` is integral if
  `comap (Polynomial.mapRingHom f : R[X] →+* S[X])` is a closed map.

In the prime spectrum of a commutative semiring:

* `PrimeSpectrum.isClosed_iff_zeroLocus_radical_ideal`, `PrimeSpectrum.isRadical_vanishingIdeal`,
  `PrimeSpectrum.zeroLocus_eq_iff`, `PrimeSpectrum.vanishingIdeal_anti_mono_iff`:
  closed subsets correspond to radical ideals.

* `PrimeSpectrum.isClosed_singleton_iff_isMaximal`: closed points correspond to maximal ideals.

* `PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime`: irreducible closed subsets correspond
  to prime ideals.

* `minimalPrimes.equivIrreducibleComponents`: irreducible components correspond to minimal primes.

* `PrimeSpectrum.mulZeroAddOneEquivClopens`: clopen subsets correspond to pairs of elements
  that add up to 1 and multiply to 0 in the semiring.

* `PrimeSpectrum.isIdempotentElemEquivClopens`: (if the semiring is a ring) clopen subsets
  correspond to idempotents in the ring.

-/

open Topology

noncomputable section

universe u v

variable (R : Type u) (S : Type v)

namespace PrimeSpectrum

section CommSemiring

variable [CommSemiring R] [CommSemiring S]
variable {R S}

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

theorem isOpen_iff (U : Set (PrimeSpectrum R)) : IsOpen U ↔ ∃ s, Uᶜ = zeroLocus s := by
  simp only [@eq_comm _ Uᶜ]; rfl

theorem isClosed_iff_zeroLocus (Z : Set (PrimeSpectrum R)) : IsClosed Z ↔ ∃ s, Z = zeroLocus s := by
  rw [← isOpen_compl_iff, isOpen_iff, compl_compl]

theorem isClosed_iff_zeroLocus_ideal (Z : Set (PrimeSpectrum R)) :
    IsClosed Z ↔ ∃ I : Ideal R, Z = zeroLocus I :=
  (isClosed_iff_zeroLocus _).trans
    ⟨fun ⟨s, hs⟩ => ⟨_, (zeroLocus_span s).substr hs⟩, fun ⟨I, hI⟩ => ⟨I, hI⟩⟩

theorem isClosed_iff_zeroLocus_radical_ideal (Z : Set (PrimeSpectrum R)) :
    IsClosed Z ↔ ∃ I : Ideal R, I.IsRadical ∧ Z = zeroLocus I :=
  (isClosed_iff_zeroLocus_ideal _).trans
    ⟨fun ⟨I, hI⟩ => ⟨_, I.radical_isRadical, (zeroLocus_radical I).substr hI⟩, fun ⟨I, _, hI⟩ =>
      ⟨I, hI⟩⟩

theorem isClosed_zeroLocus (s : Set R) : IsClosed (zeroLocus s) := by
  rw [isClosed_iff_zeroLocus]
  exact ⟨s, rfl⟩

theorem zeroLocus_vanishingIdeal_eq_closure (t : Set (PrimeSpectrum R)) :
    zeroLocus (vanishingIdeal t : Set R) = closure t := by
  rcases isClosed_iff_zeroLocus (closure t) |>.mp isClosed_closure with ⟨I, hI⟩
  rw [subset_antisymm_iff, (isClosed_zeroLocus _).closure_subset_iff, hI,
      subset_zeroLocus_iff_subset_vanishingIdeal, (gc R).u_l_u_eq_u,
      ← subset_zeroLocus_iff_subset_vanishingIdeal, ← hI]
  exact ⟨subset_closure, subset_zeroLocus_vanishingIdeal t⟩

theorem vanishingIdeal_closure (t : Set (PrimeSpectrum R)) :
    vanishingIdeal (closure t) = vanishingIdeal t :=
  zeroLocus_vanishingIdeal_eq_closure t ▸ (gc R).u_l_u_eq_u t

theorem closure_singleton (x) : closure ({x} : Set (PrimeSpectrum R)) = zeroLocus x.asIdeal := by
  rw [← zeroLocus_vanishingIdeal_eq_closure, vanishingIdeal_singleton]

theorem isClosed_singleton_iff_isMaximal (x : PrimeSpectrum R) :
    IsClosed ({x} : Set (PrimeSpectrum R)) ↔ x.asIdeal.IsMaximal := by
  rw [← closure_subset_iff_isClosed, ← zeroLocus_vanishingIdeal_eq_closure,
      vanishingIdeal_singleton]
  constructor <;> intro H
  · rcases x.asIdeal.exists_le_maximal x.2.1 with ⟨m, hm, hxm⟩
    exact (congr_arg asIdeal (@H ⟨m, hm.isPrime⟩ hxm)) ▸ hm
  · exact fun p hp ↦ PrimeSpectrum.ext (H.eq_of_le p.2.1 hp).symm

theorem isRadical_vanishingIdeal (s : Set (PrimeSpectrum R)) : (vanishingIdeal s).IsRadical := by
  rw [← vanishingIdeal_closure, ← zeroLocus_vanishingIdeal_eq_closure,
    vanishingIdeal_zeroLocus_eq_radical]
  apply Ideal.radical_isRadical

theorem zeroLocus_eq_iff {I J : Ideal R} :
    zeroLocus (I : Set R) = zeroLocus J ↔ I.radical = J.radical := by
  constructor
  · intro h; simp_rw [← vanishingIdeal_zeroLocus_eq_radical, h]
  · intro h; rw [← zeroLocus_radical, h, zeroLocus_radical]

theorem vanishingIdeal_anti_mono_iff {s t : Set (PrimeSpectrum R)} (ht : IsClosed t) :
    s ⊆ t ↔ vanishingIdeal t ≤ vanishingIdeal s :=
  ⟨vanishingIdeal_anti_mono, fun h => by
    rw [← ht.closure_subset_iff, ← ht.closure_eq]
    convert ← zeroLocus_anti_mono_ideal h <;> apply zeroLocus_vanishingIdeal_eq_closure⟩

theorem vanishingIdeal_strict_anti_mono_iff {s t : Set (PrimeSpectrum R)} (hs : IsClosed s)
    (ht : IsClosed t) : s ⊂ t ↔ vanishingIdeal t < vanishingIdeal s := by
  rw [Set.ssubset_def, vanishingIdeal_anti_mono_iff hs, vanishingIdeal_anti_mono_iff ht,
    lt_iff_le_not_ge]

/-- The antitone order embedding of closed subsets of `Spec R` into ideals of `R`. -/
def closedsEmbedding (R : Type*) [CommSemiring R] :
    (TopologicalSpace.Closeds <| PrimeSpectrum R)ᵒᵈ ↪o Ideal R :=
  OrderEmbedding.ofMapLEIff (fun s => vanishingIdeal ↑(OrderDual.ofDual s)) fun s _ =>
    (vanishingIdeal_anti_mono_iff s.2).symm

theorem t1Space_iff_isField [IsDomain R] : T1Space (PrimeSpectrum R) ↔ IsField R := by
  refine ⟨?_, fun h => ?_⟩
  · intro h
    have hbot : Ideal.IsPrime (⊥ : Ideal R) := Ideal.bot_prime
    exact
      Classical.not_not.1
        (mt
          (Ring.ne_bot_of_isMaximal_of_not_isField <|
            (isClosed_singleton_iff_isMaximal _).1 (T1Space.t1 ⟨⊥, hbot⟩))
          (by simp))
  · refine ⟨fun x => (isClosed_singleton_iff_isMaximal x).2 ?_⟩
    by_cases hx : x.asIdeal = ⊥
    · letI := h.toSemifield
      exact hx.symm ▸ Ideal.bot_isMaximal
    · exact absurd h (Ring.not_isField_iff_exists_prime.2 ⟨x.asIdeal, ⟨hx, x.2⟩⟩)

local notation "Z(" a ")" => zeroLocus (a : Set R)

theorem isIrreducible_zeroLocus_iff_of_radical (I : Ideal R) (hI : I.IsRadical) :
    IsIrreducible (zeroLocus (I : Set R)) ↔ I.IsPrime := by
  rw [Ideal.isPrime_iff, IsIrreducible]
  apply and_congr
  · rw [Set.nonempty_iff_ne_empty, Ne, zeroLocus_empty_iff_eq_top]
  · trans ∀ x y : Ideal R, Z(I) ⊆ Z(x) ∪ Z(y) → Z(I) ⊆ Z(x) ∨ Z(I) ⊆ Z(y)
    · simp_rw [isPreirreducible_iff_isClosed_union_isClosed, isClosed_iff_zeroLocus_ideal]
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

theorem isIrreducible_zeroLocus_iff (I : Ideal R) :
    IsIrreducible (zeroLocus (I : Set R)) ↔ I.radical.IsPrime :=
  zeroLocus_radical I ▸ isIrreducible_zeroLocus_iff_of_radical _ I.radical_isRadical

theorem isIrreducible_iff_vanishingIdeal_isPrime {s : Set (PrimeSpectrum R)} :
    IsIrreducible s ↔ (vanishingIdeal s).IsPrime := by
  rw [← isIrreducible_iff_closure, ← zeroLocus_vanishingIdeal_eq_closure,
    isIrreducible_zeroLocus_iff_of_radical _ (isRadical_vanishingIdeal s)]

lemma vanishingIdeal_isIrreducible :
    vanishingIdeal (R := R) '' {s | IsIrreducible s} = {P | P.IsPrime} :=
  Set.ext fun I ↦ ⟨fun ⟨_, hs, e⟩ ↦ e ▸ isIrreducible_iff_vanishingIdeal_isPrime.mp hs,
    fun h ↦ ⟨zeroLocus I, (isIrreducible_zeroLocus_iff_of_radical _ h.isRadical).mpr h,
      (vanishingIdeal_zeroLocus_eq_radical I).trans h.radical⟩⟩

lemma vanishingIdeal_isClosed_isIrreducible :
    vanishingIdeal (R := R) '' {s | IsClosed s ∧ IsIrreducible s} = {P | P.IsPrime} := by
  refine (subset_antisymm ?_ ?_).trans vanishingIdeal_isIrreducible
  · exact Set.image_mono fun _ ↦ And.right
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

/-- The prime spectrum of a commutative semiring has discrete Zariski topology iff it is finite and
the semiring has Krull dimension zero or is trivial. -/
theorem discreteTopology_iff_finite_and_krullDimLE_zero : DiscreteTopology (PrimeSpectrum R) ↔
    Finite (PrimeSpectrum R) ∧ Ring.KrullDimLE 0 R :=
  ⟨fun _ ↦ ⟨finite_of_compact_of_discrete, .mk₀ fun I h ↦ isClosed_singleton_iff_isMaximal ⟨I, h⟩
    |>.mp <| discreteTopology_iff_forall_isClosed.mp ‹_› _⟩, fun ⟨_, _⟩ ↦
    .of_finite_of_isClosed_singleton fun p ↦ (isClosed_singleton_iff_isMaximal p).mpr inferInstance⟩

@[deprecated discreteTopology_iff_finite_and_krullDimLE_zero (since := "2025-02-05")]
theorem discreteTopology_iff_finite_and_isPrime_imp_isMaximal :
    DiscreteTopology (PrimeSpectrum R) ↔
    Finite (PrimeSpectrum R) ∧ ∀ I : Ideal R, I.IsPrime → I.IsMaximal := by
  rw [discreteTopology_iff_finite_and_krullDimLE_zero, Ring.krullDimLE_zero_iff]

/-- The prime spectrum of a semiring has discrete Zariski topology iff there are only
finitely many maximal ideals and their intersection is contained in the nilradical. -/
theorem discreteTopology_iff_finite_isMaximal_and_sInf_le_nilradical :
    letI s := {I : Ideal R | I.IsMaximal}
    DiscreteTopology (PrimeSpectrum R) ↔ Finite s ∧ sInf s ≤ nilradical R := by
  rw [discreteTopology_iff_finite_and_krullDimLE_zero, Ring.krullDimLE_zero_iff,
    (equivSubtype R).finite_iff, ← Set.coe_setOf, Set.finite_coe_iff, Set.finite_coe_iff]
  refine ⟨fun h ↦ ⟨h.1.subset fun _ h ↦ h.isPrime, nilradical_eq_sInf R ▸ sInf_le_sInf h.2⟩,
    fun ⟨fin, le⟩ ↦ ?_⟩
  have hpm (I : Ideal R) (hI : I.IsPrime): I.IsMaximal := by
    replace le := le.trans (nilradical_le_prime I)
    rw [← fin.coe_toFinset, ← Finset.inf_id_eq_sInf, hI.inf_le'] at le
    have ⟨M, hM, hMI⟩ := le
    rw [fin.mem_toFinset] at hM
    rwa [← hM.eq_of_le hI.1 hMI]
  exact ⟨fin.subset hpm, hpm⟩

theorem discreteTopology_of_toLocalization_surjective
    (surj : Function.Surjective (toPiLocalization R)) :
    DiscreteTopology (PrimeSpectrum R) :=
  discreteTopology_iff_finite_and_krullDimLE_zero.mpr ⟨finite_of_toPiLocalization_surjective
    surj, .mk₀ fun I prime ↦ isMaximal_of_toPiLocalization_surjective surj ⟨I, prime⟩⟩

section Comap

variable {S' : Type*} [CommSemiring S']

/-- The continuous function between prime spectra of commutative (semi)rings induced by a ring
homomorphism. -/
def comap (f : R →+* S) : C(PrimeSpectrum S, PrimeSpectrum R) where
  toFun := f.specComap
  continuous_toFun := by
    simp only [continuous_iff_isClosed, isClosed_iff_zeroLocus]
    rintro _ ⟨s, rfl⟩
    exact ⟨_, preimage_specComap_zeroLocus_aux f s⟩

lemma coe_comap (f : R →+* S) : comap f = f.specComap := rfl

lemma comap_apply (f : R →+* S) (x) : comap f x = f.specComap x := rfl

variable (f : R →+* S)

@[simp]
theorem comap_asIdeal (y : PrimeSpectrum S) : (comap f y).asIdeal = Ideal.comap f y.asIdeal :=
  rfl

@[simp]
theorem comap_id : comap (RingHom.id R) = ContinuousMap.id _ := by
  ext
  rfl

@[simp]
theorem comap_comp (f : R →+* S) (g : S →+* S') : comap (g.comp f) = (comap f).comp (comap g) :=
  rfl

theorem comap_comp_apply (f : R →+* S) (g : S →+* S') (x : PrimeSpectrum S') :
    PrimeSpectrum.comap (g.comp f) x = (PrimeSpectrum.comap f) (PrimeSpectrum.comap g x) :=
  rfl

@[simp]
theorem preimage_comap_zeroLocus (s : Set R) : comap f ⁻¹' zeroLocus s = zeroLocus (f '' s) :=
  preimage_specComap_zeroLocus_aux f s

theorem comap_injective_of_surjective (f : R →+* S) (hf : Function.Surjective f) :
    Function.Injective (comap f) := fun _ _ h => specComap_injective_of_surjective _ hf h

variable (S)

theorem localization_specComap_injective [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    Function.Injective (algebraMap R S).specComap := by
  intro p q h
  replace h := _root_.congr_arg (fun x : PrimeSpectrum R => Ideal.map (algebraMap R S) x.asIdeal) h
  dsimp only [RingHom.specComap] at h
  rw [IsLocalization.map_comap M S, IsLocalization.map_comap M S] at h
  ext1
  exact h

theorem localization_specComap_range [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    Set.range (algebraMap R S).specComap = { p | Disjoint (M : Set R) p.asIdeal } := by
  refine Set.ext fun x ↦ ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨p, rfl⟩
    exact ((IsLocalization.isPrime_iff_isPrime_disjoint ..).mp p.2).2
  · use ⟨x.asIdeal.map (algebraMap R S), IsLocalization.isPrime_of_isPrime_disjoint M S _ x.2 h⟩
    ext1
    exact IsLocalization.comap_map_of_isPrime_disjoint M S _ x.2 h

theorem localization_comap_isInducing [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    IsInducing (comap (algebraMap R S)) := by
  refine ⟨TopologicalSpace.ext_isClosed fun Z ↦ ?_⟩
  simp_rw [isClosed_induced_iff, isClosed_iff_zeroLocus, @eq_comm _ _ (zeroLocus _),
    exists_exists_eq_and, preimage_comap_zeroLocus]
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨(Ideal.span s).comap (algebraMap R S), ?_⟩
    rw [← zeroLocus_span, ← zeroLocus_span s, ← Ideal.map, IsLocalization.map_comap M S]
  · rintro ⟨s, rfl⟩
    exact ⟨_, rfl⟩

theorem localization_comap_injective [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    Function.Injective (comap (algebraMap R S)) :=
  fun _ _ h => localization_specComap_injective S M h

theorem localization_comap_isEmbedding [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    IsEmbedding (comap (algebraMap R S)) :=
  ⟨localization_comap_isInducing S M, localization_comap_injective S M⟩

theorem localization_comap_range [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    Set.range (comap (algebraMap R S)) = { p | Disjoint (M : Set R) p.asIdeal } :=
  localization_specComap_range ..

open Function RingHom

theorem comap_isInducing_of_surjective (hf : Surjective f) : IsInducing (comap f) where
  eq_induced := by
    simp only [TopologicalSpace.ext_iff, ← isClosed_compl_iff, isClosed_iff_zeroLocus,
      isClosed_induced_iff]
    refine fun s =>
      ⟨fun ⟨F, hF⟩ =>
        ⟨zeroLocus (f ⁻¹' F), ⟨f ⁻¹' F, rfl⟩, by
          rw [preimage_comap_zeroLocus, Function.Surjective.image_preimage hf, hF]⟩,
        ?_⟩
    rintro ⟨-, ⟨F, rfl⟩, hF⟩
    exact ⟨f '' F, hF.symm.trans (preimage_comap_zeroLocus f F)⟩

/-- The embedding has closed range if the domain (and therefore the codomain) is a ring,
  see `PrimeSpectrum.isClosedEmbedding_comap_of_surjective`.
  On the other hand, `comap (Nat.castRingHom (ZMod 2))` does not have closed range. -/
theorem isEmbedding_comap_of_surjective (hf : Surjective f) : IsEmbedding (comap f) :=
  (isEmbedding_iff _).2 ⟨comap_isInducing_of_surjective _ _ hf, comap_injective_of_surjective f hf⟩

end Comap

/-- Homeomorphism between prime spectra induced by an isomorphism of semirings. -/
def homeomorphOfRingEquiv (e : R ≃+* S) : PrimeSpectrum R ≃ₜ PrimeSpectrum S where
  toFun := comap (e.symm : S →+* R)
  invFun := comap (e : R →+* S)
  left_inv _ := (comap_comp_apply ..).symm.trans (by simp)
  right_inv _ := (comap_comp_apply ..).symm.trans (by simp)

lemma isHomeomorph_comap_of_bijective {f : R →+* S} (hf : Function.Bijective f) :
    IsHomeomorph (comap f) := (homeomorphOfRingEquiv (.ofBijective f hf)).symm.isHomeomorph

end CommSemiring

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

theorem image_comap_zeroLocus_eq_zeroLocus_comap (hf : Surjective f) (I : Ideal S) :
    comap f '' zeroLocus I = zeroLocus (I.comap f) :=
  image_specComap_zeroLocus_eq_zeroLocus_comap _ f hf I

theorem range_comap_of_surjective (hf : Surjective f) :
    Set.range (comap f) = zeroLocus (ker f) :=
  range_specComap_of_surjective _ f hf

lemma comap_quotientMk_bijective_of_le_nilradical {I : Ideal R} (hle : I ≤ nilradical R) :
    Function.Bijective (comap <| Ideal.Quotient.mk I) := by
  refine ⟨comap_injective_of_surjective _ Ideal.Quotient.mk_surjective, ?_⟩
  simpa [← Set.range_eq_univ, range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    zeroLocus_eq_univ_iff]

theorem isClosed_range_comap_of_surjective (hf : Surjective f) :
    IsClosed (Set.range (comap f)) := by
  rw [range_comap_of_surjective _ f hf]
  exact isClosed_zeroLocus _

lemma isClosedEmbedding_comap_of_surjective (hf : Surjective f) : IsClosedEmbedding (comap f) where
  toIsInducing := comap_isInducing_of_surjective S f hf
  injective := comap_injective_of_surjective f hf
  isClosed_range := isClosed_range_comap_of_surjective S f hf

end SpecOfSurjective

section SpecProd

variable {R S} [CommSemiring R] [CommSemiring S]

lemma primeSpectrumProd_symm_inl (x) :
    (primeSpectrumProd R S).symm (.inl x) = comap (RingHom.fst R S) x := by
  ext; simp [Ideal.prod]

lemma primeSpectrumProd_symm_inr (x) :
    (primeSpectrumProd R S).symm (.inr x) = comap (RingHom.snd R S) x := by
  ext; simp [Ideal.prod]

lemma range_comap_fst :
    Set.range (comap (RingHom.fst R S)) = zeroLocus (RingHom.ker (RingHom.fst R S)) := by
  refine Set.ext fun p ↦ ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨I, hI, rfl⟩; exact Ideal.comap_mono bot_le
  obtain ⟨p, hp, eq⟩ | ⟨p, hp, eq⟩ := p.1.ideal_prod_prime.mp p.2
  · exact ⟨⟨p, hp⟩, PrimeSpectrum.ext <| by simpa [Ideal.prod] using eq.symm⟩
  · refine (hp.ne_top <| (Ideal.eq_top_iff_one _).mpr ?_).elim
    simpa [eq] using h (show (0, 1) ∈ RingHom.ker (RingHom.fst R S) by simp)

lemma range_comap_snd :
    Set.range (comap (RingHom.snd R S)) = zeroLocus (RingHom.ker (RingHom.snd R S)) := by
  refine Set.ext fun p ↦ ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨I, hI, rfl⟩; exact Ideal.comap_mono bot_le
  obtain ⟨p, hp, eq⟩ | ⟨p, hp, eq⟩ := p.1.ideal_prod_prime.mp p.2
  · refine (hp.ne_top <| (Ideal.eq_top_iff_one _).mpr ?_).elim
    simpa [eq] using h (show (1, 0) ∈ RingHom.ker (RingHom.snd R S) by simp)
  · exact ⟨⟨p, hp⟩, PrimeSpectrum.ext <| by simpa [Ideal.prod] using eq.symm⟩

lemma isClosedEmbedding_comap_fst : IsClosedEmbedding (comap (RingHom.fst R S)) :=
  (isClosedEmbedding_iff _).mpr ⟨isEmbedding_comap_of_surjective _ _ Prod.fst_surjective, by
    simp_rw [range_comap_fst, isClosed_zeroLocus]⟩

lemma isClosedEmbedding_comap_snd : IsClosedEmbedding (comap (RingHom.snd R S)) :=
  (isClosedEmbedding_iff _).mpr ⟨isEmbedding_comap_of_surjective _ _ Prod.snd_surjective, by
    simp_rw [range_comap_snd, isClosed_zeroLocus]⟩

/-- The prime spectrum of `R × S` is homeomorphic
to the disjoint union of `PrimeSpectrum R` and `PrimeSpectrum S`. -/
noncomputable
def primeSpectrumProdHomeo :
    PrimeSpectrum (R × S) ≃ₜ PrimeSpectrum R ⊕ PrimeSpectrum S := by
  refine ((primeSpectrumProd R S).symm.toHomeomorphOfIsInducing ?_).symm
  refine (IsClosedEmbedding.of_continuous_injective_isClosedMap ?_
    (Equiv.injective _) ?_).isInducing
  · rw [continuous_sum_dom]
    simp only [Function.comp_def, primeSpectrumProd_symm_inl, primeSpectrumProd_symm_inr]
    exact ⟨(comap _).2, (comap _).2⟩
  · simp_rw [isClosedMap_sum, primeSpectrumProd_symm_inl, primeSpectrumProd_symm_inr]
    exact ⟨isClosedEmbedding_comap_fst.isClosedMap, isClosedEmbedding_comap_snd.isClosedMap⟩

end SpecProd

section CommSemiring

variable [CommSemiring R] [CommSemiring S]
variable {R S}

section BasicOpen

/-- `basicOpen r` is the open subset containing all prime ideals not containing `r`. -/
def basicOpen (r : R) : TopologicalSpace.Opens (PrimeSpectrum R) where
  carrier := { x | r ∉ x.asIdeal }
  is_open' := ⟨{r}, Set.ext fun _ => Set.singleton_subset_iff.trans <| Classical.not_not.symm⟩

@[simp]
theorem mem_basicOpen (f : R) (x : PrimeSpectrum R) : x ∈ basicOpen f ↔ f ∉ x.asIdeal :=
  Iff.rfl

theorem isOpen_basicOpen {a : R} : IsOpen (basicOpen a : Set (PrimeSpectrum R)) :=
  (basicOpen a).isOpen

@[simp]
theorem basicOpen_eq_zeroLocus_compl (r : R) :
    (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ :=
  Set.ext fun x => by simp only [SetLike.mem_coe, mem_basicOpen, Set.mem_compl_iff, mem_zeroLocus,
    Set.singleton_subset_iff]

@[simp]
theorem basicOpen_one : basicOpen (1 : R) = ⊤ :=
  TopologicalSpace.Opens.ext <| by simp

@[simp]
theorem basicOpen_zero : basicOpen (0 : R) = ⊥ :=
  TopologicalSpace.Opens.ext <| by simp

theorem basicOpen_le_basicOpen_iff (f g : R) :
    basicOpen f ≤ basicOpen g ↔ f ∈ (Ideal.span ({g} : Set R)).radical := by
  rw [← SetLike.coe_subset_coe, basicOpen_eq_zeroLocus_compl, basicOpen_eq_zeroLocus_compl,
    Set.compl_subset_compl, zeroLocus_subset_zeroLocus_singleton_iff]

theorem basicOpen_le_basicOpen_iff_algebraMap_isUnit {f g : R} [Algebra R S]
    [IsLocalization.Away f S] : basicOpen f ≤ basicOpen g ↔ IsUnit (algebraMap R S g) := by
  simp_rw [basicOpen_le_basicOpen_iff, Ideal.mem_radical_iff, Ideal.mem_span_singleton,
    IsLocalization.Away.algebraMap_isUnit_iff f]

theorem basicOpen_mul (f g : R) : basicOpen (f * g) = basicOpen f ⊓ basicOpen g :=
  TopologicalSpace.Opens.ext <| by simp [zeroLocus_singleton_mul]

theorem basicOpen_mul_le_left (f g : R) : basicOpen (f * g) ≤ basicOpen f := by
  rw [basicOpen_mul f g]
  exact inf_le_left

theorem basicOpen_mul_le_right (f g : R) : basicOpen (f * g) ≤ basicOpen g := by
  rw [basicOpen_mul f g]
  exact inf_le_right

@[simp]
theorem basicOpen_pow (f : R) (n : ℕ) (hn : 0 < n) : basicOpen (f ^ n) = basicOpen f :=
  TopologicalSpace.Opens.ext <| by simpa using zeroLocus_singleton_pow f n hn

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

theorem eq_biUnion_of_isOpen {s : Set (PrimeSpectrum R)} (hs : IsOpen s) :
    s = ⋃ (r : R) (_ : ↑(basicOpen r) ⊆ s), basicOpen r :=
  (isTopologicalBasis_basic_opens.open_eq_sUnion' hs).trans <| by aesop

theorem isBasis_basic_opens : TopologicalSpace.Opens.IsBasis (Set.range (@basicOpen R _)) := by
  unfold TopologicalSpace.Opens.IsBasis
  convert isTopologicalBasis_basic_opens (R := R)
  rw [← Set.range_comp]
  rfl

@[simp]
theorem basicOpen_eq_bot_iff (f : R) : basicOpen f = ⊥ ↔ IsNilpotent f := by
  rw [← TopologicalSpace.Opens.coe_inj, basicOpen_eq_zeroLocus_compl]
  simp only [Set.eq_univ_iff_forall, Set.singleton_subset_iff, TopologicalSpace.Opens.coe_bot,
    nilpotent_iff_mem_prime, Set.compl_empty_iff, mem_zeroLocus, SetLike.mem_coe]
  exact ⟨fun h I hI => h ⟨I, hI⟩, fun h ⟨I, hI⟩ => h I hI⟩

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

theorem localization_away_isOpenEmbedding (S : Type v) [CommSemiring S] [Algebra R S] (r : R)
    [IsLocalization.Away r S] : IsOpenEmbedding (comap (algebraMap R S)) where
  toIsEmbedding := localization_comap_isEmbedding S (Submonoid.powers r)
  isOpen_range := by
    rw [localization_away_comap_range S r]
    exact isOpen_basicOpen

theorem isCompact_basicOpen (f : R) : IsCompact (basicOpen f : Set (PrimeSpectrum R)) := by
  rw [← localization_away_comap_range (Localization (Submonoid.powers f))]
  exact isCompact_range (map_continuous _)

lemma comap_basicOpen (f : R →+* S) (x : R) :
    TopologicalSpace.Opens.comap (comap f) (basicOpen x) = basicOpen (f x) :=
  rfl

open TopologicalSpace in
lemma iSup_basicOpen_eq_top_iff {ι : Type*} {f : ι → R} :
    (⨆ i : ι, PrimeSpectrum.basicOpen (f i)) = ⊤ ↔ Ideal.span (Set.range f) = ⊤ := by
  rw [SetLike.ext'_iff, Opens.coe_iSup]
  simp only [PrimeSpectrum.basicOpen_eq_zeroLocus_compl, Opens.coe_top, ← Set.compl_iInter,
    ← PrimeSpectrum.zeroLocus_iUnion]
  rw [← PrimeSpectrum.zeroLocus_empty_iff_eq_top, compl_involutive.eq_iff]
  simp only [Set.iUnion_singleton_eq_range, Set.compl_univ, PrimeSpectrum.zeroLocus_span]

lemma iSup_basicOpen_eq_top_iff' {s : Set R} :
    (⨆ i ∈ s, PrimeSpectrum.basicOpen i) = ⊤ ↔ Ideal.span s = ⊤ := by
  conv_rhs => rw [← Subtype.range_val (s := s), ← iSup_basicOpen_eq_top_iff]
  simp

theorem isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton [Algebra R S]
    {f : R} {p : PrimeSpectrum R} (h : (basicOpen f).1 = {p}) :
    IsLocalization.Away f S ↔ IsLocalization.AtPrime S p.1 :=
  have : IsLocalization.AtPrime (Localization.Away f) p.1 := by
    refine .of_le_of_exists_dvd (.powers f) _
      (Submonoid.powers_le.mpr <| by apply h ▸ Set.mem_singleton p) fun r hr ↦ ?_
    contrapose! hr
    simp_rw [← Ideal.mem_span_singleton] at hr
    have ⟨q, prime, le, disj⟩ := Ideal.exists_le_prime_disjoint (Ideal.span {r})
      (.powers f) (Set.disjoint_right.mpr hr)
    have : ⟨q, prime⟩ ∈ (basicOpen f).1 := Set.disjoint_right.mp disj (Submonoid.mem_powers f)
    rw [h, Set.mem_singleton_iff] at this
    rw [← this]
    exact not_not.mpr (q.span_singleton_le_iff_mem.mp le)
  IsLocalization.isLocalization_iff_of_isLocalization _ _ (Localization.Away f)

open Localization Polynomial Set in
lemma range_comap_algebraMap_localization_compl_eq_range_comap_quotientMk
    {R : Type*} [CommRing R] (c : R) :
    letI := (mapRingHom (algebraMap R (Away c))).toAlgebra
    (range (comap (algebraMap R[X] (Away c)[X])))ᶜ
      = range (comap (mapRingHom (Ideal.Quotient.mk (.span {c})))) := by
  letI := (mapRingHom (algebraMap R (Away c))).toAlgebra
  have := Polynomial.isLocalization (.powers c) (Away c)
  rw [Submonoid.map_powers] at this
  have surj : Function.Surjective (mapRingHom (Ideal.Quotient.mk (.span {c}))) :=
    Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
  rw [range_comap_of_surjective _ _ surj, localization_away_comap_range _ (C c)]
  simp [Polynomial.ker_mapRingHom, Ideal.map_span]

instance : QuasiSeparatedSpace (PrimeSpectrum R) :=
  .of_isTopologicalBasis isTopologicalBasis_basic_opens fun i j ↦ by
    simpa [← TopologicalSpace.Opens.coe_inf, ← basicOpen_mul, -basicOpen_eq_zeroLocus_compl]
      using isCompact_basicOpen _

end BasicOpen

section DiscreteTopology

variable (R) [DiscreteTopology (PrimeSpectrum R)]

theorem toPiLocalization_surjective_of_discreteTopology :
    Function.Surjective (toPiLocalization R) := fun x ↦ by
  have (p : PrimeSpectrum R) : ∃ f, (basicOpen f : Set _) = {p} :=
    have ⟨_, ⟨f, rfl⟩, hpf, hfp⟩ := isTopologicalBasis_basic_opens.isOpen_iff.mp
      (isOpen_discrete {p}) p rfl
    ⟨f, hfp.antisymm <| Set.singleton_subset_iff.mpr hpf⟩
  choose f hf using this
  let e := Equiv.ofInjective f fun p q eq ↦ Set.singleton_injective (hf p ▸ eq ▸ hf q)
  have loc a : IsLocalization.AtPrime (Localization.Away a.1) (e.symm a).1 :=
    (isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton <| hf _).mp <| by
      simp_rw [e, Equiv.apply_ofInjective_symm]; infer_instance
  let algE a := IsLocalization.algEquiv (e.symm a).1.primeCompl
    (Localization.AtPrime (e.symm a).1) (Localization.Away a.1)
  have span_eq : Ideal.span (Set.range f) = ⊤ := iSup_basicOpen_eq_top_iff.mp <| top_unique
    fun p _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨p, (hf p).ge rfl⟩
  replace hf a : (basicOpen a.1 : Set _) = {e.symm a} := by
    simp_rw [e, ← hf, Equiv.apply_ofInjective_symm]
  obtain ⟨r, eq, -⟩ := Localization.existsUnique_algebraMap_eq_of_span_eq_top _ span_eq
    (fun a ↦ algE a (x _)) fun a b ↦ by
      obtain rfl | ne := eq_or_ne a b; · rfl
      have nil : IsNilpotent (a * b : R) := (basicOpen_eq_bot_iff _).mp <| by
        simp_rw [basicOpen_mul, SetLike.ext'_iff, TopologicalSpace.Opens.coe_inf, hf]
        exact bot_unique (fun _ ⟨ha, hb⟩ ↦ ne <| e.symm.injective (ha.symm.trans hb))
      apply (IsLocalization.subsingleton (M := .powers (a * b : R)) nil).elim
  refine ⟨r, funext fun I ↦ ?_⟩
  have := eq (e I)
  rwa [← AlgEquiv.symm_apply_eq, AlgEquiv.commutes, e.symm_apply_apply] at this

theorem maximalSpectrumToPiLocalization_surjective_of_discreteTopology :
    Function.Surjective (MaximalSpectrum.toPiLocalization R) := by
  rw [← piLocalizationToMaximal_comp_toPiLocalization]
  exact (piLocalizationToMaximal_surjective R).comp
    (toPiLocalization_surjective_of_discreteTopology R)

/-- If the prime spectrum of a commutative semiring R has discrete Zariski topology, then R is
canonically isomorphic to the product of its localizations at the (finitely many) maximal ideals. -/
@[stacks 00JA
"See also `PrimeSpectrum.discreteTopology_iff_finite_isMaximal_and_sInf_le_nilradical`."]
def _root_.MaximalSpectrum.toPiLocalizationEquiv :
    R ≃+* MaximalSpectrum.PiLocalization R :=
  .ofBijective _ ⟨MaximalSpectrum.toPiLocalization_injective R,
    maximalSpectrumToPiLocalization_surjective_of_discreteTopology R⟩

@[deprecated (since := "2025-02-12")] noncomputable alias
MaximalSpectrum.toPiLocalizationEquivtoLocalizationEquiv := MaximalSpectrum.toPiLocalizationEquiv

theorem discreteTopology_iff_toPiLocalization_surjective {R} [CommSemiring R] :
    DiscreteTopology (PrimeSpectrum R) ↔ Function.Surjective (toPiLocalization R) :=
  ⟨fun _ ↦ toPiLocalization_surjective_of_discreteTopology _,
    discreteTopology_of_toLocalization_surjective⟩

theorem discreteTopology_iff_toPiLocalization_bijective {R} [CommSemiring R] :
    DiscreteTopology (PrimeSpectrum R) ↔ Function.Bijective (toPiLocalization R) :=
  discreteTopology_iff_toPiLocalization_surjective.trans
    (and_iff_right <| toPiLocalization_injective _).symm

end DiscreteTopology

section Order

/-!
## The specialization order

We endow `PrimeSpectrum R` with a partial order, where `x ≤ y` if and only if `y ∈ closure {x}`.
-/

theorem le_iff_mem_closure (x y : PrimeSpectrum R) :
    x ≤ y ↔ y ∈ closure ({x} : Set (PrimeSpectrum R)) := by
  rw [← asIdeal_le_asIdeal, ← zeroLocus_vanishingIdeal_eq_closure, mem_zeroLocus,
    vanishingIdeal_singleton, SetLike.coe_subset_coe]

theorem le_iff_specializes (x y : PrimeSpectrum R) : x ≤ y ↔ x ⤳ y :=
  (le_iff_mem_closure x y).trans specializes_iff_mem_closure.symm

/-- `nhds` as an order embedding. -/
@[simps!]
def nhdsOrderEmbedding : PrimeSpectrum R ↪o Filter (PrimeSpectrum R) :=
  OrderEmbedding.ofMapLEIff nhds fun a b => (le_iff_specializes a b).symm

instance : T0Space (PrimeSpectrum R) :=
  ⟨nhdsOrderEmbedding.inj'⟩

instance : PrespectralSpace (PrimeSpectrum R) :=
  .of_isTopologicalBasis' isTopologicalBasis_basic_opens isCompact_basicOpen

instance : SpectralSpace (PrimeSpectrum R) where

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
        ⟨a, show a ∈ x.asIdeal.primeCompl from h ha⟩ :))

section stableUnderSpecialization

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)

lemma isClosed_image_of_stableUnderSpecialization
    (Z : Set (PrimeSpectrum S)) (hZ : IsClosed Z)
    (hf : StableUnderSpecialization (comap f '' Z)) :
    IsClosed (comap f '' Z) := by
  obtain ⟨I, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Z).mp hZ
  refine (isClosed_iff_zeroLocus _).mpr ⟨I.comap f, le_antisymm ?_ fun p hp ↦ ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact Ideal.comap_mono hq
  · obtain ⟨q, hqI, hq, hqle⟩ := p.asIdeal.exists_ideal_comap_le_prime I hp
    exact hf ((le_iff_specializes ⟨q.comap f, inferInstance⟩ p).mp hqle) ⟨⟨q, hq⟩, hqI, rfl⟩

@[stacks 00HY]
lemma isClosed_range_of_stableUnderSpecialization
    (hf : StableUnderSpecialization (Set.range (comap f))) :
    IsClosed (Set.range (comap f)) := by
  rw [← Set.image_univ] at hf ⊢
  exact isClosed_image_of_stableUnderSpecialization _ _ isClosed_univ hf

variable {f} in
@[stacks 00HY]
lemma stableUnderSpecialization_range_iff :
    StableUnderSpecialization (Set.range (comap f)) ↔ IsClosed (Set.range (comap f)) :=
  ⟨isClosed_range_of_stableUnderSpecialization f, fun h ↦ h.stableUnderSpecialization⟩

lemma stableUnderSpecialization_image_iff
    (Z : Set (PrimeSpectrum S)) (hZ : IsClosed Z) :
    StableUnderSpecialization (comap f '' Z) ↔ IsClosed (comap f '' Z) :=
  ⟨isClosed_image_of_stableUnderSpecialization f Z hZ, fun h ↦ h.stableUnderSpecialization⟩

end stableUnderSpecialization

section IsQuotientMap

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {f : R →+* S}
  (h₁ : Function.Surjective (comap f))

include h₁

/-- If `f : Spec S → Spec R` is specializing and surjective, the topology on `Spec R` is the
quotient topology induced by `f`. -/
lemma isQuotientMap_of_specializingMap (h₂ : SpecializingMap (comap f)) :
    Topology.IsQuotientMap (comap f) := by
  rw [Topology.isQuotientMap_iff_isClosed]
  exact ⟨h₁, fun s ↦ ⟨fun hs ↦ hs.preimage (comap f).continuous,
    fun hsc ↦ Set.image_preimage_eq s h₁ ▸ isClosed_image_of_stableUnderSpecialization _ _ hsc
      (h₂.stableUnderSpecialization_image hsc.stableUnderSpecialization)⟩⟩

/-- If `f : Spec S → Spec R` is generalizing and surjective, the topology on `Spec R` is the
quotient topology induced by `f`. -/
lemma isQuotientMap_of_generalizingMap (h₂ : GeneralizingMap (comap f)) :
    Topology.IsQuotientMap (comap f) := by
  rw [Topology.isQuotientMap_iff_isClosed]
  refine ⟨h₁, fun s ↦ ⟨fun hs ↦ hs.preimage (comap f).continuous,
    fun hsc ↦ Set.image_preimage_eq s h₁ ▸ ?_⟩⟩
  apply isClosed_image_of_stableUnderSpecialization _ _ hsc
  rw [Set.image_preimage_eq s h₁, ← stableUnderGeneralization_compl_iff]
  convert h₂.stableUnderGeneralization_image hsc.isOpen_compl.stableUnderGeneralization
  rw [← Set.preimage_compl, Set.image_preimage_eq _ h₁]

end IsQuotientMap

section denseRange

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)

lemma vanishingIdeal_range_comap :
    vanishingIdeal (Set.range (comap f)) = (RingHom.ker f).radical := by
  ext x
  rw [RingHom.ker_eq_comap_bot, ← Ideal.comap_radical, Ideal.radical_eq_sInf]
  simp only [mem_vanishingIdeal, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
    comap_asIdeal, Ideal.mem_comap, bot_le, true_and, Submodule.mem_sInf, Set.mem_setOf_eq]
  exact ⟨fun H I hI ↦ H ⟨I, hI⟩, fun H I ↦ H I.1 I.2⟩

lemma closure_range_comap :
    closure (Set.range (comap f)) = zeroLocus (RingHom.ker f) := by
  rw [← zeroLocus_vanishingIdeal_eq_closure, vanishingIdeal_range_comap, zeroLocus_radical]

lemma denseRange_comap_iff_ker_le_nilRadical :
    DenseRange (comap f) ↔ RingHom.ker f ≤ nilradical R := by
  rw [denseRange_iff_closure_range, closure_range_comap, zeroLocus_eq_univ_iff,
    SetLike.coe_subset_coe]

@[stacks 00FL]
lemma denseRange_comap_iff_minimalPrimes :
    DenseRange (comap f) ↔ ∀ I (h : I ∈ minimalPrimes R), ⟨I, h.1.1⟩ ∈ Set.range (comap f) := by
  constructor
  · intro H I hI
    have : I ∈ (RingHom.ker f).minimalPrimes := by
      rw [denseRange_comap_iff_ker_le_nilRadical] at H
      simp only [minimalPrimes, Ideal.minimalPrimes, Set.mem_setOf] at hI ⊢
      convert hI using 2 with p
      exact ⟨fun h ↦ ⟨h.1, bot_le⟩, fun h ↦ ⟨h.1, H.trans (h.1.radical_le_iff.mpr bot_le)⟩⟩
    obtain ⟨p, hp, _, rfl⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes f (I := ⊥) I this
    exact ⟨⟨p, hp⟩, rfl⟩
  · intro H p
    obtain ⟨q, hq, hq'⟩ := Ideal.exists_minimalPrimes_le (J := p.asIdeal) bot_le
    exact ((le_iff_specializes ⟨q, hq.1.1⟩ p).mp hq').mem_closed isClosed_closure
      (subset_closure (H q hq))

end denseRange

variable (R) in
/--
Zero loci of prime ideals are closed irreducible sets in the Zariski topology and any closed
irreducible set is a zero locus of some prime ideal.
-/
protected def pointsEquivIrreducibleCloseds :
    PrimeSpectrum R ≃o (TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R))ᵒᵈ where
  __ := irreducibleSetEquivPoints.toEquiv.symm.trans OrderDual.toDual
  map_rel_iff' {p q} :=
    (RelIso.symm irreducibleSetEquivPoints).map_rel_iff.trans (le_iff_specializes p q).symm

lemma stableUnderSpecialization_singleton {x : PrimeSpectrum R} :
    StableUnderSpecialization {x} ↔ x.asIdeal.IsMaximal := by
  simp_rw [← isMax_iff, StableUnderSpecialization, ← le_iff_specializes, Set.mem_singleton_iff,
    @forall_comm _ (_ = _), forall_eq]
  exact ⟨fun H a h ↦ (H a h).le, fun H a h ↦ le_antisymm (H h) h⟩

lemma stableUnderGeneralization_singleton {x : PrimeSpectrum R} :
    StableUnderGeneralization {x} ↔ x.asIdeal ∈ minimalPrimes R := by
  simp_rw [← isMin_iff, StableUnderGeneralization, ← le_iff_specializes, Set.mem_singleton_iff,
    @forall_comm _ (_ = _), forall_eq]
  exact ⟨fun H a h ↦ (H a h).ge, fun H a h ↦ le_antisymm h (H h)⟩

lemma isCompact_isOpen_iff {s : Set (PrimeSpectrum R)} :
    IsCompact s ∧ IsOpen s ↔ ∃ t : Finset R, (zeroLocus t)ᶜ = s := by
  rw [isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis _
    isTopologicalBasis_basic_opens isCompact_basicOpen]
  simp only [basicOpen_eq_zeroLocus_compl, ← Set.compl_iInter₂, ← zeroLocus_iUnion₂,
    Set.biUnion_of_singleton]
  exact ⟨fun ⟨s, hs, e⟩ ↦ ⟨hs.toFinset, by simpa using e.symm⟩,
    fun ⟨s, e⟩ ↦ ⟨s, s.finite_toSet, by simpa using e.symm⟩⟩

lemma isCompact_isOpen_iff_ideal {s : Set (PrimeSpectrum R)} :
    IsCompact s ∧ IsOpen s ↔ ∃ I : Ideal R, I.FG ∧ (zeroLocus I)ᶜ = s := by
  rw [isCompact_isOpen_iff]
  exact ⟨fun ⟨s, e⟩ ↦ ⟨.span s, ⟨s, rfl⟩, by simpa using e⟩,
    fun ⟨I, ⟨s, hs⟩, e⟩ ↦ ⟨s, by simpa [hs.symm] using e⟩⟩

lemma basicOpen_eq_zeroLocus_of_mul_add (e f : R) (mul : e * f = 0) (add : e + f = 1) :
    basicOpen e = zeroLocus {f} := by
  ext p
  suffices e ∉ p.asIdeal ↔ f ∈ p.asIdeal by simpa
  refine ⟨(p.2.mem_or_mem_of_mul_eq_zero mul).resolve_left, fun h₁ h₂ ↦ p.2.1 ?_⟩
  rw [Ideal.eq_top_iff_one, ← add]
  exact add_mem h₂ h₁

lemma zeroLocus_eq_basicOpen_of_mul_add (e f : R) (mul : e * f = 0) (add : e + f = 1) :
    zeroLocus {e} = basicOpen f := by
  rw [basicOpen_eq_zeroLocus_of_mul_add f e] <;> simp only [mul, add, mul_comm, add_comm]

lemma isClopen_basicOpen_of_mul_add (e f : R) (mul : e * f = 0) (add : e + f = 1) :
    IsClopen (basicOpen e : Set (PrimeSpectrum R)) :=
  ⟨basicOpen_eq_zeroLocus_of_mul_add e f mul add ▸ isClosed_zeroLocus _, (basicOpen e).2⟩

lemma basicOpen_injOn_isIdempotentElem :
    {e : R | IsIdempotentElem e}.InjOn basicOpen := fun x hx y hy eq ↦ by
  by_contra! ne
  wlog ne' : x * y ≠ x generalizing x y
  · apply this y hy x hx eq.symm ne.symm
    rwa [mul_comm, of_not_not ne']
  have : x ∉ Ideal.span {y} := fun mem ↦ ne' <| by
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp mem
    rw [mul_assoc, hy]
  have ⟨p, prime, le, notMem⟩ := Ideal.exists_le_prime_notMem_of_isIdempotentElem _ x hx this
  exact ne_of_mem_of_not_mem' (a := ⟨p, prime⟩) notMem
    (not_not.mpr <| p.span_singleton_le_iff_mem.mp le) eq

lemma exists_mul_eq_zero_add_eq_one_basicOpen_eq_of_isClopen {s : Set (PrimeSpectrum R)}
    (hs : IsClopen s) : ∃ e f : R, e * f = 0 ∧ e + f = 1 ∧ s = basicOpen e ∧ sᶜ = basicOpen f := by
  cases subsingleton_or_nontrivial R
  · refine ⟨0, 0, ?_, ?_, ?_, ?_⟩ <;> apply Subsingleton.elim
  obtain ⟨I, hI, hI'⟩ := isCompact_isOpen_iff_ideal.mp ⟨hs.1.isCompact, hs.2⟩
  obtain ⟨J, hJ, hJ'⟩ := isCompact_isOpen_iff_ideal.mp
    ⟨hs.2.isClosed_compl.isCompact, hs.1.isOpen_compl⟩
  simp only [compl_eq_iff_isCompl, ← eq_compl_iff_isCompl, compl_compl] at hI' hJ'
  have : I * J ≤ nilradical R := by
    refine Ideal.radical_le_radical_iff.mp (le_of_eq ?_)
    rw [← zeroLocus_eq_iff, Ideal.zero_eq_bot, zeroLocus_bot,
      zeroLocus_mul, hI', hJ', Set.compl_union_self]
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg this (Submodule.FG.mul hI hJ)
  have hnz : n ≠ 0 := by rintro rfl; simp at hn
  rw [mul_pow, Ideal.zero_eq_bot] at hn
  have : I ^ n ⊔ J ^ n = ⊤ := by
    rw [eq_top_iff, ← Ideal.span_pow_eq_top (I ∪ J : Set R) _ n, Ideal.span_le, Set.image_union,
      Set.union_subset_iff]
    constructor
    · rintro _ ⟨x, hx, rfl⟩; exact Ideal.mem_sup_left (Ideal.pow_mem_pow hx n)
    · rintro _ ⟨x, hx, rfl⟩; exact Ideal.mem_sup_right (Ideal.pow_mem_pow hx n)
    · rw [Ideal.span_union, Ideal.span_eq, Ideal.span_eq, ← zeroLocus_empty_iff_eq_top,
        zeroLocus_sup, hI', hJ', Set.compl_inter_self]
  rw [Ideal.eq_top_iff_one, Submodule.mem_sup] at this
  obtain ⟨x, hx, y, hy, add⟩ := this
  have mul : x * y = 0 := hn (Ideal.mul_mem_mul hx hy)
  have : s = basicOpen x := by
    refine subset_antisymm ?_ ?_
    · rw [← hJ', basicOpen_eq_zeroLocus_of_mul_add _ _ mul add]
      exact zeroLocus_anti_mono (Set.singleton_subset_iff.mpr <| Ideal.pow_le_self hnz hy)
    · rw [basicOpen_eq_zeroLocus_compl, Set.compl_subset_comm, ← hI']
      exact zeroLocus_anti_mono (Set.singleton_subset_iff.mpr <| Ideal.pow_le_self hnz hx)
  refine ⟨x, y, mul, add, this, ?_⟩
  rw [this, basicOpen_eq_zeroLocus_of_mul_add _ _ mul add, basicOpen_eq_zeroLocus_compl]

lemma exists_idempotent_basicOpen_eq_of_isClopen {s : Set (PrimeSpectrum R)}
    (hs : IsClopen s) : ∃ e : R, IsIdempotentElem e ∧ s = basicOpen e :=
  have ⟨e, _, mul, add, eq, _⟩ := exists_mul_eq_zero_add_eq_one_basicOpen_eq_of_isClopen hs
  ⟨e, (IsIdempotentElem.of_mul_add mul add).1, eq⟩

@[stacks 00EE]
lemma existsUnique_idempotent_basicOpen_eq_of_isClopen {s : Set (PrimeSpectrum R)}
    (hs : IsClopen s) : ∃! e : R, IsIdempotentElem e ∧ s = basicOpen e := by
  refine existsUnique_of_exists_of_unique (exists_idempotent_basicOpen_eq_of_isClopen hs) ?_
  rintro x y ⟨hx, rfl⟩ ⟨hy, eq⟩
  exact basicOpen_injOn_isIdempotentElem hx hy (SetLike.ext' eq)

open TopologicalSpace.Opens in
lemma isClopen_iff_mul_add {s : Set (PrimeSpectrum R)} :
    IsClopen s ↔ ∃ e f : R, e * f = 0 ∧ e + f = 1 ∧ s = basicOpen e := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have ⟨e, f, h⟩ := exists_mul_eq_zero_add_eq_one_basicOpen_eq_of_isClopen h
    exact ⟨e, f, by simp only [h, and_self]⟩
  rintro ⟨e, f, mul, add, rfl⟩
  exact isClopen_basicOpen_of_mul_add e f mul add

lemma isClopen_iff_mul_add_zeroLocus {s : Set (PrimeSpectrum R)} :
    IsClopen s ↔ ∃ e f : R, e * f = 0 ∧ e + f = 1 ∧ s = zeroLocus {e} := by
  rw [isClopen_iff_mul_add, exists_swap]
  refine exists₂_congr fun e f ↦ ?_
  rw [mul_comm, add_comm, ← and_assoc, ← and_assoc, and_congr_right]
  intro ⟨mul, add⟩
  rw [zeroLocus_eq_basicOpen_of_mul_add e f mul add]

open TopologicalSpace (Clopens)

/-- Clopen subsets in the prime spectrum of a commutative semiring are in order-preserving
bijection with pairs of elements with product 0 and sum 1. (By definition, `(e₁, f₁) ≤ (e₂, f₂)`
iff `e₁ * e₂ = e₁`.) Both elements in such pairs must be idempotents, but there may exists
idempotents that do not form such pairs (does not have a "complement"). For example, in the
semiring {0, 0.5, 1} with ⊔ as + and ⊓ as *, 0.5 has no complement. -/
def mulZeroAddOneEquivClopens :
    {e : R × R // e.1 * e.2 = 0 ∧ e.1 + e.2 = 1} ≃o Clopens (PrimeSpectrum R) where
  toEquiv := .ofBijective
    (fun e ↦ ⟨basicOpen e.1.1, isClopen_iff_mul_add.mpr ⟨_, _, e.2.1, e.2.2, rfl⟩⟩) <| by
      refine ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ eq ↦ mul_eq_zero_add_eq_one_ext_left ?_, fun s ↦ ?_⟩
      · exact basicOpen_injOn_isIdempotentElem (IsIdempotentElem.of_mul_add hx.1 hx.2).1
          (IsIdempotentElem.of_mul_add hy.1 hy.2).1 <| SetLike.ext' (congr_arg (·.1) eq)
      · have ⟨e, f, mul, add, eq⟩ := isClopen_iff_mul_add.mp s.2
        exact ⟨⟨(e, f), mul, add⟩, SetLike.ext' eq.symm⟩
  map_rel_iff' {a b} := show basicOpen _ ≤ basicOpen _ ↔ _ by
    rw [← inf_eq_left, ← basicOpen_mul]
    refine ⟨fun h ↦ ?_, (by rw [·])⟩
    rw [← inf_eq_left]
    have := (IsIdempotentElem.of_mul_add a.2.1 a.2.2).1
    exact mul_eq_zero_add_eq_one_ext_left (basicOpen_injOn_isIdempotentElem
      (this.mul (IsIdempotentElem.of_mul_add b.2.1 b.2.2).1) this h)

lemma isRetrocompact_zeroLocus_compl {s : Set R} (hs : s.Finite) :
    IsRetrocompact (zeroLocus s)ᶜ :=
  (QuasiSeparatedSpace.isRetrocompact_iff_isCompact (isClosed_zeroLocus _).isOpen_compl).mpr
    (isCompact_isOpen_iff.mpr ⟨hs.toFinset, by simp⟩).1

lemma isRetrocompact_zeroLocus_compl_of_fg {I : Ideal R} (hI : I.FG) :
    IsRetrocompact (zeroLocus (I : Set R))ᶜ := by
  obtain ⟨s, rfl⟩ := hI
  rw [zeroLocus_span]
  exact isRetrocompact_zeroLocus_compl s.finite_toSet

lemma isRetrocompact_basicOpen {f : R} :
    IsRetrocompact (basicOpen f : Set (PrimeSpectrum R)) := by
  simpa using isRetrocompact_zeroLocus_compl (Set.finite_singleton f)

lemma isConstructible_basicOpen {f : R} :
    IsConstructible (basicOpen f : Set (PrimeSpectrum R)) :=
  isRetrocompact_basicOpen.isConstructible (basicOpen f).2

section IsIntegral

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

theorem isClosedMap_comap_of_isIntegral (hf : f.IsIntegral) :
    IsClosedMap (comap f) := by
  refine fun s hs ↦ isClosed_image_of_stableUnderSpecialization _ _ hs ?_
  rintro _ y e ⟨x, hx, rfl⟩
  algebraize [f]
  obtain ⟨q, hq₁, hq₂, hq₃⟩ := Ideal.exists_ideal_over_prime_of_isIntegral y.asIdeal x.asIdeal
    ((le_iff_specializes _ _).mpr e)
  refine ⟨⟨q, hq₂⟩, ((le_iff_specializes _ ⟨q, hq₂⟩).mp hq₁).mem_closed hs hx,
    PrimeSpectrum.ext hq₃⟩

theorem isClosed_comap_singleton_of_isIntegral (hf : f.IsIntegral)
    (x : PrimeSpectrum S) (hx : IsClosed ({x} : Set (PrimeSpectrum S))) :
    IsClosed ({comap f x} : Set (PrimeSpectrum R)) := by
  simpa using isClosedMap_comap_of_isIntegral f hf _ hx

lemma closure_image_comap_zeroLocus (I : Ideal S) :
    closure (comap f '' zeroLocus I) = zeroLocus (I.comap f) := by
  apply subset_antisymm
  · rw [(isClosed_zeroLocus _).closure_subset_iff, Set.image_subset_iff, preimage_comap_zeroLocus]
    exact zeroLocus_anti_mono (Set.image_preimage_subset _ _)
  · rintro x (hx : I.comap f ≤ x.asIdeal)
    obtain ⟨q, hq₁, hq₂⟩ := Ideal.exists_minimalPrimes_le hx
    obtain ⟨p', hp', hp'', rfl⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes f _ hq₁
    let p'' : PrimeSpectrum S := ⟨p', hp'⟩
    apply isClosed_closure.stableUnderSpecialization ((le_iff_specializes
      (comap f ⟨p', hp'⟩) x).mp hq₂) (subset_closure (by exact ⟨_, hp'', rfl⟩))

lemma isIntegral_of_isClosedMap_comap_mapRingHom (h : IsClosedMap (comap (mapRingHom f))) :
    f.IsIntegral := by
  algebraize [f]
  suffices Algebra.IsIntegral R S by rwa [Algebra.isIntegral_def] at this
  nontriviality R
  nontriviality S
  constructor
  intro r
  let p : S[X] := C r * X - 1
  have : (1 : R[X]) ∈ Ideal.span {X} ⊔ (Ideal.span {p}).comap (mapRingHom f) := by
    have H := h _ (isClosed_zeroLocus {p})
    rw [← zeroLocus_span, ← closure_eq_iff_isClosed, closure_image_comap_zeroLocus] at H
    rw [← Ideal.eq_top_iff_one, sup_comm, ← zeroLocus_empty_iff_eq_top, zeroLocus_sup, H]
    suffices ∀ (a : PrimeSpectrum S[X]), p ∈ a.asIdeal → X ∉ a.asIdeal by
      simpa [Set.eq_empty_iff_forall_notMem]
    intro q hpq hXq
    have : 1 ∈ q.asIdeal := by simpa [p] using (sub_mem (q.asIdeal.mul_mem_left (C r) hXq) hpq)
    exact q.2.ne_top (q.asIdeal.eq_top_iff_one.mpr this)
  obtain ⟨a, b, hb, e⟩ := Ideal.mem_span_singleton_sup.mp this
  obtain ⟨c, hc : b.map (algebraMap R S) = _⟩ := Ideal.mem_span_singleton.mp hb
  refine ⟨b.reverse * X ^ (1 + c.natDegree), ?_, ?_⟩
  · refine Monic.mul ?_ (by simp)
    have h : b.coeff 0 = 1 := by simpa using congr(($e).coeff 0)
    have : b.natTrailingDegree = 0 := by simp [h]
    rw [Monic.def, reverse_leadingCoeff, trailingCoeff, this, h]
  · have : p.natDegree ≤ 1 := by simpa using natDegree_linear_le (a := r) (b := -1)
    rw [eval₂_eq_eval_map, reverse, Polynomial.map_mul, ← reflect_map, Polynomial.map_pow,
      map_X, ← revAt_zero (1 + _), ← reflect_monomial,
      ← reflect_mul _ _ natDegree_map_le (by simp), pow_zero, mul_one, hc,
      ← add_assoc, reflect_mul _ _ (this.trans (by simp)) le_rfl,
      eval_mul, reflect_sub, reflect_mul _ _ (by simp) (by simp)]
    simp [← pow_succ']

lemma _root_.RingHom.IsIntegral.specComap_surjective {f : R →+* S} (hf : f.IsIntegral)
    (hinj : Function.Injective f) : Function.Surjective f.specComap := by
  algebraize [f]
  intro ⟨p, hp⟩
  obtain ⟨Q, _, hQ, rfl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p (⊥ : Ideal S)
    (by simp [Ideal.comap_bot_of_injective (algebraMap R S) hinj])
  exact ⟨⟨Q, hQ⟩, rfl⟩

end IsIntegral

variable (R)

/-- Zero loci of minimal prime ideals of `R` are irreducible components in `Spec R` and any
irreducible component is a zero locus of some minimal prime ideal. -/
@[stacks 00ES]
protected def _root_.minimalPrimes.equivIrreducibleComponents :
    minimalPrimes R ≃o (irreducibleComponents <| PrimeSpectrum R)ᵒᵈ := by
  let e : {p : Ideal R | p.IsPrime ∧ ⊥ ≤ p} ≃o PrimeSpectrum R :=
    ⟨⟨fun x ↦ ⟨x.1, x.2.1⟩, fun x ↦ ⟨x.1, x.2, bot_le⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩, Iff.rfl⟩
  rw [irreducibleComponents_eq_maximals_closed]
  exact OrderIso.setOfMinimalIsoSetOfMaximal
    (e.trans ((PrimeSpectrum.pointsEquivIrreducibleCloseds R).trans
    (TopologicalSpace.IrreducibleCloseds.orderIsoSubtype' (PrimeSpectrum R)).dual))

lemma vanishingIdeal_irreducibleComponents :
    vanishingIdeal '' (irreducibleComponents <| PrimeSpectrum R) = minimalPrimes R := by
  rw [irreducibleComponents_eq_maximals_closed, minimalPrimes_eq_minimals,
    image_antitone_setOf_maximal (fun s t hs _ ↦ (vanishingIdeal_anti_mono_iff hs.1).symm),
    ← funext (@Set.mem_setOf_eq _ · Ideal.IsPrime), ← vanishingIdeal_isClosed_isIrreducible]
  rfl

lemma zeroLocus_minimalPrimes :
    zeroLocus ∘ (↑) '' minimalPrimes R = irreducibleComponents (PrimeSpectrum R) := by
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

end CommSemiring

end PrimeSpectrum

namespace IsLocalRing

variable [CommSemiring R] [IsLocalRing R]

/-- The closed point in the prime spectrum of a local ring. -/
def closedPoint : PrimeSpectrum R :=
  ⟨maximalIdeal R, (maximalIdeal.isMaximal R).isPrime⟩

instance : OrderTop (PrimeSpectrum R) where
  top := closedPoint R
  le_top := fun _ ↦ le_maximalIdeal Ideal.IsPrime.ne_top'

variable {R}

theorem isLocalHom_iff_comap_closedPoint {S : Type v} [CommSemiring S] [IsLocalRing S]
    (f : R →+* S) : IsLocalHom f ↔ PrimeSpectrum.comap f (closedPoint S) = closedPoint R := by
  -- Porting note: inline `this` does **not** work
  have := (local_hom_TFAE f).out 0 4
  rw [this, PrimeSpectrum.ext_iff]
  rfl

@[simp]
theorem comap_closedPoint {S : Type v} [CommSemiring S] [IsLocalRing S] (f : R →+* S)
    [IsLocalHom f] : PrimeSpectrum.comap f (closedPoint S) = closedPoint R :=
  (isLocalHom_iff_comap_closedPoint f).mp inferInstance

theorem specializes_closedPoint (x : PrimeSpectrum R) : x ⤳ closedPoint R :=
  (PrimeSpectrum.le_iff_specializes _ _).mp (IsLocalRing.le_maximalIdeal x.2.1)

theorem closedPoint_mem_iff (U : TopologicalSpace.Opens <| PrimeSpectrum R) :
    closedPoint R ∈ U ↔ U = ⊤ := by
  constructor
  · rw [eq_top_iff]
    exact fun h x _ => (specializes_closedPoint x).mem_open U.2 h
  · rintro rfl
    exact TopologicalSpace.Opens.mem_top _

lemma closed_point_mem_iff {U : TopologicalSpace.Opens (PrimeSpectrum R)} :
    closedPoint R ∈ U ↔ U = ⊤ :=
  ⟨(eq_top_iff.mpr fun x _ ↦ (specializes_closedPoint x).mem_open U.2 ·), (· ▸ trivial)⟩

@[simp]
theorem PrimeSpectrum.comap_residue (T : Type u) [CommRing T] [IsLocalRing T]
    (x : PrimeSpectrum (ResidueField T)) : PrimeSpectrum.comap (residue T) x = closedPoint T := by
  rw [Subsingleton.elim x ⊥]
  ext1
  exact Ideal.mk_ker

variable (R) in
lemma isClosed_singleton_closedPoint : IsClosed {closedPoint R} := by
  rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal, closedPoint]
  infer_instance

end IsLocalRing

section KrullDimension

theorem PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim [CommSemiring R] :
    topologicalKrullDim (PrimeSpectrum R) = ringKrullDim R :=
  Order.krullDim_orderDual.symm.trans <| Order.krullDim_eq_of_orderIso
  (PrimeSpectrum.pointsEquivIrreducibleCloseds R).symm

end KrullDimension

section Idempotent

variable {R} [CommRing R]

namespace PrimeSpectrum

@[stacks 00EC]
lemma basicOpen_eq_zeroLocus_of_isIdempotentElem
    (e : R) (he : IsIdempotentElem e) :
    basicOpen e = zeroLocus {1 - e} :=
  basicOpen_eq_zeroLocus_of_mul_add _ _ (by simp [mul_sub, he.eq]) (by simp)

@[stacks 00EC]
lemma zeroLocus_eq_basicOpen_of_isIdempotentElem
    (e : R) (he : IsIdempotentElem e) :
    zeroLocus {e} = basicOpen (1 - e) := by
  rw [basicOpen_eq_zeroLocus_of_isIdempotentElem _ he.one_sub, sub_sub_cancel]

lemma isClopen_iff {s : Set (PrimeSpectrum R)} :
    IsClopen s ↔ ∃ e : R, IsIdempotentElem e ∧ s = basicOpen e := by
  refine ⟨exists_idempotent_basicOpen_eq_of_isClopen, ?_⟩
  rintro ⟨e, he, rfl⟩
  refine ⟨?_, (basicOpen e).2⟩
  rw [PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem e he]
  exact isClosed_zeroLocus _

lemma isClopen_iff_zeroLocus {s : Set (PrimeSpectrum R)} :
    IsClopen s ↔ ∃ e : R, IsIdempotentElem e ∧ s = zeroLocus {e} :=
  isClopen_iff.trans <| ⟨fun ⟨e, he, h⟩ ↦ ⟨1 - e, he.one_sub,
    h.trans (basicOpen_eq_zeroLocus_of_isIdempotentElem e he)⟩,
    fun ⟨e, he, h⟩ ↦ ⟨1 - e, he.one_sub, h.trans (zeroLocus_eq_basicOpen_of_isIdempotentElem e he)⟩⟩

open TopologicalSpace (Clopens Opens)

/-- Clopen subsets in the prime spectrum of a commutative ring are in 1-1 correspondence
with idempotent elements in the ring. -/
@[stacks 00EE]
def isIdempotentElemEquivClopens :
    {e : R // IsIdempotentElem e} ≃o Clopens (PrimeSpectrum R) :=
  .trans .isIdempotentElemMulZeroAddOne mulZeroAddOneEquivClopens

lemma basicOpen_isIdempotentElemEquivClopens_symm (s) :
    basicOpen (isIdempotentElemEquivClopens (R := R).symm s).1 = s.toOpens :=
  Opens.ext <| congr_arg (·.1) (isIdempotentElemEquivClopens.apply_symm_apply s)

lemma coe_isIdempotentElemEquivClopens_apply (e) :
    (isIdempotentElemEquivClopens e : Set (PrimeSpectrum R)) = basicOpen (e.1 : R) := rfl

lemma isIdempotentElemEquivClopens_apply_toOpens (e) :
    (isIdempotentElemEquivClopens e).toOpens = basicOpen (e.1 : R) := rfl

lemma isIdempotentElemEquivClopens_mul (e₁ e₂ : {e : R | IsIdempotentElem e}) :
    isIdempotentElemEquivClopens ⟨_, e₁.2.mul e₂.2⟩ =
      isIdempotentElemEquivClopens e₁ ⊓ isIdempotentElemEquivClopens e₂ :=
  map_inf ..

lemma isIdempotentElemEquivClopens_one_sub (e : {e : R | IsIdempotentElem e}) :
    isIdempotentElemEquivClopens ⟨_, e.2.one_sub⟩ = (isIdempotentElemEquivClopens e)ᶜ :=
  map_compl ..

lemma isIdempotentElemEquivClopens_symm_inf (s₁ s₂) :
    letI e := isIdempotentElemEquivClopens (R := R).symm
    e (s₁ ⊓ s₂) = ⟨_, (e s₁).2.mul (e s₂).2⟩ :=
  map_inf ..

lemma isIdempotentElemEquivClopens_symm_compl (s : Clopens (PrimeSpectrum R)) :
    isIdempotentElemEquivClopens.symm sᶜ = ⟨_, (isIdempotentElemEquivClopens.symm s).2.one_sub⟩ :=
  map_compl ..

lemma isIdempotentElemEquivClopens_symm_top :
    isIdempotentElemEquivClopens.symm ⊤ = ⟨(1 : R), .one⟩ :=
  map_top _

lemma isIdempotentElemEquivClopens_symm_bot :
    isIdempotentElemEquivClopens.symm ⊥ = ⟨(0 : R), .zero⟩ :=
  map_bot _

lemma isIdempotentElemEquivClopens_symm_sup (s₁ s₂ : Clopens (PrimeSpectrum R)) :
    letI e := isIdempotentElemEquivClopens (R := R).symm
    e (s₁ ⊔ s₂) = ⟨_, (e s₁).2.add_sub_mul (e s₂).2⟩ :=
  map_sup ..

end PrimeSpectrum

end Idempotent
