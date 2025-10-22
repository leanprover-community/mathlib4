/-
Copyright (c) 2024 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
import Mathlib.Order.SuccPred.WithBot
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Constructible sets in the prime spectrum

This file provides tooling for manipulating constructible sets in the prime spectrum of a ring.

-/

open Finset Topology
open scoped Polynomial

namespace PrimeSpectrum
variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (R) in
/-- The data of a basic constructible set `s` is a tuple `(f, g₁, ..., gₙ)` -/
@[ext]
structure BasicConstructibleSetData where
  /-- Given the data of a basic constructible set `s = V(g₁, ..., gₙ) \ V(f)`, return `f`. -/
  protected f : R
  /-- Given the data of a basic constructible set `s = V(g₁, ..., gₙ) \ V(f)`, return `n`. -/
  protected n : ℕ
  /-- Given the data of a basic constructible set `s = V(g₁, ..., gₙ) \ V(f)`, return `g`. -/
  protected g : Fin n → R

namespace BasicConstructibleSetData

noncomputable instance : DecidableEq (BasicConstructibleSetData R) := Classical.decEq _

/-- Given the data of the constructible set `s`, build the data of the constructible set
`{I | {x | φ x ∈ I} ∈ s}`. -/
@[simps]
noncomputable def map (φ : R →+* S) (C : BasicConstructibleSetData R) :
    BasicConstructibleSetData S where
  f := φ C.f
  n := C.n
  g := φ ∘ C.g

@[simp] lemma map_id (C : BasicConstructibleSetData R) : C.map (.id _) = C := by simp [map]

@[simp] lemma map_id' : map (.id R) = id := by ext : 1; simp

lemma map_comp (φ : S →+* T) (ψ : R →+* S) (C : BasicConstructibleSetData R) :
    C.map (φ.comp ψ) = (C.map ψ).map φ := by simp [map, Function.comp_def]

lemma map_comp' (φ : S →+* T) (ψ : R →+* S) : map (φ.comp ψ) = map φ ∘ map ψ := by
  ext : 1; simp [map_comp]

/-- Given the data of a basic constructible set `s`, namely a tuple `(f, g₁, ..., gₙ)` such that
`s = V(g₁, ..., gₙ) \ V(f)`, return `s`. -/
def toSet (C : BasicConstructibleSetData R) : Set (PrimeSpectrum R) :=
  zeroLocus (Set.range C.g) \ zeroLocus {C.f}

@[simp]
lemma toSet_map (φ : R →+* S) (C : BasicConstructibleSetData R) :
    (C.map φ).toSet = comap φ ⁻¹' C.toSet := by simp [toSet, map, ← Set.range_comp]
 
end BasicConstructibleSetData

variable (R) in
/-- The data of a constructible set `s` in the prime spectrum of a ring is finitely many tuples
`(f, g₁, ..., gₙ)` such that `s = ⋃ (f, g₁, ..., gₙ), V(g₁, ..., gₙ) \ V(f)`.

To obtain `s` from its data, use `PrimeSpectrum.ConstructibleSetData.toSet`. -/
abbrev ConstructibleSetData := Finset (BasicConstructibleSetData R)

namespace ConstructibleSetData

/-- Given the data of the constructible set `s`, build the data of the constructible set
`{I | {x | f x ∈ I} ∈ s}`. -/
noncomputable def map (φ : R →+* S) (s : ConstructibleSetData R) : ConstructibleSetData S :=
  s.image (.map φ)

@[simp]
lemma map_id (s : ConstructibleSetData R) : s.map (.id _) = s := by simp [map]

lemma map_comp (f : S →+* T) (g : R →+* S) (s : ConstructibleSetData R) :
    s.map (f.comp g) = (s.map g).map f := by
  simp [map, image_image, Function.comp_def, BasicConstructibleSetData.map_comp']

/-- Given the data of a constructible set `s`, namely finitely many tuples `(f, g₁, ..., gₙ)` such
that `s = ⋃ (f, g₁, ..., gₙ), V(g₁, ..., gₙ) \ V(f)`, return `s`. -/
def toSet (S : ConstructibleSetData R) : Set (PrimeSpectrum R) := ⋃ C ∈ S, C.toSet

@[simp]
lemma toSet_map (f : R →+* S) (s : ConstructibleSetData R) :
    (s.map f).toSet = comap f ⁻¹' s.toSet := by
  unfold toSet map
  rw [set_biUnion_finset_image]
  simp

/-- The degree bound on a constructible set for Chevalley's theorem for the inclusion `R ↪ R[X]`. -/
def degBound (S : ConstructibleSetData R[X]) : ℕ := S.sup fun C ↦ ∑ i, (C.g i).degree.succ

lemma isConstructible_toSet (S : ConstructibleSetData R) :
    IsConstructible S.toSet := by
  refine .biUnion S.finite_toSet fun _ _ ↦ .sdiff ?_ ?_
  · rw [← isConstructible_compl]
    exact (isRetrocompact_zeroLocus_compl (Set.finite_range _)).isConstructible
      (isClosed_zeroLocus _).isOpen_compl
  · rw [← isConstructible_compl]
    exact (isRetrocompact_zeroLocus_compl (Set.finite_singleton _)).isConstructible
      (isClosed_zeroLocus _).isOpen_compl

end ConstructibleSetData

lemma exists_constructibleSetData_iff {s : Set (PrimeSpectrum R)} :
    (∃ S : ConstructibleSetData R, S.toSet = s) ↔ IsConstructible s := by
  refine ⟨fun ⟨S, H⟩ ↦ H ▸ S.isConstructible_toSet, fun H ↦ ?_⟩
  induction s, H using IsConstructible.induction_of_isTopologicalBasis
      _ (isTopologicalBasis_basic_opens (R := R)) with
  | isCompact_basis i => exact isCompact_basicOpen _
  | sdiff i s hs =>
    have : Finite s := hs
    refine ⟨{⟨i, Nat.card s, fun i ↦ ((Finite.equivFin s).symm i).1⟩}, ?_⟩
    simp only [ConstructibleSetData.toSet, Finset.mem_singleton, BasicConstructibleSetData.toSet,
      Set.iUnion_iUnion_eq_left, basicOpen_eq_zeroLocus_compl, ← Set.compl_iInter₂,
        compl_sdiff_compl, ← zeroLocus_iUnion₂, Set.biUnion_of_singleton]
    congr! 2
    ext
    simp [← (Finite.equivFin s).exists_congr_right, - Nat.card_coe_set_eq]
  | union s hs t ht Hs Ht =>
    obtain ⟨S, rfl⟩ := Hs
    obtain ⟨T, rfl⟩ := Ht
    refine ⟨S ∪ T, ?_⟩
    simp only [ConstructibleSetData.toSet, Set.biUnion_union, ← Finset.mem_coe, Finset.coe_union]

universe u in
@[stacks 00F8 "without the finite presentation part"]
-- TODO: show that the constructed `f` is of finite presentation
lemma exists_range_eq_of_isConstructible {R : Type u} [CommRing R]
    {s : Set (PrimeSpectrum R)} (hs : IsConstructible s) :
    ∃ (S : Type u) (_ : CommRing S) (f : R →+* S), Set.range (comap f) = s := by
  obtain ⟨s, rfl⟩ := exists_constructibleSetData_iff.mpr hs
  refine ⟨Π i : s, Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range i.1.g)) i.1.f),
    inferInstance, algebraMap _ _, ?_⟩
  rw [coe_comap, ← iUnion_range_specComap_comp_evalRingHom, ConstructibleSetData.toSet]
  simp_rw [← Finset.mem_coe, Set.biUnion_eq_iUnion]
  congr! with _ _ C
  let I := Ideal.span (Set.range C.1.g)
  let f := Ideal.Quotient.mk I C.1.f
  trans comap (Ideal.Quotient.mk I) '' (Set.range (comap (algebraMap _ (Localization.Away f))))
  · rw [← Set.range_comp]; rfl
  · rw [localization_away_comap_range _ f, ← comap_basicOpen, TopologicalSpace.Opens.coe_comap,
      Set.image_preimage_eq_inter_range, range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      BasicConstructibleSetData.toSet, Set.diff_eq_compl_inter, basicOpen_eq_zeroLocus_compl,
      Ideal.mk_ker, zeroLocus_span]

@[stacks 00I0 "(1)"]
lemma isClosed_of_stableUnderSpecialization_of_isConstructible {R : Type*} [CommRing R]
    {s : Set (PrimeSpectrum R)} (hs : StableUnderSpecialization s) (hs' : IsConstructible s) :
    IsClosed s := by
  obtain ⟨S, _, f, rfl⟩ := exists_range_eq_of_isConstructible hs'
  exact isClosed_range_of_stableUnderSpecialization _ hs

@[stacks 00I0 "(1)"]
lemma isOpen_of_stableUnderGeneralization_of_isConstructible {R : Type*} [CommRing R]
    {s : Set (PrimeSpectrum R)} (hs : StableUnderGeneralization s) (hs' : IsConstructible s) :
    IsOpen s := by
  rw [← isClosed_compl_iff]
  exact isClosed_of_stableUnderSpecialization_of_isConstructible hs.compl hs'.compl

end PrimeSpectrum
