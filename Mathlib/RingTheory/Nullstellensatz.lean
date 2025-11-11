/-
Copyright (c) 2021 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Nullstellensatz
This file establishes a version of Hilbert's classical Nullstellensatz for `MvPolynomial`s.
The main statement of the theorem is `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`.

The statement is in terms of new definitions `vanishingIdeal` and `zeroLocus`.
Mathlib already has versions of these in terms of the prime spectrum of a ring,
  but those are not well-suited for expressing this result.
Suggestions for better ways to state this theorem or organize things are welcome.

The machinery around `vanishingIdeal` and `zeroLocus` is also minimal, I only added lemmas
  directly needed in this proof, since I'm not sure if they are the right approach.
-/

open Ideal

noncomputable section

namespace MvPolynomial

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable {σ : Type*}

variable (K) in
/-- Set of points that are zeroes of all polynomials in an ideal -/
def zeroLocus (I : Ideal (MvPolynomial σ k)) : Set (σ → K) :=
  {x : σ → K | ∀ p ∈ I, aeval x p = 0}

@[simp]
theorem mem_zeroLocus_iff {I : Ideal (MvPolynomial σ k)} {x : σ → K} :
    x ∈ zeroLocus K I ↔ ∀ p ∈ I, aeval x p = 0 :=
  Iff.rfl

theorem zeroLocus_anti_mono {I J : Ideal (MvPolynomial σ k)} (h : I ≤ J) :
    zeroLocus K J ≤ zeroLocus K I := fun _ hx p hp => hx p <| h hp

@[simp]
theorem zeroLocus_bot : zeroLocus K (⊥ : Ideal (MvPolynomial σ k)) = ⊤ :=
  eq_top_iff.2 fun x _ _ hp => Trans.trans (congr_arg (aeval x) (mem_bot.1 hp)) (eval x).map_zero

@[simp]
theorem zeroLocus_top : zeroLocus K (⊤ : Ideal (MvPolynomial σ k)) = ⊥ :=
  eq_bot_iff.2 fun x hx => one_ne_zero
    ((aeval (R := k) x).map_one ▸ hx 1 Submodule.mem_top : (1 : K) = 0)

variable (k) in
/-- Ideal of polynomials with common zeroes at all elements of a set -/
def vanishingIdeal (V : Set (σ → K)) : Ideal (MvPolynomial σ k) where
  carrier := {p | ∀ x ∈ V, aeval x p = 0}
  zero_mem' _ _ := RingHom.map_zero _
  add_mem' {p q} hp hq x hx := by simp only [hq x hx, hp x hx, add_zero, map_add]
  smul_mem' p q hq x hx := by
    simp only [hq x hx, Algebra.id.smul_eq_mul, mul_zero, map_mul]

@[simp]
theorem mem_vanishingIdeal_iff {V : Set (σ → K)} {p : MvPolynomial σ k} :
    p ∈ vanishingIdeal k V ↔ ∀ x ∈ V, aeval x p = 0 :=
  Iff.rfl

theorem vanishingIdeal_anti_mono {A B : Set (σ → K)} (h : A ≤ B) :
    vanishingIdeal k B ≤ vanishingIdeal k A := fun _ hp x hx => hp x <| h hx

theorem vanishingIdeal_empty : vanishingIdeal k (∅ : Set (σ → K)) = ⊤ :=
  le_antisymm le_top fun _ _ x hx => absurd hx (Set.notMem_empty x)

theorem le_vanishingIdeal_zeroLocus (I : Ideal (MvPolynomial σ k)) :
    I ≤ vanishingIdeal k (zeroLocus K I) := fun p hp _ hx => hx p hp

theorem zeroLocus_vanishingIdeal_le (V : Set (σ → K)) : V ≤ zeroLocus K (vanishingIdeal k V) :=
  fun V hV _ hp => hp V hV

theorem zeroLocus_vanishingIdeal_galoisConnection :
    @GaloisConnection (Ideal (MvPolynomial σ k)) (Set (σ → K))ᵒᵈ _ _
      (zeroLocus K) (vanishingIdeal k) :=
  GaloisConnection.monotone_intro (fun _ _ ↦ vanishingIdeal_anti_mono)
    (fun _ _ ↦ zeroLocus_anti_mono) le_vanishingIdeal_zeroLocus zeroLocus_vanishingIdeal_le

theorem le_zeroLocus_iff_le_vanishingIdeal {V : Set (σ → K)} {I : Ideal (MvPolynomial σ k)} :
    V ≤ zeroLocus K I ↔ I ≤ vanishingIdeal k V :=
  zeroLocus_vanishingIdeal_galoisConnection.le_iff_le

theorem zeroLocus_span (S : Set (MvPolynomial σ k)) :
    zeroLocus K (Ideal.span S) = { x | ∀ p ∈ S, aeval x p = 0 } :=
  eq_of_forall_le_iff fun _ => le_zeroLocus_iff_le_vanishingIdeal.trans <|
    Ideal.span_le.trans forall₂_swap

theorem mem_vanishingIdeal_singleton_iff (x : σ → K) (p : MvPolynomial σ k) :
    p ∈ (vanishingIdeal k {x} : Ideal (MvPolynomial σ k)) ↔ aeval x p = 0 :=
  ⟨fun h => h x rfl, fun hpx _ hy => hy.symm ▸ hpx⟩

instance {x : σ → K} : (vanishingIdeal k {x} : Ideal (MvPolynomial σ k)).IsPrime := by
  convert RingHom.ker_isPrime (aeval (R := k) x)
  ext; simp

instance {x : σ → K} : (vanishingIdeal K {x} : Ideal (MvPolynomial σ K)).IsMaximal := by
  convert RingHom.ker_isMaximal_of_surjective (aeval (R := K) x) ?_
  · ext; simp
  · intro z; use C z; simp

theorem radical_le_vanishingIdeal_zeroLocus (I : Ideal (MvPolynomial σ k)) :
    I.radical ≤ vanishingIdeal k (zeroLocus K I) := by
  intro p hp x hx
  rw [← mem_vanishingIdeal_singleton_iff]
  rw [radical_eq_sInf] at hp
  refine
    (mem_sInf.mp hp)
      ⟨le_trans (le_vanishingIdeal_zeroLocus I)
          (vanishingIdeal_anti_mono fun y hy => hy.symm ▸ hx),
        inferInstance⟩

/-- The point in the prime spectrum associated to a given point -/
def pointToPoint (x : σ → K) : PrimeSpectrum (MvPolynomial σ k) :=
  ⟨(vanishingIdeal k {x} : Ideal (MvPolynomial σ k)), by infer_instance⟩

@[simp]
theorem vanishingIdeal_pointToPoint (V : Set (σ → K)) :
    PrimeSpectrum.vanishingIdeal (pointToPoint '' V) = MvPolynomial.vanishingIdeal k V :=
  le_antisymm
    (fun _ hp x hx =>
      (((PrimeSpectrum.mem_vanishingIdeal _ _).1 hp) ⟨vanishingIdeal k {x}, by infer_instance⟩
        (⟨x, hx, rfl⟩ : _))
        x rfl)
    fun _ hp =>
    (PrimeSpectrum.mem_vanishingIdeal _ _).2 fun _ hI =>
      let ⟨x, hx⟩ := hI
      hx.2 ▸ fun _ hx' => (Set.mem_singleton_iff.1 hx').symm ▸ hp x hx.1

theorem pointToPoint_zeroLocus_le (I : Ideal (MvPolynomial σ K)) :
    pointToPoint (k := K) '' MvPolynomial.zeroLocus K I ≤ PrimeSpectrum.zeroLocus I := fun J hJ =>
  let ⟨_, hx⟩ := hJ
  (le_trans (le_vanishingIdeal_zeroLocus (K := K) I)
      (hx.2 ▸ vanishingIdeal_anti_mono (Set.singleton_subset_iff.2 hx.1)) :
    I ≤ J.asIdeal)

variable [IsAlgClosed K] [Finite σ]

variable (K) in
theorem eq_vanishingIdeal_singleton_of_isMaximal {I : Ideal (MvPolynomial σ k)} (hI : I.IsMaximal) :
    ∃ x : σ → K, I = vanishingIdeal k {x} := by
  let : Field (MvPolynomial σ k ⧸ I) := Quotient.field I
  have : Algebra.IsAlgebraic k (MvPolynomial σ k ⧸ I) := by
    rw [Algebra.isAlgebraic_iff_isIntegral, ← algebraMap_isIntegral_iff]
    exact MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let φ : (MvPolynomial σ k ⧸ I) →ₐ[k] K := IsAlgClosed.lift
  let x : σ → K := fun s => φ (Ideal.Quotient.mk I (X s))
  have : aeval x = φ.comp (Quotient.mkₐ k I) := by ext; simp [x]
  use x
  simp [Ideal.ext_iff, this, Ideal.Quotient.eq_zero_iff_mem]

theorem isMaximal_iff_eq_vanishingIdeal_singleton {I : Ideal (MvPolynomial σ K)} :
    I.IsMaximal ↔ ∃ x : σ → K, I = vanishingIdeal K {x} :=
  ⟨eq_vanishingIdeal_singleton_of_isMaximal K,
    fun ⟨_, hx⟩ => hx ▸ inferInstance⟩

/-- Main statement of the Nullstellensatz -/
@[simp]
theorem vanishingIdeal_zeroLocus_eq_radical (I : Ideal (MvPolynomial σ k)) :
    vanishingIdeal k (zeroLocus K I) = I.radical := by
  refine le_antisymm ?_ (radical_le_vanishingIdeal_zeroLocus _)
  rw [I.radical_eq_jacobson]
  apply le_sInf
  rintro J ⟨hJI, hJ⟩
  obtain ⟨x, hx⟩ := eq_vanishingIdeal_singleton_of_isMaximal K hJ
  refine hx.symm ▸ vanishingIdeal_anti_mono fun y hy p hp => ?_
  rw [← mem_vanishingIdeal_singleton_iff, Set.mem_singleton_iff.1 hy, ← hx]
  exact hJI hp

@[simp high] -- This needs to fire before `vanishingIdeal_zeroLocus_eq_radical`
theorem IsPrime.vanishingIdeal_zeroLocus (P : Ideal (MvPolynomial σ k)) [h : P.IsPrime] :
    vanishingIdeal k (zeroLocus K P) = P :=
  Trans.trans (vanishingIdeal_zeroLocus_eq_radical P) h.radical

end MvPolynomial
