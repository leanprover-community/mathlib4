/-
Copyright (c) 2022 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.MvPolynomial.Cardinal
import Mathlib.Algebra.Polynomial.Cardinal
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.AlgebraicIndependent

/-!
# Classification of Algebraically closed fields

This file contains results related to classifying algebraically closed fields.

## Main statements

* `IsAlgClosed.equivOfTranscendenceBasis` Two algebraically closed fields with the same
  characteristic and the same cardinality of transcendence basis are isomorphic.
* `IsAlgClosed.ringEquivOfCardinalEqOfCharEq` Two uncountable algebraically closed fields
  are isomorphic if they have the same characteristic and the same cardinality.
-/


universe u

open scoped Cardinal Polynomial

open Cardinal

namespace IsAlgClosed

section Classification

noncomputable section

variable {R L K : Type*} [CommRing R]
variable [Field K] [Algebra R K]
variable [Field L] [Algebra R L]
variable {ι : Type*} (v : ι → K)
variable {κ : Type*} (w : κ → L)
variable (hv : AlgebraicIndependent R v)

theorem isAlgClosure_of_transcendence_basis [IsAlgClosed K] (hv : IsTranscendenceBasis R v) :
    IsAlgClosure (Algebra.adjoin R (Set.range v)) K :=
  letI := RingHom.domain_nontrivial (algebraMap R K)
  { isAlgClosed := by infer_instance
    isAlgebraic := hv.isAlgebraic }

variable (hw : AlgebraicIndependent R w)

/-- setting `R` to be `ZMod (ringChar R)` this result shows that if two algebraically
closed fields have equipotent transcendence bases and the same characteristic then they are
isomorphic. -/
def equivOfTranscendenceBasis [IsAlgClosed K] [IsAlgClosed L] (e : ι ≃ κ)
    (hv : IsTranscendenceBasis R v) (hw : IsTranscendenceBasis R w) : K ≃+* L := by
  letI := isAlgClosure_of_transcendence_basis v hv
  letI := isAlgClosure_of_transcendence_basis w hw
  have e : Algebra.adjoin R (Set.range v) ≃+* Algebra.adjoin R (Set.range w) := by
    refine hv.1.aevalEquiv.symm.toRingEquiv.trans ?_
    refine (AlgEquiv.ofAlgHom (MvPolynomial.rename e)
      (MvPolynomial.rename e.symm) ?_ ?_).toRingEquiv.trans ?_
    · ext; simp
    · ext; simp
    exact hw.1.aevalEquiv.toRingEquiv
  exact IsAlgClosure.equivOfEquiv K L e

end

end Classification

section Cardinal

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K] [IsAlgClosed K]
variable {ι : Type u} (v : ι → K)

theorem cardinal_le_max_transcendence_basis (hv : IsTranscendenceBasis R v) :
    #K ≤ max (max #R #ι) ℵ₀ :=
  calc
    #K ≤ max #(Algebra.adjoin R (Set.range v)) ℵ₀ :=
      letI := isAlgClosure_of_transcendence_basis v hv
      Algebra.IsAlgebraic.cardinalMk_le_max _ _
    _ = max #(MvPolynomial ι R) ℵ₀ := by rw [Cardinal.eq.2 ⟨hv.1.aevalEquiv.toEquiv⟩]
    _ ≤ max (max (max #R #ι) ℵ₀) ℵ₀ := max_le_max MvPolynomial.cardinalMk_le_max le_rfl
    _ = _ := by simp [max_assoc]

/-- If `K` is an uncountable algebraically closed field, then its
cardinality is the same as that of a transcendence basis. -/
theorem cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt [Nontrivial R]
    (hv : IsTranscendenceBasis R v) (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) : #K = #ι :=
  have : ℵ₀ ≤ #ι := le_of_not_lt fun h => not_le_of_gt hK <|
    calc
      #K ≤ max (max #R #ι) ℵ₀ := cardinal_le_max_transcendence_basis v hv
      _ ≤ _ := max_le (max_le hR (le_of_lt h)) le_rfl
  le_antisymm
    (calc
      #K ≤ max (max #R #ι) ℵ₀ := cardinal_le_max_transcendence_basis v hv
      _ = #ι := by
        rw [max_eq_left, max_eq_right]
        · exact le_trans hR this
        · exact le_max_of_le_right this)
    (mk_le_of_injective (show Function.Injective v from hv.1.injective))

end Cardinal

variable {K L : Type} [Field K] [Field L] [IsAlgClosed K] [IsAlgClosed L]

/-- Two uncountable algebraically closed fields of characteristic zero are isomorphic
if they have the same cardinality. -/
theorem ringEquivOfCardinalEqOfCharZero [CharZero K] [CharZero L] (hK : ℵ₀ < #K)
    (hKL : #K = #L) : Nonempty (K ≃+* L) := by
  cases' exists_isTranscendenceBasis ℤ
    (show Function.Injective (algebraMap ℤ K) from Int.cast_injective) with s hs
  cases' exists_isTranscendenceBasis ℤ
    (show Function.Injective (algebraMap ℤ L) from Int.cast_injective) with t ht
  have : #s = #t := by
    rw [← cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ hs (le_of_eq mk_int) hK, ←
      cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ ht (le_of_eq mk_int), hKL]
    rwa [← hKL]
  cases' Cardinal.eq.1 this with e
  exact ⟨equivOfTranscendenceBasis _ _ e hs ht⟩

private theorem ringEquivOfCardinalEqOfCharP (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p]
    (hK : ℵ₀ < #K) (hKL : #K = #L) : Nonempty (K ≃+* L) := by
  letI : Algebra (ZMod p) K := ZMod.algebra _ _
  letI : Algebra (ZMod p) L := ZMod.algebra _ _
  cases' exists_isTranscendenceBasis (ZMod p)
    (show Function.Injective (algebraMap (ZMod p) K) from RingHom.injective _) with s hs
  cases' exists_isTranscendenceBasis (ZMod p)
    (show Function.Injective (algebraMap (ZMod p) L) from RingHom.injective _) with t ht
  have : #s = #t := by
    rw [← cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ hs
      (lt_aleph0_of_finite (ZMod p)).le hK,
      ← cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ ht
        (lt_aleph0_of_finite (ZMod p)).le, hKL]
    rwa [← hKL]
  cases' Cardinal.eq.1 this with e
  exact ⟨equivOfTranscendenceBasis _ _ e hs ht⟩

/-- Two uncountable algebraically closed fields are isomorphic
if they have the same cardinality and the same characteristic. -/
theorem ringEquivOfCardinalEqOfCharEq (p : ℕ) [CharP K p] [CharP L p] (hK : ℵ₀ < #K)
    (hKL : #K = #L) : Nonempty (K ≃+* L) := by
  rcases CharP.char_is_prime_or_zero K p with (hp | hp)
  · haveI : Fact p.Prime := ⟨hp⟩
    exact ringEquivOfCardinalEqOfCharP p hK hKL
  · simp only [hp] at *
    letI : CharZero K := CharP.charP_to_charZero K
    letI : CharZero L := CharP.charP_to_charZero L
    exact ringEquivOfCardinalEqOfCharZero hK hKL

end IsAlgClosed
