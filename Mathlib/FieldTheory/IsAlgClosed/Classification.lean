/-
Copyright (c) 2022 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.Cardinal
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Classification of Algebraically closed fields

This file contains results related to classifying algebraically closed fields.

## Main statements

* `IsAlgClosed.equivOfTranscendenceBasis` Two algebraically closed fields with the same
  characteristic and the same cardinality of transcendence basis are isomorphic.
* `IsAlgClosed.ringEquivOfCardinalEqOfCharEq` Two uncountable algebraically closed fields
  are isomorphic if they have the same characteristic and the same cardinality.
-/


universe u v w

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

variable {R : Type u} {K : Type v} [CommRing R] [Field K] [Algebra R K] [IsAlgClosed K]
variable {ι : Type w} (v : ι → K)

variable {K' : Type u} [Field K'] [Algebra R K'] [IsAlgClosed K']
variable {ι' : Type u} (v' : ι' → K')

/-- The cardinality of an algebraically closed `R`-algebra is less than or equal to
the maximum of the cardinality of `R`, the cardinality of a transcendence basis and
`ℵ₀`

For a simpler, but less universe-polymorphic statement, see
`IsAlgClosed.cardinal_le_max_transcendence_basis'` -/
theorem cardinal_le_max_transcendence_basis (hv : IsTranscendenceBasis R v) :
    Cardinal.lift.{max u w} #K ≤ max (max (Cardinal.lift.{max v w} #R)
      (Cardinal.lift.{max u v} #ι)) ℵ₀ :=
  calc
    Cardinal.lift.{max u w} #K ≤ Cardinal.lift.{max u w}
        (max #(Algebra.adjoin R (Set.range v)) ℵ₀) := by
      letI := isAlgClosure_of_transcendence_basis v hv
      simpa using Algebra.IsAlgebraic.cardinalMk_le_max (Algebra.adjoin R (Set.range v)) K
    _ = Cardinal.lift.{v} (max #(MvPolynomial ι R) ℵ₀) := by
      rw [lift_max, ← Cardinal.lift_mk_eq.2 ⟨hv.1.aevalEquiv.toEquiv⟩, lift_aleph0,
        ← lift_aleph0.{max u v w, max u w}, ← lift_max, lift_umax.{max u w, v}]
    _ ≤ Cardinal.lift.{v} (max (max (max (Cardinal.lift #R) (Cardinal.lift #ι)) ℵ₀) ℵ₀) :=
        lift_le.2 (max_le_max MvPolynomial.cardinalMk_le_max_lift le_rfl)
    _ = _ := by simp

/-- The cardinality of an algebraically closed `R`-algebra is less than or equal to
the maximum of the cardinality of `R`, the cardinality of a transcendence basis and
`ℵ₀`

A less-universe polymorphic, but simpler statement of
`IsAlgClosed.cardinal_le_max_transcendence_basis` -/
theorem cardinal_le_max_transcendence_basis' (hv : IsTranscendenceBasis R v') :
    #K' ≤ max (max #R #ι') ℵ₀ := by
  simpa using cardinal_le_max_transcendence_basis v' hv

/-- If `K` is an uncountable algebraically closed field, then its
cardinality is the same as that of a transcendence basis.

For a simpler, but less universe-polymorphic statement, see
`IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'` -/
theorem cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt [Nontrivial R]
    (hv : IsTranscendenceBasis R v) (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) :
    Cardinal.lift.{w} #K = Cardinal.lift.{v} #ι :=
  have : ℵ₀ ≤ Cardinal.lift.{max u v} #ι := le_of_not_gt fun h => not_le_of_gt
    (show ℵ₀ < Cardinal.lift.{max u w} #K by simpa) <|
    calc
      Cardinal.lift.{max u w, v} #K ≤ max (max (Cardinal.lift.{max v w, u} #R)
        (Cardinal.lift.{max u v, w} #ι)) ℵ₀ := cardinal_le_max_transcendence_basis v hv
      _ ≤ _ := max_le (max_le (by simpa) (by simpa using le_of_lt h)) le_rfl
  suffices Cardinal.lift.{max u w} #K = Cardinal.lift.{max u v} #ι
    from Cardinal.lift_injective.{u, max v w} (by simpa)
  le_antisymm
    (calc
      Cardinal.lift.{max u w} #K ≤ max (max
        (Cardinal.lift.{max v w} #R) (Cardinal.lift.{max u v} #ι)) ℵ₀ :=
        cardinal_le_max_transcendence_basis v hv
      _ = Cardinal.lift #ι := by
        rw [max_eq_left, max_eq_right]
        · exact le_trans (by simpa using hR) this
        · exact le_max_of_le_right this)
    (lift_mk_le.2 ⟨⟨v, hv.1.injective⟩⟩)

/-- If `K` is an uncountable algebraically closed field, then its
cardinality is the same as that of a transcendence basis.

This is a simpler, but less general statement of
`cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt`. -/
theorem cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' [Nontrivial R]
    (hv : IsTranscendenceBasis R v') (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K') : #K' = #ι' := by
  simpa using cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt v' hv hR hK

end Cardinal

variable {K : Type u} {L : Type v} [Field K] [Field L] [IsAlgClosed K] [IsAlgClosed L]

/-- Two uncountable algebraically closed fields of characteristic zero are isomorphic
if they have the same cardinality. -/
theorem ringEquiv_of_equiv_of_charZero [CharZero K] [CharZero L] (hK : ℵ₀ < #K)
    (hKL : Nonempty (K ≃ L)) : Nonempty (K ≃+* L) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℤ K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis ℤ L
  have hL : ℵ₀ < #L := by
    rwa [← aleph0_lt_lift.{v, u}, ← lift_mk_eq'.2 hKL, aleph0_lt_lift]
  have : Cardinal.lift.{v} #s = Cardinal.lift.{u} #t := by
    rw [← lift_injective (cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _
        hs (le_of_eq mk_int) hK),
      ← lift_injective (cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _
        ht (le_of_eq mk_int) hL)]
    exact Cardinal.lift_mk_eq'.2 hKL
  obtain ⟨e⟩ := Cardinal.lift_mk_eq'.1 this
  exact ⟨equivOfTranscendenceBasis _ _ e hs ht⟩

private theorem ringEquiv_of_Cardinal_eq_of_charP (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p]
    (hK : ℵ₀ < #K) (hKL : Nonempty (K ≃ L)) : Nonempty (K ≃+* L) := by
  letI : Algebra (ZMod p) K := ZMod.algebra _ _
  letI : Algebra (ZMod p) L := ZMod.algebra _ _
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis (ZMod p) K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis (ZMod p) L
  have hL : ℵ₀ < #L := by
    rwa [← aleph0_lt_lift.{v, u}, ← lift_mk_eq'.2 hKL, aleph0_lt_lift]
  have : Cardinal.lift.{v} #s = Cardinal.lift.{u} #t := by
    rw [← lift_injective (cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _
        hs (le_of_lt (lt_aleph0_of_finite _)) hK),
      ← lift_injective (cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _
        ht (le_of_lt (lt_aleph0_of_finite _)) hL)]
    exact Cardinal.lift_mk_eq'.2 hKL
  obtain ⟨e⟩ := Cardinal.lift_mk_eq'.1 this
  exact ⟨equivOfTranscendenceBasis _ _ e hs ht⟩

/-- Two uncountable algebraically closed fields are isomorphic
if they have the same cardinality and the same characteristic. -/
theorem ringEquiv_of_equiv_of_char_eq (p : ℕ) [CharP K p] [CharP L p] (hK : ℵ₀ < #K)
    (hKL : Nonempty (K ≃ L)) : Nonempty (K ≃+* L) := by
  rcases CharP.char_is_prime_or_zero K p with (hp | hp)
  · haveI : Fact p.Prime := ⟨hp⟩
    exact ringEquiv_of_Cardinal_eq_of_charP p hK hKL
  · simp only [hp] at *
    letI : CharZero K := CharP.charP_to_charZero K
    letI : CharZero L := CharP.charP_to_charZero L
    exact ringEquiv_of_equiv_of_charZero hK hKL

end IsAlgClosed
