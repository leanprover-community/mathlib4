/-
Copyright (c) 2022 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.RingTheory.AlgebraicIndependent
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Data.Polynomial.Cardinal
import Mathlib.Data.MvPolynomial.Cardinal
import Mathlib.Data.ZMod.Algebra

#align_import field_theory.is_alg_closed.classification from "leanprover-community/mathlib"@"0723536a0522d24fc2f159a096fb3304bef77472"

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

section AlgebraicClosure

namespace Algebra.IsAlgebraic

variable (R L : Type u) [CommRing R] [CommRing L] [IsDomain L] [Algebra R L]

variable [NoZeroSMulDivisors R L] (halg : Algebra.IsAlgebraic R L)

theorem cardinal_mk_le_sigma_polynomial :
    #L ≤ #(Σ p : R[X], { x : L // x ∈ (p.map (algebraMap R L)).roots }) :=
  @mk_le_of_injective L (Σ p : R[X], {x : L | x ∈ (p.map (algebraMap R L)).roots})
    (fun x : L =>
      let p := Classical.indefiniteDescription _ (halg x)
      ⟨p.1, x, by
        dsimp
        -- ⊢ x ∈ Polynomial.roots (Polynomial.map (algebraMap R L) ↑(Classical.indefinite …
        have h : p.1.map (algebraMap R L) ≠ 0 := by
          rw [Ne.def, ← Polynomial.degree_eq_bot,
            Polynomial.degree_map_eq_of_injective (NoZeroSMulDivisors.algebraMap_injective R L),
            Polynomial.degree_eq_bot]
          exact p.2.1
        erw [Polynomial.mem_roots h, Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def,
          p.2.2]⟩)
    fun x y => by
      intro h
      -- ⊢ x = y
      simp at h
      -- ⊢ x = y
      refine' (Subtype.heq_iff_coe_eq _).1 h.2
      -- ⊢ ∀ (x_1 : L), x_1 ∈ {x_2 | x_2 ∈ Polynomial.roots (Polynomial.map (algebraMap …
      simp only [h.1, iff_self_iff, forall_true_iff]
      -- 🎉 no goals
#align algebra.is_algebraic.cardinal_mk_le_sigma_polynomial Algebra.IsAlgebraic.cardinal_mk_le_sigma_polynomial

/-- The cardinality of an algebraic extension is at most the maximum of the cardinality
of the base ring or `ℵ₀` -/
theorem cardinal_mk_le_max : #L ≤ max #R ℵ₀ :=
  calc
    #L ≤ #(Σ p : R[X], { x : L // x ∈ (p.map (algebraMap R L)).roots }) :=
      cardinal_mk_le_sigma_polynomial R L halg
    _ = Cardinal.sum fun p : R[X] => #{x : L | x ∈ (p.map (algebraMap R L)).roots} := by
      rw [← mk_sigma]; rfl
      -- ⊢ #((p : R[X]) × { x // x ∈ Polynomial.roots (Polynomial.map (algebraMap R L)  …
                       -- 🎉 no goals
    _ ≤ Cardinal.sum.{u, u} fun _ : R[X] => ℵ₀ :=
      (sum_le_sum _ _ fun p => (Multiset.finite_toSet _).lt_aleph0.le)
    _ = #(R[X]) * ℵ₀ := (sum_const' _ _)
    _ ≤ max (max #(R[X]) ℵ₀) ℵ₀ := (mul_le_max _ _)
    _ ≤ max (max (max #R ℵ₀) ℵ₀) ℵ₀ :=
      (max_le_max (max_le_max Polynomial.cardinal_mk_le_max le_rfl) le_rfl)
    _ = max #R ℵ₀ := by simp only [max_assoc, max_comm ℵ₀, max_left_comm ℵ₀, max_self]
                        -- 🎉 no goals
#align algebra.is_algebraic.cardinal_mk_le_max Algebra.IsAlgebraic.cardinal_mk_le_max

end Algebra.IsAlgebraic

end AlgebraicClosure

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
  { alg_closed := by infer_instance
                     -- 🎉 no goals
    algebraic := hv.isAlgebraic }
#align is_alg_closed.is_alg_closure_of_transcendence_basis IsAlgClosed.isAlgClosure_of_transcendence_basis

variable (hw : AlgebraicIndependent R w)

/-- setting `R` to be `ZMod (ringChar R)` this result shows that if two algebraically
closed fields have equipotent transcendence bases and the same characteristic then they are
isomorphic. -/
def equivOfTranscendenceBasis [IsAlgClosed K] [IsAlgClosed L] (e : ι ≃ κ)
    (hv : IsTranscendenceBasis R v) (hw : IsTranscendenceBasis R w) : K ≃+* L := by
  letI := isAlgClosure_of_transcendence_basis v hv
  -- ⊢ K ≃+* L
  letI := isAlgClosure_of_transcendence_basis w hw
  -- ⊢ K ≃+* L
  have e : Algebra.adjoin R (Set.range v) ≃+* Algebra.adjoin R (Set.range w)
  -- ⊢ { x // x ∈ Algebra.adjoin R (Set.range v) } ≃+* { x // x ∈ Algebra.adjoin R  …
  · refine' hv.1.aevalEquiv.symm.toRingEquiv.trans _
    -- ⊢ MvPolynomial ι R ≃+* { x // x ∈ Algebra.adjoin R (Set.range w) }
    refine' (AlgEquiv.ofAlgHom (MvPolynomial.rename e)
      (MvPolynomial.rename e.symm) _ _).toRingEquiv.trans _
    · ext; simp
      -- ⊢ MvPolynomial.coeff m✝ (↑(AlgHom.comp (MvPolynomial.rename ↑e) (MvPolynomial. …
           -- 🎉 no goals
    · ext; simp
      -- ⊢ MvPolynomial.coeff m✝ (↑(AlgHom.comp (MvPolynomial.rename ↑e.symm) (MvPolyno …
           -- 🎉 no goals
    exact hw.1.aevalEquiv.toRingEquiv
    -- 🎉 no goals
  exact IsAlgClosure.equivOfEquiv K L e
  -- 🎉 no goals
#align is_alg_closed.equiv_of_transcendence_basis IsAlgClosed.equivOfTranscendenceBasis

end

end Classification

section Cardinal

variable {R L K : Type u} [CommRing R]

variable [Field K] [Algebra R K] [IsAlgClosed K]

variable {ι : Type u} (v : ι → K)

variable (hv : IsTranscendenceBasis R v)

theorem cardinal_le_max_transcendence_basis (hv : IsTranscendenceBasis R v) :
    #K ≤ max (max #R #ι) ℵ₀ :=
  calc
    #K ≤ max #(Algebra.adjoin R (Set.range v)) ℵ₀ :=
      letI := isAlgClosure_of_transcendence_basis v hv
      Algebra.IsAlgebraic.cardinal_mk_le_max _ _ IsAlgClosure.algebraic
    _ = max #(MvPolynomial ι R) ℵ₀ := by rw [Cardinal.eq.2 ⟨hv.1.aevalEquiv.toEquiv⟩]
                                         -- 🎉 no goals
    _ ≤ max (max (max #R #ι) ℵ₀) ℵ₀ := (max_le_max MvPolynomial.cardinal_mk_le_max le_rfl)
    _ = _ := by simp [max_assoc]
                -- 🎉 no goals
#align is_alg_closed.cardinal_le_max_transcendence_basis IsAlgClosed.cardinal_le_max_transcendence_basis

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
        -- ⊢ #R ≤ #ι
        · exact le_trans hR this
          -- 🎉 no goals
        · exact le_max_of_le_right this)
          -- 🎉 no goals
    (mk_le_of_injective (show Function.Injective v from hv.1.injective))
#align is_alg_closed.cardinal_eq_cardinal_transcendence_basis_of_aleph_0_lt IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt

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
  -- ⊢ Nonempty (K ≃+* L)
  exact ⟨equivOfTranscendenceBasis _ _ e hs ht⟩
  -- 🎉 no goals
#align is_alg_closed.ring_equiv_of_cardinal_eq_of_char_zero IsAlgClosed.ringEquivOfCardinalEqOfCharZero

private theorem ringEquivOfCardinalEqOfCharP (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p]
    (hK : ℵ₀ < #K) (hKL : #K = #L) : Nonempty (K ≃+* L) := by
  letI : Algebra (ZMod p) K := ZMod.algebra _ _
  -- ⊢ Nonempty (K ≃+* L)
  letI : Algebra (ZMod p) L := ZMod.algebra _ _
  -- ⊢ Nonempty (K ≃+* L)
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
  -- ⊢ Nonempty (K ≃+* L)
  exact ⟨equivOfTranscendenceBasis _ _ e hs ht⟩
  -- 🎉 no goals

/-- Two uncountable algebraically closed fields are isomorphic
if they have the same cardinality and the same characteristic. -/
theorem ringEquivOfCardinalEqOfCharEq (p : ℕ) [CharP K p] [CharP L p] (hK : ℵ₀ < #K)
    (hKL : #K = #L) : Nonempty (K ≃+* L) := by
  rcases CharP.char_is_prime_or_zero K p with (hp | hp)
  -- ⊢ Nonempty (K ≃+* L)
  · haveI : Fact p.Prime := ⟨hp⟩
    -- ⊢ Nonempty (K ≃+* L)
    exact ringEquivOfCardinalEqOfCharP p hK hKL
    -- 🎉 no goals
  · simp only [hp] at *
    -- ⊢ Nonempty (K ≃+* L)
    letI : CharZero K := CharP.charP_to_charZero K
    -- ⊢ Nonempty (K ≃+* L)
    letI : CharZero L := CharP.charP_to_charZero L
    -- ⊢ Nonempty (K ≃+* L)
    exact ringEquivOfCardinalEqOfCharZero hK hKL
    -- 🎉 no goals
#align is_alg_closed.ring_equiv_of_cardinal_eq_of_char_eq IsAlgClosed.ringEquivOfCardinalEqOfCharEq

end IsAlgClosed
