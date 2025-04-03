/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

/-!
# Properties of the `𝔤₂` root system.

Foo bar

## Main results:
 * `RootPairing.EmbeddedG2`: a data-bearing typeclass which distinguishes a pair of roots whose
   pairing is `-3`. This is a sufficient condition for the span of this pair of roots to be a `𝔤₂`
   root system.
 * `RootPairing.EmbeddedG2.span_eq_top`: a finite crystallographic reduced irreducible root pairing
   containing two roots with pairing `-3` is spanned by this pair (thus two-dimensional).

-/

noncomputable section

open Function Set
open MulAction (orbit mem_orbit_iff)
open Submodule (span subset_span)
open FaithfulSMul (algebraMap_injective)

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

namespace RootPairing

/-- A data-bearing typeclass which distinguishes a pair of roots whose pairing is `-3`. This is a
sufficient condition for the span of this pair of roots to be a `𝔤₂` root system. -/
class EmbeddedG2 extends P.IsCrystallographic, P.IsReduced where
  long : ι
  short : ι
  pairingIn_neg_three : P.pairingIn ℤ long short = - 3

namespace EmbeddedG2

/-- A pair of roots which pair to `+3` are also sufficient to distinguish an embedded `𝔤₂`. -/
@[simps] def ofPairingInThree [CharZero R] [P.IsCrystallographic] [P.IsReduced] (long short : ι)
    (h : P.pairingIn ℤ long short = 3) : P.EmbeddedG2 where
  long := P.reflection_perm long long
  short := short
  pairingIn_neg_three := by simp [h]

variable [P.EmbeddedG2]

abbrev shortRoot := P.root (short P)
abbrev longRoot := P.root (long P)

attribute [simp] pairingIn_neg_three

@[simp]
lemma pairing_neg_three : P.pairing (long P) (short P) = - 3 := by
  rw [← P.algebraMap_pairingIn ℤ, pairingIn_neg_three]
  simp

variable [Finite ι] [CharZero R] [IsDomain R] [NoZeroSMulDivisors R M]

@[simp]
lemma pairingIn_neg_one :
    P.pairingIn ℤ (short P) (long P) = - 1 := by
  have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic_of_isReduced (long P) (short P)
  have := pairingIn_neg_three (P := P)
  aesop

@[simp]
lemma pairing_neg_one :
    P.pairing (short P) (long P) = - 1 := by
  rw [← P.algebraMap_pairingIn ℤ, pairingIn_neg_one]
  simp

lemma short_add_long_mem_orbit :
    shortRoot P + longRoot P ∈ orbit P.weylGroup (shortRoot P) := by
  use weylGroup.ofIdx P (long P)
  simp [reflection_apply_root]

lemma two_smul_short_add_long_mem_orbit :
    (2 : R) • shortRoot P + longRoot P ∈ orbit P.weylGroup (shortRoot P) := by
  use weylGroup.ofIdx P (short P) * weylGroup.ofIdx P (long P)
  simp [mul_smul, reflection_apply_root]
  module

omit [Finite ι] [CharZero R] [IsDomain R] [NoZeroSMulDivisors R M] in
lemma three_smul_short_add_long_mem_orbit :
    (3 : R) • shortRoot P + longRoot P ∈ orbit P.weylGroup (longRoot P) := by
  use weylGroup.ofIdx P (short P)
  simp [reflection_apply_root]
  module

lemma three_smul_short_add_two_smul_long_mem_orbit :
    (3 : R) • shortRoot P + (2 : R) • longRoot P ∈ orbit P.weylGroup (longRoot P) := by
  use weylGroup.ofIdx P (long P) * weylGroup.ofIdx P (short P)
  simp [mul_smul, reflection_apply_root]
  module

variable {P}
variable (B : P.InvariantForm)

lemma long_eq_three_mul_short :
    B.form (longRoot P) (longRoot P) = 3 * B.form (shortRoot P) (shortRoot P) := by
  simpa using B.pairing_mul_eq_pairing_mul_swap (long P) (short P)

-- TODO Replace the lemmas above about orbits and the lemmas below about existentials with
-- a definition for each of these four roots + API about these definitions corresponding to the
-- clauses appearing in the various lemmas.

lemma exists_root_eq_short_add_long_and : ∃ i,
    P.root i = shortRoot P + longRoot P ∧
    B.form (P.root i) (P.root i) = B.form (shortRoot P) (shortRoot P) ∧
    ∀ j, P.pairing j i = P.pairing j (short P) + 3 * P.pairing j (long P) := by
  obtain ⟨g, hg⟩ := mem_orbit_iff.mp <| short_add_long_mem_orbit P
  let i := P.weylGroupToPerm g (short P)
  have hi : P.root i = shortRoot P + longRoot P := by simp [i, ← hg, Subgroup.smul_def]
  have hi' : B.form (P.root i) (P.root i) = B.form (shortRoot P) (shortRoot P) := by
    rw [← weylGroup_apply_root, B.apply_weylGroup_smul]
  refine ⟨i, hi, hi', fun j ↦ mul_right_cancel₀ (B.ne_zero i) ?_⟩
  calc P.pairing j i * B.form (P.root i) (P.root i)
    _ = 2 * B.form (P.root j) (P.root i) := ?_
    _ = 2 * B.form (P.root j) (shortRoot P) + 2 * B.form (P.root j) (longRoot P) := ?_
    _ = P.pairing j (short P) * B.form (shortRoot P) (shortRoot P) +
          P.pairing j (long P) * B.form (longRoot P) (longRoot P) := ?_
    _ = (P.pairing j (short P) + 3 * P.pairing j (long P)) * B.form (P.root i) (P.root i) := ?_
  · rw [B.two_mul_apply_root_root]
  · rw [hi, map_add, mul_add]
  · rw [B.two_mul_apply_root_root, B.two_mul_apply_root_root]
  · rw [long_eq_three_mul_short, hi']; ring

lemma exists_root_eq_two_smul_short_add_long_and : ∃ i,
    P.root i = (2 : R) • shortRoot P + longRoot P ∧
    B.form (P.root i) (P.root i) = B.form (shortRoot P) (shortRoot P) ∧
    ∀ j, P.pairing j i = 2 * P.pairing j (short P) + 3 * P.pairing j (long P) := by
  obtain ⟨g, hg⟩ := mem_orbit_iff.mp <| two_smul_short_add_long_mem_orbit P
  let i := P.weylGroupToPerm g (short P)
  have hi : P.root i = (2 : R) • shortRoot P + longRoot P := by simp [i, ← hg, Subgroup.smul_def]
  have hi' : B.form (P.root i) (P.root i) = B.form (shortRoot P) (shortRoot P) := by
    rw [← weylGroup_apply_root, B.apply_weylGroup_smul]
  refine ⟨i, hi, hi', fun j ↦ mul_right_cancel₀ (B.ne_zero i) ?_⟩
  calc P.pairing j i * B.form (P.root i) (P.root i)
    _ = 2 * B.form (P.root j) (P.root i) := ?_
    _ = 2 * (2 * B.form (P.root j) (shortRoot P)) + 2 * B.form (P.root j) (longRoot P) := ?_
    _ = 2 * P.pairing j (short P) * B.form (shortRoot P) (shortRoot P) +
          P.pairing j (long P) * B.form (longRoot P) (longRoot P) := ?_
    _ = (2 * P.pairing j (short P) + 3 * P.pairing j (long P)) * B.form (P.root i) (P.root i) := ?_
  · rw [B.two_mul_apply_root_root]
  · rw [hi, map_add, mul_add, map_smul, smul_eq_mul]
  · rw [B.two_mul_apply_root_root, B.two_mul_apply_root_root, mul_assoc]
  · rw [long_eq_three_mul_short, hi']; ring

lemma exists_root_eq_three_smul_short_add_long_and : ∃ i,
    P.root i = (3 : R) • shortRoot P + longRoot P ∧
    B.form (P.root i) (P.root i) = B.form (longRoot P) (longRoot P) ∧
    ∀ j, P.pairing j i = P.pairing j (short P) + P.pairing j (long P) := by
  obtain ⟨g, hg⟩ := mem_orbit_iff.mp <| three_smul_short_add_long_mem_orbit P
  let i := P.weylGroupToPerm g (long P)
  have hi : P.root i = (3 : R) • shortRoot P + longRoot P := by simp [i, ← hg, Subgroup.smul_def]
  have hi' : B.form (P.root i) (P.root i) = B.form (longRoot P) (longRoot P) := by
    rw [← weylGroup_apply_root, B.apply_weylGroup_smul]
  refine ⟨i, hi, hi', fun j ↦ mul_right_cancel₀ (B.ne_zero i) ?_⟩
  calc P.pairing j i * B.form (P.root i) (P.root i)
    _ = 2 * B.form (P.root j) (P.root i) := ?_
    _ = 3 * (2 * B.form (P.root j) (shortRoot P)) + 2 * B.form (P.root j) (longRoot P) := ?_
    _ = P.pairing j (short P) * B.form (longRoot P) (longRoot P) +
          P.pairing j (long P) * B.form (longRoot P) (longRoot P) := ?_
    _ = (P.pairing j (short P) + P.pairing j (long P)) * B.form (P.root i) (P.root i) := ?_
  · rw [B.two_mul_apply_root_root]
  · rw [hi, map_add, mul_add, map_smul, smul_eq_mul]; ring
  · rw [B.two_mul_apply_root_root, B.two_mul_apply_root_root, long_eq_three_mul_short]; ring
  · rw [hi']; ring

lemma exists_root_eq_three_smul_short_add_two_smul_long_and : ∃ i,
    P.root i = (3 : R) • shortRoot P + (2 : R) • longRoot P ∧
    B.form (P.root i) (P.root i) = B.form (longRoot P) (longRoot P) ∧
    ∀ j, P.pairing j i = P.pairing j (short P) + 2 * P.pairing j (long P) := by
  obtain ⟨g, hg⟩ := mem_orbit_iff.mp <| three_smul_short_add_two_smul_long_mem_orbit P
  let i := P.weylGroupToPerm g (long P)
  have hi : P.root i = (3 : R) • shortRoot P + (2 : R) • longRoot P := by
    simp [i, ← hg, Subgroup.smul_def]
  have hi' : B.form (P.root i) (P.root i) = B.form (longRoot P) (longRoot P) := by
    rw [← weylGroup_apply_root, B.apply_weylGroup_smul]
  refine ⟨i, hi, hi', fun j ↦ mul_right_cancel₀ (B.ne_zero i) ?_⟩
  calc P.pairing j i * B.form (P.root i) (P.root i)
    _ = 2 * B.form (P.root j) (P.root i) := ?_
    _ = 3 * (2 * B.form (P.root j) (shortRoot P)) + 2 * (2 * B.form (P.root j) (longRoot P)) := ?_
    _ = P.pairing j (short P) * B.form (longRoot P) (longRoot P) +
          2 * P.pairing j (long P) * B.form (longRoot P) (longRoot P) := ?_
    _ = (P.pairing j (short P) + 2 * P.pairing j (long P)) * B.form (P.root i) (P.root i) := ?_
  · rw [B.two_mul_apply_root_root]
  · rw [hi, map_add, mul_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]; ring
  · rw [B.two_mul_apply_root_root, B.two_mul_apply_root_root, long_eq_three_mul_short]; ring
  · rw [hi']; ring

variable {B}
variable {k : ι} (hk : P.root k ∉ span R {longRoot P, shortRoot P})
include hk

-- Pretty horrible lemma. Think again if this is best we can do.
omit [Finite ι] [CharZero R] [IsDomain R] [NoZeroSMulDivisors R M] in
private lemma ne_and_ne_neg {l : ι} (hl : P.root l ∈ span R {longRoot P, shortRoot P}) :
      k ≠ l ∧ P.root k ≠ - P.root l := by
    contrapose! hk
    rcases eq_or_ne k l with rfl | hkl; · assumption
    rw [hk hkl]
    exact neg_mem hl

lemma isOrthogonal_short_and_long_of_len_short
    (h_len : B.form (P.root k) (P.root k) = B.form (shortRoot P) (shortRoot P)) :
    P.IsOrthogonal k (long P) ∧ P.IsOrthogonal k (short P) := by
  suffices P.pairingIn ℤ k (long P) = 0 ∧ P.pairingIn ℤ k (short P) = 0 by
    simpa [B.isOrthogonal_iff_pairingIn_eq_zero, ← P.algebraMap_pairingIn ℤ]
  obtain ⟨i, hi₁, hi₂, hi₃⟩ := exists_root_eq_short_add_long_and B
  obtain ⟨j, hj₁, hj₂, hj₃⟩ := exists_root_eq_two_smul_short_add_long_and B
  -- TODO How to tidy up this `∈ span` stuff? Just part of API planned definitions?
  have hshort : shortRoot P ∈ span R {longRoot P, shortRoot P} :=
    subset_span <| mem_insert_of_mem _ rfl
  have hi₄ : P.root i ∈ span R {longRoot P, shortRoot P} :=
    hi₁ ▸ add_mem (subset_span <| mem_insert_of_mem _ rfl) (subset_span <| mem_insert _ _)
  have hj₄ : P.root j ∈ span R {longRoot P, shortRoot P} :=
    hj₁ ▸ add_mem (Submodule.smul_mem _ _ hshort) (subset_span <| mem_insert _ _)
  let a := P.pairingIn ℤ k (long P)
  let b := P.pairingIn ℤ k (short P)
  let c := P.pairingIn ℤ k i
  let d := P.pairingIn ℤ k j
  change a = 0 ∧ b = 0
  -- TODO How to tidy up the repetition below?
  have hb : b ∈ Icc (-1) 1 := by
    have := P.pairingIn_pairingIn_mem_set_of_length_eq_of_ne (i := k) (j := short P) (B := B)
      h_len (ne_and_ne_neg hk hshort).1 (ne_and_ne_neg hk hshort).2
    simp at this ⊢
    omega
  have hc : c ∈ Icc (-1) 1 := by
    have := P.pairingIn_pairingIn_mem_set_of_length_eq_of_ne (i := k) (j := i) (B := B)
      (by rw [h_len, hi₂]) (ne_and_ne_neg hk hi₄).1 (ne_and_ne_neg hk hi₄).2
    simp at this ⊢
    omega
  have hd : d ∈ Icc (-1) 1 := by
    have := P.pairingIn_pairingIn_mem_set_of_length_eq_of_ne (i := k) (j := j) (B := B)
      (by rw [h_len, hj₂]) (ne_and_ne_neg hk hj₄).1 (ne_and_ne_neg hk hj₄).2
    simp at this ⊢
    omega
  have habc : c = b + 3 * a := algebraMap_injective ℤ R <| by
    simpa only [a, b, c, algebraMap_pairingIn, map_add, map_mul, map_ofNat] using hi₃ k
  have habd : d = 2 * b + 3 * a := algebraMap_injective ℤ R <| by
    simpa only [a, b, d, algebraMap_pairingIn, map_add, map_mul, map_ofNat] using hj₃ k
  simp only [mem_Icc] at hb hc hd
  omega

-- Can we unify with lemma above and avoid all this repetition?
lemma isOrthogonal_short_and_long_of_len_long
    (h_len : B.form (P.root k) (P.root k) = B.form (longRoot P) (longRoot P)) :
    P.IsOrthogonal k (long P) ∧ P.IsOrthogonal k (short P) := by
  suffices P.pairingIn ℤ k (long P) = 0 ∧ P.pairingIn ℤ k (short P) = 0 by
    simpa [B.isOrthogonal_iff_pairingIn_eq_zero, ← P.algebraMap_pairingIn ℤ]
  obtain ⟨i, hi₁, hi₂, hi₃⟩ := exists_root_eq_three_smul_short_add_long_and B
  obtain ⟨j, hj₁, hj₂, hj₃⟩ := exists_root_eq_three_smul_short_add_two_smul_long_and B
  have hlong : longRoot P ∈ span R {longRoot P, shortRoot P} := subset_span <| mem_insert _ _
  have hi₄ : P.root i ∈ span R {longRoot P, shortRoot P} :=
    hi₁ ▸ add_mem (Submodule.smul_mem _ _ <| subset_span <| mem_insert_of_mem _ rfl)
      (subset_span <| mem_insert _ _)
  have hj₄ : P.root j ∈ span R {longRoot P, shortRoot P} :=
    hj₁ ▸ add_mem (Submodule.smul_mem _ _ <| subset_span <| mem_insert_of_mem _ rfl)
      (Submodule.smul_mem _ _ <| subset_span <| mem_insert _ _)
  let a := P.pairingIn ℤ k (long P)
  let b := P.pairingIn ℤ k (short P)
  let e := P.pairingIn ℤ k i
  let f := P.pairingIn ℤ k j
  change a = 0 ∧ b = 0
  have ha : a ∈ Icc (-1) 1 := by
    have := P.pairingIn_pairingIn_mem_set_of_length_eq_of_ne (i := k) (j := long P) (B := B)
      h_len (ne_and_ne_neg hk hlong).1 (ne_and_ne_neg hk hlong).2
    simp at this ⊢
    omega
  have hb : b ∈ Icc (-3) 3 ∧ 3 ∣ b := by
    simp only [b]
    suffices P.pairingIn ℤ k (short P) = P.pairingIn ℤ (short P) k * 3 by
      constructor
      · have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic_of_isReduced k (short P)
        -- The below should just be `aesop` but unfortunately it chokes.
        simp only [Prod.mk_zero_zero, Prod.mk_one_one, mem_insert_iff,
          Prod.mk_eq_zero, Prod.mk_eq_one, Prod.mk.injEq, mem_singleton_iff,
          mem_Icc] at this ⊢
        rcases this with ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ |
           ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ <;> rw [l] <;> norm_num
      · rw [this]
        exact Int.dvd_mul_left _ 3
    suffices P.pairing k (short P) = P.pairing (short P) k * 3 by
      apply algebraMap_injective ℤ R
      simp only [algebraMap_pairingIn, map_mul]
      simpa only [algebraMap_int_eq, eq_intCast, Int.cast_ofNat]
    apply mul_right_cancel₀ (B.ne_zero <| short P)
    rw [mul_assoc, ← long_eq_three_mul_short B, B.pairing_mul_eq_pairing_mul_swap (short P) k,
      h_len]
  have he : e ∈ Icc (-1) 1 := by
    have := P.pairingIn_pairingIn_mem_set_of_length_eq_of_ne (i := k) (j := i) (B := B)
      (by rw [h_len, hi₂]) (ne_and_ne_neg hk hi₄).1 (ne_and_ne_neg hk hi₄).2
    simp at this ⊢
    omega
  have hf : f ∈ Icc (-1) 1 := by
    have := P.pairingIn_pairingIn_mem_set_of_length_eq_of_ne (i := k) (j := j) (B := B)
      (by rw [h_len, hj₂]) (ne_and_ne_neg hk hj₄).1 (ne_and_ne_neg hk hj₄).2
    simp at this ⊢
    omega
  have habe : e = b + a := algebraMap_injective ℤ R <| by
    simpa only [a, b, e, algebraMap_pairingIn, map_add, map_mul, map_ofNat] using hi₃ k
  have habf : f = b + 2 * a := algebraMap_injective ℤ R <| by
    simpa only [a, b, f, algebraMap_pairingIn, map_add, map_mul, map_ofNat] using hj₃ k
  simp only [mem_Icc] at ha hb he hf
  omega

variable [P.IsIrreducible]

lemma isOrthogonal_short_and_long_of_isIrreducible :
    P.IsOrthogonal k (long P) ∧ P.IsOrthogonal k (short P) := by
  have : Fintype ι := Fintype.ofFinite ι
  have B : P.InvariantForm := (P.posRootForm ℤ).toInvariantForm
  have len : B.form (longRoot P) (longRoot P) ≠ B.form (shortRoot P) (shortRoot P) := by
    simp [long_eq_three_mul_short B]
  rcases B.apply_eq_or_of_apply_ne len k with long | short
  · exact isOrthogonal_short_and_long_of_len_long hk long
  · exact isOrthogonal_short_and_long_of_len_short hk short

omit hk

variable (P)

@[simp] lemma span_eq_top [Invertible (2 : R)] :
    span R {longRoot P, shortRoot P} = ⊤ := by
  have := P.span_root_image_eq_top_of_forall_orthogonal {long P, short P} (by simp)
  rw [show P.root '' {long P, short P} = {longRoot P, shortRoot P} from by aesop] at this
  refine this fun k hk ij hij ↦ ?_
  have aux := isOrthogonal_short_and_long_of_isIrreducible hk
  rcases hij with rfl | rfl <;> tauto

end EmbeddedG2

end RootPairing
