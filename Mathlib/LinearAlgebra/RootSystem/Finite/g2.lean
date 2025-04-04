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
    (∀ j, P.pairing i j = P.pairing (short P) j + P.pairing (long P) j) ∧
    (∀ j, P.pairing j i = P.pairing j (short P) + 3 * P.pairing j (long P)) := by
  obtain ⟨g, hg⟩ := mem_orbit_iff.mp <| short_add_long_mem_orbit P
  let i := P.weylGroupToPerm g (short P)
  have hi : P.root i = shortRoot P + longRoot P := by simp [i, ← hg, Subgroup.smul_def]
  have hi' : B.form (P.root i) (P.root i) = B.form (shortRoot P) (shortRoot P) := by
    rw [← weylGroup_apply_root, B.apply_weylGroup_smul]
  refine ⟨i, hi, hi', fun j ↦ mul_right_cancel₀ (B.ne_zero j) ?_,
    fun j ↦ mul_right_cancel₀ (B.ne_zero i) ?_⟩
  · rw [← B.two_mul_apply_root_root]; simp [hi, mul_add, add_mul, B.two_mul_apply_root_root]
  · calc P.pairing j i * B.form (P.root i) (P.root i)
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
    (∀ j, P.pairing i j = 2 * P.pairing (short P) j + P.pairing (long P) j) ∧
    (∀ j, P.pairing j i = 2 * P.pairing j (short P) + 3 * P.pairing j (long P)) := by
  obtain ⟨g, hg⟩ := mem_orbit_iff.mp <| two_smul_short_add_long_mem_orbit P
  let i := P.weylGroupToPerm g (short P)
  have hi : P.root i = (2 : R) • shortRoot P + longRoot P := by simp [i, ← hg, Subgroup.smul_def]
  have hi' : B.form (P.root i) (P.root i) = B.form (shortRoot P) (shortRoot P) := by
    rw [← weylGroup_apply_root, B.apply_weylGroup_smul]
  refine ⟨i, hi, hi', fun j ↦ mul_right_cancel₀ (B.ne_zero j) ?_,
    fun j ↦ mul_right_cancel₀ (B.ne_zero i) ?_⟩
  · rw [← B.two_mul_apply_root_root]; simp [hi, mul_add, add_mul, B.two_mul_apply_root_root]; ring
  · calc P.pairing j i * B.form (P.root i) (P.root i)
      _ = 2 * B.form (P.root j) (P.root i) := ?_
      _ = 2 * (2 * B.form (P.root j) (shortRoot P)) + 2 * B.form (P.root j) (longRoot P) := ?_
      _ = 2 * P.pairing j (short P) * B.form (shortRoot P) (shortRoot P) +
            P.pairing j (long P) * B.form (longRoot P) (longRoot P) := ?_
      _ = (2 * P.pairing j (short P) + 3 * P.pairing j (long P)) * B.form (P.root i) (P.root i) :=?_
    · rw [B.two_mul_apply_root_root]
    · rw [hi, map_add, mul_add, map_smul, smul_eq_mul]
    · rw [B.two_mul_apply_root_root, B.two_mul_apply_root_root, mul_assoc]
    · rw [long_eq_three_mul_short, hi']; ring

lemma exists_root_eq_three_smul_short_add_long_and : ∃ i,
    P.root i = (3 : R) • shortRoot P + longRoot P ∧
    B.form (P.root i) (P.root i) = B.form (longRoot P) (longRoot P) ∧
    (∀ j, P.pairing i j = 3 * P.pairing (short P) j + P.pairing (long P) j) ∧
    (∀ j, P.pairing j i = P.pairing j (short P) + P.pairing j (long P)) := by
  obtain ⟨g, hg⟩ := mem_orbit_iff.mp <| three_smul_short_add_long_mem_orbit P
  let i := P.weylGroupToPerm g (long P)
  have hi : P.root i = (3 : R) • shortRoot P + longRoot P := by simp [i, ← hg, Subgroup.smul_def]
  have hi' : B.form (P.root i) (P.root i) = B.form (longRoot P) (longRoot P) := by
    rw [← weylGroup_apply_root, B.apply_weylGroup_smul]
  refine ⟨i, hi, hi', fun j ↦ mul_right_cancel₀ (B.ne_zero j) ?_,
    fun j ↦ mul_right_cancel₀ (B.ne_zero i) ?_⟩
  · rw [← B.two_mul_apply_root_root]
    simp [hi, mul_add, add_mul, B.two_mul_apply_root_root, mul_left_comm (2 : R) (3 : R)]; ring
  · calc P.pairing j i * B.form (P.root i) (P.root i)
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
    (∀ j, P.pairing i j = 3 * P.pairing (short P) j + 2 * P.pairing (long P) j) ∧
    (∀ j, P.pairing j i = P.pairing j (short P) + 2 * P.pairing j (long P)) := by
  obtain ⟨g, hg⟩ := mem_orbit_iff.mp <| three_smul_short_add_two_smul_long_mem_orbit P
  let i := P.weylGroupToPerm g (long P)
  have hi : P.root i = (3 : R) • shortRoot P + (2 : R) • longRoot P := by
    simp [i, ← hg, Subgroup.smul_def]
  have hi' : B.form (P.root i) (P.root i) = B.form (longRoot P) (longRoot P) := by
    rw [← weylGroup_apply_root, B.apply_weylGroup_smul]
  refine ⟨i, hi, hi', fun j ↦ mul_right_cancel₀ (B.ne_zero j) ?_,
    fun j ↦ mul_right_cancel₀ (B.ne_zero i) ?_⟩
  · rw [← B.two_mul_apply_root_root]
    simp [hi, mul_add, add_mul, B.two_mul_apply_root_root, mul_left_comm (2 : R) (3 : R)]; ring
  · calc P.pairing j i * B.form (P.root i) (P.root i)
      _ = 2 * B.form (P.root j) (P.root i) := ?_
      _ = 3 * (2 * B.form (P.root j) (shortRoot P)) + 2 * (2 * B.form (P.root j) (longRoot P)) := ?_
      _ = P.pairing j (short P) * B.form (longRoot P) (longRoot P) +
            2 * P.pairing j (long P) * B.form (longRoot P) (longRoot P) := ?_
      _ = (P.pairing j (short P) + 2 * P.pairing j (long P)) * B.form (P.root i) (P.root i) := ?_
    · rw [B.two_mul_apply_root_root]
    · rw [hi, map_add, mul_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]; ring
    · rw [B.two_mul_apply_root_root, B.two_mul_apply_root_root, long_eq_three_mul_short]; ring
    · rw [hi']; ring

-- TODO Find a way to excise this lemma.
omit [Finite ι] [CharZero R] [IsDomain R] [NoZeroSMulDivisors R M] in
private lemma ne_and_ne_neg {k : ι} (l : ι) (hk : P.root k ∉ span R {longRoot P, shortRoot P})
    (hl : P.root l ∈ span R {longRoot P, shortRoot P}) :
      k ≠ l ∧ P.root k ≠ - P.root l := by
    contrapose! hk
    rcases eq_or_ne k l with rfl | hkl; · assumption
    rw [hk hkl]
    exact neg_mem hl

lemma isOrthogonal_short_and_long
    {k : ι} (hk : P.root k ∉ span R {longRoot P, shortRoot P}) :
    P.IsOrthogonal k (short P) ∧ P.IsOrthogonal k (long P) := by
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm ℤ).toInvariantForm
  suffices P.pairingIn ℤ k (short P) = 0 ∧ P.pairingIn ℤ k (long P) = 0 by
    simpa [B.isOrthogonal_iff_pairingIn_eq_zero, ← P.algebraMap_pairingIn ℤ]
  obtain ⟨i, hi₁, hi₂, hi₃, hi₄⟩ := exists_root_eq_short_add_long_and B
  obtain ⟨j, hj₁, hj₂, hj₃, hj₄⟩ := exists_root_eq_two_smul_short_add_long_and B
  obtain ⟨l, hl₁, hl₂, hl₃, hl₄⟩ := exists_root_eq_three_smul_short_add_long_and B
  obtain ⟨m, hm₁, hm₂, hm₃, hm₄⟩ := exists_root_eq_three_smul_short_add_two_smul_long_and B
  specialize hi₃ k; specialize hi₄ k
  specialize hj₃ k; specialize hj₄ k
  specialize hl₃ k; specialize hl₄ k
  specialize hm₃ k; specialize hm₄ k
  have h2 : OfNat.ofNat (2 : ℕ) = (2 : ℤ) := by rw [← Int.cast_two]
  have h3 : OfNat.ofNat (3 : ℕ) = (3 : ℤ) := by rw [← Int.cast_three]
  simp only [← P.algebraMap_pairingIn ℤ, ← map_add, ← map_mul, ← map_ofNat (algebraMap ℤ R) 2,
    ← map_ofNat (algebraMap ℤ R) 3, h2, h3,
    (algebraMap_injective ℤ R).eq_iff] at hi₃ hi₄ hj₃ hj₄ hl₃ hl₄ hm₃ hm₄
  -- TODO Find a way to excise the silly repetition below.
  have hshort : (P.pairingIn ℤ k (short P), P.pairingIn ℤ (short P) k) ∈ ({(0, 0), (1, 1), (-1, -1),
      (1, 2), (2, 1), (-1, -2), (-2, -1), (1, 3), (3, 1), (-1, -3), (-3, -1)} : Set (ℤ × ℤ)) := by
    have := ne_and_ne_neg (short P) hk (subset_span <| mem_insert_of_mem _ rfl)
    exact P.pairingIn_pairingIn_mem_set_of_isCrystallographic_of_isReduced' _ _ this.1 this.2
  have hlong : (P.pairingIn ℤ k (long P), P.pairingIn ℤ (long P) k) ∈ ({(0, 0), (1, 1), (-1, -1),
      (1, 2), (2, 1), (-1, -2), (-2, -1), (1, 3), (3, 1), (-1, -3), (-3, -1)} : Set (ℤ × ℤ)) := by
    have := ne_and_ne_neg (long P) hk (subset_span <| mem_insert _ _)
    exact P.pairingIn_pairingIn_mem_set_of_isCrystallographic_of_isReduced' _ _ this.1 this.2
  have hi₅ : (P.pairingIn ℤ k i, P.pairingIn ℤ i k) ∈ ({(0, 0), (1, 1), (-1, -1),
      (1, 2), (2, 1), (-1, -2), (-2, -1), (1, 3), (3, 1), (-1, -3), (-3, -1)} : Set (ℤ × ℤ)) := by
    have := ne_and_ne_neg i hk (hi₁ ▸ add_mem (subset_span <| mem_insert_of_mem _ rfl)
      (subset_span <| mem_insert _ _))
    exact P.pairingIn_pairingIn_mem_set_of_isCrystallographic_of_isReduced' _ _ this.1 this.2
  have hj₅ : (P.pairingIn ℤ k j, P.pairingIn ℤ j k) ∈ ({(0, 0), (1, 1), (-1, -1),
      (1, 2), (2, 1), (-1, -2), (-2, -1), (1, 3), (3, 1), (-1, -3), (-3, -1)} : Set (ℤ × ℤ)) := by
    have := ne_and_ne_neg j hk (hj₁ ▸ add_mem (Submodule.smul_mem _ _ <| subset_span <|
      mem_insert_of_mem _ rfl) (subset_span <| mem_insert _ _))
    exact P.pairingIn_pairingIn_mem_set_of_isCrystallographic_of_isReduced' _ _ this.1 this.2
  have hl₅ : (P.pairingIn ℤ k l, P.pairingIn ℤ l k) ∈ ({(0, 0), (1, 1), (-1, -1),
      (1, 2), (2, 1), (-1, -2), (-2, -1), (1, 3), (3, 1), (-1, -3), (-3, -1)} : Set (ℤ × ℤ)) := by
    have := ne_and_ne_neg l hk (hl₁ ▸ add_mem (Submodule.smul_mem _ _ <| subset_span <|
      mem_insert_of_mem _ rfl) (subset_span <| mem_insert _ _))
    exact P.pairingIn_pairingIn_mem_set_of_isCrystallographic_of_isReduced' _ _ this.1 this.2
  have hm₅ : (P.pairingIn ℤ k m, P.pairingIn ℤ m k) ∈ ({(0, 0), (1, 1), (-1, -1),
      (1, 2), (2, 1), (-1, -2), (-2, -1), (1, 3), (3, 1), (-1, -3), (-3, -1)} : Set (ℤ × ℤ)) := by
    have := ne_and_ne_neg m hk (hm₁ ▸ add_mem (Submodule.smul_mem _ _ <| subset_span <|
      mem_insert_of_mem _ rfl) (Submodule.smul_mem _ _ <| subset_span <| mem_insert _ _))
    exact P.pairingIn_pairingIn_mem_set_of_isCrystallographic_of_isReduced' _ _ this.1 this.2
  simp at hshort hlong hi₅ hj₅ hl₅ hm₅
  omega

variable (P)

@[simp] lemma span_eq_top [Invertible (2 : R)] [P.IsIrreducible] :
    span R {longRoot P, shortRoot P} = ⊤ := by
  have := P.span_root_image_eq_top_of_forall_orthogonal {long P, short P} (by simp)
  rw [show P.root '' {long P, short P} = {longRoot P, shortRoot P} from by aesop] at this
  refine this fun k hk ij hij ↦ ?_
  have aux := isOrthogonal_short_and_long hk
  rcases hij with rfl | rfl <;> tauto

end EmbeddedG2

end RootPairing
