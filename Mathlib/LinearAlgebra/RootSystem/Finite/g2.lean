/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

/-!
# Properties of the `𝔤₂` root system.

The `𝔤₂` root pairing is special enough to deserve its own API. We provide one in this file.

As an application we prove the key result that a finite, crystallographic, reduced, irreducible root
pairing containing two roots of Coxeter weight three is spanned by this pair of roots (and thus
is two-dimensional). This result is usually proved only for pairs of roots belonging to a base (as a
corollary of the fact that no node can have degree greater than three) and moreover usually requires
stronger assumptions on the coefficients than here.

## Main results:
 * `RootPairing.EmbeddedG2`: a data-bearing typeclass which distinguishes a pair of roots whose
   pairing is `-3` (equivalently, with a distinguished choice of base). This is a sufficient
   condition for the span of this pair of roots to be a `𝔤₂` root system.
 * `RootPairing.EmbeddedG2.shortRoot`: the distinguished short root, which we often donate `α`
 * `RootPairing.EmbeddedG2.longRoot`: the distinguished long root, which we often donate `β`
 * `RootPairing.EmbeddedG2.shortAddLong`: the short root `α + β`
 * `RootPairing.EmbeddedG2.twoShortAddLong`: the short root `2α + β`
 * `RootPairing.EmbeddedG2.threeShortAddLong`: the long root `3α + β`
 * `RootPairing.EmbeddedG2.threeShortAddTwoLong`: the long root `3α + 2β`
 * `RootPairing.EmbeddedG2.span_eq_top`: a finite crystallographic reduced irreducible root pairing
   containing two roots with pairing `-3` is spanned by this pair (thus two-dimensional).
 * `RootPairing.EmbeddedG2.card_index_eq_twelve`: the `𝔤₂`root pairing has twelve roots.

-/

noncomputable section

open FaithfulSMul Function Set Submodule
open List hiding mem_toFinset

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

namespace RootPairing

/-- A data-bearing typeclass which distinguishes a pair of roots whose pairing is `-3`. This is a
sufficient condition for the span of this pair of roots to be a `𝔤₂` root system. -/
class EmbeddedG2 extends P.IsCrystallographic, P.IsReduced where
  /-- The distinguished long root of an embedded `𝔤₂` root pairing. -/
  long : ι
  /-- The distinguished short root of an embedded `𝔤₂` root pairing. -/
  short : ι
  pairingIn_long_short : P.pairingIn ℤ long short = - 3

namespace EmbeddedG2

/-- A pair of roots which pair to `+3` are also sufficient to distinguish an embedded `𝔤₂`. -/
@[simps] def ofPairingInThree [CharZero R] [P.IsCrystallographic] [P.IsReduced] (long short : ι)
    (h : P.pairingIn ℤ long short = 3) : P.EmbeddedG2 where
  long := P.reflection_perm long long
  short := short
  pairingIn_long_short := by simp [h]

variable [P.EmbeddedG2]

attribute [simp] pairingIn_long_short

@[simp]
lemma pairing_long_short : P.pairing (long P) (short P) = - 3 := by
  rw [← P.algebraMap_pairingIn ℤ, pairingIn_long_short]
  simp

/-- The index of the root `α + β` where `α` is the short root and `β` is the long root. -/
def shortAddLong : ι := P.reflection_perm (long P) (short P)

/-- The index of the root `2α + β` where `α` is the short root and `β` is the long root. -/
def twoShortAddLong : ι := P.reflection_perm (short P) <| P.reflection_perm (long P) (short P)

/-- The index of the root `3α + β` where `α` is the short root and `β` is the long root. -/
def threeShortAddLong : ι := P.reflection_perm (short P) (long P)

/-- The index of the root `3α + 2β` where `α` is the short root and `β` is the long root. -/
def threeShortAddTwoLong : ι := P.reflection_perm (long P) <| P.reflection_perm (short P) (long P)

/-- The short root `α`. -/
abbrev shortRoot := P.root (short P)

/-- The long root `β`. -/
abbrev longRoot := P.root (long P)

/-- The short root `α + β`. -/
abbrev shortAddLongRoot : M := P.root (shortAddLong P)

/-- The short root `2α + β`. -/
abbrev twoShortAddLongRoot : M := P.root (twoShortAddLong P)

/-- The short root `3α + β`. -/
abbrev threeShortAddLongRoot : M := P.root (threeShortAddLong P)

/-- The short root `3α + 2β`. -/
abbrev threeShortAddTwoLongRoot : M := P.root (threeShortAddTwoLong P)

/-- The list of all 12 roots belonging to the embedded `𝔤₂`. -/
abbrev allRoots : List M :=
  [ longRoot P, -longRoot P,
    shortRoot P, -shortRoot P,
    shortAddLongRoot P, -shortAddLongRoot P,
    twoShortAddLongRoot P, -twoShortAddLongRoot P,
    threeShortAddLongRoot P, -threeShortAddLongRoot P,
    threeShortAddTwoLongRoot P, -threeShortAddTwoLongRoot P ]

lemma allRoots_subset_range_root [DecidableEq M] :
    ↑(allRoots P).toFinset ⊆ range P.root := by
  intro x hx
  simp only [toFinset_cons, toFinset_nil, insert_empty_eq, Finset.coe_insert,
    Finset.coe_singleton, mem_insert_iff, mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

variable [Finite ι] [CharZero R] [IsDomain R] [NoZeroSMulDivisors R M]

@[simp]
lemma pairingIn_short_long :
    P.pairingIn ℤ (short P) (long P) = - 1 := by
  have := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed (long P) (short P)
  have := pairingIn_long_short (P := P)
  aesop

@[simp]
lemma pairing_short_long :
    P.pairing (short P) (long P) = - 1 := by
  rw [← P.algebraMap_pairingIn ℤ, pairingIn_short_long]
  simp

lemma shortAddLongRoot_eq :
    shortAddLongRoot P = shortRoot P + longRoot P := by
  simp [shortAddLongRoot, shortAddLong, reflection_apply_root]

lemma twoShortAddLongRoot_eq :
    twoShortAddLongRoot P = (2 : R) • shortRoot P + longRoot P := by
  simp [twoShortAddLongRoot, twoShortAddLong, reflection_apply_root]
  module

omit [Finite ι] [CharZero R] [IsDomain R] [NoZeroSMulDivisors R M] in
lemma threeShortAddLongRoot_eq :
    threeShortAddLongRoot P = (3 : R) • shortRoot P + longRoot P := by
  simp [threeShortAddLongRoot, threeShortAddLong, reflection_apply_root]
  module

lemma threeShortAddTwoLongRoot_eq :
    threeShortAddTwoLongRoot P = (3 : R) • shortRoot P + (2 : R) • longRoot P := by
  simp [threeShortAddTwoLongRoot, threeShortAddTwoLong, reflection_apply_root]
  module

lemma linearIndependent_short_long :
    LinearIndependent R ![shortRoot P, longRoot P] := by
  simp [P.linearIndependent_iff_coxeterWeightIn_ne_four ℤ, coxeterWeightIn]

/-- The coefficients of each root in the `𝔤₂` root pairing, relative to the base. -/
abbrev allCoeffs : List (Fin 2 → ℤ) :=
  [![0, 1], ![0, -1], ![1, 0], ![-1, 0], ![1, 1], ![-1, -1],
    ![2, 1], ![-2, -1], ![3, 1], ![-3, -1], ![3, 2], ![-3, -2]]

lemma allRoots_eq_map_allCoeffs :
    allRoots P = allCoeffs.map (Fintype.linearCombination ℤ ![shortRoot P, longRoot P]) := by
  simp [Fintype.linearCombination_apply, neg_add, -neg_add_rev, shortAddLongRoot_eq,
    twoShortAddLongRoot_eq, threeShortAddLongRoot_eq, threeShortAddTwoLongRoot_eq,
    ← Int.cast_smul_eq_zsmul R]

lemma allRoots_nodup : (allRoots P).Nodup := by
  have hli : Injective (Fintype.linearCombination ℤ ![shortRoot P, longRoot P]) := by
    rw [← Fintype.linearIndependent_iff_injective]
    exact (linearIndependent_short_long P).restrict_scalars' ℤ
  rw [allRoots_eq_map_allCoeffs, nodup_map_iff hli]
  decide

lemma mem_span_of_mem_allRoots {x : M} (hx : x ∈ allRoots P) :
    x ∈ span ℤ {longRoot P, shortRoot P} := by
  have : {longRoot P, shortRoot P} = range ![shortRoot P, longRoot P] := by simp
  simp_rw [this, Submodule.mem_span_range_iff_exists_fun, ← Fintype.linearCombination_apply]
  simp [allRoots_eq_map_allCoeffs] at hx
  tauto

section InvariantForm

variable {P}
variable (B : P.InvariantForm)

lemma long_eq_three_mul_short :
    B.form (longRoot P) (longRoot P) = 3 * B.form (shortRoot P) (shortRoot P) := by
  simpa using B.pairing_mul_eq_pairing_mul_swap (long P) (short P)

omit [Finite ι] [CharZero R] [IsDomain R] [NoZeroSMulDivisors R M]

/-- `α + β` is short. -/
@[simp] lemma shortAddLongRoot_shortRoot :
    B.form (shortAddLongRoot P) (shortAddLongRoot P) = B.form (shortRoot P) (shortRoot P) := by
  simp [shortAddLongRoot, shortAddLong]

/-- `2α + β` is short. -/
@[simp] lemma twoShortAddLongRoot_shortRoot :
    B.form (twoShortAddLongRoot P) (twoShortAddLongRoot P) =
      B.form (shortRoot P) (shortRoot P) := by
  simp [twoShortAddLongRoot, twoShortAddLong]

/-- `3α + β` is long. -/
@[simp] lemma threeShortAddLongRoot_longRoot :
    B.form (threeShortAddLongRoot P) (threeShortAddLongRoot P) =
      B.form (longRoot P) (longRoot P) := by
  simp [threeShortAddLongRoot, threeShortAddLong]

/-- `3α + 2β` is long. -/
@[simp] lemma threeShortAddTwoLongRoot_longRoot :
    B.form (threeShortAddTwoLongRoot P) (threeShortAddTwoLongRoot P) =
      B.form (longRoot P) (longRoot P) := by
  simp [threeShortAddTwoLongRoot, threeShortAddTwoLong]

end InvariantForm

section Pairing

variable (i : ι)

@[simp] lemma pairingIn_shortAddLong_left :
    P.pairingIn ℤ (shortAddLong P) i = P.pairingIn ℤ (short P) i + P.pairingIn ℤ (long P) i := by
  suffices P.pairing (shortAddLong P) i = P.pairing (short P) i + P.pairing (long P) i from
    algebraMap_injective ℤ R <| by simpa only [algebraMap_pairingIn, map_add]
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm ℤ).toInvariantForm
  apply mul_right_cancel₀ (B.ne_zero i)
  rw [← B.two_mul_apply_root_root]
  simp [shortAddLongRoot_eq, mul_add, add_mul, B.two_mul_apply_root_root]

@[simp] lemma pairingIn_shortAddLong_right :
    P.pairingIn ℤ i (shortAddLong P) =
      P.pairingIn ℤ i (short P) + 3 * P.pairingIn ℤ i (long P) := by
  suffices P.pairing i (shortAddLong P) = P.pairing i (short P) + 3 * P.pairing i (long P) from
    algebraMap_injective ℤ R <| by simpa only [algebraMap_pairingIn, map_add, map_mul, map_ofNat]
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm ℤ).toInvariantForm
  apply mul_right_cancel₀ (B.ne_zero (shortAddLong P))
  calc P.pairing i (shortAddLong P) * B.form (P.root (shortAddLong P)) (P.root (shortAddLong P))
    _ = 2 * B.form (P.root i) (shortAddLongRoot P) := ?_
    _ = 2 * B.form (P.root i) (shortRoot P) + 2 * B.form (P.root i) (longRoot P) := ?_
    _ = P.pairing i (short P) * B.form (shortRoot P) (shortRoot P) +
          P.pairing i (long P) * B.form (longRoot P) (longRoot P) := ?_
    _ = (P.pairing i (short P) + 3 * P.pairing i (long P)) *
          B.form (shortAddLongRoot P) (shortAddLongRoot P) := ?_
  · rw [B.two_mul_apply_root_root]
  · rw [shortAddLongRoot_eq, map_add, mul_add]
  · rw [B.two_mul_apply_root_root, B.two_mul_apply_root_root]
  · rw [long_eq_three_mul_short, shortAddLongRoot_shortRoot]; ring

@[simp] lemma pairingIn_twoShortAddLong_left :
    P.pairingIn ℤ (twoShortAddLong P) i =
      2 * P.pairingIn ℤ (short P) i + P.pairingIn ℤ (long P) i := by
  suffices P.pairing (twoShortAddLong P) i = 2 * P.pairing (short P) i + P.pairing (long P) i from
    algebraMap_injective ℤ R <| by simpa only [algebraMap_pairingIn, map_add, map_mul, map_ofNat]
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm ℤ).toInvariantForm
  apply mul_right_cancel₀ (B.ne_zero i)
  rw [← B.two_mul_apply_root_root]
  simp [twoShortAddLongRoot_eq, mul_add, add_mul, B.two_mul_apply_root_root]
  ring

@[simp] lemma pairingIn_twoShortAddLong_right :
    P.pairingIn ℤ i (twoShortAddLong P) =
      2 * P.pairingIn ℤ i (short P) + 3 * P.pairingIn ℤ i (long P) := by
  suffices P.pairing i (twoShortAddLong P) =
      2 * P.pairing i (short P) + 3 * P.pairing i (long P) from
    algebraMap_injective ℤ R <| by simpa only [algebraMap_pairingIn, map_add, map_mul, map_ofNat]
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm ℤ).toInvariantForm
  apply mul_right_cancel₀ (B.ne_zero <| twoShortAddLong P)
  calc P.pairing i (twoShortAddLong P) * B.form (twoShortAddLongRoot P) (twoShortAddLongRoot P)
    _ = 2 * B.form (P.root i) (twoShortAddLongRoot P) := ?_
    _ = 2 * (2 * B.form (P.root i) (shortRoot P)) + 2 * B.form (P.root i) (longRoot P) := ?_
    _ = 2 * P.pairing i (short P) * B.form (shortRoot P) (shortRoot P) +
          P.pairing i (long P) * B.form (longRoot P) (longRoot P) := ?_
    _ = (2 * P.pairing i (short P) +
          3 * P.pairing i (long P)) * B.form (twoShortAddLongRoot P) (twoShortAddLongRoot P) :=?_
  · rw [B.two_mul_apply_root_root]
  · rw [twoShortAddLongRoot_eq, map_add, mul_add, map_smul, smul_eq_mul]
  · rw [B.two_mul_apply_root_root, B.two_mul_apply_root_root, mul_assoc]
  · rw [long_eq_three_mul_short, twoShortAddLongRoot_shortRoot]; ring

omit [NoZeroSMulDivisors R M] in
@[simp] lemma pairingIn_threeShortAddLong_left :
    P.pairingIn ℤ (threeShortAddLong P) i =
      3 * P.pairingIn ℤ (short P) i + P.pairingIn ℤ (long P) i := by
  suffices P.pairing (threeShortAddLong P) i =
      3 * P.pairing (short P) i + P.pairing (long P) i from
    algebraMap_injective ℤ R <| by simpa only [algebraMap_pairingIn, map_add, map_mul, map_ofNat]
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm ℤ).toInvariantForm
  apply mul_right_cancel₀ (B.ne_zero i)
  rw [← B.two_mul_apply_root_root]
  simp [threeShortAddLongRoot_eq, mul_add, B.two_mul_apply_root_root, mul_left_comm (2 : R) (3 : R)]
  ring

@[simp] lemma pairingIn_threeShortAddLong_right :
    P.pairingIn ℤ i (threeShortAddLong P) =
      P.pairingIn ℤ i (short P) + P.pairingIn ℤ i (long P) := by
  suffices P.pairing i (threeShortAddLong P) =
      P.pairing i (short P) + P.pairing i (long P) from
    algebraMap_injective ℤ R <| by simpa only [algebraMap_pairingIn, map_add, map_mul, map_ofNat]
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm ℤ).toInvariantForm
  apply mul_right_cancel₀ (B.ne_zero <| threeShortAddLong P)
  calc P.pairing i (threeShortAddLong P) *
          B.form (threeShortAddLongRoot P) (threeShortAddLongRoot P)
    _ = 2 * B.form (P.root i) (threeShortAddLongRoot P) := ?_
    _ = 3 * (2 * B.form (P.root i) (shortRoot P)) + 2 * B.form (P.root i) (longRoot P) := ?_
    _ = P.pairing i (short P) * B.form (longRoot P) (longRoot P) +
          P.pairing i (long P) * B.form (longRoot P) (longRoot P) := ?_
    _ = (P.pairing i (short P) + P.pairing i (long P)) *
          B.form (threeShortAddLongRoot P) (threeShortAddLongRoot P) := ?_
  · rw [B.two_mul_apply_root_root]
  · rw [threeShortAddLongRoot_eq, map_add, mul_add, map_smul, smul_eq_mul]; ring
  · rw [B.two_mul_apply_root_root, B.two_mul_apply_root_root, long_eq_three_mul_short]; ring
  · rw [threeShortAddLongRoot_longRoot]; ring

@[simp] lemma pairingIn_threeShortAddTwoLong_left :
    P.pairingIn ℤ (threeShortAddTwoLong P) i =
      3 * P.pairingIn ℤ (short P) i + 2 * P.pairingIn ℤ (long P) i := by
  suffices P.pairing (threeShortAddTwoLong P) i =
      3 * P.pairing (short P) i + 2 * P.pairing (long P) i from
    algebraMap_injective ℤ R <| by simpa only [algebraMap_pairingIn, map_add, map_mul, map_ofNat]
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm ℤ).toInvariantForm
  apply mul_right_cancel₀ (B.ne_zero i)
  rw [← B.two_mul_apply_root_root]
  simp [threeShortAddTwoLongRoot_eq, mul_add, B.two_mul_apply_root_root, mul_left_comm _ (3 : R)]
  ring

@[simp] lemma pairingIn_threeShortAddTwoLong_right :
    P.pairingIn ℤ i (threeShortAddTwoLong P) =
      P.pairingIn ℤ i (short P) + 2 * P.pairingIn ℤ i (long P) := by
  suffices P.pairing i (threeShortAddTwoLong P) =
      P.pairing i (short P) + 2 * P.pairing i (long P) from
    algebraMap_injective ℤ R <| by simpa only [algebraMap_pairingIn, map_add, map_mul, map_ofNat]
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm ℤ).toInvariantForm
  apply mul_right_cancel₀ (B.ne_zero <| threeShortAddTwoLong P)
  calc P.pairing i (threeShortAddTwoLong P) *
          B.form (threeShortAddTwoLongRoot P) (threeShortAddTwoLongRoot P)
    _ = 2 * B.form (P.root i) (threeShortAddTwoLongRoot P) := ?_
    _ = 3 * (2 * B.form (P.root i) (shortRoot P)) + 2 * (2 * B.form (P.root i) (longRoot P)) := ?_
    _ = P.pairing i (short P) * B.form (longRoot P) (longRoot P) +
          2 * P.pairing i (long P) * B.form (longRoot P) (longRoot P) := ?_
    _ = (P.pairing i (short P) + 2 * P.pairing i (long P)) *
          B.form (threeShortAddTwoLongRoot P) (threeShortAddTwoLongRoot P) := ?_
  · rw [B.two_mul_apply_root_root]
  · simp only [threeShortAddTwoLongRoot_eq, map_add, mul_add, map_smul, smul_eq_mul]; ring
  · rw [B.two_mul_apply_root_root, B.two_mul_apply_root_root, long_eq_three_mul_short]; ring
  · rw [threeShortAddTwoLongRoot_longRoot]; ring

end Pairing

private lemma isOrthogonal_short_and_long_aux {a b c d e f a' b' c' d' e' f' : ℤ} {S : Set (ℤ × ℤ)}
    (S_def : S = {(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1), (-1, -2), (-2, -1), (1, 3), (3, 1),
      (-1, -3), (-3, -1)})
    (ha : (a, a') ∈ S)
    (hb : (b, b') ∈ S)
    (hc : (c, c') ∈ S)
    (hd : (d, d') ∈ S)
    (he : (e, e') ∈ S)
    (hf : (f, f') ∈ S)
    (h₁ : c = a + 3 * b)
    (h₂ : c' = a' + b')
    (h₃ : d = 2 * a + 3 * b)
    (h₄ : d' = 2 * a' + b')
    (h₅ : e = a + b)
    (h₆ : e' = 3 * a' + b')
    (h₇ : f = a + 2 * b)
    (h₈ : f' = 3 * a' + 2 * b') :
    a = 0 ∧ b = 0 := by
  simp [S_def] at ha hb hc hd he hf
  omega

lemma isOrthogonal_short_and_long {i : ι} (hi : P.root i ∉ allRoots P) :
    P.IsOrthogonal i (short P) ∧ P.IsOrthogonal i (long P) := by
  suffices P.pairingIn ℤ i (short P) = 0 ∧ P.pairingIn ℤ i (long P) = 0 by
    have : Fintype ι := Fintype.ofFinite ι
    have B := (P.posRootForm ℤ).toInvariantForm
    simpa [B.isOrthogonal_iff_pairing_eq_zero, ← P.algebraMap_pairingIn ℤ]
  simp only [mem_cons, not_mem_nil, or_false, not_or] at hi
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩ := hi
  have ha := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' i (short P) ‹_› ‹_›
  have hb := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' i (long P) ‹_› ‹_›
  have hc := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' i (shortAddLong P) ‹_› ‹_›
  have hd := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' i (twoShortAddLong P) ‹_› ‹_›
  have he := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' i (threeShortAddLong P) ‹_› ‹_›
  have hf := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' i (threeShortAddTwoLong P) ‹_› ‹_›
  apply isOrthogonal_short_and_long_aux rfl ha hb hc hd he hf <;> simp

section IsIrreducible

variable [P.IsIrreducible]

@[simp] lemma span_eq_top :
    span R {longRoot P, shortRoot P} = ⊤ := by
  have := P.span_root_image_eq_top_of_forall_orthogonal {long P, short P} (by simp)
  rw [show P.root '' {long P, short P} = {longRoot P, shortRoot P} from by aesop] at this
  refine this fun k hk ij hij ↦ ?_
  replace hk : P.root k ∉ allRoots P :=
    fun contra ↦ hk <| span_subset_span ℤ _ _ <| mem_span_of_mem_allRoots P contra
  have aux := isOrthogonal_short_and_long P hk
  rcases hij with rfl | rfl <;> tauto

lemma mem_allRoots (i : ι) :
    P.root i ∈ allRoots P := by
  by_contra hi
  obtain ⟨h₁, h₂⟩ := isOrthogonal_short_and_long P hi
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm ℤ).toInvariantForm
  rw [B.isOrthogonal_iff_pairing_eq_zero, ← B.apply_root_root_zero_iff] at h₁ h₂
  have key : B.form (P.root i) = 0 := by
    ext x
    have hx : x ∈ span R {longRoot P, shortRoot P} := by simp
    simp only [LinearMap.zero_apply]
    induction hx using Submodule.span_induction with
    | zero => simp
    | mem => aesop
    | add => aesop
    | smul => aesop
  simpa using LinearMap.congr_fun key (P.root i)

open scoped Classical in
/-- The natural labelling of `RootPairing.EmbeddedG2.allRoots`. -/
@[simps] def indexEquivAllRoots : ι ≃ (allRoots P).toFinset :=
  { toFun i := ⟨P.root i, List.mem_toFinset.mpr <| mem_allRoots P i⟩
    invFun x := (allRoots_subset_range_root P x.property).choose
    left_inv i := by simp
    right_inv := by
      rintro ⟨x, hx⟩
      simp only [Subtype.mk.injEq]
      exact (allRoots_subset_range_root P hx).choose_spec }

include P in
lemma card_index_eq_twelve :
    Nat.card ι = 12 := by
  classical
  have this : Nat.card (allRoots P).toFinset = 12 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, toFinset_card_of_nodup (allRoots_nodup P)]
    simp
  rw [← this]
  exact Nat.card_congr <| indexEquivAllRoots P

lemma setOf_index_eq_univ :
    letI _i := P.indexNeg
    { long P, -long P,
      short P, -short P,
      shortAddLong P, -shortAddLong P,
      twoShortAddLong P, -twoShortAddLong P,
      threeShortAddLong P, -threeShortAddLong P,
      threeShortAddTwoLong P, -threeShortAddTwoLong P } = univ :=
  eq_univ_iff_forall.mpr fun i ↦ by simpa using mem_allRoots P i

end IsIrreducible

end EmbeddedG2

end RootPairing
