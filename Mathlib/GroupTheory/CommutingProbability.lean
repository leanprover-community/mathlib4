/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning

! This file was ported from Lean 3 source module group_theory.commuting_probability
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.GroupTheory.Abelianization
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Util.PiNotation

/-!
# Commuting Probability
This file introduces the commuting probability of finite groups.

## Main definitions
* `commProb`: The commuting probability of a finite type with a multiplication operation.

## Todo
* Neumann's theorem.
-/
noncomputable section

open Classical

open BigOperators

open Fintype

variable (M : Type _) [Mul M]

/-- The commuting probability of a finite type with a multiplication operation. -/
def commProb : ℚ :=
  Nat.card { p : M × M // p.1 * p.2 = p.2 * p.1 } / (Nat.card M : ℚ) ^ 2
#align comm_prob commProb

theorem commProb_def :
    commProb M = Nat.card { p : M × M // p.1 * p.2 = p.2 * p.1 } / (Nat.card M : ℚ) ^ 2 :=
  rfl
#align comm_prob_def commProb_def

theorem commProb_prod (M' : Type _) [Mul M'] : commProb (M × M') = commProb M * commProb M' := by
  simp_rw [commProb_def, div_mul_div_comm, Nat.card_prod, Nat.cast_mul, mul_pow, ←Nat.cast_mul,
    ←Nat.card_prod, Prod.ext_iff]
  congr 2
  exact Nat.card_congr ⟨fun x => ⟨⟨⟨x.1.1.1, x.1.2.1⟩, x.2.1⟩, ⟨⟨x.1.1.2, x.1.2.2⟩, x.2.2⟩⟩,
    fun x => ⟨⟨⟨x.1.1.1, x.2.1.1⟩, ⟨x.1.1.2, x.2.1.2⟩⟩, ⟨x.1.2, x.2.2⟩⟩, fun x => rfl, fun x => rfl⟩

open PiNotation

theorem commProb_pi (i : α → Type _) [Fintype α] [Π a, Group (i a)] :
    commProb (Π a, i a) = ∏ a, commProb (i a) := by
  simp_rw [commProb_def, Finset.prod_div_distrib, Finset.prod_pow, ←Nat.cast_prod,
    ←Nat.card_pi, Function.funext_iff]
  congr 2
  exact Nat.card_congr ⟨fun x a => ⟨⟨x.1.1 a, x.1.2 a⟩, x.2 a⟩, fun x => ⟨⟨fun a => (x a).1.1,
    fun a => (x a).1.2⟩, fun a => (x a).2⟩, fun x => rfl, fun x => rfl⟩

variable [Finite M]

theorem commProb_pos [h : Nonempty M] : 0 < commProb M :=
  h.elim fun x ↦
    div_pos (Nat.cast_pos.mpr (Finite.card_pos_iff.mpr ⟨⟨(x, x), rfl⟩⟩))
      (pow_pos (Nat.cast_pos.mpr Finite.card_pos) 2)
#align comm_prob_pos commProb_pos

theorem commProb_le_one : commProb M ≤ 1 := by
  refine' div_le_one_of_le _ (sq_nonneg (Nat.card M : ℚ))
  rw [← Nat.cast_pow, Nat.cast_le, sq, ← Nat.card_prod]
  apply Finite.card_subtype_le
#align comm_prob_le_one commProb_le_one

variable {M}

theorem commProb_eq_one_iff [h : Nonempty M] :
    commProb M = 1 ↔ Commutative ((· * ·) : M → M → M) := by
  haveI := Fintype.ofFinite M
  rw [commProb, ← Set.coe_setOf, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [div_eq_one_iff_eq, ← Nat.cast_pow, Nat.cast_inj, sq, ← card_prod,
    set_fintype_card_eq_univ_iff, Set.eq_univ_iff_forall]
  · exact ⟨fun h x y ↦ h (x, y), fun h x ↦ h x.1 x.2⟩
  · exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr card_ne_zero)
#align comm_prob_eq_one_iff commProb_eq_one_iff

variable (G : Type _) [Group G] [Finite G]

theorem card_comm_eq_card_conjClasses_mul_card :
    Nat.card { p : G × G // p.1 * p.2 = p.2 * p.1 } = Nat.card (ConjClasses G) * Nat.card G := by
  haveI := Fintype.ofFinite G
  simp only [Nat.card_eq_fintype_card]
  -- Porting note: Changed `calc` proof into a `rw` proof.
  rw [card_congr (Equiv.subtypeProdEquivSigmaSubtype fun g h : G ↦ g * h = h * g), card_sigma,
    sum_equiv ConjAct.toConjAct.toEquiv (fun a ↦ card { b // a * b = b * a })
      (fun g ↦ card (MulAction.fixedBy (ConjAct G) G g))
      fun g ↦ card_congr' <| congr_arg _ <| funext fun h ↦ mul_inv_eq_iff_eq_mul.symm.to_eq,
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group, ConjAct.card,
    (Setoid.ext fun g h ↦ (Setoid.comm' _).trans isConj_iff.symm :
      MulAction.orbitRel (ConjAct G) G = IsConj.setoid G),
    @card_congr' (Quotient (IsConj.setoid G)) (ConjClasses G) _ _ rfl]
#align card_comm_eq_card_conj_classes_mul_card card_comm_eq_card_conjClasses_mul_card

theorem commProb_def' : commProb G = Nat.card (ConjClasses G) / Nat.card G := by
  rw [commProb, card_comm_eq_card_conjClasses_mul_card, Nat.cast_mul, sq]
  exact mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr Finite.card_pos.ne')
#align comm_prob_def' commProb_def'

-- porting note: inserted [Group G]
variable {G} [Group G] (H : Subgroup G)

theorem Subgroup.commProb_subgroup_le : commProb H ≤ commProb G * (H.index : ℚ) ^ 2 := by
  /- After rewriting with `commProb_def`, we reduce to showing that `G` has at least as many
      commuting pairs as `H`. -/
  rw [commProb_def, commProb_def, div_le_iff, mul_assoc, ← mul_pow, ← Nat.cast_mul,
    mul_comm H.index, H.card_mul_index, div_mul_cancel, Nat.cast_le]
  · refine' Finite.card_le_of_injective (fun p ↦ ⟨⟨p.1.1, p.1.2⟩, Subtype.ext_iff.mp p.2⟩) _
    exact fun p q h ↦ by simpa only [Subtype.ext_iff, Prod.ext_iff] using h
  · exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr Finite.card_pos.ne')
  · exact pow_pos (Nat.cast_pos.mpr Finite.card_pos) 2
#align subgroup.comm_prob_subgroup_le Subgroup.commProb_subgroup_le

theorem Subgroup.commProb_quotient_le [H.Normal] : commProb (G ⧸ H) ≤ commProb G * Nat.card H := by
  /- After rewriting with `commProb_def'`, we reduce to showing that `G` has at least as many
      conjugacy classes as `G ⧸ H`. -/
  rw [commProb_def', commProb_def', div_le_iff, mul_assoc, ← Nat.cast_mul, ← Subgroup.index,
    H.card_mul_index, div_mul_cancel, Nat.cast_le]
  · apply Finite.card_le_of_surjective
    show Function.Surjective (ConjClasses.map (QuotientGroup.mk' H))
    exact ConjClasses.map_surjective Quotient.surjective_Quotient_mk''
  · exact Nat.cast_ne_zero.mpr Finite.card_pos.ne'
  · exact Nat.cast_pos.mpr Finite.card_pos
#align subgroup.comm_prob_quotient_le Subgroup.commProb_quotient_le

variable (G)

theorem inv_card_commutator_le_commProb : (↑(Nat.card (commutator G)))⁻¹ ≤ commProb G :=
  (inv_pos_le_iff_one_le_mul (Nat.cast_pos.mpr Finite.card_pos)).mpr
    (le_trans (ge_of_eq (commProb_eq_one_iff.mpr (Abelianization.commGroup G).mul_comm))
      (commutator G).commProb_quotient_le)
#align inv_card_commutator_le_comm_prob inv_card_commutator_le_commProb

lemma aux1 {n : ℕ} (h0 : n ≠ 0) : n / 2 < n :=
  Nat.div_lt_self (Nat.pos_of_ne_zero h0) (lt_add_one 1)

lemma aux2 {n : ℕ} (h0 : n ≠ 0) (h1 : n ≠ 1) : n / 4 + 1 < n := by
  rw [←lt_tsub_iff_right, Nat.div_lt_iff_lt_mul four_pos, tsub_mul, one_mul,
      lt_tsub_iff_right]
  calc
    n + 4 < n * 1 + 2 * 3 := by rw [mul_one, add_lt_add_iff_left]; norm_num
    _ ≤ n * 1 + n * 3 :=
      add_le_add_left (mul_le_mul_right' ((Nat.two_le_iff n).mpr ⟨h0, h1⟩) 3) (n * 1)
    _ = n * 4 := by rw [←mul_add]

namespace CommutingProbability1

def reciprocalFactors (n : ℕ) : List ℕ :=
  if h0 : n = 0 then [0]
  else if h1 : n = 1 then []
  else if 2 ∣ n then
    have := aux1 h0
    3 :: reciprocalFactors (n / 2)
  else
    have := aux2 h0 h1
    n % 4 * n :: reciprocalFactors (n / 4 + 1)

def ReciprocalGroup (n : ℕ) : Type :=
  Π i : Fin (reciprocalFactors n).length, DihedralGroup ((reciprocalFactors n)[i])

instance (n : ℕ) : Group (ReciprocalGroup n) := by
  simp_rw [ReciprocalGroup]
  infer_instance

lemma reciprocalFactorsZero : reciprocalFactors 0 = [0] := rfl

lemma reciprocalFactorsOne : reciprocalFactors 1 = [] := rfl

lemma reciprocalFactorsEven (h0 : n ≠ 0) (h2 : 2 ∣ n) :
    reciprocalFactors n = 3 :: reciprocalFactors (n / 2) := by
  conv_lhs => unfold reciprocalFactors
  rw [dif_neg, dif_neg, if_pos h2]
  sorry

lemma reciprocalFactorsOdd (h0 : n ≠ 0) (h1 : n ≠ 1) (h2 : ¬ 2 ∣ n) :
    reciprocalFactors n = n % 4 * 4 :: reciprocalFactors (n / 4 + 1) := by
  sorry

theorem commProb_ReciprocalGroup (n : ℕ) : commProb (ReciprocalGroup n) = 1 / n := by
  unfold ReciprocalGroup
  rw [commProb_pi]
  have key : reciprocalFactors n = reciprocalFactors n := rfl
  conv_rhs at key => unfold reciprocalFactors


  refine' n.strong_induction_on _
  intro k h
  rcases eq_or_ne k 0 with rfl | h0
  . simp_rw [reciprocalFactorsZero, Nat.cast_zero, div_zero, List.length_singleton,
      Fin.prod_univ_one]
    change commProb (DihedralGroup 0) = 0
    sorry
  rcases eq_or_ne k 1 with rfl | h1
  . simp_rw [reciprocalFactorsOne, Nat.cast_one, div_one]
  by_cases h2 : 2 ∣ k
  . simp_rw [reciprocalFactorsEven h0 h2]
    sorry
  . sorry

end CommutingProbability1

namespace CommutingProbability

def ReciprocalGroup (n : ℕ) : Type :=
  if h0 : n = 0 then DihedralGroup 0
  else if h1 : n = 1 then DihedralGroup 1
  else if h2 : 2 ∣ n then
    have := aux1 h0
    DihedralGroup 3 × ReciprocalGroup (n / 2)
  else
    have := aux2 h0 h1
    DihedralGroup (n % 4 * n) × ReciprocalGroup (n / 4 + 1)

instance foo (n : ℕ) : Group (ReciprocalGroup n) := by
  unfold ReciprocalGroup
  by_cases h0 : n = 0
  . rw [dif_pos h0]
    infer_instance
  . rw [dif_neg h0]
    by_cases h1 : n = 1
    . rw [dif_pos h1]
      infer_instance
    . rw [dif_neg h1]
      by_cases h2 : 2 ∣ n
      . rw [dif_pos h2]
        have := aux1 h0
        have := foo (n / 2)
        infer_instance
      . rw [dif_neg h2]
        have := aux2 h0 h1
        have := foo (n / 4 + 1)
        infer_instance

theorem commProb_ReciprocalGroup (n : ℕ) : commProb (ReciprocalGroup n) = 1 / n := by
  unfold ReciprocalGroup

theorem commProb_ReciprocalGroup (n : ℕ) : commProb (ReciprocalGroup n) = 1 / n := by
  simp_rw [ReciprocalGroup, commProb_pi]
  refine' n.strong_induction_on _
  intro k h
  rcases eq_or_ne k 0 with rfl | h0
  . simp_rw [reciprocalFactorsZero, Nat.cast_zero, div_zero, List.length_singleton,
      Fin.prod_univ_one]
    change commProb (DihedralGroup 0) = 0
    sorry
  rcases eq_or_ne k 1 with rfl | h1
  . simp_rw [reciprocalFactorsOne, Nat.cast_one, div_one]
  by_cases h2 : 2 ∣ k
  . simp_rw [reciprocalFactorsEven h0 h2]
    sorry
  . sorry

#eval reciprocalFactors 15

end CommutingProbability
