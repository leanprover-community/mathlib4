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
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.ModCases
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

open BigOperators Fintype PiNotation

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

theorem commProb_pi (i : α → Type _) [Fintype α] [Π a, Group (i a)] :
    commProb (Π a, i a) = ∏ a, commProb (i a) := by
  simp_rw [commProb_def, Finset.prod_div_distrib, Finset.prod_pow, ←Nat.cast_prod,
    ←Nat.card_pi, Function.funext_iff]
  congr 2
  exact Nat.card_congr ⟨fun x a => ⟨⟨x.1.1 a, x.1.2 a⟩, x.2 a⟩, fun x => ⟨⟨fun a => (x a).1.1,
    fun a => (x a).1.2⟩, fun a => (x a).2⟩, fun x => rfl, fun x => rfl⟩

theorem commProb_eq_zero_of_infinite [Infinite M] : commProb M = 0 :=
  div_eq_zero_iff.2 (Or.inr (sq_eq_zero_iff.2 (Nat.cast_eq_zero.2 Nat.card_eq_zero_of_infinite)))

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

variable (G : Type _) [Group G]

instance [Infinite G] : Infinite { p : G × G // p.1 * p.2 = p.2 * p.1 } :=
  Infinite.of_injective (fun g => ⟨⟨g, g⟩, rfl⟩) (fun _ _ => by simp only [Subtype.mk.injEq, Prod.mk.injEq,
    and_self, imp_self])

theorem card_comm_eq_card_conjClasses_mul_card :
    Nat.card { p : G × G // p.1 * p.2 = p.2 * p.1 } = Nat.card (ConjClasses G) * Nat.card G := by
  rcases fintypeOrInfinite G
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
  rw [Nat.card_eq_zero_of_infinite, @Nat.card_eq_zero_of_infinite G, mul_zero]
#align card_comm_eq_card_conj_classes_mul_card card_comm_eq_card_conjClasses_mul_card

theorem commProb_def' : commProb G = Nat.card (ConjClasses G) / Nat.card G := by
  rw [commProb, card_comm_eq_card_conjClasses_mul_card, Nat.cast_mul, sq]
  by_cases (Nat.card G : ℚ) = 0
  . rw [h, zero_mul, div_zero, div_zero]
  . exact mul_div_mul_right _ _ h
#align comm_prob_def' commProb_def'

-- porting note: inserted [Group G]
variable {G} [Group G] [Finite G] (H : Subgroup G)

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

lemma aux2 : {n : ℕ} → (h0 : n ≠ 0) → (h1 : n ≠ 1) → n / 4 + 1 < n
| 0 => by decide
| 1 => by decide
| 2 => by decide
| 3 => by decide
| n + 4 => by intros; rw [n.add_div_right four_pos, Nat.succ_lt_succ_iff, Nat.succ_lt_succ_iff,
  Nat.lt_succ_iff]; exact (n.div_le_self 4).trans n.le_succ

namespace CommutingProbability

def reciprocalFactors (n : ℕ) : List ℕ :=
  if h0 : n = 0 then [0]
  else if h1 : n = 1 then []
  else if 2 ∣ n then
    have := aux1 h0
    3 :: reciprocalFactors (n / 2)
  else
    have := aux2 h0 h1
    n % 4 * n :: reciprocalFactors (n / 4 + 1)

def ReciprocalGroup (l : List ℕ) : Type :=
  Π i : Fin l.length, DihedralGroup (l[i])

instance (l : List ℕ) : Group (ReciprocalGroup l) := Pi.group

lemma commProb_ReciprocalGroup (l : List ℕ) :
    commProb (ReciprocalGroup l) = (l.map (fun k => commProb (DihedralGroup k))).prod := by
  unfold ReciprocalGroup
  rw [commProb_pi]
  induction' l with n l h
  . rfl
  . simp_rw [List.length_cons, Fin.prod_univ_succ, List.map_cons, List.prod_cons, ←h]
    rfl

lemma card_conjClasses_dihedralGroup_odd (n : ℕ) (hn : ¬ 2 ∣ n) :
    Nat.card (ConjClasses (DihedralGroup n)) = (n + 3) / 2 :=
sorry

-- todo: compute conjugacy classes of dihedral group by counting commuting pairs
lemma commProb_DihedralGroup_Odd (n : ℕ) (hn : ¬ 2 ∣ n) :
    commProb (DihedralGroup n) = (n + 3) / (4 * n) := by
  have hn' : n ≠ 0 := fun h => hn (h ▸ Nat.dvd_zero 2)
  have : NeZero n := ⟨hn'⟩
  rw [commProb_def', card_conjClasses_dihedralGroup_odd n hn,
      Nat.card_eq_fintype_card, DihedralGroup.card]
  have : ((n + 3) / 2 : ℕ) = ((n + 3 : ℕ) : ℚ) / (2 : ℕ) := by
    rw [Nat.cast_div]
    rw [Nat.two_dvd_ne_zero] at hn
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hn]
    norm_num
    norm_num
  rw [this]
  field_simp [hn']
  left
  ring

namespace DihedralGroup

def fintypeHelper {n : ℕ} : Sum (ZMod n) (ZMod n) ≃ DihedralGroup n where
  invFun i := match i with
    | DihedralGroup.r j => Sum.inl j
    | DihedralGroup.sr j => Sum.inr j
  toFun i := match i with
    | Sum.inl j => DihedralGroup.r j
    | Sum.inr j => DihedralGroup.sr j
  left_inv := by rintro (x | x) <;> rfl
  right_inv := by rintro (x | x) <;> rfl

instance : Infinite (DihedralGroup 0) := by
  rw [←DihedralGroup.fintypeHelper.infinite_iff]
  infer_instance

end DihedralGroup

theorem key0 (n : ℕ) (h2 : ¬ 2 ∣ n) : n % 4 = 1 ∨ n % 4 = 3 :=
Nat.odd_mod_four_iff.mp (Nat.two_dvd_ne_zero.mp h2)

theorem key1 (n : ℕ) (h2 : ¬ 2 ∣ n) : (n % 4) ^ 2 + 3 = n % 4 * 4 := by
  rcases (key0 n h2) with h | h <;> rw [h] <;> norm_num

theorem commProb_ReciprocalGroup_reciprocalFactors (n : ℕ) :
    commProb (ReciprocalGroup (reciprocalFactors n)) = 1 / n := by
  rw [commProb_ReciprocalGroup]
  unfold reciprocalFactors
  by_cases h0 : n = 0
  . rw [dif_pos h0, List.map_singleton, List.prod_singleton, h0, Nat.cast_zero, div_zero]
    apply commProb_eq_zero_of_infinite
  . by_cases h1 : n = 1
    . rw [dif_neg h0, dif_pos h1, List.map_nil, List.prod_nil, h1, Nat.cast_one, div_one]
    . by_cases h2 : 2 ∣  n
      . have := aux1 h0
        rw [dif_neg h0, dif_neg h1, if_pos h2, List.map_cons, List.prod_cons,
            ←commProb_ReciprocalGroup, commProb_ReciprocalGroup_reciprocalFactors (n / 2),
            commProb_DihedralGroup_Odd 3 (by norm_num)]
        field_simp [h0]
        norm_num
      . have := aux2 h0 h1
        rw [dif_neg h0, dif_neg h1, if_neg h2, List.map_cons, List.prod_cons,
            ←commProb_ReciprocalGroup, commProb_ReciprocalGroup_reciprocalFactors (n / 4 + 1),
            commProb_DihedralGroup_Odd (n % 4 * n)]
        rw [div_mul_div_comm, mul_one, div_eq_div_iff]
        . norm_cast
          have key : (n % 4) ^ 2 + 3 = n % 4 * 4 := key1 n h2
          calc ((n % 4) * n + 3) * n = ((n % 4) * (4 * (n / 4) + n % 4) + 3) * n := by rw [Nat.div_add_mod]
            _ = ((n % 4) ^ 2 + 3 + (n % 4) * 4 * (n / 4)) * n := by ring
            _ = (n % 4 * 4 + (n % 4) * 4 * (n / 4)) * n := by rw [key]
            _ = 1 * (4 * (n % 4 * n) * (n / 4 + 1)) := by ring
        . norm_cast
          have h4 : n % 4 ≠ 0 := by
            contrapose! h2
            rw [←Nat.dvd_iff_mod_eq_zero] at h2
            exact dvd_trans (by norm_num) h2
          positivity
        . norm_cast
        . apply Nat.prime_two.not_dvd_mul _ h2
          rcases (key0 n h2) with h | h <;> rw [h] <;> norm_num

end CommutingProbability
