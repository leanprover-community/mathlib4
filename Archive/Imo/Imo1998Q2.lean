/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Finite.Prod
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

/-!
# IMO 1998 Q2
In a competition, there are `a` contestants and `b` judges, where `b ≥ 3` is an odd integer. Each
judge rates each contestant as either "pass" or "fail". Suppose `k` is a number such that, for any
two judges, their ratings coincide for at most `k` contestants. Prove that `k / a ≥ (b - 1) / (2b)`.

## Solution
The problem asks us to think about triples consisting of a contestant and two judges whose ratings
agree for that contestant. We thus consider the subset `A ⊆ C × JJ` of all such incidences of
agreement, where `C` and `J` are the sets of contestants and judges, and `JJ = J × J - {(j, j)}`. We
have natural maps: `left : A → C` and `right: A → JJ`. We count the elements of `A` in two ways: as
the sum of the cardinalities of the fibres of `left` and as the sum of the cardinalities of the
fibres of `right`. We obtain an upper bound on the cardinality of `A` from the count for `right`,
and a lower bound from the count for `left`. These two bounds combine to the required result.

First consider the map `right : A → JJ`. Since the size of any fibre over a point in JJ is bounded
by `k` and since `|JJ| = b^2 - b`, we obtain the upper bound: `|A| ≤ k(b^2-b)`.

Now consider the map `left : A → C`. The fibre over a given contestant `c ∈ C` is the set of
ordered pairs of (distinct) judges who agree about `c`. We seek to bound the cardinality of this
fibre from below. Minimum agreement for a contestant occurs when the judges' ratings are split as
evenly as possible. Since `b` is odd, this occurs when they are divided into groups of size
`(b-1)/2` and `(b+1)/2`. This corresponds to a fibre of cardinality `(b-1)^2/2` and so we obtain
the lower bound: `a(b-1)^2/2 ≤ |A|`.

Rearranging gives the result.
-/

variable {C J : Type*} (r : C → J → Prop)

namespace Imo1998Q2

noncomputable section

/-- An ordered pair of judges. -/
abbrev JudgePair (J : Type*) :=
  J × J

/-- A triple consisting of contestant together with an ordered pair of judges. -/
abbrev AgreedTriple (C J : Type*) :=
  C × JudgePair J

/-- The first judge from an ordered pair of judges. -/
abbrev JudgePair.judge₁ : JudgePair J → J :=
  Prod.fst

/-- The second judge from an ordered pair of judges. -/
abbrev JudgePair.judge₂ : JudgePair J → J :=
  Prod.snd

/-- The proposition that the judges in an ordered pair are distinct. -/
abbrev JudgePair.Distinct (p : JudgePair J) :=
  p.judge₁ ≠ p.judge₂

/-- The proposition that the judges in an ordered pair agree about a contestant's rating. -/
abbrev JudgePair.Agree (p : JudgePair J) (c : C) :=
  r c p.judge₁ ↔ r c p.judge₂

/-- The contestant from the triple consisting of a contestant and an ordered pair of judges. -/
abbrev AgreedTriple.contestant : AgreedTriple C J → C :=
  Prod.fst

/-- The ordered pair of judges from the triple consisting of a contestant and an ordered pair of
judges. -/
abbrev AgreedTriple.judgePair : AgreedTriple C J → JudgePair J :=
  Prod.snd

@[simp]
theorem JudgePair.agree_iff_same_rating (p : JudgePair J) (c : C) :
    p.Agree r c ↔ (r c p.judge₁ ↔ r c p.judge₂) :=
  Iff.rfl

open scoped Classical in
/-- The set of contestants on which two judges agree. -/
def agreedContestants [Fintype C] (p : JudgePair J) : Finset C :=
  Finset.univ.filter fun c => p.Agree r c
section

variable [Fintype J] [Fintype C]

open scoped Classical in
/-- All incidences of agreement. -/
def A : Finset (AgreedTriple C J) :=
  Finset.univ.filter @fun (a : AgreedTriple C J) =>
    (a.judgePair.Agree r a.contestant ∧ a.judgePair.Distinct)

open scoped Classical in
theorem A_maps_to_offDiag_judgePair (a : AgreedTriple C J) :
    a ∈ A r → a.judgePair ∈ Finset.offDiag (@Finset.univ J _) := by simp [A, Finset.mem_offDiag]

open scoped Classical in
theorem A_fibre_over_contestant (c : C) :
    (Finset.univ.filter fun p : JudgePair J => p.Agree r c ∧ p.Distinct) =
      ((A r).filter fun a : AgreedTriple C J => a.contestant = c).image Prod.snd := by
  ext p
  simp [A]

open scoped Classical in
theorem A_fibre_over_contestant_card (c : C) :
    (Finset.univ.filter fun p : JudgePair J => p.Agree r c ∧ p.Distinct).card =
      ((A r).filter fun a : AgreedTriple C J => a.contestant = c).card := by
  rw [A_fibre_over_contestant r]
  apply Finset.card_image_of_injOn
  unfold Set.InjOn
  rintro ⟨a, p⟩ h ⟨a', p'⟩ h' rfl
  aesop (add simp AgreedTriple.contestant)

open scoped Classical in
theorem A_fibre_over_judgePair {p : JudgePair J} (h : p.Distinct) :
    agreedContestants r p = ((A r).filter fun a : AgreedTriple C J => a.judgePair = p).image
    AgreedTriple.contestant := by
  dsimp only [A, agreedContestants]; ext c; constructor <;> intro h
  · rw [Finset.mem_image]; refine ⟨⟨c, p⟩, ?_⟩; aesop
  · aesop

open scoped Classical in
theorem A_fibre_over_judgePair_card {p : JudgePair J} (h : p.Distinct) :
    (agreedContestants r p).card =
      ((A r).filter fun a : AgreedTriple C J => a.judgePair = p).card := by
  rw [A_fibre_over_judgePair r h]
  apply Finset.card_image_of_injOn
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10936): used to be `tidy`
  unfold Set.InjOn; intros; ext; all_goals aesop

theorem A_card_upper_bound {k : ℕ}
    (hk : ∀ p : JudgePair J, p.Distinct → (agreedContestants r p).card ≤ k) :
    (A r).card ≤ k * (Fintype.card J * Fintype.card J - Fintype.card J) := by
  change _ ≤ k * (Finset.card _ * Finset.card _ - Finset.card _)
  classical
  rw [← Finset.offDiag_card]
  apply Finset.card_le_mul_card_image_of_maps_to (A_maps_to_offDiag_judgePair r)
  intro p hp
  have hp' : p.Distinct := by grind
  rw [← A_fibre_over_judgePair_card r hp']; apply hk; exact hp'

end

theorem add_sq_add_sq_sub {α : Type*} [Ring α] (x y : α) :
    (x + y) * (x + y) + (x - y) * (x - y) = 2 * x * x + 2 * y * y := by noncomm_ring

theorem norm_bound_of_odd_sum {x y z : ℤ} (h : x + y = 2 * z + 1) :
    2 * z * z + 2 * z + 1 ≤ x * x + y * y := by
  suffices 4 * z * z + 4 * z + 1 + 1 ≤ 2 * x * x + 2 * y * y by
    rw [← mul_le_mul_left (zero_lt_two' ℤ)]; ring_nf at this ⊢; exact this
  have h' : (x + y) * (x + y) = 4 * z * z + 4 * z + 1 := by rw [h]; ring
  rw [← add_sq_add_sq_sub, h', add_le_add_iff_left]
  suffices 0 < (x - y) * (x - y) by apply Int.add_one_le_of_lt this
  rw [mul_self_pos, sub_ne_zero]; apply Int.ne_of_odd_add ⟨z, h⟩

section

variable [Fintype J]

open scoped Classical in
theorem judge_pairs_card_lower_bound {z : ℕ} (hJ : Fintype.card J = 2 * z + 1) (c : C) :
    2 * z * z + 2 * z + 1 ≤ (Finset.univ.filter fun p : JudgePair J => p.Agree r c).card := by
  let x := (Finset.univ.filter fun j => r c j).card
  let y := (Finset.univ.filter fun j => ¬r c j).card
  have h : (Finset.univ.filter fun p : JudgePair J => p.Agree r c).card = x * x + y * y := by
    simp [x, y, ← Finset.filter_product_card]
  rw [h]; apply Int.le_of_ofNat_le_ofNat; simp only [Int.natCast_add, Int.natCast_mul]
  apply norm_bound_of_odd_sum
  suffices x + y = 2 * z + 1 by simp [← Int.natCast_add, this]
  rw [Finset.filter_card_add_filter_neg_card_eq_card, ← hJ, Finset.card_univ]

open scoped Classical in
theorem distinct_judge_pairs_card_lower_bound {z : ℕ} (hJ : Fintype.card J = 2 * z + 1) (c : C) :
    2 * z * z ≤ (Finset.univ.filter fun p : JudgePair J => p.Agree r c ∧ p.Distinct).card := by
  let s := Finset.univ.filter fun p : JudgePair J => p.Agree r c
  let t := Finset.univ.filter fun p : JudgePair J => p.Distinct
  have hs : 2 * z * z + 2 * z + 1 ≤ s.card := judge_pairs_card_lower_bound r hJ c
  have hst : s \ t = Finset.univ.diag := by
    ext p; constructor <;> intros hp
    · unfold s t at hp
      aesop
    · unfold s t
      suffices p.judge₁ = p.judge₂ by simp [this]
      aesop
  have hst' : (s \ t).card = 2 * z + 1 := by rw [hst, Finset.diag_card, ← hJ, Finset.card_univ]
  rw [Finset.filter_and, ← Finset.sdiff_sdiff_self_left s t, Finset.card_sdiff]
  · rw [hst']; rw [add_assoc] at hs; apply le_tsub_of_add_le_right hs
  · apply Finset.sdiff_subset

theorem A_card_lower_bound [Fintype C] {z : ℕ} (hJ : Fintype.card J = 2 * z + 1) :
    2 * z * z * Fintype.card C ≤ (A r).card := by
  classical
  have h : ∀ a, a ∈ A r → Prod.fst a ∈ @Finset.univ C _ := by intros; apply Finset.mem_univ
  apply Finset.mul_card_image_le_card_of_maps_to h
  intro c _
  rw [← A_fibre_over_contestant_card]
  apply distinct_judge_pairs_card_lower_bound r hJ

end

theorem clear_denominators {a b k : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (b - 1 : ℚ) / (2 * b) ≤ k / a ↔ ((b : ℕ) - 1) * a ≤ k * (2 * b) := by
  rw [div_le_div_iff₀]
  on_goal 1 => convert Nat.cast_le (α := ℚ)
  all_goals simp [ha, hb]

end

end Imo1998Q2

open Imo1998Q2

theorem imo1998_q2 [Fintype J] [Fintype C] (a b k : ℕ) (hC : Fintype.card C = a)
    (hJ : Fintype.card J = b) (ha : 0 < a) (hb : Odd b)
    (hk : ∀ p : JudgePair J, p.Distinct → (agreedContestants r p).card ≤ k) :
    (b - 1 : ℚ) / (2 * b) ≤ k / a := by
  rw [clear_denominators ha hb.pos]
  obtain ⟨z, hz⟩ := hb; rw [hz] at hJ; rw [hz]
  have h := le_trans (A_card_lower_bound r hJ) (A_card_upper_bound r hk)
  rw [hC, hJ] at h
  -- We are now essentially done; we just need to bash `h` into exactly the right shape.
  have hl : k * ((2 * z + 1) * (2 * z + 1) - (2 * z + 1)) = k * (2 * (2 * z + 1)) * z := by
    have : 0 < 2 * z + 1 := by aesop
    simp only [mul_comm, add_mul, one_mul, add_tsub_cancel_right]; ring
  have hr : 2 * z * z * a = 2 * z * a * z := by ring
  rw [hl, hr] at h
  rcases z with - | z
  · simp
  · exact le_of_mul_le_mul_right h z.succ_pos
