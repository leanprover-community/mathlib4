/-
Copyright (c) 2023 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.GroupTheory.PGroup

/-!
# Zagier's "one-sentence proof" of Fermat's theorem on sums of two squares

"The involution on the finite set `S = {(x, y, z) : ℕ × ℕ × ℕ | x ^ 2 + 4 * y * z = p}` defined by
```
(x, y, z) ↦ (x + 2 * z, z, y - x - z) if x < y - z
            (2 * y - x, y, x - y + z) if y - z < x < 2 * y
            (x - 2 * y, x - y + z, y) if x > 2 * y
```
has exactly one fixed point, so `|S|` is odd and the involution defined by
`(x, y, z) ↦ (x, z, y)` also has a fixed point."
-/


section Defs

open Finset

variable (k : ℕ) [hk : Fact (4 * k + 1).Prime]

/-- The set of all triples of natural numbers `(x, y, z)` satisfying
`x * x + 4 * y * z = 4 * k + 1`, as a `Set`. -/
def zagierSet := {t : ℕ × ℕ × ℕ | t.1 * t.1 + 4 * t.2.1 * t.2.2 = 4 * k + 1}

lemma zagierSet_lower_bound {x y z : ℕ} (h : (x, y, z) ∈ zagierSet k) : 0 < x ∧ 0 < y ∧ 0 < z := by
  simp_rw [zagierSet, Set.mem_setOf_eq] at h
  refine' ⟨_, _, _⟩ <;> (by_contra q; push_neg at q; rw [le_zero_iff] at q; subst q; simp at h)
  · apply_fun (· % 4) at h
    simp [mul_assoc, Nat.add_mod] at h
  all_goals cases' (Nat.dvd_prime hk.out).1 (dvd_of_mul_left_eq _ h) with e e <;>
    (subst e; simp at h; subst h; simp at hk; exact hk.out)

lemma zagierSet_upper_bound {x y z : ℕ} (h : (x, y, z) ∈ zagierSet k) :
    x ≤ k + 1 ∧ y ≤ k ∧ z ≤ k := by
  obtain ⟨hx, hy, hz⟩ := zagierSet_lower_bound k h
  simp_rw [zagierSet, Set.mem_setOf_eq] at h
  refine' ⟨_, _, _⟩ <;> nlinarith

/-- The set of all triples of natural numbers `(x, y, z) ∈ (0, k + 1] × (0, k] × (0, k]` satisfying
`x * x + 4 * y * z = 4 * k + 1`, as a `Finset`. This is shown to be equivalent to `zagierSet`. -/
def zagierFinset :=
  ((Ioc 0 (k + 1)).product ((Ioc 0 k).product (Ioc 0 k))).filter
    (fun ⟨x, y, z⟩ => x * x + 4 * y * z = 4 * k + 1)

theorem zagierSet_eq : zagierSet k = zagierFinset k := by
  ext ⟨x, y, z⟩
  refine' ⟨fun h => _, fun h => _⟩
  · unfold zagierSet at h
    unfold zagierFinset; simp_all
    have lb := zagierSet_lower_bound k h
    have ub := zagierSet_upper_bound k h
    apply mem_product.2; simp
    constructor; · exact ⟨lb.1, ub.1⟩
    apply mem_product.2; simp
    exact ⟨⟨lb.2.1, ub.2.1⟩, ⟨lb.2.2, ub.2.2⟩⟩
  · unfold zagierFinset at h
    unfold zagierSet; simp_all

/-- The set of all triples of natural numbers `(x, y, z)` satisfying
`x * x + 4 * y * z = 4 * k + 1`, as a `Subtype`. -/
def zagierSubtype := {t // t ∈ zagierSet k}

instance : Fintype (zagierSubtype k) := by
  unfold zagierSubtype
  rw [zagierSet_eq]
  infer_instance

end Defs

section Key

variable {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ} [hp : Fact p.Prime]
  (f : Function.End α) (hf : f^[p] = id)

open Function Submonoid

/-- A shim theorem. -/
theorem pow_eq_iterate (k : ℕ) : f ^ k = f^[k] := by
  induction k with
    | zero => rfl
    | succ n ih =>
      simp only [iterate_succ', ← ih, pow_succ]
      rfl

/-- The powers of a periodic endomorphism form a group with composition as the operation. -/
def groupPowers : Group (powers f) where
  inv := fun ⟨g, hg⟩ => ⟨g^[p - 1], by
    rw [mem_powers_iff] at hg ⊢
    obtain ⟨k, hk⟩ := hg
    use k * (p - 1)
    rw [← pow_eq_iterate, ← hk, pow_mul]⟩
  mul_left_inv := fun ⟨g, hg⟩ => by
    simp only [ge_iff_le, mk_mul_mk]
    congr
    rw [← pow_eq_iterate, ← pow_succ',
      Nat.sub_add_cancel (one_le_two.trans (Nat.Prime.two_le hp.out))]
    rw [mem_powers_iff] at hg
    obtain ⟨k, hk⟩ := hg
    rw [← hk, ← pow_mul, mul_comm, pow_mul, pow_eq_iterate f, hf, pow_eq_iterate, iterate_id]
    rfl

instance : MulAction (powers f) α where
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem isPGroup_of_powers : @IsPGroup p (powers f) (groupPowers f hf) := by
  unfold IsPGroup
  intro ⟨g, hg⟩
  use 1
  simp; congr
  rw [mem_powers_iff] at hg
  obtain ⟨k, hk⟩ := hg
  rw [← hk, ← pow_mul, mul_comm, pow_mul, pow_eq_iterate f, hf, pow_eq_iterate, iterate_id]
  rfl

noncomputable instance : Fintype (MulAction.fixedPoints (powers f) α) :=
  Fintype.ofFinite (MulAction.fixedPoints (powers f) α)

theorem key (hf : Involutive f) :
    Fintype.card α ≡ Fintype.card (MulAction.fixedPoints (powers f) α) [MOD 2] := by
  rw [involutive_iff_iter_2_eq_id] at hf
  exact @IsPGroup.card_modEq_card_fixedPoints _ _ (_) (isPGroup_of_powers f hf) _ _ _ _ _

end Key

section Involution

open Finset Function Submonoid

variable (k : ℕ) [hk : Fact (4 * k + 1).Prime]

/-- The obvious involution `(x, y, z) ↦ (x, z, y)`. Its fixed points correspond to representations
of `4 * k + 1` as a sum of two squares. -/
def obvInvo : Function.End (zagierSubtype k) := fun ⟨⟨x, y, z⟩, h⟩ => ⟨⟨x, z, y⟩, by
  unfold zagierSet at *
  simp_all
  linarith [h]⟩

theorem involutive_obvInvo : Involutive (obvInvo k) := by
  unfold Involutive obvInvo zagierSubtype; simp

theorem sq_add_sq_of_nonempty_fixedPoints
    (hn : (MulAction.fixedPoints (powers (obvInvo k)) (zagierSubtype k)).Nonempty) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = 4 * k + 1 := by
  simp_rw [sq]
  obtain ⟨⟨⟨x, y, z⟩, he⟩, hf⟩ := hn
  rw [MulAction.mem_fixedPoints, Subtype.forall] at hf
  have := hf (obvInvo k) (mem_powers _)
  apply_fun Subtype.val at this
  rw [Submonoid.smul_def, End.smul_def] at this
  unfold obvInvo at this; simp at this
  unfold zagierSet at he; simp at he
  use x, (2 * y)
  rw [this.1, show 4 * y * y = 2 * y * (2 * y) by linarith] at he
  assumption

/-- The complicated involution, which is shown to have exactly one fixed point `(1, 1, k)`. -/
def complexInvo : Function.End (zagierSubtype k) := fun ⟨⟨x, y, z⟩, h⟩ =>
  ⟨if x + z < y then ⟨x + 2 * z, z, y - x - z⟩ else
   if 2 * y < x then ⟨x - 2 * y, x + z - y, y⟩ else
                     ⟨2 * y - x, y, x + z - y⟩, by
  unfold zagierSet at *
  simp at h
  split_ifs with less more <;> simp
  · rw [Nat.sub_sub]
    zify [less.le] at h ⊢
    ring_nf
    linarith [h]
  · push_neg at less
    zify [less, more.le] at h ⊢
    ring_nf
    linarith [h]
  · push_neg at less more
    zify [less, more] at h ⊢
    ring_nf
    linarith [h]⟩

theorem involutive_complexInvo : Involutive (complexInvo k) := by
  unfold Involutive
  intro ⟨⟨x, y, z⟩, h⟩
  obtain ⟨xb, _, _⟩ := zagierSet_lower_bound k h
  conv_lhs =>
    arg 2
    tactic => unfold complexInvo
    dsimp
  split_ifs with less more <;> (unfold complexInvo; simp; congr)
  · simp [show ¬(x + 2 * z + (y - x - z) < z) by linarith [less], xb]
    rw [Nat.sub_sub, two_mul, ← tsub_add_eq_add_tsub (by linarith), ← add_assoc,
      Nat.add_sub_cancel, add_comm (x + z), Nat.sub_add_cancel (less.le)]
  · push_neg at less
    simp [(show x - 2 * y + y < x + z - y by zify [more.le, less]; linarith)]
    constructor
    · rw [Nat.sub_add_cancel more.le]
    · rw [Nat.sub_right_comm, Nat.sub_sub _ _ y, ← two_mul, add_comm, Nat.add_sub_assoc more.le,
        Nat.add_sub_cancel]
  · push_neg at less more
    simp [(show ¬(2 * y - x + (x + z - y) < y) by push_neg; zify [less, more]; linarith),
      (show ¬(2 * y < 2 * y - x) by push_neg; zify [more]; linarith)]
    constructor
    · rw [tsub_tsub_assoc (by rfl) more, tsub_self, zero_add]
    · rw [← Nat.add_sub_assoc less (2 * y - x), ← add_assoc, Nat.sub_add_cancel more,
        Nat.sub_sub _ _ y, ← two_mul, add_comm, Nat.add_sub_cancel]

theorem unique {t : zagierSubtype k}
    (mem : t ∈ (MulAction.fixedPoints (powers (complexInvo k)) (zagierSubtype k))) :
    t.val = (1, 1, k):= by
  simp only [MulAction.mem_fixedPoints, Subtype.forall] at mem
  replace mem := mem (complexInvo k) (mem_powers _)
  rw [Submonoid.smul_def, End.smul_def] at mem
  unfold complexInvo at mem
  obtain ⟨⟨x, y, z⟩, h⟩ := t
  obtain ⟨xb, yb, zb⟩ := zagierSet_lower_bound k h
  apply_fun Subtype.val at mem
  simp at mem
  split_ifs at mem with less more <;> simp_all
  · obtain ⟨_, _, _⟩ := mem
    simp_all
  · -- True case
    unfold zagierSet at h; simp at h
    replace mem := mem.1
    rw [tsub_eq_iff_eq_add_of_le more, ← two_mul] at mem
    replace mem := (mul_left_cancel₀ two_ne_zero mem).symm
    subst mem
    rw [show x * x + 4 * x * z = x * (x + 4 * z) by linarith] at h
    cases' (Nat.dvd_prime hk.out).1 (dvd_of_mul_left_eq _ h) with e e
    · rw [e, mul_one] at h; subst h
      simp_all [show z = 0 by linarith [e]]
    · rw [e, mul_left_eq_self₀] at h; simp_all
      linarith [e]

theorem aux :
    MulAction.fixedPoints (powers (complexInvo k)) (zagierSubtype k) =
    {⟨(1, 1, k), (by unfold zagierSet; simp; linarith)⟩} := by
  rw [Set.eq_singleton_iff_unique_mem]
  constructor
  · simp
    intro f h
    rw [Submonoid.smul_def, End.smul_def]
    simp
    rw [mem_powers_iff] at h
    obtain ⟨n, h⟩ := h
    cases' Nat.even_or_odd n with heven hodd <;> rw [pow_eq_iterate] at h
    · rw [(involutive_complexInvo k).iterate_even heven] at h
      rw [← h, id_eq]
    · rw [(involutive_complexInvo k).iterate_odd hodd] at h
      rw [← h]
      unfold complexInvo
      simp
  · intro t mem
    replace mem := unique k mem
    unfold zagierSubtype at t
    congr!

theorem positive_of_odd {n : ℕ} (h : n % 2 = 1) : 0 < n := by
  by_contra j; push_neg at j; rw [nonpos_iff_eq_zero] at j; subst j; norm_num at h

theorem result : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 4 * k + 1 := by
  apply sq_add_sq_of_nonempty_fixedPoints
  have := (key (obvInvo k) (involutive_obvInvo k)).symm.trans
    (key (complexInvo k) (involutive_complexInvo k))
  rw [← Set.toFinset_card] at this
  simp [aux] at this; unfold Nat.ModEq at this; norm_num at this
  replace this := positive_of_odd this
  rw [← Set.toFinset_card, card_pos, Set.toFinset_nonempty] at this
  assumption

end Involution

/-- **Fermat's theorem on sums of two squares**. Every prime congruent to 1 mod 4 is the sum
of two squares, proved using Zagier's involutions. -/
theorem Nat.Prime.sq_add_sq' {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  have md := div_add_mod p 4
  rw [hp] at md
  have := @result (p / 4) (by rw [md]; infer_instance)
  rw [md] at this
  assumption

-- Verify that the above proof does not rely on quadratic reciprocity,
-- unlike `Nat.Prime.sq_add_sq` in `NumberTheory/SumTwoSquares.lean`
assert_not_exists Nat.Prime.sq_add_sq
