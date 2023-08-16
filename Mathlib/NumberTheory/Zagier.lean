/-
Copyright (c) 2023 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.GroupTheory.PGroup

/-!
# Zagier's "one-sentence proof" of Fermat's theorem of sums of two squares

Involving some extreme trickery with parities of fixed points of involutions.
-/


section Defs

open Finset

variable (k : ℕ) [hk : Fact (4 * k + 1).Prime]

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

instance fintypeZagierSet : Fintype (zagierSet k) := by rw [zagierSet_eq]; infer_instance

def zagierSubtype := {t // t ∈ zagierSet k}

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

instance mulActionPowers : MulAction (powers f) α where
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

noncomputable instance mafp : Fintype (MulAction.fixedPoints (powers f) α) :=
  Fintype.ofFinite (MulAction.fixedPoints (powers f) α)

def key := @IsPGroup.card_modEq_card_fixedPoints _ _ (_) (isPGroup_of_powers f hf) _ α _ _ _

end Key

section Two

open Function Submonoid Fintype

variable {α : Type*} [Fintype α] [DecidableEq α] (f : Function.End α)

theorem key2 (hf : Involutive f) : card α ≡ card (MulAction.fixedPoints (powers f) α) [MOD 2] := by
  rw [involutive_iff_iter_2_eq_id] at hf
  exact key (p := 2) f hf

end Two

section Involution

open Finset Function Submonoid

variable (k : ℕ) [hk : Fact (4 * k + 1).Prime]

def obvInvo : Function.End (zagierSubtype k) := fun ⟨⟨x, y, z⟩, h⟩ => ⟨⟨x, z, y⟩, by
  unfold zagierSet at *
  simp_all
  linarith [h]⟩

theorem involutive_obvInvo : Involutive (obvInvo k) := by
  unfold Involutive obvInvo zagierSubtype; simp

theorem sq_add_sq_of_nonempty_fixedPoints
    (hn : (MulAction.fixedPoints (powers (obvInvo k)) (zagierSubtype k)).Nonempty) :
    ∃ a b : ℕ, a * a + b * b = 4 * k + 1 := by
  obtain ⟨⟨⟨x, y, z⟩, he⟩, hf⟩ := hn
  rw [MulAction.mem_fixedPoints, Subtype.forall] at hf
  have := hf (obvInvo k) (mem_powers _)
  sorry

end Involution
