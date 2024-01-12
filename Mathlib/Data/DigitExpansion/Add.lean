/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Data.DigitExpansion.Defs

/-!
# Defining reals without the use of rationals, the additive group structure

* [Defining reals without the use of rationals][debruijn1976]

-/

-- TODO
theorem Int.neg_mod {a b : ℤ} : -a % b = (b - a) % b := by
  rw [← Int.add_emod_self_left, sub_eq_add_neg]

-- TODO
lemma Fin.pos_of_ne_zero {n : ℕ} {a : Fin (n + 1)} (h : a ≠ 0) :
    0 < a :=
  Nat.pos_of_ne_zero (Fin.val_ne_of_ne h)

-- TODO
theorem Fin.neg_coe_eq_one (n : ℕ) : -(n : Fin (n + 1)) = 1 := by
  simp [neg_eq_iff_add_eq_zero]

-- TODO
@[elab_as_elim]
theorem Succ.rec' {Z : Type*} [LinearOrder Z] [SuccOrder Z] [IsSuccArchimedean Z] {P : Z → Prop}
    {m : Z} (h0 : P m) (h1 : ∀ n, m ≤ n → (∀ k, m ≤ k → k ≤ n → P k) → P (Order.succ n)) ⦃n : Z⦄
    (hmn : m ≤ n) : P n := by
  refine' Succ.rec h0 _ hmn
  intro n hn _
  refine' h1 n hn _
  refine' Succ.rec _ _ hn
  · intro k hmk hkm
    rwa [le_antisymm hkm hmk]
  · intro n hmn IH k hmk hkn
    rcases hkn.eq_or_lt with (rfl | hkn')
    · exact h1 _ hmn IH
    · exact IH _ hmk (Order.le_of_lt_succ hkn')

-- TODO
-- TODO
lemma Fin.rev_add {n : ℕ} (a b : Fin n) : rev (a + b) = rev a - b := by
  cases' n
  · exact a.elim0
  rw [← last_sub, ← last_sub, sub_add_eq_sub_sub]

lemma Fin.rev_sub {n : ℕ} (a b : Fin n) : rev (a - b) = rev a + b := by
  cases' n
  · exact a.elim0
  rw [← last_sub, ← last_sub, sub_sub_eq_add_sub, add_sub_right_comm]

lemma Fin.lt_sub_iff {n : ℕ} {a b : Fin n} : a < a - b ↔ a < b := by
  cases' n with n
  · exact a.elim0
  rcases lt_or_le a b with h|h
  · simp only [h, iff_true]
    rw [lt_iff_val_lt_val, sub_def]
    simp only
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt b.is_lt
    have : n.succ - b = k + 1 := by
      simp_rw [hk]
      rw [add_assoc, add_tsub_cancel_left]
    rw [this, Nat.mod_eq_of_lt]
    · simp
    · refine' hk.ge.trans_lt' ?_
      simp [add_assoc, h]
  · simp only [h.not_lt, iff_false, not_lt]
    obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le h
    rw [le_iff_val_le_val, sub_def, hl]
    simp only
    rw [add_right_comm, add_tsub_cancel_of_le b.is_lt.le, Nat.add_mod_left, Nat.mod_eq_of_lt]
    · simp
    · refine a.is_lt.trans_le' ?_
      simp [hl]

lemma Fin.add_lt_left_iff {n : ℕ} {a b : Fin n} : a + b < a ↔ rev b < a := by
  cases' n
  · exact a.elim0
  rw [← Fin.rev_lt_rev, Iff.comm, ← Fin.rev_lt_rev, rev_add, lt_sub_iff, rev_rev]

-- TODO
@[simp]
theorem Fin.neg_last (n : ℕ) : -Fin.last n = 1 := by simp [neg_eq_iff_add_eq_zero]

-- TODO
@[simp]
lemma Fin.lt_one_iff' {n : ℕ} [hn : NeZero n] (x : Fin (n + 1)) : x < 1 ↔ x = 0 := by
  cases' n
  · simp at hn
  simp [Fin.lt_iff_val_lt_val, Fin.ext_iff]

open Order

namespace DigitExpansion

variable {Z : Type*} [PartialOrder Z] [SuccOrder Z] [NoMaxOrder Z] [PredOrder Z] [NoMinOrder Z]
    [IsSuccArchimedean Z] {b : ℕ} [hb : NeZero b]
    [∀ (f g : DigitExpansion Z b) z, Decidable (∃ x > z, f x < g x ∧ ∀ y < x, z < y → f y ≤ g y)]

instance : Sub (DigitExpansion Z b) :=
  ⟨fun f g =>
    { toFun := fun x => f x - g x - difcar f g x
      bounded' := by
        rintro ⟨x, hx⟩
        obtain ⟨w, hw, hfgw⟩ : ∃ w ≥ x, difcar f g w = 0 := by
          cases' difcar_eq_zero_or_one f g x with px px
          · exact ⟨x, le_rfl, px⟩
          · rw [difcar_eq_one_iff] at px
            obtain ⟨y, hxy, hfgy, _⟩ := px
            have := hx y hxy
            rw [sub_eq_iff_eq_add] at this
            refine' ⟨y, le_of_lt hxy, _⟩
            refine' Or.resolve_right (difcar_eq_zero_or_one _ _ _) fun H => _
            rw [H, ← Nat.cast_add_one, Fin.nat_cast_self, sub_eq_zero] at this
            exact absurd this hfgy.ne
        suffices ∀ z > w, difcar f g z = 0 ∧ f z = b by
          obtain ⟨z, hwz, hz⟩ := f.exists_bounded w
          exact not_le_of_lt hz (this _ hwz).right.ge
        suffices ∀ z > x, difcar f g (pred z) = 0 → f z = b ∧ g z = 0 ∧ difcar f g z = 0 by
          intro z hwz
          refine' Succ.rec _ _ (succ_le_of_lt hwz)
          · refine' (this _ (lt_of_le_of_lt hw (lt_succ _)) _).symm.imp And.right id
            rwa [pred_succ]
          · rintro k hk ⟨hd, _⟩
            refine' (this _ _ _).symm.imp And.right id
            · exact lt_of_lt_of_le (lt_of_le_of_lt hw (succ_le_iff.mp hk)) (le_succ _)
            · rwa [pred_succ]
        intro z hxz hfgz
        specialize hx z hxz
        rw [sub_eq_iff_eq_add, sub_eq_iff_eq_add] at hx
        rcases lt_trichotomy (f z) (g z) with (H | H | H)
        · simp [difcar_pred_eq_one H, hb.out] at hfgz
        · simp [← difcar_pred_eq_difcar H, H, hfgz, Fin.ext_iff, hb.out] at hx
        cases' difcar_eq_zero_or_one f g z with hd hd
        · rw [hd, add_zero] at hx
          cases' (Fin.zero_le' (g z)).eq_or_lt with hg hg
          · simp [hx, ← hg, hd]
          · have : g z - 1 = b + g z := by simp [sub_eq_iff_eq_add, add_right_comm]
            cases b
            · simpa using hb.out
            rw [hx, ← this, Fin.lt_sub_one_iff] at H
            simp [hx, H, hd]
        · simp [hd, H.ne'] at hx }⟩

variable (f g : DigitExpansion Z b)

protected theorem sub_def (x : Z) : (f - g) x = f x - g x - difcar f g x :=
  rfl

theorem coe_sub (z : Z) :
    ((f - g) z : ℤ) = f z - g z - difcar f g z + (b + 1) * difcar f g (pred z) := by
  simp_rw [f.sub_def, Fin.coe_sub]
  simp only [Nat.cast_sub, (g z).is_lt.le, (difcar f g z).is_lt.le, Nat.mod_add_mod,
    Int.coe_nat_mod, Nat.cast_add, Nat.cast_one]
  rw [add_sub, add_sub, add_comm, ← add_sub, Int.add_emod_self_left, add_comm, ← add_sub, ← add_sub,
    Int.add_emod_self_left]
  cases b
  · exact absurd rfl hb.out
  rw [← Nat.cast_succ]
  rcases lt_trichotomy (f z) (g z) with (h | h | h)
  · simp only [difcar_pred_eq_one h, Fin.val_one, Nat.cast_one, mul_one]
    rw [← Int.add_emod_self, Int.emod_eq_of_lt]
    · rw [sub_add, sub_sub, le_sub_comm, sub_zero, add_sub, tsub_le_iff_right, ← Nat.cast_add, ←
        Nat.cast_add, Int.ofNat_le]
      exact
        le_add_self.trans' (add_le_add (g z).is_le (Fin.le_iff_val_le_val.mp (difcar_le_one _ _ _)))
    · simp only [sub_lt_comm, add_lt_iff_neg_right, tsub_zero]
      refine (Int.sub_le_self _ (Int.ofNat_nonneg _)).trans_lt ?_
      simp [h]
  · simp only [h, difcar_pred_eq_difcar h, Int.neg_mod, sub_self, zero_sub]
    cases' difcar_eq_zero_or_one f g z with hd hd
    · simp [hd, Int.emod_self]
    · rw [hd, Fin.val_one, ← Nat.cast_sub, ← Int.coe_nat_mod]
      · simp [eq_neg_add_iff_add_eq, add_comm]
      · simp [Nat.succ_le_succ_iff]
  · simp only [difcar_pred_eq_zero h, Fin.val_zero, Nat.cast_zero, MulZeroClass.mul_zero, add_zero]
    have h' := h
    rw [Fin.lt_iff_val_lt_val] at h'
    rw [← Nat.cast_sub h'.le, Int.emod_eq_of_lt]
    · rw [sub_nonneg, Int.ofNat_le, le_tsub_iff_right h'.le, add_comm]
      cases' difcar_eq_zero_or_one f g z with hd hd <;> simp [hd, Nat.succ_le_iff, h, h.le]
    · rw [← Nat.cast_sub, Int.ofNat_lt]
      · exact tsub_lt_of_lt (tsub_lt_of_lt (f z).is_lt)
      · refine' (Fin.le_iff_val_le_val.mp (difcar_le_one _ _ _)).trans _
        rw [Fin.val_one, Nat.succ_le_iff, tsub_pos_iff_lt]
        exact h'

protected theorem sub_zero : f - 0 = f := by
  ext; simp [DigitExpansion.sub_def]

protected theorem sub_self : f - f = 0 := by
  ext; simp [DigitExpansion.sub_def]

protected theorem sub_sub_comm (h : DigitExpansion Z b) :
    f - (g - h) = h - (g - f) := by
  set p := difcar g h with hp
  set s := g - h with hs
  set t := f - s with ht
  set q := difcar f s with hq
  set p' := difcar g f with hp'
  set s' := g - f with hs'
  set t' := h - s' with ht'
  set q' := difcar h s' with hq'
  have hsz : ∀ z, (s z : ℤ) = g z - h z - p z + (b + 1) * p (pred z) := by
    intro z; rw [hs, hp, coe_sub g h z]
  have htz :
      ∀ z, (t z : ℤ) = f z + h z - g z + (p z - q z) - (b + 1) * (p (pred z) - q (pred z)) := by
    intro z; rw [ht, hq, coe_sub f s z, hsz]; ring
  have hsz' : ∀ z, (s' z : ℤ) = g z - f z - p' z + (b + 1) * p' (pred z) := by
    intro z; rw [hs', hp', coe_sub g f z]
  have htz' :
    ∀ z, (t' z : ℤ) = h z + f z - g z + (p' z - q' z) - (b + 1) * (p' (pred z) - q' (pred z)) := by
    intro z; rw [ht', hq', coe_sub h s' z, hsz']; ring
  have H :
      ∀ z, (t z : ℤ) - t' z = p z - q z - (p' z - q' z) -
          (b + 1) * (p (pred z) - q (pred z) - (p' (pred z) - q' (pred z))) := by
    intro z; rw [htz, htz']; ring
  clear hsz hsz' htz htz'
  have htd : ∀ z, |(t z : ℤ) - t' z| < b + 1 := by
    intro z
    rw [abs_lt, ← Nat.cast_succ]
    refine'
      ⟨Int.neg_lt_sub_left_of_lt_add ((Int.le_add_of_nonneg_right _).trans_lt' _),
        Int.sub_right_lt_of_lt_add ((Int.le_add_of_nonneg_right _).trans_lt' _)⟩
    · simp
    · exact Int.ofNat_lt_ofNat_of_lt (t' z).is_lt
    · simp
    · exact Int.ofNat_lt_ofNat_of_lt (t z).is_lt
  have hpq1 : ∀ z, |(p z : ℤ) - q z| ≤ 1 := by
    intro z
    rw [hp, hq]
    cases b
    · exact absurd rfl hb.out
    cases' difcar_eq_zero_or_one g h z with hp0 hp0 <;>
        cases' difcar_eq_zero_or_one f s z with hq0 hq0 <;>
      norm_num [hp0, hq0]
  have hpq1' : ∀ z, |(p' z : ℤ) - q' z| ≤ 1 := by
    intro z
    rw [hp', hq']
    cases b
    · exact absurd rfl hb.out
    cases' difcar_eq_zero_or_one g f z with hp0 hp0 <;>
        cases' difcar_eq_zero_or_one h s' z with hq0 hq0 <;>
      norm_num [hp0, hq0]
  have hr2 : ∀ z, |(p z : ℤ) - q z - (p' z - q' z)| ≤ 2 := by
    intro z
    refine' (abs_sub _ _).trans ((add_le_add (hpq1 _) (hpq1' _)).trans _)
    norm_num
  replace hr2 : ∀ z, |(p (pred z) : ℤ) - q (pred z) - (p' (pred z) - q' (pred z))| ≤ 1
  · intro z
    specialize htd z
    rw [H] at htd
    have hr2' := hr2 (pred z)
    rw [abs_le] at hr2' ⊢
    rw [le_iff_lt_or_eq, le_iff_lt_or_eq, Int.lt_iff_add_one_le, Int.lt_iff_add_one_le] at hr2'
    rcases hr2' with ⟨hl | hl, hr | hr⟩
    · rw [← le_sub_iff_add_le] at hr
      norm_num1 at hl hr
      exact ⟨hl, hr⟩
    · rw [hr, abs_lt, mul_two, ← sub_sub, sub_lt_iff_lt_add, lt_sub_comm, sub_neg_eq_add,
        sub_add_cancel] at htd
      suffices (b : ℤ) + 1 < 2 by norm_num [← lt_sub_iff_add_lt, hb.out] at this
      exact htd.left.trans_le (le_of_abs_le (hr2 _))
    · rw [← hl, abs_lt, mul_neg, sub_neg_eq_add, mul_two, ← add_assoc, add_lt_iff_neg_right] at htd
      suffices (b : ℤ) + 1 < 2 by norm_num [← lt_sub_iff_add_lt, hb.out] at this
      rw [← sub_neg_eq_add _ ((b : ℤ) + 1), ← sub_neg_eq_add _ ((b : ℤ) + 1), sub_lt_iff_lt_add,
        zero_add, lt_neg] at htd
      exact htd.right.trans_le ((neg_le_abs_self _).trans (hr2 _))
    · rw [hr, abs_lt, mul_two, ← sub_sub, sub_lt_iff_lt_add, lt_sub_comm, sub_neg_eq_add,
        sub_add_cancel] at htd
      suffices (b : ℤ) + 1 < 2 by norm_num [← lt_sub_iff_add_lt, hb.out] at this
      exact htd.left.trans_le (le_of_abs_le (hr2 _))
  replace hpq1 :
    ∀ z,
      (p (pred z) : ℤ) - q (pred z) - (p' (pred z) - q' (pred z)) = 1 →
        (p z : ℤ) - q z - (p' z - q' z) = 1
  · intro z hz
    specialize H z
    rw [hz, mul_one] at H
    have hr2' := hr2 (succ z)
    rw [pred_succ, Int.abs_le_one_iff] at hr2'
    rcases hr2' with (hr2' | hr2' | hr2')
    · rw [hr2', zero_sub] at H
      exact absurd H (neg_lt_of_abs_lt (htd _)).ne'
    · exact hr2'
    · rw [hr2'] at H
      refine' absurd H (ne_of_gt ((neg_lt_of_abs_lt (htd _)).trans' _))
      rw [← zero_sub ((b : ℤ) + 1), sub_lt_sub_iff_right, neg_lt_zero]
      exact zero_lt_one
  replace hpq1' :
    ∀ z,
      (p' (pred z) : ℤ) - q' (pred z) - (p (pred z) - q (pred z)) = 1 →
        (p' z : ℤ) - q' z - (p z - q z) = 1
  · intro z hz
    specialize H z
    rw [← neg_inj, neg_sub] at hz
    rw [hz, mul_neg, mul_one, sub_neg_eq_add] at H
    have hr2' := hr2 (succ z)
    rw [pred_succ, Int.abs_le_one_iff] at hr2'
    rcases hr2' with (hr2' | hr2' | hr2')
    · rw [hr2', zero_add] at H
      exact absurd H (lt_of_abs_lt (htd _)).ne
    · rw [hr2'] at H
      refine' absurd H (ne_of_lt ((lt_of_abs_lt (htd _)).trans _))
      simp
    · rw [← neg_inj, neg_sub, hr2']
  clear htd
  replace hpq1 :
    ∀ z,
      (p (pred z) : ℤ) - q (pred z) - (p' (pred z) - q' (pred z)) = 1 →
        ∀ y ≥ z, (p y : ℤ) - q y - (p' y - q' y) = 1
  · intro z hz y hy
    refine' Succ.rec (hpq1 _ hz) (fun x _ hpx => hpq1 _ _) hy
    rw [pred_succ]
    exact hpx
  replace hpq1' :
    ∀ z,
      (p (pred z) : ℤ) - q (pred z) - (p' (pred z) - q' (pred z)) = -1 →
        ∀ y ≥ z, (p y : ℤ) - q y - (p' y - q' y) = -1
  · intro z hz y hy
    rw [eq_comm, neg_eq_iff_eq_neg, eq_comm, neg_sub] at hz ⊢
    refine' Succ.rec (hpq1' _ hz) (fun x _ hpx => hpq1' _ _) hy
    rw [pred_succ]
    exact hpx
  replace hpq1 : ¬∃ z, (p (pred z) : ℤ) - q (pred z) - (p' (pred z) - q' (pred z)) = 1
  · rintro ⟨z, hz⟩
    suffices ∀ y > z, (t' y : ℤ) = b by
      obtain ⟨x, hx, hb⟩ := t'.exists_bounded z
      specialize this x hx
      simp only [Nat.cast_inj] at this
      rw [Fin.lt_iff_val_lt_val, Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt (Nat.lt_succ_self _)] at hb
      exact hb.ne this
    intro y hy
    specialize H y
    rw [hpq1 z hz _ (le_pred_of_lt hy), hpq1 z hz _ (le_of_lt hy), mul_one] at H
    cases' (Fin.le_last (t' y)).eq_or_lt with hbz hbz
    · simp [hbz]
    · have htz0 : (0 : ℤ) = t y := by
        refine' le_antisymm _ _
        · rw [← Nat.cast_zero, Nat.cast_le]
          exact (t y).zero_le
        rw [sub_eq_iff_eq_add] at H
        rw [H, sub_add, sub_le_comm, sub_zero, add_comm, ← add_sub, le_add_iff_nonneg_right,
            sub_nonneg, Nat.cast_le]
        exact (t' y).is_le
      rw [← htz0, zero_sub, neg_eq_iff_eq_neg, eq_comm] at H
      simp [← H]
  replace hpq1' : ¬∃ z, (p (pred z) : ℤ) - q (pred z) - (p' (pred z) - q' (pred z)) = -1
  · rintro ⟨z, hz⟩
    suffices ∀ y > z, (t y : ℤ) = b by
      obtain ⟨x, hx, hb⟩ := t.exists_bounded z
      specialize this x hx
      simp only [Nat.cast_inj] at this
      rw [Fin.lt_iff_val_lt_val, Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt (Nat.lt_succ_self _)] at hb
      exact hb.ne this
    intro y hy
    specialize H y
    rw [hpq1' z hz _ (le_pred_of_lt hy), hpq1' z hz _ (le_of_lt hy), mul_neg, mul_one] at H
    cases' (Fin.le_last (t y)).eq_or_lt with hbz hbz
    · simp [hbz]
    · have htz0 : (0 : ℤ) = t' y := by
        refine' le_antisymm _ _
        · rw [← Nat.cast_zero, Nat.cast_le]
          exact (t' y).zero_le
        rw [← neg_add', eq_comm, neg_eq_iff_eq_neg, eq_comm, neg_sub, sub_eq_iff_eq_add,
            ← sub_eq_add_neg, ← sub_sub, sub_sub_cancel_left] at H
        rw [H, add_comm, ← sub_eq_add_neg, sub_le_comm, sub_zero, Nat.cast_le]
        exact (t y).is_le
      rw [← htz0, sub_zero] at H
      simp [H]
  replace hr2 : ∀ z, (p z : ℤ) - q z - (p' z - q' z) = 0
  · push_neg at hpq1 hpq1'
    intro z
    specialize hr2 (succ z)
    rw [Int.abs_le_one_iff] at hr2
    rcases hr2 with (hr2' | hr2' | hr2')
    · rw [← pred_succ z]
      exact hr2'
    · exact absurd hr2' (hpq1 _)
    · exact absurd hr2' (hpq1' _)
  ext z
  rw [← @Nat.cast_inj ℤ, ← sub_eq_zero, H, hr2, hr2, MulZeroClass.mul_zero, sub_zero]

instance : Add (DigitExpansion Z b) :=
  ⟨fun f g => f - (0 - g)⟩

protected theorem add_def : f + g = f - (0 - g) :=
  rfl

protected theorem add_zero : f + 0 = f :=
  calc
    f + 0 = f - (0 - 0) := rfl
    _ = f - 0 := by rw [DigitExpansion.sub_zero]
    _ = f := DigitExpansion.sub_zero _

protected theorem add_comm : f + g = g + f :=
  calc
    f + g = f - (0 - g) := rfl
    _ = g - (0 - f) := (DigitExpansion.sub_sub_comm _ _ _)
    _ = g + f := rfl

protected theorem add_assoc (h : DigitExpansion Z b) : f + (g + h) = f + g + h :=
  calc
    f + (g + h) = f + (h + g) := by rw [g.add_comm]
    _ = f - (0 - (h - (0 - g))) := by simp_rw [DigitExpansion.add_def]
    _ = f - (0 - g - (h - 0)) := by rw [DigitExpansion.sub_sub_comm 0, DigitExpansion.sub_zero]
    _ = f - (0 - g - h) := by rw [DigitExpansion.sub_zero]
    _ = h - (0 - g - f) := (DigitExpansion.sub_sub_comm _ _ _)
    _ = h - (0 - g - (f - 0)) := by rw [DigitExpansion.sub_zero]
    _ = h - (0 - (f - (0 - g))) := by rw [DigitExpansion.sub_sub_comm 0, DigitExpansion.sub_zero]
    _ = h + (f + g) := by simp_rw [DigitExpansion.add_def]
    _ = f + g + h := DigitExpansion.add_comm _ _

protected theorem add_sub_cancel : g + (f - g) = f :=
  calc
    g + (f - g) = g - (0 - (f - g)) := DigitExpansion.add_def _ _
    _ = g - (g - (f - 0)) := by rw [DigitExpansion.sub_sub_comm g f 0]
    _ = g - (g - f) := by rw [DigitExpansion.sub_zero]
    _ = f - (g - g) := (DigitExpansion.sub_sub_comm _ _ _)
    _ = f - 0 := by rw [DigitExpansion.sub_self]
    _ = f := DigitExpansion.sub_zero _

instance : Neg (DigitExpansion Z b) :=
  ⟨fun f => 0 - f⟩

protected theorem neg_def : -f = 0 - f :=
  rfl

instance : AddCommGroup (DigitExpansion Z b) where
  add := (· + ·)
  add_assoc _ _ _ := (DigitExpansion.add_assoc _ _ _).symm
  zero := 0
  zero_add _ := by
    simp_rw [DigitExpansion.add_def, DigitExpansion.sub_sub_comm, DigitExpansion.sub_zero]
  add_zero := DigitExpansion.add_zero
  neg f := -f
  sub f g := f - g
  sub_eq_add_neg f g := by
    simp [g.neg_def, f.add_def, DigitExpansion.sub_sub_comm 0, DigitExpansion.sub_zero]
  add_left_neg f := by
    rw [f.neg_def, DigitExpansion.add_def]
    simp [DigitExpansion.sub_sub_comm,
      DigitExpansion.sub_sub_comm 0 0 f, DigitExpansion.sub_zero, DigitExpansion.sub_self]
  add_comm _ _ := DigitExpansion.add_comm _ _

theorem Negative.neg_positive {Z : Type*} [PartialOrder Z] [SuccOrder Z] [NoMaxOrder Z]
    [PredOrder Z] [NoMinOrder Z] [IsSuccArchimedean Z] {b : ℕ} [hb : NeZero b]
    [∀ (f g : DigitExpansion Z b) z, Decidable (∃ x > z, f x < g x ∧ ∀ y < x, z < y → f y ≤ g y)]
    {f : DigitExpansion Z b} (hf : f.Negative) : (-f).Positive := by
  refine' ⟨_, _⟩
  · rw [Ne.def, neg_eq_iff_eq_neg, eq_comm, neg_zero]
    exact hf.left.symm
  · simp_rw [f.neg_def, DigitExpansion.sub_def]
    obtain ⟨x, hx⟩ := hf.right
    refine' ⟨pred x, fun y hy => _⟩
    simp_rw [hx y (hy.trans (pred_lt _)), zero_apply, zero_sub, sub_eq_zero]
    rw [Fin.neg_coe_eq_one b, eq_comm, difcar_eq_one_iff]
    refine' ⟨pred x, hy, _⟩
    simpa [hx (pred x) (pred_lt _), Fin.lt_iff_val_lt_val] using Nat.pos_of_ne_zero hb.out

variable {Z : Type*} [LinearOrder Z] [SuccOrder Z] [NoMaxOrder Z] [PredOrder Z] [NoMinOrder Z]
    [IsSuccArchimedean Z] {b : ℕ} [hb : NeZero b]
    [∀ (f g : DigitExpansion Z b) z, Decidable (∃ x > z, f x < g x ∧ ∀ y < x, z < y → f y ≤ g y)]
    {f g : DigitExpansion Z b}

theorem Positive.exists_least_pos (hf : f.Positive) : ∃ x, 0 < f x ∧ ∀ y < x, f y = 0 := by
  obtain ⟨x, hx⟩ : ∃ x, ∀ y ≤ x, f y = 0 := by
    obtain ⟨_, x, hx⟩ := hf
    exact ⟨pred x, fun y hy => hx _ (hy.trans_lt (pred_lt _))⟩
  obtain ⟨hne, -⟩ := id hf
  contrapose! hne
  ext z : 1
  rw [zero_apply]
  cases' le_total z x with h h
  · rw [hx _ h]
  refine' Succ.rec' _ _ h
  · rw [hx _ le_rfl]
  intro w _ IH
  cases' (Fin.zero_le' (f (succ w))).eq_or_lt with H H
  · exact H.symm
  · obtain ⟨y, hy, hne⟩ := hne _ H
    refine' absurd (IH _ _ (le_of_lt_succ hy)) hne
    refine' Or.resolve_right (le_total _ _) fun H => hne _
    rw [hx _ H]

theorem Negative.exists_least_cap (hf : f.Negative) : ∃ x, f x ≠ b ∧ ∀ y < x, f y = b := by
  obtain ⟨x, hx⟩ : ∃ x, ∀ y ≤ x, f y = b := by
    obtain ⟨_, x, hx⟩ := hf
    exact ⟨pred x, fun y hy => hx _ (hy.trans_lt (pred_lt _))⟩
  obtain ⟨z, hz, hz'⟩ := f.exists_bounded x
  revert hz'
  refine' Succ.rec' _ _ hz.le
  · intro hxb
    refine' ⟨x, hxb.ne, _⟩
    intro y hy
    exact hx y hy.le
  intro w _ IH hw
  by_cases H : ∃ u, x ≤ u ∧ u ≤ w ∧ f u < b
  · obtain ⟨u, hu, hu', hu''⟩ := H
    exact IH u hu hu' hu''
  · push_neg at H
    refine' ⟨succ w, hw.ne, _⟩
    intro y hy
    rw [lt_succ_iff] at hy
    cases' le_total y x with hxy hxy
    · exact hx _ hxy
    · specialize H y hxy hy
      refine' le_antisymm ((Fin.le_last _).trans _) H
      simp

theorem Positive.not_negative (h : f.Positive) : ¬f.Negative := fun H => by
  suffices (b : Fin (b + 1)) = 0 by simp [Fin.ext_iff, hb.out] at this
  obtain ⟨x, hx⟩ := h.right
  obtain ⟨z, hz⟩ := H.right
  cases' le_or_lt x z with hxz hxz
  · rw [← hx (pred x) (pred_lt _), hz (pred x)]
    exact (pred_lt _).trans_le hxz
  · rw [← hx (pred z), hz (pred z) (pred_lt _)]
    exact (pred_lt _).trans hxz

theorem Negative.not_positive (h : f.Negative) : ¬f.Positive := fun H => by
  suffices (b : Fin (b + 1)) = 0 by simp [Fin.ext_iff, hb.out] at this
  obtain ⟨x, hx⟩ := h.right
  obtain ⟨z, hz⟩ := H.right
  cases' le_or_lt x z with hxz hxz
  · rw [← hx (pred x) (pred_lt _), hz (pred x)]
    exact (pred_lt _).trans_le hxz
  · rw [← hx (pred z), hz (pred z) (pred_lt _)]
    exact (pred_lt _).trans hxz

theorem Positive.sub_negative (hf : f.Positive) (hg : g.Negative) : (f - g).Positive := by
  refine' ⟨_, _⟩
  · rw [Ne.def, sub_eq_zero]
    rintro rfl
    exact hf.not_negative hg
  · obtain ⟨x, hx⟩ := hf.right
    obtain ⟨z, hz⟩ := hg.right
    refine' ⟨min (pred x) (pred z), fun y hy => _⟩
    rw [DigitExpansion.sub_def, sub_eq_zero, hx y (hy.trans _), hz y (hy.trans _), zero_sub,
      Fin.neg_coe_eq_one, eq_comm, difcar_eq_one_iff]
    · refine' ⟨min (pred x) (pred z), hy, _, fun w hw _ => _⟩
      · rw [hx, hz, Fin.lt_iff_val_lt_val]
        · simpa using Nat.pos_of_ne_zero hb.out
        · simp
        · simp
      · rw [hx _ (hw.trans _), hz _ (hw.trans _)]
        · simp
        · simp
        · simp
    · simp
    · simp

theorem Positive.neg_negative (hf : f.Positive) : (-f).Negative := by
  refine' ⟨_, _⟩
  · rw [Ne.def, neg_eq_iff_eq_neg, eq_comm, neg_zero]
    exact hf.left.symm
  · simp_rw [f.neg_def, DigitExpansion.sub_def]
    obtain ⟨x, hx⟩ := hf.right
    obtain ⟨z, hz⟩ : ∃ z, 0 < f z := by
      by_contra!
      refine' hf.left (DigitExpansion.ext _)
      simpa
    refine' ⟨pred x, fun y hy => _⟩
    simp_rw [hx y (hy.trans (pred_lt _)), zero_apply, sub_self, zero_sub]
    rw [neg_eq_iff_eq_neg, eq_comm, Fin.neg_coe_eq_one b, eq_comm, difcar_eq_one_iff]
    refine' ⟨z, _, hz, _⟩
    · contrapose! hz
      rw [hx _ (hz.trans_lt (hy.trans (pred_lt _)))]
    · simp

theorem Negative.sub_positive (hf : f.Negative) (hg : g.Positive) : (f - g).Negative := by
  refine' ⟨_, _⟩
  · rw [Ne.def, sub_eq_zero]
    rintro rfl
    exact hf.not_positive hg
  · obtain ⟨x, hx⟩ := hf.right
    obtain ⟨z, hz⟩ := hg.right
    refine' ⟨pred (min (pred x) (pred z)), fun y hy => _⟩
    rw [DigitExpansion.sub_def, hx y (hy.trans ((pred_lt _).trans _)),
      hz y (hy.trans ((pred_lt _).trans _)), sub_zero, sub_eq_self, difcar_eq_zero_iff]
    · intro w hw hfg
      rw [gt_iff_lt, ← succ_le_iff] at hw
      rw [← succ_lt_succ_iff, succ_pred] at hy
      rcases hw.eq_or_lt with (rfl | hw')
      · rw [hx _ (hy.trans _), hz _ (hy.trans _)] at hfg
        · simp at hfg
        · simp
        · simp
      · refine' ⟨succ y, hw', lt_succ _, _⟩
        rw [hx _ (hy.trans _), hz _ (hy.trans _), Fin.lt_iff_val_lt_val]
        · simpa using Nat.pos_of_ne_zero hb.out
        · simp
        · simp
    · simp
    · simp

theorem Positive.sub_positive (hf : f.Positive) (hg : g.Positive) (hne : f ≠ g) :
    ((f - g).Positive ∧ ∃ x₀, f x₀ > g x₀ ∧ ∀ y < x₀, f y = g y) ∨
      (f - g).Negative ∧ ¬∃ x₀, f x₀ > g x₀ ∧ ∀ y < x₀, f y = g y := by
  obtain ⟨x, hx⟩ : ∃ x, ∀ y ≤ x, f y = 0 ∧ g y = 0 := by
    obtain ⟨x, hx⟩ := hf.right
    obtain ⟨z, hz⟩ := hg.right
    refine' ⟨min (pred x) (pred z), fun y hy => ⟨hx _ (hy.trans_lt _), hz _ (hy.trans_lt _)⟩⟩ <;>
      simp
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, f x₀ ≠ g x₀ ∧ ∀ y < x₀, f y = g y := by
    contrapose! hne
    ext z : 1
    cases' le_total z x with h h
    · rw [(hx _ h).left, (hx _ h).right]
    refine' Succ.rec' _ _ h
    · rw [(hx _ le_rfl).left, (hx _ le_rfl).right]
    intro w _ IH
    by_cases H : f (succ w) = g (succ w)
    · exact H
    · obtain ⟨y, hy, hne⟩ := hne _ H
      refine' absurd (IH _ _ (le_of_lt_succ hy)) hne
      refine' Or.resolve_right (le_total _ _) fun H => hne _
      rw [(hx _ H).left, (hx _ H).right]
  have hd : (∀ z < x₀, difcar f g z = 1) ↔ f x₀ < g x₀ := by
    simp_rw [difcar_eq_one_iff]
    constructor
    · intro IH
      refine' hx₀.left.lt_or_lt.resolve_right (not_lt_of_le _)
      obtain ⟨w, hw, hfgw, IH'⟩ := IH (pred x₀) (pred_lt _)
      cases' (le_of_pred_lt hw).eq_or_lt with hw' hw'
      · subst hw'
        exact hfgw.le
      · exact IH' _ hw' (pred_lt _)
    · intro hfgx z hz
      exact ⟨x₀, hz, hfgx, fun y hy _ => (hx₀.right y hy).le⟩
  have hd' : (∀ z < x₀, difcar f g z = 0) ↔ g x₀ < f x₀ := by
    rw [← not_iff_not]
    push_neg
    simp only [le_iff_lt_or_eq, hx₀.left, ← hd, Ne.def, or_false_iff]
    constructor
    · rintro ⟨z, hz, H⟩
      rw [difcar_eq_zero_iff] at H
      push_neg at H
      obtain ⟨w, _, hfgw, H⟩ := H
      intro k hk
      cases' lt_or_le k w with hwk hwk
      · rw [difcar_eq_one_iff]
        refine' ⟨w, hwk, hfgw, fun y hy _ => _⟩
        cases' lt_or_le z y with hzy hzy
        · exact H _ hy hzy
        · exact (hx₀.right _ (hzy.trans_lt hz)).le
      · exact absurd (hx₀.right _ (hwk.trans_lt hk)) hfgw.ne
    · intro H
      refine' ⟨pred x₀, pred_lt _, _⟩
      rw [H _ (pred_lt _)]
      simp [hb.out]
  refine' hx₀.left.lt_or_lt.symm.imp _ _ <;> intro H
  · refine' ⟨⟨_, x₀, fun y hy => _⟩, ⟨_, H, hx₀.right⟩⟩
    · rwa [Ne.def, sub_eq_zero]
    · rw [← hd'] at H
      simp [DigitExpansion.sub_def, hx₀.right _ hy, H _ hy]
  · refine' ⟨⟨_, x₀, fun y hy => _⟩, _⟩
    · rwa [Ne.def, sub_eq_zero]
    · rw [← hd] at H
      simp only [DigitExpansion.sub_def, hx₀.right _ hy, H _ hy, sub_self, zero_sub]
      rw [neg_eq_iff_eq_neg, eq_comm, Fin.neg_coe_eq_one]
    · push_neg
      intro z hz
      refine' ⟨x₀, _, H.ne⟩
      contrapose! hz
      rcases hz.eq_or_lt with (rfl | hz')
      · exact H.le
      · exact (hx₀.right _ hz').le

theorem Negative.sub_negative (hf : f.Negative) (hg : g.Negative) (hne : f ≠ g) :
    ((f - g).Positive ∧ ∃ x₀, f x₀ > g x₀ ∧ ∀ y < x₀, f y = g y) ∨
      (f - g).Negative ∧ ¬∃ x₀, f x₀ > g x₀ ∧ ∀ y < x₀, f y = g y := by
  -- ideally, use (hf.neg_positive).sub_positive (hg.neg_positive)
  -- because the tactic proof is identical expect for this obtain
  obtain ⟨x, hx⟩ : ∃ x, ∀ y ≤ x, f y = b ∧ g y = b := by
    obtain ⟨x, hx⟩ := hf.right
    obtain ⟨z, hz⟩ := hg.right
    refine' ⟨min (pred x) (pred z), fun y hy => ⟨hx _ (hy.trans_lt _), hz _ (hy.trans_lt _)⟩⟩ <;>
      simp
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, f x₀ ≠ g x₀ ∧ ∀ y < x₀, f y = g y := by
    contrapose! hne
    ext z : 1
    cases' le_total z x with h h
    · rw [(hx _ h).left, (hx _ h).right]
    refine' Succ.rec' _ _ h
    · rw [(hx _ le_rfl).left, (hx _ le_rfl).right]
    intro w _ IH
    by_cases H : f (succ w) = g (succ w)
    · exact H
    · obtain ⟨y, hy, hne⟩ := hne _ H
      refine' absurd (IH _ _ (le_of_lt_succ hy)) hne
      refine' Or.resolve_right (le_total _ _) fun H => hne _
      rw [(hx _ H).left, (hx _ H).right]
  have hd : (∀ z < x₀, difcar f g z = 1) ↔ f x₀ < g x₀ := by
    simp_rw [difcar_eq_one_iff]
    constructor
    · intro IH
      refine' hx₀.left.lt_or_lt.resolve_right (not_lt_of_le _)
      obtain ⟨w, hw, hfgw, IH'⟩ := IH (pred x₀) (pred_lt _)
      cases' (le_of_pred_lt hw).eq_or_lt with hw' hw'
      · subst hw'
        exact hfgw.le
      · exact IH' _ hw' (pred_lt _)
    · intro hfgx z hz
      exact ⟨x₀, hz, hfgx, fun y hy _ => (hx₀.right y hy).le⟩
  have hd' : (∀ z < x₀, difcar f g z = 0) ↔ g x₀ < f x₀ := by
    rw [← not_iff_not]
    push_neg
    simp only [le_iff_lt_or_eq, hx₀.left, ← hd, Ne.def, or_false_iff]
    constructor
    · rintro ⟨z, hz, H⟩
      rw [difcar_eq_zero_iff] at H
      push_neg at H
      obtain ⟨w, _, hfgw, H⟩ := H
      intro k hk
      cases' lt_or_le k w with hwk hwk
      · rw [difcar_eq_one_iff]
        refine' ⟨w, hwk, hfgw, fun y hy _ => _⟩
        cases' lt_or_le z y with hzy hzy
        · exact H _ hy hzy
        · exact (hx₀.right _ (hzy.trans_lt hz)).le
      · exact absurd (hx₀.right _ (hwk.trans_lt hk)) hfgw.ne
    · intro H
      refine' ⟨pred x₀, pred_lt _, _⟩
      rw [H _ (pred_lt _)]
      simp [hb.out]
  refine' hx₀.left.lt_or_lt.symm.imp _ _ <;> intro H
  · refine' ⟨⟨_, x₀, fun y hy => _⟩, ⟨_, H, hx₀.right⟩⟩
    · rwa [Ne.def, sub_eq_zero]
    · rw [← hd'] at H
      simp [DigitExpansion.sub_def, hx₀.right _ hy, H _ hy]
  · refine' ⟨⟨_, x₀, fun y hy => _⟩, _⟩
    · rwa [Ne.def, sub_eq_zero]
    · rw [← hd] at H
      simp only [DigitExpansion.sub_def, hx₀.right _ hy, H _ hy, sub_self, zero_sub]
      rw [neg_eq_iff_eq_neg, Fin.neg_coe_eq_one]
    · push_neg
      intro z hz
      refine' ⟨x₀, _, H.ne⟩
      contrapose! hz
      rcases hz.eq_or_lt with (rfl | hz')
      · exact H.le
      · exact (hx₀.right _ hz').le

lemma Positive.positive_or_eq_sub_single {f : DigitExpansion Z b} (hf : f.Positive) (z : Z) :
    DigitExpansion.Positive (f - single z (f z)) ∨ f = single z (f z) := by
  obtain ⟨x, xpos, hx⟩ := hf.exists_least_pos
  rcases lt_or_le z x with hz|hz
  · simp [hx _ hz, hf]
  rcases eq_or_ne (f z) 0 with hz'|hz'
  · simp [hz', hf]
  by_cases H : ∃ y > x, 0 < f y
  · obtain ⟨y, hy, ypos⟩ := H
    refine Or.inl ⟨?_, x, ?_⟩
    · rw [FunLike.ne_iff]
      rcases eq_or_ne z y with rfl|hy'
      · refine ⟨x, ?_⟩
        simp only [DigitExpansion.sub_def, single_apply_of_ne _ _ _ hy.ne', sub_zero,
          zero_apply, ne_eq]
        rw [difcar_eq_zero_iff.mpr]
        · simpa using xpos.ne'
        intro w _ hw'
        have : w = z := by
          contrapose! hw'
          simp [single_apply_of_ne _ _ _ hw'.symm]
        simp [this] at hw'
      · refine ⟨y, ?_⟩
        simp only [DigitExpansion.sub_def, single_apply_of_ne _ _ _ hy', sub_zero,
          zero_apply, ne_eq]
        rw [difcar_eq_zero_iff.mpr]
        · simpa using ypos.ne'
        intro w _ hw'
        have : w = z := by
          contrapose! hw'
          simp [single_apply_of_ne _ _ _ hw'.symm]
        simp [this] at hw'
    · intro w hw
      simp only [DigitExpansion.sub_def, hx _ hw, single_apply_of_ne _ _ _ (hw.trans_le hz).ne',
        sub_self, zero_sub, neg_eq_zero, difcar_eq_zero_iff, gt_iff_lt]
      intro u _ hu
      have : z = u := by
        contrapose! hu
        simp [single_apply_of_ne _ _ _ hu]
      simp [this] at hu
  · push_neg at H
    simp only [gt_iff_lt, Fin.le_zero_iff] at H
    refine Or.inr ?_
    have : z = x := by
      contrapose! hz'
      rw [H]
      exact lt_of_le_of_ne hz hz'.symm
    subst z
    ext z
    rcases lt_trichotomy z x with hz|rfl|hz
    · simp [single_apply_of_ne _ _ _ hz.ne', hx _ hz]
    · simp
    · simp [single_apply_of_ne _ _ _ hz.ne, H _ hz]

lemma single_add_single_of_lt (z : Z) (k l : Fin (b + 1)) (h : k.val + l.val < (b + 1)) :
    single z k + single z l = single z (k + l) := by
  rw [eq_comm, ← sub_eq_iff_eq_add]
  ext w : 1
  rcases eq_or_ne w z with rfl|hw
  · simp [DigitExpansion.sub_def]
  · simp only [DigitExpansion.sub_def, single_apply_of_ne _ _ _ hw.symm, sub_self, zero_sub,
      neg_eq_zero, difcar_eq_zero_iff, gt_iff_lt]
    intro y _ hy'
    rcases eq_or_ne y z with rfl|hz
    · simp only [single_apply_self, Fin.lt_iff_val_lt_val, Fin.add_def, Nat.mod_eq_of_lt h] at hy'
      simp at hy'
    · simp [single_apply_of_ne _ _ _ hz.symm] at hy'

lemma single_add_single_of_le (z : Z) (k l : Fin (b + 1)) (h : (b + 1) < k.val + l.val) :
    single z k + single z l = single z (k + l) + single (pred z) 1 := by
  rw [eq_comm, ← sub_eq_iff_eq_add, add_sub_assoc, add_comm, eq_comm, ← sub_eq_iff_eq_add]
  ext w : 1
  rcases eq_or_ne w z with rfl|hw
  · simp only [DigitExpansion.sub_def, single_apply_self, sub_add_cancel',
    difcar_single_single_self, sub_zero, ne_eq, pred_eq_iff_isMin, not_isMin, not_false_eq_true,
    single_apply_of_ne, zero_sub]
    rw [difcar_eq_zero_iff.mpr]
    · simp
    intro _ hx
    simp [single_apply_of_ne _ _ _ hx.ne]
  · simp only [DigitExpansion.sub_def, single_apply_of_ne _ _ _ hw.symm, sub_self, zero_sub,
      neg_eq_zero, difcar_eq_zero_iff, gt_iff_lt]
    have hk : k + l < k := by
      rw [Fin.add_lt_left_iff, Fin.lt_iff_val_lt_val, ← Fin.last_sub, Fin.sub_def]
      simp only [Fin.val_last]
      rw [← add_tsub_assoc_of_le l.is_lt.le, add_comm, add_tsub_assoc_of_le l.is_le,
          Nat.add_mod_left, Nat.mod_eq_of_lt (tsub_lt_of_lt (Nat.lt_succ_self _)),
          tsub_lt_iff_left l.is_le, add_comm]
      exact (h.trans' (Nat.lt_succ_self _))
    rcases eq_or_ne w (pred z) with rfl|hw'
    · simp only [single_apply_self, sub_zero]
      rw [difcar_pred_eq_zero, difcar_pred_eq_one, neg_zero, sub_self]
      · simp only [ne_eq, pred_eq_iff_isMin, not_isMin, not_false_eq_true, single_apply_of_ne,
        single_apply_self]
        contrapose! h
        simp only [Fin.le_zero_iff] at h
        simp [h]
      · simp only [single_apply_self]
        exact hk
    · rw [single_apply_of_ne _ _ _ hw'.symm, sub_self, zero_sub, neg_inj, eq_comm,
          difcar_eq_zero_iff.mpr]
      · rcases lt_or_le w z with hwz|hwz
        · rw [(difcar_single_single_of_lt_eq_zero_iff_le hwz).mpr]
          exact hk.le
        · rw [difcar_single_single_eq_zero_of_le _ _ hwz]
      · intros x hx hx'
        have : x = z := by
          contrapose! hx'
          simp [single_apply_of_ne _ _ _ hx'.symm]
        subst x
        refine ⟨pred z, pred_lt _, lt_of_le_of_ne (le_pred_of_lt hx) hw', ?_⟩
        simp only [single_apply_of_ne _ _ _ (pred_lt _).ne', single_apply_self]
        refine lt_of_le_of_ne (Fin.zero_le _) ?_
        simp [hb.out]

lemma nsmul_single_eq_single (z : Z) (n : Fin (b + 1)) :
    n.val • single z 1 = single z n := by
  induction' hn' : n.val with n' hn generalizing n
  · simp [zero_nsmul, Fin.ext_iff, hn', eq_comm]
  have : 1 < b + 1 := Nat.succ_lt_succ (Nat.pos_of_ne_zero hb.out)
  have H : ((n - 1 : Fin (b + 1)) : ℕ) = n' := by
    rw [Fin.coe_sub, hn', Fin.val_one', Nat.mod_eq_of_lt this]
    suffices n' < b + 1 by
      simp [Nat.succ_eq_add_one, add_right_comm, add_assoc, this]
    exact n.is_lt.trans_le' (hn'.ge.trans' (Nat.le_succ _))
  rw [succ_nsmul, hn _ H, eq_comm, ← sub_eq_iff_eq_add]
  ext x : 1
  rcases eq_or_ne x z with rfl|hx
  · simp [DigitExpansion.sub_def]
  · simp only [DigitExpansion.sub_def, single_apply_of_ne _ _ _ hx.symm, sub_self, zero_sub,
    neg_eq_zero, difcar_eq_zero_iff, gt_iff_lt]
    intro y _ hy'
    rcases eq_or_ne y z with rfl|hz
    · simp [Fin.lt_iff_val_lt_val, H, hn', (Nat.le_succ _).not_lt] at hy'
    · simp [single_apply_of_ne _ _ _ hz.symm] at hy'

lemma base_nsmul_single_one_succ_one_eq_single (z : Z) :
    (b + 1) • single (succ z) (1 : Fin (b + 1)) = single z 1 := by
  have : b • single (succ z) 1 = (b : Fin (b + 1)).val • single (succ z) (1 : Fin (b + 1)) := by
    congr
    simp
  rw [succ_nsmul, this, nsmul_single_eq_single _ b, eq_comm, ← sub_eq_iff_eq_add]
  ext x : 1
  rcases eq_or_ne x (succ z) with rfl|hx
  · simp only [Fin.cast_nat_eq_last, DigitExpansion.sub_def, ne_eq, pred_eq_iff_isMin, not_isMin,
    not_false_eq_true, single_apply_of_ne, single_apply_self, zero_sub, Fin.neg_last, sub_eq_self,
    difcar_eq_zero_iff, gt_iff_lt, (lt_succ z).ne]
    intro y hy
    simp [single_apply_of_ne _ _ _ hy.ne]
  · rcases eq_or_ne x z with rfl|hz
    · simp only [Fin.cast_nat_eq_last, DigitExpansion.sub_def, single_apply_self,
      single_apply_of_ne _ _ _ hx.symm, sub_zero]
      rw [difcar_eq_one_iff.mpr]
      · simp
      · refine ⟨succ x, lt_succ _, ?_, ?_⟩
        · simp [Fin.lt_iff_val_lt_val, Nat.pos_of_ne_zero hb.out,
                single_apply_of_ne _ _ _ (lt_succ _).ne]
        · simp only [lt_succ_iff]
          intro _ h h'
          exact absurd h h'.not_le
    · simp only [Fin.cast_nat_eq_last, DigitExpansion.sub_def, ne_eq, hz.symm, not_false_eq_true,
      single_apply_of_ne, hx.symm, sub_self, zero_sub, neg_eq_zero, difcar_eq_zero_iff]
      intro y hy hy'
      have : y = succ z := by
        contrapose! hy'
        simp [single_apply_of_ne _ _ _ hy'.symm]
      subst y
      refine ⟨z, lt_succ _, ?_, ?_⟩
      · contrapose! hy
        rw [succ_le_iff]
        exact lt_of_le_of_ne hy hz.symm
      · simp [single_apply_of_ne _ _ _ (pred_lt z).ne']

lemma base_nsmul_single_succ_one_eq_single (z : Z) (n : Fin (b + 1)) :
    (b + 1) • single (succ z) n = single z n := by
  rw [succ_nsmul, ← nsmul_single_eq_single, nsmul_left_comm, ← nsmul_add,
      ← nsmul_single_eq_single z, ← base_nsmul_single_one_succ_one_eq_single z, succ_nsmul]

lemma shift_sub (f g : DigitExpansion Z b) : shift (f - g) = shift f - shift g := by
  ext z : 1
  simp only [shift_apply, DigitExpansion.sub_def, sub_right_inj]
  rcases difcar_eq_zero_or_one f g (pred z) with hd|hd
  · rw [hd, eq_comm]
    rw [difcar_eq_zero_iff] at hd ⊢
    simp only [gt_iff_lt, shift_apply]
    intro x hx hx'
    obtain ⟨y, hy, hy', hy''⟩ := hd (pred x) (pred_lt_pred hx) hx'
    exact ⟨succ y, by simpa using succ_lt_succ hy, by simpa using succ_lt_succ hy', by simp [hy'']⟩
  · rw [hd, eq_comm]
    rw [difcar_eq_one_iff] at hd ⊢
    obtain ⟨x, hx, hx', hx''⟩ := hd
    refine ⟨succ x, by simpa using succ_lt_succ hx, by simp [hx'], fun y hy hy' ↦ ?_⟩
    simp only [shift_apply]
    exact hx'' _ (by simpa using hy) (pred_lt_pred hy')

lemma shift_neg (f : DigitExpansion Z b) : shift (-f) = - shift f := by
  rw [← zero_sub, shift_sub, shift_zero, zero_sub]

lemma shift_add (f g : DigitExpansion Z b) : shift (f + g) = shift f + shift g := by
  rw [← sub_neg_eq_add, shift_sub, shift_neg, sub_neg_eq_add]

lemma shift_nsmul_comm (f : DigitExpansion Z b) (n : ℕ) : shift (n • f) = n • shift f := by
  induction' n with n IH
  · simp [zero_nsmul]
  · rw [succ_nsmul, shift_add, IH, succ_nsmul]

end DigitExpansion
