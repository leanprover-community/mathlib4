/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Positivity


/-!
# Defining reals without the use of rationals

* [Defining reals without the use of rationals][debruijn1976]

-/


section S01

structure FormalSeries (Z : Type*) [LT Z] (b : ℕ) where
  -- b will the base - 1
  toFun : Z → Fin (b + 1)
  bounded' : ¬∃ i₀, ∀ i > i₀, toFun i = b

namespace FormalSeries

-- we can treat it like a function
instance funLike (Z : Type*) [LT Z] (b : ℕ) : FunLike (FormalSeries Z b) Z fun _ => Fin (b + 1)
    where
  coe := FormalSeries.toFun
  coe_injective' := by rintro ⟨⟩ ⟨⟩; simp


variable {Z : Type*} [LT Z] {b : ℕ} (f g : FormalSeries Z b) (i : Z)

-- extensional equality
@[ext]
theorem ext (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h

@[simp]
theorem toFun_apply : f.toFun i = f i :=
  rfl

@[simp]
theorem mk_apply (f : Z → Fin (b + 1)) (hf) : (⟨f, hf⟩ : FormalSeries Z b) i = f i :=
  rfl

end FormalSeries

end S01

-- section 2 defines notation
open Order

-- Z is the set of all integers
-- variable {Z : Type*} [LT Z] {b : ℕ}
  -- [Nonempty Z] [ConditionallyCompleteLinearOrder Z] [NoMaxOrder Z]
  -- [NoMinOrder Z] [SuccOrder Z] [PredOrder Z] [IsSuccArchimedean Z]
  -- b is a fixed integer > 1
  -- [hb : Fact (b > 0)]

-- because we use the base - 1
-- If P and Q are sets then Q^P is the set of all mappings of P into Q

-- TODO
@[simp]
theorem Nat.mod_succ (n : ℕ) : n % n.succ = n :=
  Nat.mod_eq_of_lt (Nat.lt_succ_self _)

instance base_nontrivial {b : ℕ} [hb : Fact (0 < b)] : Nontrivial (Fin (b + 1)) :=
  ⟨⟨0, 1, by
      have : 1 < b + 1 := Nat.succ_lt_succ_iff.mpr hb.out
      simp [Fin.ext_iff, Fin.val_one', Nat.mod_eq_of_lt this]⟩⟩

theorem FormalSeries.exists_bounded {Z : Type*} [LT Z] {b : ℕ} (f : FormalSeries Z b) (z : Z) :
    ∃ x > z, f x < b := by
  have := f.bounded'
  push_neg at this
  refine' (this z).imp fun x => And.imp_right _
  cases' (Fin.le_last (f x)).eq_or_lt with h h
  · simp [h, Fin.ext_iff]
  · intro
    simpa [Fin.lt_iff_val_lt_val] using h

instance {Z : Type*} [Preorder Z] [SuccOrder Z] [NoMaxOrder Z] {b : ℕ} [hb : Fact (0 < b)] :
    Zero (FormalSeries Z b) :=
  ⟨{  toFun := (0 : Z → Fin (b + 1))
      bounded' := by
        push_neg
        intro x
        refine' ⟨succ x, lt_succ _, _⟩
        simp [Fin.ext_iff, LT.lt.ne hb.out] }⟩

@[simp]
theorem zero_apply {Z : Type*} [Preorder Z] [SuccOrder Z] [NoMaxOrder Z] {b : ℕ} [Fact (0 < b)]
    (z : Z) : (0 : FormalSeries Z b) z = 0 :=
  rfl

open scoped Classical

noncomputable section

section S03

variable {Z : Type*} [LT Z] {b : ℕ} (f g : FormalSeries Z b)

def difcar : Z → Fin (b + 1) := fun z =>
  if ∃ x > z, f x < g x ∧ ∀ y < x, z < y → f y ≤ g y then 1 else 0

variable {f g}

theorem difcar_eq_one_iff [Fact (0 < b)] {z : Z} :
    difcar f g z = 1 ↔ ∃ x > z, f x < g x ∧ ∀ y < x, z < y → f y ≤ g y :=
  by
  dsimp [difcar]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun H => absurd H zero_ne_one, fun H => absurd H h⟩

theorem difcar_eq_zero_iff [Fact (0 < b)] {z : Z} :
    difcar f g z = 0 ↔ ∀ x > z, f x < g x → ∃ y : Z, y < x ∧ z < y ∧ g y < f y :=
  by
  dsimp [difcar]
  split_ifs with h
  · refine' ⟨fun H => absurd H.symm zero_ne_one, fun _ => absurd h _⟩
    push_neg
    assumption
  · push_neg at h
    exact ⟨fun _ => h, fun _ => rfl⟩

variable (f g)

theorem difcar_eq_zero_or_one [Fact (0 < b)] (x : Z) : difcar f g x = 0 ∨ difcar f g x = 1 :=
  by
  rw [difcar_eq_zero_iff, difcar_eq_one_iff]
  refine' (em' _).imp_left _
  push_neg
  exact id

theorem difcar_le_one [Fact (0 < b)] (x : Z) : difcar f g x ≤ 1 := by
  cases' difcar_eq_zero_or_one f g x with h h <;> simp [h]

variable {Z : Type*} [PartialOrder Z] [SuccOrder Z] [NoMaxOrder Z] [PredOrder Z] [NoMinOrder Z]
  {b : ℕ}
variable {f g : FormalSeries Z b}

theorem difcar_pred_eq_one [Fact (0 < b)] {z : Z} (h : f z < g z) : difcar f g (pred z) = 1 :=
  by
  rw [difcar_eq_one_iff]
  refine' ⟨z, pred_lt _, h, fun y hyz hy => _⟩
  rw [pred_lt_iff_eq_or_lt_of_not_isMin] at hy
  · rcases hy with (rfl | hy)
    · exact absurd hyz (lt_irrefl _)
    · exact absurd hyz hy.not_lt
  · exact not_isMin z

theorem difcar_pred_eq_zero [Fact (0 < b)] {z : Z} (h : g z < f z) : difcar f g (pred z) = 0 :=
  by
  rw [difcar_eq_zero_iff]
  intro x hx hfgx
  rcases(le_of_pred_lt hx).eq_or_lt with (rfl | hz)
  · exact absurd hfgx h.not_lt
  exact ⟨z, hz, pred_lt _, h⟩

theorem difcar_pred_eq_difcar [Fact (0 < b)] {z : Z} (h : f z = g z) : difcar f g (pred z) = difcar f g z :=
  by
  cases' difcar_eq_zero_or_one f g z with hz hz
  · rw [hz]
    rw [difcar_eq_zero_iff] at hz ⊢
    intro x hx hfgx
    rcases(le_of_pred_lt hx).eq_or_lt with (rfl | hzx)
    · exact absurd h hfgx.ne
    obtain ⟨y, hy, hyz, hfgy⟩ := hz x hzx hfgx
    exact ⟨y, hy, (pred_lt _).trans hyz, hfgy⟩
  · rw [hz]
    rw [difcar_eq_one_iff] at hz ⊢
    obtain ⟨x, hzx, hfgx, hz⟩ := hz
    refine' ⟨x, (pred_lt _).trans hzx, hfgx, fun y hy hyz => _⟩
    rcases(le_of_pred_lt hyz).eq_or_lt with (rfl | hyz')
    · exact h.le
    exact hz y hy hyz'

@[simp]
theorem difcar_zero_right [Fact (0 < b)] (f : FormalSeries Z b) (z : Z) : difcar f 0 z = 0 := by
  simp [difcar_eq_zero_iff]

@[simp]
theorem difcar_self [Fact (0 < b)] (f : FormalSeries Z b) (z : Z) : difcar f f z = 0 := by
  simp [difcar_eq_zero_iff]

def subAux (x : Z) : Fin (b + 1) :=
  f x - g x - difcar f g x

theorem pred_min {Z : Type*} [LinearOrder Z] [PredOrder Z] (x y : Z) :
    pred (min x y) = min (pred x) (pred y) := by
  cases' le_total x y with h h
  · rw [min_eq_left h, min_eq_left]
    simp [h]
  · rw [min_eq_right h, min_eq_right]
    simp [h]

theorem pred_max {Z : Type*} [LinearOrder Z] [PredOrder Z] (x y : Z) :
    pred (max x y) = max (pred x) (pred y) := by
  cases' le_total x y with h h
  · rw [max_eq_right h, max_eq_right]
    simp [h]
  · rw [max_eq_left h, max_eq_left]
    simp [h]

theorem succ_min {Z : Type*} [LinearOrder Z] [SuccOrder Z] (x y : Z) :
    succ (min x y) = min (succ x) (succ y) := by
  cases' le_total x y with h h
  · rw [min_eq_left h, min_eq_left]
    simp [h]
  · rw [min_eq_right h, min_eq_right]
    simp [h]

theorem succ_max {Z : Type*} [LinearOrder Z] [SuccOrder Z] (x y : Z) :
    succ (max x y) = max (succ x) (succ y) := by
  cases' le_total x y with h h
  · rw [max_eq_right h, max_eq_right]
    simp [h]
  · rw [max_eq_left h, max_eq_left]
    simp [h]

namespace Fin

theorem add_one_le_of_lt {n : ℕ} {a b : Fin (n + 1)} (h : a < b) : a + 1 ≤ b :=
  by
  cases' a with a ha
  cases' b with b hb
  cases n
  · simp only [Nat.zero_eq, zero_add, Nat.lt_one_iff] at ha hb
    simp [ha, hb]
  simp only [le_iff_val_le_val, val_add, lt_iff_val_lt_val, val_mk, val_one] at h ⊢
  rwa [Nat.mod_eq_of_lt, Nat.succ_le_iff]
  rw [Nat.succ_lt_succ_iff]
  exact h.trans_le (Nat.le_of_lt_succ hb)

theorem exists_eq_add_of_le {n : ℕ} {a b : Fin n} (h : a ≤ b) : ∃ k ≤ b, b = a + k :=
  by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (b : ℕ) = a + k := Nat.exists_eq_add_of_le h
  have hkb : k ≤ b := le_add_self.trans hk.ge
  refine' ⟨⟨k, hkb.trans_lt b.is_lt⟩, hkb, _⟩
  simp [Fin.ext_iff, Fin.val_add, ← hk, Nat.mod_eq_of_lt b.is_lt]

theorem exists_eq_add_of_lt {n : ℕ} {a b : Fin (n + 1)} (h : a < b) :
    ∃ k < b, k + 1 ≤ b ∧ b = a + k + 1 := by
  cases n
  · cases' a with a ha
    cases' b with b hb
    simp only [Nat.zero_eq, zero_add, Nat.lt_one_iff] at ha hb
    simp [ha, hb] at h
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (b : ℕ) = a + k + 1 := Nat.exists_eq_add_of_lt h
  have hkb : k < b := by
    rw [hk, add_comm _ k, Nat.lt_succ_iff]
    exact le_self_add
  refine' ⟨⟨k, hkb.trans b.is_lt⟩, hkb, _, _⟩
  · rw [Fin.le_iff_val_le_val, Fin.val_add_one]
    split_ifs <;> simp [Nat.succ_le_iff, hkb]
  simp [Fin.ext_iff, Fin.val_add, ← hk, Nat.mod_eq_of_lt b.is_lt]

@[simp]
theorem neg_last (n : ℕ) : -Fin.last n = 1 := by simp [neg_eq_iff_add_eq_zero]

instance charP (n : ℕ) : CharP (Fin (n + 1)) (n + 1) where
    cast_eq_zero_iff' := by
      simp [Fin.eq_iff_veq, Nat.dvd_iff_mod_eq_zero]

@[simp]
theorem nat_cast_add_one_eq_zero (n : ℕ) : (n : Fin (n + 1)) + 1 = 0 := by
  rw [←Nat.cast_add_one, CharP.cast_eq_zero]

@[simp]
theorem neg_coe_eq_one (n : ℕ) : -(n : Fin (n + 1)) = 1 := by
  simp [neg_eq_iff_add_eq_zero]

end Fin

instance {Z : Type*} [PartialOrder Z] [SuccOrder Z] [NoMaxOrder Z] [PredOrder Z] [NoMinOrder Z]
    [IsSuccArchimedean Z] {b : ℕ} [hb : Fact (0 < b)] :
    Sub (FormalSeries Z b) :=
  ⟨fun f g =>
    { toFun := fun x => f x - g x - difcar f g x
      bounded' := by
        rintro ⟨x, hx⟩
        obtain ⟨w, hw, hfgw⟩ : ∃ w ≥ x, difcar f g w = 0 :=
          by
          cases' difcar_eq_zero_or_one f g x with px px
          · exact ⟨x, le_rfl, px⟩
          · rw [difcar_eq_one_iff] at px
            obtain ⟨y, hxy, hfgy, _⟩ := px
            have := hx y hxy
            rw [sub_eq_iff_eq_add] at this
            refine' ⟨y, le_of_lt hxy, _⟩
            refine' Or.resolve_right (difcar_eq_zero_or_one _ _ _) fun H => _
            rw [H, ← Nat.cast_add_one, ZMod.nat_cast_self, sub_eq_zero] at this
            exact absurd this hfgy.ne
        suffices ∀ z > w, difcar f g z = 0 ∧ f z = b
          by
          obtain ⟨z, hwz, hz⟩ := f.exists_bounded w
          exact not_le_of_lt hz (this _ hwz).right.ge
        suffices ∀ z > x, difcar f g (pred z) = 0 → f z = b ∧ g z = 0 ∧ difcar f g z = 0
          by
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
        · simp [difcar_pred_eq_one H, ne_of_gt hb.out] at hfgz
        · simp [← difcar_pred_eq_difcar H, H, hfgz, Fin.ext_iff, ne_of_gt hb.out] at hx
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

variable {Z : Type*} [PartialOrder Z] [SuccOrder Z] [NoMaxOrder Z] [PredOrder Z] [NoMinOrder Z]
    [IsSuccArchimedean Z] {b : ℕ} [hb : Fact (0 < b)]
variable (f g : FormalSeries Z b)

-- /-- A recursor that splits `n` into a multiple of `b` and a remainder `r` -/
-- def Int.mulAddCases {C : ℤ → Sort _} (n b : ℤ) (hb : b ≠ 0)
--     (hm : ∀ (k : ℤ), ∀ r < |b|, C (b * k + r)) : C n :=
--   cast (congr_arg _ (Int.div_add_mod n b)) (hm (n / b) (n % b) (Int.emod_lt _ hb))

-- /-- Recursion principle based on the div and modulus decomposition against some base `b : ℤ`:
-- given maps `C k → C (k + b)` and `C k → C (k - b)` for each `k`,
-- and the construction of `C r` for all `r < |b|`, one can construct `C n` for any `n : ℤ`.  -/
-- @[elab_as_elim]
-- def addSubBaseRec {C : ℤ → Sort _} (n b : ℤ) (hb : b ≠ 0) (hr : ∀ r < |b|, C r)
--     (hp : ∀ k, C k → C (k + b)) (hn : ∀ k, C k → C (k - b)) : C n :=
--   Int.mulAddCases _ _ hb fun z =>
--     Int.inductionOn' z 0 (fun r hrb => cast (congr_arg _ (by ring)) (hr r hrb))
--       (fun k kpos IH r hrb => cast (congr_arg _ (by ring)) (hp _ (IH r hrb))) fun k kneg IH r hrb =>
--       cast (congr_arg _ (by ring)) (hn _ (IH r hrb))

theorem Int.neg_mod {a b : ℤ} : -a % b = (b - a) % b := by
  rw [← Int.add_emod_self_left, sub_eq_add_neg]

protected theorem FormalSeries.sub_def (x : Z) : (f - g) x = f x - g x - difcar f g x :=
  rfl

theorem coe_sub (z : Z) :
    ((f - g) z : ℤ) = f z - g z - difcar f g z + (b + 1) * difcar f g (pred z) :=
  by
  simp_rw [f.sub_def, Fin.coe_sub]
  simp only [Nat.cast_sub, (g z).is_lt.le, (difcar f g z).is_lt.le, Nat.mod_add_mod,
    Int.coe_nat_mod, Nat.cast_add, Nat.cast_one]
  rw [add_sub, add_sub, add_comm, ← add_sub, Int.add_emod_self_left, add_comm, ← add_sub, ← add_sub,
    Int.add_emod_self_left]
  cases b
  · exact absurd hb.out (lt_irrefl _)
  rw [← Nat.cast_succ]
  rcases lt_trichotomy (f z) (g z) with (h | h | h)
  any_goals have h' := h; rw [Fin.lt_iff_val_lt_val] at h'
  · simp only [difcar_pred_eq_one h, Fin.val_one, Nat.cast_one, mul_one]
    rw [← Int.add_emod_self, Int.emod_eq_of_lt]
    · rw [sub_add, sub_sub, le_sub_comm, sub_zero, add_sub, tsub_le_iff_right, ← Nat.cast_add, ←
        Nat.cast_add, Int.ofNat_le]
      exact
        le_add_self.trans' (add_le_add (g z).is_le (Fin.le_iff_val_le_val.mp (difcar_le_one _ _ _)))
    · simp only [sub_lt_comm, add_lt_iff_neg_right, tsub_zero]
      refine' (Int.sub_le_self _ _).trans_lt _ <;> simp [h]
  · simp only [h, difcar_pred_eq_difcar h, Int.neg_mod, sub_self, zero_sub]
    cases' difcar_eq_zero_or_one f g z with hd hd
    · simp [hd, Int.emod_self]
    · rw [hd, Fin.val_one, ← Nat.cast_sub, ← Int.coe_nat_mod] <;> simp [Nat.succ_le_succ_iff]
  · simp only [difcar_pred_eq_zero h, Fin.val_zero, Nat.cast_zero, MulZeroClass.mul_zero, add_zero]
    rw [← Nat.cast_sub h'.le, Int.emod_eq_of_lt]
    · rw [sub_nonneg, Nat.cast_le, le_tsub_iff_right h'.le, add_comm]
      cases' difcar_eq_zero_or_one f g z with hd hd <;> simp [hd, Nat.succ_le_iff, h, h.le]
    · rw [← Nat.cast_sub, Int.ofNat_lt]
      · exact tsub_lt_of_lt (tsub_lt_of_lt (f z).is_lt)
      · refine' (Fin.le_iff_val_le_val.mp (difcar_le_one _ _ _)).trans _
        rw [Fin.val_one, Nat.succ_le_iff, tsub_pos_iff_lt]
        exact h'

protected theorem FormalSeries.sub_zero (f : FormalSeries Z b) : f - 0 = f := by
  ext; simp [FormalSeries.sub_def]

protected theorem FormalSeries.sub_self (f : FormalSeries Z b) : f - f = 0 := by
  ext; simp [FormalSeries.sub_def]

end S03

section S04

variable {Z : Type*} [PartialOrder Z] [SuccOrder Z] [NoMaxOrder Z] [PredOrder Z] [NoMinOrder Z]
    [IsSuccArchimedean Z] {b : ℕ} [hb : Fact (0 < b)]

-- set_option pp.coercions false
-- The paper mistakenly says `f - (g - h) = h - (f - g)`.
protected theorem FormalSeries.sub_sub_comm (f g h : FormalSeries Z b) :
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
    · exact absurd hb.out (lt_irrefl _)
    cases' difcar_eq_zero_or_one g h z with hp0 hp0 <;>
        cases' difcar_eq_zero_or_one f s z with hq0 hq0 <;>
      norm_num [hp0, hq0]
  have hpq1' : ∀ z, |(p' z : ℤ) - q' z| ≤ 1 := by
    intro z
    rw [hp', hq']
    cases b
    · exact absurd hb.out (lt_irrefl _)
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
      suffices (b : ℤ) + 1 < 2 by norm_num [← lt_sub_iff_add_lt, ne_of_gt hb.out] at this
      exact htd.left.trans_le (le_of_abs_le (hr2 _))
    · rw [← hl, abs_lt, mul_neg, sub_neg_eq_add, mul_two, ← add_assoc, add_lt_iff_neg_right] at htd
      suffices (b : ℤ) + 1 < 2 by norm_num [← lt_sub_iff_add_lt, ne_of_gt hb.out] at this
      rw [← sub_neg_eq_add _ ((b : ℤ) + 1), ← sub_neg_eq_add _ ((b : ℤ) + 1), sub_lt_iff_lt_add,
        zero_add, lt_neg] at htd
      exact htd.right.trans_le ((neg_le_abs_self _).trans (hr2 _))
    · rw [hr, abs_lt, mul_two, ← sub_sub, sub_lt_iff_lt_add, lt_sub_comm, sub_neg_eq_add,
        sub_add_cancel] at htd
      suffices (b : ℤ) + 1 < 2 by norm_num [← lt_sub_iff_add_lt, ne_of_gt hb.out] at this
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
    suffices ∀ y > z, (t' y : ℤ) = b
      by
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
    suffices ∀ y > z, (t y : ℤ) = b
      by
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

end S04

section S05

instance {Z : Type*} [PartialOrder Z] [SuccOrder Z] [NoMaxOrder Z] [PredOrder Z] [NoMinOrder Z]
    [IsSuccArchimedean Z] {b : ℕ} [Fact (0 < b)] :
    Add (FormalSeries Z b) :=
  ⟨fun f g => f - (0 - g)⟩

variable {Z : Type*} [PartialOrder Z] [SuccOrder Z] [NoMaxOrder Z] [PredOrder Z] [NoMinOrder Z]
    [IsSuccArchimedean Z] {b : ℕ} [hb : Fact (0 < b)]
variable (f g : FormalSeries Z b)

-- 5.1
protected theorem FormalSeries.add_def : f + g = f - (0 - g) :=
  rfl

-- (i)
protected theorem FormalSeries.add_zero : f + 0 = f :=
  calc
    f + 0 = f - (0 - 0) := rfl
    _ = f - 0 := by rw [FormalSeries.sub_zero]
    _ = f := FormalSeries.sub_zero _

-- (ii)
protected theorem FormalSeries.add_comm : f + g = g + f :=
  calc
    f + g = f - (0 - g) := rfl
    _ = g - (0 - f) := (FormalSeries.sub_sub_comm _ _ _)
    _ = g + f := rfl

-- (iii)
protected theorem FormalSeries.add_assoc (f g h : FormalSeries Z b) : f + (g + h) = f + g + h :=
  calc
    f + (g + h) = f + (h + g) := by rw [g.add_comm]
    _ = f - (0 - (h - (0 - g))) := by simp_rw [FormalSeries.add_def]
    _ = f - (0 - g - (h - 0)) := by rw [FormalSeries.sub_sub_comm 0, FormalSeries.sub_zero]
    _ = f - (0 - g - h) := by rw [FormalSeries.sub_zero]
    _ = h - (0 - g - f) := (FormalSeries.sub_sub_comm _ _ _)
    _ = h - (0 - g - (f - 0)) := by rw [FormalSeries.sub_zero]
    _ = h - (0 - (f - (0 - g))) := by rw [FormalSeries.sub_sub_comm 0, FormalSeries.sub_zero]
    _ = h + (f + g) := by simp_rw [FormalSeries.add_def]
    _ = f + g + h := FormalSeries.add_comm _ _

-- (iv)
protected theorem FormalSeries.add_sub_cancel : g + (f - g) = f :=
  calc
    g + (f - g) = g - (0 - (f - g)) := FormalSeries.add_def _ _
    _ = g - (g - (f - 0)) := by rw [FormalSeries.sub_sub_comm g f 0]
    _ = g - (g - f) := by rw [FormalSeries.sub_zero]
    _ = f - (g - g) := (FormalSeries.sub_sub_comm _ _ _)
    _ = f - 0 := by rw [FormalSeries.sub_self]
    _ = f := FormalSeries.sub_zero _

instance : Neg (FormalSeries Z b) :=
  ⟨fun f => 0 - f⟩

protected theorem FormalSeries.neg_def : -f = 0 - f :=
  rfl

instance {Z : Type*} [PartialOrder Z] [SuccOrder Z] [NoMaxOrder Z] [PredOrder Z] [NoMinOrder Z]
    [IsSuccArchimedean Z] {b : ℕ} [Fact (0 < b)] : AddCommGroup (FormalSeries Z b) where
  add := (· + ·)
  add_assoc _ _ _ := (FormalSeries.add_assoc _ _ _).symm
  zero := 0
  zero_add _ := by simp_rw [FormalSeries.add_def, FormalSeries.sub_sub_comm, FormalSeries.sub_zero]
  add_zero := FormalSeries.add_zero
  neg f := -f
  sub f g := f - g
  sub_eq_add_neg f g := by
    simp [g.neg_def, f.add_def, FormalSeries.sub_sub_comm 0, FormalSeries.sub_zero]
  add_left_neg f := by
    rw [f.neg_def, FormalSeries.add_def]
    simp [FormalSeries.sub_sub_comm,
      FormalSeries.sub_sub_comm 0 0 f, FormalSeries.sub_zero, FormalSeries.sub_self]
  add_comm _ _ := FormalSeries.add_comm _ _

end S05

section S06

@[elab_as_elim]
theorem Succ.rec' {Z : Type*} [LinearOrder Z] [SuccOrder Z] [IsSuccArchimedean Z] {P : Z → Prop}
    {m : Z} (h0 : P m) (h1 : ∀ n, m ≤ n → (∀ k, m ≤ k → k ≤ n → P k) → P (succ n)) ⦃n : Z⦄
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
    · exact IH _ hmk (le_of_lt_succ hkn')

namespace FormalSeries

protected def Positive {Z : Type*} [Preorder Z] [SuccOrder Z] [NoMaxOrder Z] {b : ℕ} [Fact (0 < b)]
    (f : FormalSeries Z b) : Prop :=
  f ≠ 0 ∧ ∃ x, ∀ y < x, f y = 0

protected def Negative {Z : Type*} [Preorder Z] [SuccOrder Z] [NoMaxOrder Z] {b : ℕ} [Fact (0 < b)]
    (f : FormalSeries Z b) : Prop :=
  f ≠ 0 ∧ ∃ x, ∀ y < x, f y = b

theorem not_positive_zero {Z : Type*} [Preorder Z] [SuccOrder Z] [NoMaxOrder Z] {b : ℕ}
    [Fact (0 < b)] : ¬FormalSeries.Positive (0 : FormalSeries Z b) := fun H => H.left rfl

theorem not_negative_zero {Z : Type*} [Preorder Z] [SuccOrder Z] [NoMaxOrder Z] {b : ℕ}
    [Fact (0 < b)] : ¬FormalSeries.Negative (0 : FormalSeries Z b) := fun H => H.left rfl

-- 6.1 defined by separate cases to provide for separate lemmas
-- (i)
theorem Negative.neg_positive {Z : Type*} [PartialOrder Z] [SuccOrder Z] [NoMaxOrder Z]
    [PredOrder Z] [NoMinOrder Z] [IsSuccArchimedean Z] {b : ℕ} [hb : Fact (0 < b)]
    {f : FormalSeries Z b} (hf : f.Negative) : (-f).Positive := by
  refine' ⟨_, _⟩
  · rw [Ne.def, neg_eq_iff_eq_neg, eq_comm, neg_zero]
    exact hf.left.symm
  · simp_rw [f.neg_def, FormalSeries.sub_def]
    obtain ⟨x, hx⟩ := hf.right
    refine' ⟨pred x, fun y hy => _⟩
    simp_rw [hx y (hy.trans (pred_lt _)), zero_apply, zero_sub, sub_eq_zero]
    rw [Fin.neg_coe_eq_one b, eq_comm, difcar_eq_one_iff]
    refine' ⟨pred x, hy, _⟩
    simpa [hx (pred x) (pred_lt _), Fin.lt_iff_val_lt_val] using hb.out

variable {Z : Type*} [LinearOrder Z] [SuccOrder Z] [NoMaxOrder Z] [PredOrder Z] [NoMinOrder Z]
    [IsSuccArchimedean Z] {b : ℕ} [hb : Fact (0 < b)]
variable {f g : FormalSeries Z b}

theorem Positive.exists_least_pos (hf : f.Positive) : ∃ x, 0 < f x ∧ ∀ y < x, f y = 0 := by
  obtain ⟨x, hx⟩ : ∃ x, ∀ y ≤ x, f y = 0 :=
    by
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

theorem Positive.not_negative (h : f.Positive) : ¬f.Negative := fun H => by
  suffices (b : Fin (b + 1)) = 0 by simp [Fin.ext_iff, ne_of_gt hb.out] at this
  obtain ⟨x, hx⟩ := h.right
  obtain ⟨z, hz⟩ := H.right
  cases' le_or_lt x z with hxz hxz
  · rw [← hx (pred x) (pred_lt _), hz (pred x)]
    exact (pred_lt _).trans_le hxz
  · rw [← hx (pred z), hz (pred z) (pred_lt _)]
    exact (pred_lt _).trans hxz

theorem Negative.not_positive (h : f.Negative) : ¬f.Positive := fun H => by
  suffices (b : Fin (b + 1)) = 0 by simp [Fin.ext_iff, ne_of_gt hb.out] at this
  obtain ⟨x, hx⟩ := h.right
  obtain ⟨z, hz⟩ := H.right
  cases' le_or_lt x z with hxz hxz
  · rw [← hx (pred x) (pred_lt _), hz (pred x)]
    exact (pred_lt _).trans_le hxz
  · rw [← hx (pred z), hz (pred z) (pred_lt _)]
    exact (pred_lt _).trans hxz

theorem Positive.sub_negative (hf : f.Positive) (hg : g.Negative) : (f - g).Positive := by
  have := hf.not_negative
  refine' ⟨_, _⟩
  · rw [Ne.def, sub_eq_zero]
    rintro rfl
    exact hf.not_negative hg
  · obtain ⟨x, hx⟩ := hf.right
    obtain ⟨z, hz⟩ := hg.right
    refine' ⟨min (pred x) (pred z), fun y hy => _⟩
    rw [FormalSeries.sub_def, sub_eq_zero, hx y (hy.trans _), hz y (hy.trans _), zero_sub,
      Fin.neg_coe_eq_one, eq_comm, difcar_eq_one_iff]
    · refine' ⟨min (pred x) (pred z), hy, _, fun w hw _ => _⟩
      · rw [hx, hz, Fin.lt_iff_val_lt_val]
        · simpa using hb.out
        · simp
        · simp
      · rw [hx _ (hw.trans _), hz _ (hw.trans _)]
        · simp
        · simp
        · simp
    · simp
    · simp

-- (ii)
theorem Positive.neg_negative (hf : f.Positive) : (-f).Negative :=
  by
  refine' ⟨_, _⟩
  · rw [Ne.def, neg_eq_iff_eq_neg, eq_comm, neg_zero]
    exact hf.left.symm
  · simp_rw [f.neg_def, FormalSeries.sub_def]
    obtain ⟨x, hx⟩ := hf.right
    obtain ⟨z, hz⟩ : ∃ z, 0 < f z := by
      by_contra'
      refine' hf.left (FormalSeries.ext _ _ _)
      simpa
    refine' ⟨pred x, fun y hy => _⟩
    simp_rw [hx y (hy.trans (pred_lt _)), zero_apply, sub_self, zero_sub]
    rw [neg_eq_iff_eq_neg, eq_comm, Fin.neg_coe_eq_one b, eq_comm, difcar_eq_one_iff]
    refine' ⟨z, _, hz, _⟩
    · contrapose! hz
      rw [hx _ (hz.trans_lt (hy.trans (pred_lt _)))]
    · simp

theorem Negative.sub_positive (hf : f.Negative) (hg : g.Positive) : (f - g).Negative :=
  by
  refine' ⟨_, _⟩
  · rw [Ne.def, sub_eq_zero]
    rintro rfl
    exact hf.not_positive hg
  · obtain ⟨x, hx⟩ := hf.right
    obtain ⟨z, hz⟩ := hg.right
    refine' ⟨pred (min (pred x) (pred z)), fun y hy => _⟩
    rw [FormalSeries.sub_def, hx y (hy.trans ((pred_lt _).trans _)),
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
        · simpa using hb.out
        · simp
        · simp
    · simp
    · simp

-- (iii)
theorem Positive.sub_positive (hf : f.Positive) (hg : g.Positive) (hne : f ≠ g) :
    ((f - g).Positive ∧ ∃ x₀, f x₀ > g x₀ ∧ ∀ y < x₀, f y = g y) ∨
      (f - g).Negative ∧ ¬∃ x₀, f x₀ > g x₀ ∧ ∀ y < x₀, f y = g y :=
  by
  obtain ⟨x, hx⟩ : ∃ x, ∀ y ≤ x, f y = 0 ∧ g y = 0 :=
    by
    obtain ⟨x, hx⟩ := hf.right
    obtain ⟨z, hz⟩ := hg.right
    refine' ⟨min (pred x) (pred z), fun y hy => ⟨hx _ (hy.trans_lt _), hz _ (hy.trans_lt _)⟩⟩ <;>
      simp
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, f x₀ ≠ g x₀ ∧ ∀ y < x₀, f y = g y :=
    by
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
  have hd : (∀ z < x₀, difcar f g z = 1) ↔ f x₀ < g x₀ :=
    by
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
  have hd' : (∀ z < x₀, difcar f g z = 0) ↔ g x₀ < f x₀ :=
    by
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
      exact one_ne_zero
  refine' hx₀.left.lt_or_lt.symm.imp _ _ <;> intro H
  · refine' ⟨⟨_, x₀, fun y hy => _⟩, ⟨_, H, hx₀.right⟩⟩
    · rwa [Ne.def, sub_eq_zero]
    · rw [← hd'] at H
      simp [FormalSeries.sub_def, hx₀.right _ hy, H _ hy]
  · refine' ⟨⟨_, x₀, fun y hy => _⟩, _⟩
    · rwa [Ne.def, sub_eq_zero]
    · rw [← hd] at H
      simp only [FormalSeries.sub_def, hx₀.right _ hy, H _ hy, sub_self, zero_sub]
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
      (f - g).Negative ∧ ¬∃ x₀, f x₀ > g x₀ ∧ ∀ y < x₀, f y = g y :=
  by
  -- ideally, use (hf.neg_positive).sub_positive (hg.neg_positive)
  -- because the tactic proof is identical expect for this obtain
  obtain ⟨x, hx⟩ : ∃ x, ∀ y ≤ x, f y = b ∧ g y = b :=
    by
    obtain ⟨x, hx⟩ := hf.right
    obtain ⟨z, hz⟩ := hg.right
    refine' ⟨min (pred x) (pred z), fun y hy => ⟨hx _ (hy.trans_lt _), hz _ (hy.trans_lt _)⟩⟩ <;>
      simp
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, f x₀ ≠ g x₀ ∧ ∀ y < x₀, f y = g y :=
    by
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
  have hd : (∀ z < x₀, difcar f g z = 1) ↔ f x₀ < g x₀ :=
    by
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
  have hd' : (∀ z < x₀, difcar f g z = 0) ↔ g x₀ < f x₀ :=
    by
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
      exact one_ne_zero
  refine' hx₀.left.lt_or_lt.symm.imp _ _ <;> intro H
  · refine' ⟨⟨_, x₀, fun y hy => _⟩, ⟨_, H, hx₀.right⟩⟩
    · rwa [Ne.def, sub_eq_zero]
    · rw [← hd'] at H
      simp [FormalSeries.sub_def, hx₀.right _ hy, H _ hy]
  · refine' ⟨⟨_, x₀, fun y hy => _⟩, _⟩
    · rwa [Ne.def, sub_eq_zero]
    · rw [← hd] at H
      simp only [FormalSeries.sub_def, hx₀.right _ hy, H _ hy, sub_self, zero_sub]
      rw [neg_eq_iff_eq_neg, Fin.neg_coe_eq_one]
    · push_neg
      intro z hz
      refine' ⟨x₀, _, H.ne⟩
      contrapose! hz
      rcases hz.eq_or_lt with (rfl | hz')
      · exact H.le
      · exact (hx₀.right _ hz').le

end FormalSeries

end S06

section S07

variable (Z : Type*) [LinearOrder Z] [SuccOrder Z] [NoMaxOrder Z] [PredOrder Z] [NoMinOrder Z]
    [IsSuccArchimedean Z] (b : ℕ) [hb : Fact (0 < b)]

-- 7.1
def FormalSeries.real : AddSubgroup (FormalSeries Z b)
    where
  carrier := {f | f.Positive ∨ f.Negative ∨ f = 0}
  add_mem' := by
    simp_rw [← sub_neg_eq_add]
    simp only [Set.mem_setOf_eq]
    rintro f g (hf | hf | rfl) (hg | hg | rfl)
    · exact Or.inl (hf.sub_negative hg.neg_negative)
    · rcases eq_or_ne f (-g) with (rfl | hne)
      · simp
      rw [← or_assoc]
      exact Or.inl ((hf.sub_positive hg.neg_positive hne).imp And.left fun H => H.left)
    · simp [hf]
    · rcases eq_or_ne f (-g) with (rfl | hne)
      · simp
      rw [← or_assoc]
      exact Or.inl ((hf.sub_negative hg.neg_negative hne).imp And.left fun H => H.left)
    · exact Or.inr (Or.inl (hf.sub_positive hg.neg_positive))
    · simp [hf]
    · simp [hg]
    · simp [hg]
    · simp
  zero_mem' := by simp
  neg_mem' := by
    simp only [Set.mem_setOf_eq]
    rintro f (hf | hf | rfl)
    · exact Or.inr (Or.inl hf.neg_negative)
    · exact Or.inl hf.neg_positive
    · simp

instance : LT (FormalSeries.real Z b) :=
  ⟨fun f g => (g - f : FormalSeries Z b).Positive⟩

variable {Z} {b}
variable {f g : FormalSeries Z b}

protected theorem FormalSeries.real.apply_eq_coe_apply (f : FormalSeries.real Z b) (z : Z) :
    (f : FormalSeries Z b) z = (f : FormalSeries Z b) z :=
  rfl

protected theorem FormalSeries.real.lt_def {f g : FormalSeries.real Z b} :
    f < g ↔ (g - f : FormalSeries Z b).Positive :=
  Iff.rfl

variable (b) (Z)

-- 7.2(ii)
instance FormalSeries.real.PartialOrder : PartialOrder (FormalSeries.real Z b)
    where
  le f g := f = g ∨ f < g
  lt := (· < ·)
  le_refl _ := Or.inl rfl
  le_trans f g h := by
    rintro (rfl | hfg) (rfl | hgh)
    · exact Or.inl rfl
    · exact Or.inr hgh
    · exact Or.inr hfg
    · refine' Or.inr _
      rw [FormalSeries.real.lt_def] at hfg hgh ⊢
      rw [← sub_sub_sub_cancel_right _ _ (g : FormalSeries Z b), ← neg_sub (g : FormalSeries Z b) f]
      exact hgh.sub_negative hfg.neg_negative
  lt_iff_le_not_le f g := by
    constructor
    · intro h
      refine' ⟨Or.inr h, _⟩
      rintro (rfl | H) <;> rw [FormalSeries.real.lt_def] at *
      · refine' (_ : (g : FormalSeries Z b) ≠ g) rfl
        rw [Ne.def, ← sub_eq_zero]
        exact h.left
      · rw [← neg_sub] at H
        exact h.neg_negative.not_positive H
    · rintro ⟨rfl | h, H⟩
      · contrapose! H
        exact Or.inl rfl
      · exact h
  le_antisymm f g := by
    rintro (rfl | hfg) (hgf | hgf)
    · rfl
    · rfl
    · exact hgf.symm
    · rw [FormalSeries.real.lt_def] at hfg hgf
      rw [← neg_sub] at hgf
      exact absurd hgf hfg.neg_negative.not_positive

-- 7.2(i)
noncomputable instance : LinearOrder (FormalSeries.real Z b) :=
  { FormalSeries.real.PartialOrder _
      _ with
    le_total := fun f g =>
      by
      rcases hfg : f - g with ⟨h, H | H | rfl⟩ <;>
        simp only [Subtype.ext_iff, AddSubgroup.coe_sub, Subtype.coe_mk] at hfg
      · subst hfg
        exact Or.inr (Or.inr H)
      · subst hfg
        replace H := H.neg_positive
        rw [neg_sub] at H
        exact Or.inl (Or.inr H)
      · rw [sub_eq_zero, ← Subtype.ext_iff] at hfg
        subst hfg
        exact Or.inl le_rfl
    decidableLE := Classical.decRel _ }

-- 7.2(iii)
instance : CovariantClass (FormalSeries.real Z b) (FormalSeries.real Z b) (· + ·) (· < ·) :=
  ⟨fun _ _ _ => by simp_rw [FormalSeries.real.lt_def]; simp⟩

variable {Z} {b}

-- 7.2(iv)
theorem FormalSeries.real.positive_iff {f : FormalSeries.real Z b} :
    (f : FormalSeries Z b).Positive ↔ 0 < f := by
  simp [FormalSeries.real.lt_def]

theorem FormalSeries.real.negative_iff {f : FormalSeries.real Z b} :
    (f : FormalSeries Z b).Negative ↔ f < 0 := by
  simp only [FormalSeries.real.lt_def, AddSubgroup.coe_zero, zero_sub]
  refine' ⟨FormalSeries.Negative.neg_positive, fun h => _⟩
  rw [← neg_neg (f : FormalSeries Z b)]
  exact h.neg_negative

end S07

section S08

-- TODO
def AddSubgroup.subCopy {A : Type*} [AddCommGroup A] (s : Set A) (hn : s.Nonempty)
    (hs : ∀ {f g : A}, f ∈ s → g ∈ s → f - g ∈ s) : AddSubgroup A
    where
  carrier := s
  add_mem' := by
    intros f g hf hg
    rw [← sub_neg_eq_add]
    refine' hs hf _
    rw [← zero_sub, ← sub_self f]
    exact hs (hs hf hf) hg
  zero_mem' := Exists.elim hn fun x hx => sub_self x ▸ hs hx hx
  neg_mem' := by intro f hf; simp_rw [← zero_sub, ← sub_self f]; exact hs (hs hf hf) hf

variable (b) (Z)

namespace FormalSeries

variable (Z : Type*) [Nonempty Z] [LinearOrder Z] [SuccOrder Z] [NoMaxOrder Z] [PredOrder Z]
  [NoMinOrder Z] [IsSuccArchimedean Z] (b : ℕ) [hb : Fact (0 < b)]

def hensel : AddSubgroup (FormalSeries Z b) :=
  AddSubgroup.subCopy {f : FormalSeries Z b | ∃ x, ∀ z > x, f z = 0} ⟨0, by simp⟩
    (by
      simp only [gt_iff_lt, Set.mem_setOf_eq, forall_exists_index]
      intro f g x hfx y hgy
      use max x y
      intro z hz
      simp only [max_lt_iff] at hz
      rw [FormalSeries.sub_def, hfx _ hz.left, hgy _ hz.right]
      simp only [difcar_eq_zero_iff, sub_self, neg_zero, zero_sub, neg_eq_zero, gt_iff_lt]
      intro w hw
      simp [hfx _ (hz.left.trans hw), hgy _ (hz.right.trans hw)])

def henselInt [Zero Z] : AddSubgroup (FormalSeries Z b) :=
  AddSubgroup.subCopy {f : FormalSeries Z b | ∀ z > 0, f z = 0} ⟨0, by simp⟩
    (by
      intro f g hf hg z hz
      simp only [FormalSeries.sub_def, hf _ hz, hg _ hz, difcar_eq_zero_iff, sub_self, neg_zero,
        zero_sub, neg_eq_zero, gt_iff_lt]
      intro w hw
      simp [hf _ (hw.trans' hz), hg _ (hw.trans' hz)])

def realHensel : AddSubgroup (FormalSeries Z b) :=
  real Z b ⊓ hensel Z b

def real.hensel : AddSubgroup (real Z b) :=
  (realHensel Z b).comap (AddSubgroup.subtype _)

def zStar [Zero Z] : AddSubgroup (FormalSeries Z b) :=
  real Z b ⊓ henselInt Z b

variable {Z} {b}

-- 8.2
theorem real.dense {f g : real Z b} (hfg : f > g) :
    ∃ h ∈ real.hensel Z b, f > h ∧ h > g := by
  set k := f - g with hk
  have kpos : FormalSeries.Positive (k : FormalSeries Z b) := by
    rwa [real.positive_iff, hk, sub_pos]
  obtain ⟨x, xpos, hx⟩ := kpos.exists_least_pos
  let p' : FormalSeries Z b := ⟨fun y => if y ≤ x then 0 else if y = succ x then 1
    else (f : FormalSeries Z b) y, ?_⟩
  swap
  · rintro ⟨z, hz⟩
    obtain ⟨w, hwz, hw⟩ := exists_bounded (f : FormalSeries Z b) z
    cases' le_or_lt w x with h h
    · specialize hz _ hwz
      simp only at hz
      rw [if_pos h, ← Fin.val_last b, Fin.cast_val_eq_self] at hz
      cases b
      · exact absurd hb.out (lt_irrefl _)
      · exact (Fin.last_pos : 0 < Fin.last _).ne hz
    · obtain ⟨w', hww', hw'⟩ := exists_bounded (f : FormalSeries Z b) (succ w)
      specialize hz w' ((lt_trans hwz (lt_succ _)).trans hww')
      simp only at hz
      rw [if_neg ((succ_strictMono h).trans hww').ne',
        if_neg (not_le_of_lt (h.trans ((lt_succ _).trans hww')))] at hz
      exact hw'.ne hz
  have px0 : ∀ y ≤ x, p' y = 0 := by
    intro y hy
    exact if_pos hy
  have ppos : p'.Positive := by
    refine' ⟨fun H => _, x, _⟩
    · replace H : p' (succ x) = 0
      · rw [H, zero_apply]
      simp [p', ne_of_gt hb.out] at H
    · intro y hy
      exact px0 _ hy.le
  let p : real Z b := ⟨p', Or.inl ppos⟩
  refine' ⟨f - p, ⟨(f - p).prop, succ x, _⟩, _, _⟩
  · intro z hz
    simp only [FormalSeries.sub_def, AddSubgroup.coeSubtype, AddSubgroup.coe_sub, Subtype.coe_mk,
      mk_apply, ne_of_gt hz, not_le_of_lt ((lt_trans (lt_succ x)) hz),
      real.apply_eq_coe_apply, difcar_eq_zero_iff, if_false, sub_self, zero_sub,
      neg_eq_zero, gt_iff_lt]
    intro w hzw
    simp [not_le_of_lt (lt_trans (lt_succ x) (lt_trans hz hzw)), ne_of_gt (lt_trans hz hzw)]
  · rw [gt_iff_lt, sub_lt_comm, sub_self, ← real.positive_iff]
    exact ppos
  suffices k > p by
    rwa [gt_iff_lt, ← add_lt_add_iff_left (g - p), hk, sub_add_sub_cancel', sub_add_cancel] at this
  rw [gt_iff_lt, real.lt_def]
  refine' ((kpos.sub_positive ppos fun H => xpos.ne _).resolve_right _).left
  · rw [H, px0 _ le_rfl]
  · push_neg
    refine' fun _ => ⟨x, _, fun y hy => _⟩
    · rwa [px0 _ le_rfl]
    · rw [hx _ hy, px0 _ hy.le]

-- 8.3
theorem real.exists_lt_zStar [Zero Z] (f : real Z b) :
    ∃ h : zStar Z b, (⟨_, h.prop.left⟩ : real Z b) > f := by
  let q' : FormalSeries Z b := ⟨fun x => if x ≤ 0 then b else (f : FormalSeries Z b) x, ?_⟩
  swap
  · rintro ⟨z, hz⟩
    obtain ⟨x, hx, hx'⟩ := exists_bounded (f : FormalSeries Z b) (max (succ z) (succ 0))
    refine' hx'.ne _
    simp only at hz
    rw [← hz x (lt_trans _ hx), if_neg (not_le_of_lt (lt_trans _ hx)),
        real.apply_eq_coe_apply] <;>
      simp
  have qneg : q'.Negative := by
    refine' ⟨fun H => _, 0, fun y hy => _⟩
    · replace H : q' 0 = 0
      · rw [H, zero_apply]
      simp only [q', mk_apply, if_pos le_rfl] at H
      rw [← Fin.val_last b, Fin.cast_val_eq_self] at H
      cases b
      · exact absurd hb.out (lt_irrefl _)
      · exact (Fin.last_pos : 0 < Fin.last _).ne' H
    · simp [q', hy.not_lt]
  let q : real Z b := ⟨q', Or.inr (Or.inl qneg)⟩
  refine' ⟨⟨f - q, (f - q).prop, fun z zpos => _⟩, _⟩
  · simp only [FormalSeries.sub_def, not_le_of_lt zpos, real.apply_eq_coe_apply,
      difcar_eq_zero_iff, Subtype.coe_mk, mk_apply, if_false, sub_self, zero_sub,
      neg_eq_zero, gt_iff_lt]
    intro x hx
    simp [(hx.trans' zpos).not_le]
  · change f < f - q
    rwa [lt_sub_comm, sub_self, ← real.negative_iff]

end FormalSeries
end S08

section S10

namespace FormalSeries

def cutoff {Z : Type*} [LT Z] {b : ℕ} [hb : Fact (0 < b)] (z : Z) (f : FormalSeries Z b) :
    FormalSeries Z b :=
  ⟨fun x => if z < x then 0 else f x, by
    rintro ⟨y, hy⟩
    obtain ⟨w, hwy, hw⟩ := f.exists_bounded y
    specialize hy w hwy
    simp only at hy
    have : (b : Fin (b + 1)) = Fin.last b
    · rw [←Fin.val_last b, Fin.cast_val_eq_self]
      simp
    rw [this] at hy hw
    split_ifs at hy
    · cases b
      · exact absurd rfl (ne_of_lt hb.out)
      · exact (Fin.last_pos : 0 < Fin.last _).ne hy
    · exact hw.ne hy⟩

theorem cutoff_apply_le {Z : Type*} [Preorder Z] {b : ℕ} [Fact (0 < b)]
    (f : FormalSeries Z b) (z x : Z) (h : x ≤ z) : f.cutoff z x = f x :=
  if_neg (not_lt_of_le h)

theorem cutoff_apply_lt {Z : Type*} [LT Z] {b : ℕ} [Fact (0 < b)]
    (f : FormalSeries Z b) (z x : Z) (h : z < x) : f.cutoff z x = 0 :=
  if_pos h

variable {Z : Type*} [LinearOrder Z] [SuccOrder Z] [NoMaxOrder Z] [PredOrder Z] [NoMinOrder Z]
    [IsSuccArchimedean Z] {b : ℕ} [hb : Fact (0 < b)]

def real.cutoff (z : Z) (f : real Z b) : real Z b :=
  ⟨FormalSeries.cutoff z (f : FormalSeries Z b), by
    rcases f with ⟨f, hf | hf | rfl⟩ <;> rw [Subtype.coe_mk]
    · obtain ⟨x, xpos, hx⟩ := hf.exists_least_pos
      cases' lt_or_le z x with h h
      · refine' Or.inr (Or.inr _)
        ext y : 1
        cases' lt_or_le z y with hy hy
        · rw [cutoff_apply_lt _ _ _ hy, zero_apply]
        · rw [cutoff_apply_le _ _ _ hy]
          exact hx _ (h.trans_le' hy)
      · refine' Or.inl ⟨fun H => xpos.ne _, x, fun y hy => _⟩
        · rw [← cutoff_apply_le _ _ _ h, H, zero_apply]
        · rw [cutoff_apply_le _ _ _ (hy.le.trans h), hx _ hy]
    · obtain ⟨hne, x, hx⟩ := hf
      refine' Or.inr (Or.inl ⟨fun H => _, min x z, fun y hy => _⟩)
      · replace H : f.cutoff z (min z (pred x)) = 0
        · rw [H, zero_apply]
        cases' b with b
        · exact absurd rfl (ne_of_lt hb.out)
        · refine' (Fin.last_pos : 0 < Fin.last (Nat.succ b)).ne _
          rw [← Fin.cast_val_eq_self (Fin.last _), Fin.val_last, ← hx (min z (pred x)), ← H,
              cutoff_apply_le] <;>
            simp
      · rw [lt_min_iff] at hy
        rw [cutoff_apply_le _ _ _ hy.right.le, hx _ hy.left]
    · refine' Or.inr (Or.inr _)
      ext x : 1
      cases' lt_or_le z x with h h <;> simp [cutoff_apply_le, cutoff_apply_lt, h]⟩

theorem real.exists_isLeast_image_cutoff (S : Set (real Z b))
    (hn : S.Nonempty) (h : BddBelow S) (z : Z) : ∃ x, IsLeast (real.cutoff z '' S) x := by
  sorry

end FormalSeries
end S10
