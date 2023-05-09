import Mathlib.Data.Int.ModEq
import Mathlib.Data.Real.ENNReal
import Mathlib.Tactic.RelCongr.Basic

/-! # ≤, + -/

attribute [rel_congr]
  add_le_add -- tt + tt
  add_le_add_left -- ff + tt
  add_le_add_right -- tt + ff

/-! # <, + -/

attribute [rel_congr]
  add_lt_add ENNReal.add_lt_add -- tt + tt
  add_lt_add_left ENNReal.add_lt_add_left -- ff + tt
  add_lt_add_right ENNReal.add_lt_add_right -- tt + ff

/-! # ≡ ZMOD, + -/

attribute [rel_congr]
  Int.ModEq.add -- tt + tt
  Int.ModEq.add_left -- ff + tt
  Int.ModEq.add_right -- tt + ff

/-! # ≤, - -/

attribute [rel_congr]
  sub_le_sub -- tt - tt
  sub_le_sub_left -- ff - tt
  sub_le_sub_right -- tt - ff

/-! # <, - -/

attribute [rel_congr]
  sub_lt_sub -- tt - tt
  sub_lt_sub_left -- ff - tt
  sub_lt_sub_right -- tt - ff

/-! # ≡ ZMOD, - -/

attribute [rel_congr]
  Int.ModEq.sub -- tt - tt
  Int.ModEq.sub_left -- ff - tt
  Int.ModEq.sub_right -- tt - ff

/-! # ≤, * -/

attribute [rel_congr]
  mul_le_mul' mul_le_mul -- tt * tt
  mul_le_mul_left' mul_le_mul_of_nonneg_left -- ff * tt
  mul_le_mul_right' mul_le_mul_of_nonneg_right -- tt * ff

/-! # <, * -/

theorem ENNReal.mul_lt_mul_left' {a b c : ENNReal} (h0 : a ≠ 0) (hinf : a ≠ ⊤) (bc : b < c) :
    a * b < a * c :=
  ENNReal.mul_left_strictMono h0 hinf bc

theorem ENNReal.mul_lt_mul_right' {a b c : ENNReal} (h0 : a ≠ 0) (hinf : a ≠ ⊤) (bc : b < c) :
    b * a < c * a :=
  mul_comm b a ▸ mul_comm c a ▸ ENNReal.mul_left_strictMono h0 hinf bc

attribute [rel_congr]
  mul_lt_mul_of_lt_of_lt mul_lt_mul'' ENNReal.mul_lt_mul -- tt * tt
  mul_lt_mul_left' mul_lt_mul_of_pos_left ENNReal.mul_lt_mul_left' -- ff * tt
  mul_lt_mul_right' mul_lt_mul_of_pos_right ENNReal.mul_lt_mul_right' -- tt * ff

/-! # ≡ ZMOD, * -/

attribute [rel_congr]
  Int.ModEq.mul -- tt * tt
  Int.ModEq.mul_left -- ff * tt
  Int.ModEq.mul_right -- tt * ff

/-! # ≤, / -/

theorem Nat.div_le_div (a b c d : ℕ) (h1 : a ≤ b) (h2 : d ≤ c) (h3 : d ≠ 0) : a / c ≤ b / d :=
  calc a / c ≤ b / c := Nat.div_le_div_right h1
    _ ≤ b / d := Nat.div_le_div_left h2 (Nat.pos_of_ne_zero h3)

attribute [rel_congr]
  div_le_div'' div_le_div Nat.div_le_div ENNReal.div_le_div -- tt / tt
  div_le_div_left' div_le_div_of_le_left Nat.div_le_div_left ENNReal.div_le_div_left -- ff / tt
  div_le_div_right' div_le_div_of_le Nat.div_le_div_right ENNReal.div_le_div_right -- tt / ff

/-! # <, / -/

attribute [rel_congr]
  div_lt_div'' div_lt_div -- tt / tt
  div_lt_div_left' div_lt_div_of_lt_left -- ff / tt
  div_lt_div_right' div_lt_div_of_lt -- tt / ff

/-! # ≤, ⁻¹ -/

theorem ENNReal.inv_le_inv' {a b : ENNReal} (h : a ≤ b) : b⁻¹ ≤ a⁻¹ :=
  ENNReal.inv_strictAnti.antitone h

theorem ENNReal.inv_lt_inv' {a b : ENNReal} (h : a < b) : b⁻¹ < a⁻¹ := ENNReal.inv_strictAnti h

attribute [rel_congr]
  inv_le_inv_of_le inv_le_inv' ENNReal.inv_le_inv' -- tt
  inv_lt_inv_of_lt inv_lt_inv' ENNReal.inv_lt_inv' -- tt

/-! # ≤, ^ -/

attribute [rel_congr]
  pow_le_pow pow_le_pow' zpow_le_zpow zpow_le_of_le ENNReal.zpow_le_of_le -- ff ^ tt
  pow_le_pow_of_le_left pow_le_pow_of_le_left' zpow_le_zpow' -- tt ^ ff

/-! # <, ^ -/

theorem zpow_lt_of_lt [LinearOrderedSemifield α] {a : α} {m n : ℤ} (hx : 1 < a) (h : m < n) :
    a ^ m < a ^ n :=
  zpow_strictMono hx h

theorem ENNReal.pow_lt_pow_of_lt_left {x y : ENNReal} (h : x < y) {n : ℕ} (hn : n ≠ 0) :
    x ^ n < y ^ n :=
  ENNReal.pow_strictMono hn h

attribute [rel_congr]
  pow_lt_pow pow_lt_pow' zpow_lt_zpow zpow_lt_of_lt -- ff ^ tt
  pow_lt_pow_of_lt_left ENNReal.pow_lt_pow_of_lt_left zpow_lt_zpow' -- tt ^ ff

/-! # ≡ ZMOD, ^ -/

attribute [rel_congr]
  Int.ModEq.pow -- tt * ff

/-! # ≤, ∑ -/

-- a variant statement of `Finset.sum_le_sum`, since it doesn't match the attribute pattern in the
-- library statement:
theorem RelCongr.Finset.sum_le_sum [OrderedAddCommMonoid N] {f g : ι → N} {s : Finset ι}
    (h : ∀ (i : ι), i ∈ s → f i ≤ g i) : s.sum f ≤ s.sum g :=
  s.sum_le_sum h

attribute [rel_congr]
  RelCongr.Finset.sum_le_sum

/-! # <, ∑ -/

-- a variant statement of `Finset.sum_lt_sum`, since it doesn't match the attribute pattern in the
-- library statement:
theorem RelCongr.Finset.sum_lt_sum_of_nonempty [OrderedCancelAddCommMonoid M]
    {f g : ι → M} {s : Finset ι} (hs : Finset.Nonempty s) (Hlt : ∀ (i : ι), i ∈ s → f i < g i) :
    s.sum f < s.sum g :=
  s.sum_lt_sum_of_nonempty hs Hlt

attribute [rel_congr]
  RelCongr.Finset.sum_lt_sum_of_nonempty

/-! # ≤, ∏ -/

-- a variant statement of `Finset.prod_le_prod'`, since it doesn't match the attribute pattern in
-- the library statement:
theorem RelCongr.Finset.prod_le_prod' [OrderedCommMonoid N] {f g : ι → N} {s : Finset ι}
    (h : ∀ (i : ι), i ∈ s → f i ≤ g i) : s.prod f ≤ s.prod g :=
  s.prod_le_prod' h

-- a variant statement of `Finset.prod_le_prod`, since it doesn't match the attribute pattern in the
-- library statement:
theorem RelCongr.Finset.prod_le_prod [OrderedCommSemiring R] {f g : ι → R}
    {s : Finset ι} (h0 : ∀ (i : ι), i ∈ s → 0 ≤ f i) (h1 : ∀ (i : ι), i ∈ s → f i ≤ g i) :
    s.prod f ≤ s.prod g :=
  s.prod_le_prod h0 h1

attribute [rel_congr]
  RelCongr.Finset.prod_le_prod' RelCongr.Finset.prod_le_prod

/-! # <, ∏ -/

-- a variant statement of `Finset.prod_lt_prod_of_nonempty'`, since it doesn't match the attribute
-- pattern in the library statement:
theorem RelCongr.Finset.prod_lt_prod_of_nonempty' [OrderedCancelCommMonoid M]
    {f g : ι → M} {s : Finset ι} (hs : Finset.Nonempty s) (Hlt : ∀ (i : ι), i ∈ s → f i < g i) :
    s.prod f < s.prod g :=
  s.prod_lt_prod_of_nonempty' hs Hlt

attribute [rel_congr]
  RelCongr.Finset.prod_lt_prod_of_nonempty'
