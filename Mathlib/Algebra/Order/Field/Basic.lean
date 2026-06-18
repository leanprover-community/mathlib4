/-
Copyright (c) 2014 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Order.GroupWithZero.OrderIso
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Set.Monotone
public import Mathlib.Order.Bounds.OrderIso
public import Mathlib.Tactic.Positivity.Core

/-!
# Lemmas about (linear) ordered (semi)fields
-/

@[expose] public section


open Function OrderDual

variable {ι α β : Type*}

section PartialOrderedSemifield

variable [Semifield α] [PartialOrder α] [PosMulReflectLT α] {a b c d e : α} {m n : ℤ}

attribute [local instance] PosMulReflectLT.toMulPosReflectLT

/-!
### Relating one division and involving `1`
-/

@[bound]
theorem le_div_self (ha : 0 ≤ a) (hb₀ : 0 < b) (hb₁ : b ≤ 1) : a ≤ a / b := by
  simpa only [div_one] using div_le_div_of_nonneg_left ha hb₀ hb₁

theorem one_le_div (hb : 0 < b) : 1 ≤ a / b ↔ b ≤ a := by rw [le_div_iff₀ hb, one_mul]

theorem div_le_one (hb : 0 < b) : a / b ≤ 1 ↔ a ≤ b := by rw [div_le_iff₀ hb, one_mul]

theorem one_lt_div (hb : 0 < b) : 1 < a / b ↔ b < a := by rw [lt_div_iff₀ hb, one_mul]

theorem div_lt_one (hb : 0 < b) : a / b < 1 ↔ a < b := by rw [div_lt_iff₀ hb, one_mul]

theorem one_div_le (ha : 0 < a) (hb : 0 < b) : 1 / a ≤ b ↔ 1 / b ≤ a := by
  simpa using inv_le_comm₀ ha hb

theorem one_div_lt (ha : 0 < a) (hb : 0 < b) : 1 / a < b ↔ 1 / b < a := by
  simpa using inv_lt_comm₀ ha hb

theorem le_one_div (ha : 0 < a) (hb : 0 < b) : a ≤ 1 / b ↔ b ≤ 1 / a := by
  simpa using le_inv_comm₀ ha hb

theorem lt_one_div (ha : 0 < a) (hb : 0 < b) : a < 1 / b ↔ b < 1 / a := by
  simpa using lt_inv_comm₀ ha hb

@[bound] lemma Bound.one_lt_div_of_pos_of_lt (b0 : 0 < b) : b < a → 1 < a / b := (one_lt_div b0).mpr

@[bound] lemma Bound.div_lt_one_of_pos_of_lt (b0 : 0 < b) : a < b → a / b < 1 := (div_lt_one b0).mpr

/-!
### Relating two divisions, involving `1`
-/

theorem one_div_le_one_div_of_le (ha : 0 < a) (h : a ≤ b) : 1 / b ≤ 1 / a := by
  simpa using inv_anti₀ ha h

theorem one_div_lt_one_div_of_lt (ha : 0 < a) (h : a < b) : 1 / b < 1 / a := by
  rwa [lt_div_iff₀' ha, ← div_eq_mul_one_div, div_lt_one (ha.trans h)]

theorem le_of_one_div_le_one_div (ha : 0 < a) (h : 1 / a ≤ 1 / b) : b ≤ a := by
  simpa using one_div_le_one_div_of_le (by simpa) h

theorem lt_of_one_div_lt_one_div (ha : 0 < a) (h : 1 / a < 1 / b) : b < a := by
  simpa using one_div_lt_one_div_of_lt (by simpa) h

variable [IsStrictOrderedRing α]

@[bound]
theorem div_le_self (ha : 0 ≤ a) (hb : 1 ≤ b) : a / b ≤ a := by
  simpa only [div_one] using div_le_div_of_nonneg_left ha zero_lt_one hb

@[bound]
theorem div_lt_self (ha : 0 < a) (hb : 1 < b) : a / b < a := by
  simpa only [div_one] using div_lt_div_of_pos_left ha zero_lt_one hb

/-- For the single implications with fewer assumptions, see `one_div_le_one_div_of_le` and
  `le_of_one_div_le_one_div` -/
theorem one_div_le_one_div (ha : 0 < a) (hb : 0 < b) : 1 / a ≤ 1 / b ↔ b ≤ a :=
  div_le_div_iff_of_pos_left zero_lt_one ha hb

/-- For the single implications with fewer assumptions, see `one_div_lt_one_div_of_lt` and
  `lt_of_one_div_lt_one_div` -/
theorem one_div_lt_one_div (ha : 0 < a) (hb : 0 < b) : 1 / a < 1 / b ↔ b < a :=
  div_lt_div_iff_of_pos_left zero_lt_one ha hb

theorem one_lt_one_div (h1 : 0 < a) (h2 : a < 1) : 1 < 1 / a := by
  rwa [lt_one_div (@zero_lt_one α _ _ _ _ _) h1, one_div_one]

theorem one_le_one_div (h1 : 0 < a) (h2 : a ≤ 1) : 1 ≤ 1 / a := by
  rwa [le_one_div (@zero_lt_one α _ _ _ _ _) h1, one_div_one]

/-!
### Results about halving.
The equalities also hold in semifields of characteristic `0`.
-/

theorem half_pos (h : 0 < a) : 0 < a / 2 :=
  div_pos h zero_lt_two

theorem one_half_pos : (0 : α) < 1 / 2 :=
  half_pos zero_lt_one

@[simp]
theorem half_le_self_iff : a / 2 ≤ a ↔ 0 ≤ a := by
  rw [div_le_iff₀ (zero_lt_two' α), mul_two, le_add_iff_nonneg_left]

@[simp]
theorem half_lt_self_iff : a / 2 < a ↔ 0 < a := by
  rw [div_lt_iff₀ (zero_lt_two' α), mul_two, lt_add_iff_pos_left]

alias ⟨_, half_le_self⟩ := half_le_self_iff

alias ⟨_, half_lt_self⟩ := half_lt_self_iff

alias div_two_lt_of_pos := half_lt_self

theorem one_half_lt_one : (1 / 2 : α) < 1 :=
  half_lt_self zero_lt_one

theorem two_inv_lt_one : (2⁻¹ : α) < 1 :=
  (one_div _).symm.trans_lt one_half_lt_one

theorem left_lt_add_div_two : a < (a + b) / 2 ↔ a < b := by simp [lt_div_iff₀, mul_two]

theorem add_div_two_lt_right : (a + b) / 2 < b ↔ a < b := by simp [div_lt_iff₀, mul_two]

omit [PosMulReflectLT α] in
theorem add_thirds (a : α) : a / 3 + a / 3 + a / 3 = a := by
  rw [← add_div, ← add_div, ← two_mul, ← add_one_mul 2 a, two_add_one_eq_three,
    mul_div_cancel_left₀ a three_ne_zero]

/-!
### Miscellaneous lemmas
-/

@[simp] lemma div_pos_iff_of_pos_left (ha : 0 < a) : 0 < a / b ↔ 0 < b := by
  simp only [div_eq_mul_inv, mul_pos_iff_of_pos_left ha, inv_pos]

@[simp] lemma div_pos_iff_of_pos_right (hb : 0 < b) : 0 < a / b ↔ 0 < a := by
  simp only [div_eq_mul_inv, mul_pos_iff_of_pos_right (inv_pos.2 hb)]

theorem div_mul_le_div_mul_of_div_le_div (h : a / b ≤ c / d) (he : 0 ≤ e) :
    a / (b * e) ≤ c / (d * e) := by
  rw [div_mul_eq_div_mul_one_div, div_mul_eq_div_mul_one_div]
  gcongr
  exact one_div_nonneg.2 he

omit [IsStrictOrderedRing α] in
theorem mul_le_mul_of_mul_div_le (h : a * (b / c) ≤ d) (hc : 0 < c) : b * a ≤ d * c := by
  rw [← mul_div_assoc] at h
  rwa [mul_comm b, ← div_le_iff₀ hc]

omit [IsStrictOrderedRing α] in
lemma monotone_div_right_of_nonneg (ha : 0 ≤ a) : Monotone (· / a) :=
  fun _b _c hbc ↦ div_le_div_of_nonneg_right hbc ha

omit [IsStrictOrderedRing α] in
lemma strictMono_div_right_of_pos (ha : 0 < a) : StrictMono (· / a) :=
  fun _b _c hbc ↦ div_lt_div_of_pos_right hbc ha

omit [IsStrictOrderedRing α] in
theorem Monotone.div_const {β : Type*} [Preorder β] {f : β → α} (hf : Monotone f) {c : α}
    (hc : 0 ≤ c) : Monotone fun x => f x / c := (monotone_div_right_of_nonneg hc).comp hf

theorem StrictMono.div_const {β : Type*} [Preorder β] {f : β → α} (hf : StrictMono f) {c : α}
    (hc : 0 < c) : StrictMono fun x => f x / c := by
  simpa only [div_eq_mul_inv] using hf.mul_const (inv_pos.2 hc)

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedSemiField.toDenselyOrdered : DenselyOrdered α where
  dense a₁ a₂ h :=
    ⟨(a₁ + a₂) / 2,
      calc
        a₁ = (a₁ + a₁) / 2 := (add_self_div_two a₁).symm
        _ < (a₁ + a₂) / 2 := by gcongr; exact zero_lt_two,
      calc
        (a₁ + a₂) / 2 < (a₂ + a₂) / 2 := by gcongr; exact zero_lt_two
        _ = a₂ := add_self_div_two a₂
        ⟩

theorem one_div_strictAntiOn : StrictAntiOn (fun x : α => 1 / x) (Set.Ioi 0) :=
  fun _ x1 _ y1 xy => (one_div_lt_one_div (Set.mem_Ioi.mp y1) (Set.mem_Ioi.mp x1)).mpr xy

theorem one_div_pow_le_one_div_pow_of_le (a1 : 1 ≤ a) {m n : ℕ} (mn : m ≤ n) :
    1 / a ^ n ≤ 1 / a ^ m := by
  refine (one_div_le_one_div ?_ ?_).mpr (pow_right_mono₀ a1 mn) <;>
    exact pow_pos (zero_lt_one.trans_le a1) _

theorem one_div_pow_lt_one_div_pow_of_lt (a1 : 1 < a) {m n : ℕ} (mn : m < n) :
    1 / a ^ n < 1 / a ^ m := by
  refine (one_div_lt_one_div ?_ ?_).2 (pow_lt_pow_right₀ a1 mn) <;>
    exact pow_pos (zero_lt_one.trans a1) _

theorem one_div_pow_anti (a1 : 1 ≤ a) : Antitone fun n : ℕ => 1 / a ^ n := fun _ _ =>
  one_div_pow_le_one_div_pow_of_le a1

theorem one_div_pow_strictAnti (a1 : 1 < a) : StrictAnti fun n : ℕ => 1 / a ^ n := fun _ _ =>
  one_div_pow_lt_one_div_pow_of_lt a1

omit [IsStrictOrderedRing α] in
theorem inv_strictAntiOn : StrictAntiOn (fun x : α => x⁻¹) (Set.Ioi 0) := fun _ hx _ hy xy =>
  (inv_lt_inv₀ hy hx).2 xy

theorem inv_pow_le_inv_pow_of_le (a1 : 1 ≤ a) {m n : ℕ} (mn : m ≤ n) : (a ^ n)⁻¹ ≤ (a ^ m)⁻¹ := by
  convert! one_div_pow_le_one_div_pow_of_le a1 mn using 1 <;> simp

theorem inv_pow_lt_inv_pow_of_lt (a1 : 1 < a) {m n : ℕ} (mn : m < n) : (a ^ n)⁻¹ < (a ^ m)⁻¹ := by
  convert! one_div_pow_lt_one_div_pow_of_lt a1 mn using 1 <;> simp

theorem inv_pow_anti (a1 : 1 ≤ a) : Antitone fun n : ℕ => (a ^ n)⁻¹ := fun _ _ =>
  inv_pow_le_inv_pow_of_le a1

theorem inv_pow_strictAnti (a1 : 1 < a) : StrictAnti fun n : ℕ => (a ^ n)⁻¹ := fun _ _ =>
  inv_pow_lt_inv_pow_of_lt a1

theorem le_iff_forall_one_lt_le_mul₀ {α : Type*}
    [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
    {a b : α} (hb : 0 ≤ b) : a ≤ b ↔ ∀ ε, 1 < ε → a ≤ b * ε := by
  refine ⟨fun h _ hε ↦ h.trans <| le_mul_of_one_le_right hb hε.le, fun h ↦ ?_⟩
  obtain rfl | hb := hb.eq_or_lt
  · simp_rw [zero_mul] at h
    exact h 2 one_lt_two
  refine le_of_forall_gt_imp_ge_of_dense fun x hbx => ?_
  convert! h (x / b) ((one_lt_div hb).mpr hbx)
  rw [mul_div_cancel₀ _ hb.ne']

theorem div_nat_le_self_of_nonnneg (ha : 0 ≤ a) (n : ℕ) : a / n ≤ a :=
  if h : n = 0 then by simpa [h] using ha
  else div_le_self ha (n.one_le_cast_iff_ne_zero.mpr h)

theorem div_nat_lt_self_of_pos_of_two_le (ha : 0 < a) {n : ℕ} (hn : 2 ≤ n) : a / n < a :=
  div_lt_self ha (n.one_lt_cast.mpr hn)

/-! ### Results about `IsGLB` -/


theorem IsGLB.mul_left {s : Set α} (ha : 0 ≤ a) (hs : IsGLB s b) :
    IsGLB ((fun b => a * b) '' s) (a * b) := by
  rcases lt_or_eq_of_le ha with (ha | rfl)
  · exact (OrderIso.mulLeft₀ _ ha).isGLB_image'.2 hs
  · simp_rw [zero_mul]
    rw [hs.nonempty.image_const]
    exact isGLB_singleton

theorem IsGLB.mul_right {s : Set α} (ha : 0 ≤ a) (hs : IsGLB s b) :
    IsGLB ((fun b => b * a) '' s) (b * a) := by simpa [mul_comm] using hs.mul_left ha

/-! ### Results about `IsLUB` -/


theorem IsLUB.mul_left {s : Set α} (ha : 0 ≤ a) (hs : IsLUB s b) :
    IsLUB ((fun b => a * b) '' s) (a * b) := by
  obtain ha | rfl := ha.lt_or_eq
  · exact (OrderIso.mulLeft₀ _ ha).isLUB_image'.2 hs
  · simp_rw [zero_mul]
    obtain rfl | ne := s.eq_empty_or_nonempty
    · simp only [Set.image_empty, isLUB_empty_iff] at hs ⊢
      have hb := hs (b + b)
      rw [le_add_iff_nonneg_right] at hb
      exact hs.mono hb
    rw [ne.image_const]
    exact isLUB_singleton

theorem IsLUB.mul_right {s : Set α} (ha : 0 ≤ a) (hs : IsLUB s b) :
    IsLUB ((fun b => b * a) '' s) (b * a) := by simpa [mul_comm] using hs.mul_left ha

end PartialOrderedSemifield

section LinearOrderedSemifield

variable {α : Type*} [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] {a b c d e : α}

theorem exists_pos_mul_lt {a : α} (h : 0 < a) (b : α) : ∃ c : α, 0 < c ∧ b * c < a := by
  have : 0 < a / max (b + 1) 1 := div_pos h (lt_max_iff.2 (Or.inr zero_lt_one))
  refine ⟨a / max (b + 1) 1, this, ?_⟩
  rw [← lt_div_iff₀ this, div_div_cancel₀ h.ne']
  exact lt_max_iff.2 (Or.inl <| lt_add_one _)

theorem exists_pos_lt_mul {a : α} (h : 0 < a) (b : α) : ∃ c : α, 0 < c ∧ b < c * a :=
  let ⟨c, hc₀, hc⟩ := exists_pos_mul_lt h b;
  ⟨c⁻¹, inv_pos.2 hc₀, by rwa [← div_eq_inv_mul, lt_div_iff₀ hc₀]⟩

theorem min_div_div_right {c : α} (hc : 0 ≤ c) (a b : α) : min (a / c) (b / c) = min a b / c :=
  (monotone_div_right_of_nonneg hc).map_min.symm

theorem max_div_div_right {c : α} (hc : 0 ≤ c) (a b : α) : max (a / c) (b / c) = max a b / c :=
  (monotone_div_right_of_nonneg hc).map_max.symm

end LinearOrderedSemifield

section PartialOrderedField

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

attribute [local instance] PosMulReflectLT.toMulPosReflectLT

/-! ### Lemmas about pos, nonneg, nonpos, neg -/

/-- A version of `inv_lt_zero` which holds with different assumptions. In particular, the type
must be a field, not just a `GroupWithZero`, but the order assumptions replace `LinearOrder` and
`PosMulMono` with `PartialOrder`, `IsStrictOrderedRing` and `PosMulReflectLT`. Thus neither version
is more general than the other. This one applies, for instance, to `ℂ`. -/
theorem inv_lt_zero' : a⁻¹ < 0 ↔ a < 0 := by
  rw [← neg_pos, ← inv_neg, inv_pos, neg_pos]

/-- A version of `inv_nonpos` which holds with different assumptions. In particular, the type
must be a field, not just a `GroupWithZero`, but the order assumptions replace `LinearOrder` and
`PosMulMono` with `PartialOrder`, `IsStrictOrderedRing` and `PosMulReflectLT`. Thus neither version
is more general than the other. This one applies, for instance, to `ℂ`. -/
theorem inv_nonpos' : a⁻¹ ≤ 0 ↔ a ≤ 0 := by
  grind [inv_lt_zero', le_iff_eq_or_lt]

theorem div_nonneg_of_nonpos (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a / b :=
  div_eq_mul_inv a b ▸ mul_nonneg_of_nonpos_of_nonpos ha (inv_nonpos'.2 hb)

theorem div_pos_of_neg_of_neg (ha : a < 0) (hb : b < 0) : 0 < a / b :=
  div_eq_mul_inv a b ▸ mul_pos_of_neg_of_neg ha (inv_lt_zero'.2 hb)

theorem div_neg_of_neg_of_pos (ha : a < 0) (hb : 0 < b) : a / b < 0 :=
  div_eq_mul_inv a b ▸ mul_neg_of_neg_of_pos ha (inv_pos.2 hb)

theorem div_neg_of_pos_of_neg (ha : 0 < a) (hb : b < 0) : a / b < 0 :=
  div_eq_mul_inv a b ▸ mul_neg_of_pos_of_neg ha (inv_lt_zero'.2 hb)

/-! ### Relating one division with another term -/

theorem div_le_iff_of_neg (hc : c < 0) : b / c ≤ a ↔ a * c ≤ b where
  mp h := div_mul_cancel₀ b (ne_of_lt hc) ▸ mul_le_mul_of_nonpos_right h hc.le
  mpr h := calc
    a = a * c * (1 / c) := mul_mul_div a (ne_of_lt hc)
    _ ≥ b * (1 / c) := mul_le_mul_of_nonpos_right h <| inv_eq_one_div c ▸ (inv_lt_zero'.2 hc).le
    _ = b / c := (div_eq_mul_one_div b c).symm

theorem div_le_iff_of_neg' (hc : c < 0) : b / c ≤ a ↔ c * a ≤ b := by
  rw [mul_comm, div_le_iff_of_neg hc]

theorem le_div_iff_of_neg (hc : c < 0) : a ≤ b / c ↔ b ≤ a * c := by
  rw [← neg_neg c, mul_neg, div_neg, le_neg, div_le_iff₀ (neg_pos.2 hc), neg_mul]

theorem le_div_iff_of_neg' (hc : c < 0) : a ≤ b / c ↔ b ≤ c * a := by
  rw [mul_comm, le_div_iff_of_neg hc]

theorem div_lt_iff_of_neg (hc : c < 0) : b / c < a ↔ a * c < b where
  mp h := div_mul_cancel₀ b (ne_of_lt hc) ▸ mul_lt_mul_of_neg_right h hc
  mpr h := calc
    a = a * c * c⁻¹ := mul_inv_cancel_right₀ hc.ne _ |>.symm
    _ > b * c⁻¹ := mul_lt_mul_of_neg_right h <| inv_lt_zero'.2 hc
    _ = b / c := division_def b c |>.symm

theorem div_lt_iff_of_neg' (hc : c < 0) : b / c < a ↔ c * a < b := by
  rw [mul_comm, div_lt_iff_of_neg hc]

theorem lt_div_iff_of_neg (hc : c < 0) : a < b / c ↔ b < a * c := by
  rw [← neg_neg c, mul_neg, div_neg, lt_neg, div_lt_iff₀ (neg_pos.2 hc), neg_mul]

theorem lt_div_iff_of_neg' (hc : c < 0) : a < b / c ↔ b < c * a := by
  rw [mul_comm, lt_div_iff_of_neg hc]

theorem div_le_one_of_ge (h : b ≤ a) (hb : b ≤ 0) : a / b ≤ 1 := by
  simpa only [neg_div_neg_eq] using div_le_one_of_le₀ (neg_le_neg h) (neg_nonneg_of_nonpos hb)

/-! ### Bi-implications of inequalities using inversions -/

theorem inv_le_inv_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a := by
  rw [← one_div, div_le_iff_of_neg ha, ← div_eq_inv_mul, div_le_iff_of_neg hb, one_mul]

theorem inv_le_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ ≤ b ↔ b⁻¹ ≤ a := by
  rw [← inv_le_inv_of_neg hb (inv_lt_zero'.2 ha), inv_inv]

theorem le_inv_of_neg (ha : a < 0) (hb : b < 0) : a ≤ b⁻¹ ↔ b ≤ a⁻¹ := by
  rw [← inv_le_inv_of_neg (inv_lt_zero'.2 hb) ha, inv_inv]

theorem inv_lt_inv_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ < b⁻¹ ↔ b < a := by
  have := div_lt_iff_of_neg ha (b := 1) (a := b⁻¹)
  rwa [one_div, mul_comm b⁻¹, ← division_def, div_lt_iff_of_neg hb, one_mul] at this

theorem inv_lt_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ < b ↔ b⁻¹ < a := by
  simpa using inv_lt_inv_of_neg ha (inv_lt_zero'.2 hb)

theorem lt_inv_of_neg (ha : a < 0) (hb : b < 0) : a < b⁻¹ ↔ b < a⁻¹ := by
  simpa using inv_lt_inv_of_neg (inv_lt_zero'.2 ha) hb

/-!
### Monotonicity results involving inversion
-/


theorem sub_inv_antitoneOn_Ioi :
    AntitoneOn (fun x ↦ (x - c)⁻¹) (Set.Ioi c) :=
  antitoneOn_iff_forall_lt.mpr fun _ ha _ hb hab ↦
    inv_le_inv₀ (sub_pos.mpr hb) (sub_pos.mpr ha) |>.mpr <| sub_le_sub (le_of_lt hab) le_rfl

theorem sub_inv_antitoneOn_Iio :
    AntitoneOn (fun x ↦ (x - c)⁻¹) (Set.Iio c) :=
  antitoneOn_iff_forall_lt.mpr fun _ ha _ hb hab ↦
    inv_le_inv_of_neg (sub_neg.mpr hb) (sub_neg.mpr ha) |>.mpr <| sub_le_sub (le_of_lt hab) le_rfl

theorem sub_inv_antitoneOn_Icc_right (ha : c < a) :
    AntitoneOn (fun x ↦ (x - c)⁻¹) (Set.Icc a b) := by
  by_cases hab : a ≤ b
  · exact sub_inv_antitoneOn_Ioi.mono <| (Set.Icc_subset_Ioi_iff hab).mpr ha
  · simp [hab, Set.Subsingleton.antitoneOn]

theorem sub_inv_antitoneOn_Icc_left (ha : b < c) :
    AntitoneOn (fun x ↦ (x - c)⁻¹) (Set.Icc a b) := by
  by_cases hab : a ≤ b
  · exact sub_inv_antitoneOn_Iio.mono <| (Set.Icc_subset_Iio_iff hab).mpr ha
  · simp [hab, Set.Subsingleton.antitoneOn]

theorem inv_antitoneOn_Ioi :
    AntitoneOn (fun x : α ↦ x⁻¹) (Set.Ioi 0) := by
  convert! sub_inv_antitoneOn_Ioi (α := α)
  exact (sub_zero _).symm

theorem inv_antitoneOn_Iio :
    AntitoneOn (fun x : α ↦ x⁻¹) (Set.Iio 0) := by
  convert! sub_inv_antitoneOn_Iio (α := α)
  exact (sub_zero _).symm

theorem inv_antitoneOn_Icc_right (ha : 0 < a) :
    AntitoneOn (fun x : α ↦ x⁻¹) (Set.Icc a b) := by
  convert! sub_inv_antitoneOn_Icc_right ha
  exact (sub_zero _).symm

theorem inv_antitoneOn_Icc_left (hb : b < 0) :
    AntitoneOn (fun x : α ↦ x⁻¹) (Set.Icc a b) := by
  convert! sub_inv_antitoneOn_Icc_left hb
  exact (sub_zero _).symm

/-! ### Relating two divisions -/


theorem div_le_div_of_nonpos_of_le (hc : c ≤ 0) (h : b ≤ a) : a / c ≤ b / c := by
  rw [div_eq_mul_inv a c, div_eq_mul_inv b c]
  exact mul_le_mul_of_nonpos_right h (inv_nonpos'.2 hc)

theorem div_lt_div_of_neg_of_lt (hc : c < 0) (h : b < a) : a / c < b / c := by
  rw [div_eq_mul_inv a c, div_eq_mul_inv b c]
  exact mul_lt_mul_of_neg_right h (inv_lt_zero'.2 hc)

theorem div_le_div_right_of_neg (hc : c < 0) : a / c ≤ b / c ↔ b ≤ a := by
  rw [div_le_iff_of_neg hc, div_mul_cancel₀ _ hc.ne]

theorem div_lt_div_right_of_neg (hc : c < 0) : a / c < b / c ↔ b < a := by
  rw [div_lt_iff_of_neg hc, div_mul_cancel₀ _ hc.ne]

/-! ### Relating one division and involving `1` -/


theorem one_le_div_of_neg (hb : b < 0) : 1 ≤ a / b ↔ a ≤ b := by rw [le_div_iff_of_neg hb, one_mul]

theorem div_le_one_of_neg (hb : b < 0) : a / b ≤ 1 ↔ b ≤ a := by rw [div_le_iff_of_neg hb, one_mul]

theorem one_lt_div_of_neg (hb : b < 0) : 1 < a / b ↔ a < b := by rw [lt_div_iff_of_neg hb, one_mul]

theorem div_lt_one_of_neg (hb : b < 0) : a / b < 1 ↔ b < a := by rw [div_lt_iff_of_neg hb, one_mul]

theorem one_div_le_of_neg (ha : a < 0) (hb : b < 0) : 1 / a ≤ b ↔ 1 / b ≤ a := by
  simpa using inv_le_of_neg ha hb

theorem one_div_lt_of_neg (ha : a < 0) (hb : b < 0) : 1 / a < b ↔ 1 / b < a := by
  simpa using inv_lt_of_neg ha hb

theorem le_one_div_of_neg (ha : a < 0) (hb : b < 0) : a ≤ 1 / b ↔ b ≤ 1 / a := by
  simpa using le_inv_of_neg ha hb

theorem lt_one_div_of_neg (ha : a < 0) (hb : b < 0) : a < 1 / b ↔ b < 1 / a := by
  simpa using lt_inv_of_neg ha hb

/-! ### Relating two divisions, involving `1` -/


theorem one_div_le_one_div_of_neg_of_le (hb : b < 0) (h : a ≤ b) : 1 / b ≤ 1 / a := by
  rwa [div_le_iff_of_neg' hb, ← div_eq_mul_one_div, div_le_one_of_neg (h.trans_lt hb)]

theorem one_div_lt_one_div_of_neg_of_lt (hb : b < 0) (h : a < b) : 1 / b < 1 / a := by
  rwa [div_lt_iff_of_neg' hb, ← div_eq_mul_one_div, div_lt_one_of_neg (h.trans hb)]

theorem le_of_neg_of_one_div_le_one_div (hb : b < 0) (h : 1 / a ≤ 1 / b) : b ≤ a := by
  simpa using one_div_le_one_div_of_neg_of_le (one_div b ▸ inv_lt_zero'.2 hb) h

theorem lt_of_neg_of_one_div_lt_one_div (hb : b < 0) (h : 1 / a < 1 / b) : b < a := by
  simpa using one_div_lt_one_div_of_neg_of_lt (one_div b ▸ inv_lt_zero'.2 hb) h

/-- For the single implications with fewer assumptions, see `one_div_lt_one_div_of_neg_of_lt` and
  `lt_of_one_div_lt_one_div` -/
theorem one_div_le_one_div_of_neg (ha : a < 0) (hb : b < 0) : 1 / a ≤ 1 / b ↔ b ≤ a := by
  simpa [one_div] using inv_le_inv_of_neg ha hb

/-- For the single implications with fewer assumptions, see `one_div_lt_one_div_of_lt` and
  `lt_of_one_div_lt_one_div` -/
theorem one_div_lt_one_div_of_neg (ha : a < 0) (hb : b < 0) : 1 / a < 1 / b ↔ b < a := by
  simpa [one_div] using inv_lt_inv_of_neg ha hb

theorem one_div_lt_neg_one (h1 : a < 0) (h2 : -1 < a) : 1 / a < -1 :=
  suffices 1 / a < 1 / -1 by rwa [one_div_neg_one_eq_neg_one] at this
  one_div_lt_one_div_of_neg_of_lt h1 h2

theorem one_div_le_neg_one (h1 : a < 0) (h2 : -1 ≤ a) : 1 / a ≤ -1 :=
  suffices 1 / a ≤ 1 / -1 by rwa [one_div_neg_one_eq_neg_one] at this
  one_div_le_one_div_of_neg_of_le h1 h2

/-! ### Results about halving -/

omit [PosMulReflectLT α] in
theorem sub_self_div_two (a : α) : a - a / 2 = a / 2 := by
  grind

omit [PosMulReflectLT α] in
theorem div_two_sub_self (a : α) : a / 2 - a = -(a / 2) := by
  grind

theorem add_sub_div_two_lt (h : a < b) : a + (b - a) / 2 < b := by
  rwa [← div_sub_div_same, sub_eq_add_neg, add_comm (b / 2), ← add_assoc, ← sub_eq_add_neg, ←
    lt_sub_iff_add_lt, sub_self_div_two, sub_self_div_two,
    div_lt_div_iff_of_pos_right (zero_lt_two' α)]

/-- An inequality involving `2`. -/
theorem sub_one_div_inv_le_two (a2 : 2 ≤ a) : (1 - 1 / a)⁻¹ ≤ 2 := by
  -- Take inverses on both sides to obtain `2⁻¹ ≤ 1 - 1 / a`
  refine (inv_anti₀ (inv_pos.2 <| zero_lt_two' α) ?_).trans_eq (inv_inv (2 : α))
  -- move `1 / a` to the left and `2⁻¹` to the right.
  rw [le_sub_iff_add_le, add_comm, ← le_sub_iff_add_le]
  -- take inverses on both sides and use the assumption `2 ≤ a`.
  convert! (one_div a).le.trans (inv_anti₀ zero_lt_two a2) using 1
    -- show `1 - 1 / 2 = 1 / 2`.

  -- show `1 - 1 / 2 = 1 / 2`.
  rw [sub_eq_iff_eq_add, ← two_mul, mul_inv_cancel₀ two_ne_zero]

/-! ### Miscellaneous lemmas -/


omit [PosMulReflectLT α] in
theorem mul_sub_mul_div_mul_neg_iff (hc : c ≠ 0) (hd : d ≠ 0) :
    (a * d - b * c) / (c * d) < 0 ↔ a / c < b / d := by
  rw [mul_comm b c, ← div_sub_div _ _ hc hd, sub_lt_zero]

omit [PosMulReflectLT α] in
theorem mul_sub_mul_div_mul_nonpos_iff (hc : c ≠ 0) (hd : d ≠ 0) :
    (a * d - b * c) / (c * d) ≤ 0 ↔ a / c ≤ b / d := by
  rw [mul_comm b c, ← div_sub_div _ _ hc hd, sub_nonpos]

alias ⟨div_lt_div_of_mul_sub_mul_div_neg, mul_sub_mul_div_mul_neg⟩ := mul_sub_mul_div_mul_neg_iff

alias ⟨div_le_div_of_mul_sub_mul_div_nonpos, mul_sub_mul_div_mul_nonpos⟩ :=
  mul_sub_mul_div_mul_nonpos_iff

theorem exists_add_lt_and_pos_of_lt (h : b < a) : ∃ c, b + c < a ∧ 0 < c :=
  ⟨(a - b) / 2, add_sub_div_two_lt h, div_pos (sub_pos_of_lt h) zero_lt_two⟩

end PartialOrderedField

section LinearOrderedField

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a b c d : α} {n : ℤ}

theorem div_pos_iff : 0 < a / b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  simp only [division_def, mul_pos_iff, inv_pos, inv_lt_zero]

theorem div_neg_iff : a / b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b := by
  simp [division_def, mul_neg_iff]

theorem div_nonneg_iff : 0 ≤ a / b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  simp [division_def, mul_nonneg_iff]

theorem div_nonpos_iff : a / b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b := by
  simp [division_def, mul_nonpos_iff]

theorem one_lt_div_iff : 1 < a / b ↔ 0 < b ∧ b < a ∨ b < 0 ∧ a < b := by
  rcases lt_trichotomy b 0 with (hb | rfl | hb)
  · simp [hb, hb.not_gt, one_lt_div_of_neg]
  · simp [zero_le_one]
  · simp [hb, hb.not_gt, one_lt_div]

theorem one_le_div_iff : 1 ≤ a / b ↔ 0 < b ∧ b ≤ a ∨ b < 0 ∧ a ≤ b := by
  rcases lt_trichotomy b 0 with (hb | rfl | hb)
  · simp [hb, hb.not_gt, one_le_div_of_neg]
  · simp [zero_lt_one.not_ge]
  · simp [hb, hb.not_gt, one_le_div]

theorem div_lt_one_iff : a / b < 1 ↔ 0 < b ∧ a < b ∨ b = 0 ∨ b < 0 ∧ b < a := by
  rcases lt_trichotomy b 0 with (hb | rfl | hb)
  · simp [hb, hb.not_gt, hb.ne, div_lt_one_of_neg]
  · simp [zero_lt_one]
  · simp [hb, hb.not_gt, div_lt_one, hb.ne.symm]

theorem div_le_one_iff : a / b ≤ 1 ↔ 0 < b ∧ a ≤ b ∨ b = 0 ∨ b < 0 ∧ b ≤ a := by
  rcases lt_trichotomy b 0 with (hb | rfl | hb)
  · simp [hb, hb.not_gt, hb.ne, div_le_one_of_neg]
  · simp [zero_le_one]
  · simp [hb, hb.not_gt, div_le_one, hb.ne.symm]

theorem le_of_forall_sub_le (h : ∀ ε > 0, b - ε ≤ a) : b ≤ a := by
  contrapose! h
  simpa only [@and_comm ((0 : α) < _), lt_sub_iff_add_lt, gt_iff_lt] using
    exists_add_lt_and_pos_of_lt h

private lemma exists_lt_mul_left_of_nonneg {a b c : α} (ha : 0 ≤ a) (hc : 0 ≤ c) (h : c < a * b) :
    ∃ a' ∈ Set.Ico 0 a, c < a' * b := by
  have hb : 0 < b := pos_of_mul_pos_right (hc.trans_lt h) ha
  obtain ⟨a', ha', a_a'⟩ := exists_between ((div_lt_iff₀ hb).2 h)
  exact ⟨a', ⟨(div_nonneg hc hb.le).trans ha'.le, a_a'⟩, (div_lt_iff₀ hb).1 ha'⟩

private lemma exists_lt_mul_right_of_nonneg {a b c : α} (ha : 0 ≤ a) (hc : 0 ≤ c) (h : c < a * b) :
    ∃ b' ∈ Set.Ico 0 b, c < a * b' := by
  have hb : 0 < b := pos_of_mul_pos_right (hc.trans_lt h) ha
  simp_rw [mul_comm a] at h ⊢
  exact exists_lt_mul_left_of_nonneg hb.le hc h

private lemma exists_mul_left_lt₀ {a b c : α} (hc : a * b < c) : ∃ a' > a, a' * b < c := by
  rcases le_or_gt b 0 with hb | hb
  · obtain ⟨a', ha'⟩ := exists_gt a
    exact ⟨a', ha', hc.trans_le' (antitone_mul_right hb ha'.le)⟩
  · obtain ⟨a', ha', hc'⟩ := exists_between ((lt_div_iff₀ hb).2 hc)
    exact ⟨a', ha', (lt_div_iff₀ hb).1 hc'⟩

private lemma exists_mul_right_lt₀ {a b c : α} (hc : a * b < c) : ∃ b' > b, a * b' < c := by
  simp_rw [mul_comm a] at hc ⊢; exact exists_mul_left_lt₀ hc

lemma le_mul_of_forall_lt₀ {a b c : α} (h : ∀ a' > a, ∀ b' > b, c ≤ a' * b') : c ≤ a * b := by
  refine le_of_forall_gt_imp_ge_of_dense fun d hd ↦ ?_
  obtain ⟨a', ha', hd⟩ := exists_mul_left_lt₀ hd
  obtain ⟨b', hb', hd⟩ := exists_mul_right_lt₀ hd
  exact (h a' ha' b' hb').trans hd.le

lemma mul_le_of_forall_lt_of_nonneg {a b c : α} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (h : ∀ a' ≥ 0, a' < a → ∀ b' ≥ 0, b' < b → a' * b' ≤ c) : a * b ≤ c := by
  refine le_of_forall_lt_imp_le_of_dense fun d d_ab ↦ ?_
  rcases lt_or_ge d 0 with hd | hd
  · exact hd.le.trans hc
  obtain ⟨a', ha', d_ab⟩ := exists_lt_mul_left_of_nonneg ha hd d_ab
  obtain ⟨b', hb', d_ab⟩ := exists_lt_mul_right_of_nonneg ha'.1 hd d_ab
  exact d_ab.le.trans (h a' ha'.1 ha'.2 b' hb'.1 hb'.2)

  -- surely there is an easier proof of this, or we already have something like it somewhere.
  -- It doesn't even need `α` to be a field, so it doesn't belong in this file.
theorem mul_self_inj_of_nonneg {α : Type*} [CommRing α] [NoZeroDivisors α] [PartialOrder α]
    [IsStrictOrderedRing α] {a b : α} (a0 : 0 ≤ a) (b0 : 0 ≤ b) :
    a * a = b * b ↔ a = b := by
  have := fun h ↦ le_antisymm (neg_nonneg.mp h) b0
  grind [sq_sub_sq, mul_eq_zero, add_eq_zero_iff_eq_neg]

theorem min_div_div_right_of_nonpos (hc : c ≤ 0) (a b : α) : min (a / c) (b / c) = max a b / c :=
  Eq.symm <| Antitone.map_max fun _ _ => div_le_div_of_nonpos_of_le hc

theorem max_div_div_right_of_nonpos (hc : c ≤ 0) (a b : α) : max (a / c) (b / c) = min a b / c :=
  Eq.symm <| Antitone.map_min fun _ _ => div_le_div_of_nonpos_of_le hc

@[simp, grind =]
theorem abs_inv (a : α) : |a⁻¹| = |a|⁻¹ :=
  map_inv₀ (absHom : α →*₀ α) a

@[grind =]
theorem abs_div (a b : α) : |a / b| = |a| / |b| :=
  map_div₀ (absHom : α →*₀ α) a b

theorem abs_one_div (a : α) : |1 / a| = 1 / |a| := by rw [abs_div, abs_one]

theorem uniform_continuous_npow_on_bounded (B : α) {ε : α} (hε : 0 < ε) (n : ℕ) :
    ∃ δ > 0, ∀ q r : α, |r| ≤ B → |q - r| ≤ δ → |q ^ n - r ^ n| < ε := by
  wlog! B_pos : 0 < B generalizing B
  · have ⟨δ, δ_pos, cont⟩ := this 1 zero_lt_one
    exact ⟨δ, δ_pos, fun q r hr ↦ cont q r (hr.trans (B_pos.trans zero_le_one))⟩
  have pos : 0 < 1 + ↑n * (B + 1) ^ (n - 1) := zero_lt_one.trans_le <| le_add_of_nonneg_right <|
    mul_nonneg n.cast_nonneg <| (pow_pos (B_pos.trans <| lt_add_of_pos_right _ zero_lt_one) _).le
  refine ⟨min 1 (ε / (1 + n * (B + 1) ^ (n - 1))), lt_min zero_lt_one (div_pos hε pos),
    fun q r hr hqr ↦ (abs_pow_sub_pow_le ..).trans_lt ?_⟩
  rw [le_inf_iff, le_div_iff₀ pos, mul_one_add, ← mul_assoc] at hqr
  obtain h | h := (abs_nonneg (q - r)).eq_or_lt
  · simpa only [← h, zero_mul] using hε
  refine (lt_of_le_of_lt ?_ <| lt_add_of_pos_left _ h).trans_le hqr.2
  gcongr
  · exact mul_nonneg (abs_nonneg _) n.cast_nonneg
  · exact (abs_nonneg _).trans le_sup_left
  refine max_le ?_ (hr.trans <| le_add_of_nonneg_right zero_le_one)
  exact add_sub_cancel r q ▸ (abs_add_le ..).trans (add_le_add hr hqr.1)

lemma two_mul_le_add_mul_sq {ε : α} (hε : 0 < ε) :
    2 * a * b ≤ ε * a ^ 2 + ε⁻¹ * b ^ 2 := by
  have h : 2 * (ε * a) * b ≤ (ε * a) ^ 2 + b ^ 2 := two_mul_le_add_sq (ε * a) b
  calc 2 * a * b
  _ = 2 * a * b * (ε * ε⁻¹) := by rw [mul_inv_cancel₀ hε.ne', mul_one]
  _ = (2 * (ε * a) * b) * ε⁻¹ := by simp_rw [mul_assoc, mul_comm ε, mul_assoc]
  _ ≤ ((ε * a) ^ 2 + b ^ 2) * ε⁻¹ := by gcongr; exact inv_nonneg.mpr hε.le
  _ = ε * a ^ 2 + ε⁻¹ * b ^ 2 := by
    rw [mul_comm _ ε⁻¹, mul_pow, mul_add, ← mul_assoc, pow_two, ← mul_assoc, inv_mul_cancel₀ hε.ne',
      one_mul]

end LinearOrderedField

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

section PositivityExt

variable {α : Type*} [GroupWithZero α] [PartialOrder α]
variable {a b : α}

lemma div_nonneg_of_pos_of_nonneg [PosMulReflectLT α] (ha : 0 < a) (hb : 0 ≤ b) :
    0 ≤ a / b :=
  div_nonneg ha.le hb

lemma div_nonneg_of_nonneg_of_pos [PosMulReflectLT α] (ha : 0 ≤ a) (hb : 0 < b) :
    0 ≤ a / b :=
  div_nonneg ha hb.le

lemma div_ne_zero_of_pos_of_ne_zero (ha : 0 < a) (hb : b ≠ 0) : a / b ≠ 0 :=
  div_ne_zero ha.ne' hb

lemma div_ne_zero_of_ne_zero_of_pos (ha : a ≠ 0) (hb : 0 < b) : a / b ≠ 0 :=
  div_ne_zero ha hb.ne'

lemma zpow_zero_pos {α : Type*} [Semifield α] [PartialOrder α] [IsStrictOrderedRing α]
    (a : α) : 0 < a ^ (0 : ℤ) :=
  zero_lt_one.trans_eq (zpow_zero a).symm

/-- The `positivity` extension which identifies expressions of the form `a / b`,
such that `positivity` successfully recognises both `a` and `b`. -/
@[positivity _ / _] meta def evalDiv : PositivityExt where eval {u α} zα pα? e := do
  let .app (.app (f : Q($α → $α → $α)) (a : Q($α))) (b : Q($α)) ← withReducible (whnf e)
    | throwError "not /"
  let _e_eq : $e =Q $f $a $b := ⟨⟩
  trace[Tactic.positivity.zeroness] "evalDiv: {a} divided by {b}"
  let _a ← synthInstanceQ q(Semifield $α)
  let ⟨_f_eq⟩ ← withDefault <| withNewMCtxDepth <| assertDefEqQ q($f) q(HDiv.hDiv)
  let some pα := pα? |
    match ← core zα pα? a, ← core zα pα? b with
    | .nonzero pa, .nonzero pb =>
      let _a ← synthInstanceQ q(GroupWithZero $α)
      assumeInstancesCommute
      pure (.nonzero q(div_ne_zero $pa $pb))
    | _, _ => pure .none
  let _a ← synthInstanceQ q(GroupWithZero $α)
  let _a ← synthInstanceQ q(PosMulReflectLT $α)
  assumeInstancesCommute
  let ra ← core zα pα a; let rb ← core zα pα b
  match ra, rb with
  | .positive pa, .positive pb => pure (.positive q(div_pos $pa $pb))
  | .positive pa, .nonnegative pb => pure (.nonnegative q(div_nonneg_of_pos_of_nonneg $pa $pb))
  | .nonnegative pa, .positive pb => pure (.nonnegative q(div_nonneg_of_nonneg_of_pos $pa $pb))
  | .nonnegative pa, .nonnegative pb => pure (.nonnegative q(div_nonneg $pa $pb))
  | .positive pa, .nonzero pb => pure (.nonzero q(div_ne_zero_of_pos_of_ne_zero $pa $pb))
  | .nonzero pa, .positive pb => pure (.nonzero q(div_ne_zero_of_ne_zero_of_pos $pa $pb))
  | .nonzero pa, .nonzero pb => pure (.nonzero q(div_ne_zero $pa $pb))
  | _, _ => pure .none

/-- The `positivity` extension which identifies expressions of the form `a⁻¹`,
such that `positivity` successfully recognises `a`. -/
@[positivity _⁻¹]
meta def evalInv : PositivityExt where eval {u α} zα pα? e := do
  let .app (f : Q($α → $α)) (a : Q($α)) ← withReducible (whnf e) | throwError "not ⁻¹"
  let _e_eq : $e =Q $f $a := ⟨⟩
  let _a ← synthInstanceQ q(Semifield $α)
  let ⟨_f_eq⟩ ← withDefault <| withNewMCtxDepth <| assertDefEqQ q($f) q(Inv.inv)
  let some _ := pα? |
    match ← core zα pα? a with
    | .nonzero pa =>
      let _a ← synthInstanceQ q(GroupWithZero $α)
      assumeInstancesCommute
      pure (.nonzero q(inv_ne_zero $pa))
    | _ => pure .none
  let _a ← synthInstanceQ q(GroupWithZero $α)
  let _a ← synthInstanceQ q(PartialOrder $α)
  let _a ← synthInstanceQ q(PosMulReflectLT $α)
  assumeInstancesCommute
  let ra ← core zα pα? a
  match ra with
  | .positive pa =>
    assumeInstancesCommute
    pure (.positive q(inv_pos_of_pos $pa))
  | .nonnegative pa =>
    assumeInstancesCommute
    pure (.nonnegative q(inv_nonneg_of_nonneg $pa))
  | .nonzero pa => pure (.nonzero q(inv_ne_zero $pa))
  | .none => pure .none

/-- The `positivity` extension which identifies expressions of the form `a ^ (0:ℤ)`. -/
@[positivity _ ^ (0 : ℤ), Pow.pow _ (0 : ℤ)]
meta def evalPowZeroInt : PositivityExt where eval {u α} _zα pα? e := do
  let .app (.app _ (a : Q($α))) _ ← withReducible (whnf e) | throwError "not ^"
  let some _ := pα? | pure .none
  let _a ← synthInstanceQ q(Semifield $α)
  let _a ← synthInstanceQ q(LinearOrder $α)
  let _a ← synthInstanceQ q(IsStrictOrderedRing $α)
  assumeInstancesCommute
  let ⟨_a⟩ ← Qq.assertDefEqQ q($e) q($a ^ (0 : ℤ))
  pure (.positive q(zpow_zero_pos $a))

end PositivityExt

end Mathlib.Meta.Positivity
