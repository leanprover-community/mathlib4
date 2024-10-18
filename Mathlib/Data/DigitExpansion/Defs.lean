/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Order.Fin
import Mathlib.Order.SuccPred.Basic
import Mathlib.Tactic.Ring


/-!
# Defining reals without the use of rationals

* [Defining reals without the use of rationals][debruijn1976]

-/

/-- A possibly infinite sequence of digits in `Fin (b + 1)`, which
can represent a number system like the reals.
It is constrained to not end in an infinite string of the top digit. -/
structure DigitExpansion (Z : Type*) [LT Z] (b : ℕ) where
  /-- The digit sequence, such that `b` is the base - 1. -/
  toFun : Z → Fin (b + 1)
  /-- The constraint that the sequence does not trail end infinitely at the top digit. -/
  bounded' : ¬∃ i₀, ∀ i > i₀, toFun i = b

namespace DigitExpansion

instance funLike (Z : Type*) [LT Z] (b : ℕ) : FunLike (DigitExpansion Z b) Z (Fin (b + 1))
    where
  coe := DigitExpansion.toFun
  coe_injective' := by rintro ⟨⟩ ⟨⟩; simp


variable {Z : Type*} [LT Z] {b : ℕ} (f g : DigitExpansion Z b) (i : Z)

@[ext]
theorem ext {f g : DigitExpansion Z b} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp]
theorem toFun_apply : f.toFun i = f i :=
  rfl

@[simp]
theorem mk_apply (f : Z → Fin (b + 1)) (hf) : (⟨f, hf⟩ : DigitExpansion Z b) i = f i :=
  rfl

open Order

theorem exists_bounded {Z : Type*} [LT Z] {b : ℕ} (f : DigitExpansion Z b) (z : Z) :
    ∃ x > z, f x < b := by
  have := f.bounded'
  push_neg at this
  refine' (this z).imp fun x => And.imp_right _
  cases' (Fin.le_last (f x)).eq_or_lt with h h
  · simp [h, Fin.ext_iff]
  · intro
    simpa [Fin.lt_iff_val_lt_val] using h

instance {Z : Type*} [Preorder Z] [SuccOrder Z] [NoMaxOrder Z] {b : ℕ} [hb : NeZero b] :
    Zero (DigitExpansion Z b) :=
  ⟨{  toFun := (0 : Z → Fin (b + 1))
      bounded' := by
        push_neg
        intro x
        refine' ⟨succ x, lt_succ _, _⟩
        simp [Fin.ext_iff, hb.out.symm] }⟩

@[simp]
theorem zero_apply {Z : Type*} [Preorder Z] [SuccOrder Z] [NoMaxOrder Z] {b : ℕ} [NeZero b]
    (z : Z) : (0 : DigitExpansion Z b) z = 0 :=
  rfl

section difcar

variable {Z : Type*} [LT Z] {b : ℕ}
  [∀ (f g : DigitExpansion Z b) z, Decidable (∃ x > z, f x < g x ∧ ∀ y < x, z < y → f y ≤ g y)]
  (f g : DigitExpansion Z b)

/-- Difference carry as an auxiliary function for defining subtraction. -/
def difcar : Z → Fin (b + 1) := fun z =>
  if ∃ x > z, f x < g x ∧ ∀ y < x, z < y → f y ≤ g y then 1 else 0

variable {f g : DigitExpansion Z b}

theorem difcar_eq_one_iff [hb : NeZero b] {z : Z} :
    difcar f g z = 1 ↔ ∃ x > z, f x < g x ∧ ∀ y < x, z < y → f y ≤ g y := by
  dsimp [difcar]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · refine ⟨fun H => absurd H ?_, fun H => absurd H h⟩
    simp [hb.out]

theorem difcar_eq_zero_iff [hb : NeZero b] {z : Z}:
    difcar f g z = 0 ↔ ∀ x > z, f x < g x → ∃ y : Z, y < x ∧ z < y ∧ g y < f y := by
  dsimp [difcar]
  split_ifs with h
  · refine ⟨fun H => absurd H.symm ?_, fun _ => absurd h ?_⟩
    · simp [hb.out]
    · push_neg
      assumption
  · push_neg at h
    exact ⟨fun _ => h, fun _ => rfl⟩

variable (f g : DigitExpansion Z b)

theorem difcar_eq_zero_or_one [NeZero b] (x : Z) : difcar f g x = 0 ∨ difcar f g x = 1 := by
  rw [difcar_eq_zero_iff, difcar_eq_one_iff]
  refine' (em' _).imp_left _
  push_neg
  exact id

theorem difcar_le_one [NeZero b] (x : Z) : difcar f g x ≤ 1 := by
  cases' difcar_eq_zero_or_one f g x with h h <;> simp [h]

variable {Z : Type*} [PartialOrder Z] [SuccOrder Z] [NoMaxOrder Z] [PredOrder Z] [NoMinOrder Z]
  {b : ℕ}
  [∀ (f g : DigitExpansion Z b) z, Decidable (∃ x > z, f x < g x ∧ ∀ y < x, z < y → f y ≤ g y)]
variable {f g : DigitExpansion Z b}

theorem difcar_pred_eq_one [NeZero b] {z : Z} (h : f z < g z) : difcar f g (pred z) = 1 := by
  rw [difcar_eq_one_iff]
  refine' ⟨z, pred_lt _, h, fun y hyz hy => _⟩
  rw [pred_lt_iff_eq_or_lt_of_not_isMin] at hy
  · rcases hy with (rfl | hy)
    · exact absurd hyz (lt_irrefl _)
    · exact absurd hyz hy.not_lt
  · exact not_isMin z

theorem difcar_pred_eq_zero [NeZero b] {z : Z} (h : g z < f z) : difcar f g (pred z) = 0 := by
  rw [difcar_eq_zero_iff]
  intro x hx hfgx
  rcases(le_of_pred_lt hx).eq_or_lt with (rfl | hz)
  · exact absurd hfgx h.not_lt
  exact ⟨z, hz, pred_lt _, h⟩

theorem difcar_pred_eq_difcar [NeZero b] {z : Z} (h : f z = g z) :
    difcar f g (pred z) = difcar f g z := by
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
theorem difcar_zero_right [NeZero b] (f : DigitExpansion Z b) (z : Z) : difcar f 0 z = 0 := by
  simp [difcar_eq_zero_iff]

@[simp]
theorem difcar_self [NeZero b] (f : DigitExpansion Z b) (z : Z) : difcar f f z = 0 := by
  simp [difcar_eq_zero_iff]

end difcar

section sign

variable {Z : Type*} [Preorder Z] [SuccOrder Z] [NoMaxOrder Z] {b : ℕ} [NeZero b]
    (f : DigitExpansion Z b)

/-- A sequence is positive iff it is not zero and has a left-tail of solely digit 0. -/
protected def Positive : Prop :=
  f ≠ 0 ∧ ∃ x, ∀ y < x, f y = 0

/-- A sequence is negative iff it is not zero and has a left-tail of solely the top digit. -/
protected def Negative : Prop :=
  f ≠ 0 ∧ ∃ x, ∀ y < x, f y = b

theorem not_positive_zero :
    ¬DigitExpansion.Positive (0 : DigitExpansion Z b) :=
  fun H => H.left rfl

theorem not_negative_zero :
    ¬DigitExpansion.Negative (0 : DigitExpansion Z b) :=
  fun H => H.left rfl

lemma not_positive_of_isEmpty {Z : Type*} [IsEmpty Z] [Preorder Z] [SuccOrder Z] [NoMaxOrder Z]
    {b : ℕ} [NeZero b] (f : DigitExpansion Z b) : ¬DigitExpansion.Positive f := by
  rintro ⟨hne, -, -⟩
  simp [DFunLike.ext_iff] at hne

lemma not_negative_of_isEmpty {Z : Type*} [IsEmpty Z] [Preorder Z] [SuccOrder Z] [NoMaxOrder Z]
    {b : ℕ} [NeZero b] (f : DigitExpansion Z b) : ¬DigitExpansion.Negative f := by
  rintro ⟨hne, -, -⟩
  simp [DFunLike.ext_iff] at hne

end sign

section cutoff

/-- An auxiliary function that truncates the right-tail of a sequence by setting that tail to
all digit 0. Such truncation preserves order. -/
def cutoff {Z : Type*} [LT Z] [DecidableRel (α := Z) (· < ·)] {b : ℕ} [hb : NeZero b] (z : Z)
    (f : DigitExpansion Z b) : DigitExpansion Z b :=
  ⟨fun x => if z < x then 0 else f x, by
    rintro ⟨y, hy⟩
    obtain ⟨w, hwy, hw⟩ := f.exists_bounded y
    specialize hy w hwy
    simp only at hy
    have : (b : Fin (b + 1)) = Fin.last b := by
      rw [← Fin.val_last b, Fin.cast_val_eq_self]
      simp
    rw [this] at hy hw
    split_ifs at hy
    · cases b
      · exact absurd rfl hb.out
      · exact (Fin.last_pos : 0 < Fin.last _).ne hy
    · exact hw.ne hy⟩

theorem cutoff_apply_le {Z : Type*} [Preorder Z] [DecidableRel (α := Z) (· < ·)] {b : ℕ} [NeZero b]
    (f : DigitExpansion Z b) (z x : Z) (h : x ≤ z) : f.cutoff z x = f x :=
  if_neg (not_lt_of_le h)

@[simp]
theorem cutoff_apply_self {Z : Type*} [Preorder Z] [DecidableRel (α := Z) (· < ·)] {b : ℕ}
    [NeZero b] (f : DigitExpansion Z b) (z : Z) : f.cutoff z z = f z :=
  cutoff_apply_le _ _ _ le_rfl

theorem cutoff_apply_lt {Z : Type*} [LT Z] [DecidableRel (α := Z) (· < ·)] {b : ℕ} [NeZero b]
    (f : DigitExpansion Z b) (z x : Z) (h : z < x) : f.cutoff z x = 0 :=
  if_pos h

theorem cutoff_cutoff_of_le {Z : Type*} [LinearOrder Z] {b : ℕ} [NeZero b]
    (f : DigitExpansion Z b) {z x : Z} (h : x ≤ z) : cutoff x (cutoff z f) = cutoff x f := by
  ext y
  cases' le_or_lt y x with hyx hyx
  · rw [cutoff_apply_le _ _ _ hyx, cutoff_apply_le _ _ _ hyx, cutoff_apply_le _ _ _ (hyx.trans h)]
  · rw [cutoff_apply_lt _ _ _ hyx, cutoff_apply_lt _ _ _ hyx]

@[simp]
lemma cutoff_idem {Z : Type*} [LinearOrder Z] {b : ℕ} [NeZero b]
    (f : DigitExpansion Z b) (z : Z) : (cutoff z (cutoff z f)) = cutoff z f :=
  cutoff_cutoff_of_le _ le_rfl

variable {Z : Type*} [LinearOrder Z] [SuccOrder Z] [NoMaxOrder Z] [PredOrder Z] [NoMinOrder Z]
    [IsSuccArchimedean Z] {b : ℕ} [hb : NeZero b]

@[simp] lemma cutoff_zero (z : Z) : cutoff z (0 : DigitExpansion Z b) = 0 := by
  ext y
  cases' le_or_lt y z with h h
  · rw [cutoff_apply_le _ _ _ h]
  · rw [cutoff_apply_lt _ _ _ h, zero_apply]

lemma Negative.negative_cutoff {f : DigitExpansion Z b} (hf : f.Negative) (z : Z) :
    (f.cutoff z).Negative := by
  obtain ⟨hne, x, hx⟩ := hf
  refine' ⟨λ H => _, min x z, λ y hy => _⟩
  · replace H : f.cutoff z (min z (pred x)) = 0 := by rw [H, zero_apply]
    cases' b with b
    · exact absurd rfl hb.out
    · refine' (Fin.last_pos : 0 < Fin.last (Nat.succ b)).ne _
      rw [← Fin.cast_val_eq_self (Fin.last _), Fin.val_last, ← hx (min z (pred x)), ← H,
          cutoff_apply_le] <;>
      simp
  · rw [lt_min_iff] at hy
    rw [cutoff_apply_le _ _ _ hy.right.le, hx _ hy.left]

lemma negative_cutoff_iff {f : DigitExpansion Z b} {z : Z} :
    (f.cutoff z).Negative ↔ f.Negative := by
  refine' ⟨_, fun h => Negative.negative_cutoff h z⟩
  rintro ⟨hne, x, hx⟩
  refine' ⟨_, x, _⟩
  · contrapose! hne
    simp [hne]
  intro y hy
  rw [← cutoff_apply_le _ z]
  · exact hx y hy
  contrapose! hx
  refine' ⟨y, hy, _⟩
  rw [cutoff_apply_lt _ _ _ hx]
  simp [Fin.ext_iff, hb.out.symm]

variable
  [∀ (f g : DigitExpansion Z b) z, Decidable (∃ x > z, f x < g x ∧ ∀ y < x, z < y → f y ≤ g y)]

lemma difcar_cutoff_cutoff_of_le (f g : DigitExpansion Z b) (z x : Z) (hx : z ≤ x) :
    difcar (f.cutoff z) (g.cutoff z) x = 0 := by
  rw [difcar_eq_zero_iff]
  intros y hy hy'
  simp [cutoff_apply_lt _ _ _ (hx.trans_lt hy)] at hy'

end cutoff

section single

variable {Z : Type*} [LinearOrder Z] [SuccOrder Z] [NoMaxOrder Z] [PredOrder Z]
    [NoMinOrder Z] [IsSuccArchimedean Z] {b : ℕ} [hb : NeZero b]

/-- An auxiliary function defining a sequence that has the specified digit at the specified
position, and 0 elsewhere. Compare to `Pi.single`. Not included in the de Bruijn paper.
The resulting sequence is real. See `DigitExpansion.real.single` for the direct construction. -/
def single (z : Z) (n : Fin (b + 1)) :
    DigitExpansion Z b where
  toFun := fun x => if z = x then n else 0
  bounded' := by
    rintro ⟨x, hx⟩
    specialize hx (succ (max x z)) (by simp)
    dsimp only at hx
    rw [if_neg, Fin.ext_iff, Fin.val_zero] at hx
    · refine hb.out ?_
      simp [hx]
    · cases' le_total x z with h h
      · simp [h, (lt_succ z).ne]
      · simp [h, ((lt_succ x).trans_le' h).ne]

@[simp]
lemma single_apply_self (z : Z) (n : Fin (b + 1)) : single z n z = n := if_pos rfl

@[simp]
lemma single_apply_of_ne (z x : Z) (n : Fin (b + 1)) (h : z ≠ x) : single z n x = 0 := if_neg h

@[simp]
lemma single_zero (z : Z) : single z (0 : Fin (b + 1)) = 0 := by
  ext x
  rcases eq_or_ne z x with rfl|hx
  · simp
  · simp [hx]

@[simp]
lemma single_eq_zero_iff {z : Z} {n : Fin (b + 1)} : single z n = 0 ↔ n = 0 := by
  constructor
  · intro H
    rw [DFunLike.ext_iff] at H
    simpa using H z
  · simp (config := {contextual := true})

lemma single_positive_of_ne_zero (z : Z) {n : Fin (b + 1)} (hn : n ≠ 0) : (single z n).Positive :=
  ⟨by simp [hn], z, fun x hx => by simp [hx.ne']⟩

variable
  [∀ (f g : DigitExpansion Z b) z, Decidable (∃ x > z, f x < g x ∧ ∀ y < x, z < y → f y ≤ g y)]

lemma difcar_single_single_eq_zero_of_le {z x : Z} (n m : Fin (b + 1)) (h : z ≤ x) :
    difcar (single z n) (single z m) x = 0 := by
  rw [difcar_eq_zero_iff]
  intro _ hy
  simp [(hy.trans_le' h).ne]

@[simp]
lemma difcar_single_single_self (z : Z) (n m : Fin (b + 1)) :
    difcar (single z n) (single z m) z = 0 :=
  difcar_single_single_eq_zero_of_le _ _ le_rfl

lemma difcar_single_single_of_lt_eq_zero_iff_le
    {z x : Z} {n m : Fin (b + 1)} (hx : x < z) :
    difcar (single z n) (single z m) x = 0 ↔ m ≤ n := by
  rw [difcar_eq_zero_iff]
  constructor
  · contrapose!
    intro H
    refine ⟨z, hx, by simp [H], ?_⟩
    intro y hy
    simp [hy.ne']
  · intro h y hy
    rcases eq_or_ne z y with rfl|hz
    · simp [h.not_lt]
    · simp [hz]

lemma difcar_single_single_of_lt_eq_one_iff_lt
    {z x : Z} {n m : Fin (b + 1)} (hx : x < z) :
    difcar (single z n) (single z m) x = 1 ↔ n < m := by
  rw [← not_le, iff_not_comm, ← difcar_single_single_of_lt_eq_zero_iff_le hx]
  cases' difcar_eq_zero_or_one (single z n) (single z m) x with H H <;>
  simp [H, hb.out]

@[simp]
lemma difcar_self_single_eq_zero (f : DigitExpansion Z b) (z x : Z) :
    difcar f (single z (f z)) x = 0 := by
  rw [difcar_eq_zero_iff (f := f) (g := single z (f z))]
  intro y hy hy'
  rcases eq_or_ne z y with rfl|hz
  · simp at hy'
  · simp [single_apply_of_ne _ _ _ hz] at hy'

end single

section shift

variable {Z : Type*} [PartialOrder Z] [PredOrder Z] [SuccOrder Z] [NoMaxOrder Z] {b : ℕ}

/-- "Divide" the expansion by shifting the expansion one digit to the right. Also called
"half" in the orignal de Bruijn paper. -/
def shift (f : DigitExpansion Z b) : DigitExpansion Z b :=
  ⟨fun z ↦ f (pred z),
   fun ⟨i, hi⟩ ↦ f.bounded' ⟨i, fun j hj ↦ by simpa using hi (succ j) (hj.trans (lt_succ _))⟩⟩

@[simp]
lemma shift_apply (f : DigitExpansion Z b) (z : Z) : shift f z = f (pred z) := rfl

@[simp]
lemma shift_zero [NeZero b] : shift (0 : DigitExpansion Z b) = 0 := rfl

@[simp]
lemma shift_eq_zero [NeZero b] {f : DigitExpansion Z b} : shift f = 0 ↔ f = 0 :=
  ⟨fun h ↦ ext fun z ↦ by simpa using DFunLike.ext_iff.mp h (succ z) , congr_arg _⟩

lemma Positive.shift [NeZero b] {f : DigitExpansion Z b} (hf : f.Positive) :
    (shift f).Positive :=
  ⟨by simpa using hf.left,
   hf.right.imp fun x hx y hy ↦ by simpa using hx (pred y) ((pred_le _).trans_lt hy)⟩

lemma Negative.shift [NeZero b] {f : DigitExpansion Z b} (hf : f.Negative) :
    (shift f).Negative :=
  ⟨by simpa using hf.left,
   hf.right.imp fun x hx y hy ↦ by simpa using hx (pred y) ((pred_le _).trans_lt hy)⟩

@[simp]
lemma shift_single {Z : Type*} [LinearOrder Z] [SuccOrder Z] [NoMaxOrder Z] [PredOrder Z]
    [NoMinOrder Z] {b : ℕ} [hb : NeZero b](z : Z) (n : Fin (b + 1)) :
    shift (single z n) = single (succ z) n := by
  ext x
  rcases lt_trichotomy (pred x) z with h|rfl|h
  · have : x < succ z := by simpa using succ_lt_succ h
    simp [h.ne', this.ne']
  · simp
  · have : succ z < x := by simpa using succ_lt_succ h
    simp [h.ne, this.ne]

end shift

section left_shift

variable {Z : Type*} [PartialOrder Z] [PredOrder Z] [SuccOrder Z] [NoMaxOrder Z]
  [NoMinOrder Z] {b : ℕ}

/-- "Multiply" the expansion by shifting the expansion one digit to the left.
The inverse to `DigitExpansion.shift`. -/
def leftShift (f : DigitExpansion Z b) : DigitExpansion Z b :=
  ⟨fun z ↦ f (succ z),
   fun ⟨i, hi⟩ ↦ f.bounded' ⟨succ i, fun j hj ↦ by
    simpa [pred_succ] using hi (pred j) (by simpa using pred_lt_pred hj)⟩⟩

@[simp]
lemma leftShift_apply (f : DigitExpansion Z b) (z : Z) : leftShift f z = f (succ z) := rfl

lemma leftInverse_shift_leftShift :
    Function.LeftInverse (α := DigitExpansion Z b) shift leftShift :=
  fun _ ↦ ext <| by simp

lemma leftInverse_leftShift_shift :
    Function.LeftInverse (α := DigitExpansion Z b) leftShift shift :=
  fun _ ↦ ext <| by simp

@[simp]
lemma leftShift_zero [NeZero b] : shift (0 : DigitExpansion Z b) = 0 := rfl

@[simp]
lemma leftShift_eq_zero [NeZero b] {f : DigitExpansion Z b} : leftShift f = 0 ↔ f = 0 := by
  rw [← leftInverse_leftShift_shift.injective.eq_iff, leftInverse_shift_leftShift]
  simp

lemma Positive.of_shift [NeZero b] {f : DigitExpansion Z b} (hf : f.shift.Positive) :
    f.Positive :=
  ⟨by simpa using hf.left, by
   obtain ⟨x, hx⟩ := hf.right
   refine ⟨pred x, fun y hy ↦ ?_⟩
   simpa using hx (succ y) (by simpa using succ_lt_succ hy)⟩

lemma Negative.of_shift [NeZero b] {f : DigitExpansion Z b} (hf : f.shift.Negative) :
    f.Negative :=
  ⟨by simpa using hf.left, by
   obtain ⟨x, hx⟩ := hf.right
   refine ⟨pred x, fun y hy ↦ ?_⟩
   simpa using hx (succ y) (by simpa using succ_lt_succ hy)⟩

lemma Positive.leftShift [NeZero b] {f : DigitExpansion Z b} (hf : f.Positive) :
    (leftShift f).Positive := by
  rw [← leftInverse_shift_leftShift f] at hf
  exact hf.of_shift

lemma Negative.leftShift [NeZero b] {f : DigitExpansion Z b} (hf : f.Negative) :
    (leftShift f).Negative := by
  rw [← leftInverse_shift_leftShift f] at hf
  exact hf.of_shift

lemma Positive.of_leftShift [NeZero b] {f : DigitExpansion Z b} (hf : f.leftShift.Positive) :
    f.Positive := by
  rw [← leftInverse_shift_leftShift f]
  exact hf.shift

lemma Negative.of_leftShift [NeZero b] {f : DigitExpansion Z b} (hf : f.leftShift.Negative) :
    f.Negative := by
  rw [← leftInverse_shift_leftShift f]
  exact hf.shift

@[simp]
lemma leftShift_single {Z : Type*} [LinearOrder Z] [SuccOrder Z] [NoMaxOrder Z] [PredOrder Z]
    [NoMinOrder Z] {b : ℕ} [hb : NeZero b] (z : Z) (n : Fin (b + 1)) :
    leftShift (single z n) = single (pred z) n := by
  rw [eq_comm, ← leftInverse_leftShift_shift (single _ _), shift_single, succ_pred]

end left_shift

end DigitExpansion
