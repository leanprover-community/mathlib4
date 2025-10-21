/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Ordinal.Family

/-! # Ordinal exponential

In this file we define the power function and the logarithm function on ordinals. The two are
related by the lemma `Ordinal.opow_le_iff_le_log : b ^ c ≤ x ↔ c ≤ log b x` for nontrivial inputs
`b`, `c`.
-/

noncomputable section

open Function Set Equiv Order
open scoped Cardinal Ordinal

universe u v w

namespace Ordinal

/-- The ordinal exponential, defined by transfinite recursion.

We call this `opow` in theorems in order to disambiguate from other exponentials. -/
instance instPow : Pow Ordinal Ordinal :=
  ⟨fun a b ↦ if a = 0 then 1 - b else
    limitRecOn b 1 (fun _ x ↦ x * a) fun o _ f ↦ ⨆ x : Iio o, f x.1 x.2⟩

private theorem opow_of_ne_zero {a b : Ordinal} (h : a ≠ 0) : a ^ b =
    limitRecOn b 1 (fun _ x ↦ x * a) fun o _ f ↦ ⨆ x : Iio o, f x.1 x.2 :=
  if_neg h

/-- `0 ^ a = 1` if `a = 0` and `0 ^ a = 0` otherwise. -/
theorem zero_opow' (a : Ordinal) : 0 ^ a = 1 - a :=
  if_pos rfl

theorem zero_opow_le (a : Ordinal) : (0 : Ordinal) ^ a ≤ 1 := by
  rw [zero_opow']
  exact sub_le_self 1 a

@[simp]
theorem zero_opow {a : Ordinal} (a0 : a ≠ 0) : (0 : Ordinal) ^ a = 0 := by
  rwa [zero_opow', Ordinal.sub_eq_zero_iff_le, one_le_iff_ne_zero]

@[simp]
theorem opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1 := by
  obtain rfl | h := eq_or_ne a 0
  · rw [zero_opow', Ordinal.sub_zero]
  · rw [opow_of_ne_zero h, limitRecOn_zero]

@[simp]
theorem opow_succ (a b : Ordinal) : a ^ succ b = a ^ b * a := by
  obtain rfl | h := eq_or_ne a 0
  · rw [zero_opow (succ_ne_zero b), mul_zero]
  · rw [opow_of_ne_zero h, opow_of_ne_zero h, limitRecOn_succ]

theorem opow_limit {a b : Ordinal} (ha : a ≠ 0) (hb : IsSuccLimit b) :
    a ^ b = ⨆ x : Iio b, a ^ x.1 := by
  simp_rw [opow_of_ne_zero ha, limitRecOn_limit _ _ _ _ hb]

theorem opow_le_of_isSuccLimit {a b c : Ordinal} (a0 : a ≠ 0) (h : IsSuccLimit b) :
    a ^ b ≤ c ↔ ∀ b' < b, a ^ b' ≤ c := by
  rw [opow_limit a0 h, Ordinal.iSup_le_iff, Subtype.forall]
  rfl

@[deprecated (since := "2025-07-08")]
alias opow_le_of_limit := opow_le_of_isSuccLimit

theorem lt_opow_of_isSuccLimit {a b c : Ordinal} (b0 : b ≠ 0) (h : IsSuccLimit c) :
    a < b ^ c ↔ ∃ c' < c, a < b ^ c' := by
  simpa using (opow_le_of_isSuccLimit b0 h).not

@[deprecated (since := "2025-07-08")]
alias lt_opow_of_limit := lt_opow_of_isSuccLimit

@[simp]
theorem opow_one (a : Ordinal) : a ^ (1 : Ordinal) = a := by
  rw [← succ_zero, opow_succ]
  simp only [opow_zero, one_mul]

@[simp]
theorem one_opow (a : Ordinal) : (1 : Ordinal) ^ a = 1 := by
  induction a using limitRecOn with
  | zero => simp only [opow_zero]
  | succ _ ih =>
    simp only [opow_succ, ih, mul_one]
  | limit b l IH =>
    refine eq_of_forall_ge_iff fun c => ?_
    rw [opow_le_of_isSuccLimit Ordinal.one_ne_zero l]
    exact ⟨fun H => by simpa only [opow_zero] using H 0 l.bot_lt, fun H b' h => by rwa [IH _ h]⟩

theorem opow_pos {a : Ordinal} (b : Ordinal) (a0 : 0 < a) : 0 < a ^ b := by
  have h0 : 0 < a ^ (0 : Ordinal) := by simp only [opow_zero, zero_lt_one]
  induction b using limitRecOn with
  | zero => exact h0
  | succ b IH =>
    rw [opow_succ]
    exact mul_pos IH a0
  | limit b l _ =>
    exact (lt_opow_of_isSuccLimit (Ordinal.pos_iff_ne_zero.1 a0) l).2 ⟨0, l.bot_lt, h0⟩

theorem opow_ne_zero {a : Ordinal} (b : Ordinal) (a0 : a ≠ 0) : a ^ b ≠ 0 :=
  Ordinal.pos_iff_ne_zero.1 <| opow_pos b <| Ordinal.pos_iff_ne_zero.2 a0

@[simp]
theorem opow_eq_zero {a b : Ordinal} : a ^ b = 0 ↔ a = 0 ∧ b ≠ 0 := by
  by_cases a = 0 <;> by_cases b = 0 <;> simp_all [opow_ne_zero]

@[simp, norm_cast]
theorem opow_natCast (a : Ordinal) (n : ℕ) : a ^ (n : Ordinal) = a ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, opow_zero, pow_zero]
  | succ n IH => rw [Nat.cast_succ, add_one_eq_succ, opow_succ, pow_succ, IH]

theorem isNormal_opow {a : Ordinal} (h : 1 < a) : IsNormal (a ^ ·) := by
  have ha : 0 < a := zero_lt_one.trans h
  refine IsNormal.of_succ_lt ?_ fun hl ↦ ?_
  · simpa only [mul_one, opow_succ] using fun b ↦ mul_lt_mul_of_pos_left h (opow_pos b ha)
  · simp [IsLUB, IsLeast, upperBounds, lowerBounds, ← opow_le_of_isSuccLimit ha.ne' hl]

@[simp]
theorem opow_lt_opow_iff_right {a b c : Ordinal} (a1 : 1 < a) : a ^ b < a ^ c ↔ b < c :=
  (isNormal_opow a1).lt_iff

@[simp]
theorem opow_le_opow_iff_right {a b c : Ordinal} (a1 : 1 < a) : a ^ b ≤ a ^ c ↔ b ≤ c :=
  (isNormal_opow a1).le_iff

@[simp]
theorem opow_right_inj {a b c : Ordinal} (a1 : 1 < a) : a ^ b = a ^ c ↔ b = c :=
  (isNormal_opow a1).inj

theorem isSuccLimit_opow {a b : Ordinal} (a1 : 1 < a) : IsSuccLimit b → IsSuccLimit (a ^ b) :=
  (isNormal_opow a1).isSuccLimit

@[deprecated (since := "2025-07-08")]
alias isLimit_opow := isSuccLimit_opow

theorem isSuccLimit_opow_left {a b : Ordinal} (l : IsSuccLimit a) (hb : b ≠ 0) :
    IsSuccLimit (a ^ b) := by
  rcases zero_or_succ_or_isSuccLimit b with (e | ⟨b, rfl⟩ | l')
  · exact absurd e hb
  · rw [opow_succ]
    exact isSuccLimit_mul (opow_pos _ l.bot_lt) l
  · exact isSuccLimit_opow (one_lt_of_isSuccLimit l) l'

@[deprecated (since := "2025-07-08")]
alias isLimit_opow_left := isSuccLimit_opow_left

theorem opow_le_opow_right {a b c : Ordinal} (h₁ : 0 < a) (h₂ : b ≤ c) : a ^ b ≤ a ^ c := by
  rcases (one_le_iff_pos.2 h₁).eq_or_lt' with h₁ | h₁
  · simp_all
  · exact (opow_le_opow_iff_right h₁).2 h₂

theorem opow_le_opow_left {a b : Ordinal} (c : Ordinal) (ab : a ≤ b) : a ^ c ≤ b ^ c := by
  by_cases ha : a = 0
  · by_cases c = 0 <;> simp_all
  · induction c using limitRecOn with
    | zero => simp
    | succ c IH => simpa using mul_le_mul' IH ab
    | limit c l IH =>
      exact (opow_le_of_isSuccLimit ha l).2 fun b' h ↦
        (IH _ h).trans (opow_le_opow_right ((Ordinal.pos_iff_ne_zero.2 ha).trans_le ab) h.le)

theorem opow_le_opow {a b c d : Ordinal} (hac : a ≤ c) (hbd : b ≤ d) (hc : 0 < c) : a ^ b ≤ c ^ d :=
  (opow_le_opow_left b hac).trans (opow_le_opow_right hc hbd)

theorem left_le_opow (a : Ordinal) {b : Ordinal} (b1 : 0 < b) : a ≤ a ^ b := by
  nth_rw 1 [← opow_one a]
  rcases le_or_gt a 1 with a1 | a1
  · rcases lt_or_eq_of_le a1 with a0 | a1
    · rw [lt_one_iff_zero] at a0
      rw [a0, zero_opow Ordinal.one_ne_zero]
      exact Ordinal.zero_le _
    rw [a1, one_opow, one_opow]
  rwa [opow_le_opow_iff_right a1, one_le_iff_pos]

theorem left_lt_opow {a b : Ordinal} (ha : 1 < a) (hb : 1 < b) : a < a ^ b := by
  conv_lhs => rw [← opow_one a]
  rwa [opow_lt_opow_iff_right ha]

theorem right_le_opow {a : Ordinal} (b : Ordinal) (a1 : 1 < a) : b ≤ a ^ b :=
  (isNormal_opow a1).le_apply

theorem opow_lt_opow_left_of_succ {a b c : Ordinal} (ab : a < b) : a ^ succ c < b ^ succ c := by
  rw [opow_succ, opow_succ]
  exact (mul_le_mul_right' (opow_le_opow_left c ab.le) a).trans_lt <|
    mul_lt_mul_of_pos_left ab <| opow_pos c <| (Ordinal.zero_le a).trans_lt ab

theorem opow_add (a b c : Ordinal) : a ^ (b + c) = a ^ b * a ^ c := by
  rcases eq_or_ne a 0 with (rfl | a0)
  · rcases eq_or_ne c 0 with (rfl | c0)
    · simp
    have : b + c ≠ 0 := ((Ordinal.pos_iff_ne_zero.2 c0).trans_le (le_add_left _ _)).ne'
    simp only [zero_opow c0, zero_opow this, mul_zero]
  rcases eq_or_lt_of_le (one_le_iff_ne_zero.2 a0) with (rfl | a1)
  · simp only [one_opow, mul_one]
  induction c using limitRecOn with
  | zero => simp
  | succ c IH =>
    rw [add_succ, opow_succ, IH, opow_succ, mul_assoc]
  | limit c l IH =>
    refine
      eq_of_forall_ge_iff fun d =>
        (((isNormal_opow a1).trans (isNormal_add_right b)).limit_le l).trans ?_
    dsimp only [Function.comp_def]
    simp +contextual only [IH]
    exact
      (((isNormal_mul_right <| opow_pos b (Ordinal.pos_iff_ne_zero.2 a0)).trans
              (isNormal_opow a1)).limit_le
          l).symm

theorem opow_one_add (a b : Ordinal) : a ^ (1 + b) = a * a ^ b := by rw [opow_add, opow_one]

theorem opow_dvd_opow (a : Ordinal) {b c : Ordinal} (h : b ≤ c) : a ^ b ∣ a ^ c :=
  ⟨a ^ (c - b), by rw [← opow_add, Ordinal.add_sub_cancel_of_le h]⟩

theorem opow_dvd_opow_iff {a b c : Ordinal} (a1 : 1 < a) : a ^ b ∣ a ^ c ↔ b ≤ c :=
  ⟨fun h =>
    le_of_not_gt fun hn =>
      not_le_of_gt ((opow_lt_opow_iff_right a1).2 hn) <|
        le_of_dvd (opow_ne_zero _ <| one_le_iff_ne_zero.1 <| a1.le) h,
    opow_dvd_opow _⟩

theorem opow_mul (a b c : Ordinal) : a ^ (b * c) = (a ^ b) ^ c := by
  by_cases b0 : b = 0; · simp only [b0, zero_mul, opow_zero, one_opow]
  by_cases a0 : a = 0
  · subst a
    by_cases c0 : c = 0
    · simp only [c0, mul_zero, opow_zero]
    simp only [zero_opow b0, zero_opow c0, zero_opow (mul_ne_zero b0 c0)]
  rcases eq_or_lt_of_le (one_le_iff_ne_zero.2 a0) with a1 | a1
  · subst a1
    simp only [one_opow]
  induction c using limitRecOn with
  | zero => simp only [mul_zero, opow_zero]
  | succ c IH =>
    rw [mul_succ, opow_add, IH, opow_succ]
  | limit c l IH =>
    refine
      eq_of_forall_ge_iff fun d =>
        (((isNormal_opow a1).trans (isNormal_mul_right (Ordinal.pos_iff_ne_zero.2 b0))).limit_le
              l).trans
          ?_
    dsimp only [Function.comp_def]
    simp +contextual only [IH]
    exact (opow_le_of_isSuccLimit (opow_ne_zero _ a0) l).symm

theorem opow_mul_add_pos {b v : Ordinal} (hb : b ≠ 0) (u : Ordinal) (hv : v ≠ 0) (w : Ordinal) :
    0 < b ^ u * v + w :=
  (opow_pos u <| Ordinal.pos_iff_ne_zero.2 hb).trans_le <|
    (le_mul_left _ <| Ordinal.pos_iff_ne_zero.2 hv).trans <| le_add_right _ _

theorem opow_mul_add_lt_opow_mul {b u w x : Ordinal} {v : Ordinal} (hw : w < b ^ u) (hv : v < x) :
    b ^ u * v + w < b ^ u * x := by
  apply lt_of_lt_of_le (b := b ^ u * (v + 1))
  · rwa [mul_add_one, add_lt_add_iff_left]
  · exact mul_le_mul_left' (add_one_le_of_lt hv) _

@[deprecated opow_mul_add_lt_opow_mul (since := "2025-08-27")]
theorem opow_mul_add_lt_opow_mul_succ {b u w : Ordinal} (v : Ordinal) (hw : w < b ^ u) :
    b ^ u * v + w < b ^ u * succ v :=
  opow_mul_add_lt_opow_mul hw (lt_succ v)

theorem opow_mul_add_lt_opow {b u v w x : Ordinal} (hv : v < b) (hw : w < b ^ u) (hu : u < x) :
    b ^ u * v + w < b ^ x := by
  apply (opow_mul_add_lt_opow_mul hw hv).trans_le
  rw [← opow_succ]
  exact opow_le_opow_right hv.pos (succ_le_of_lt hu)

@[deprecated opow_mul_add_lt_opow_succ (since := "2025-08-27")]
theorem opow_mul_add_lt_opow_succ {b u v w : Ordinal} (hvb : v < b) (hw : w < b ^ u) :
    b ^ u * v + w < b ^ succ u :=
  opow_mul_add_lt_opow hvb hw (lt_succ u)

/-! ### Ordinal logarithm -/

/-- The ordinal logarithm is the solution `u` to the equation `x = b ^ u * v + w` where `v < b` and
`w < b ^ u`. -/
@[pp_nodot]
def log (b : Ordinal) (x : Ordinal) : Ordinal :=
  if 1 < b then pred (sInf { o | x < b ^ o }) else 0

/-- The set in the definition of `log` is nonempty. -/
private theorem log_nonempty {b x : Ordinal} (h : 1 < b) : { o : Ordinal | x < b ^ o }.Nonempty :=
  ⟨_, succ_le_iff.1 (right_le_opow _ h)⟩

theorem log_def {b : Ordinal} (h : 1 < b) (x : Ordinal) : log b x = pred (sInf { o | x < b ^ o }) :=
  if_pos h

theorem log_of_left_le_one {b : Ordinal} (h : b ≤ 1) (x : Ordinal) : log b x = 0 :=
  if_neg h.not_gt

@[simp]
theorem log_zero_left : ∀ b, log 0 b = 0 :=
  log_of_left_le_one zero_le_one

@[simp]
theorem log_zero_right (b : Ordinal) : log b 0 = 0 := by
  obtain hb | hb := lt_or_ge 1 b
  · rw [log_def hb, ← Ordinal.le_zero, pred_le_iff_le_succ, succ_zero]
    apply csInf_le'
    rw [mem_setOf, opow_one]
    exact bot_lt_of_lt hb
  · rw [log_of_left_le_one hb]

@[simp]
theorem log_one_left : ∀ b, log 1 b = 0 :=
  log_of_left_le_one le_rfl

theorem succ_log_def {b x : Ordinal} (hb : 1 < b) (hx : x ≠ 0) :
    succ (log b x) = sInf { o : Ordinal | x < b ^ o } := by
  let t := sInf { o : Ordinal | x < b ^ o }
  have : x < b ^ t := csInf_mem (log_nonempty hb)
  rcases zero_or_succ_or_isSuccLimit t with (h | h | h)
  · refine ((one_le_iff_ne_zero.2 hx).not_gt ?_).elim
    simpa only [h, opow_zero] using this
  · rw [log_def hb x, succ_pred_eq_iff_not_isSuccPrelimit, not_isSuccPrelimit_iff']
    simpa [eq_comm] using h
  · rcases (lt_opow_of_isSuccLimit (zero_lt_one.trans hb).ne' h).1 this with ⟨a, h₁, h₂⟩
    exact h₁.not_ge.elim ((le_csInf_iff'' (log_nonempty hb)).1 le_rfl a h₂)

theorem lt_opow_succ_log_self {b : Ordinal} (hb : 1 < b) (x : Ordinal) :
    x < b ^ succ (log b x) := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · apply opow_pos _ (zero_lt_one.trans hb)
  · rw [succ_log_def hb hx]
    exact csInf_mem (log_nonempty hb)

theorem opow_log_le_self (b : Ordinal) {x : Ordinal} (hx : x ≠ 0) : b ^ log b x ≤ x := by
  rcases eq_or_ne b 0 with (rfl | b0)
  · exact (zero_opow_le _).trans (one_le_iff_ne_zero.2 hx)
  rcases lt_or_eq_of_le (one_le_iff_ne_zero.2 b0) with (hb | rfl)
  · refine le_of_not_gt fun h => (lt_succ (log b x)).not_ge ?_
    have := @csInf_le' _ _ { o | x < b ^ o } _ h
    rwa [← succ_log_def hb hx] at this
  · rwa [one_opow, one_le_iff_ne_zero]

/-- `opow b` and `log b` (almost) form a Galois connection.

See `opow_le_iff_le_log'` for a variant assuming `c ≠ 0` rather than `x ≠ 0`. See also
`le_log_of_opow_le` and `opow_le_of_le_log`, which are both separate implications under weaker
assumptions. -/
theorem opow_le_iff_le_log {b x c : Ordinal} (hb : 1 < b) (hx : x ≠ 0) :
    b ^ c ≤ x ↔ c ≤ log b x := by
  constructor <;>
  intro h
  · apply le_of_not_gt
    intro hn
    apply (lt_opow_succ_log_self hb x).not_ge <|
      ((opow_le_opow_iff_right hb).2 <| succ_le_of_lt hn).trans h
  · exact ((opow_le_opow_iff_right hb).2 h).trans <| opow_log_le_self b hx

/-- `opow b` and `log b` (almost) form a Galois connection.

See `opow_le_iff_le_log` for a variant assuming `x ≠ 0` rather than `c ≠ 0`. See also
`le_log_of_opow_le` and `opow_le_of_le_log`, which are both separate implications under weaker
assumptions. -/
theorem opow_le_iff_le_log' {b x c : Ordinal} (hb : 1 < b) (hc : c ≠ 0) :
    b ^ c ≤ x ↔ c ≤ log b x := by
  obtain rfl | hx := eq_or_ne x 0
  · simp [hc, (zero_lt_one.trans hb).ne']
  · exact opow_le_iff_le_log hb hx

theorem le_log_of_opow_le {b x c : Ordinal} (hb : 1 < b) (h : b ^ c ≤ x) : c ≤ log b x := by
  obtain rfl | hx := eq_or_ne x 0
  · rw [Ordinal.le_zero, opow_eq_zero] at h
    exact (zero_lt_one.asymm <| h.1 ▸ hb).elim
  · exact (opow_le_iff_le_log hb hx).1 h

theorem opow_le_of_le_log {b x c : Ordinal} (hc : c ≠ 0) (h : c ≤ log b x) : b ^ c ≤ x := by
  obtain hb | hb := le_or_gt b 1
  · rw [log_of_left_le_one hb] at h
    exact (h.not_gt (Ordinal.pos_iff_ne_zero.2 hc)).elim
  · rwa [opow_le_iff_le_log' hb hc]

/-- `opow b` and `log b` (almost) form a Galois connection.

See `lt_opow_iff_log_lt'` for a variant assuming `c ≠ 0` rather than `x ≠ 0`. See also
`lt_opow_of_log_lt` and `lt_log_of_lt_opow`, which are both separate implications under weaker
assumptions. -/
theorem lt_opow_iff_log_lt {b x c : Ordinal} (hb : 1 < b) (hx : x ≠ 0) : x < b ^ c ↔ log b x < c :=
  lt_iff_lt_of_le_iff_le (opow_le_iff_le_log hb hx)

/-- `opow b` and `log b` (almost) form a Galois connection.

See `lt_opow_iff_log_lt` for a variant assuming `x ≠ 0` rather than `c ≠ 0`. See also
`lt_opow_of_log_lt` and `lt_log_of_lt_opow`, which are both separate implications under weaker
assumptions. -/
theorem lt_opow_iff_log_lt' {b x c : Ordinal} (hb : 1 < b) (hc : c ≠ 0) : x < b ^ c ↔ log b x < c :=
  lt_iff_lt_of_le_iff_le (opow_le_iff_le_log' hb hc)

theorem lt_opow_of_log_lt {b x c : Ordinal} (hb : 1 < b) : log b x < c → x < b ^ c :=
  lt_imp_lt_of_le_imp_le <| le_log_of_opow_le hb

theorem lt_log_of_lt_opow {b x c : Ordinal} (hc : c ≠ 0) : x < b ^ c → log b x < c :=
  lt_imp_lt_of_le_imp_le <| opow_le_of_le_log hc

theorem log_pos {b o : Ordinal} (hb : 1 < b) (ho : o ≠ 0) (hbo : b ≤ o) : 0 < log b o := by
  rwa [← succ_le_iff, succ_zero, ← opow_le_iff_le_log hb ho, opow_one]

theorem log_eq_zero {b o : Ordinal} (hbo : o < b) : log b o = 0 := by
  rcases eq_or_ne o 0 with (rfl | ho)
  · exact log_zero_right b
  rcases le_or_gt b 1 with hb | hb
  · rcases le_one_iff.1 hb with (rfl | rfl)
    · exact log_zero_left o
    · exact log_one_left o
  · rwa [← Ordinal.le_zero, ← lt_succ_iff, succ_zero, ← lt_opow_iff_log_lt hb ho, opow_one]

@[mono]
theorem log_mono_right (b : Ordinal) {x y : Ordinal} (xy : x ≤ y) : log b x ≤ log b y := by
  obtain rfl | hx := eq_or_ne x 0
  · simp_rw [log_zero_right, Ordinal.zero_le]
  · obtain hb | hb := lt_or_ge 1 b
    · exact (opow_le_iff_le_log hb (hx.bot_lt.trans_le xy).ne').1 <|
        (opow_log_le_self _ hx).trans xy
    · rw [log_of_left_le_one hb, log_of_left_le_one hb]

theorem log_le_self (b x : Ordinal) : log b x ≤ x := by
  obtain rfl | hx := eq_or_ne x 0
  · rw [log_zero_right]
  · obtain hb | hb := lt_or_ge 1 b
    · exact (right_le_opow _ hb).trans (opow_log_le_self b hx)
    · simp_rw [log_of_left_le_one hb, Ordinal.zero_le]

@[simp]
theorem log_one_right (b : Ordinal) : log b 1 = 0 := by
  obtain hb | hb := lt_or_ge 1 b
  · exact log_eq_zero hb
  · exact log_of_left_le_one hb 1

theorem mod_opow_log_lt_self (b : Ordinal) {o : Ordinal} (ho : o ≠ 0) : o % (b ^ log b o) < o := by
  rcases eq_or_ne b 0 with (rfl | hb)
  · simpa using Ordinal.pos_iff_ne_zero.2 ho
  · exact (mod_lt _ <| opow_ne_zero _ hb).trans_le (opow_log_le_self _ ho)

theorem log_mod_opow_log_lt_log_self {b o : Ordinal} (hb : 1 < b) (hbo : b ≤ o) :
    log b (o % (b ^ log b o)) < log b o := by
  rcases eq_or_ne (o % (b ^ log b o)) 0 with h | h
  · rw [h, log_zero_right]
    exact log_pos hb (one_le_iff_ne_zero.1 (hb.le.trans hbo)) hbo
  · rw [← succ_le_iff, succ_log_def hb h]
    apply csInf_le'
    apply mod_lt
    rw [← Ordinal.pos_iff_ne_zero]
    exact opow_pos _ (zero_lt_one.trans hb)

theorem log_eq_iff {b x : Ordinal} (hb : 1 < b) (hx : x ≠ 0) (y : Ordinal) :
    log b x = y ↔ b ^ y ≤ x ∧ x < b ^ succ y := by
  constructor
  · rintro rfl
    use opow_log_le_self b hx, lt_opow_succ_log_self hb x
  · rintro ⟨hx₁, hx₂⟩
    apply le_antisymm
    · rwa [← lt_succ_iff, ← lt_opow_iff_log_lt hb hx]
    · rwa [← opow_le_iff_le_log hb hx]

theorem log_opow_mul_add {b u v w : Ordinal} (hb : 1 < b) (hv : v ≠ 0) (hw : w < b ^ u) :
    log b (b ^ u * v + w) = u + log b v := by
  rw [log_eq_iff hb]
  · constructor
    · rw [opow_add]
      exact (mul_le_mul_left' (opow_log_le_self b hv) _).trans (le_add_right _ w)
    · apply (add_lt_add_left hw _).trans_le
      rw [← mul_succ, ← add_succ, opow_add]
      apply mul_le_mul_left'
      rw [succ_le_iff]
      exact lt_opow_succ_log_self hb _
  · exact fun h ↦ mul_ne_zero (opow_ne_zero u (bot_lt_of_lt hb).ne') hv <|
      left_eq_zero_of_add_eq_zero h

theorem log_opow_mul {b v : Ordinal} (hb : 1 < b) (u : Ordinal) (hv : v ≠ 0) :
    log b (b ^ u * v) = u + log b v := by
  simpa using log_opow_mul_add hb hv (opow_pos u (bot_lt_of_lt hb))

theorem log_opow {b : Ordinal} (hb : 1 < b) (x : Ordinal) : log b (b ^ x) = x := by
  convert log_opow_mul hb x zero_ne_one.symm using 1
  · rw [mul_one]
  · rw [log_one_right, add_zero]

theorem div_opow_log_pos (b : Ordinal) {o : Ordinal} (ho : o ≠ 0) : 0 < o / (b ^ log b o) := by
  rcases eq_zero_or_pos b with (rfl | hb)
  · simpa using Ordinal.pos_iff_ne_zero.2 ho
  · rw [div_pos (opow_ne_zero _ hb.ne')]
    exact opow_log_le_self b ho

theorem div_opow_log_lt {b : Ordinal} (o : Ordinal) (hb : 1 < b) : o / (b ^ log b o) < b := by
  rw [div_lt (opow_pos _ (zero_lt_one.trans hb)).ne', ← opow_succ]
  exact lt_opow_succ_log_self hb o

theorem add_log_le_log_mul {x y : Ordinal} (b : Ordinal) (hx : x ≠ 0) (hy : y ≠ 0) :
    log b x + log b y ≤ log b (x * y) := by
  obtain hb | hb := lt_or_ge 1 b
  · rw [← opow_le_iff_le_log hb (mul_ne_zero hx hy), opow_add]
    exact mul_le_mul' (opow_log_le_self b hx) (opow_log_le_self b hy)
  · simpa only [log_of_left_le_one hb, zero_add] using le_rfl

theorem omega0_opow_mul_nat_lt {a b : Ordinal} (h : a < b) (n : ℕ) : ω ^ a * n < ω ^ b := by
  apply lt_of_lt_of_le _ (opow_le_opow_right omega0_pos (succ_le_of_lt h))
  rw [opow_succ]
  gcongr
  exacts [opow_pos a omega0_pos, nat_lt_omega0 n]

theorem lt_omega0_opow {a b : Ordinal} (hb : b ≠ 0) :
    a < ω ^ b ↔ ∃ c < b, ∃ n : ℕ, a < ω ^ c * n := by
  refine ⟨fun ha ↦ ⟨_, lt_log_of_lt_opow hb ha, ?_⟩,
    fun ⟨c, hc, n, hn⟩ ↦ hn.trans (omega0_opow_mul_nat_lt hc n)⟩
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt a one_lt_omega0)
  use n.succ
  rw [natCast_succ, ← hn]
  exact lt_mul_succ_div a (opow_ne_zero _ omega0_ne_zero)

theorem lt_omega0_opow_succ {a b : Ordinal} : a < ω ^ succ b ↔ ∃ n : ℕ, a < ω ^ b * n := by
  refine ⟨fun ha ↦ ?_, fun ⟨n, hn⟩ ↦ hn.trans (omega0_opow_mul_nat_lt (lt_succ b) n)⟩
  obtain ⟨c, hc, n, hn⟩ := (lt_omega0_opow (succ_ne_zero b)).1 ha
  refine ⟨n, hn.trans_le (mul_le_mul_right' ?_ _)⟩
  rwa [opow_le_opow_iff_right one_lt_omega0, ← lt_succ_iff]

/-! ### Interaction with `Nat.cast` -/

@[simp, norm_cast]
theorem natCast_opow (m : ℕ) : ∀ n : ℕ, ↑(m ^ n : ℕ) = (m : Ordinal) ^ (n : Ordinal)
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, natCast_mul, natCast_opow m n, Nat.cast_succ, add_one_eq_succ, opow_succ]

theorem iSup_pow {o : Ordinal} (ho : 0 < o) : ⨆ n : ℕ, o ^ n = o ^ ω := by
  simp_rw [← opow_natCast]
  rcases (one_le_iff_pos.2 ho).lt_or_eq with ho₁ | rfl
  · exact (isNormal_opow ho₁).apply_omega0
  · rw [one_opow]
    refine le_antisymm (Ordinal.iSup_le fun n => by rw [one_opow]) ?_
    exact_mod_cast Ordinal.le_iSup _ 0

end Ordinal

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: Port this meta code.

-- namespace Tactic

-- open Ordinal Mathlib.Meta.Positivity

-- /-- Extension for the `positivity` tactic: `ordinal.opow` takes positive values on positive
-- inputs. -/
-- @[positivity]
-- unsafe def positivity_opow : expr → tactic strictness
--   | q(@Pow.pow _ _ $(inst) $(a) $(b)) => do
--     let strictness_a ← core a
--     match strictness_a with
--       | positive p => positive <$> mk_app `` opow_pos [b, p]
--       | _ => failed
--   |-- We already know that `0 ≤ x` for all `x : Ordinal`
--     _ =>
--     failed

-- end Tactic
