/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Ordinal.Arithmetic

#align_import set_theory.ordinal.exponential from "leanprover-community/mathlib"@"b67044ba53af18680e1dd246861d9584e968495d"

/-! # Ordinal exponential

In this file we define the power function and the logarithm function on ordinals. The two are
related by the lemma `Ordinal.opow_le_iff_le_log : (b^c) ≤ x ↔ c ≤ log b x` for nontrivial inputs
`b`, `c`.
-/


noncomputable section

open Function Cardinal Set Equiv Order

open Classical Cardinal Ordinal

universe u v w

namespace Ordinal

/-- The ordinal exponential, defined by transfinite recursion. -/
instance pow : Pow Ordinal Ordinal :=
  ⟨fun a b => if a = 0 then 1 - b else limitRecOn b 1 (fun _ IH => IH * a) fun b _ => bsup.{u, u} b⟩

-- Porting note: Ambiguous notations.
-- local infixr:0 "^" => @Pow.pow Ordinal Ordinal Ordinal.instPowOrdinalOrdinal

theorem opow_def (a b : Ordinal) :
    (a^b) = if a = 0 then 1 - b else limitRecOn b 1 (fun _ IH => IH * a) fun b _ => bsup.{u, u} b :=
  rfl
#align ordinal.opow_def Ordinal.opow_def

-- Porting note: `if_pos rfl` → `if_true`
theorem zero_opow' (a : Ordinal) : (0^a) = 1 - a := by simp only [opow_def, if_true]
                                                       -- 🎉 no goals
#align ordinal.zero_opow' Ordinal.zero_opow'

@[simp]
theorem zero_opow {a : Ordinal} (a0 : a ≠ 0) : (0^a) = 0 := by
  rwa [zero_opow', Ordinal.sub_eq_zero_iff_le, one_le_iff_ne_zero]
  -- 🎉 no goals
#align ordinal.zero_opow Ordinal.zero_opow

@[simp]
theorem opow_zero (a : Ordinal) : (a^0) = 1 := by
  by_cases h : a = 0
  -- ⊢ a ^ 0 = 1
  · simp only [opow_def, if_pos h, sub_zero]
    -- 🎉 no goals
  · simp only [opow_def, if_neg h, limitRecOn_zero]
    -- 🎉 no goals
#align ordinal.opow_zero Ordinal.opow_zero

@[simp]
theorem opow_succ (a b : Ordinal) : (a^succ b) = (a^b) * a :=
  if h : a = 0 then by subst a; simp only [zero_opow (succ_ne_zero _), mul_zero]
                       -- ⊢ 0 ^ succ b = 0 ^ b * 0
                                -- 🎉 no goals
  else by simp only [opow_def, limitRecOn_succ, if_neg h]
          -- 🎉 no goals
#align ordinal.opow_succ Ordinal.opow_succ

theorem opow_limit {a b : Ordinal} (a0 : a ≠ 0) (h : IsLimit b) :
    (a^b) = bsup.{u, u} b fun c _ => a^c := by
  simp only [opow_def, if_neg a0]; rw [limitRecOn_limit _ _ _ _ h]
  -- ⊢ (limitRecOn b 1 (fun x IH => IH * a) fun b x => bsup b) = bsup b fun c x =>  …
                                   -- 🎉 no goals
#align ordinal.opow_limit Ordinal.opow_limit

theorem opow_le_of_limit {a b c : Ordinal} (a0 : a ≠ 0) (h : IsLimit b) :
    (a^b) ≤ c ↔ ∀ b' < b, (a^b') ≤ c := by rw [opow_limit a0 h, bsup_le_iff]
                                           -- 🎉 no goals
#align ordinal.opow_le_of_limit Ordinal.opow_le_of_limit

theorem lt_opow_of_limit {a b c : Ordinal} (b0 : b ≠ 0) (h : IsLimit c) :
    a < (b^c) ↔ ∃ c' < c, a < (b^c') := by
  rw [← not_iff_not, not_exists]; simp only [not_lt, opow_le_of_limit b0 h, exists_prop, not_and]
  -- ⊢ ¬a < b ^ c ↔ ∀ (x : Ordinal.{u_1}), ¬(x < c ∧ a < b ^ x)
                                  -- 🎉 no goals
#align ordinal.lt_opow_of_limit Ordinal.lt_opow_of_limit

@[simp]
theorem opow_one (a : Ordinal) : (a^1) = a := by
  rw [← succ_zero, opow_succ]; simp only [opow_zero, one_mul]
  -- ⊢ a ^ 0 * a = a
                               -- 🎉 no goals
#align ordinal.opow_one Ordinal.opow_one

@[simp]
theorem one_opow (a : Ordinal) : (1^a) = 1 := by
  induction a using limitRecOn with
  | H₁ => simp only [opow_zero]
  | H₂ _ ih =>
    simp only [opow_succ, ih, mul_one]
  | H₃ b l IH =>
    refine' eq_of_forall_ge_iff fun c => _
    rw [opow_le_of_limit Ordinal.one_ne_zero l]
    exact ⟨fun H => by simpa only [opow_zero] using H 0 l.pos, fun H b' h => by rwa [IH _ h]⟩
#align ordinal.one_opow Ordinal.one_opow

theorem opow_pos {a : Ordinal} (b) (a0 : 0 < a) : 0 < (a^b) := by
  have h0 : 0 < (a^0) := by simp only [opow_zero, zero_lt_one]
  -- ⊢ 0 < a ^ b
  induction b using limitRecOn with
  | H₁ => exact h0
  | H₂ b IH =>
    rw [opow_succ]
    exact mul_pos IH a0
  | H₃ b l _ =>
    exact (lt_opow_of_limit (Ordinal.pos_iff_ne_zero.1 a0) l).2 ⟨0, l.pos, h0⟩
#align ordinal.opow_pos Ordinal.opow_pos

theorem opow_ne_zero {a : Ordinal} (b) (a0 : a ≠ 0) : (a^b) ≠ 0 :=
  Ordinal.pos_iff_ne_zero.1 <| opow_pos b <| Ordinal.pos_iff_ne_zero.2 a0
#align ordinal.opow_ne_zero Ordinal.opow_ne_zero

theorem opow_isNormal {a : Ordinal} (h : 1 < a) : IsNormal ((·^·) a) :=
  have a0 : 0 < a := zero_lt_one.trans h
  ⟨fun b => by simpa only [mul_one, opow_succ] using (mul_lt_mul_iff_left (opow_pos b a0)).2 h,
               -- 🎉 no goals
    fun b l c => opow_le_of_limit (ne_of_gt a0) l⟩
#align ordinal.opow_is_normal Ordinal.opow_isNormal

theorem opow_lt_opow_iff_right {a b c : Ordinal} (a1 : 1 < a) : (a^b) < (a^c) ↔ b < c :=
  (opow_isNormal a1).lt_iff
#align ordinal.opow_lt_opow_iff_right Ordinal.opow_lt_opow_iff_right

theorem opow_le_opow_iff_right {a b c : Ordinal} (a1 : 1 < a) : (a^b) ≤ (a^c) ↔ b ≤ c :=
  (opow_isNormal a1).le_iff
#align ordinal.opow_le_opow_iff_right Ordinal.opow_le_opow_iff_right

theorem opow_right_inj {a b c : Ordinal} (a1 : 1 < a) : (a^b) = (a^c) ↔ b = c :=
  (opow_isNormal a1).inj
#align ordinal.opow_right_inj Ordinal.opow_right_inj

theorem opow_isLimit {a b : Ordinal} (a1 : 1 < a) : IsLimit b → IsLimit (a^b) :=
  (opow_isNormal a1).isLimit
#align ordinal.opow_is_limit Ordinal.opow_isLimit

theorem opow_isLimit_left {a b : Ordinal} (l : IsLimit a) (hb : b ≠ 0) : IsLimit (a^b) := by
  rcases zero_or_succ_or_limit b with (e | ⟨b, rfl⟩ | l')
  · exact absurd e hb
    -- 🎉 no goals
  · rw [opow_succ]
    -- ⊢ IsLimit (a ^ b * a)
    exact mul_isLimit (opow_pos _ l.pos) l
    -- 🎉 no goals
  · exact opow_isLimit l.one_lt l'
    -- 🎉 no goals
#align ordinal.opow_is_limit_left Ordinal.opow_isLimit_left

theorem opow_le_opow_right {a b c : Ordinal} (h₁ : 0 < a) (h₂ : b ≤ c) : (a^b) ≤ (a^c) := by
  cases' lt_or_eq_of_le (one_le_iff_pos.2 h₁) with h₁ h₁
  -- ⊢ a ^ b ≤ a ^ c
  · exact (opow_le_opow_iff_right h₁).2 h₂
    -- 🎉 no goals
  · subst a
    -- ⊢ 1 ^ b ≤ 1 ^ c
    -- Porting note: `le_refl` is required.
    simp only [one_opow, le_refl]
    -- 🎉 no goals
#align ordinal.opow_le_opow_right Ordinal.opow_le_opow_right

theorem opow_le_opow_left {a b : Ordinal} (c) (ab : a ≤ b) : (a^c) ≤ (b^c) := by
  by_cases a0 : a = 0
  -- ⊢ a ^ c ≤ b ^ c
  -- Porting note: `le_refl` is required.
  · subst a
    -- ⊢ 0 ^ c ≤ b ^ c
    by_cases c0 : c = 0
    -- ⊢ 0 ^ c ≤ b ^ c
    · subst c
      -- ⊢ 0 ^ 0 ≤ b ^ 0
      simp only [opow_zero, le_refl]
      -- 🎉 no goals
    · simp only [zero_opow c0, Ordinal.zero_le]
      -- 🎉 no goals
  · induction c using limitRecOn with
    | H₁ => simp only [opow_zero, le_refl]
    | H₂ c IH =>
      simpa only [opow_succ] using mul_le_mul' IH ab
    | H₃ c l IH =>
      exact
        (opow_le_of_limit a0 l).2 fun b' h =>
          (IH _ h).trans (opow_le_opow_right ((Ordinal.pos_iff_ne_zero.2 a0).trans_le ab) h.le)
#align ordinal.opow_le_opow_left Ordinal.opow_le_opow_left

theorem left_le_opow (a : Ordinal) {b : Ordinal} (b1 : 0 < b) : a ≤ (a^b) := by
  nth_rw 1 [← opow_one a]
  -- ⊢ a ^ 1 ≤ a ^ b
  cases' le_or_gt a 1 with a1 a1
  -- ⊢ a ^ 1 ≤ a ^ b
  · cases' lt_or_eq_of_le a1 with a0 a1
    -- ⊢ a ^ 1 ≤ a ^ b
    · rw [lt_one_iff_zero] at a0
      -- ⊢ a ^ 1 ≤ a ^ b
      rw [a0, zero_opow Ordinal.one_ne_zero]
      -- ⊢ 0 ≤ 0 ^ b
      exact Ordinal.zero_le _
      -- 🎉 no goals
    rw [a1, one_opow, one_opow]
    -- 🎉 no goals
  rwa [opow_le_opow_iff_right a1, one_le_iff_pos]
  -- 🎉 no goals
#align ordinal.left_le_opow Ordinal.left_le_opow

theorem right_le_opow {a : Ordinal} (b) (a1 : 1 < a) : b ≤ (a^b) :=
  (opow_isNormal a1).self_le _
#align ordinal.right_le_opow Ordinal.right_le_opow

theorem opow_lt_opow_left_of_succ {a b c : Ordinal} (ab : a < b) : (a^succ c) < (b^succ c) := by
  rw [opow_succ, opow_succ]
  -- ⊢ a ^ c * a < b ^ c * b
  exact
    (mul_le_mul_right' (opow_le_opow_left c ab.le) a).trans_lt
      (mul_lt_mul_of_pos_left ab (opow_pos c ((Ordinal.zero_le a).trans_lt ab)))
#align ordinal.opow_lt_opow_left_of_succ Ordinal.opow_lt_opow_left_of_succ

theorem opow_add (a b c : Ordinal) : a^(b + c) = (a^b) * (a^c) := by
  rcases eq_or_ne a 0 with (rfl | a0)
  -- ⊢ 0 ^ (b + c) = 0 ^ b * 0 ^ c
  · rcases eq_or_ne c 0 with (rfl | c0)
    -- ⊢ 0 ^ (b + 0) = 0 ^ b * 0 ^ 0
    · simp
      -- 🎉 no goals
    have : b + c ≠ 0 := ((Ordinal.pos_iff_ne_zero.2 c0).trans_le (le_add_left _ _)).ne'
    -- ⊢ 0 ^ (b + c) = 0 ^ b * 0 ^ c
    simp only [zero_opow c0, zero_opow this, mul_zero]
    -- 🎉 no goals
  rcases eq_or_lt_of_le (one_le_iff_ne_zero.2 a0) with (rfl | a1)
  -- ⊢ 1 ^ (b + c) = 1 ^ b * 1 ^ c
  · simp only [one_opow, mul_one]
    -- 🎉 no goals
  induction c using limitRecOn with
  | H₁ => simp
  | H₂ c IH =>
    rw [add_succ, opow_succ, IH, opow_succ, mul_assoc]
  | H₃ c l IH =>
    refine'
      eq_of_forall_ge_iff fun d =>
        (((opow_isNormal a1).trans (add_isNormal b)).limit_le l).trans _
    dsimp only [Function.comp]
    simp (config := { contextual := true }) only [IH]
    exact
      (((mul_isNormal <| opow_pos b (Ordinal.pos_iff_ne_zero.2 a0)).trans
              (opow_isNormal a1)).limit_le
          l).symm
#align ordinal.opow_add Ordinal.opow_add

theorem opow_one_add (a b : Ordinal) : a^(1 + b) = a * (a^b) := by rw [opow_add, opow_one]
                                                                   -- 🎉 no goals
#align ordinal.opow_one_add Ordinal.opow_one_add

theorem opow_dvd_opow (a) {b c : Ordinal} (h : b ≤ c) : (a^b) ∣ (a^c) :=
  ⟨a^(c - b), by rw [← opow_add, Ordinal.add_sub_cancel_of_le h]⟩
                 -- 🎉 no goals
#align ordinal.opow_dvd_opow Ordinal.opow_dvd_opow

theorem opow_dvd_opow_iff {a b c : Ordinal} (a1 : 1 < a) : (a^b) ∣ (a^c) ↔ b ≤ c :=
  ⟨fun h =>
    le_of_not_lt fun hn =>
      not_le_of_lt ((opow_lt_opow_iff_right a1).2 hn) <|
        le_of_dvd (opow_ne_zero _ <| one_le_iff_ne_zero.1 <| a1.le) h,
    opow_dvd_opow _⟩
#align ordinal.opow_dvd_opow_iff Ordinal.opow_dvd_opow_iff

theorem opow_mul (a b c : Ordinal) : a^(b * c) = ((a^b)^c) := by
  by_cases b0 : b = 0; · simp only [b0, zero_mul, opow_zero, one_opow]
  -- ⊢ a ^ (b * c) = (a ^ b) ^ c
                         -- 🎉 no goals
  by_cases a0 : a = 0
  -- ⊢ a ^ (b * c) = (a ^ b) ^ c
  · subst a
    -- ⊢ 0 ^ (b * c) = (0 ^ b) ^ c
    by_cases c0 : c = 0
    -- ⊢ 0 ^ (b * c) = (0 ^ b) ^ c
    · simp only [c0, mul_zero, opow_zero]
      -- 🎉 no goals
    simp only [zero_opow b0, zero_opow c0, zero_opow (mul_ne_zero b0 c0)]
    -- 🎉 no goals
  cases' eq_or_lt_of_le (one_le_iff_ne_zero.2 a0) with a1 a1
  -- ⊢ a ^ (b * c) = (a ^ b) ^ c
  · subst a1
    -- ⊢ 1 ^ (b * c) = (1 ^ b) ^ c
    simp only [one_opow]
    -- 🎉 no goals
  induction c using limitRecOn with
  | H₁ => simp only [mul_zero, opow_zero]
  | H₂ c IH =>
    rw [mul_succ, opow_add, IH, opow_succ]
  | H₃ c l IH =>
    refine'
      eq_of_forall_ge_iff fun d =>
        (((opow_isNormal a1).trans (mul_isNormal (Ordinal.pos_iff_ne_zero.2 b0))).limit_le
              l).trans
          _
    dsimp only [Function.comp]
    simp (config := { contextual := true }) only [IH]
    exact (opow_le_of_limit (opow_ne_zero _ a0) l).symm
#align ordinal.opow_mul Ordinal.opow_mul

/-! ### Ordinal logarithm -/


/-- The ordinal logarithm is the solution `u` to the equation `x = b ^ u * v + w` where `v < b` and
    `w < b ^ u`. -/
-- @[pp_nodot] -- Porting note: Unknown attribute.
def log (b : Ordinal) (x : Ordinal) : Ordinal :=
  if _h : 1 < b then pred (sInf { o | x < (b^o) }) else 0
#align ordinal.log Ordinal.log

/-- The set in the definition of `log` is nonempty. -/
theorem log_nonempty {b x : Ordinal} (h : 1 < b) : { o | x < (b^o) }.Nonempty :=
  ⟨_, succ_le_iff.1 (right_le_opow _ h)⟩
#align ordinal.log_nonempty Ordinal.log_nonempty

theorem log_def {b : Ordinal} (h : 1 < b) (x : Ordinal) : log b x = pred (sInf { o | x < (b^o) }) :=
  by simp only [log, dif_pos h]
     -- 🎉 no goals
#align ordinal.log_def Ordinal.log_def

theorem log_of_not_one_lt_left {b : Ordinal} (h : ¬1 < b) (x : Ordinal) : log b x = 0 := by
  simp only [log, dif_neg h]
  -- 🎉 no goals
#align ordinal.log_of_not_one_lt_left Ordinal.log_of_not_one_lt_left

theorem log_of_left_le_one {b : Ordinal} (h : b ≤ 1) : ∀ x, log b x = 0 :=
  log_of_not_one_lt_left h.not_lt
#align ordinal.log_of_left_le_one Ordinal.log_of_left_le_one

@[simp]
theorem log_zero_left : ∀ b, log 0 b = 0 :=
  log_of_left_le_one zero_le_one
#align ordinal.log_zero_left Ordinal.log_zero_left

@[simp]
theorem log_zero_right (b : Ordinal) : log b 0 = 0 :=
  if b1 : 1 < b then by
    rw [log_def b1, ← Ordinal.le_zero, pred_le]
    -- ⊢ sInf {o | 0 < b ^ o} ≤ succ 0
    apply csInf_le'
    -- ⊢ succ 0 ∈ {o | 0 < b ^ o}
    dsimp
    -- ⊢ 0 < b ^ succ 0
    rw [succ_zero, opow_one]
    -- ⊢ 0 < b
    exact zero_lt_one.trans b1
    -- 🎉 no goals
  else by simp only [log_of_not_one_lt_left b1]
          -- 🎉 no goals
#align ordinal.log_zero_right Ordinal.log_zero_right

@[simp]
theorem log_one_left : ∀ b, log 1 b = 0 :=
  log_of_left_le_one le_rfl
#align ordinal.log_one_left Ordinal.log_one_left

theorem succ_log_def {b x : Ordinal} (hb : 1 < b) (hx : x ≠ 0) :
    succ (log b x) = sInf { o | x < (b^o) } := by
  let t := sInf { o | x < (b^o) }
  -- ⊢ succ (log b x) = sInf {o | x < b ^ o}
  have : x < (b^t) := csInf_mem (log_nonempty hb)
  -- ⊢ succ (log b x) = sInf {o | x < b ^ o}
  rcases zero_or_succ_or_limit t with (h | h | h)
  · refine' ((one_le_iff_ne_zero.2 hx).not_lt _).elim
    -- ⊢ x < 1
    simpa only [h, opow_zero] using this
    -- 🎉 no goals
  · rw [show log b x = pred t from log_def hb x, succ_pred_iff_is_succ.2 h]
    -- 🎉 no goals
  · rcases(lt_opow_of_limit (zero_lt_one.trans hb).ne' h).1 this with ⟨a, h₁, h₂⟩
    -- ⊢ succ (log b x) = sInf {o | x < b ^ o}
    exact h₁.not_le.elim ((le_csInf_iff'' (log_nonempty hb)).1 le_rfl a h₂)
    -- 🎉 no goals
#align ordinal.succ_log_def Ordinal.succ_log_def

theorem lt_opow_succ_log_self {b : Ordinal} (hb : 1 < b) (x : Ordinal) :
    x < (b^succ (log b x)) := by
  rcases eq_or_ne x 0 with (rfl | hx)
  -- ⊢ 0 < b ^ succ (log b 0)
  · apply opow_pos _ (zero_lt_one.trans hb)
    -- 🎉 no goals
  · rw [succ_log_def hb hx]
    -- ⊢ x < b ^ sInf {o | x < b ^ o}
    exact csInf_mem (log_nonempty hb)
    -- 🎉 no goals
#align ordinal.lt_opow_succ_log_self Ordinal.lt_opow_succ_log_self

theorem opow_log_le_self (b) {x : Ordinal} (hx : x ≠ 0) : (b^log b x) ≤ x := by
  rcases eq_or_ne b 0 with (rfl | b0)
  -- ⊢ 0 ^ log 0 x ≤ x
  · rw [zero_opow']
    -- ⊢ 1 - log 0 x ≤ x
    refine' (sub_le_self _ _).trans (one_le_iff_ne_zero.2 hx)
    -- 🎉 no goals
  rcases lt_or_eq_of_le (one_le_iff_ne_zero.2 b0) with (hb | rfl)
  -- ⊢ b ^ log b x ≤ x
  · refine' le_of_not_lt fun h => (lt_succ (log b x)).not_le _
    -- ⊢ succ (log b x) ≤ log b x
    have := @csInf_le' _ _ { o | x < (b^o) } _ h
    -- ⊢ succ (log b x) ≤ log b x
    rwa [← succ_log_def hb hx] at this
    -- 🎉 no goals
  · rwa [one_opow, one_le_iff_ne_zero]
    -- 🎉 no goals
#align ordinal.opow_log_le_self Ordinal.opow_log_le_self

/-- `opow b` and `log b` (almost) form a Galois connection. -/
theorem opow_le_iff_le_log {b x c : Ordinal} (hb : 1 < b) (hx : x ≠ 0) : (b^c) ≤ x ↔ c ≤ log b x :=
  ⟨fun h =>
    le_of_not_lt fun hn =>
      (lt_opow_succ_log_self hb x).not_le <|
        ((opow_le_opow_iff_right hb).2 (succ_le_of_lt hn)).trans h,
    fun h => ((opow_le_opow_iff_right hb).2 h).trans (opow_log_le_self b hx)⟩
#align ordinal.opow_le_iff_le_log Ordinal.opow_le_iff_le_log

theorem lt_opow_iff_log_lt {b x c : Ordinal} (hb : 1 < b) (hx : x ≠ 0) : x < (b^c) ↔ log b x < c :=
  lt_iff_lt_of_le_iff_le (opow_le_iff_le_log hb hx)
#align ordinal.lt_opow_iff_log_lt Ordinal.lt_opow_iff_log_lt

theorem log_pos {b o : Ordinal} (hb : 1 < b) (ho : o ≠ 0) (hbo : b ≤ o) : 0 < log b o := by
  rwa [← succ_le_iff, succ_zero, ← opow_le_iff_le_log hb ho, opow_one]
  -- 🎉 no goals
#align ordinal.log_pos Ordinal.log_pos

theorem log_eq_zero {b o : Ordinal} (hbo : o < b) : log b o = 0 := by
  rcases eq_or_ne o 0 with (rfl | ho)
  -- ⊢ log b 0 = 0
  · exact log_zero_right b
    -- 🎉 no goals
  cases' le_or_lt b 1 with hb hb
  -- ⊢ log b o = 0
  · rcases le_one_iff.1 hb with (rfl | rfl)
    -- ⊢ log 0 o = 0
    · exact log_zero_left o
      -- 🎉 no goals
    · exact log_one_left o
      -- 🎉 no goals
  · rwa [← Ordinal.le_zero, ← lt_succ_iff, succ_zero, ← lt_opow_iff_log_lt hb ho, opow_one]
    -- 🎉 no goals
#align ordinal.log_eq_zero Ordinal.log_eq_zero

@[mono]
theorem log_mono_right (b) {x y : Ordinal} (xy : x ≤ y) : log b x ≤ log b y :=
  if hx : x = 0 then by simp only [hx, log_zero_right, Ordinal.zero_le]
                        -- 🎉 no goals
  else
    if hb : 1 < b then
      (opow_le_iff_le_log hb (lt_of_lt_of_le (Ordinal.pos_iff_ne_zero.2 hx) xy).ne').1 <|
        (opow_log_le_self _ hx).trans xy
    else by simp only [log_of_not_one_lt_left hb, Ordinal.zero_le]
            -- 🎉 no goals
#align ordinal.log_mono_right Ordinal.log_mono_right

theorem log_le_self (b x : Ordinal) : log b x ≤ x :=
  if hx : x = 0 then by simp only [hx, log_zero_right, Ordinal.zero_le]
                        -- 🎉 no goals
  else
    if hb : 1 < b then (right_le_opow _ hb).trans (opow_log_le_self b hx)
    else by simp only [log_of_not_one_lt_left hb, Ordinal.zero_le]
            -- 🎉 no goals
#align ordinal.log_le_self Ordinal.log_le_self

@[simp]
theorem log_one_right (b : Ordinal) : log b 1 = 0 :=
  if hb : 1 < b then log_eq_zero hb else log_of_not_one_lt_left hb 1
#align ordinal.log_one_right Ordinal.log_one_right

theorem mod_opow_log_lt_self (b : Ordinal) {o : Ordinal} (ho : o ≠ 0) : o % (b^log b o) < o := by
  rcases eq_or_ne b 0 with (rfl | hb)
  -- ⊢ o % 0 ^ log 0 o < o
  · simpa using Ordinal.pos_iff_ne_zero.2 ho
    -- 🎉 no goals
  · exact (mod_lt _ <| opow_ne_zero _ hb).trans_le (opow_log_le_self _ ho)
    -- 🎉 no goals
#align ordinal.mod_opow_log_lt_self Ordinal.mod_opow_log_lt_self

theorem log_mod_opow_log_lt_log_self {b o : Ordinal} (hb : 1 < b) (ho : o ≠ 0) (hbo : b ≤ o) :
    log b (o % (b^log b o)) < log b o := by
  cases' eq_or_ne (o % (b^log b o)) 0 with h h
  -- ⊢ log b (o % b ^ log b o) < log b o
  · rw [h, log_zero_right]
    -- ⊢ 0 < log b o
    apply log_pos hb ho hbo
    -- 🎉 no goals
  · rw [← succ_le_iff, succ_log_def hb h]
    -- ⊢ sInf {o_1 | o % b ^ log b o < b ^ o_1} ≤ log b o
    apply csInf_le'
    -- ⊢ log b o ∈ {o_1 | o % b ^ log b o < b ^ o_1}
    apply mod_lt
    -- ⊢ b ^ log b o ≠ 0
    rw [← Ordinal.pos_iff_ne_zero]
    -- ⊢ 0 < b ^ log b o
    exact opow_pos _ (zero_lt_one.trans hb)
    -- 🎉 no goals
#align ordinal.log_mod_opow_log_lt_log_self Ordinal.log_mod_opow_log_lt_log_self

theorem opow_mul_add_pos {b v : Ordinal} (hb : b ≠ 0) (u) (hv : v ≠ 0) (w) : 0 < (b^u) * v + w :=
  (opow_pos u <| Ordinal.pos_iff_ne_zero.2 hb).trans_le <|
    (le_mul_left _ <| Ordinal.pos_iff_ne_zero.2 hv).trans <| le_add_right _ _
#align ordinal.opow_mul_add_pos Ordinal.opow_mul_add_pos

theorem opow_mul_add_lt_opow_mul_succ {b u w : Ordinal} (v : Ordinal) (hw : w < (b^u)) :
    (b^u) * v + w < (b^u) * succ v := by rwa [mul_succ, add_lt_add_iff_left]
                                         -- 🎉 no goals
#align ordinal.opow_mul_add_lt_opow_mul_succ Ordinal.opow_mul_add_lt_opow_mul_succ

theorem opow_mul_add_lt_opow_succ {b u v w : Ordinal} (hvb : v < b) (hw : w < (b^u)) :
    (b^u) * v + w < (b^succ u) := by
  convert (opow_mul_add_lt_opow_mul_succ v hw).trans_le (mul_le_mul_left' (succ_le_of_lt hvb) _)
    using 1
  exact opow_succ b u
  -- 🎉 no goals
#align ordinal.opow_mul_add_lt_opow_succ Ordinal.opow_mul_add_lt_opow_succ

theorem log_opow_mul_add {b u v w : Ordinal} (hb : 1 < b) (hv : v ≠ 0) (hvb : v < b)
    (hw : w < (b^u)) : log b ((b^u) * v + w) = u := by
  have hne' := (opow_mul_add_pos (zero_lt_one.trans hb).ne' u hv w).ne'
  -- ⊢ log b (b ^ u * v + w) = u
  by_contra' hne
  -- ⊢ False
  cases' lt_or_gt_of_ne hne with h h
  -- ⊢ False
  · rw [← lt_opow_iff_log_lt hb hne'] at h
    -- ⊢ False
    exact h.not_le ((le_mul_left _ (Ordinal.pos_iff_ne_zero.2 hv)).trans (le_add_right _ _))
    -- 🎉 no goals
  · conv at h => change u < log b (b ^ u * v + w)
    -- ⊢ False
    rw [← succ_le_iff, ← opow_le_iff_le_log hb hne'] at h
    -- ⊢ False
    exact (not_lt_of_le h) (opow_mul_add_lt_opow_succ hvb hw)
    -- 🎉 no goals
#align ordinal.log_opow_mul_add Ordinal.log_opow_mul_add

theorem log_opow {b : Ordinal} (hb : 1 < b) (x : Ordinal) : log b (b^x) = x := by
  convert log_opow_mul_add hb zero_ne_one.symm hb (opow_pos x (zero_lt_one.trans hb))
    using 1
  rw [add_zero, mul_one]
  -- 🎉 no goals
#align ordinal.log_opow Ordinal.log_opow

theorem div_opow_log_pos (b : Ordinal) {o : Ordinal} (ho : o ≠ 0) : 0 < o / (b^log b o) := by
  rcases eq_zero_or_pos b with (rfl | hb)
  -- ⊢ 0 < o / 0 ^ log 0 o
  · simpa using Ordinal.pos_iff_ne_zero.2 ho
    -- 🎉 no goals
  · rw [div_pos (opow_ne_zero _ hb.ne')]
    -- ⊢ b ^ log b o ≤ o
    exact opow_log_le_self b ho
    -- 🎉 no goals
#align ordinal.div_opow_log_pos Ordinal.div_opow_log_pos

theorem div_opow_log_lt {b : Ordinal} (o : Ordinal) (hb : 1 < b) : o / (b^log b o) < b := by
  rw [div_lt (opow_pos _ (zero_lt_one.trans hb)).ne', ← opow_succ]
  -- ⊢ o < b ^ succ (log b o)
  exact lt_opow_succ_log_self hb o
  -- 🎉 no goals
#align ordinal.div_opow_log_lt Ordinal.div_opow_log_lt

theorem add_log_le_log_mul {x y : Ordinal} (b : Ordinal) (hx : x ≠ 0) (hy : y ≠ 0) :
    log b x + log b y ≤ log b (x * y) := by
  by_cases hb : 1 < b
  -- ⊢ log b x + log b y ≤ log b (x * y)
  · rw [← opow_le_iff_le_log hb (mul_ne_zero hx hy), opow_add]
    -- ⊢ b ^ log b x * b ^ log b y ≤ x * y
    exact mul_le_mul' (opow_log_le_self b hx) (opow_log_le_self b hy)
    -- 🎉 no goals
  -- Porting note: `le_refl` is required.
  simp only [log_of_not_one_lt_left hb, zero_add, le_refl]
  -- 🎉 no goals
#align ordinal.add_log_le_log_mul Ordinal.add_log_le_log_mul

/-! ### Interaction with `Nat.cast` -/

@[simp, norm_cast]
theorem nat_cast_opow (m : ℕ) : ∀ n : ℕ, ((m ^ n : ℕ) : Ordinal) = (m^n)
  | 0 => by simp
            -- 🎉 no goals
  | n + 1 => by
    rw [pow_succ', nat_cast_mul, nat_cast_opow m n, Nat.cast_succ, add_one_eq_succ, opow_succ]
    -- 🎉 no goals
#align ordinal.nat_cast_opow Ordinal.nat_cast_opow

theorem sup_opow_nat {o : Ordinal} (ho : 0 < o) : (sup fun n : ℕ => o^n) = (o^ω) := by
  rcases lt_or_eq_of_le (one_le_iff_pos.2 ho) with (ho₁ | rfl)
  -- ⊢ (sup fun n => o ^ ↑n) = o ^ ω
  · exact (opow_isNormal ho₁).apply_omega
    -- 🎉 no goals
  · rw [one_opow]
    -- ⊢ (sup fun n => 1 ^ ↑n) = 1
    refine' le_antisymm (sup_le fun n => by rw [one_opow]) _
    -- ⊢ 1 ≤ sup fun n => 1 ^ ↑n
    convert le_sup (fun n : ℕ => 1^n) 0
    -- ⊢ 1 = 1 ^ ↑0
    rw [Nat.cast_zero, opow_zero]
    -- 🎉 no goals
#align ordinal.sup_opow_nat Ordinal.sup_opow_nat

end Ordinal

-- Porting note: TODO: Port this meta code.

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
-- #align tactic.positivity_opow Tactic.positivity_opow

-- end Tactic
