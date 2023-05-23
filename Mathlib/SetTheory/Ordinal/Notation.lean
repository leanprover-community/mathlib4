/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module set_theory.ordinal.notation
! leanprover-community/mathlib commit b67044ba53af18680e1dd246861d9584e968495d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.SetTheory.Ordinal.Principal

/-!
# Ordinal notation

Constructive ordinal arithmetic for ordinals below `ε₀`.

We define a type `onote`, with constructors `0 : onote` and `onote.oadd e n a` representing
`ω ^ e * n + a`.
We say that `o` is in Cantor normal form - `onote.NF o` - if either `o = 0` or
`o = ω ^ e * n + a` with `a < ω ^ e` and `a` in Cantor normal form.

The type `nonote` is the type of ordinals below `ε₀` in Cantor normal form.
Various operations (addition, subtraction, multiplication, power function)
are defined on `onote` and `nonote`.
-/


open Ordinal Order

open Ordinal

-- get notation for `ω`
/-- Recursive definition of an ordinal notation. `zero` denotes the
  ordinal 0, and `oadd e n a` is intended to refer to `ω^e * n + a`.
  For this to be valid Cantor normal form, we must have the exponents
  decrease to the right, but we can't state this condition until we've
  defined `repr`, so it is a separate definition `NF`. -/
inductive Onote : Type
  | zero : Onote
  | oadd : Onote → ℕ+ → Onote → Onote
  deriving DecidableEq
#align onote Onote

namespace Onote

/-- Notation for 0 -/
instance : Zero Onote :=
  ⟨zero⟩

@[simp]
theorem zero_def : zero = 0 :=
  rfl
#align onote.zero_def Onote.zero_def

instance : Inhabited Onote :=
  ⟨0⟩

/-- Notation for 1 -/
instance : One Onote :=
  ⟨oadd 0 1 0⟩

/-- Notation for ω -/
def omega : Onote :=
  oadd 1 1 0
#align onote.omega Onote.omega

/-- The ordinal denoted by a notation -/
@[simp]
noncomputable def repr : Onote → Ordinal.{0}
  | 0 => 0
  | oadd e n a => ω ^ repr e * n + repr a
#align onote.repr Onote.repr

/-- Auxiliary definition to print an ordinal notation -/
def toStringAux1 (e : Onote) (n : ℕ) (s : String) : String :=
  if e = 0 then toString n
  else (if e = 1 then "ω" else "ω^(" ++ s ++ ")") ++ if n = 1 then "" else "*" ++ toString n
#align onote.to_string_aux1 Onote.toStringAux1

/-- Print an ordinal notation -/
def toString : Onote → String
  | zero => "0"
  | oadd e n 0 => toStringAux1 e n (toString e)
  | oadd e n a => toStringAux1 e n (toString e) ++ " + " ++ toString a
#align onote.to_string Onote.toString

/-- Print an ordinal notation -/
def repr' : Onote → String
  | zero => "0"
  | oadd e n a => "(oadd " ++ repr' e ++ " " ++ toString (n : ℕ) ++ " " ++ repr' a ++ ")"
#align onote.repr' Onote.repr'

instance : ToString Onote :=
  ⟨toString⟩

instance : Repr Onote :=
  ⟨repr'⟩

instance : Preorder Onote where
  le x y := repr x ≤ repr y
  lt x y := repr x < repr y
  le_refl a := @le_refl Ordinal _ _
  le_trans a b c := @le_trans Ordinal _ _ _ _
  lt_iff_le_not_le a b := @lt_iff_le_not_le Ordinal _ _ _

theorem lt_def {x y : Onote} : x < y ↔ repr x < repr y :=
  Iff.rfl
#align onote.lt_def Onote.lt_def

theorem le_def {x y : Onote} : x ≤ y ↔ repr x ≤ repr y :=
  Iff.rfl
#align onote.le_def Onote.le_def

/-- Convert a `nat` into an ordinal -/
@[simp]
def ofNat : ℕ → Onote
  | 0 => 0
  | Nat.succ n => oadd 0 n.succPNat 0
#align onote.of_nat Onote.ofNat

@[simp]
theorem ofNat_one : ofNat 1 = 1 :=
  rfl
#align onote.of_nat_one Onote.ofNat_one

@[simp]
theorem repr_ofNat (n : ℕ) : repr (ofNat n) = n := by cases n <;> simp
#align onote.repr_of_nat Onote.repr_ofNat

@[simp]
theorem repr_one : repr 1 = 1 := by simpa using repr_of_nat 1
#align onote.repr_one Onote.repr_one

theorem omega_le_oadd (e n a) : ω ^ repr e ≤ repr (oadd e n a) :=
  by
  unfold repr
  refine' le_trans _ (le_add_right _ _)
  simpa using (mul_le_mul_iff_left <| opow_pos (repr e) omega_pos).2 (nat_cast_le.2 n.2)
#align onote.omega_le_oadd Onote.omega_le_oadd

theorem oadd_pos (e n a) : 0 < oadd e n a :=
  @lt_of_lt_of_le _ _ _ _ _ (opow_pos _ omega_pos) (omega_le_oadd _ _ _)
#align onote.oadd_pos Onote.oadd_pos

/-- Compare ordinal notations -/
def cmp : Onote → Onote → Ordering
  | 0, 0 => Ordering.eq
  | _, 0 => Ordering.gt
  | 0, _ => Ordering.lt
  | o₁@(oadd e₁ n₁ a₁), o₂@(oadd e₂ n₂ a₂) =>
    (cmp e₁ e₂).orElse <| (cmp (n₁ : ℕ) n₂).orElse (cmp a₁ a₂)
#align onote.cmp Onote.cmp

theorem eq_of_cmp_eq : ∀ {o₁ o₂}, cmp o₁ o₂ = Ordering.eq → o₁ = o₂
  | 0, 0, h => rfl
  | oadd e n a, 0, h => by injection h
  | 0, oadd e n a, h => by injection h
  | o₁@(oadd e₁ n₁ a₁), o₂@(oadd e₂ n₂ a₂), h =>
    by
    revert h; simp only [cmp]
    cases h₁ : cmp e₁ e₂ <;> intro h <;> try cases h
    obtain rfl := eq_of_cmp_eq h₁
    revert h; cases h₂ : _root_.cmp (n₁ : ℕ) n₂ <;> intro h <;> try cases h
    obtain rfl := eq_of_cmp_eq h
    rw [_root_.cmp, cmpUsing_eq_eq] at h₂
    obtain rfl := Subtype.eq (eq_of_incomp h₂)
    simp
#align onote.eq_of_cmp_eq Onote.eq_of_cmp_eq

protected theorem zero_lt_one : (0 : Onote) < 1 := by
  rw [lt_def, repr, repr_one] <;> exact zero_lt_one
#align onote.zero_lt_one Onote.zero_lt_one

/-- `NF_below o b` says that `o` is a normal form ordinal notation
  satisfying `repr o < ω ^ b`. -/
inductive NFBelow : Onote → Ordinal.{0} → Prop
  | zero {b} : NF_below 0 b
  | oadd' {e n a eb b} : NF_below e eb → NF_below a (repr e) → repr e < b → NF_below (oadd e n a) b
#align onote.NF_below Onote.NFBelow

/-- A normal form ordinal notation has the form

     ω ^ a₁ * n₁ + ω ^ a₂ * n₂ + ... ω ^ aₖ * nₖ
  where `a₁ > a₂ > ... > aₖ` and all the `aᵢ` are
  also in normal form.

  We will essentially only be interested in normal form
  ordinal notations, but to avoid complicating the algorithms
  we define everything over general ordinal notations and
  only prove correctness with normal form as an invariant. -/
class NF (o : Onote) : Prop where
  out : Exists (NFBelow o)
#align onote.NF Onote.NF

attribute [pp_nodot] NF

instance NF.zero : NF 0 :=
  ⟨⟨0, NFBelow.zero⟩⟩
#align onote.NF.zero Onote.NF.zero

theorem NFBelow.oadd {e n a b} : NF e → NFBelow a (repr e) → repr e < b → NFBelow (oadd e n a) b
  | ⟨⟨eb, h⟩⟩ => NFBelow.oadd' h
#align onote.NF_below.oadd Onote.NFBelow.oadd

theorem NFBelow.fst {e n a b} (h : NFBelow (oadd e n a) b) : NF e := by
  cases' h with _ _ _ _ eb _ h₁ h₂ h₃ <;> exact ⟨⟨_, h₁⟩⟩
#align onote.NF_below.fst Onote.NFBelow.fst

theorem NF.fst {e n a} : NF (oadd e n a) → NF e
  | ⟨⟨b, h⟩⟩ => h.fst
#align onote.NF.fst Onote.NF.fst

theorem NFBelow.snd {e n a b} (h : NFBelow (oadd e n a) b) : NFBelow a (repr e) := by
  cases' h with _ _ _ _ eb _ h₁ h₂ h₃ <;> exact h₂
#align onote.NF_below.snd Onote.NFBelow.snd

theorem NF.snd' {e n a} : NF (oadd e n a) → NFBelow a (repr e)
  | ⟨⟨b, h⟩⟩ => h.snd
#align onote.NF.snd' Onote.NF.snd'

theorem NF.snd {e n a} (h : NF (oadd e n a)) : NF a :=
  ⟨⟨_, h.snd'⟩⟩
#align onote.NF.snd Onote.NF.snd

theorem NF.oadd {e a} (h₁ : NF e) (n) (h₂ : NFBelow a (repr e)) : NF (oadd e n a) :=
  ⟨⟨_, NFBelow.oadd h₁ h₂ (lt_succ _)⟩⟩
#align onote.NF.oadd Onote.NF.oadd

instance NF.oadd_zero (e n) [h : NF e] : NF (oadd e n 0) :=
  h.oadd _ NFBelow.zero
#align onote.NF.oadd_zero Onote.NF.oadd_zero

theorem NFBelow.lt {e n a b} (h : NFBelow (oadd e n a) b) : repr e < b := by
  cases' h with _ _ _ _ eb _ h₁ h₂ h₃ <;> exact h₃
#align onote.NF_below.lt Onote.NFBelow.lt

theorem nFBelow_zero : ∀ {o}, NFBelow o 0 ↔ o = 0
  | 0 => ⟨fun _ => rfl, fun _ => NFBelow.zero⟩
  | oadd e n a =>
    ⟨fun h => (not_le_of_lt h.lt).elim (Ordinal.zero_le _), fun e => e.symm ▸ NFBelow.zero⟩
#align onote.NF_below_zero Onote.nFBelow_zero

theorem NF.zero_of_zero {e n a} (h : NF (oadd e n a)) (e0 : e = 0) : a = 0 := by
  simpa [e0, NF_below_zero] using h.snd'
#align onote.NF.zero_of_zero Onote.NF.zero_of_zero

theorem NFBelow.repr_lt {o b} (h : NFBelow o b) : repr o < ω ^ b :=
  by
  induction' h with _ e n a eb b h₁ h₂ h₃ _ IH
  · exact opow_pos _ omega_pos
  · rw [repr]
    apply ((add_lt_add_iff_left _).2 IH).trans_le
    rw [← mul_succ]
    apply (mul_le_mul_left' (succ_le_of_lt (nat_lt_omega _)) _).trans
    rw [← opow_succ]
    exact opow_le_opow_right omega_pos (succ_le_of_lt h₃)
#align onote.NF_below.repr_lt Onote.NFBelow.repr_lt

theorem NFBelow.mono {o b₁ b₂} (bb : b₁ ≤ b₂) (h : NFBelow o b₁) : NFBelow o b₂ :=
  by
  induction' h with _ e n a eb b h₁ h₂ h₃ _ IH <;> constructor
  exacts[h₁, h₂, lt_of_lt_of_le h₃ bb]
#align onote.NF_below.mono Onote.NFBelow.mono

theorem NF.below_of_lt {e n a b} (H : repr e < b) : NF (oadd e n a) → NFBelow (oadd e n a) b
  | ⟨⟨b', h⟩⟩ => by cases' h with _ _ _ _ eb _ h₁ h₂ h₃ <;> exact NF_below.oadd' h₁ h₂ H
#align onote.NF.below_of_lt Onote.NF.below_of_lt

theorem NF.below_of_lt' : ∀ {o b}, repr o < ω ^ b → NF o → NFBelow o b
  | 0, b, H, _ => NFBelow.zero
  | oadd e n a, b, H, h =>
    h.below_of_lt <|
      (opow_lt_opow_iff_right one_lt_omega).1 <| lt_of_le_of_lt (omega_le_oadd _ _ _) H
#align onote.NF.below_of_lt' Onote.NF.below_of_lt'

theorem nFBelow_ofNat : ∀ n, NFBelow (ofNat n) 1
  | 0 => NFBelow.zero
  | Nat.succ n => NFBelow.oadd NF.zero NFBelow.zero zero_lt_one
#align onote.NF_below_of_nat Onote.nFBelow_ofNat

instance nF_ofNat (n) : NF (ofNat n) :=
  ⟨⟨_, nFBelow_ofNat n⟩⟩
#align onote.NF_of_nat Onote.nF_ofNat

instance nF_one : NF 1 := by rw [← of_nat_one] <;> infer_instance
#align onote.NF_one Onote.nF_one

theorem oadd_lt_oadd_1 {e₁ n₁ o₁ e₂ n₂ o₂} (h₁ : NF (oadd e₁ n₁ o₁)) (h : e₁ < e₂) :
    oadd e₁ n₁ o₁ < oadd e₂ n₂ o₂ :=
  @lt_of_lt_of_le _ _ _ _ _ (h₁.below_of_lt h).repr_lt (omega_le_oadd _ _ _)
#align onote.oadd_lt_oadd_1 Onote.oadd_lt_oadd_1

theorem oadd_lt_oadd_2 {e o₁ o₂ : Onote} {n₁ n₂ : ℕ+} (h₁ : NF (oadd e n₁ o₁)) (h : (n₁ : ℕ) < n₂) :
    oadd e n₁ o₁ < oadd e n₂ o₂ := by
  simp [lt_def]
  refine' lt_of_lt_of_le ((add_lt_add_iff_left _).2 h₁.snd'.repr_lt) (le_trans _ (le_add_right _ _))
  rwa [← mul_succ, mul_le_mul_iff_left (opow_pos _ omega_pos), succ_le_iff, nat_cast_lt]
#align onote.oadd_lt_oadd_2 Onote.oadd_lt_oadd_2

theorem oadd_lt_oadd_3 {e n a₁ a₂} (h : a₁ < a₂) : oadd e n a₁ < oadd e n a₂ :=
  by
  rw [lt_def]; unfold repr
  exact add_lt_add_left h _
#align onote.oadd_lt_oadd_3 Onote.oadd_lt_oadd_3

theorem cmp_compares : ∀ (a b : Onote) [NF a] [NF b], (cmp a b).Compares a b
  | 0, 0, h₁, h₂ => rfl
  | oadd e n a, 0, h₁, h₂ => oadd_pos _ _ _
  | 0, oadd e n a, h₁, h₂ => oadd_pos _ _ _
  | o₁@(oadd e₁ n₁ a₁), o₂@(oadd e₂ n₂ a₂), h₁, h₂ =>
    by
    rw [cmp]
    have IHe := @cmp_compares _ _ h₁.fst h₂.fst
    cases cmp e₁ e₂
    case lt => exact oadd_lt_oadd_1 h₁ IHe
    case gt => exact oadd_lt_oadd_1 h₂ IHe
    change e₁ = e₂ at IHe; subst IHe
    unfold _root_.cmp; cases nh : cmpUsing (· < ·) (n₁ : ℕ) n₂
    case lt => rw [cmpUsing_eq_lt] at nh; exact oadd_lt_oadd_2 h₁ nh
    case gt => rw [cmpUsing_eq_gt] at nh; exact oadd_lt_oadd_2 h₂ nh
    rw [cmpUsing_eq_eq] at nh
    obtain rfl := Subtype.eq (eq_of_incomp nh)
    have IHa := @cmp_compares _ _ h₁.snd h₂.snd
    cases cmp a₁ a₂
    case lt => exact oadd_lt_oadd_3 IHa
    case gt => exact oadd_lt_oadd_3 IHa
    change a₁ = a₂ at IHa; subst IHa; exact rfl
#align onote.cmp_compares Onote.cmp_compares

theorem repr_inj {a b} [NF a] [NF b] : repr a = repr b ↔ a = b :=
  ⟨match cmp a b, cmp_compares a b with
    | Ordering.lt, (h : repr a < repr b), e => (ne_of_lt h e).elim
    | Ordering.gt, (h : repr a > repr b), e => (ne_of_gt h e).elim
    | Ordering.eq, h, e => h,
    congr_arg _⟩
#align onote.repr_inj Onote.repr_inj

theorem NF.of_dvd_omega_opow {b e n a} (h : NF (oadd e n a)) (d : ω ^ b ∣ repr (oadd e n a)) :
    b ≤ repr e ∧ ω ^ b ∣ repr a :=
  by
  have := mt repr_inj.1 (fun h => by injection h : oadd e n a ≠ 0)
  have L := le_of_not_lt fun l => not_le_of_lt (h.below_of_lt l).repr_lt (le_of_dvd this d)
  simp at d
  exact ⟨L, (dvd_add_iff <| (opow_dvd_opow _ L).mulRight _).1 d⟩
#align onote.NF.of_dvd_omega_opow Onote.NF.of_dvd_omega_opow

theorem NF.of_dvd_omega {e n a} (h : NF (oadd e n a)) :
    ω ∣ repr (oadd e n a) → repr e ≠ 0 ∧ ω ∣ repr a := by
  rw [← opow_one ω, ← one_le_iff_ne_zero] <;> exact h.of_dvd_omega_opow
#align onote.NF.of_dvd_omega Onote.NF.of_dvd_omega

/-- `top_below b o` asserts that the largest exponent in `o`, if
  it exists, is less than `b`. This is an auxiliary definition
  for decidability of `NF`. -/
def TopBelow (b) : Onote → Prop
  | 0 => True
  | oadd e n a => cmp e b = Ordering.lt
#align onote.top_below Onote.TopBelow

instance decidableTopBelow : DecidableRel TopBelow := by
  intro b o <;> cases o <;> delta top_below <;> infer_instance
#align onote.decidable_top_below Onote.decidableTopBelow

theorem nFBelow_iff_topBelow {b} [NF b] : ∀ {o}, NFBelow o (repr b) ↔ NF o ∧ TopBelow b o
  | 0 => ⟨fun h => ⟨⟨⟨_, h⟩⟩, trivial⟩, fun _ => NFBelow.zero⟩
  | oadd e n a =>
    ⟨fun h => ⟨⟨⟨_, h⟩⟩, (@cmp_compares _ b h.fst _).eq_lt.2 h.lt⟩, fun ⟨h₁, h₂⟩ =>
      h₁.below_of_lt <| (@cmp_compares _ b h₁.fst _).eq_lt.1 h₂⟩
#align onote.NF_below_iff_top_below Onote.nFBelow_iff_topBelow

instance decidableNF : DecidablePred NF
  | 0 => isTrue NF.zero
  | oadd e n a => by
    have := decidable_NF e
    have := decidable_NF a; skip
    apply decidable_of_iff (NF e ∧ NF a ∧ top_below e a)
    abstract 
      rw [← and_congr_right fun h => @NF_below_iff_top_below _ h _]
      exact ⟨fun ⟨h₁, h₂⟩ => NF.oadd h₁ n h₂, fun h => ⟨h.fst, h.snd'⟩⟩
#align onote.decidable_NF Onote.decidableNF

/-- Addition of ordinal notations (correct only for normal input) -/
def add : Onote → Onote → Onote
  | 0, o => o
  | oadd e n a, o =>
    match add a o with
    | 0 => oadd e n 0
    | o'@(oadd e' n' a') =>
      match cmp e e' with
      | Ordering.lt => o'
      | Ordering.eq => oadd e (n + n') a'
      | Ordering.gt => oadd e n o'
#align onote.add Onote.add

instance : Add Onote :=
  ⟨add⟩

@[simp]
theorem zero_add (o : Onote) : 0 + o = o :=
  rfl
#align onote.zero_add Onote.zero_add

theorem oadd_add (e n a o) : oadd e n a + o = Add._match1 e n (a + o) :=
  rfl
#align onote.oadd_add Onote.oadd_add

/-- Subtraction of ordinal notations (correct only for normal input) -/
def sub : Onote → Onote → Onote
  | 0, o => 0
  | o, 0 => o
  | o₁@(oadd e₁ n₁ a₁), oadd e₂ n₂ a₂ =>
    match cmp e₁ e₂ with
    | Ordering.lt => 0
    | Ordering.gt => o₁
    | Ordering.eq =>
      match (n₁ : ℕ) - n₂ with
      | 0 => if n₁ = n₂ then sub a₁ a₂ else 0
      | Nat.succ k => oadd e₁ k.succPNat a₁
#align onote.sub Onote.sub

instance : Sub Onote :=
  ⟨sub⟩

theorem add_nFBelow {b} : ∀ {o₁ o₂}, NFBelow o₁ b → NFBelow o₂ b → NFBelow (o₁ + o₂) b
  | 0, o, h₁, h₂ => h₂
  | oadd e n a, o, h₁, h₂ =>
    by
    have h' := add_NF_below (h₁.snd.mono <| le_of_lt h₁.lt) h₂
    simp [oadd_add]; cases' a + o with e' n' a'
    · exact NF_below.oadd h₁.fst NF_below.zero h₁.lt
    simp [add]; have := @cmp_compares _ _ h₁.fst h'.fst
    cases cmp e e' <;> simp [add]
    · exact h'
    · simp at this
      subst e'
      exact NF_below.oadd h'.fst h'.snd h'.lt
    · exact NF_below.oadd h₁.fst (NF.below_of_lt this ⟨⟨_, h'⟩⟩) h₁.lt
#align onote.add_NF_below Onote.add_nFBelow

instance add_nF (o₁ o₂) : ∀ [NF o₁] [NF o₂], NF (o₁ + o₂)
  | ⟨⟨b₁, h₁⟩⟩, ⟨⟨b₂, h₂⟩⟩ =>
    ⟨(le_total b₁ b₂).elim (fun h => ⟨b₂, add_nFBelow (h₁.mono h) h₂⟩) fun h =>
        ⟨b₁, add_nFBelow h₁ (h₂.mono h)⟩⟩
#align onote.add_NF Onote.add_nF

@[simp]
theorem repr_add : ∀ (o₁ o₂) [NF o₁] [NF o₂], repr (o₁ + o₂) = repr o₁ + repr o₂
  | 0, o, h₁, h₂ => by simp
  | oadd e n a, o, h₁, h₂ => by
    haveI := h₁.snd; have h' := repr_add a o
    conv at h' in _ + o => simp [(· + ·)]
    have nf := Onote.add_nF a o
    conv at nf in _ + o => simp [(· + ·)]
    conv in _ + o => simp [(· + ·), add]
    cases' add a o with e' n' a' <;> simp [add, h'.symm, add_assoc]
    have := h₁.fst; haveI := nf.fst; have ee := cmp_compares e e'
    cases cmp e e' <;> simp [add]
    · rw [← add_assoc, @add_absorp _ (repr e') (ω ^ repr e' * (n' : ℕ))]
      · have := (h₁.below_of_lt ee).repr_lt
        unfold repr at this
        exact lt_of_le_of_lt (le_add_right _ _) this
      · simpa using (mul_le_mul_iff_left <| opow_pos (repr e') omega_pos).2 (nat_cast_le.2 n'.pos)
    · change e = e' at ee
      subst e'
      rw [← add_assoc, ← mul_add, ← Nat.cast_add]
#align onote.repr_add Onote.repr_add

theorem sub_nFBelow : ∀ {o₁ o₂ b}, NFBelow o₁ b → NF o₂ → NFBelow (o₁ - o₂) b
  | 0, o, b, h₁, h₂ => by cases o <;> exact NF_below.zero
  | oadd e n a, 0, b, h₁, h₂ => h₁
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, b, h₁, h₂ =>
    by
    have h' := sub_NF_below h₁.snd h₂.snd
    simp [Sub.sub, sub] at h'⊢
    have := @cmp_compares _ _ h₁.fst h₂.fst
    cases cmp e₁ e₂ <;> simp [sub]
    · apply NF_below.zero
    · simp at this
      subst e₂
      cases mn : (n₁ : ℕ) - n₂ <;> simp [sub]
      · by_cases en : n₁ = n₂ <;> simp [en]
        · exact h'.mono (le_of_lt h₁.lt)
        · exact NF_below.zero
      · exact NF_below.oadd h₁.fst h₁.snd h₁.lt
    · exact h₁
#align onote.sub_NF_below Onote.sub_nFBelow

instance sub_nF (o₁ o₂) : ∀ [NF o₁] [NF o₂], NF (o₁ - o₂)
  | ⟨⟨b₁, h₁⟩⟩, h₂ => ⟨⟨b₁, sub_nFBelow h₁ h₂⟩⟩
#align onote.sub_NF Onote.sub_nF

@[simp]
theorem repr_sub : ∀ (o₁ o₂) [NF o₁] [NF o₂], repr (o₁ - o₂) = repr o₁ - repr o₂
  | 0, o, h₁, h₂ => by cases o <;> exact (Ordinal.zero_sub _).symm
  | oadd e n a, 0, h₁, h₂ => (Ordinal.sub_zero _).symm
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, h₁, h₂ =>
    by
    haveI := h₁.snd; haveI := h₂.snd; have h' := repr_sub a₁ a₂
    conv at h' in a₁ - a₂ => simp [Sub.sub]
    have nf := Onote.sub_nF a₁ a₂
    conv at nf in a₁ - a₂ => simp [Sub.sub]
    conv in _ - oadd _ _ _ => simp [Sub.sub, sub]
    have ee := @cmp_compares _ _ h₁.fst h₂.fst
    cases cmp e₁ e₂
    · rw [Ordinal.sub_eq_zero_iff_le.2]
      · rfl
      exact le_of_lt (oadd_lt_oadd_1 h₁ ee)
    · change e₁ = e₂ at ee
      subst e₂
      unfold sub._match_1
      cases mn : (n₁ : ℕ) - n₂ <;> dsimp only [sub._match_2]
      · by_cases en : n₁ = n₂
        · simpa [en]
        · simp [en, -repr]
          exact
            (Ordinal.sub_eq_zero_iff_le.2 <|
                le_of_lt <|
                  oadd_lt_oadd_2 h₁ <|
                    lt_of_le_of_ne (tsub_eq_zero_iff_le.1 mn) (mt PNat.eq en)).symm
      · simp [Nat.succPNat, -Nat.cast_succ]
        rw [(tsub_eq_iff_eq_add_of_le <| le_of_lt <| Nat.lt_of_sub_eq_succ mn).1 mn, add_comm,
          Nat.cast_add, mul_add, add_assoc, add_sub_add_cancel]
        refine'
          (Ordinal.sub_eq_of_add_eq <|
              add_absorp h₂.snd'.repr_lt <| le_trans _ (le_add_right _ _)).symm
        simpa using mul_le_mul_left' (nat_cast_le.2 <| Nat.succ_pos _) _
    ·
      exact
        (Ordinal.sub_eq_of_add_eq <|
            add_absorp (h₂.below_of_lt ee).repr_lt <| omega_le_oadd _ _ _).symm
#align onote.repr_sub Onote.repr_sub

/-- Multiplication of ordinal notations (correct only for normal input) -/
def mul : Onote → Onote → Onote
  | 0, _ => 0
  | _, 0 => 0
  | o₁@(oadd e₁ n₁ a₁), oadd e₂ n₂ a₂ =>
    if e₂ = 0 then oadd e₁ (n₁ * n₂) a₁ else oadd (e₁ + e₂) n₂ (mul o₁ a₂)
#align onote.mul Onote.mul

instance : Mul Onote :=
  ⟨mul⟩

instance : MulZeroClass Onote where
  mul := (· * ·)
  zero := 0
  zero_mul o := by cases o <;> rfl
  mul_zero o := by cases o <;> rfl

theorem oadd_mul (e₁ n₁ a₁ e₂ n₂ a₂) :
    oadd e₁ n₁ a₁ * oadd e₂ n₂ a₂ =
      if e₂ = 0 then oadd e₁ (n₁ * n₂) a₁ else oadd (e₁ + e₂) n₂ (oadd e₁ n₁ a₁ * a₂) :=
  rfl
#align onote.oadd_mul Onote.oadd_mul

theorem oadd_mul_nFBelow {e₁ n₁ a₁ b₁} (h₁ : NFBelow (oadd e₁ n₁ a₁) b₁) :
    ∀ {o₂ b₂}, NFBelow o₂ b₂ → NFBelow (oadd e₁ n₁ a₁ * o₂) (repr e₁ + b₂)
  | 0, b₂, h₂ => NFBelow.zero
  | oadd e₂ n₂ a₂, b₂, h₂ => by
    have IH := oadd_mul_NF_below h₂.snd
    by_cases e0 : e₂ = 0 <;> simp [e0, oadd_mul]
    · apply NF_below.oadd h₁.fst h₁.snd
      simpa using (add_lt_add_iff_left (repr e₁)).2 (lt_of_le_of_lt (Ordinal.zero_le _) h₂.lt)
    · haveI := h₁.fst
      haveI := h₂.fst
      apply NF_below.oadd
      infer_instance
      · rwa [repr_add]
      · rw [repr_add, add_lt_add_iff_left]
        exact h₂.lt
#align onote.oadd_mul_NF_below Onote.oadd_mul_nFBelow

instance mul_nF : ∀ (o₁ o₂) [NF o₁] [NF o₂], NF (o₁ * o₂)
  | 0, o, h₁, h₂ => by cases o <;> exact NF.zero
  | oadd e n a, o, ⟨⟨b₁, hb₁⟩⟩, ⟨⟨b₂, hb₂⟩⟩ => ⟨⟨_, oadd_mul_nFBelow hb₁ hb₂⟩⟩
#align onote.mul_NF Onote.mul_nF

@[simp]
theorem repr_mul : ∀ (o₁ o₂) [NF o₁] [NF o₂], repr (o₁ * o₂) = repr o₁ * repr o₂
  | 0, o, h₁, h₂ => by cases o <;> exact (MulZeroClass.zero_mul _).symm
  | oadd e₁ n₁ a₁, 0, h₁, h₂ => (MulZeroClass.mul_zero _).symm
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, h₁, h₂ =>
    by
    have IH : repr (mul _ _) = _ := @repr_mul _ _ h₁ h₂.snd
    conv =>
      lhs
      simp [(· * ·)]
    have ao : repr a₁ + ω ^ repr e₁ * (n₁ : ℕ) = ω ^ repr e₁ * (n₁ : ℕ) :=
      by
      apply add_absorp h₁.snd'.repr_lt
      simpa using (mul_le_mul_iff_left <| opow_pos _ omega_pos).2 (nat_cast_le.2 n₁.2)
    by_cases e0 : e₂ = 0 <;> simp [e0, mul]
    · cases' Nat.exists_eq_succ_of_ne_zero n₂.ne_zero with x xe
      simp [h₂.zero_of_zero e0, xe, -Nat.cast_succ]
      rw [nat_cast_succ x, add_mul_succ _ ao, mul_assoc]
    · haveI := h₁.fst
      haveI := h₂.fst
      simp [IH, repr_add, opow_add, mul_add]
      rw [← mul_assoc]
      congr 2
      have := mt repr_inj.1 e0
      rw [add_mul_limit ao (opow_is_limit_left omega_is_limit this), mul_assoc,
        mul_omega_dvd (nat_cast_pos.2 n₁.pos) (nat_lt_omega _)]
      simpa using opow_dvd_opow ω (one_le_iff_ne_zero.2 this)
#align onote.repr_mul Onote.repr_mul

/-- Calculate division and remainder of `o` mod ω.
  `split' o = (a, n)` means `o = ω * a + n`. -/
def split' : Onote → Onote × ℕ
  | 0 => (0, 0)
  | oadd e n a =>
    if e = 0 then (0, n)
    else
      let (a', m) := split' a
      (oadd (e - 1) n a', m)
#align onote.split' Onote.split'

/-- Calculate division and remainder of `o` mod ω.
  `split o = (a, n)` means `o = a + n`, where `ω ∣ a`. -/
def split : Onote → Onote × ℕ
  | 0 => (0, 0)
  | oadd e n a =>
    if e = 0 then (0, n)
    else
      let (a', m) := split a
      (oadd e n a', m)
#align onote.split Onote.split

/-- `scale x o` is the ordinal notation for `ω ^ x * o`. -/
def scale (x : Onote) : Onote → Onote
  | 0 => 0
  | oadd e n a => oadd (x + e) n (scale a)
#align onote.scale Onote.scale

/-- `mul_nat o n` is the ordinal notation for `o * n`. -/
def mulNat : Onote → ℕ → Onote
  | 0, m => 0
  | _, 0 => 0
  | oadd e n a, m + 1 => oadd e (n * m.succPNat) a
#align onote.mul_nat Onote.mulNat

/-- Auxiliary definition to compute the ordinal notation for the ordinal
exponentiation in `opow` -/
def opowAux (e a0 a : Onote) : ℕ → ℕ → Onote
  | _, 0 => 0
  | 0, m + 1 => oadd e m.succPNat 0
  | k + 1, m => scale (e + mulNat a0 k) a + opow_aux k m
#align onote.opow_aux Onote.opowAux

/-- `opow o₁ o₂` calculates the ordinal notation for
  the ordinal exponential `o₁ ^ o₂`. -/
def opow (o₁ o₂ : Onote) : Onote :=
  match split o₁ with
  | (0, 0) => if o₂ = 0 then 1 else 0
  | (0, 1) => 1
  | (0, m + 1) =>
    let (b', k) := split' o₂
    oadd b' (@Pow.pow ℕ+ _ _ m.succPNat k) 0
  | (a@(oadd a0 _ _), m) =>
    match split o₂ with
    | (b, 0) => oadd (a0 * b) 1 0
    | (b, k + 1) =>
      let eb := a0 * b
      scale (eb + mulNat a0 k) a + opowAux eb a0 (mulNat a m) k m
#align onote.opow Onote.opow

instance : Pow Onote Onote :=
  ⟨opow⟩

theorem opow_def (o₁ o₂ : Onote) : o₁ ^ o₂ = Opow._match1 o₂ (split o₁) :=
  rfl
#align onote.opow_def Onote.opow_def

theorem split_eq_scale_split' : ∀ {o o' m} [NF o], split' o = (o', m) → split o = (scale 1 o', m)
  | 0, o', m, h, p => by injection p <;> substs o' m <;> rfl
  | oadd e n a, o', m, h, p =>
    by
    by_cases e0 : e = 0 <;> simp [e0, split, split'] at p⊢
    · rcases p with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
    · revert p
      cases' h' : split' a with a' m'
      haveI := h.fst
      haveI := h.snd
      simp [split_eq_scale_split' h', split, split']
      have : 1 + (e - 1) = e := by
        refine' repr_inj.1 _
        simp
        have := mt repr_inj.1 e0
        exact Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 this)
      intros
      substs o' m
      simp [scale, this]
#align onote.split_eq_scale_split' Onote.split_eq_scale_split'

theorem nF_repr_split' : ∀ {o o' m} [NF o], split' o = (o', m) → NF o' ∧ repr o = ω * repr o' + m
  | 0, o', m, h, p => by injection p <;> substs o' m <;> simp [NF.zero]
  | oadd e n a, o', m, h, p =>
    by
    by_cases e0 : e = 0 <;> simp [e0, split, split'] at p⊢
    · rcases p with ⟨rfl, rfl⟩
      simp [h.zero_of_zero e0, NF.zero]
    · revert p
      cases' h' : split' a with a' m'
      haveI := h.fst
      haveI := h.snd
      cases' NF_repr_split' h' with IH₁ IH₂
      simp [IH₂, split']
      intros
      substs o' m
      have : (ω : Ordinal.{0}) ^ repr e = ω ^ (1 : Ordinal.{0}) * ω ^ (repr e - 1) :=
        by
        have := mt repr_inj.1 e0
        rw [← opow_add, Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 this)]
      refine' ⟨NF.oadd (by infer_instance) _ _, _⟩
      · simp at this⊢
        refine'
          IH₁.below_of_lt'
            ((mul_lt_mul_iff_left omega_pos).1 <| lt_of_le_of_lt (le_add_right _ m') _)
        rw [← this, ← IH₂]
        exact h.snd'.repr_lt
      · rw [this]
        simp [mul_add, mul_assoc, add_assoc]
#align onote.NF_repr_split' Onote.nF_repr_split'

theorem scale_eq_mul (x) [NF x] : ∀ (o) [NF o], scale x o = oadd x 1 0 * o
  | 0, h => rfl
  | oadd e n a, h => by
    simp [(· * ·)]; simp [mul, scale]
    haveI := h.snd
    by_cases e0 : e = 0
    · rw [scale_eq_mul]
      simp [e0, h.zero_of_zero, show x + 0 = x from repr_inj.1 (by simp)]
    · simp [e0, scale_eq_mul, (· * ·)]
#align onote.scale_eq_mul Onote.scale_eq_mul

instance nF_scale (x) [NF x] (o) [NF o] : NF (scale x o) := by rw [scale_eq_mul] <;> infer_instance
#align onote.NF_scale Onote.nF_scale

@[simp]
theorem repr_scale (x) [NF x] (o) [NF o] : repr (scale x o) = ω ^ repr x * repr o := by
  simp [scale_eq_mul]
#align onote.repr_scale Onote.repr_scale

theorem nF_repr_split {o o' m} [NF o] (h : split o = (o', m)) : NF o' ∧ repr o = repr o' + m :=
  by
  cases' e : split' o with a n
  cases' NF_repr_split' e with s₁ s₂; skip
  rw [split_eq_scale_split' e] at h
  injection h; substs o' n
  simp [repr_scale, s₂.symm]
  infer_instance
#align onote.NF_repr_split Onote.nF_repr_split

theorem split_dvd {o o' m} [NF o] (h : split o = (o', m)) : ω ∣ repr o' :=
  by
  cases' e : split' o with a n
  rw [split_eq_scale_split' e] at h
  injection h; subst o'
  cases NF_repr_split' e; skip; simp
#align onote.split_dvd Onote.split_dvd

theorem split_add_lt {o e n a m} [NF o] (h : split o = (oadd e n a, m)) : repr a + m < ω ^ repr e :=
  by
  cases' NF_repr_split h with h₁ h₂
  cases' h₁.of_dvd_omega (split_dvd h) with e0 d
  have := h₁.fst; have := h₁.snd
  apply principal_add_omega_opow _ h₁.snd'.repr_lt (lt_of_lt_of_le (nat_lt_omega _) _)
  simpa using opow_le_opow_right omega_pos (one_le_iff_ne_zero.2 e0)
#align onote.split_add_lt Onote.split_add_lt

@[simp]
theorem mulNat_eq_mul (n o) : mulNat o n = o * ofNat n := by cases o <;> cases n <;> rfl
#align onote.mul_nat_eq_mul Onote.mulNat_eq_mul

instance nF_mulNat (o) [NF o] (n) : NF (mulNat o n) := by simp <;> infer_instance
#align onote.NF_mul_nat Onote.nF_mulNat

instance nF_opowAux (e a0 a) [NF e] [NF a0] [NF a] : ∀ k m, NF (opowAux e a0 a k m)
  | k, 0 => by cases k <;> exact NF.zero
  | 0, m + 1 => NF.oadd_zero _ _
  | k + 1, m + 1 => by
    haveI := NF_opow_aux k <;> simp [opow_aux, Nat.succ_ne_zero] <;> infer_instance
#align onote.NF_opow_aux Onote.nF_opowAux

instance nF_opow (o₁ o₂) [NF o₁] [NF o₂] : NF (o₁ ^ o₂) :=
  by
  cases' e₁ : split o₁ with a m
  have na := (NF_repr_split e₁).1
  cases' e₂ : split' o₂ with b' k
  haveI := (NF_repr_split' e₂).1
  cases' a with a0 n a'
  · cases' m with m
    · by_cases o₂ = 0 <;> simp [pow, opow, *] <;> infer_instance
    · by_cases m = 0
      · simp only [pow, opow, *, zero_def]
        infer_instance
      · simp [pow, opow, *, -npow_eq_pow]
        infer_instance
  · simp [pow, opow, e₁, e₂, split_eq_scale_split' e₂]
    have := na.fst
    cases' k with k <;> simp [opow] <;> skip <;> infer_instance
#align onote.NF_opow Onote.nF_opow

theorem scale_opowAux (e a0 a : Onote) [NF e] [NF a0] [NF a] :
    ∀ k m, repr (opowAux e a0 a k m) = ω ^ repr e * repr (opowAux 0 a0 a k m)
  | 0, m => by cases m <;> simp [opow_aux]
  | k + 1, m => by
    by_cases m = 0 <;> simp [h, opow_aux, mul_add, opow_add, mul_assoc, scale_opow_aux]
#align onote.scale_opow_aux Onote.scale_opowAux

theorem repr_opow_aux₁ {e a} [Ne : NF e] [Na : NF a] {a' : Ordinal} (e0 : repr e ≠ 0)
    (h : a' < (ω : Ordinal.{0}) ^ repr e) (aa : repr a = a') (n : ℕ+) :
    ((ω : Ordinal.{0}) ^ repr e * (n : ℕ) + a') ^ (ω : Ordinal.{0}) =
      (ω ^ repr e) ^ (ω : Ordinal.{0}) :=
  by
  subst aa
  have No := Ne.oadd n (Na.below_of_lt' h)
  have := omega_le_oadd e n a; unfold repr at this
  refine' le_antisymm _ (opow_le_opow_left _ this)
  apply (opow_le_of_limit ((opow_pos _ omega_pos).trans_le this).ne' omega_is_limit).2
  intro b l
  have := (No.below_of_lt (lt_succ _)).repr_lt; unfold repr at this
  apply (opow_le_opow_left b <| this.le).trans
  rw [← opow_mul, ← opow_mul]
  apply opow_le_opow_right omega_pos
  cases' le_or_lt ω (repr e) with h h
  · apply (mul_le_mul_left' (le_succ b) _).trans
    rw [← add_one_eq_succ, add_mul_succ _ (one_add_of_omega_le h), add_one_eq_succ, succ_le_iff,
      mul_lt_mul_iff_left (Ordinal.pos_iff_ne_zero.2 e0)]
    exact omega_is_limit.2 _ l
  · apply (principal_mul_omega (omega_is_limit.2 _ h) l).le.trans
    simpa using mul_le_mul_right' (one_le_iff_ne_zero.2 e0) ω
#align onote.repr_opow_aux₁ Onote.repr_opow_aux₁

section

-- mathport name: ordinal.pow
local infixr:0 "^" => @pow Ordinal.{0} Ordinal Ordinal.hasPow

theorem repr_opow_aux₂ {a0 a'} [N0 : NF a0] [Na' : NF a'] (m : ℕ) (d : ω ∣ repr a')
    (e0 : repr a0 ≠ 0) (h : repr a' + m < (ω^repr a0)) (n : ℕ+) (k : ℕ) :
    let R := repr (opowAux 0 a0 (oadd a0 n a' * ofNat m) k m)
    (k ≠ 0 → R < ((ω^repr a0)^succ k)) ∧
      ((ω^repr a0)^k) * ((ω^repr a0) * (n : ℕ) + repr a') + R =
        ((ω^repr a0) * (n : ℕ) + repr a' + m^succ k) :=
  by
  intro
  haveI No : NF (oadd a0 n a') :=
    N0.oadd n (Na'.below_of_lt' <| lt_of_le_of_lt (le_add_right _ _) h)
  induction' k with k IH
  · cases m <;> simp [opow_aux, R]
  rename' R => R'
  let R := repr (opow_aux 0 a0 (oadd a0 n a' * of_nat m) k m)
  let ω0 := ω^repr a0
  let α' := ω0 * n + repr a'
  change (k ≠ 0 → R < (ω0^succ k)) ∧ (ω0^k) * α' + R = (α' + m^succ k) at IH
  have RR : R' = (ω0^k) * (α' * m) + R :=
    by
    by_cases m = 0 <;> simp [h, R', opow_aux, R, opow_mul]
    · cases k <;> simp [opow_aux]
    · rfl
  have α0 : 0 < α' := by simpa [α', lt_def, repr] using oadd_pos a0 n a'
  have ω00 : 0 < (ω0^k) := opow_pos _ (opow_pos _ omega_pos)
  have Rl : R < (ω^repr a0 * succ ↑k) := by
    by_cases k0 : k = 0
    · simp [k0]
      refine' lt_of_lt_of_le _ (opow_le_opow_right omega_pos (one_le_iff_ne_zero.2 e0))
      cases' m with m <;> simp [k0, R, opow_aux, omega_pos]
      rw [← add_one_eq_succ, ← Nat.cast_succ]
      apply nat_lt_omega
    · rw [opow_mul]
      exact IH.1 k0
  refine' ⟨fun _ => _, _⟩
  · rw [RR, ← opow_mul _ _ (succ k.succ)]
    have e0 := Ordinal.pos_iff_ne_zero.2 e0
    have rr0 := lt_of_lt_of_le e0 (le_add_left _ _)
    apply principal_add_omega_opow
    · simp [opow_mul, ω0, opow_add, mul_assoc]
      rw [mul_lt_mul_iff_left ω00, ← Ordinal.opow_add]
      have := (No.below_of_lt _).repr_lt
      unfold repr at this
      refine' mul_lt_omega_opow rr0 this (nat_lt_omega _)
      simpa using (add_lt_add_iff_left (repr a0)).2 e0
    ·
      refine'
        lt_of_lt_of_le Rl
          (opow_le_opow_right omega_pos <|
            mul_le_mul_left' (succ_le_succ_iff.2 (nat_cast_le.2 (le_of_lt k.lt_succ_self))) _)
  calc
    (ω0^k.succ) * α' + R' = (ω0^succ k) * α' + ((ω0^k) * α' * m + R) := by
      rw [nat_cast_succ, RR, ← mul_assoc]
    _ = ((ω0^k) * α' + R) * α' + ((ω0^k) * α' + R) * m := _
    _ = (α' + m^succ k.succ) := by rw [← mul_add, nat_cast_succ, opow_succ, IH.2]
    
  congr 1
  · have αd : ω ∣ α' :=
      dvd_add (dvd_mul_of_dvd_left (by simpa using opow_dvd_opow ω (one_le_iff_ne_zero.2 e0)) _) d
    rw [mul_add (ω0^k), add_assoc, ← mul_assoc, ← opow_succ,
      add_mul_limit _ (is_limit_iff_omega_dvd.2 ⟨ne_of_gt α0, αd⟩), mul_assoc,
      @mul_omega_dvd n (nat_cast_pos.2 n.pos) (nat_lt_omega _) _ αd]
    apply @add_absorp _ (repr a0 * succ k)
    · refine' principal_add_omega_opow _ _ Rl
      rw [opow_mul, opow_succ, mul_lt_mul_iff_left ω00]
      exact No.snd'.repr_lt
    · have := mul_le_mul_left' (one_le_iff_pos.2 <| nat_cast_pos.2 n.pos) (ω0^succ k)
      rw [opow_mul]
      simpa [-opow_succ]
  · cases m
    · have : R = 0 := by cases k <;> simp [R, opow_aux]
      simp [this]
    · rw [nat_cast_succ, add_mul_succ]
      apply add_absorp Rl
      rw [opow_mul, opow_succ]
      apply mul_le_mul_left'
      simpa [α', repr] using omega_le_oadd a0 n a'
#align onote.repr_opow_aux₂ Onote.repr_opow_aux₂

end

theorem repr_opow (o₁ o₂) [NF o₁] [NF o₂] : repr (o₁ ^ o₂) = repr o₁ ^ repr o₂ :=
  by
  cases' e₁ : split o₁ with a m
  cases' NF_repr_split e₁ with N₁ r₁
  cases' a with a0 n a'
  · cases' m with m
    · by_cases o₂ = 0 <;> simp [opow_def, opow, e₁, h, r₁]
      have := mt repr_inj.1 h
      rw [zero_opow this]
    · cases' e₂ : split' o₂ with b' k
      cases' NF_repr_split' e₂ with _ r₂
      by_cases m = 0 <;> simp [opow_def, opow, e₁, h, r₁, e₂, r₂, -Nat.cast_succ]
      rw [opow_add, opow_mul, opow_omega _ (nat_lt_omega _)]
      simpa using nat_cast_lt.2 (Nat.succ_lt_succ <| pos_iff_ne_zero.2 h)
  · haveI := N₁.fst
    haveI := N₁.snd
    cases' N₁.of_dvd_omega (split_dvd e₁) with a00 ad
    have al := split_add_lt e₁
    have aa : repr (a' + of_nat m) = repr a' + m := by simp
    cases' e₂ : split' o₂ with b' k
    cases' NF_repr_split' e₂ with _ r₂
    simp [opow_def, opow, e₁, r₁, split_eq_scale_split' e₂]
    cases' k with k <;> skip
    · simp [opow, r₂, opow_mul, repr_opow_aux₁ a00 al aa, add_assoc]
    · simp [opow, r₂, opow_add, opow_mul, mul_assoc, add_assoc]
      rw [repr_opow_aux₁ a00 al aa, scale_opow_aux]
      simp [opow_mul]
      rw [← mul_add, ← add_assoc ((ω : Ordinal.{0}) ^ repr a0 * (n : ℕ))]
      congr 1
      rw [← opow_succ]
      exact (repr_opow_aux₂ _ ad a00 al _ _).2
#align onote.repr_opow Onote.repr_opow

/-- Given an ordinal, returns `inl none` for `0`, `inl (some a)` for `a+1`, and
  `inr f` for a limit ordinal `a`, where `f i` is a sequence converging to `a`. -/
def fundamentalSequence : Onote → Sum (Option Onote) (ℕ → Onote)
  | zero => Sum.inl none
  | oadd a m b =>
    match fundamental_sequence b with
    | Sum.inr f => Sum.inr fun i => oadd a m (f i)
    | Sum.inl (some b') => Sum.inl (some (oadd a m b'))
    | Sum.inl none =>
      match fundamental_sequence a, m.natPred with
      | Sum.inl none, 0 => Sum.inl (some zero)
      | Sum.inl none, m + 1 => Sum.inl (some (oadd zero m.succPNat zero))
      | Sum.inl (some a'), 0 => Sum.inr fun i => oadd a' i.succPNat zero
      | Sum.inl (some a'), m + 1 => Sum.inr fun i => oadd a m.succPNat (oadd a' i.succPNat zero)
      | Sum.inr f, 0 => Sum.inr fun i => oadd (f i) 1 zero
      | Sum.inr f, m + 1 => Sum.inr fun i => oadd a m.succPNat (oadd (f i) 1 zero)
#align onote.fundamental_sequence Onote.fundamentalSequence

private theorem exists_lt_add {α} [hα : Nonempty α] {o : Ordinal} {f : α → Ordinal}
    (H : ∀ ⦃a⦄, a < o → ∃ i, a < f i) {b : Ordinal} ⦃a⦄ (h : a < b + o) : ∃ i, a < b + f i :=
  by
  cases' lt_or_le a b with h h'
  · obtain ⟨i⟩ := id hα
    exact ⟨i, h.trans_le (le_add_right _ _)⟩
  · rw [← Ordinal.add_sub_cancel_of_le h', add_lt_add_iff_left] at h
    refine' (H h).imp fun i H => _
    rwa [← Ordinal.add_sub_cancel_of_le h', add_lt_add_iff_left]
#align onote.exists_lt_add onote.exists_lt_add

private theorem exists_lt_mul_omega' {o : Ordinal} ⦃a⦄ (h : a < o * ω) : ∃ i : ℕ, a < o * ↑i + o :=
  by
  obtain ⟨i, hi, h'⟩ := (lt_mul_of_limit omega_is_limit).1 h
  obtain ⟨i, rfl⟩ := lt_omega.1 hi
  exact ⟨i, h'.trans_le (le_add_right _ _)⟩
#align onote.exists_lt_mul_omega' onote.exists_lt_mul_omega'

-- mathport name: ordinal.pow
local infixr:0 "^" => @pow Ordinal Ordinal Ordinal.hasPow

private theorem exists_lt_omega_opow' {α} {o b : Ordinal} (hb : 1 < b) (ho : o.IsLimit)
    {f : α → Ordinal} (H : ∀ ⦃a⦄, a < o → ∃ i, a < f i) ⦃a⦄ (h : a < (b^o)) : ∃ i, a < (b^f i) :=
  by
  obtain ⟨d, hd, h'⟩ := (lt_opow_of_limit (zero_lt_one.trans hb).ne' ho).1 h
  exact (H hd).imp fun i hi => h'.trans <| (opow_lt_opow_iff_right hb).2 hi
#align onote.exists_lt_omega_opow' onote.exists_lt_omega_opow'

/-- The property satisfied by `fundamental_sequence o`:
  * `inl none` means `o = 0`
  * `inl (some a)` means `o = succ a`
  * `inr f` means `o` is a limit ordinal and `f` is a
    strictly increasing sequence which converges to `o` -/
def FundamentalSequenceProp (o : Onote) : Sum (Option Onote) (ℕ → Onote) → Prop
  | Sum.inl none => o = 0
  | Sum.inl (some a) => o.repr = succ a.repr ∧ (o.NF → a.NF)
  | Sum.inr f =>
    o.repr.IsLimit ∧
      (∀ i, f i < f (i + 1) ∧ f i < o ∧ (o.NF → (f i).NF)) ∧ ∀ a, a < o.repr → ∃ i, a < (f i).repr
#align onote.fundamental_sequence_prop Onote.FundamentalSequenceProp

theorem fundamentalSequence_has_prop (o) : FundamentalSequenceProp o (fundamentalSequence o) :=
  by
  induction' o with a m b iha ihb; · exact rfl
  rw [fundamental_sequence]
  rcases e : b.fundamental_sequence with (⟨_ | b'⟩ | f) <;>
      simp only [fundamental_sequence, fundamental_sequence_prop] <;>
    rw [e, fundamental_sequence_prop] at ihb
  · rcases e : a.fundamental_sequence with (⟨_ | a'⟩ | f) <;> cases' e' : m.nat_pred with m' <;>
              simp only [fundamental_sequence, fundamental_sequence_prop] <;>
            rw [e, fundamental_sequence_prop] at iha <;>
          try
            rw [show m = 1 by have := PNat.natPred_add_one m; rw [e'] at this;
                exact PNat.coe_inj.1 this.symm] <;>
        try
          rw [show m = m'.succ.succ_pnat by
              rw [← e', ← PNat.coe_inj, Nat.succPNat_coe, ← Nat.add_one, PNat.natPred_add_one]] <;>
      simp only [repr, iha, ihb, opow_lt_opow_iff_right one_lt_omega, add_lt_add_iff_left, add_zero,
        coe_coe, eq_self_iff_true, lt_add_iff_pos_right, lt_def, mul_one, Nat.cast_zero,
        Nat.cast_succ, Nat.succPNat_coe, opow_succ, opow_zero, mul_add_one, PNat.one_coe, succ_zero,
        true_and_iff, _root_.zero_add, zero_def]
    · infer_instance
    · exact ⟨rfl, inferInstance⟩
    · have := opow_pos _ omega_pos
      refine'
        ⟨mul_is_limit this omega_is_limit, fun i =>
          ⟨this, _, fun H => @NF.oadd_zero _ _ (iha.2 H.fst)⟩, exists_lt_mul_omega'⟩
      rw [← mul_succ, ← nat_cast_succ, Ordinal.mul_lt_mul_iff_left this]
      apply nat_lt_omega
    · have := opow_pos _ omega_pos
      refine'
        ⟨add_is_limit _ (mul_is_limit this omega_is_limit), fun i => ⟨this, _, _⟩,
          exists_lt_add exists_lt_mul_omega'⟩
      · rw [← mul_succ, ← nat_cast_succ, Ordinal.mul_lt_mul_iff_left this]
        apply nat_lt_omega
      · refine' fun H => H.fst.oadd _ (NF.below_of_lt' _ (@NF.oadd_zero _ _ (iha.2 H.fst)))
        rw [repr, repr, add_zero, iha.1, opow_succ, Ordinal.mul_lt_mul_iff_left this]
        apply nat_lt_omega
    · rcases iha with ⟨h1, h2, h3⟩
      refine' ⟨opow_is_limit one_lt_omega h1, fun i => _, exists_lt_omega_opow' one_lt_omega h1 h3⟩
      obtain ⟨h4, h5, h6⟩ := h2 i
      exact ⟨h4, h5, fun H => @NF.oadd_zero _ _ (h6 H.fst)⟩
    · rcases iha with ⟨h1, h2, h3⟩
      refine'
        ⟨add_is_limit _ (opow_is_limit one_lt_omega h1), fun i => _,
          exists_lt_add (exists_lt_omega_opow' one_lt_omega h1 h3)⟩
      obtain ⟨h4, h5, h6⟩ := h2 i
      refine' ⟨h4, h5, fun H => H.fst.oadd _ (NF.below_of_lt' _ (@NF.oadd_zero _ _ (h6 H.fst)))⟩
      rwa [repr, repr, add_zero, coe_coe, PNat.one_coe, Nat.cast_one, mul_one,
        opow_lt_opow_iff_right one_lt_omega]
  · refine'
      ⟨by rw [repr, ihb.1, add_succ, repr], fun H => H.fst.oadd _ (NF.below_of_lt' _ (ihb.2 H.snd))⟩
    have := H.snd'.repr_lt
    rw [ihb.1] at this
    exact (lt_succ _).trans this
  · rcases ihb with ⟨h1, h2, h3⟩
    simp only [repr]
    exact
      ⟨Ordinal.add_isLimit _ h1, fun i =>
        ⟨oadd_lt_oadd_3 (h2 i).1, oadd_lt_oadd_3 (h2 i).2.1, fun H =>
          H.fst.oadd _ (NF.below_of_lt' (lt_trans (h2 i).2.1 H.snd'.repr_lt) ((h2 i).2.2 H.snd))⟩,
        exists_lt_add h3⟩
#align onote.fundamental_sequence_has_prop Onote.fundamentalSequence_has_prop

/-- The fast growing hierarchy for ordinal notations `< ε₀`. This is a sequence of
functions `ℕ → ℕ` indexed by ordinals, with the definition:
* `f_0(n) = n + 1`
* `f_(α+1)(n) = f_α^[n](n)`
* `f_α(n) = f_(α[n])(n)` where `α` is a limit ordinal
   and `α[i]` is the fundamental sequence converging to `α` -/
def fastGrowing : Onote → ℕ → ℕ
  | o =>
    match fundamentalSequence o, fundamentalSequence_has_prop o with
    | Sum.inl none, _ => Nat.succ
    | Sum.inl (some a), h =>
      have : a < o := by rw [lt_def, h.1]; apply lt_succ
      fun i => (fast_growing a^[i]) i
    | Sum.inr f, h => fun i =>
      have : f i < o := (h.2.1 i).2.1
      fast_growing (f i) i termination_by'
  ⟨_, InvImage.wf repr Ordinal.lt_wf⟩
#align onote.fast_growing Onote.fastGrowing

theorem fastGrowing_def {o : Onote} {x} (e : fundamentalSequence o = x) :
    fastGrowing o =
      FastGrowing._match1 o (fun a _ _ => a.fastGrowing) (fun f _ i _ => (f i).fastGrowing i) x
        (e ▸ fundamentalSequence_has_prop _) :=
  by
  subst x
  rw [fast_growing]
#align onote.fast_growing_def Onote.fastGrowing_def

theorem fastGrowing_zero' (o : Onote) (h : fundamentalSequence o = Sum.inl none) :
    fastGrowing o = Nat.succ := by
  rw [fast_growing_def h]
  rfl
#align onote.fast_growing_zero' Onote.fastGrowing_zero'

theorem fastGrowing_succ (o) {a} (h : fundamentalSequence o = Sum.inl (some a)) :
    fastGrowing o = fun i => (fastGrowing a^[i]) i :=
  by
  rw [fast_growing_def h]
  rfl
#align onote.fast_growing_succ Onote.fastGrowing_succ

theorem fastGrowing_limit (o) {f} (h : fundamentalSequence o = Sum.inr f) :
    fastGrowing o = fun i => fastGrowing (f i) i :=
  by
  rw [fast_growing_def h]
  rfl
#align onote.fast_growing_limit Onote.fastGrowing_limit

@[simp]
theorem fastGrowing_zero : fastGrowing 0 = Nat.succ :=
  fastGrowing_zero' _ rfl
#align onote.fast_growing_zero Onote.fastGrowing_zero

@[simp]
theorem fastGrowing_one : fastGrowing 1 = fun n => 2 * n :=
  by
  rw [@fast_growing_succ 1 0 rfl]; funext i; rw [two_mul, fast_growing_zero]
  suffices : ∀ a b, (Nat.succ^[a]) b = b + a; exact this _ _
  intro a b; induction a <;> simp [*, Function.iterate_succ', Nat.add_succ]
#align onote.fast_growing_one Onote.fastGrowing_one

section

-- mathport name: pow
local infixr:0 "^" => pow

@[simp]
theorem fastGrowing_two : fastGrowing 2 = fun n => (2^n) * n :=
  by
  rw [@fast_growing_succ 2 1 rfl]; funext i; rw [fast_growing_one]
  suffices : ∀ a b, ((fun n : ℕ => 2 * n)^[a]) b = (2^a) * b; exact this _ _
  intro a b; induction a <;> simp [*, Function.iterate_succ', pow_succ, mul_assoc]
#align onote.fast_growing_two Onote.fastGrowing_two

end

/-- We can extend the fast growing hierarchy one more step to `ε₀` itself,
  using `ω^(ω^...^ω^0)` as the fundamental sequence converging to `ε₀` (which is not an `onote`).
  Extending the fast growing hierarchy beyond this requires a definition of fundamental sequence
  for larger ordinals. -/
def fastGrowingε₀ (i : ℕ) : ℕ :=
  fastGrowing (((fun a => a.oadd 1 0)^[i]) 0) i
#align onote.fast_growing_ε₀ Onote.fastGrowingε₀

theorem fastGrowingε₀_zero : fastGrowingε₀ 0 = 1 := by simp [fast_growing_ε₀]
#align onote.fast_growing_ε₀_zero Onote.fastGrowingε₀_zero

theorem fastGrowingε₀_one : fastGrowingε₀ 1 = 2 := by
  simp [fast_growing_ε₀, show oadd 0 1 0 = 1 from rfl]
#align onote.fast_growing_ε₀_one Onote.fastGrowingε₀_one

theorem fastGrowingε₀_two : fastGrowingε₀ 2 = 2048 := by
  norm_num [fast_growing_ε₀, show oadd 0 1 0 = 1 from rfl, @fast_growing_limit (oadd 1 1 0) _ rfl,
    show oadd 0 (2 : Nat).succPNat 0 = 3 from rfl, @fast_growing_succ 3 2 rfl]
#align onote.fast_growing_ε₀_two Onote.fastGrowingε₀_two

end Onote

/-- The type of normal ordinal notations. (It would have been
  nicer to define this right in the inductive type, but `NF o`
  requires `repr` which requires `onote`, so all these things
  would have to be defined at once, which messes up the VM
  representation.) -/
def Nonote :=
  { o : Onote // o.NF }
#align nonote Nonote

instance : DecidableEq Nonote := by unfold Nonote <;> infer_instance

namespace Nonote

open Onote

instance nF (o : Nonote) : NF o.1 :=
  o.2
#align nonote.NF Nonote.nF

/-- Construct a `nonote` from an ordinal notation
  (and infer normality) -/
def mk (o : Onote) [h : NF o] : Nonote :=
  ⟨o, h⟩
#align nonote.mk Nonote.mk

/-- The ordinal represented by an ordinal notation.
  (This function is noncomputable because ordinal
  arithmetic is noncomputable. In computational applications
  `nonote` can be used exclusively without reference
  to `ordinal`, but this function allows for correctness
  results to be stated.) -/
noncomputable def repr (o : Nonote) : Ordinal :=
  o.1.repr
#align nonote.repr Nonote.repr

instance : ToString Nonote :=
  ⟨fun x => x.1.toString⟩

instance : Repr Nonote :=
  ⟨fun x => x.1.repr'⟩

instance : Preorder Nonote where
  le x y := repr x ≤ repr y
  lt x y := repr x < repr y
  le_refl a := @le_refl Ordinal _ _
  le_trans a b c := @le_trans Ordinal _ _ _ _
  lt_iff_le_not_le a b := @lt_iff_le_not_le Ordinal _ _ _

instance : Zero Nonote :=
  ⟨⟨0, NF.zero⟩⟩

instance : Inhabited Nonote :=
  ⟨0⟩

theorem lt_wf : @WellFounded Nonote (· < ·) :=
  InvImage.wf repr Ordinal.lt_wf
#align nonote.lt_wf Nonote.lt_wf

instance : WellFoundedLT Nonote :=
  ⟨lt_wf⟩

instance : WellFoundedRelation Nonote :=
  ⟨(· < ·), lt_wf⟩

/-- Convert a natural number to an ordinal notation -/
def ofNat (n : ℕ) : Nonote :=
  ⟨ofNat n, ⟨⟨_, nFBelow_ofNat _⟩⟩⟩
#align nonote.of_nat Nonote.ofNat

/-- Compare ordinal notations -/
def cmp (a b : Nonote) : Ordering :=
  cmp a.1 b.1
#align nonote.cmp Nonote.cmp

theorem cmp_compares : ∀ a b : Nonote, (cmp a b).Compares a b
  | ⟨a, ha⟩, ⟨b, hb⟩ => by
    skip
    dsimp [cmp]; have := Onote.cmp_compares a b
    cases Onote.cmp a b <;> try exact this
    exact Subtype.mk_eq_mk.2 this
#align nonote.cmp_compares Nonote.cmp_compares

instance : LinearOrder Nonote :=
  linearOrderOfCompares cmp cmp_compares

instance : IsWellOrder Nonote (· < ·) where

/-- Asserts that `repr a < ω ^ repr b`. Used in `nonote.rec_on` -/
def below (a b : Nonote) : Prop :=
  NFBelow a.1 (repr b)
#align nonote.below Nonote.below

/-- The `oadd` pseudo-constructor for `nonote` -/
def oadd (e : Nonote) (n : ℕ+) (a : Nonote) (h : below a e) : Nonote :=
  ⟨_, NF.oadd e.2 n h⟩
#align nonote.oadd Nonote.oadd

/-- This is a recursor-like theorem for `nonote` suggesting an
  inductive definition, which can't actually be defined this
  way due to conflicting dependencies. -/
@[elab_as_elim]
def recOn {C : Nonote → Sort _} (o : Nonote) (H0 : C 0)
    (H1 : ∀ e n a h, C e → C a → C (oadd e n a h)) : C o :=
  by
  cases' o with o h; induction' o with e n a IHe IHa
  · exact H0
  · exact H1 ⟨e, h.fst⟩ n ⟨a, h.snd⟩ h.snd' (IHe _) (IHa _)
#align nonote.rec_on Nonote.recOn

/-- Addition of ordinal notations -/
instance : Add Nonote :=
  ⟨fun x y => mk (x.1 + y.1)⟩

theorem repr_add (a b) : repr (a + b) = repr a + repr b :=
  Onote.repr_add a.1 b.1
#align nonote.repr_add Nonote.repr_add

/-- Subtraction of ordinal notations -/
instance : Sub Nonote :=
  ⟨fun x y => mk (x.1 - y.1)⟩

theorem repr_sub (a b) : repr (a - b) = repr a - repr b :=
  Onote.repr_sub a.1 b.1
#align nonote.repr_sub Nonote.repr_sub

/-- Multiplication of ordinal notations -/
instance : Mul Nonote :=
  ⟨fun x y => mk (x.1 * y.1)⟩

theorem repr_mul (a b) : repr (a * b) = repr a * repr b :=
  Onote.repr_mul a.1 b.1
#align nonote.repr_mul Nonote.repr_mul

/-- Exponentiation of ordinal notations -/
def opow (x y : Nonote) :=
  mk (x.1.opow y.1)
#align nonote.opow Nonote.opow

theorem repr_opow (a b) : repr (opow a b) = repr a ^ repr b :=
  Onote.repr_opow a.1 b.1
#align nonote.repr_opow Nonote.repr_opow

end Nonote

