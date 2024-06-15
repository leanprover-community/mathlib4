/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Init.Data.Ordering.Lemmas
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.Tactic.NormNum

#align_import set_theory.ordinal.notation from "leanprover-community/mathlib"@"b67044ba53af18680e1dd246861d9584e968495d"

/-!
# Ordinal notation

Constructive ordinal arithmetic for ordinals below `ε₀`.

We define a type `ONote`, with constructors `0 : ONote` and `ONote.oadd e n a` representing
`ω ^ e * n + a`.
We say that `o` is in Cantor normal form - `ONote.NF o` - if either `o = 0` or
`o = ω ^ e * n + a` with `a < ω ^ e` and `a` in Cantor normal form.

The type `NONote` is the type of ordinals below `ε₀` in Cantor normal form.
Various operations (addition, subtraction, multiplication, power function)
are defined on `ONote` and `NONote`.
-/

set_option linter.uppercaseLean3 false


open Ordinal Order

-- Porting note: the generated theorem is warned by `simpNF`.
set_option genSizeOfSpec false in
/-- Recursive definition of an ordinal notation. `zero` denotes the
  ordinal 0, and `oadd e n a` is intended to refer to `ω^e * n + a`.
  For this to be valid Cantor normal form, we must have the exponents
  decrease to the right, but we can't state this condition until we've
  defined `repr`, so it is a separate definition `NF`. -/
inductive ONote : Type
  | zero : ONote
  | oadd : ONote → ℕ+ → ONote → ONote
  deriving DecidableEq
#align onote ONote

compile_inductive% ONote

namespace ONote

/-- Notation for 0 -/
instance : Zero ONote :=
  ⟨zero⟩

@[simp]
theorem zero_def : zero = 0 :=
  rfl
#align onote.zero_def ONote.zero_def

instance : Inhabited ONote :=
  ⟨0⟩

/-- Notation for 1 -/
instance : One ONote :=
  ⟨oadd 0 1 0⟩

/-- Notation for ω -/
def omega : ONote :=
  oadd 1 1 0
#align onote.omega ONote.omega

/-- The ordinal denoted by a notation -/
@[simp]
noncomputable def repr : ONote → Ordinal.{0}
  | 0 => 0
  | oadd e n a => ω ^ repr e * n + repr a
#align onote.repr ONote.repr

/-- Auxiliary definition to print an ordinal notation -/
def toStringAux1 (e : ONote) (n : ℕ) (s : String) : String :=
  if e = 0 then toString n
  else (if e = 1 then "ω" else "ω^(" ++ s ++ ")") ++ if n = 1 then "" else "*" ++ toString n
#align onote.to_string_aux1 ONote.toStringAux1

/-- Print an ordinal notation -/
def toString : ONote → String
  | zero => "0"
  | oadd e n 0 => toStringAux1 e n (toString e)
  | oadd e n a => toStringAux1 e n (toString e) ++ " + " ++ toString a
#align onote.to_string ONote.toString

open Lean in
/-- Print an ordinal notation -/
def repr' (prec : ℕ) : ONote → Format
  | zero => "0"
  | oadd e n a =>
    Repr.addAppParen
      ("oadd " ++ (repr' max_prec e) ++ " " ++ Nat.repr (n : ℕ) ++ " " ++ (repr' max_prec a))
      prec
#align onote.repr' ONote.repr

instance : ToString ONote :=
  ⟨toString⟩

instance : Repr ONote where
  reprPrec o prec := repr' prec o

instance : Preorder ONote where
  le x y := repr x ≤ repr y
  lt x y := repr x < repr y
  le_refl _ := @le_refl Ordinal _ _
  le_trans _ _ _ := @le_trans Ordinal _ _ _ _
  lt_iff_le_not_le _ _ := @lt_iff_le_not_le Ordinal _ _ _

theorem lt_def {x y : ONote} : x < y ↔ repr x < repr y :=
  Iff.rfl
#align onote.lt_def ONote.lt_def

theorem le_def {x y : ONote} : x ≤ y ↔ repr x ≤ repr y :=
  Iff.rfl
#align onote.le_def ONote.le_def

instance : WellFoundedRelation ONote :=
  ⟨(· < ·), InvImage.wf repr Ordinal.lt_wf⟩

/-- Convert a `Nat` into an ordinal -/
@[coe]
def ofNat : ℕ → ONote
  | 0 => 0
  | Nat.succ n => oadd 0 n.succPNat 0
#align onote.of_nat ONote.ofNat

-- Porting note (#11467): during the port we marked these lemmas with `@[eqns]`
-- to emulate the old Lean 3 behaviour.

@[simp] theorem ofNat_zero : ofNat 0 = 0 :=
  rfl

@[simp] theorem ofNat_succ (n) : ofNat (Nat.succ n) = oadd 0 n.succPNat 0 :=
  rfl

instance nat (n : ℕ) : OfNat ONote n where
  ofNat := ofNat n

@[simp 1200]
theorem ofNat_one : ofNat 1 = 1 :=
  rfl
#align onote.of_nat_one ONote.ofNat_one

@[simp]
theorem repr_ofNat (n : ℕ) : repr (ofNat n) = n := by cases n <;> simp
#align onote.repr_of_nat ONote.repr_ofNat

-- @[simp] -- Porting note (#10618): simp can prove this
theorem repr_one : repr (ofNat 1) = (1 : ℕ) := repr_ofNat 1
#align onote.repr_one ONote.repr_one

theorem omega_le_oadd (e n a) : ω ^ repr e ≤ repr (oadd e n a) := by
  refine le_trans ?_ (le_add_right _ _)
  simpa using (Ordinal.mul_le_mul_iff_left <| opow_pos (repr e) omega_pos).2 (natCast_le.2 n.2)
#align onote.omega_le_oadd ONote.omega_le_oadd

theorem oadd_pos (e n a) : 0 < oadd e n a :=
  @lt_of_lt_of_le _ _ _ (ω ^ repr e) _ (opow_pos (repr e) omega_pos) (omega_le_oadd e n a)
#align onote.oadd_pos ONote.oadd_pos

/-- Compare ordinal notations -/
def cmp : ONote → ONote → Ordering
  | 0, 0 => Ordering.eq
  | _, 0 => Ordering.gt
  | 0, _ => Ordering.lt
  | _o₁@(oadd e₁ n₁ a₁), _o₂@(oadd e₂ n₂ a₂) =>
    (cmp e₁ e₂).orElse <| (_root_.cmp (n₁ : ℕ) n₂).orElse (cmp a₁ a₂)
#align onote.cmp ONote.cmp

theorem eq_of_cmp_eq : ∀ {o₁ o₂}, cmp o₁ o₂ = Ordering.eq → o₁ = o₂
  | 0, 0, _ => rfl
  | oadd e n a, 0, h => by injection h
  | 0, oadd e n a, h => by injection h
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, h => by
    revert h; simp only [cmp]
    cases h₁ : cmp e₁ e₂ <;> intro h <;> try cases h
    obtain rfl := eq_of_cmp_eq h₁
    revert h; cases h₂ : _root_.cmp (n₁ : ℕ) n₂ <;> intro h <;> try cases h
    obtain rfl := eq_of_cmp_eq h
    rw [_root_.cmp, cmpUsing_eq_eq] at h₂
    obtain rfl := Subtype.eq (eq_of_incomp h₂)
    simp
#align onote.eq_of_cmp_eq ONote.eq_of_cmp_eq

protected theorem zero_lt_one : (0 : ONote) < 1 := by
  simp only [lt_def, repr, opow_zero, Nat.succPNat_coe, Nat.cast_one, mul_one, add_zero,
    zero_lt_one]
#align onote.zero_lt_one ONote.zero_lt_one

/-- `NFBelow o b` says that `o` is a normal form ordinal notation
  satisfying `repr o < ω ^ b`. -/
inductive NFBelow : ONote → Ordinal.{0} → Prop
  | zero {b} : NFBelow 0 b
  | oadd' {e n a eb b} : NFBelow e eb → NFBelow a (repr e) → repr e < b → NFBelow (oadd e n a) b
#align onote.NF_below ONote.NFBelow

/-- A normal form ordinal notation has the form

     ω ^ a₁ * n₁ + ω ^ a₂ * n₂ + ... ω ^ aₖ * nₖ
  where `a₁ > a₂ > ... > aₖ` and all the `aᵢ` are
  also in normal form.

  We will essentially only be interested in normal form
  ordinal notations, but to avoid complicating the algorithms
  we define everything over general ordinal notations and
  only prove correctness with normal form as an invariant. -/
class NF (o : ONote) : Prop where
  out : Exists (NFBelow o)
#align onote.NF ONote.NF

instance NF.zero : NF 0 :=
  ⟨⟨0, NFBelow.zero⟩⟩
#align onote.NF.zero ONote.NF.zero

theorem NFBelow.oadd {e n a b} : NF e → NFBelow a (repr e) → repr e < b → NFBelow (oadd e n a) b
  | ⟨⟨_, h⟩⟩ => NFBelow.oadd' h
#align onote.NF_below.oadd ONote.NFBelow.oadd

theorem NFBelow.fst {e n a b} (h : NFBelow (ONote.oadd e n a) b) : NF e := by
  cases' h with _ _ _ _ eb _ h₁ h₂ h₃; exact ⟨⟨_, h₁⟩⟩
#align onote.NF_below.fst ONote.NFBelow.fst

theorem NF.fst {e n a} : NF (oadd e n a) → NF e
  | ⟨⟨_, h⟩⟩ => h.fst
#align onote.NF.fst ONote.NF.fst

theorem NFBelow.snd {e n a b} (h : NFBelow (ONote.oadd e n a) b) : NFBelow a (repr e) := by
  cases' h with _ _ _ _ eb _ h₁ h₂ h₃; exact h₂
#align onote.NF_below.snd ONote.NFBelow.snd

theorem NF.snd' {e n a} : NF (oadd e n a) → NFBelow a (repr e)
  | ⟨⟨_, h⟩⟩ => h.snd
#align onote.NF.snd' ONote.NF.snd'

theorem NF.snd {e n a} (h : NF (oadd e n a)) : NF a :=
  ⟨⟨_, h.snd'⟩⟩
#align onote.NF.snd ONote.NF.snd

theorem NF.oadd {e a} (h₁ : NF e) (n) (h₂ : NFBelow a (repr e)) : NF (oadd e n a) :=
  ⟨⟨_, NFBelow.oadd h₁ h₂ (lt_succ _)⟩⟩
#align onote.NF.oadd ONote.NF.oadd

instance NF.oadd_zero (e n) [h : NF e] : NF (ONote.oadd e n 0) :=
  h.oadd _ NFBelow.zero
#align onote.NF.oadd_zero ONote.NF.oadd_zero

theorem NFBelow.lt {e n a b} (h : NFBelow (ONote.oadd e n a) b) : repr e < b := by
  cases' h with _ _ _ _ eb _ h₁ h₂ h₃; exact h₃
#align onote.NF_below.lt ONote.NFBelow.lt

theorem NFBelow_zero : ∀ {o}, NFBelow o 0 ↔ o = 0
  | 0 => ⟨fun _ => rfl, fun _ => NFBelow.zero⟩
  | oadd _ _ _ =>
    ⟨fun h => (not_le_of_lt h.lt).elim (Ordinal.zero_le _), fun e => e.symm ▸ NFBelow.zero⟩
#align onote.NF_below_zero ONote.NFBelow_zero

theorem NF.zero_of_zero {e n a} (h : NF (ONote.oadd e n a)) (e0 : e = 0) : a = 0 := by
  simpa [e0, NFBelow_zero] using h.snd'
#align onote.NF.zero_of_zero ONote.NF.zero_of_zero

theorem NFBelow.repr_lt {o b} (h : NFBelow o b) : repr o < ω ^ b := by
  induction' h with _ e n a eb b h₁ h₂ h₃ _ IH
  · exact opow_pos _ omega_pos
  · rw [repr]
    apply ((add_lt_add_iff_left _).2 IH).trans_le
    rw [← mul_succ]
    apply (mul_le_mul_left' (succ_le_of_lt (nat_lt_omega _)) _).trans
    rw [← opow_succ]
    exact opow_le_opow_right omega_pos (succ_le_of_lt h₃)
#align onote.NF_below.repr_lt ONote.NFBelow.repr_lt

theorem NFBelow.mono {o b₁ b₂} (bb : b₁ ≤ b₂) (h : NFBelow o b₁) : NFBelow o b₂ := by
  induction' h with _ e n a eb b h₁ h₂ h₃ _ _ <;> constructor
  exacts [h₁, h₂, lt_of_lt_of_le h₃ bb]
#align onote.NF_below.mono ONote.NFBelow.mono

theorem NF.below_of_lt {e n a b} (H : repr e < b) :
    NF (ONote.oadd e n a) → NFBelow (ONote.oadd e n a) b
  | ⟨⟨b', h⟩⟩ => by (cases' h with _ _ _ _ eb _ h₁ h₂ h₃; exact NFBelow.oadd' h₁ h₂ H)
#align onote.NF.below_of_lt ONote.NF.below_of_lt

theorem NF.below_of_lt' : ∀ {o b}, repr o < ω ^ b → NF o → NFBelow o b
  | 0, _, _, _ => NFBelow.zero
  | ONote.oadd _ _ _, _, H, h =>
    h.below_of_lt <|
      (opow_lt_opow_iff_right one_lt_omega).1 <| lt_of_le_of_lt (omega_le_oadd _ _ _) H
#align onote.NF.below_of_lt' ONote.NF.below_of_lt'

theorem nfBelow_ofNat : ∀ n, NFBelow (ofNat n) 1
  | 0 => NFBelow.zero
  | Nat.succ _ => NFBelow.oadd NF.zero NFBelow.zero zero_lt_one
#align onote.NF_below_of_nat ONote.nfBelow_ofNat

instance nf_ofNat (n) : NF (ofNat n) :=
  ⟨⟨_, nfBelow_ofNat n⟩⟩
#align onote.NF_of_nat ONote.nf_ofNat

instance nf_one : NF 1 := by rw [← ofNat_one]; infer_instance
#align onote.NF_one ONote.nf_one

theorem oadd_lt_oadd_1 {e₁ n₁ o₁ e₂ n₂ o₂} (h₁ : NF (oadd e₁ n₁ o₁)) (h : e₁ < e₂) :
    oadd e₁ n₁ o₁ < oadd e₂ n₂ o₂ :=
  @lt_of_lt_of_le _ _ (repr (oadd e₁ n₁ o₁)) _ _
    (NF.below_of_lt h h₁).repr_lt (omega_le_oadd e₂ n₂ o₂)
#align onote.oadd_lt_oadd_1 ONote.oadd_lt_oadd_1

theorem oadd_lt_oadd_2 {e o₁ o₂ : ONote} {n₁ n₂ : ℕ+} (h₁ : NF (oadd e n₁ o₁)) (h : (n₁ : ℕ) < n₂) :
    oadd e n₁ o₁ < oadd e n₂ o₂ := by
  simp only [lt_def, repr]
  refine lt_of_lt_of_le ((add_lt_add_iff_left _).2 h₁.snd'.repr_lt) (le_trans ?_ (le_add_right _ _))
  rwa [← mul_succ,Ordinal.mul_le_mul_iff_left (opow_pos _ omega_pos), succ_le_iff, natCast_lt]
#align onote.oadd_lt_oadd_2 ONote.oadd_lt_oadd_2

theorem oadd_lt_oadd_3 {e n a₁ a₂} (h : a₁ < a₂) : oadd e n a₁ < oadd e n a₂ := by
  rw [lt_def]; unfold repr
  exact @add_lt_add_left _ _ _ _ (repr a₁) _ h _
#align onote.oadd_lt_oadd_3 ONote.oadd_lt_oadd_3

theorem cmp_compares : ∀ (a b : ONote) [NF a] [NF b], (cmp a b).Compares a b
  | 0, 0, _, _ => rfl
  | oadd e n a, 0, _, _ => oadd_pos _ _ _
  | 0, oadd e n a, _, _ => oadd_pos _ _ _
  | o₁@(oadd e₁ n₁ a₁), o₂@(oadd e₂ n₂ a₂), h₁, h₂ => by -- TODO: golf
    rw [cmp]
    have IHe := @cmp_compares _ _ h₁.fst h₂.fst
    simp only [Ordering.Compares, gt_iff_lt] at IHe; revert IHe
    cases cmp e₁ e₂
    case lt => intro IHe; exact oadd_lt_oadd_1 h₁ IHe
    case gt => intro IHe; exact oadd_lt_oadd_1 h₂ IHe
    case eq =>
      intro IHe; dsimp at IHe; subst IHe
      unfold _root_.cmp; cases nh : cmpUsing (· < ·) (n₁ : ℕ) n₂ <;>
      rw [cmpUsing, ite_eq_iff, not_lt] at nh
      case lt =>
        cases' nh with nh nh
        · exact oadd_lt_oadd_2 h₁ nh.left
        · rw [ite_eq_iff] at nh; cases' nh.right with nh nh <;> cases nh <;> contradiction
      case gt =>
        cases' nh with nh nh
        · cases nh; contradiction
        · cases' nh with _ nh
          rw [ite_eq_iff] at nh; cases' nh with nh nh
          · exact oadd_lt_oadd_2 h₂ nh.left
          · cases nh; contradiction
      cases' nh with nh nh
      · cases nh; contradiction
      cases' nh with nhl nhr
      rw [ite_eq_iff] at nhr
      cases' nhr with nhr nhr
      · cases nhr; contradiction
      obtain rfl := Subtype.eq (eq_of_incomp ⟨(not_lt_of_ge nhl), nhr.left⟩)
      have IHa := @cmp_compares _ _ h₁.snd h₂.snd
      revert IHa; cases cmp a₁ a₂ <;> intro IHa <;> dsimp at IHa
      case lt => exact oadd_lt_oadd_3 IHa
      case gt => exact oadd_lt_oadd_3 IHa
      subst IHa; exact rfl
#align onote.cmp_compares ONote.cmp_compares

theorem repr_inj {a b} [NF a] [NF b] : repr a = repr b ↔ a = b :=
  ⟨fun e => match cmp a b, cmp_compares a b with
    | Ordering.lt, (h : repr a < repr b) => (ne_of_lt h e).elim
    | Ordering.gt, (h : repr a > repr b)=> (ne_of_gt h e).elim
    | Ordering.eq, h => h,
    congr_arg _⟩
#align onote.repr_inj ONote.repr_inj

theorem NF.of_dvd_omega_opow {b e n a} (h : NF (ONote.oadd e n a))
    (d : ω ^ b ∣ repr (ONote.oadd e n a)) :
    b ≤ repr e ∧ ω ^ b ∣ repr a := by
  have := mt repr_inj.1 (fun h => by injection h : ONote.oadd e n a ≠ 0)
  have L := le_of_not_lt fun l => not_le_of_lt (h.below_of_lt l).repr_lt (le_of_dvd this d)
  simp only [repr] at d
  exact ⟨L, (dvd_add_iff <| (opow_dvd_opow _ L).mul_right _).1 d⟩
#align onote.NF.of_dvd_omega_opow ONote.NF.of_dvd_omega_opow

theorem NF.of_dvd_omega {e n a} (h : NF (ONote.oadd e n a)) :
    ω ∣ repr (ONote.oadd e n a) → repr e ≠ 0 ∧ ω ∣ repr a := by
  (rw [← opow_one ω, ← one_le_iff_ne_zero]; exact h.of_dvd_omega_opow)
#align onote.NF.of_dvd_omega ONote.NF.of_dvd_omega

/-- `TopBelow b o` asserts that the largest exponent in `o`, if
  it exists, is less than `b`. This is an auxiliary definition
  for decidability of `NF`. -/
def TopBelow (b : ONote) : ONote → Prop
  | 0 => True
  | oadd e _ _ => cmp e b = Ordering.lt
#align onote.top_below ONote.TopBelow

instance decidableTopBelow : DecidableRel TopBelow := by
  intro b o
  cases o <;> delta TopBelow <;> infer_instance
#align onote.decidable_top_below ONote.decidableTopBelow

theorem nfBelow_iff_topBelow {b} [NF b] : ∀ {o}, NFBelow o (repr b) ↔ NF o ∧ TopBelow b o
  | 0 => ⟨fun h => ⟨⟨⟨_, h⟩⟩, trivial⟩, fun _ => NFBelow.zero⟩
  | oadd _ _ _ =>
    ⟨fun h => ⟨⟨⟨_, h⟩⟩, (@cmp_compares _ b h.fst _).eq_lt.2 h.lt⟩, fun ⟨h₁, h₂⟩ =>
      h₁.below_of_lt <| (@cmp_compares _ b h₁.fst _).eq_lt.1 h₂⟩
#align onote.NF_below_iff_top_below ONote.nfBelow_iff_topBelow

instance decidableNF : DecidablePred NF
  | 0 => isTrue NF.zero
  | oadd e n a => by
    have := decidableNF e
    have := decidableNF a
    apply decidable_of_iff (NF e ∧ NF a ∧ TopBelow e a)
    rw [← and_congr_right fun h => @nfBelow_iff_topBelow _ h _]
    exact ⟨fun ⟨h₁, h₂⟩ => NF.oadd h₁ n h₂, fun h => ⟨h.fst, h.snd'⟩⟩
#align onote.decidable_NF ONote.decidableNF

/-- Auxiliary definition for `add` -/
def addAux (e : ONote) (n : ℕ+) (o : ONote) : ONote :=
    match o with
    | 0 => oadd e n 0
    | o'@(oadd e' n' a') =>
      match cmp e e' with
      | Ordering.lt => o'
      | Ordering.eq => oadd e (n + n') a'
      | Ordering.gt => oadd e n o'

/-- Addition of ordinal notations (correct only for normal input) -/
def add : ONote → ONote → ONote
  | 0, o => o
  | oadd e n a, o => addAux e n (add a o)
#align onote.add ONote.add

instance : Add ONote :=
  ⟨add⟩

@[simp]
theorem zero_add (o : ONote) : 0 + o = o :=
  rfl
#align onote.zero_add ONote.zero_add

theorem oadd_add (e n a o) : oadd e n a + o = addAux e n (a + o) :=
  rfl
#align onote.oadd_add ONote.oadd_add

/-- Subtraction of ordinal notations (correct only for normal input) -/
def sub : ONote → ONote → ONote
  | 0, _ => 0
  | o, 0 => o
  | o₁@(oadd e₁ n₁ a₁), oadd e₂ n₂ a₂ =>
    match cmp e₁ e₂ with
    | Ordering.lt => 0
    | Ordering.gt => o₁
    | Ordering.eq =>
      match (n₁ : ℕ) - n₂ with
      | 0 => if n₁ = n₂ then sub a₁ a₂ else 0
      | Nat.succ k => oadd e₁ k.succPNat a₁
#align onote.sub ONote.sub

instance : Sub ONote :=
  ⟨sub⟩

theorem add_nfBelow {b} : ∀ {o₁ o₂}, NFBelow o₁ b → NFBelow o₂ b → NFBelow (o₁ + o₂) b
  | 0, _, _, h₂ => h₂
  | oadd e n a, o, h₁, h₂ => by
    have h' := add_nfBelow (h₁.snd.mono <| le_of_lt h₁.lt) h₂
    simp [oadd_add]; revert h'; cases' a + o with e' n' a' <;> intro h'
    · exact NFBelow.oadd h₁.fst NFBelow.zero h₁.lt
    have : ((e.cmp e').Compares e e') := @cmp_compares _ _ h₁.fst h'.fst
    cases h: cmp e e' <;> dsimp [addAux] <;> simp [h]
    · exact h'
    · simp [h] at this
      subst e'
      exact NFBelow.oadd h'.fst h'.snd h'.lt
    · simp [h] at this
      exact NFBelow.oadd h₁.fst (NF.below_of_lt this ⟨⟨_, h'⟩⟩) h₁.lt
#align onote.add_NF_below ONote.add_nfBelow

instance add_nf (o₁ o₂) : ∀ [NF o₁] [NF o₂], NF (o₁ + o₂)
  | ⟨⟨b₁, h₁⟩⟩, ⟨⟨b₂, h₂⟩⟩ =>
    ⟨(le_total b₁ b₂).elim (fun h => ⟨b₂, add_nfBelow (h₁.mono h) h₂⟩) fun h =>
        ⟨b₁, add_nfBelow h₁ (h₂.mono h)⟩⟩
#align onote.add_NF ONote.add_nf

@[simp]
theorem repr_add : ∀ (o₁ o₂) [NF o₁] [NF o₂], repr (o₁ + o₂) = repr o₁ + repr o₂
  | 0, o, _, _ => by simp
  | oadd e n a, o, h₁, h₂ => by
    haveI := h₁.snd; have h' := repr_add a o
    conv_lhs at h' => simp [HAdd.hAdd, Add.add]
    have nf := ONote.add_nf a o
    conv at nf => simp [HAdd.hAdd, Add.add]
    conv in _ + o => simp [HAdd.hAdd, Add.add]
    cases' h : add a o with e' n' a' <;>
      simp only [Add.add, add, addAux, h'.symm, h, add_assoc, repr] at nf h₁ ⊢
    have := h₁.fst; haveI := nf.fst; have ee := cmp_compares e e'
    cases he: cmp e e' <;> simp only [he, Ordering.compares_gt, Ordering.compares_lt,
        Ordering.compares_eq, repr, gt_iff_lt, PNat.add_coe, Nat.cast_add] at ee ⊢
    · rw [← add_assoc, @add_absorp _ (repr e') (ω ^ repr e' * (n' : ℕ))]
      · have := (h₁.below_of_lt ee).repr_lt
        unfold repr at this
        cases he': e' <;> simp only [he', zero_def, opow_zero, repr, gt_iff_lt] at this ⊢ <;>
        exact lt_of_le_of_lt (le_add_right _ _) this
      · simpa using (Ordinal.mul_le_mul_iff_left <| opow_pos (repr e') omega_pos).2
          (natCast_le.2 n'.pos)
    · rw [ee, ← add_assoc, ← mul_add]
#align onote.repr_add ONote.repr_add

theorem sub_nfBelow : ∀ {o₁ o₂ b}, NFBelow o₁ b → NF o₂ → NFBelow (o₁ - o₂) b
  | 0, o, b, _, h₂ => by cases o <;> exact NFBelow.zero
  | oadd _ _ _, 0, _, h₁, _ => h₁
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, b, h₁, h₂ => by
    have h' := sub_nfBelow h₁.snd h₂.snd
    simp only [HSub.hSub, Sub.sub, sub] at h' ⊢
    have := @cmp_compares _ _ h₁.fst h₂.fst
    cases h : cmp e₁ e₂ <;> simp [sub]
    · apply NFBelow.zero
    · simp only [h, Ordering.compares_eq] at this
      subst e₂
      cases (n₁ : ℕ) - n₂ <;> simp [sub]
      · by_cases en : n₁ = n₂ <;> simp [en]
        · exact h'.mono (le_of_lt h₁.lt)
        · exact NFBelow.zero
      · exact NFBelow.oadd h₁.fst h₁.snd h₁.lt
    · exact h₁
#align onote.sub_NF_below ONote.sub_nfBelow

instance sub_nf (o₁ o₂) : ∀ [NF o₁] [NF o₂], NF (o₁ - o₂)
  | ⟨⟨b₁, h₁⟩⟩, h₂ => ⟨⟨b₁, sub_nfBelow h₁ h₂⟩⟩
#align onote.sub_NF ONote.sub_nf

@[simp]
theorem repr_sub : ∀ (o₁ o₂) [NF o₁] [NF o₂], repr (o₁ - o₂) = repr o₁ - repr o₂
  | 0, o, _, h₂ => by cases o <;> exact (Ordinal.zero_sub _).symm
  | oadd e n a, 0, _, _ => (Ordinal.sub_zero _).symm
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, h₁, h₂ => by
    haveI := h₁.snd; haveI := h₂.snd; have h' := repr_sub a₁ a₂
    conv_lhs at h' => dsimp [HSub.hSub, Sub.sub, sub]
    conv_lhs => dsimp only [HSub.hSub, Sub.sub]; dsimp only [sub]
    have ee := @cmp_compares _ _ h₁.fst h₂.fst
    cases h : cmp e₁ e₂ <;> simp only [h] at ee
    · rw [Ordinal.sub_eq_zero_iff_le.2]
      · rfl
      exact le_of_lt (oadd_lt_oadd_1 h₁ ee)
    · change e₁ = e₂ at ee
      subst e₂
      dsimp only
      cases mn : (n₁ : ℕ) - n₂ <;> dsimp only
      · by_cases en : n₁ = n₂
        · simpa [en]
        · simp only [en, ite_false]
          exact
            (Ordinal.sub_eq_zero_iff_le.2 <|
                le_of_lt <|
                  oadd_lt_oadd_2 h₁ <|
                    lt_of_le_of_ne (tsub_eq_zero_iff_le.1 mn) (mt PNat.eq en)).symm
      · simp [Nat.succPNat]
        rw [(tsub_eq_iff_eq_add_of_le <| le_of_lt <| Nat.lt_of_sub_eq_succ mn).1 mn, add_comm,
          Nat.cast_add, mul_add, add_assoc, add_sub_add_cancel]
        refine
          (Ordinal.sub_eq_of_add_eq <|
              add_absorp h₂.snd'.repr_lt <| le_trans ?_ (le_add_right _ _)).symm
        simpa using mul_le_mul_left' (natCast_le.2 <| Nat.succ_pos _) _
    · exact
        (Ordinal.sub_eq_of_add_eq <|
            add_absorp (h₂.below_of_lt ee).repr_lt <| omega_le_oadd _ _ _).symm
#align onote.repr_sub ONote.repr_sub

/-- Multiplication of ordinal notations (correct only for normal input) -/
def mul : ONote → ONote → ONote
  | 0, _ => 0
  | _, 0 => 0
  | o₁@(oadd e₁ n₁ a₁), oadd e₂ n₂ a₂ =>
    if e₂ = 0 then oadd e₁ (n₁ * n₂) a₁ else oadd (e₁ + e₂) n₂ (mul o₁ a₂)
#align onote.mul ONote.mul

instance : Mul ONote :=
  ⟨mul⟩

instance : MulZeroClass ONote where
  mul := (· * ·)
  zero := 0
  zero_mul o := by cases o <;> rfl
  mul_zero o := by cases o <;> rfl

theorem oadd_mul (e₁ n₁ a₁ e₂ n₂ a₂) :
    oadd e₁ n₁ a₁ * oadd e₂ n₂ a₂ =
      if e₂ = 0 then oadd e₁ (n₁ * n₂) a₁ else oadd (e₁ + e₂) n₂ (oadd e₁ n₁ a₁ * a₂) :=
  rfl
#align onote.oadd_mul ONote.oadd_mul

theorem oadd_mul_nfBelow {e₁ n₁ a₁ b₁} (h₁ : NFBelow (oadd e₁ n₁ a₁) b₁) :
    ∀ {o₂ b₂}, NFBelow o₂ b₂ → NFBelow (oadd e₁ n₁ a₁ * o₂) (repr e₁ + b₂)
  | 0, b₂, _ => NFBelow.zero
  | oadd e₂ n₂ a₂, b₂, h₂ => by
    have IH := oadd_mul_nfBelow h₁ h₂.snd
    by_cases e0 : e₂ = 0 <;> simp [e0, oadd_mul]
    · apply NFBelow.oadd h₁.fst h₁.snd
      simpa using (add_lt_add_iff_left (repr e₁)).2 (lt_of_le_of_lt (Ordinal.zero_le _) h₂.lt)
    · haveI := h₁.fst
      haveI := h₂.fst
      apply NFBelow.oadd
      · infer_instance
      · rwa [repr_add]
      · rw [repr_add, add_lt_add_iff_left]
        exact h₂.lt
#align onote.oadd_mul_NF_below ONote.oadd_mul_nfBelow

instance mul_nf : ∀ (o₁ o₂) [NF o₁] [NF o₂], NF (o₁ * o₂)
  | 0, o, _, h₂ => by cases o <;> exact NF.zero
  | oadd e n a, o, ⟨⟨b₁, hb₁⟩⟩, ⟨⟨b₂, hb₂⟩⟩ => ⟨⟨_, oadd_mul_nfBelow hb₁ hb₂⟩⟩
#align onote.mul_NF ONote.mul_nf

@[simp]
theorem repr_mul : ∀ (o₁ o₂) [NF o₁] [NF o₂], repr (o₁ * o₂) = repr o₁ * repr o₂
  | 0, o, _, h₂ => by cases o <;> exact (zero_mul _).symm
  | oadd e₁ n₁ a₁, 0, _, _ => (mul_zero _).symm
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, h₁, h₂ => by
    have IH : repr (mul _ _) = _ := @repr_mul _ _ h₁ h₂.snd
    conv =>
      lhs
      simp [(· * ·)]
    have ao : repr a₁ + ω ^ repr e₁ * (n₁ : ℕ) = ω ^ repr e₁ * (n₁ : ℕ) := by
      apply add_absorp h₁.snd'.repr_lt
      simpa using (Ordinal.mul_le_mul_iff_left <| opow_pos _ omega_pos).2 (natCast_le.2 n₁.2)
    by_cases e0 : e₂ = 0 <;> simp [e0, mul]
    · cases' Nat.exists_eq_succ_of_ne_zero n₂.ne_zero with x xe
      simp only [xe, h₂.zero_of_zero e0, repr, add_zero]
      rw [natCast_succ x, add_mul_succ _ ao, mul_assoc]
    · haveI := h₁.fst
      haveI := h₂.fst
      simp only [Mul.mul, mul, e0, ite_false, repr.eq_2, repr_add, opow_add, IH, repr, mul_add]
      rw [← mul_assoc]
      congr 2
      have := mt repr_inj.1 e0
      rw [add_mul_limit ao (opow_isLimit_left omega_isLimit this), mul_assoc,
        mul_omega_dvd (natCast_pos.2 n₁.pos) (nat_lt_omega _)]
      simpa using opow_dvd_opow ω (one_le_iff_ne_zero.2 this)
#align onote.repr_mul ONote.repr_mul

/-- Calculate division and remainder of `o` mod ω.
  `split' o = (a, n)` means `o = ω * a + n`. -/
def split' : ONote → ONote × ℕ
  | 0 => (0, 0)
  | oadd e n a =>
    if e = 0 then (0, n)
    else
      let (a', m) := split' a
      (oadd (e - 1) n a', m)
#align onote.split' ONote.split'

/-- Calculate division and remainder of `o` mod ω.
  `split o = (a, n)` means `o = a + n`, where `ω ∣ a`. -/
def split : ONote → ONote × ℕ
  | 0 => (0, 0)
  | oadd e n a =>
    if e = 0 then (0, n)
    else
      let (a', m) := split a
      (oadd e n a', m)
#align onote.split ONote.split

/-- `scale x o` is the ordinal notation for `ω ^ x * o`. -/
def scale (x : ONote) : ONote → ONote
  | 0 => 0
  | oadd e n a => oadd (x + e) n (scale x a)
#align onote.scale ONote.scale

/-- `mulNat o n` is the ordinal notation for `o * n`. -/
def mulNat : ONote → ℕ → ONote
  | 0, _ => 0
  | _, 0 => 0
  | oadd e n a, m + 1 => oadd e (n * m.succPNat) a
#align onote.mul_nat ONote.mulNat

/-- Auxiliary definition to compute the ordinal notation for the ordinal
exponentiation in `opow` -/
def opowAux (e a0 a : ONote) : ℕ → ℕ → ONote
  | _, 0 => 0
  | 0, m + 1 => oadd e m.succPNat 0
  | k + 1, m => scale (e + mulNat a0 k) a + (opowAux e a0 a k m)
#align onote.opow_aux ONote.opowAux

/-- Auxiliary definition to compute the ordinal notation for the ordinal
exponentiation in `opow` -/
def opowAux2 (o₂ : ONote) (o₁ : ONote × ℕ) : ONote :=
  match o₁ with
  | (0, 0) => if o₂ = 0 then 1 else 0
  | (0, 1) => 1
  | (0, m + 1) =>
    let (b', k) := split' o₂
    oadd b' (m.succPNat ^ k) 0
  | (a@(oadd a0 _ _), m) =>
    match split o₂ with
    | (b, 0) => oadd (a0 * b) 1 0
    | (b, k + 1) =>
      let eb := a0 * b
      scale (eb + mulNat a0 k) a + opowAux eb a0 (mulNat a m) k m

/-- `opow o₁ o₂` calculates the ordinal notation for
  the ordinal exponential `o₁ ^ o₂`. -/
def opow (o₁ o₂ : ONote) : ONote := opowAux2 o₂ (split o₁)
#align onote.opow ONote.opow

instance : Pow ONote ONote :=
  ⟨opow⟩

theorem opow_def (o₁ o₂ : ONote) : o₁ ^ o₂ = opowAux2 o₂ (split o₁) :=
  rfl
#align onote.opow_def ONote.opow_def

theorem split_eq_scale_split' : ∀ {o o' m} [NF o], split' o = (o', m) → split o = (scale 1 o', m)
  | 0, o', m, _, p => by injection p; substs o' m; rfl
  | oadd e n a, o', m, h, p => by
    by_cases e0 : e = 0 <;> simp [e0, split, split'] at p ⊢
    · rcases p with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
    · revert p
      cases' h' : split' a with a' m'
      haveI := h.fst
      haveI := h.snd
      simp only [split_eq_scale_split' h', and_imp]
      have : 1 + (e - 1) = e := by
        refine repr_inj.1 ?_
        simp only [repr_add, repr, opow_zero, Nat.succPNat_coe, Nat.cast_one, mul_one, add_zero,
          repr_sub]
        have := mt repr_inj.1 e0
        refine Ordinal.add_sub_cancel_of_le ?_
        have := one_le_iff_ne_zero.2 this
        exact this
      intros
      substs o' m
      simp [scale, this]
#align onote.split_eq_scale_split' ONote.split_eq_scale_split'

theorem nf_repr_split' : ∀ {o o' m} [NF o], split' o = (o', m) → NF o' ∧ repr o = ω * repr o' + m
  | 0, o', m, _, p => by injection p; substs o' m; simp [NF.zero]
  | oadd e n a, o', m, h, p => by
    by_cases e0 : e = 0 <;> simp [e0, split, split'] at p ⊢
    · rcases p with ⟨rfl, rfl⟩
      simp [h.zero_of_zero e0, NF.zero]
    · revert p
      cases' h' : split' a with a' m'
      haveI := h.fst
      haveI := h.snd
      cases' nf_repr_split' h' with IH₁ IH₂
      simp only [IH₂, and_imp]
      intros
      substs o' m
      have : (ω : Ordinal.{0}) ^ repr e = ω ^ (1 : Ordinal.{0}) * ω ^ (repr e - 1) := by
        have := mt repr_inj.1 e0
        rw [← opow_add, Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 this)]
      refine ⟨NF.oadd (by infer_instance) _ ?_, ?_⟩
      · simp at this ⊢
        refine
          IH₁.below_of_lt'
            ((Ordinal.mul_lt_mul_iff_left omega_pos).1 <| lt_of_le_of_lt (le_add_right _ m') ?_)
        rw [← this, ← IH₂]
        exact h.snd'.repr_lt
      · rw [this]
        simp [mul_add, mul_assoc, add_assoc]
#align onote.NF_repr_split' ONote.nf_repr_split'

theorem scale_eq_mul (x) [NF x] : ∀ (o) [NF o], scale x o = oadd x 1 0 * o
  | 0, _ => rfl
  | oadd e n a, h => by
    simp only [HMul.hMul]; simp only [scale]
    haveI := h.snd
    by_cases e0 : e = 0
    · simp_rw [scale_eq_mul]
      simp [Mul.mul, mul, scale_eq_mul, e0, h.zero_of_zero,
        show x + 0 = x from repr_inj.1 (by simp)]
    · simp [e0, Mul.mul, mul, scale_eq_mul, (· * ·)]
#align onote.scale_eq_mul ONote.scale_eq_mul

instance nf_scale (x) [NF x] (o) [NF o] : NF (scale x o) := by
  rw [scale_eq_mul]
  infer_instance
#align onote.NF_scale ONote.nf_scale

@[simp]
theorem repr_scale (x) [NF x] (o) [NF o] : repr (scale x o) = ω ^ repr x * repr o := by
  simp only [scale_eq_mul, repr_mul, repr, PNat.one_coe, Nat.cast_one, mul_one, add_zero]
#align onote.repr_scale ONote.repr_scale

theorem nf_repr_split {o o' m} [NF o] (h : split o = (o', m)) : NF o' ∧ repr o = repr o' + m := by
  cases' e : split' o with a n
  cases' nf_repr_split' e with s₁ s₂
  rw [split_eq_scale_split' e] at h
  injection h; substs o' n
  simp only [repr_scale, repr, opow_zero, Nat.succPNat_coe, Nat.cast_one, mul_one, add_zero,
    opow_one, s₂.symm, and_true]
  infer_instance
#align onote.NF_repr_split ONote.nf_repr_split

theorem split_dvd {o o' m} [NF o] (h : split o = (o', m)) : ω ∣ repr o' := by
  cases' e : split' o with a n
  rw [split_eq_scale_split' e] at h
  injection h; subst o'
  cases nf_repr_split' e; simp
#align onote.split_dvd ONote.split_dvd

theorem split_add_lt {o e n a m} [NF o] (h : split o = (oadd e n a, m)) :
    repr a + m < ω ^ repr e := by
  cases' nf_repr_split h with h₁ h₂
  cases' h₁.of_dvd_omega (split_dvd h) with e0 d
  apply principal_add_omega_opow _ h₁.snd'.repr_lt (lt_of_lt_of_le (nat_lt_omega _) _)
  simpa using opow_le_opow_right omega_pos (one_le_iff_ne_zero.2 e0)
#align onote.split_add_lt ONote.split_add_lt

@[simp]
theorem mulNat_eq_mul (n o) : mulNat o n = o * ofNat n := by cases o <;> cases n <;> rfl
#align onote.mul_nat_eq_mul ONote.mulNat_eq_mul

instance nf_mulNat (o) [NF o] (n) : NF (mulNat o n) := by simp; exact ONote.mul_nf o (ofNat n)
#align onote.NF_mul_nat ONote.nf_mulNat

instance nf_opowAux (e a0 a) [NF e] [NF a0] [NF a] : ∀ k m, NF (opowAux e a0 a k m) := by
  intro k m
  unfold opowAux
  cases' m with m m
  · cases k <;> exact NF.zero
  cases' k with k k
  · exact NF.oadd_zero _ _
  · haveI := nf_opowAux e a0 a k
    simp only [Nat.succ_ne_zero m, IsEmpty.forall_iff, mulNat_eq_mul]; infer_instance
#align onote.NF_opow_aux ONote.nf_opowAux

instance nf_opow (o₁ o₂) [NF o₁] [NF o₂] : NF (o₁ ^ o₂) := by
  cases' e₁ : split o₁ with a m
  have na := (nf_repr_split e₁).1
  cases' e₂ : split' o₂ with b' k
  haveI := (nf_repr_split' e₂).1
  cases' a with a0 n a'
  · cases' m with m
    · by_cases o₂ = 0 <;> simp only [(· ^ ·), Pow.pow, pow, opow, opowAux2, *] <;> decide
    · by_cases m = 0
      · simp only [(· ^ ·), Pow.pow, pow, opow, opowAux2, *, zero_def]
        decide
      · simp only [(· ^ ·), Pow.pow, pow, opow, opowAux2, mulNat_eq_mul, ofNat, *]
        infer_instance
  · simp [(· ^ ·),Pow.pow,pow, opow, opowAux2, e₁, e₂, split_eq_scale_split' e₂]
    have := na.fst
    cases' k with k <;> simp
    · infer_instance
    · cases k <;> cases m <;> infer_instance
#align onote.NF_opow ONote.nf_opow

theorem scale_opowAux (e a0 a : ONote) [NF e] [NF a0] [NF a] :
    ∀ k m, repr (opowAux e a0 a k m) = ω ^ repr e * repr (opowAux 0 a0 a k m)
  | 0, m => by cases m <;> simp [opowAux]
  | k + 1, m => by
    by_cases h : m = 0
    · simp [h, opowAux, mul_add, opow_add, mul_assoc, scale_opowAux _ _ _ k]
    · -- Porting note: rewrote proof
      rw [opowAux]; swap
      · assumption
      rw [opowAux]; swap
      · assumption
      rw [repr_add, repr_scale, scale_opowAux _ _ _ k]
      simp only [repr_add, repr_scale, opow_add, mul_assoc, zero_add, mul_add]
#align onote.scale_opow_aux ONote.scale_opowAux

theorem repr_opow_aux₁ {e a} [Ne : NF e] [Na : NF a] {a' : Ordinal} (e0 : repr e ≠ 0)
    (h : a' < (ω : Ordinal.{0}) ^ repr e) (aa : repr a = a') (n : ℕ+) :
    ((ω : Ordinal.{0}) ^ repr e * (n : ℕ) + a') ^ (ω : Ordinal.{0}) =
      (ω ^ repr e) ^ (ω : Ordinal.{0}) := by
  subst aa
  have No := Ne.oadd n (Na.below_of_lt' h)
  have := omega_le_oadd e n a
  rw [repr] at this
  refine le_antisymm ?_ (opow_le_opow_left _ this)
  apply (opow_le_of_limit ((opow_pos _ omega_pos).trans_le this).ne' omega_isLimit).2
  intro b l
  have := (No.below_of_lt (lt_succ _)).repr_lt
  rw [repr] at this
  apply (opow_le_opow_left b <| this.le).trans
  rw [← opow_mul, ← opow_mul]
  apply opow_le_opow_right omega_pos
  rcases le_or_lt ω (repr e) with h | h
  · apply (mul_le_mul_left' (le_succ b) _).trans
    rw [← add_one_eq_succ, add_mul_succ _ (one_add_of_omega_le h), add_one_eq_succ, succ_le_iff,
      Ordinal.mul_lt_mul_iff_left (Ordinal.pos_iff_ne_zero.2 e0)]
    exact omega_isLimit.2 _ l
  · apply (principal_mul_omega (omega_isLimit.2 _ h) l).le.trans
    simpa using mul_le_mul_right' (one_le_iff_ne_zero.2 e0) ω
#align onote.repr_opow_aux₁ ONote.repr_opow_aux₁

section

-- Porting note: `R'` is used in the proof but marked as an unused variable.
set_option linter.unusedVariables false in
theorem repr_opow_aux₂ {a0 a'} [N0 : NF a0] [Na' : NF a'] (m : ℕ) (d : ω ∣ repr a')
    (e0 : repr a0 ≠ 0) (h : repr a' + m < (ω ^ repr a0)) (n : ℕ+) (k : ℕ) :
    let R := repr (opowAux 0 a0 (oadd a0 n a' * ofNat m) k m)
    (k ≠ 0 → R < ((ω ^ repr a0) ^ succ (k : Ordinal))) ∧
      ((ω ^ repr a0) ^ (k : Ordinal)) * ((ω ^ repr a0) * (n : ℕ) + repr a') + R =
        ((ω ^ repr a0) * (n : ℕ) + repr a' + m) ^ succ (k : Ordinal) := by
  intro R'
  haveI No : NF (oadd a0 n a') :=
    N0.oadd n (Na'.below_of_lt' <| lt_of_le_of_lt (le_add_right _ _) h)
  induction' k with k IH
  · cases m <;> simp [R', opowAux]
  -- rename R => R'
  let R := repr (opowAux 0 a0 (oadd a0 n a' * ofNat m) k m)
  let ω0 := ω ^ repr a0
  let α' := ω0 * n + repr a'
  change (k ≠ 0 → R < (ω0 ^ succ (k : Ordinal))) ∧ (ω0 ^ (k : Ordinal)) * α' + R
    = (α' + m) ^ (succ ↑k : Ordinal) at IH
  have RR : R' = ω0 ^ (k : Ordinal) * (α' * m) + R := by
    by_cases h : m = 0
    · simp only [R, R', h, ONote.ofNat, Nat.cast_zero, zero_add, ONote.repr, mul_zero,
        ONote.opowAux, add_zero]
    · simp only [R', ONote.repr_scale, ONote.repr, ONote.mulNat_eq_mul, ONote.opowAux,
        ONote.repr_ofNat, ONote.repr_mul, ONote.repr_add, Ordinal.opow_mul, ONote.zero_add]
  have α0 : 0 < α' := by simpa [lt_def, repr] using oadd_pos a0 n a'
  have ω00 : 0 < ω0 ^ (k : Ordinal) := opow_pos _ (opow_pos _ omega_pos)
  have Rl : R < ω ^ (repr a0 * succ ↑k) := by
    by_cases k0 : k = 0
    · simp [R, k0]
      refine lt_of_lt_of_le ?_ (opow_le_opow_right omega_pos (one_le_iff_ne_zero.2 e0))
      cases' m with m <;> simp [opowAux, omega_pos]
      rw [← add_one_eq_succ, ← Nat.cast_succ]
      apply nat_lt_omega
    · rw [opow_mul]
      exact IH.1 k0
  refine ⟨fun _ => ?_, ?_⟩
  · rw [RR, ← opow_mul _ _ (succ k.succ)]
    have e0 := Ordinal.pos_iff_ne_zero.2 e0
    have rr0 : 0 < repr a0 + repr a0 := lt_of_lt_of_le e0 (le_add_left _ _)
    apply principal_add_omega_opow
    · simp [opow_mul, opow_add, mul_assoc]
      rw [Ordinal.mul_lt_mul_iff_left ω00, ← Ordinal.opow_add]
      have : _ < ω ^ (repr a0 + repr a0) := (No.below_of_lt ?_).repr_lt
      · exact mul_lt_omega_opow rr0 this (nat_lt_omega _)
      · simpa using (add_lt_add_iff_left (repr a0)).2 e0
    · exact
        lt_of_lt_of_le Rl
          (opow_le_opow_right omega_pos <|
            mul_le_mul_left' (succ_le_succ_iff.2 (natCast_le.2 (le_of_lt k.lt_succ_self))) _)
  calc
    (ω0 ^ (k.succ : Ordinal)) * α' + R'
    _ = (ω0 ^ succ (k : Ordinal)) * α' + ((ω0 ^ (k : Ordinal)) * α' * m + R) := by
        rw [natCast_succ, RR, ← mul_assoc]
    _ = ((ω0 ^ (k : Ordinal)) * α' + R) * α' + ((ω0 ^ (k : Ordinal)) * α' + R) * m := ?_
    _ = (α' + m) ^ succ (k.succ : Ordinal) := by rw [← mul_add, natCast_succ, opow_succ, IH.2]
  congr 1
  · have αd : ω ∣ α' :=
      dvd_add (dvd_mul_of_dvd_left (by simpa using opow_dvd_opow ω (one_le_iff_ne_zero.2 e0)) _) d
    rw [mul_add (ω0 ^ (k : Ordinal)), add_assoc, ← mul_assoc, ← opow_succ,
      add_mul_limit _ (isLimit_iff_omega_dvd.2 ⟨ne_of_gt α0, αd⟩), mul_assoc,
      @mul_omega_dvd n (natCast_pos.2 n.pos) (nat_lt_omega _) _ αd]
    apply @add_absorp _ (repr a0 * succ ↑k)
    · refine principal_add_omega_opow _ ?_ Rl
      rw [opow_mul, opow_succ, Ordinal.mul_lt_mul_iff_left ω00]
      exact No.snd'.repr_lt
    · have := mul_le_mul_left' (one_le_iff_pos.2 <| natCast_pos.2 n.pos) (ω0 ^ succ (k : Ordinal))
      rw [opow_mul]
      simpa [-opow_succ]
  · cases m
    · have : R = 0 := by cases k <;> simp [R, opowAux]
      simp [this]
    · rw [natCast_succ, add_mul_succ]
      apply add_absorp Rl
      rw [opow_mul, opow_succ]
      apply mul_le_mul_left'
      simpa [repr] using omega_le_oadd a0 n a'
#align onote.repr_opow_aux₂ ONote.repr_opow_aux₂

end

theorem repr_opow (o₁ o₂) [NF o₁] [NF o₂] : repr (o₁ ^ o₂) = repr o₁ ^ repr o₂ := by
  cases' e₁ : split o₁ with a m
  cases' nf_repr_split e₁ with N₁ r₁
  cases' a with a0 n a'
  · cases' m with m
    · by_cases h : o₂ = 0 <;> simp [opow_def, opowAux2, opow, e₁, h, r₁]
      have := mt repr_inj.1 h
      rw [zero_opow this]
    · cases' e₂ : split' o₂ with b' k
      cases' nf_repr_split' e₂ with _ r₂
      by_cases h : m = 0
      · simp [opow_def, opow, e₁, h, r₁, e₂, r₂, ← Nat.one_eq_succ_zero]
      simp only [opow_def, opowAux2, opow, e₁, h, r₁, e₂, r₂, repr,
          opow_zero, Nat.succPNat_coe, Nat.cast_succ, Nat.cast_zero, _root_.zero_add, mul_one,
          add_zero, one_opow, npow_eq_pow]
      rw [opow_add, opow_mul, opow_omega, add_one_eq_succ]
      · congr
        conv_lhs =>
          dsimp [(· ^ ·)]
          simp [Pow.pow, opow, Ordinal.succ_ne_zero]
      · simpa [Nat.one_le_iff_ne_zero]
      · rw [← Nat.cast_succ, lt_omega]
        exact ⟨_, rfl⟩
  · haveI := N₁.fst
    haveI := N₁.snd
    cases' N₁.of_dvd_omega (split_dvd e₁) with a00 ad
    have al := split_add_lt e₁
    have aa : repr (a' + ofNat m) = repr a' + m := by
      simp only [eq_self_iff_true, ONote.repr_ofNat, ONote.repr_add]
    cases' e₂ : split' o₂ with b' k
    cases' nf_repr_split' e₂ with _ r₂
    simp only [opow_def, opow, e₁, r₁, split_eq_scale_split' e₂, opowAux2, repr]
    cases' k with k
    · simp [r₂, opow_mul, repr_opow_aux₁ a00 al aa, add_assoc]
    · simp? [r₂, opow_add, opow_mul, mul_assoc, add_assoc, -repr] says
        simp only [mulNat_eq_mul, repr_add, repr_scale, repr_mul, repr_ofNat, opow_add, opow_mul,
          mul_assoc, add_assoc, r₂, Nat.cast_add, Nat.cast_one, add_one_eq_succ, opow_succ]
      simp only [repr, opow_zero, Nat.succPNat_coe, Nat.cast_one, mul_one, add_zero, opow_one]
      rw [repr_opow_aux₁ a00 al aa, scale_opowAux]
      simp only [repr_mul, repr_scale, repr, opow_zero, Nat.succPNat_coe, Nat.cast_one, mul_one,
        add_zero, opow_one, opow_mul]
      rw [← mul_add, ← add_assoc ((ω : Ordinal.{0}) ^ repr a0 * (n : ℕ))]
      congr 1
      rw [← opow_succ]
      exact (repr_opow_aux₂ _ ad a00 al _ _).2
#align onote.repr_opow ONote.repr_opow

/-- Given an ordinal, returns `inl none` for `0`, `inl (some a)` for `a+1`, and
  `inr f` for a limit ordinal `a`, where `f i` is a sequence converging to `a`. -/
def fundamentalSequence : ONote → Sum (Option ONote) (ℕ → ONote)
  | zero => Sum.inl none
  | oadd a m b =>
    match fundamentalSequence b with
    | Sum.inr f => Sum.inr fun i => oadd a m (f i)
    | Sum.inl (some b') => Sum.inl (some (oadd a m b'))
    | Sum.inl none =>
      match fundamentalSequence a, m.natPred with
      | Sum.inl none, 0 => Sum.inl (some zero)
      | Sum.inl none, m + 1 => Sum.inl (some (oadd zero m.succPNat zero))
      | Sum.inl (some a'), 0 => Sum.inr fun i => oadd a' i.succPNat zero
      | Sum.inl (some a'), m + 1 => Sum.inr fun i => oadd a m.succPNat (oadd a' i.succPNat zero)
      | Sum.inr f, 0 => Sum.inr fun i => oadd (f i) 1 zero
      | Sum.inr f, m + 1 => Sum.inr fun i => oadd a m.succPNat (oadd (f i) 1 zero)
#align onote.fundamental_sequence ONote.fundamentalSequence

private theorem exists_lt_add {α} [hα : Nonempty α] {o : Ordinal} {f : α → Ordinal}
    (H : ∀ ⦃a⦄, a < o → ∃ i, a < f i) {b : Ordinal} ⦃a⦄ (h : a < b + o) : ∃ i, a < b + f i := by
  cases' lt_or_le a b with h h'
  · obtain ⟨i⟩ := id hα
    exact ⟨i, h.trans_le (le_add_right _ _)⟩
  · rw [← Ordinal.add_sub_cancel_of_le h', add_lt_add_iff_left] at h
    refine (H h).imp fun i H => ?_
    rwa [← Ordinal.add_sub_cancel_of_le h', add_lt_add_iff_left]

private theorem exists_lt_mul_omega' {o : Ordinal} ⦃a⦄ (h : a < o * ω) :
    ∃ i : ℕ, a < o * ↑i + o := by
  obtain ⟨i, hi, h'⟩ := (lt_mul_of_limit omega_isLimit).1 h
  obtain ⟨i, rfl⟩ := lt_omega.1 hi
  exact ⟨i, h'.trans_le (le_add_right _ _)⟩

private theorem exists_lt_omega_opow' {α} {o b : Ordinal} (hb : 1 < b) (ho : o.IsLimit)
    {f : α → Ordinal} (H : ∀ ⦃a⦄, a < o → ∃ i, a < f i) ⦃a⦄ (h : a < b ^ o) :
        ∃ i, a < b ^ f i := by
  obtain ⟨d, hd, h'⟩ := (lt_opow_of_limit (zero_lt_one.trans hb).ne' ho).1 h
  exact (H hd).imp fun i hi => h'.trans <| (opow_lt_opow_iff_right hb).2 hi

/-- The property satisfied by `fundamentalSequence o`:
  * `inl none` means `o = 0`
  * `inl (some a)` means `o = succ a`
  * `inr f` means `o` is a limit ordinal and `f` is a
    strictly increasing sequence which converges to `o` -/
def FundamentalSequenceProp (o : ONote) : Sum (Option ONote) (ℕ → ONote) → Prop
  | Sum.inl none => o = 0
  | Sum.inl (some a) => o.repr = succ a.repr ∧ (o.NF → a.NF)
  | Sum.inr f =>
    o.repr.IsLimit ∧
      (∀ i, f i < f (i + 1) ∧ f i < o ∧ (o.NF → (f i).NF)) ∧ ∀ a, a < o.repr → ∃ i, a < (f i).repr
#align onote.fundamental_sequence_prop ONote.FundamentalSequenceProp

theorem fundamentalSequenceProp_inl_none (o) :
    FundamentalSequenceProp o (Sum.inl none) ↔ o = 0 :=
  Iff.rfl

theorem fundamentalSequenceProp_inl_some (o a) :
    FundamentalSequenceProp o (Sum.inl (some a)) ↔ o.repr = succ a.repr ∧ (o.NF → a.NF) :=
  Iff.rfl

theorem fundamentalSequenceProp_inr (o f) :
    FundamentalSequenceProp o (Sum.inr f) ↔
      o.repr.IsLimit ∧
        (∀ i, f i < f (i + 1) ∧ f i < o ∧ (o.NF → (f i).NF)) ∧
        ∀ a, a < o.repr → ∃ i, a < (f i).repr :=
  Iff.rfl

attribute
  [eqns
    fundamentalSequenceProp_inl_none
    fundamentalSequenceProp_inl_some
    fundamentalSequenceProp_inr]
  FundamentalSequenceProp

theorem fundamentalSequence_has_prop (o) : FundamentalSequenceProp o (fundamentalSequence o) := by
  induction' o with a m b iha ihb; · exact rfl
  rw [fundamentalSequence]
  rcases e : b.fundamentalSequence with (⟨_ | b'⟩ | f) <;>
    simp only [FundamentalSequenceProp] <;>
    rw [e, FundamentalSequenceProp] at ihb
  · rcases e : a.fundamentalSequence with (⟨_ | a'⟩ | f) <;> cases' e' : m.natPred with m' <;>
      simp only [FundamentalSequenceProp] <;>
      rw [e, FundamentalSequenceProp] at iha <;>
      (try rw [show m = 1 by
            have := PNat.natPred_add_one m; rw [e'] at this; exact PNat.coe_inj.1 this.symm]) <;>
      (try rw [show m = (m' + 1).succPNat by
              rw [← e', ← PNat.coe_inj, Nat.succPNat_coe, ← Nat.add_one, PNat.natPred_add_one]]) <;>
      simp only [repr, iha, ihb, opow_lt_opow_iff_right one_lt_omega, add_lt_add_iff_left, add_zero,
        eq_self_iff_true, lt_add_iff_pos_right, lt_def, mul_one, Nat.cast_zero, Nat.cast_succ,
        Nat.succPNat_coe, opow_succ, opow_zero, mul_add_one, PNat.one_coe, succ_zero,
        true_and_iff, _root_.zero_add, zero_def]
    · decide
    · exact ⟨rfl, inferInstance⟩
    · have := opow_pos (repr a') omega_pos
      refine
        ⟨mul_isLimit this omega_isLimit, fun i =>
          ⟨this, ?_, fun H => @NF.oadd_zero _ _ (iha.2 H.fst)⟩, exists_lt_mul_omega'⟩
      rw [← mul_succ, ← natCast_succ, Ordinal.mul_lt_mul_iff_left this]
      apply nat_lt_omega
    · have := opow_pos (repr a') omega_pos
      refine
        ⟨add_isLimit _ (mul_isLimit this omega_isLimit), fun i => ⟨this, ?_, ?_⟩,
          exists_lt_add exists_lt_mul_omega'⟩
      · rw [← mul_succ, ← natCast_succ, Ordinal.mul_lt_mul_iff_left this]
        apply nat_lt_omega
      · refine fun H => H.fst.oadd _ (NF.below_of_lt' ?_ (@NF.oadd_zero _ _ (iha.2 H.fst)))
        rw [repr, ← zero_def, repr, add_zero, iha.1, opow_succ, Ordinal.mul_lt_mul_iff_left this]
        apply nat_lt_omega
    · rcases iha with ⟨h1, h2, h3⟩
      refine ⟨opow_isLimit one_lt_omega h1, fun i => ?_, exists_lt_omega_opow' one_lt_omega h1 h3⟩
      obtain ⟨h4, h5, h6⟩ := h2 i
      exact ⟨h4, h5, fun H => @NF.oadd_zero _ _ (h6 H.fst)⟩
    · rcases iha with ⟨h1, h2, h3⟩
      refine
        ⟨add_isLimit _ (opow_isLimit one_lt_omega h1), fun i => ?_,
          exists_lt_add (exists_lt_omega_opow' one_lt_omega h1 h3)⟩
      obtain ⟨h4, h5, h6⟩ := h2 i
      refine ⟨h4, h5, fun H => H.fst.oadd _ (NF.below_of_lt' ?_ (@NF.oadd_zero _ _ (h6 H.fst)))⟩
      rwa [repr, ← zero_def, repr, add_zero, PNat.one_coe, Nat.cast_one, mul_one,
        opow_lt_opow_iff_right one_lt_omega]
  · refine ⟨by
      rw [repr, ihb.1, add_succ, repr], fun H => H.fst.oadd _ (NF.below_of_lt' ?_ (ihb.2 H.snd))⟩
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
#align onote.fundamental_sequence_has_prop ONote.fundamentalSequence_has_prop

/-- The fast growing hierarchy for ordinal notations `< ε₀`. This is a sequence of
functions `ℕ → ℕ` indexed by ordinals, with the definition:
* `f_0(n) = n + 1`
* `f_(α+1)(n) = f_α^[n](n)`
* `f_α(n) = f_(α[n])(n)` where `α` is a limit ordinal
   and `α[i]` is the fundamental sequence converging to `α` -/
def fastGrowing : ONote → ℕ → ℕ
  | o =>
    match fundamentalSequence o, fundamentalSequence_has_prop o with
    | Sum.inl none, _ => Nat.succ
    | Sum.inl (some a), h =>
      have : a < o := by rw [lt_def, h.1]; apply lt_succ
      fun i => (fastGrowing a)^[i] i
    | Sum.inr f, h => fun i =>
      have : f i < o := (h.2.1 i).2.1
      fastGrowing (f i) i
  termination_by o => o
#align onote.fast_growing ONote.fastGrowing

-- Porting note: the bug of the linter, should be fixed.
@[nolint unusedHavesSuffices]
theorem fastGrowing_def {o : ONote} {x} (e : fundamentalSequence o = x) :
    fastGrowing o =
      match
        (motive := (x : Option ONote ⊕ (ℕ → ONote)) → FundamentalSequenceProp o x → ℕ → ℕ)
        x, e ▸ fundamentalSequence_has_prop o with
      | Sum.inl none, _ => Nat.succ
      | Sum.inl (some a), _ =>
        fun i => (fastGrowing a)^[i] i
      | Sum.inr f, _ => fun i =>
        fastGrowing (f i) i := by
  subst x
  rw [fastGrowing]
#align onote.fast_growing_def ONote.fastGrowing_def

theorem fastGrowing_zero' (o : ONote) (h : fundamentalSequence o = Sum.inl none) :
    fastGrowing o = Nat.succ := by
  rw [fastGrowing_def h]
#align onote.fast_growing_zero' ONote.fastGrowing_zero'

theorem fastGrowing_succ (o) {a} (h : fundamentalSequence o = Sum.inl (some a)) :
    fastGrowing o = fun i => (fastGrowing a)^[i] i := by
  rw [fastGrowing_def h]
#align onote.fast_growing_succ ONote.fastGrowing_succ

theorem fastGrowing_limit (o) {f} (h : fundamentalSequence o = Sum.inr f) :
    fastGrowing o = fun i => fastGrowing (f i) i := by
  rw [fastGrowing_def h]
#align onote.fast_growing_limit ONote.fastGrowing_limit

@[simp]
theorem fastGrowing_zero : fastGrowing 0 = Nat.succ :=
  fastGrowing_zero' _ rfl
#align onote.fast_growing_zero ONote.fastGrowing_zero

@[simp]
theorem fastGrowing_one : fastGrowing 1 = fun n => 2 * n := by
  rw [@fastGrowing_succ 1 0 rfl]; funext i; rw [two_mul, fastGrowing_zero]
  suffices ∀ a b, Nat.succ^[a] b = b + a from this _ _
  intro a b; induction a <;> simp [*, Function.iterate_succ', Nat.add_assoc, -Function.iterate_succ]
#align onote.fast_growing_one ONote.fastGrowing_one

section

@[simp]
theorem fastGrowing_two : fastGrowing 2 = fun n => (2 ^ n) * n := by
  rw [@fastGrowing_succ 2 1 rfl]; funext i; rw [fastGrowing_one]
  suffices ∀ a b, (fun n : ℕ => 2 * n)^[a] b = (2 ^ a) * b from this _ _
  intro a b; induction a <;>
    simp [*, Function.iterate_succ, pow_succ, mul_assoc, -Function.iterate_succ]
#align onote.fast_growing_two ONote.fastGrowing_two

end

/-- We can extend the fast growing hierarchy one more step to `ε₀` itself,
  using `ω^(ω^...^ω^0)` as the fundamental sequence converging to `ε₀` (which is not an `ONote`).
  Extending the fast growing hierarchy beyond this requires a definition of fundamental sequence
  for larger ordinals. -/
def fastGrowingε₀ (i : ℕ) : ℕ :=
  fastGrowing ((fun a => a.oadd 1 0)^[i] 0) i
#align onote.fast_growing_ε₀ ONote.fastGrowingε₀

theorem fastGrowingε₀_zero : fastGrowingε₀ 0 = 1 := by simp [fastGrowingε₀]
#align onote.fast_growing_ε₀_zero ONote.fastGrowingε₀_zero

theorem fastGrowingε₀_one : fastGrowingε₀ 1 = 2 := by
  simp [fastGrowingε₀, show oadd 0 1 0 = 1 from rfl]
#align onote.fast_growing_ε₀_one ONote.fastGrowingε₀_one

theorem fastGrowingε₀_two : fastGrowingε₀ 2 = 2048 := by
  norm_num [fastGrowingε₀, show oadd 0 1 0 = 1 from rfl, @fastGrowing_limit (oadd 1 1 0) _ rfl,
    show oadd 0 (2 : Nat).succPNat 0 = 3 from rfl, @fastGrowing_succ 3 2 rfl]
#align onote.fast_growing_ε₀_two ONote.fastGrowingε₀_two

end ONote

/-- The type of normal ordinal notations. (It would have been
  nicer to define this right in the inductive type, but `NF o`
  requires `repr` which requires `ONote`, so all these things
  would have to be defined at once, which messes up the VM
  representation.) -/
def NONote :=
  { o : ONote // o.NF }
#align nonote NONote

instance : DecidableEq NONote := by unfold NONote; infer_instance

namespace NONote

open ONote

instance NF (o : NONote) : NF o.1 :=
  o.2
#align nonote.NF NONote.NF

/-- Construct a `NONote` from an ordinal notation
  (and infer normality) -/
def mk (o : ONote) [h : ONote.NF o] : NONote :=
  ⟨o, h⟩
#align nonote.mk NONote.mk

/-- The ordinal represented by an ordinal notation.
  (This function is noncomputable because ordinal
  arithmetic is noncomputable. In computational applications
  `NONote` can be used exclusively without reference
  to `Ordinal`, but this function allows for correctness
  results to be stated.) -/
noncomputable def repr (o : NONote) : Ordinal :=
  o.1.repr
#align nonote.repr NONote.repr

instance : ToString NONote :=
  ⟨fun x => x.1.toString⟩

instance : Repr NONote :=
  ⟨fun x prec => x.1.repr' prec⟩

instance : Preorder NONote where
  le x y := repr x ≤ repr y
  lt x y := repr x < repr y
  le_refl _ := @le_refl Ordinal _ _
  le_trans _ _ _ := @le_trans Ordinal _ _ _ _
  lt_iff_le_not_le _ _ := @lt_iff_le_not_le Ordinal _ _ _

instance : Zero NONote :=
  ⟨⟨0, NF.zero⟩⟩

instance : Inhabited NONote :=
  ⟨0⟩

theorem lt_wf : @WellFounded NONote (· < ·) :=
  InvImage.wf repr Ordinal.lt_wf
#align nonote.lt_wf NONote.lt_wf

instance : WellFoundedLT NONote :=
  ⟨lt_wf⟩

instance : WellFoundedRelation NONote :=
  ⟨(· < ·), lt_wf⟩

/-- Convert a natural number to an ordinal notation -/
def ofNat (n : ℕ) : NONote :=
  ⟨ONote.ofNat n, ⟨⟨_, nfBelow_ofNat _⟩⟩⟩
#align nonote.of_nat NONote.ofNat

/-- Compare ordinal notations -/
def cmp (a b : NONote) : Ordering :=
  ONote.cmp a.1 b.1
#align nonote.cmp NONote.cmp

theorem cmp_compares : ∀ a b : NONote, (cmp a b).Compares a b
  | ⟨a, ha⟩, ⟨b, hb⟩ => by
    dsimp [cmp]
    have := ONote.cmp_compares a b
    cases h : ONote.cmp a b <;> simp only [h] at this <;> try exact this
    exact Subtype.mk_eq_mk.2 this
#align nonote.cmp_compares NONote.cmp_compares

instance : LinearOrder NONote :=
  linearOrderOfCompares cmp cmp_compares

instance : IsWellOrder NONote (· < ·) where

/-- Asserts that `repr a < ω ^ repr b`. Used in `NONote.recOn` -/
def below (a b : NONote) : Prop :=
  NFBelow a.1 (repr b)
#align nonote.below NONote.below

/-- The `oadd` pseudo-constructor for `NONote` -/
def oadd (e : NONote) (n : ℕ+) (a : NONote) (h : below a e) : NONote :=
  ⟨_, NF.oadd e.2 n h⟩
#align nonote.oadd NONote.oadd

/-- This is a recursor-like theorem for `NONote` suggesting an
  inductive definition, which can't actually be defined this
  way due to conflicting dependencies. -/
@[elab_as_elim]
def recOn {C : NONote → Sort*} (o : NONote) (H0 : C 0)
    (H1 : ∀ e n a h, C e → C a → C (oadd e n a h)) : C o := by
  cases' o with o h; induction' o with e n a IHe IHa
  · exact H0
  · exact H1 ⟨e, h.fst⟩ n ⟨a, h.snd⟩ h.snd' (IHe _) (IHa _)
#align nonote.rec_on NONote.recOn

/-- Addition of ordinal notations -/
instance : Add NONote :=
  ⟨fun x y => mk (x.1 + y.1)⟩

theorem repr_add (a b) : repr (a + b) = repr a + repr b :=
  ONote.repr_add a.1 b.1
#align nonote.repr_add NONote.repr_add

/-- Subtraction of ordinal notations -/
instance : Sub NONote :=
  ⟨fun x y => mk (x.1 - y.1)⟩

theorem repr_sub (a b) : repr (a - b) = repr a - repr b :=
  ONote.repr_sub a.1 b.1
#align nonote.repr_sub NONote.repr_sub

/-- Multiplication of ordinal notations -/
instance : Mul NONote :=
  ⟨fun x y => mk (x.1 * y.1)⟩

theorem repr_mul (a b) : repr (a * b) = repr a * repr b :=
  ONote.repr_mul a.1 b.1
#align nonote.repr_mul NONote.repr_mul

/-- Exponentiation of ordinal notations -/
def opow (x y : NONote) :=
  mk (x.1 ^ y.1)
#align nonote.opow NONote.opow

theorem repr_opow (a b) : repr (opow a b) = repr a ^ repr b :=
  ONote.repr_opow a.1 b.1
#align nonote.repr_opow NONote.repr_opow

end NONote
