/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Data.Ordering.Lemmas
import Mathlib.Data.PNat.Basic
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.Tactic.NormNum

/-!
# Ordinal notation

Constructive ordinal arithmetic for ordinals below `ε₀`.

We define a type `ONote`, with constructors `0 : ONote` and `ONote.oadd e n a` representing
`ω ^ e * n + a`.
We say that `o` is in Cantor normal form - `ONote.NF o` - if either `o = 0` or
`o = ω ^ e * n + a` with `a < ω ^ e` and `a` in Cantor normal form.

The type `NONote` is the type of ordinals below `ε₀` in Cantor normal form.
Various operations (addition, subtraction, multiplication, exponentiation)
are defined on `ONote` and `NONote`.
-/



open Ordinal Order

-- The generated theorem `ONote.zero.sizeOf_spec` is flagged by `simpNF`,
-- and we don't otherwise need it.
set_option genSizeOfSpec false in
/-- Recursive definition of an ordinal notation. `zero` denotes the ordinal 0, and `oadd e n a` is
intended to refer to `ω ^ e * n + a`. For this to be a valid Cantor normal form, we must have the
exponents decrease to the right, but we can't state this condition until we've defined `repr`, so we
make it a separate definition `NF`. -/
inductive ONote : Type
  | zero : ONote
  | oadd : ONote → ℕ+ → ONote → ONote
  deriving DecidableEq

compile_inductive% ONote

namespace ONote

/-- Notation for 0 -/
instance : Zero ONote :=
  ⟨zero⟩

@[simp]
theorem zero_def : zero = 0 :=
  rfl

instance : Inhabited ONote :=
  ⟨0⟩

/-- Notation for 1 -/
instance : One ONote :=
  ⟨oadd 0 1 0⟩

/-- Notation for ω -/
def omega : ONote :=
  oadd 1 1 0

/-- The ordinal denoted by a notation -/
noncomputable def repr : ONote → Ordinal.{0}
  | 0 => 0
  | oadd e n a => ω ^ repr e * n + repr a
@[simp] theorem repr_zero : repr 0 = 0 := rfl
attribute [simp] repr.eq_1 repr.eq_2

/-- Print `ω^s*n`, omitting `s` if `e = 0` or `e = 1`, and omitting `n` if `n = 1` -/
private def toString_aux (e : ONote) (n : ℕ) (s : String) : String :=
  if e = 0 then toString n
  else (if e = 1 then "ω" else "ω^(" ++ s ++ ")") ++ if n = 1 then "" else "*" ++ toString n

/-- Print an ordinal notation -/
def toString : ONote → String
  | zero => "0"
  | oadd e n 0 => toString_aux e n (toString e)
  | oadd e n a => toString_aux e n (toString e) ++ " + " ++ toString a

open Lean in
/-- Print an ordinal notation -/
def repr' (prec : ℕ) : ONote → Format
  | zero => "0"
  | oadd e n a =>
    Repr.addAppParen
      ("oadd " ++ (repr' max_prec e) ++ " " ++ Nat.repr (n : ℕ) ++ " " ++ (repr' max_prec a))
      prec

instance : ToString ONote :=
  ⟨toString⟩

instance : Repr ONote where
  reprPrec o prec := repr' prec o

instance : Preorder ONote where
  le x y := repr x ≤ repr y
  lt x y := repr x < repr y
  le_refl _ := @le_refl Ordinal _ _
  le_trans _ _ _ := @le_trans Ordinal _ _ _ _
  lt_iff_le_not_ge _ _ := @lt_iff_le_not_ge Ordinal _ _ _

theorem lt_def {x y : ONote} : x < y ↔ repr x < repr y :=
  Iff.rfl

theorem le_def {x y : ONote} : x ≤ y ↔ repr x ≤ repr y :=
  Iff.rfl

@[gcongr] alias ⟨repr_le_repr, _⟩ := le_def
@[gcongr] alias ⟨repr_lt_repr, _⟩ := lt_def

instance : WellFoundedRelation ONote :=
  ⟨(· < ·), InvImage.wf repr Ordinal.lt_wf⟩

/-- Convert a `Nat` into an ordinal -/
@[coe] def ofNat : ℕ → ONote
  | 0 => 0
  | Nat.succ n => oadd 0 n.succPNat 0

@[simp] theorem ofNat_zero : ofNat 0 = 0 :=
  rfl

@[simp] theorem ofNat_succ (n) : ofNat (Nat.succ n) = oadd 0 n.succPNat 0 :=
  rfl

instance (priority := low) nat (n : ℕ) : OfNat ONote n where
  ofNat := ofNat n

@[simp 1200] theorem ofNat_one : ofNat 1 = 1 := rfl

@[simp] theorem repr_ofNat (n : ℕ) : repr (ofNat n) = n := by cases n <;> simp

@[simp] theorem repr_one : repr 1 = (1 : ℕ) := repr_ofNat 1

theorem omega0_le_oadd (e n a) : ω ^ repr e ≤ repr (oadd e n a) := by
  refine le_trans ?_ (le_add_right _ _)
  simpa using (mul_le_mul_iff_right₀ <| opow_pos (repr e) omega0_pos).2 (Nat.cast_le.2 n.2)

theorem oadd_pos (e n a) : 0 < oadd e n a :=
  @lt_of_lt_of_le _ _ _ (ω ^ repr e) _ (opow_pos (repr e) omega0_pos) (omega0_le_oadd e n a)

/-- Comparison of ordinal notations:

`ω ^ e₁ * n₁ + a₁` is less than `ω ^ e₂ * n₂ + a₂` when either `e₁ < e₂`, or `e₁ = e₂` and
`n₁ < n₂`, or `e₁ = e₂`, `n₁ = n₂`, and `a₁ < a₂`. -/
def cmp : ONote → ONote → Ordering
  | 0, 0 => Ordering.eq
  | _, 0 => Ordering.gt
  | 0, _ => Ordering.lt
  | _o₁@(oadd e₁ n₁ a₁), _o₂@(oadd e₂ n₂ a₂) =>
    (cmp e₁ e₂).then <| (_root_.cmp (n₁ : ℕ) n₂).then (cmp a₁ a₂)

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
    rw [_root_.cmp, cmpUsing_eq_eq, not_lt, not_lt, ← le_antisymm_iff] at h₂
    obtain rfl := Subtype.ext h₂
    simp

protected theorem zero_lt_one : (0 : ONote) < 1 := by
  simp only [lt_def, repr_zero, repr_one, Nat.cast_one, zero_lt_one]

/-- `NFBelow o b` says that `o` is a normal form ordinal notation satisfying `repr o < ω ^ b`. -/
inductive NFBelow : ONote → Ordinal.{0} → Prop
  | zero {b} : NFBelow 0 b
  | oadd' {e n a eb b} : NFBelow e eb → NFBelow a (repr e) → repr e < b → NFBelow (oadd e n a) b

/-- A normal form ordinal notation has the form

`ω ^ a₁ * n₁ + ω ^ a₂ * n₂ + ⋯ + ω ^ aₖ * nₖ`

where `a₁ > a₂ > ⋯ > aₖ` and all the `aᵢ` are also in normal form.

We will essentially only be interested in normal form ordinal notations, but to avoid complicating
the algorithms, we define everything over general ordinal notations and only prove correctness with
normal form as an invariant. -/
class NF (o : ONote) : Prop where
  out : Exists (NFBelow o)

instance NF.zero : NF 0 :=
  ⟨⟨0, NFBelow.zero⟩⟩

theorem NFBelow.oadd {e n a b} : NF e → NFBelow a (repr e) → repr e < b → NFBelow (oadd e n a) b
  | ⟨⟨_, h⟩⟩ => NFBelow.oadd' h

theorem NFBelow.fst {e n a b} (h : NFBelow (ONote.oadd e n a) b) : NF e := by
  obtain - | ⟨h₁, h₂, h₃⟩ := h; exact ⟨⟨_, h₁⟩⟩

theorem NF.fst {e n a} : NF (oadd e n a) → NF e
  | ⟨⟨_, h⟩⟩ => h.fst

theorem NFBelow.snd {e n a b} (h : NFBelow (ONote.oadd e n a) b) : NFBelow a (repr e) := by
  obtain - | ⟨h₁, h₂, h₃⟩ := h; exact h₂

theorem NF.snd' {e n a} : NF (oadd e n a) → NFBelow a (repr e)
  | ⟨⟨_, h⟩⟩ => h.snd

theorem NF.snd {e n a} (h : NF (oadd e n a)) : NF a :=
  ⟨⟨_, h.snd'⟩⟩

theorem NF.oadd {e a} (h₁ : NF e) (n) (h₂ : NFBelow a (repr e)) : NF (oadd e n a) :=
  ⟨⟨_, NFBelow.oadd h₁ h₂ (lt_succ _)⟩⟩

instance NF.oadd_zero (e n) [h : NF e] : NF (ONote.oadd e n 0) :=
  h.oadd _ NFBelow.zero

theorem NFBelow.lt {e n a b} (h : NFBelow (ONote.oadd e n a) b) : repr e < b := by
  obtain - | ⟨h₁, h₂, h₃⟩ := h; exact h₃

theorem NFBelow_zero : ∀ {o}, NFBelow o 0 ↔ o = 0
  | 0 => ⟨fun _ => rfl, fun _ => NFBelow.zero⟩
  | oadd _ _ _ =>
    ⟨fun h => (not_le_of_gt h.lt).elim (Ordinal.zero_le _), fun e => e.symm ▸ NFBelow.zero⟩

theorem NF.zero_of_zero {e n a} (h : NF (ONote.oadd e n a)) (e0 : e = 0) : a = 0 := by
  simpa [e0, NFBelow_zero] using h.snd'

theorem NFBelow.repr_lt {o b} (h : NFBelow o b) : repr o < ω ^ b := by
  induction h with
  | zero => exact opow_pos _ omega0_pos
  | oadd' _ _ h₃ _ IH =>
    rw [repr]
    apply (add_lt_add_left IH _).trans_le
    grw [← mul_succ, succ_le_of_lt (nat_lt_omega0 _), ← opow_succ, succ_le_of_lt h₃]
    exact omega0_pos

theorem NFBelow.mono {o b₁ b₂} (bb : b₁ ≤ b₂) (h : NFBelow o b₁) : NFBelow o b₂ := by
  induction h with
  | zero => exact zero
  | oadd' h₁ h₂ h₃ _ _ => constructor; exacts [h₁, h₂, lt_of_lt_of_le h₃ bb]

theorem NF.below_of_lt {e n a b} (H : repr e < b) :
    NF (ONote.oadd e n a) → NFBelow (ONote.oadd e n a) b
  | ⟨⟨b', h⟩⟩ => by (obtain - | ⟨h₁, h₂, h₃⟩ := h; exact NFBelow.oadd' h₁ h₂ H)

theorem NF.below_of_lt' : ∀ {o b}, repr o < ω ^ b → NF o → NFBelow o b
  | 0, _, _, _ => NFBelow.zero
  | ONote.oadd _ _ _, _, H, h =>
    h.below_of_lt <|
      (opow_lt_opow_iff_right one_lt_omega0).1 <| lt_of_le_of_lt (omega0_le_oadd _ _ _) H

theorem nfBelow_ofNat : ∀ n, NFBelow (ofNat n) 1
  | 0 => NFBelow.zero
  | Nat.succ _ => NFBelow.oadd NF.zero NFBelow.zero zero_lt_one

instance nf_ofNat (n) : NF (ofNat n) :=
  ⟨⟨_, nfBelow_ofNat n⟩⟩

instance nf_one : NF 1 := by rw [← ofNat_one]; infer_instance

theorem oadd_lt_oadd_1 {e₁ n₁ o₁ e₂ n₂ o₂} (h₁ : NF (oadd e₁ n₁ o₁)) (h : e₁ < e₂) :
    oadd e₁ n₁ o₁ < oadd e₂ n₂ o₂ :=
  @lt_of_lt_of_le _ _ (repr (oadd e₁ n₁ o₁)) _ _
    (NF.below_of_lt h h₁).repr_lt (omega0_le_oadd e₂ n₂ o₂)

theorem oadd_lt_oadd_2 {e o₁ o₂ : ONote} {n₁ n₂ : ℕ+} (h₁ : NF (oadd e n₁ o₁)) (h : (n₁ : ℕ) < n₂) :
    oadd e n₁ o₁ < oadd e n₂ o₂ := by
  simp only [lt_def, repr]
  refine lt_of_lt_of_le ((add_lt_add_iff_left _).2 h₁.snd'.repr_lt) (le_trans ?_ (le_add_right _ _))
  rwa [← mul_succ, mul_le_mul_iff_right₀ (opow_pos _ omega0_pos), succ_le_iff, Nat.cast_lt]

theorem oadd_lt_oadd_3 {e n a₁ a₂} (h : a₁ < a₂) : oadd e n a₁ < oadd e n a₂ := by
  rw [lt_def]; unfold repr; gcongr

theorem cmp_compares : ∀ (a b : ONote) [NF a] [NF b], (cmp a b).Compares a b
  | 0, 0, _, _ => rfl
  | oadd _ _ _, 0, _, _ => oadd_pos _ _ _
  | 0, oadd _ _ _, _, _ => oadd_pos _ _ _
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
        rcases nh with nh | nh
        · exact oadd_lt_oadd_2 h₁ nh.left
        · rw [ite_eq_iff] at nh; rcases nh.right with nh | nh <;> cases nh <;> contradiction
      case gt =>
        rcases nh with nh | nh
        · cases nh; contradiction
        · obtain ⟨_, nh⟩ := nh
          rw [ite_eq_iff] at nh; rcases nh with nh | nh
          · exact oadd_lt_oadd_2 h₂ nh.left
          · cases nh; contradiction
      rcases nh with nh | nh
      · cases nh; contradiction
      obtain ⟨nhl, nhr⟩ := nh
      rw [ite_eq_iff] at nhr
      rcases nhr with nhr | nhr
      · cases nhr; contradiction
      obtain rfl := Subtype.ext (nhl.eq_of_not_lt nhr.1)
      have IHa := @cmp_compares _ _ h₁.snd h₂.snd
      revert IHa; cases cmp a₁ a₂ <;> intro IHa <;> dsimp at IHa
      case lt => exact oadd_lt_oadd_3 IHa
      case gt => exact oadd_lt_oadd_3 IHa
      subst IHa; exact rfl

theorem repr_inj {a b} [NF a] [NF b] : repr a = repr b ↔ a = b :=
  ⟨fun e => match cmp a b, cmp_compares a b with
    | Ordering.lt, (h : repr a < repr b) => (ne_of_lt h e).elim
    | Ordering.gt, (h : repr a > repr b)=> (ne_of_gt h e).elim
    | Ordering.eq, h => h,
    congr_arg _⟩

theorem NF.of_dvd_omega0_opow {b e n a} (h : NF (ONote.oadd e n a))
    (d : ω ^ b ∣ repr (ONote.oadd e n a)) :
    b ≤ repr e ∧ ω ^ b ∣ repr a := by
  have := mt repr_inj.1 (fun h => by injection h : ONote.oadd e n a ≠ 0)
  have L := le_of_not_gt fun l => not_le_of_gt (h.below_of_lt l).repr_lt (le_of_dvd this d)
  simp only [repr] at d
  exact ⟨L, (dvd_add_iff <| (opow_dvd_opow _ L).mul_right _).1 d⟩

theorem NF.of_dvd_omega0 {e n a} (h : NF (ONote.oadd e n a)) :
    ω ∣ repr (ONote.oadd e n a) → repr e ≠ 0 ∧ ω ∣ repr a := by
  (rw [← opow_one ω, ← one_le_iff_ne_zero]; exact h.of_dvd_omega0_opow)

/-- `TopBelow b o` asserts that the largest exponent in `o`, if it exists, is less than `b`. This is
an auxiliary definition for decidability of `NF`. -/
def TopBelow (b : ONote) : ONote → Prop
  | 0 => True
  | oadd e _ _ => cmp e b = Ordering.lt

instance decidableTopBelow : DecidableRel TopBelow := by
  intro b o
  cases o <;> delta TopBelow <;> infer_instance

theorem nfBelow_iff_topBelow {b} [NF b] : ∀ {o}, NFBelow o (repr b) ↔ NF o ∧ TopBelow b o
  | 0 => ⟨fun h => ⟨⟨⟨_, h⟩⟩, trivial⟩, fun _ => NFBelow.zero⟩
  | oadd _ _ _ =>
    ⟨fun h => ⟨⟨⟨_, h⟩⟩, (@cmp_compares _ b h.fst _).eq_lt.2 h.lt⟩, fun ⟨h₁, h₂⟩ =>
      h₁.below_of_lt <| (@cmp_compares _ b h₁.fst _).eq_lt.1 h₂⟩

instance decidableNF : DecidablePred NF
  | 0 => isTrue NF.zero
  | oadd e n a => by
    have := decidableNF e
    have := decidableNF a
    apply decidable_of_iff (NF e ∧ NF a ∧ TopBelow e a)
    rw [← and_congr_right fun h => @nfBelow_iff_topBelow _ h _]
    exact ⟨fun ⟨h₁, h₂⟩ => NF.oadd h₁ n h₂, fun h => ⟨h.fst, h.snd'⟩⟩

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

instance : Add ONote :=
  ⟨add⟩

@[simp]
theorem zero_add (o : ONote) : 0 + o = o :=
  rfl

theorem oadd_add (e n a o) : oadd e n a + o = addAux e n (a + o) :=
  rfl

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

instance : Sub ONote :=
  ⟨sub⟩

theorem add_nfBelow {b} : ∀ {o₁ o₂}, NFBelow o₁ b → NFBelow o₂ b → NFBelow (o₁ + o₂) b
  | 0, _, _, h₂ => h₂
  | oadd e n a, o, h₁, h₂ => by
    have h' := add_nfBelow (h₁.snd.mono <| le_of_lt h₁.lt) h₂
    simp only [oadd_add]; revert h'; obtain - | ⟨e', n', a'⟩ := a + o <;> intro h'
    · exact NFBelow.oadd h₁.fst NFBelow.zero h₁.lt
    have : ((e.cmp e').Compares e e') := @cmp_compares _ _ h₁.fst h'.fst
    cases h : cmp e e' <;> dsimp [addAux] <;> simp only [h]
    · exact h'
    · simp only [h] at this
      subst e'
      exact NFBelow.oadd h'.fst h'.snd h'.lt
    · simp only [h] at this
      exact NFBelow.oadd h₁.fst (NF.below_of_lt this ⟨⟨_, h'⟩⟩) h₁.lt

instance add_nf (o₁ o₂) : ∀ [NF o₁] [NF o₂], NF (o₁ + o₂)
  | ⟨⟨b₁, h₁⟩⟩, ⟨⟨b₂, h₂⟩⟩ =>
    ⟨(le_total b₁ b₂).elim (fun h => ⟨b₂, add_nfBelow (h₁.mono h) h₂⟩) fun h =>
        ⟨b₁, add_nfBelow h₁ (h₂.mono h)⟩⟩

@[simp]
theorem repr_add : ∀ (o₁ o₂) [NF o₁] [NF o₂], repr (o₁ + o₂) = repr o₁ + repr o₂
  | 0, o, _, _ => by simp
  | oadd e n a, o, h₁, h₂ => by
    haveI := h₁.snd; have h' := repr_add a o
    conv_lhs at h' => simp [HAdd.hAdd, Add.add]
    have nf := ONote.add_nf a o
    conv at nf => simp [HAdd.hAdd, Add.add]
    conv in _ + o => simp [HAdd.hAdd, Add.add]
    rcases h : add a o with - | ⟨e', n', a'⟩ <;>
      simp only [add, addAux, h'.symm, h, add_assoc, repr] at nf h₁ ⊢
    have := h₁.fst; haveI := nf.fst; have ee := cmp_compares e e'
    cases he : cmp e e' <;> simp only [he, Ordering.compares_gt, Ordering.compares_lt,
        Ordering.compares_eq, repr, gt_iff_lt, PNat.add_coe, Nat.cast_add] at ee ⊢
    · rw [← add_assoc, @add_absorp _ (repr e') (ω ^ repr e' * (n' : ℕ))]
      · have := (h₁.below_of_lt ee).repr_lt
        unfold repr at this
        cases he' : e' <;> simp only [he', zero_def, opow_zero, repr, gt_iff_lt] at this ⊢ <;>
        exact lt_of_le_of_lt (le_add_right _ _) this
      · simpa using (mul_le_mul_iff_right₀ <| opow_pos (repr e') omega0_pos).2
          (Nat.cast_le.2 n'.pos)
    · rw [ee, ← add_assoc, ← mul_add]

theorem sub_nfBelow : ∀ {o₁ o₂ b}, NFBelow o₁ b → NF o₂ → NFBelow (o₁ - o₂) b
  | 0, o, b, _, h₂ => by cases o <;> exact NFBelow.zero
  | oadd _ _ _, 0, _, h₁, _ => h₁
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, b, h₁, h₂ => by
    have h' := sub_nfBelow h₁.snd h₂.snd
    simp only [HSub.hSub, Sub.sub, sub] at h' ⊢
    have := @cmp_compares _ _ h₁.fst h₂.fst
    cases h : cmp e₁ e₂
    · apply NFBelow.zero
    · rw [Nat.sub_eq]
      simp only [h, Ordering.compares_eq] at this
      subst e₂
      cases (n₁ : ℕ) - n₂
      · by_cases en : n₁ = n₂ <;> simp only [en, ↓reduceIte]
        · exact h'.mono (le_of_lt h₁.lt)
        · exact NFBelow.zero
      · exact NFBelow.oadd h₁.fst h₁.snd h₁.lt
    · exact h₁

instance sub_nf (o₁ o₂) : ∀ [NF o₁] [NF o₂], NF (o₁ - o₂)
  | ⟨⟨b₁, h₁⟩⟩, h₂ => ⟨⟨b₁, sub_nfBelow h₁ h₂⟩⟩

@[simp]
theorem repr_sub : ∀ (o₁ o₂) [NF o₁] [NF o₂], repr (o₁ - o₂) = repr o₁ - repr o₂
  | 0, o, _, h₂ => by cases o <;> exact (Ordinal.zero_sub _).symm
  | oadd _ _ _, 0, _, _ => (Ordinal.sub_zero _).symm
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
      · simp only [Nat.succPNat, Nat.succ_eq_add_one, repr, PNat.mk_coe, Nat.cast_add,
          Nat.cast_one, add_one_eq_succ]
        rw [(tsub_eq_iff_eq_add_of_le <| le_of_lt <| Nat.lt_of_sub_eq_succ mn).1 mn, add_comm,
          Nat.cast_add, mul_add, add_assoc, add_sub_add_cancel]
        refine
          (Ordinal.sub_eq_of_add_eq <|
              add_absorp h₂.snd'.repr_lt <| le_trans ?_ (le_add_right _ _)).symm
        exact Ordinal.le_mul_left _ (Nat.cast_lt.2 <| Nat.succ_pos _)
    · exact
        (Ordinal.sub_eq_of_add_eq <|
            add_absorp (h₂.below_of_lt ee).repr_lt <| omega0_le_oadd _ _ _).symm

/-- Multiplication of ordinal notations (correct only for normal input) -/
def mul : ONote → ONote → ONote
  | 0, _ => 0
  | _, 0 => 0
  | o₁@(oadd e₁ n₁ a₁), oadd e₂ n₂ a₂ =>
    if e₂ = 0 then oadd e₁ (n₁ * n₂) a₁ else oadd (e₁ + e₂) n₂ (mul o₁ a₂)

instance : Mul ONote :=
  ⟨mul⟩

instance : MulZeroClass ONote where
  zero_mul o := by cases o <;> rfl
  mul_zero o := by cases o <;> rfl

theorem oadd_mul (e₁ n₁ a₁ e₂ n₂ a₂) :
    oadd e₁ n₁ a₁ * oadd e₂ n₂ a₂ =
      if e₂ = 0 then oadd e₁ (n₁ * n₂) a₁ else oadd (e₁ + e₂) n₂ (oadd e₁ n₁ a₁ * a₂) :=
  rfl

theorem oadd_mul_nfBelow {e₁ n₁ a₁ b₁} (h₁ : NFBelow (oadd e₁ n₁ a₁) b₁) :
    ∀ {o₂ b₂}, NFBelow o₂ b₂ → NFBelow (oadd e₁ n₁ a₁ * o₂) (repr e₁ + b₂)
  | 0, _, _ => NFBelow.zero
  | oadd e₂ n₂ a₂, b₂, h₂ => by
    have IH := oadd_mul_nfBelow h₁ h₂.snd
    by_cases e0 : e₂ = 0 <;> simp only [e0, oadd_mul, ↓reduceIte]
    · apply NFBelow.oadd h₁.fst h₁.snd
      simpa using (add_lt_add_iff_left (repr e₁)).2 (lt_of_le_of_lt (Ordinal.zero_le _) h₂.lt)
    · haveI := h₁.fst
      haveI := h₂.fst
      apply NFBelow.oadd
      · infer_instance
      · rwa [repr_add]
      · rw [repr_add, add_lt_add_iff_left]
        exact h₂.lt

instance mul_nf : ∀ (o₁ o₂) [NF o₁] [NF o₂], NF (o₁ * o₂)
  | 0, o, _, h₂ => by cases o <;> exact NF.zero
  | oadd _ _ _, _, ⟨⟨_, hb₁⟩⟩, ⟨⟨_, hb₂⟩⟩ => ⟨⟨_, oadd_mul_nfBelow hb₁ hb₂⟩⟩

@[simp]
theorem repr_mul : ∀ (o₁ o₂) [NF o₁] [NF o₂], repr (o₁ * o₂) = repr o₁ * repr o₂
  | 0, o, _, h₂ => by cases o <;> exact (zero_mul _).symm
  | oadd _ _ _, 0, _, _ => (mul_zero _).symm
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, h₁, h₂ => by
    have IH : repr (mul _ _) = _ := @repr_mul _ _ h₁ h₂.snd
    conv =>
      lhs
      simp [(· * ·)]
    have ao : repr a₁ + ω ^ repr e₁ * (n₁ : ℕ) = ω ^ repr e₁ * (n₁ : ℕ) := by
      apply add_absorp h₁.snd'.repr_lt
      simpa using (mul_le_mul_iff_right₀ <| opow_pos _ omega0_pos).2 (Nat.cast_le.2 n₁.2)
    by_cases e0 : e₂ = 0
    · obtain ⟨x, xe⟩ := Nat.exists_eq_succ_of_ne_zero n₂.ne_zero
      simp only [Mul.mul, mul, e0, ↓reduceIte, repr, PNat.mul_coe, natCast_mul, opow_zero, one_mul]
      simp only [xe, h₂.zero_of_zero e0, repr, add_zero]
      rw [natCast_succ x, add_mul_succ _ ao, mul_assoc]
    · simp only [repr]
      haveI := h₁.fst
      haveI := h₂.fst
      simp only [Mul.mul, mul, e0, ite_false, repr.eq_2, repr_add, opow_add, IH, repr, mul_add]
      rw [← mul_assoc]
      congr 2
      have := mt repr_inj.1 e0
      rw [add_mul_of_isSuccLimit ao (isSuccLimit_opow_left isSuccLimit_omega0 this), mul_assoc,
        mul_omega0_dvd (Nat.cast_pos'.2 n₁.pos) (nat_lt_omega0 _)]
      simpa using opow_dvd_opow ω (one_le_iff_ne_zero.2 this)

/-- Calculate division and remainder of `o` mod `ω`:

`split' o = (a, n)` means `o = ω * a + n`. -/
def split' : ONote → ONote × ℕ
  | 0 => (0, 0)
  | oadd e n a =>
    if e = 0 then (0, n)
    else
      let (a', m) := split' a
      (oadd (e - 1) n a', m)

/-- Calculate division and remainder of `o` mod `ω`:

`split o = (a, n)` means `o = a + n`, where `ω ∣ a`. -/
def split : ONote → ONote × ℕ
  | 0 => (0, 0)
  | oadd e n a =>
    if e = 0 then (0, n)
    else
      let (a', m) := split a
      (oadd e n a', m)

/-- `scale x o` is the ordinal notation for `ω ^ x * o`. -/
def scale (x : ONote) : ONote → ONote
  | 0 => 0
  | oadd e n a => oadd (x + e) n (scale x a)

/-- `mulNat o n` is the ordinal notation for `o * n`. -/
def mulNat : ONote → ℕ → ONote
  | 0, _ => 0
  | _, 0 => 0
  | oadd e n a, m + 1 => oadd e (n * m.succPNat) a

/-- Auxiliary definition to compute the ordinal notation for the ordinal exponentiation in `opow` -/
def opowAux (e a0 a : ONote) : ℕ → ℕ → ONote
  | _, 0 => 0
  | 0, m + 1 => oadd e m.succPNat 0
  | k + 1, m => scale (e + mulNat a0 k) a + (opowAux e a0 a k m)

/-- Auxiliary definition to compute the ordinal notation for the ordinal exponentiation in `opow` -/
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

/-- `opow o₁ o₂` calculates the ordinal notation for the ordinal exponential `o₁ ^ o₂`. -/
def opow (o₁ o₂ : ONote) : ONote := opowAux2 o₂ (split o₁)

instance : Pow ONote ONote :=
  ⟨opow⟩

theorem opow_def (o₁ o₂ : ONote) : o₁ ^ o₂ = opowAux2 o₂ (split o₁) :=
  rfl

theorem split_eq_scale_split' : ∀ {o o' m} [NF o], split' o = (o', m) → split o = (scale 1 o', m)
  | 0, o', m, _, p => by injection p; substs o' m; rfl
  | oadd e n a, o', m, h, p => by
    by_cases e0 : e = 0 <;> simp only [split', e0, ↓reduceIte, Prod.mk.injEq, split] at p ⊢
    · rcases p with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
    · revert p
      rcases h' : split' a with ⟨a', m'⟩
      haveI := h.fst
      haveI := h.snd
      simp only [split_eq_scale_split' h', and_imp]
      have : 1 + (e - 1) = e := by
        refine repr_inj.1 ?_
        simp only [repr_add, repr_one, Nat.cast_one, repr_sub]
        have := mt repr_inj.1 e0
        exact Ordinal.add_sub_cancel_of_le <| one_le_iff_ne_zero.2 this
      intros
      substs o' m
      simp [scale, this]

theorem nf_repr_split' : ∀ {o o' m} [NF o], split' o = (o', m) → NF o' ∧ repr o = ω * repr o' + m
  | 0, o', m, _, p => by injection p; substs o' m; simp [NF.zero]
  | oadd e n a, o', m, h, p => by
    by_cases e0 : e = 0 <;>
      simp only [split', e0, ↓reduceIte, Prod.mk.injEq, repr, repr_zero, opow_zero, one_mul] at p ⊢
    · rcases p with ⟨rfl, rfl⟩
      simp [h.zero_of_zero e0, NF.zero]
    · revert p
      rcases h' : split' a with ⟨a', m'⟩
      haveI := h.fst
      haveI := h.snd
      obtain ⟨IH₁, IH₂⟩ := nf_repr_split' h'
      simp only [IH₂, and_imp]
      intros
      substs o' m
      have : (ω : Ordinal.{0}) ^ repr e = ω ^ (1 : Ordinal.{0}) * ω ^ (repr e - 1) := by
        have := mt repr_inj.1 e0
        rw [← opow_add, Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 this)]
      refine ⟨NF.oadd (by infer_instance) _ ?_, ?_⟩
      · simp only [opow_one, repr_sub, repr_one, Nat.cast_one] at this ⊢
        refine IH₁.below_of_lt' <|
          (mul_lt_mul_iff_right₀ omega0_pos).1 <| lt_of_le_of_lt (le_add_right _ m') ?_
        rw [← this, ← IH₂]
        exact h.snd'.repr_lt
      · rw [this]
        simp [mul_add, mul_assoc, add_assoc]

theorem scale_eq_mul (x) [NF x] : ∀ (o) [NF o], scale x o = oadd x 1 0 * o
  | 0, _ => rfl
  | oadd e n a, h => by
    simp only [HMul.hMul]; simp only [scale]
    haveI := h.snd
    by_cases e0 : e = 0
    · simp_rw [scale_eq_mul]
      simp [Mul.mul, mul, e0, h.zero_of_zero,
        show x + 0 = x from repr_inj.1 (by simp)]
    · simp [e0, Mul.mul, mul, scale_eq_mul, (· * ·)]

instance nf_scale (x) [NF x] (o) [NF o] : NF (scale x o) := by
  rw [scale_eq_mul]
  infer_instance

@[simp]
theorem repr_scale (x) [NF x] (o) [NF o] : repr (scale x o) = ω ^ repr x * repr o := by
  simp only [scale_eq_mul, repr_mul, repr, PNat.one_coe, Nat.cast_one, mul_one, add_zero]

theorem nf_repr_split {o o' m} [NF o] (h : split o = (o', m)) : NF o' ∧ repr o = repr o' + m := by
  rcases e : split' o with ⟨a, n⟩
  obtain ⟨s₁, s₂⟩ := nf_repr_split' e
  rw [split_eq_scale_split' e] at h
  injection h; substs o' n
  simp only [repr_scale, repr_one, Nat.cast_one, opow_one, ← s₂, and_true]
  infer_instance

theorem split_dvd {o o' m} [NF o] (h : split o = (o', m)) : ω ∣ repr o' := by
  rcases e : split' o with ⟨a, n⟩
  rw [split_eq_scale_split' e] at h
  injection h; subst o'
  cases nf_repr_split' e; simp

theorem split_add_lt {o e n a m} [NF o] (h : split o = (oadd e n a, m)) :
    repr a + m < ω ^ repr e := by
  obtain ⟨h₁, h₂⟩ := nf_repr_split h
  obtain ⟨e0, d⟩ := h₁.of_dvd_omega0 (split_dvd h)
  apply principal_add_omega0_opow _ h₁.snd'.repr_lt (lt_of_lt_of_le (nat_lt_omega0 _) _)
  simpa using opow_le_opow_right omega0_pos (one_le_iff_ne_zero.2 e0)

@[simp]
theorem mulNat_eq_mul (n o) : mulNat o n = o * ofNat n := by cases o <;> cases n <;> rfl

instance nf_mulNat (o) [NF o] (n) : NF (mulNat o n) := by simpa using ONote.mul_nf o (ofNat n)

instance nf_opowAux (e a0 a) [NF e] [NF a0] [NF a] : ∀ k m, NF (opowAux e a0 a k m) := by
  intro k m
  unfold opowAux
  cases m with
  | zero => cases k <;> exact NF.zero
  | succ m =>
    cases k with
    | zero => exact NF.oadd_zero _ _
    | succ k =>
      haveI := nf_opowAux e a0 a k
      simp only [mulNat_eq_mul]; infer_instance

instance nf_opow (o₁ o₂) [NF o₁] [NF o₂] : NF (o₁ ^ o₂) := by
  rcases e₁ : split o₁ with ⟨a, m⟩
  have na := (nf_repr_split e₁).1
  rcases e₂ : split' o₂ with ⟨b', k⟩
  haveI := (nf_repr_split' e₂).1
  obtain - | ⟨a0, n, a'⟩ := a
  · rcases m with - | m
    · by_cases o₂ = 0 <;> simp only [(· ^ ·), Pow.pow, opow, opowAux2, *] <;> decide
    · by_cases m = 0
      · simp only [(· ^ ·), Pow.pow, opow, opowAux2, *, zero_def]
        decide
      · simp only [(· ^ ·), Pow.pow, opow, opowAux2, *]
        infer_instance
  · simp only [(· ^ ·), Pow.pow, opow, opowAux2, e₁, split_eq_scale_split' e₂, mulNat_eq_mul]
    have := na.fst
    rcases k with - | k
    · infer_instance
    · cases k <;> cases m <;> infer_instance

theorem scale_opowAux (e a0 a : ONote) [NF e] [NF a0] [NF a] :
    ∀ k m, repr (opowAux e a0 a k m) = ω ^ repr e * repr (opowAux 0 a0 a k m)
  | 0, m => by cases m <;> simp [opowAux]
  | k + 1, m => by
    by_cases h : m = 0 <;> simp only [h, opowAux, mulNat_eq_mul, repr_add, repr_scale, repr_mul,
      repr_ofNat, zero_add, mul_add, repr_zero, mul_zero, scale_opowAux e, opow_add, mul_assoc]

theorem repr_opow_aux₁ {e a} [Ne : NF e] [Na : NF a] {a' : Ordinal} (e0 : repr e ≠ 0)
    (h : a' < (ω : Ordinal.{0}) ^ repr e) (aa : repr a = a') (n : ℕ+) :
    ((ω : Ordinal.{0}) ^ repr e * (n : ℕ) + a') ^ (ω : Ordinal.{0}) =
      (ω ^ repr e) ^ (ω : Ordinal.{0}) := by
  subst aa
  have No := Ne.oadd n (Na.below_of_lt' h)
  have := omega0_le_oadd e n a
  rw [repr] at this
  refine le_antisymm ?_ (opow_le_opow_left _ this)
  apply (opow_le_of_isSuccLimit ((opow_pos _ omega0_pos).trans_le this).ne' isSuccLimit_omega0).2
  intro b l
  have := (No.below_of_lt (lt_succ _)).repr_lt
  rw [repr] at this
  apply (opow_le_opow_left b <| this.le).trans
  rw [← opow_mul, ← opow_mul]
  rcases le_or_gt ω (repr e) with h | h
  · grw [le_succ b, ← add_one_eq_succ, add_mul_succ _ (one_add_of_omega0_le h), add_one_eq_succ]
    · gcongr
      · exact omega0_pos
      · exact succ_le_iff.2 <| by gcongr; exact isSuccLimit_omega0.succ_lt l
    · exact omega0_pos
  · grw [show _ * _ < _ from principal_mul_omega0 (isSuccLimit_omega0.succ_lt h) l]
    · simpa using mul_le_mul_right' (one_le_iff_ne_zero.2 e0) ω
    · exact omega0_pos

section

theorem repr_opow_aux₂ {a0 a'} [N0 : NF a0] [Na' : NF a'] (m : ℕ) (d : ω ∣ repr a')
    (e0 : repr a0 ≠ 0) (h : repr a' + m < (ω ^ repr a0)) (n : ℕ+) (k : ℕ) :
    let R := repr (opowAux 0 a0 (oadd a0 n a' * ofNat m) k m)
    (k ≠ 0 → R < ((ω ^ repr a0) ^ succ (k : Ordinal))) ∧
      ((ω ^ repr a0) ^ (k : Ordinal)) * ((ω ^ repr a0) * (n : ℕ) + repr a') + R =
        ((ω ^ repr a0) * (n : ℕ) + repr a' + m) ^ succ (k : Ordinal) := by
  intro R'
  haveI No : NF (oadd a0 n a') :=
    N0.oadd n (Na'.below_of_lt' <| lt_of_le_of_lt (le_add_right _ _) h)
  induction k with
  | zero => cases m <;> simp [R', opowAux]
  | succ k IH =>
  -- rename R => R'
  let R := repr (opowAux 0 a0 (oadd a0 n a' * ofNat m) k m)
  let ω0 := ω ^ repr a0
  let α' := ω0 * n + repr a'
  change (k ≠ 0 → R < (ω0 ^ succ (k : Ordinal))) ∧ (ω0 ^ (k : Ordinal)) * α' + R
    = (α' + m) ^ (succ ↑k : Ordinal) at IH
  have RR : R' = ω0 ^ (k : Ordinal) * (α' * m) + R := by
    by_cases h : m = 0
    · simp only [R, R', h, ONote.ofNat, Nat.cast_zero, ONote.repr, mul_zero,
        ONote.opowAux, add_zero]
    · simp only [α', ω0, R, R', ONote.repr_scale, ONote.repr, ONote.mulNat_eq_mul, ONote.opowAux,
        ONote.repr_ofNat, ONote.repr_mul, ONote.repr_add, Ordinal.opow_mul, ONote.zero_add]
  have α0 : 0 < α' := by simpa [lt_def, repr] using oadd_pos a0 n a'
  have ω00 : 0 < ω0 ^ (k : Ordinal) := opow_pos _ (opow_pos _ omega0_pos)
  have Rl : R < ω ^ (repr a0 * succ ↑k) := by
    by_cases k0 : k = 0
    · simp only [k0, Nat.cast_zero, succ_zero, mul_one, R]
      refine lt_of_lt_of_le ?_ (opow_le_opow_right omega0_pos (one_le_iff_ne_zero.2 e0))
      rcases m with - | m <;> simp [opowAux, omega0_pos]
      rw [← add_one_eq_succ, ← Nat.cast_succ]
      apply nat_lt_omega0
    · rw [opow_mul]
      exact IH.1 k0
  refine ⟨fun _ => ?_, ?_⟩
  · rw [RR, ← opow_mul _ _ (succ k.succ)]
    have e0 := Ordinal.pos_iff_ne_zero.2 e0
    have rr0 : 0 < repr a0 + repr a0 := lt_of_lt_of_le e0 (le_add_left _ _)
    apply principal_add_omega0_opow
    · simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, add_one_eq_succ,
        opow_mul, opow_succ, mul_assoc]
      gcongr ?_ * ?_
      rw [← Ordinal.opow_add]
      have : _ < ω ^ (repr a0 + repr a0) := (No.below_of_lt ?_).repr_lt
      · exact mul_lt_omega0_opow rr0 this (nat_lt_omega0 _)
      · simpa using (add_lt_add_iff_left (repr a0)).2 e0
    · exact
        lt_of_lt_of_le Rl
          (opow_le_opow_right omega0_pos <|
            mul_le_mul_left' (succ_le_succ_iff.2 (Nat.cast_le.2 (le_of_lt k.lt_succ_self))) _)
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
      add_mul_of_isSuccLimit _ (isSuccLimit_iff_omega0_dvd.2 ⟨ne_of_gt α0, αd⟩), mul_assoc,
      @mul_omega0_dvd n (Nat.cast_pos'.2 n.pos) (nat_lt_omega0 _) _ αd]
    apply @add_absorp _ (repr a0 * succ ↑k)
    · refine principal_add_omega0_opow _ ?_ Rl
      rw [opow_mul, opow_succ]
      gcongr
      exact No.snd'.repr_lt
    · have := mul_le_mul_left' (one_le_iff_pos.2 <| Nat.cast_pos'.2 n.pos) (ω0 ^ succ (k : Ordinal))
      rw [opow_mul]
      simpa [-opow_succ]
  · cases m
    · have : R = 0 := by cases k <;> simp [R, opowAux]
      simp [this]
    · rw [natCast_succ, add_mul_succ]
      apply add_absorp Rl
      rw [opow_mul, opow_succ]
      gcongr
      simpa [repr] using omega0_le_oadd a0 n a'

end

theorem repr_opow (o₁ o₂) [NF o₁] [NF o₂] : repr (o₁ ^ o₂) = repr o₁ ^ repr o₂ := by
  rcases e₁ : split o₁ with ⟨a, m⟩
  obtain ⟨N₁, r₁⟩ := nf_repr_split e₁
  obtain - | ⟨a0, n, a'⟩ := a
  · rcases m with - | m
    · by_cases h : o₂ = 0 <;> simp [opow_def, opowAux2, e₁, h, r₁]
      have := mt repr_inj.1 h
      rw [zero_opow this]
    · rcases e₂ : split' o₂ with ⟨b', k⟩
      obtain ⟨_, r₂⟩ := nf_repr_split' e₂
      by_cases h : m = 0
      · simp [opowAux2, opow_def, e₁, h, r₁, r₂]
      simp only [opow_def, opowAux2, e₁, r₁, e₂, r₂, repr,
          Nat.cast_succ, _root_.zero_add,
          add_zero]
      rw [opow_add, opow_mul, opow_omega0, add_one_eq_succ]
      · simp
      · simpa [Nat.one_le_iff_ne_zero]
      · rw [← Nat.cast_succ, lt_omega0]
        exact ⟨_, rfl⟩
  · haveI := N₁.fst
    haveI := N₁.snd
    obtain ⟨a00, ad⟩ := N₁.of_dvd_omega0 (split_dvd e₁)
    have al := split_add_lt e₁
    have aa : repr (a' + ofNat m) = repr a' + m := by
      simp only [ONote.repr_ofNat, ONote.repr_add]
    rcases e₂ : split' o₂ with ⟨b', k⟩
    obtain ⟨_, r₂⟩ := nf_repr_split' e₂
    simp only [opow_def, e₁, r₁, split_eq_scale_split' e₂, opowAux2, repr]
    rcases k with - | k
    · simp [r₂, opow_mul, repr_opow_aux₁ a00 al aa, add_assoc]
    · simp [r₂, opow_add, opow_mul, mul_assoc, add_assoc]
      rw [repr_opow_aux₁ a00 al aa, scale_opowAux]
      simp only [repr_mul, repr_scale, repr, opow_zero, PNat.val_ofNat, Nat.cast_one, mul_one,
        add_zero, opow_one, opow_mul]
      rw [← mul_add, ← add_assoc ((ω : Ordinal.{0}) ^ repr a0 * (n : ℕ))]
      congr 1
      rw [← pow_succ, ← opow_natCast, ← opow_natCast]
      exact (repr_opow_aux₂ _ ad a00 al _ _).2

/-- Given an ordinal, returns:

* `inl none` for `0`
* `inl (some a)` for `a + 1`
* `inr f` for a limit ordinal `a`, where `f i` is a sequence converging to `a` -/
def fundamentalSequence : ONote → (Option ONote) ⊕ (ℕ → ONote)
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

private theorem exists_lt_add {α} [hα : Nonempty α] {o : Ordinal} {f : α → Ordinal}
    (H : ∀ ⦃a⦄, a < o → ∃ i, a < f i) {b : Ordinal} ⦃a⦄ (h : a < b + o) : ∃ i, a < b + f i := by
  rcases lt_or_ge a b with h | h'
  · obtain ⟨i⟩ := id hα
    exact ⟨i, h.trans_le (le_add_right _ _)⟩
  · rw [← Ordinal.add_sub_cancel_of_le h', add_lt_add_iff_left] at h
    refine (H h).imp fun i H => ?_
    rwa [← Ordinal.add_sub_cancel_of_le h', add_lt_add_iff_left]

private theorem exists_lt_mul_omega0' {o : Ordinal} ⦃a⦄ (h : a < o * ω) :
    ∃ i : ℕ, a < o * ↑i + o := by
  obtain ⟨i, hi, h'⟩ := (lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).1 h
  obtain ⟨i, rfl⟩ := lt_omega0.1 hi
  exact ⟨i, h'.trans_le (le_add_right _ _)⟩

private theorem exists_lt_omega0_opow' {α} {o b : Ordinal} (hb : 1 < b) (ho : IsSuccLimit o)
    {f : α → Ordinal} (H : ∀ ⦃a⦄, a < o → ∃ i, a < f i) ⦃a⦄ (h : a < b ^ o) :
        ∃ i, a < b ^ f i := by
  obtain ⟨d, hd, h'⟩ := (lt_opow_of_isSuccLimit (zero_lt_one.trans hb).ne' ho).1 h
  exact (H hd).imp fun i hi => h'.trans <| (opow_lt_opow_iff_right hb).2 hi

/-- The property satisfied by `fundamentalSequence o`:

* `inl none` means `o = 0`
* `inl (some a)` means `o = succ a`
* `inr f` means `o` is a limit ordinal and `f` is a strictly increasing sequence which converges to
  `o` -/
def FundamentalSequenceProp (o : ONote) : (Option ONote) ⊕ (ℕ → ONote) → Prop
  | Sum.inl none => o = 0
  | Sum.inl (some a) => o.repr = succ a.repr ∧ (o.NF → a.NF)
  | Sum.inr f =>
    IsSuccLimit o.repr ∧
      (∀ i, f i < f (i + 1) ∧ f i < o ∧ (o.NF → (f i).NF)) ∧ ∀ a, a < o.repr → ∃ i, a < (f i).repr

theorem fundamentalSequenceProp_inl_none (o) :
    FundamentalSequenceProp o (Sum.inl none) ↔ o = 0 :=
  Iff.rfl

theorem fundamentalSequenceProp_inl_some (o a) :
    FundamentalSequenceProp o (Sum.inl (some a)) ↔ o.repr = succ a.repr ∧ (o.NF → a.NF) :=
  Iff.rfl

theorem fundamentalSequenceProp_inr (o f) :
    FundamentalSequenceProp o (Sum.inr f) ↔
      IsSuccLimit o.repr ∧
        (∀ i, f i < f (i + 1) ∧ f i < o ∧ (o.NF → (f i).NF)) ∧
        ∀ a, a < o.repr → ∃ i, a < (f i).repr :=
  Iff.rfl

theorem fundamentalSequence_has_prop (o) : FundamentalSequenceProp o (fundamentalSequence o) := by
  induction o with
  | zero => exact rfl
  | oadd a m b iha ihb
  rw [fundamentalSequence]
  rcases e : b.fundamentalSequence with (⟨_ | b'⟩ | f) <;>
    simp only [FundamentalSequenceProp] <;>
    rw [e, FundamentalSequenceProp] at ihb
  · rcases e : a.fundamentalSequence with (⟨_ | a'⟩ | f) <;> rcases e' : m.natPred with - | m' <;>
      simp only <;>
      rw [e, FundamentalSequenceProp] at iha <;>
      (try rw [show m = 1 by
            have := PNat.natPred_add_one m; rw [e'] at this; exact PNat.coe_inj.1 this.symm]) <;>
      (try rw [show m = (m' + 1).succPNat by
              rw [← e', ← PNat.coe_inj, Nat.succPNat_coe, ← Nat.add_one, PNat.natPred_add_one]]) <;>
      simp only [repr, iha, ihb, opow_lt_opow_iff_right one_lt_omega0, add_lt_add_iff_left,
        add_zero, lt_add_iff_pos_right, lt_def, mul_one, Nat.cast_zero,
        Nat.cast_succ, Nat.succPNat_coe, opow_succ, opow_zero, mul_add_one, PNat.one_coe, succ_zero,
        _root_.zero_add, zero_def]
    · decide
    · exact ⟨rfl, inferInstance⟩
    · have := opow_pos (repr a') omega0_pos
      refine
        ⟨isSuccLimit_mul this isSuccLimit_omega0, fun i =>
          ⟨this, ?_, fun H => @NF.oadd_zero _ _ (iha.2 H.fst)⟩, exists_lt_mul_omega0'⟩
      rw [← mul_succ, ← natCast_succ]
      gcongr
      apply nat_lt_omega0
    · have := opow_pos (repr a') omega0_pos
      refine
        ⟨isSuccLimit_add _ (isSuccLimit_mul this isSuccLimit_omega0), fun i => ⟨this, ?_, ?_⟩,
          exists_lt_add exists_lt_mul_omega0'⟩
      · rw [← mul_succ, ← natCast_succ]
        gcongr
        apply nat_lt_omega0
      · refine fun H => H.fst.oadd _ (NF.below_of_lt' ?_ (@NF.oadd_zero _ _ (iha.2 H.fst)))
        rw [repr, ← zero_def, repr, add_zero, iha.1, opow_succ]
        gcongr
        apply nat_lt_omega0
    · rcases iha with ⟨h1, h2, h3⟩
      refine ⟨isSuccLimit_opow one_lt_omega0 h1, fun i => ?_,
        exists_lt_omega0_opow' one_lt_omega0 h1 h3⟩
      obtain ⟨h4, h5, h6⟩ := h2 i
      exact ⟨h4, h5, fun H => @NF.oadd_zero _ _ (h6 H.fst)⟩
    · rcases iha with ⟨h1, h2, h3⟩
      refine
        ⟨isSuccLimit_add _ (isSuccLimit_opow one_lt_omega0 h1), fun i => ?_,
          exists_lt_add (exists_lt_omega0_opow' one_lt_omega0 h1 h3)⟩
      obtain ⟨h4, h5, h6⟩ := h2 i
      refine ⟨h4, h5, fun H => H.fst.oadd _ (NF.below_of_lt' ?_ (@NF.oadd_zero _ _ (h6 H.fst)))⟩
      rwa [repr, ← zero_def, repr, add_zero, PNat.one_coe, Nat.cast_one, mul_one,
        opow_lt_opow_iff_right one_lt_omega0]
  · refine ⟨by
      rw [repr, ihb.1, add_succ, repr], fun H => H.fst.oadd _ (NF.below_of_lt' ?_ (ihb.2 H.snd))⟩
    have := H.snd'.repr_lt
    rw [ihb.1] at this
    exact (lt_succ _).trans this
  · rcases ihb with ⟨h1, h2, h3⟩
    simp only [repr]
    exact
      ⟨isSuccLimit_add _ h1, fun i =>
        ⟨oadd_lt_oadd_3 (h2 i).1, oadd_lt_oadd_3 (h2 i).2.1, fun H =>
          H.fst.oadd _ (NF.below_of_lt' (lt_trans (h2 i).2.1 H.snd'.repr_lt) ((h2 i).2.2 H.snd))⟩,
        exists_lt_add h3⟩

/-- The fast growing hierarchy for ordinal notations `< ε₀`. This is a sequence of functions `ℕ → ℕ`
indexed by ordinals, with the definition:

* `f_0(n) = n + 1`
* `f_(α + 1)(n) = f_α^[n](n)`
* `f_α(n) = f_(α[n])(n)` where `α` is a limit ordinal and `α[i]` is the fundamental sequence
  converging to `α` -/
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

theorem fastGrowing_zero' (o : ONote) (h : fundamentalSequence o = Sum.inl none) :
    fastGrowing o = Nat.succ := by
  rw [fastGrowing_def h]

theorem fastGrowing_succ (o) {a} (h : fundamentalSequence o = Sum.inl (some a)) :
    fastGrowing o = fun i => (fastGrowing a)^[i] i := by
  rw [fastGrowing_def h]

theorem fastGrowing_limit (o) {f} (h : fundamentalSequence o = Sum.inr f) :
    fastGrowing o = fun i => fastGrowing (f i) i := by
  rw [fastGrowing_def h]

@[simp]
theorem fastGrowing_zero : fastGrowing 0 = Nat.succ :=
  fastGrowing_zero' _ rfl

@[simp]
theorem fastGrowing_one : fastGrowing 1 = fun n => 2 * n := by
  rw [@fastGrowing_succ 1 0 rfl]; funext i; rw [two_mul, fastGrowing_zero]
  suffices ∀ a b, Nat.succ^[a] b = b + a from this _ _
  intro a b; induction a <;> simp [*, Function.iterate_succ', Nat.add_assoc, -Function.iterate_succ]

@[simp]
theorem fastGrowing_two : fastGrowing 2 = fun n => (2 ^ n) * n := by
  rw [@fastGrowing_succ 2 1 rfl]
  simp

/-- We can extend the fast growing hierarchy one more step to `ε₀` itself, using `ω ^ (ω ^ (⋯ ^ ω))`
as the fundamental sequence converging to `ε₀` (which is not an `ONote`). Extending the fast
growing hierarchy beyond this requires a definition of fundamental sequence for larger ordinals. -/
def fastGrowingε₀ (i : ℕ) : ℕ :=
  fastGrowing ((fun a => a.oadd 1 0)^[i] 0) i

theorem fastGrowingε₀_zero : fastGrowingε₀ 0 = 1 := by simp [fastGrowingε₀]

theorem fastGrowingε₀_one : fastGrowingε₀ 1 = 2 := by
  simp [fastGrowingε₀, show oadd 0 1 0 = 1 from rfl]

theorem fastGrowingε₀_two : fastGrowingε₀ 2 = 2048 := by
  norm_num [fastGrowingε₀, show oadd 0 1 0 = 1 from rfl, @fastGrowing_limit (oadd 1 1 0) _ rfl,
    show oadd 0 (2 : Nat).succPNat 0 = 3 from rfl, @fastGrowing_succ 3 2 rfl]

end ONote

/-- The type of normal ordinal notations.

It would have been nicer to define this right in the inductive type, but `NF o` requires `repr`
which requires `ONote`, so all these things would have to be defined at once, which messes up the VM
representation. -/
def NONote :=
  { o : ONote // o.NF }

instance : DecidableEq NONote := by unfold NONote; infer_instance

namespace NONote

open ONote

instance NF (o : NONote) : NF o.1 :=
  o.2

/-- Construct a `NONote` from an ordinal notation (and infer normality) -/
def mk (o : ONote) [h : ONote.NF o] : NONote :=
  ⟨o, h⟩

/-- The ordinal represented by an ordinal notation.

This function is noncomputable because ordinal arithmetic is noncomputable. In computational
applications `NONote` can be used exclusively without reference to `Ordinal`, but this function
allows for correctness results to be stated. -/
noncomputable def repr (o : NONote) : Ordinal :=
  o.1.repr

instance : ToString NONote :=
  ⟨fun x => x.1.toString⟩

instance : Repr NONote :=
  ⟨fun x prec => x.1.repr' prec⟩

instance : Preorder NONote where
  le x y := repr x ≤ repr y
  lt x y := repr x < repr y
  le_refl _ := @le_refl Ordinal _ _
  le_trans _ _ _ := @le_trans Ordinal _ _ _ _
  lt_iff_le_not_ge _ _ := @lt_iff_le_not_ge Ordinal _ _ _

instance : Zero NONote :=
  ⟨⟨0, NF.zero⟩⟩

instance : Inhabited NONote :=
  ⟨0⟩

theorem lt_wf : @WellFounded NONote (· < ·) :=
  InvImage.wf repr Ordinal.lt_wf

instance : WellFoundedLT NONote :=
  ⟨lt_wf⟩

instance : WellFoundedRelation NONote :=
  ⟨(· < ·), lt_wf⟩

/-- Convert a natural number to an ordinal notation -/
def ofNat (n : ℕ) : NONote :=
  ⟨ONote.ofNat n, ⟨⟨_, nfBelow_ofNat _⟩⟩⟩

/-- Compare ordinal notations -/
def cmp (a b : NONote) : Ordering :=
  ONote.cmp a.1 b.1

theorem cmp_compares : ∀ a b : NONote, (cmp a b).Compares a b
  | ⟨a, ha⟩, ⟨b, hb⟩ => by
    dsimp [cmp]
    have := ONote.cmp_compares a b
    cases h : ONote.cmp a b <;> simp only [h] at this <;> try exact this
    exact Subtype.mk_eq_mk.2 this

instance : LinearOrder NONote :=
  linearOrderOfCompares cmp cmp_compares

/-- Asserts that `repr a < ω ^ repr b`. Used in `NONote.recOn`. -/
def below (a b : NONote) : Prop :=
  NFBelow a.1 (repr b)

/-- The `oadd` pseudo-constructor for `NONote` -/
def oadd (e : NONote) (n : ℕ+) (a : NONote) (h : below a e) : NONote :=
  ⟨_, NF.oadd e.2 n h⟩

/-- This is a recursor-like theorem for `NONote` suggesting an inductive definition, which can't
actually be defined this way due to conflicting dependencies. -/
@[elab_as_elim]
def recOn {C : NONote → Sort*} (o : NONote) (H0 : C 0)
    (H1 : ∀ e n a h, C e → C a → C (oadd e n a h)) : C o := by
  obtain ⟨o, h⟩ := o; induction o with
  | zero => exact H0
  | oadd e n a IHe IHa => exact H1 ⟨e, h.fst⟩ n ⟨a, h.snd⟩ h.snd' (IHe _) (IHa _)

/-- Addition of ordinal notations -/
instance : Add NONote :=
  ⟨fun x y => mk (x.1 + y.1)⟩

theorem repr_add (a b) : repr (a + b) = repr a + repr b :=
  ONote.repr_add a.1 b.1

/-- Subtraction of ordinal notations -/
instance : Sub NONote :=
  ⟨fun x y => mk (x.1 - y.1)⟩

theorem repr_sub (a b) : repr (a - b) = repr a - repr b :=
  ONote.repr_sub a.1 b.1

/-- Multiplication of ordinal notations -/
instance : Mul NONote :=
  ⟨fun x y => mk (x.1 * y.1)⟩

theorem repr_mul (a b) : repr (a * b) = repr a * repr b :=
  ONote.repr_mul a.1 b.1

/-- Exponentiation of ordinal notations -/
def opow (x y : NONote) :=
  mk (x.1 ^ y.1)

theorem repr_opow (a b) : repr (opow a b) = repr a ^ repr b :=
  ONote.repr_opow a.1 b.1

end NONote
